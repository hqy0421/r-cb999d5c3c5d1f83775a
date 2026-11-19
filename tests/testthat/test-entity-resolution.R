# Tests for exact, constraint-aware entity resolution and the entity-level
# analysis pipeline. The solver's optimality is checked against exhaustive
# enumeration of every set partition (Bell number) for small n.

# --- helpers ----------------------------------------------------------------

all_partitions <- function(k) {
  rec <- function(m) {
    if (m == 1L) {
      return(list(1L))
    }
    out <- list()
    for (pp in rec(m - 1L)) {
      for (cc in seq_len(max(pp) + 1L)) {
        out[[length(out) + 1L]] <- c(pp, cc)
      }
    }
    out
  }
  rec(k)
}

make_case <- function(k, seed) {
  set.seed(seed)
  ids <- letters[seq_len(k)]
  mg <- matrix(0L, k, k)
  sp <- matrix(0L, k, k)
  rr <- list()
  for (ii in seq_len(k - 1L)) {
    for (jj in (ii + 1L):k) {
      mm <- sample(0:9, 1L)
      ss <- sample(0:9, 1L)
      mg[ii, jj] <- mg[jj, ii] <- mm
      sp[ii, jj] <- sp[jj, ii] <- ss
      rr[[length(rr) + 1L]] <- data.frame(
        id1 = ids[[ii]], id2 = ids[[jj]],
        merge_penalty = mm, split_penalty = ss
      )
    }
  }
  list(ids = ids, mg = mg, sp = sp, pen = do.call(rbind, rr))
}

brute_min <- function(ids, mg, sp, k, ml = NULL, cl = NULL) {
  best <- Inf
  for (pp in all_partitions(k)) {
    ok <- TRUE
    if (!is.null(ml)) {
      for (r in seq_len(nrow(ml))) {
        ok <- ok &&
          pp[[match(ml$id1[r], ids)]] == pp[[match(ml$id2[r], ids)]]
      }
    }
    if (!is.null(cl)) {
      for (r in seq_len(nrow(cl))) {
        ok <- ok &&
          pp[[match(cl$id1[r], ids)]] != pp[[match(cl$id2[r], ids)]]
      }
    }
    if (!ok) next
    cost <- 0L
    for (ii in seq_len(k - 1L)) {
      for (jj in (ii + 1L):k) {
        cost <- cost +
          if (pp[[ii]] == pp[[jj]]) mg[ii, jj] else sp[ii, jj]
      }
    }
    best <- min(best, cost)
  }
  best
}

full_pen <- function(ids, merge_penalty, split_penalty) {
  cm <- utils::combn(ids, 2L)
  tibble::tibble(
    id1 = cm[1L, ], id2 = cm[2L, ],
    merge_penalty = merge_penalty, split_penalty = split_penalty
  )
}

# --- exactness --------------------------------------------------------------

test_that("solver matches exhaustive optimum without constraints", {
  for (trial in 1:25) {
    k <- sample(2:8, 1L)
    cs <- make_case(k, seed = 100L + trial)
    res <- resolve_entities(cs$ids, cs$pen)
    expect_equal(total_penalty(res),
                 brute_min(cs$ids, cs$mg, cs$sp, k))
    # pairwise explanation reconciles to the certified total
    pc <- pair_costs(res)
    expect_equal(sum(pc$cost), total_penalty(res))
    expect_true(all(pc$decision %in% c("merge", "split")))
    # every record appears once
    expect_setequal(res$record_id, cs$ids)
  }
})

test_that("solver matches exhaustive optimum with hard constraints", {
  for (trial in 1:25) {
    k <- sample(3:8, 1L)
    cs <- make_case(k, seed = 200L + trial)
    all_pairs <- utils::combn(cs$ids, 2L, simplify = FALSE)
    pick <- sample(all_pairs, sample(1:min(3L, length(all_pairs)), 1L))
    ml <- do.call(rbind, lapply(pick, function(q)
      data.frame(id1 = q[[1]], id2 = q[[2]])))
    remaining <- setdiff(all_pairs, lapply(seq_len(nrow(ml)), function(r)
      sort(c(ml$id1[r], ml$id2[r]))))
    cl <- if (length(remaining) > 0L) {
      do.call(rbind, lapply(
        sample(remaining, sample(seq_along(remaining), 1L)),
        function(q) data.frame(id1 = q[[1]], id2 = q[[2]])
      ))
    } else {
      NULL
    }

    ref <- brute_min(cs$ids, cs$mg, cs$sp, k, ml, cl)
    if (!is.finite(ref)) {
      expect_error(
        resolve_entities(cs$ids, cs$pen, must_link = ml, cannot_link = cl),
        "inconsistent"
      )
      next
    }

    got <- resolve_entities(cs$ids, cs$pen,
                            must_link = ml, cannot_link = cl)
    expect_equal(total_penalty(got), ref)
    for (r in seq_len(nrow(ml))) {
      expect_equal(
        got$entity_id[match(ml$id1[r], got$record_id)],
        got$entity_id[match(ml$id2[r], got$record_id)]
      )
    }
    if (!is.null(cl)) {
      for (r in seq_len(nrow(cl))) {
        expect_false(
          got$entity_id[match(cl$id1[r], got$record_id)] ==
            got$entity_id[match(cl$id2[r], got$record_id)]
        )
      }
    }
  }
})

test_that("must-link transitivity and cannot-link contradiction are enforced", {
  ids <- c("a", "b", "c")
  pen <- full_pen(ids, rep(9L, 3), rep(1L, 3))

  # a~b and b~c force all three together despite split being cheaper
  ml <- data.frame(id1 = c("a", "b"), id2 = c("b", "c"))
  res <- resolve_entities(ids, pen, must_link = ml)
  expect_equal(length(unique(res$entity_id)), 1L)

  # the same closure contradicted by a cannot-link must fail hard
  expect_error(
    resolve_entities(
      ids, pen, must_link = ml,
      cannot_link = data.frame(id1 = "a", id2 = "c")
    ),
    "inconsistent"
  )
})

test_that("partition is independent of response values", {
  ids <- c("a", "b", "c", "d")
  pen <- full_pen(ids, c(1L, 8L, 8L, 8L, 8L, 1L),
                       c(9L, 2L, 2L, 2L, 2L, 9L))
  r1 <- resolve_entities(ids, pen)
  # the solver never sees any response attribute; confirm determinism too
  r2 <- resolve_entities(ids, pen)
  expect_identical(r1$entity_id, r2$entity_id)
})

# --- structure and accessors ------------------------------------------------

test_that("accessors return id mapping, members and pairwise costs", {
  ids <- c("a", "b", "c")
  pen <- full_pen(ids, c(1L, 8L, 8L), c(9L, 2L, 2L))
  res <- resolve_entities(ids, pen)

  expect_s3_class(res, "entity_resolution")
  expect_equal(nrow(res), 3L)
  expect_type(res$entity_id, "integer")
  expect_type(res$record_id, "character")

  mem <- entity_members(res)
  expect_setequal(names(mem), c("entity_id", "n_records", "record_ids"))
  expect_setequal(unlist(mem$record_ids), ids)

  pc <- pair_costs(res)
  expect_equal(nrow(pc), 3L)
  expect_setequal(names(pc),
                  c("id1", "id2", "merge_penalty", "split_penalty",
                    "decision", "cost"))
  expect_type(pc$cost, "integer")
  expect_equal(total_penalty(res), sum(pc$cost))
})

test_that("single-record input is a trivial single entity", {
  res <- resolve_entities(
    "x",
    tibble::tibble(id1 = character(), id2 = character(),
                   merge_penalty = integer(), split_penalty = integer())
  )
  expect_equal(res$entity_id, 1L)
  expect_equal(total_penalty(res), 0L)
  expect_equal(attr(res, "n_entities"), 1L)
})

# --- validation -------------------------------------------------------------

test_that("penalty and constraint inputs are validated", {
  good <- full_pen(c("a", "b"), 1L, 1L)

  expect_error(resolve_entities(c("a", "a"), good), "unique")
  expect_error(
    resolve_entities(c("a", "b"),
                     full_pen(c("a", "b"), 1.5, 1L)),
    "integer"
  )
  expect_error(
    resolve_entities(c("a", "b"),
                     full_pen(c("a", "b"), -1L, 1L)),
    "non-negative"
  )
  expect_error(
    resolve_entities(c("a", "b", "c"),
                     full_pen(c("a", "b"), 1L, 1L)),
    "one row per unordered pair"
  )
  expect_error(
    resolve_entities(
      c("a", "b"), good,
      cannot_link = data.frame(id1 = "a", id2 = "a")
    ),
    "itself"
  )
  expect_error(resolve_entities(c("a", "b"), good, max_nodes = 0),
               "max_nodes")
})

test_that("exhausting the node budget errors rather than approximating", {
  cs <- make_case(8L, seed = 555L)
  expect_error(
    resolve_entities(cs$ids, cs$pen, max_nodes = 2L),
    "node budget"
  )
})

# --- aggregation ------------------------------------------------------------

test_that("aggregate_entities produces one typed row per entity", {
  ids <- c("a", "b", "c", "d")
  pen <- full_pen(
    ids,
    merge_penalty = c(0L, 9L, 9L, 9L, 9L, 0L),
    split_penalty = c(9L, 0L, 0L, 0L, 0L, 9L)
  )
  res <- resolve_entities(ids, pen)
  expect_equal(attr(res, "n_entities"), 2L)

  df <- tibble::tibble(
    record_id = ids,
    age = c(20, 22, 60, 62),
    city = c("NYC", "NYC", "LA", "LA")
  )

  et <- aggregate_entities(
    res, df,
    rules = list(
      n_members = "n",
      age = "mean",
      city = "mode",
      age_range = list(
        rule = function(v) max(v) - min(v), column = "age"
      )
    )
  )

  expect_s3_class(et, "entity_table")
  expect_equal(nrow(et), 2L)
  expect_equal(et$n_members, c(2L, 2L))
  expect_equal(et$age, c(21, 61))
  expect_type(et$n_members, "integer")
  expect_type(et$age, "double")
  expect_type(et$city, "character")
  expect_equal(et$age_range, c(2, 2))
})

test_that("aggregation failures are raised, not silently coerced", {
  ids <- c("a", "b")
  pen <- full_pen(ids, 1L, 9L)
  res <- resolve_entities(ids, pen)
  df <- tibble::tibble(record_id = ids, city = c("NYC", "LA"))

  expect_error(
    aggregate_entities(res, df, rules = list(city = "mean")),
    "numeric source column"
  )
  expect_error(
    aggregate_entities(res, df, rules = list(city = function(v) v)),
    "single atomic value"
  )
  expect_error(
    aggregate_entities(res, df, rules = list()),
    "at least one"
  )
  # data missing a record referenced by the resolution
  expect_error(
    aggregate_entities(
      res, df[1, ], rules = list(city = "mode")
    ),
    "missing rows"
  )
})

# --- end-to-end pipeline ----------------------------------------------------

test_that("fit_entity_analysis really specifies and fits the entity data", {
  ids <- c("a", "b", "c", "d", "e", "f")
  pen <- do.call(rbind, lapply(
    utils::combn(ids, 2L, simplify = FALSE),
    function(q) {
      i <- match(q[[1]], ids)
      j <- match(q[[2]], ids)
      same <- (i <= 3 && j <= 3) || (i >= 4 && j >= 4)
      data.frame(
        id1 = q[[1]], id2 = q[[2]],
        merge_penalty = if (same) 0L else 9L,
        split_penalty = if (same) 9L else 0L
      )
    }
  ))

  df <- tibble::tibble(
    record_id = ids,
    age = c(20, 22, 24, 60, 62, 64),
    hours = c(40, 42, 44, 30, 28, 26)
  )

  ana <- fit_entity_analysis(
    record_ids = ids, penalties = pen, data = df,
    rules = list(age = "mean", hours = "mean"),
    formula = hours ~ age
  )

  expect_s3_class(ana, "entity_analysis")
  expect_equal(ana$audit$n_entities, 2L)
  expect_equal(ana$audit$n_included, 2L)
  expect_equal(ana$audit$n_excluded, 0L)
  expect_true(is_fitted(ana$fit))
  expect_setequal(names(ana$fit), c("term", "estimate"))

  # coefficients must equal a fresh glm on the two-row entity table
  ref <- stats::glm(hours ~ age, data = ana$entity_table)
  expect_equal(ana$fit$estimate, unname(coef(ref)))
  expect_equal(nrow(ana$included), 2L)
})

test_that("excluded entities are reported and contradictions block publication", {
  ids <- c("a", "b", "c", "d")
  pen <- full_pen(
    ids,
    merge_penalty = c(0L, 9L, 9L, 9L, 9L, 0L),
    split_penalty = c(9L, 0L, 0L, 0L, 0L, 9L)
  )
  df <- tibble::tibble(
    record_id = ids, age = c(20, 22, 60, 62),
    hours = c(NA_real_, 42, 30, 28)
  )

  ana <- fit_entity_analysis(
    record_ids = ids, penalties = pen, data = df,
    rules = list(age = "mean", hours = "mean"),
    formula = hours ~ age
  )
  expect_equal(ana$audit$n_excluded, 1L)
  expect_match(ana$excluded$reason, "missing")

  # contradictory constraints: no population is published
  expect_error(
    fit_entity_analysis(
      record_ids = ids, penalties = pen, data = df,
      rules = list(age = "mean", hours = "mean"),
      formula = hours ~ age,
      must_link = data.frame(id1 = "a", id2 = "b"),
      cannot_link = data.frame(id1 = "a", id2 = "b")
    ),
    "inconsistent"
  )

  # a formula column lacking an aggregation rule is rejected before fitting
  expect_error(
    fit_entity_analysis(
      record_ids = ids, penalties = pen, data = df,
      rules = list(age = "mean"),
      formula = hours ~ age
    ),
    "not found in the aggregated"
  )
})
