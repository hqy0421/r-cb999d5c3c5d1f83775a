#' Resolve records into consistent entities under hard constraints
#'
#' @description
#'
#' `resolve_entities()` performs entity-level analysis: it partitions a set of
#' records, identified by stable `record_id`s, into entities (clusters) that
#' (1) satisfy every supplied must-link and cannot-link constraint and
#' (2) minimize the total pairwise penalty. The optimum is found **exactly**
#' with a branch-and-bound search over partitions --- there is no threshold,
#' no connected-components shortcut, and no greedy approximation. Any one of
#' possibly several globally optimal partitions may be returned.
#'
#' The partition depends only on the supplied penalties and hard constraints,
#' never on response values or any other attribute of the records.
#'
#' @param record_ids An atomic vector of stable, unique record identifiers.
#'   Coerced to character.
#' @param penalties A data frame (or tibble) with exactly one row per
#'   unordered pair of records and the columns:
#'
#'   * `id1`, `id2`: record identifiers from `record_ids` (a pair may be listed
#'     in either orientation);
#'   * `merge_penalty`: non-negative integer cost incurred if the two records
#'     are placed in the **same** entity;
#'   * `split_penalty`: non-negative integer cost incurred if the two records
#'     are placed in **different** entities.
#'
#'   Every pair of distinct records must be listed exactly once.
#' @param must_link An optional data frame with columns `id1` and `id2`
#'   declaring trusted pairs that must end up in the same entity. Must-links
#'   are closed under transitivity.
#' @param cannot_link An optional data frame with columns `id1` and `id2`
#'   declaring trusted pairs that must end up in different entities.
#' @param max_nodes A positive integer bounding the number of branch-and-bound
#'   nodes. If the bound is hit before optimality is proved, the function
#'   errors rather than returning an approximate partition.
#'
#' @return An `entity_resolution` object: a tibble with one row per record and
#'   columns `entity_id` (integer, ordered by the smallest member record) and
#'   `record_id`, carrying metadata accessible via [entity_members()],
#'   [pair_costs()], and [total_penalty()].
#'
#' @family entity resolution
#' @export
#' @examples
#' ids <- c("a", "b", "c", "d")
#' penalties <- tibble::tribble(
#'   ~id1, ~id2, ~merge_penalty, ~split_penalty,
#'   "a",  "b",            1L,             9L,
#'   "a",  "c",            8L,             2L,
#'   "a",  "d",            8L,             2L,
#'   "b",  "c",            8L,             2L,
#'   "b",  "d",            8L,             2L,
#'   "c",  "d",            1L,             9L
#' )
#'
#' resolve_entities(ids, penalties)
#'
#' # force a and c together; the optimum changes because the constraint is hard
#' resolve_entities(
#'   ids, penalties,
#'   must_link = tibble::tibble(id1 = "a", id2 = "c")
#' )
resolve_entities <- function(
  record_ids,
  penalties,
  must_link = NULL,
  cannot_link = NULL,
  max_nodes = 100000L
) {
  call <- rlang::current_env()

  record_ids <- check_record_ids(record_ids, call)
  max_nodes <- check_max_nodes(max_nodes, call)
  penalties <- check_penalties(penalties, record_ids, call)
  must_link <- check_links(must_link, record_ids, "must_link", call)
  cannot_link <- check_links(
    cannot_link, record_ids, "cannot_link", call
  )

  n <- length(record_ids)

  # Degenerate case: a single record forms a single entity with zero cost.
  # Pairwise validation (which assumes at least two records) is bypassed.
  if (n == 1L) {
    return(build_resolution(
      entity_id = 1L,
      record_ids = record_ids,
      penalties = tibble::tibble(
        id1 = character(), id2 = character(),
        merge_penalty = integer(), split_penalty = integer(),
        .pos_i = integer(), .pos_j = integer()
      ),
      search_nodes = 1L
    ))
  }

  # 1. Close must-links under transitivity into forced blocks.
  ml <- collapse_must_links(record_ids, must_link)
  block <- ml$block
  n_blocks <- ml$n_blocks

  # 2. Translate cannot-links to blocks; detect hard-constraint contradictions.
  forbidden <- build_cannot_graph(
    cannot_link, block, record_ids, call
  )

  # 3. Accumulate block-level cost matrices and the forced within-block cost.
  costs <- build_block_costs(penalties, block, n_blocks, n)
  within_cost <- forced_within_cost(penalties, block)

  # 4. Exact global optimization.
  solution <- solve_bb(
    costs$merge_cost,
    costs$split_cost,
    forbidden,
    n_blocks,
    within_cost,
    max_nodes,
    call
  )

  entity_by_block <- relabel_entities(solution$assign)
  entity_id <- entity_by_block[block]

  res <- build_resolution(
    entity_id = entity_id,
    record_ids = record_ids,
    penalties = penalties,
    search_nodes = solution$nodes
  )

  # Defensive cross-check: the explained pairwise total must equal the
  # optimizer's certified value.
  explained <- sum(pair_costs(res)$cost)
  if (explained != total_penalty(res)) {
    cli::cli_abort(
      "Internal error: explained penalty {explained} does not match certified \\
       optimum {total_penalty(res)}. No resolution is returned.",
      call = call
    )
  }

  res
}

# Input validation -----------------------------------------------------------

check_record_ids <- function(record_ids, call) {
  check_type(record_ids, is.atomic, "an atomic vector", call = call)
  if (length(record_ids) == 0L) {
    cli::cli_abort("`record_ids` must contain at least one id.", call = call)
  }
  if (anyNA(record_ids)) {
    cli::cli_abort("`record_ids` must not contain missing values.", call = call)
  }
  ids <- as.character(record_ids)
  if (anyDuplicated(ids) > 0L) {
    dup <- unique(ids[duplicated(ids)])
    cli::cli_abort(
      "`record_ids` must be unique. Duplicate id{?s}: {.val {utils::head(dup, 5L)}}.",
      call = call
    )
  }
  ids
}

check_max_nodes <- function(max_nodes, call) {
  if (!is.numeric(max_nodes) || length(max_nodes) != 1L ||
    !is.finite(max_nodes) || max_nodes < 1 ||
    abs(max_nodes - round(max_nodes)) > 0) {
    cli::cli_abort(
      "`max_nodes` must be a single positive whole number.",
      call = call
    )
  }
  as.integer(max_nodes)
}

check_penalties <- function(penalties, record_ids, call) {
  check_type(penalties, is.data.frame, "a data frame", call = call)
  required <- c("id1", "id2", "merge_penalty", "split_penalty")
  missing_cols <- setdiff(required, names(penalties))
  if (length(missing_cols) > 0L) {
    cli::cli_abort(
      "`penalties` is missing required column{?s}: {.val {missing_cols}}.",
      call = call
    )
  }

  n <- length(record_ids)
  expected_pairs <- (n * (n - 1L)) %/% 2L

  # With a single record there are no pairs; an empty penalty frame is the
  # only valid input and is handled directly.
  if (n == 1L) {
    if (nrow(penalties) != 0L) {
      cli::cli_abort(
        "`penalties` must be empty when there is only one record.",
        call = call
      )
    }
    return(tibble::tibble(
      id1 = character(), id2 = character(),
      merge_penalty = integer(), split_penalty = integer(),
      .pos_i = integer(), .pos_j = integer()
    ))
  }

  if (nrow(penalties) != expected_pairs) {
    cli::cli_abort(
      c(
        "`penalties` must contain exactly one row per unordered pair of \\
         records ({expected_pairs} pair{?s} for {n} record{?s}).",
        x = "Got {nrow(penalties)} row{?s}."
      ),
      call = call
    )
  }

  id_pos <- stats::setNames(seq_along(record_ids), record_ids)
  id1 <- as.character(penalties$id1)
  id2 <- as.character(penalties$id2)

  unknown <- setdiff(unique(c(id1, id2)), record_ids)
  if (length(unknown) > 0L) {
    cli::cli_abort(
      "`penalties` reference{?s an/} unknown record id{?s}: \\
       {.val {utils::head(unknown, 5L)}}.",
      call = call
    )
  }

  self <- id1 == id2
  if (any(self)) {
    cli::cli_abort(
      "`penalties` must only contain pairs of distinct records; \\
       self-pairs are not allowed.",
      call = call
    )
  }

  merge_penalty <- coerce_penalty(
    penalties$merge_penalty, "merge_penalty", call
  )
  split_penalty <- coerce_penalty(
    penalties$split_penalty, "split_penalty", call
  )

  # Canonicalize orientation so each pair is comparable, then check coverage.
  pos_i <- id_pos[id1]
  pos_j <- id_pos[id2]
  swap <- pos_i > pos_j
  tmp <- pos_i[swap]
  pos_i[swap] <- pos_j[swap]
  pos_j[swap] <- tmp
  tmp_id <- id1[swap]
  id1[swap] <- id2[swap]
  id2[swap] <- tmp_id

  pair_keys <- pos_i * (n + 1L) + pos_j
  if (anyDuplicated(pair_keys) > 0L) {
    cli::cli_abort(
      "Each unordered pair may appear in `penalties` exactly once; \\
       duplicate pairs were supplied.",
      call = call
    )
  }
  expected_keys <- {
    combos <- utils::combn(seq_len(n), 2L)
    combos[1L, ] * (n + 1L) + combos[2L, ]
  }
  if (!setequal(pair_keys, expected_keys)) {
    cli::cli_abort(
      "`penalties` must cover every unordered pair of records exactly once.",
      call = call
    )
  }

  tibble::tibble(
    id1 = id1,
    id2 = id2,
    merge_penalty = merge_penalty,
    split_penalty = split_penalty,
    .pos_i = pos_i,
    .pos_j = pos_j
  )
}

coerce_penalty <- function(x, col, call) {
  if (!is.numeric(x) || anyNA(x) || !all(is.finite(x))) {
    cli::cli_abort(
      "`{col}` must contain finite, non-missing numeric values.",
      call = call
    )
  }
  if (any(x < 0)) {
    cli::cli_abort(
      "`{col}` must be non-negative.",
      call = call
    )
  }
  if (any(abs(x - round(x)) > .Machine$double.eps^0.5)) {
    cli::cli_abort(
      "`{col}` must contain whole-number (integer) penalties.",
      call = call
    )
  }
  as.integer(round(x))
}

check_links <- function(links, record_ids, arg, call) {
  if (is.null(links)) {
    return(tibble::tibble(id1 = character(), id2 = character()))
  }
  check_type(links, is.data.frame, "a data frame", call = call)
  missing_cols <- setdiff(c("id1", "id2"), names(links))
  if (length(missing_cols) > 0L) {
    cli::cli_abort(
      "`{arg}` is missing required column{?s}: {.val {missing_cols}}.",
      call = call
    )
  }

  id1 <- as.character(links$id1)
  id2 <- as.character(links$id2)
  if (length(id1) == 0L) {
    return(tibble::tibble(id1 = character(), id2 = character()))
  }
  if (anyNA(id1) || anyNA(id2)) {
    cli::cli_abort("`{arg}` must not contain missing ids.", call = call)
  }
  unknown <- setdiff(unique(c(id1, id2)), record_ids)
  if (length(unknown) > 0L) {
    cli::cli_abort(
      "`{arg}` reference{?s an/} unknown record id{?s}: \\
       {.val {utils::head(unknown, 5L)}}.",
      call = call
    )
  }
  if (any(id1 == id2) && arg == "cannot_link") {
    cli::cli_abort(
      "A cannot-link cannot be declared between a record and itself.",
      call = call
    )
  }

  tibble::tibble(id1 = id1, id2 = id2)
}

# Construction and accessors -------------------------------------------------

build_resolution <- function(entity_id, record_ids, penalties, search_nodes) {
  res <- tibble::tibble(
    entity_id = as.integer(entity_id),
    record_id = record_ids
  )
  class(res) <- c("entity_resolution", class(res))

  attr(res, "record_ids") <- record_ids
  attr(res, "search_nodes") <- search_nodes
  attr(res, "n_entities") <- length(unique(entity_id))
  attr(res, "pair_costs") <- res_pair_costs_impl(res, penalties)
  attr(res, "total_penalty") <- sum(attr(res, "pair_costs")$cost)
  attr(res, "members") <- res_members_impl(res)

  res
}

res_pair_costs_impl <- function(res, penalties) {
  ent <- stats::setNames(res$entity_id, res$record_id)
  same <- ent[penalties$id1] == ent[penalties$id2]
  tibble::tibble(
    id1 = penalties$id1,
    id2 = penalties$id2,
    merge_penalty = penalties$merge_penalty,
    split_penalty = penalties$split_penalty,
    decision = ifelse(same, "merge", "split"),
    cost = ifelse(
      same, penalties$merge_penalty, penalties$split_penalty
    )
  )
}

res_members_impl <- function(res) {
  split_ids <- split(res$record_id, res$entity_id)
  entity_ids <- sort(unique(res$entity_id))
  tibble::tibble(
    entity_id = entity_ids,
    n_records = vapply(
      split_ids[as.character(entity_ids)], length, integer(1L)
    ),
    record_ids = unname(split_ids[as.character(entity_ids)])
  )
}

#' Extract per-pair cost explanations from an entity resolution
#'
#' @param x An `entity_resolution` object returned by [resolve_entities()].
#' @return A tibble with one row per input record pair, the two penalties, the
#'   decision taken (`"merge"` or `"split"`), and the integer cost incurred.
#' @family entity resolution
#' @export
pair_costs <- function(x) {
  check_entity_resolution(x)
  attr(x, "pair_costs")
}

#' Extract entity membership from an entity resolution
#'
#' @param x An `entity_resolution` object returned by [resolve_entities()].
#' @return A tibble with one row per entity: `entity_id`, `n_records`, and a
#'   list-column `record_ids` preserving the original id mapping.
#' @family entity resolution
#' @export
entity_members <- function(x) {
  check_entity_resolution(x)
  attr(x, "members")
}

#' Extract the certified minimal total penalty
#'
#' @param x An `entity_resolution` object returned by [resolve_entities()].
#' @return An integer total penalty of the returned partition.
#' @family entity resolution
#' @export
total_penalty <- function(x) {
  check_entity_resolution(x)
  attr(x, "total_penalty")
}

check_entity_resolution <- function(x, call = rlang::caller_env()) {
  if (!inherits(x, "entity_resolution")) {
    cli::cli_abort(
      "`x` must be an {.val entity_resolution} object from \\
       {.fn resolve_entities}.",
      call = call
    )
  }
}

#' @export
print.entity_resolution <- function(x, ...) {
  cat(
    glue::glue(
      "Entity resolution: {length(attr(x, 'record_ids'))} records -> ",
      "{attr(x, 'n_entities')} entit{if (attr(x, 'n_entities') == 1L) 'y' else 'ies'}; ",
      "minimum total penalty = {attr(x, 'total_penalty')} ",
      "(search nodes: {attr(x, 'search_nodes')}).\n"
    )
  )
  NextMethod()
  invisible(x)
}
