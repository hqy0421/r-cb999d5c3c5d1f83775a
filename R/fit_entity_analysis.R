# End-to-end entity-level analysis ------------------------------------------
#
# This wrapper runs the full, real infer pipeline on the aggregated entity
# population: the partition from `resolve_entities()`, the declared column
# aggregations from `aggregate_entities()`, then an actual `specify()` /
# `fit()` on the one-row-per-entity data. It never reuses a model fit on the
# pre-resolution records, and it reports exactly which entities entered the
# model and which were excluded (and why). If hard constraints are
# inconsistent, aggregation fails, or fitting fails, no new analysis
# population is published: the function errors instead of returning partial
# output.

#' Run the full infer pipeline on an entity-resolved population
#'
#' @description
#'
#' `fit_entity_analysis()` ties the entity-resolution workflow together. It
#' (1) re-runs [resolve_entities()] to obtain the exact optimal partition,
#' (2) applies the pre-declared `rules` with [aggregate_entities()] to build
#' one row per entity, (3) calls [specify()] and [fit()] **on that entity
#' table** with the supplied formula, and (4) reports the entities actually
#' included in and excluded from the fit. The model is genuinely fitted to the
#' new entity-level data; no model from the original records is reused, and no
#' grouping ids alone are returned.
#'
#' Failures are total: an inconsistent hard-constraint system, an aggregation
#' error, or a fitting error all raise an error before any new analysis
#' population is published.
#'
#' @inheritParams resolve_entities
#' @param data Source data frame containing `record_id` and every column named
#'   in `rules` and in `formula`.
#' @param rules Pre-declared aggregation rules, as in [aggregate_entities()].
#' @param formula A two-sided or one-sided formula passed to [specify()] on the
#'   entity table, e.g. `hours ~ age + college`.
#' @param record_id_col Name of the stable record id column in `data`.
#' @param success Optional success level for binary responses, passed to
#'   [specify()].
#' @param ... Additional arguments passed to [fit()] (e.g. `family`).
#'
#' @return A list of class `entity_analysis` with elements:
#'
#' * `resolution`: the [resolve_entities()] output;
#' * `entity_table`: the one-row-per-entity [aggregate_entities()] output;
#' * `fit`: the model fit on the entity table (real `specify()`/`fit()`
#'   output);
#' * `included`: tibble of entities that entered the fit with their member
#'   record ids;
#' * `excluded`: tibble of entities dropped before fitting (e.g. due to
#'   missing values) with a `reason`;
#' * `audit`: counts and the certified minimum total penalty.
#'
#' @family entity resolution
#' @export
#' @examples
#' ids <- c("a", "b", "c", "d")
#' penalties <- tibble::tribble(
#'   ~id1, ~id2, ~merge_penalty, ~split_penalty,
#'   "a", "b", 1L, 9L,
#'   "a", "c", 8L, 2L,
#'   "a", "d", 8L, 2L,
#'   "b", "c", 8L, 2L,
#'   "b", "d", 8L, 2L,
#'   "c", "d", 1L, 9L
#' )
#' df <- tibble::tibble(
#'   record_id = ids,
#'   age = c(25, 27, 60, 62),
#'   hours = c(40, 42, 30, 28)
#' )
#'
#' \dontrun{
#' fit_entity_analysis(
#'   record_ids = ids,
#'   penalties = penalties,
#'   data = df,
#'   rules = list(age = "mean", hours = "mean"),
#'   formula = hours ~ age
#' )
#' }
fit_entity_analysis <- function(
  record_ids,
  penalties,
  data,
  rules,
  formula,
  must_link = NULL,
  cannot_link = NULL,
  record_id_col = "record_id",
  success = NULL,
  max_nodes = 100000L,
  ...
) {
  call <- rlang::current_env()

  if (!rlang::is_formula(formula)) {
    cli::cli_abort("`formula` must be a formula.", call = call)
  }

  # Stage 1: exact resolution. Hard-constraint contradictions abort here,
  # before any population is built.
  resolution <- resolve_entities(
    record_ids = record_ids,
    penalties = penalties,
    must_link = must_link,
    cannot_link = cannot_link,
    max_nodes = max_nodes
  )

  # Stage 2: declared aggregation. Type/rule failures abort here.
  entity_table <- aggregate_entities(
    resolution = resolution,
    data = data,
    rules = rules,
    record_id_col = record_id_col
  )

  formula_vars <- all.vars(formula)
  absent <- setdiff(formula_vars, names(entity_table))
  if (length(absent) > 0L) {
    cli::cli_abort(
      "Formula variable{?s} {.val {absent}} not found in the aggregated \\
       entity table. Declare aggregation rules for every modeled column.",
      call = call
    )
  }

  # Stage 3: record inclusion/exclusion against the modeling columns. Entities
  # with missing modeled values cannot enter the fit; the rest do. Exclusion
  # is reported, never silent.
  model_frame <- entity_table[, formula_vars, drop = FALSE]
  complete <- stats::complete.cases(model_frame)
  included_ids <- entity_table$entity_id[complete]
  excluded_ids <- entity_table$entity_id[!complete]

  member_lookup <- entity_members(resolution)

  excluded <- if (length(excluded_ids) == 0L) {
    tibble::tibble(
      entity_id = integer(),
      n_records = integer(),
      record_ids = list(),
      reason = character()
    )
  } else {
    reasons <- vapply(
      excluded_ids,
      function(eid) {
        row <- which(entity_table$entity_id == eid)
        miss <- formula_vars[
          vapply(model_frame[row, ], is.na, logical(1L))
        ]
        paste0(
          "missing modeled value(s): ", paste(miss, collapse = ", ")
        )
      },
      character(1L)
    )
    ex <- member_lookup[
      member_lookup$entity_id %in% excluded_ids, , drop = FALSE
    ]
    ex$reason <- reasons
    ex
  }

  included <- member_lookup[
    member_lookup$entity_id %in% included_ids, , drop = FALSE
  ]

  if (length(included_ids) == 0L) {
    cli::cli_abort(
      "No entities remain after excluding incomplete rows; cannot fit a \\
       model. No analysis population is published.",
      call = call
    )
  }

  fit_data <- entity_table[complete, , drop = FALSE]

  # Stage 4: the real, current fit on the entity-level population.
  fitted <- tryCatch(
    fit_data |>
      specify(formula = formula, success = success) |>
      fit(...),
    error = function(e) {
      cli::cli_abort(
        c(
          "Fitting the model to the entity-level population failed.",
          x = conditionMessage(e)
        ),
        call = call
      )
    }
  )

  structure(
    list(
      resolution = resolution,
      entity_table = entity_table,
      fit = fitted,
      included = included,
      excluded = excluded,
      audit = list(
        n_records = length(attr(resolution, "record_ids")),
        n_entities = attr(resolution, "n_entities"),
        n_included = length(included_ids),
        n_excluded = length(excluded_ids),
        minimum_total_penalty = total_penalty(resolution),
        search_nodes = attr(resolution, "search_nodes"),
        formula = deparse(formula)
      )
    ),
    class = "entity_analysis"
  )
}

#' @export
print.entity_analysis <- function(x, ...) {
  a <- x$audit
  cat(
    glue::glue(
      "Entity analysis\n",
      "  records resolved : {a$n_records}\n",
      "  entities formed  : {a$n_entities} (minimum total penalty ",
      "{a$minimum_total_penalty})\n",
      "  entities in fit  : {a$n_included}\n",
      "  entities excluded: {a$n_excluded}\n",
      "  formula          : {a$formula}\n"
    )
  )
  print(x$fit)
  invisible(x)
}
