# Entity-level column aggregation -------------------------------------------
#
# A resolution only says *which* records belong together. Turning records into
# one row per entity requires an explicit, pre-declared aggregation rule for
# every output column. Rules never inspect response values to decide the
# partition; they merely summarize the records already assigned to an entity.

# Built-in rule implementations. Each takes a column vector (the member
# records of one entity) and returns a length-1 atomic value whose storage
# type is asserted afterwards.
entity_agg_rules <- function() {
  list(
    # numeric summaries
    mean = numeric_rule(
      function(v) mean(v, na.rm = FALSE), "numeric"
    ),
    sum = numeric_rule(function(v) sum(v), "numeric"),
    median = numeric_rule(function(v) stats::median(v), "numeric"),
    min = numeric_rule(function(v) min(v), "numeric"),
    max = numeric_rule(function(v) max(v), "numeric"),
    sd = numeric_rule(
      function(v) stats::sd(v), "numeric"
    ),
    n = function(v) length(v),
    # categorical / identity summaries
    first = function(v) v[[1L]],
    last = function(v) v[[length(v)]],
    mode = function(v) {
      tab <- table(v, useNA = "no")
      if (length(tab) == 0L) {
        cli::cli_abort(
          "Cannot compute the modal value of an all-missing member column."
        )
      }
      # deterministic tie break: most frequent, then first in sort order
      winners <- names(tab)[tab == max(tab)]
      sort(winners)[[1L]]
    },
    collapse = function(v) {
      paste(sort(unique(as.character(v))), collapse = ",")
    }
  )
}

numeric_rule <- function(fn, ptype) {
  function(v) {
    if (!is.numeric(v)) {
      cli::cli_abort(
        "This aggregation rule requires a numeric source column, got \\
         {.val {class(v)[[1L]]}}."
      )
    }
    as.numeric(fn(v))
  }
}

#' Aggregate resolved records into one row per entity
#'
#' @description
#'
#' `aggregate_entities()` applies a pre-declared aggregation rule to each
#' requested source column for every entity produced by [resolve_entities()],
#' yielding a type-checked tibble with exactly one row per entity. Rules are
#' declared up front and operate only on the member records of an entity; they
#' cannot alter the partition and never select entities based on response
#' values.
#'
#' Named rules: `"mean"`, `"sum"`, `"median"`, `"min"`, `"max"`, `"sd"`,
#' `"n"` (member count), `"first"`, `"last"`, `"mode"` (most frequent value,
#' ties broken alphabetically), and `"collapse"` (sorted unique values joined
#' by commas). A rule may also be a function `function(values) length-1 value`.
#'
#' @param resolution An `entity_resolution` object from [resolve_entities()].
#' @param data A data frame containing the source columns. It must include the
#'   `record_id` column used to build the resolution.
#' @param rules A named list mapping output column names to aggregation rules.
#'   A rule is a built-in rule name (string) or a function. Every element must
#'   be named, every source column referenced must exist, and each rule must
#'   return a single atomic value of a consistent type across all entities.
#' @param record_id_col Name of the column in `data` holding the stable record
#'   ids used in the resolution, as a string.
#'
#' @return An `entity_table` tibble with one row per entity, an integer
#'   `entity_id` column followed by `n_records` and the declared output
#'   columns. The original id mapping and membership remain available via
#'   [entity_members()].
#'
#' @family entity resolution
#' @export
#' @examples
#' ids <- c("a", "b", "c")
#' penalties <- tibble::tibble(
#'   id1 = c("a", "a", "b"),
#'   id2 = c("b", "c", "c"),
#'   merge_penalty = c(1L, 8L, 8L),
#'   split_penalty = c(9L, 2L, 2L)
#' )
#' res <- resolve_entities(ids, penalties)
#'
#' df <- tibble::tibble(
#'   record_id = ids,
#'   age = c(30, 32, 80),
#'   city = c("NYC", "NYC", "LA")
#' )
#'
#' aggregate_entities(
#'   res, df,
#'   rules = list(avg_age = "mean", home_city = "mode", ages_seen = "collapse")
#' )
aggregate_entities <- function(
  resolution,
  data,
  rules,
  record_id_col = "record_id"
) {
  call <- rlang::current_env()
  check_entity_resolution(resolution, call)
  check_type(data, is.data.frame, "a data frame", call = call)
  check_rules_arg(rules, call)

  if (!rlang::is_string(record_id_col) ||
    !(record_id_col %in% names(data))) {
    cli::cli_abort(
      "`record_id_col` must name a column in `data`; got {.val {record_id_col}}.",
      call = call
    )
  }

  data <- tibble::as_tibble(data)
  data_ids <- as.character(data[[record_id_col]])
  known <- attr(resolution, "record_ids")
  unknown <- setdiff(data_ids, known)
  if (length(unknown) > 0L) {
    cli::cli_abort(
      "`data` contains record ids absent from the resolution: \\
       {.val {utils::head(unknown, 5L)}}.",
      call = call
    )
  }
  if (anyDuplicated(data_ids) > 0L) {
    cli::cli_abort(
      "The record id column in `data` must be unique (one row per record).",
      call = call
    )
  }
  missing_rows <- setdiff(known, data_ids)
  if (length(missing_rows) > 0L) {
    cli::cli_abort(
      "`data` is missing rows for record id{?s} in the resolution: \\
       {.val {utils::head(missing_rows, 5L)}}.",
      call = call
    )
  }

  rule_fns <- lapply(
    stats::setNames(names(rules), names(rules)),
    function(out_name) compile_rule(rules[[out_name]], out_name, call)
  )
  source_cols <- lapply(rule_fns, function(r) attr(r, "source_col"))

  # Validate source columns up front.
  for (out_name in names(rules)) {
    src <- source_cols[[out_name]]
    if (!is.null(src) && !(src %in% names(data))) {
      cli::cli_abort(
        "Rule for output column {.val {out_name}} references missing source \\
         column {.val {src}}.",
        call = call
      )
    }
  }

  # Align data rows to the resolution's record order and attach entity ids.
  pos <- stats::setNames(seq_len(nrow(data)), data_ids)
  aligned <- data[pos[known], , drop = FALSE]
  aligned$entity_id <- resolution$entity_id

  members <- entity_members(resolution)
  out <- members[, c("entity_id", "n_records")]

  for (out_name in names(rule_fns)) {
    fn <- rule_fns[[out_name]]
    src <- source_cols[[out_name]]
    # Rules without a source column (currently only `n`) summarize membership
    # itself; everything else reads the declared source column.
    if (is.null(src)) {
      src <- record_id_col
    }
    if (!(src %in% names(aligned))) {
      cli::cli_abort(
        "Rule for output column {.val {out_name}} references missing source \\
         column {.val {src}}.",
        call = call
      )
    }
    col_vec <- aligned[[src]]

    # Probe the first entity to learn the output storage type, so the result
    # vector is pre-allocated with the correct mode (custom functions have no
    # declared ptype).
    first_vals <- col_vec[
      aligned$record_id %in% members$record_ids[[1L]]
    ]
    first_result <- fn(first_vals)
    check_scalar_atomic(first_result, out_name, call)
    values <- vector(mode = storage_mode(first_result), length = nrow(members))
    values[[1L]] <- first_result

    for (e in seq_len(nrow(members))[-1L]) {
      vals <- col_vec[aligned$record_id %in% members$record_ids[[e]]]
      result <- fn(vals)
      check_scalar_atomic(result, out_name, call)
      if (!identical(class(result)[[1L]], class(first_result)[[1L]])) {
        cli::cli_abort(
          "Output column {.val {out_name}} has inconsistent element types; \\
           each entity must produce the same type.",
          call = call
        )
      }
      values[[e]] <- result
    }
    out[[out_name]] <- values
  }

  out <- enforce_output_types(out, rules, rule_fns, call)

  class(out) <- c("entity_table", class(out))
  attr(out, "resolution") <- resolution
  attr(out, "record_id_col") <- record_id_col
  out
}

check_rules_arg <- function(rules, call) {
  check_type(rules, is.list, "a list", call = call)
  if (length(rules) == 0L) {
    cli::cli_abort(
      "`rules` must declare at least one output column aggregation.",
      call = call
    )
  }
  if (is.null(names(rules)) || any(names(rules) == "")) {
    cli::cli_abort(
      "Every element of `rules` must be named with its output column name.",
      call = call
    )
  }
  if (anyDuplicated(names(rules)) > 0L) {
    cli::cli_abort("Output column names in `rules` must be unique.", call = call)
  }
  reserved <- c("entity_id", "n_records")
  clash <- intersect(names(rules), reserved)
  if (length(clash) > 0L) {
    cli::cli_abort(
      "Output column name{?s} {.val {clash}} {?is/are} reserved.",
      call = call
    )
  }
}

# Resolve a rule specification into a function, tagging it with the source
# column it consumes. Rules are either:
#   * a bare built-in name, e.g. "mean"
#   * a named list(rule = <name or fn>, column = <source column>)
#   * a function (source column defaults to the output column name)
compile_rule <- function(rule, out_name, call) {
  builtins <- entity_agg_rules()

  if (rlang::is_string(rule)) {
    if (!(rule %in% names(builtins))) {
      cli::cli_abort(
        "Unknown aggregation rule {.val {rule}} for {.val {out_name}}. \\
         Built-ins: {.val {names(builtins)}}.",
        call = call
      )
    }
    fn <- builtins[[rule]]
    attr(fn, "source_col") <- if (rule == "n") NULL else out_name
    attr(fn, "ptype") <- rule_ptype(rule)
    return(fn)
  }

  if (is.function(rule)) {
    attr(rule, "source_col") <- out_name
    attr(rule, "ptype") <- NULL
    return(rule)
  }

  if (is.list(rule) && all(c("rule", "column") %in% names(rule))) {
    inner <- rule$rule
    src <- rule$column
    if (!rlang::is_string(src)) {
      cli::cli_abort(
        "Rule {.val {out_name}}: `column` must be a single string.",
        call = call
      )
    }
    if (rlang::is_string(inner)) {
      if (!(inner %in% names(builtins))) {
        cli::cli_abort(
          "Unknown aggregation rule {.val {inner}} for {.val {out_name}}.",
          call = call
        )
      }
      fn <- builtins[[inner]]
      attr(fn, "ptype") <- rule_ptype(inner)
    } else if (is.function(inner)) {
      fn <- inner
      attr(fn, "ptype") <- NULL
    } else {
      cli::cli_abort(
        "Rule {.val {out_name}}: `rule` must be a built-in name or function.",
        call = call
      )
    }
    attr(fn, "source_col") <- src
    return(fn)
  }

  cli::cli_abort(
    "Rule for {.val {out_name}} must be a built-in name, a function, or a \\
     list with `rule` and `column`.",
    call = call
  )
}

rule_ptype <- function(name) {
  switch(
    name,
    mean = ,
    sum = ,
    median = ,
    min = ,
    max = ,
    sd = "numeric",
    n = "integer",
    "character"
  )
}

# vapply template: retained for documentation of built-in output types;
# custom functions are probed per entity at call time.
vector_of_ptype <- function(fn) {
  ptype <- attr(fn, "ptype")
  if (identical(ptype, "integer")) {
    return(integer(1L))
  }
  if (identical(ptype, "numeric")) {
    return(numeric(1L))
  }
  character(1L)
}

check_scalar_atomic <- function(result, out_name, call) {
  if (!is.atomic(result) || !is.null(dim(result)) || length(result) != 1L) {
    cli::cli_abort(
      "Aggregation of {.val {out_name}} must return a single atomic value \\
       per entity.",
      call = call
    )
  }
}

storage_mode <- function(x) {
  if (is.integer(x)) {
    return("integer")
  }
  if (is.numeric(x)) {
    return("double")
  }
  if (is.logical(x)) {
    return("logical")
  }
  "character"
}

# Assert every declared output column is atomic and length-consistent; coerce
# numeric built-ins explicitly so their types are guaranteed.
enforce_output_types <- function(out, rules, rule_fns, call) {
  for (out_name in names(rules)) {
    v <- out[[out_name]]
    if (!is.atomic(v) || !is.null(dim(v))) {
      cli::cli_abort(
        "Aggregation of {.val {out_name}} did not return an atomic vector.",
        call = call
      )
    }
    if (length(v) != nrow(out)) {
      cli::cli_abort(
        "Aggregation of {.val {out_name}} should return one value per entity \\
         but got length {length(v)} for {nrow(out)} entities.",
        call = call
      )
    }
    ptype <- attr(rule_fns[[out_name]], "ptype")
    if (identical(ptype, "numeric") && !is.numeric(v)) {
      cli::cli_abort(
        "Output column {.val {out_name}} must be numeric.",
        call = call
      )
    }
    if (identical(ptype, "integer") && !is.integer(v)) {
      storage.mode(v) <- "integer"
      out[[out_name]] <- v
    }
  }
  out
}

#' @export
print.entity_table <- function(x, ...) {
  res <- attr(x, "resolution")
  cat(
    glue::glue(
      "Entity table: one row per entity ({nrow(x)} entit{if (nrow(x) == 1L) 'y' else 'ies'}, ",
      "{length(attr(res, 'record_ids'))} source records).\n"
    )
  )
  NextMethod()
  invisible(x)
}
