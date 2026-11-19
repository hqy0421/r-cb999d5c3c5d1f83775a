# Exact entity resolution solver ---------------------------------------------
#
# Given pairwise merge/split integer penalties and hard must-link /
# cannot-link constraints, find a partition of the records that:
#
#   * respects every hard constraint,
#   * minimizes the total pairwise penalty (correlation clustering objective),
#
# exactly. This is the "minimum penalty correlation clustering" problem, which
# is NP-hard, so a branch-and-bound search is used. There is no threshold, no
# connected-components shortcut and no greedy approximation: the returned
# partition is certified globally optimal (one of possibly several optima).
#
# The search operates on "blocks" produced by closing the must-link relation
# under transitivity. Must-link is an equivalence relation, so every block is
# forced into one entity. Cannot-links forbid two blocks sharing an entity.

# Union-find (disjoint set union) over integer positions 1..n.
uf_make <- function(n) {
  parent <- seq_len(n)
  size <- rep(1L, n)
  list(parent = parent, size = size)
}

uf_find <- function(uf, x) {
  parent <- uf$parent
  root <- x
  while (parent[[root]] != root) {
    root <- parent[[root]]
  }
  # path compression
  while (parent[[x]] != x) {
    nxt <- parent[[x]]
    parent[[x]] <- root
    x <- nxt
  }
  uf$parent <- parent
  root
}

# Returns FALSE if the union would contradict an existing structure; here the
# union-find never self-contradicts, so this always succeeds. Kept as a
# function for readability of the preprocessing stage.
uf_union <- function(uf, x, y) {
  rx <- uf_find(uf, x)
  ry <- uf_find(uf, y)
  if (rx == ry) {
    return(uf)
  }
  if (uf$size[[rx]] < uf$size[[ry]]) {
    tmp <- rx
    rx <- ry
    ry <- tmp
  }
  uf$parent[[ry]] <- rx
  uf$size[[rx]] <- uf$size[[rx]] + uf$size[[ry]]
  uf
}

# Close must-links under transitivity, returning integer block labels
# (1..number of blocks) aligned with `ids`.
collapse_must_links <- function(ids, must_link) {
  n <- length(ids)
  uf <- uf_make(n)
  id_pos <- stats::setNames(seq_len(n), ids)

  if (!is.null(must_link) && nrow(must_link) > 0L) {
    for (k in seq_len(nrow(must_link))) {
      i <- id_pos[[must_link[[1L]][[k]]]]
      j <- id_pos[[must_link[[2L]][[k]]]]
      uf <- uf_union(uf, i, j)
    }
  }

  roots <- vapply(seq_len(n), function(k) uf_find(uf, k), integer(1L))
  # deterministic labels ordered by the smallest original position in each block
  block_id <- match(roots, unique(roots))
  list(block = as.integer(block_id), n_blocks = length(unique(roots)))
}

# Build block-level penalty matrices by summing record-pair penalties across
# every pair of records belonging to distinct blocks. Pairs inside a block are
# forced merges and are accounted for separately.
build_block_costs <- function(penalty, block, n_blocks, n) {
  merge_cost <- matrix(0L, n_blocks, n_blocks)
  split_cost <- matrix(0L, n_blocks, n_blocks)

  if (nrow(penalty) > 0L) {
    bi <- block[penalty$.pos_i]
    bj <- block[penalty$.pos_j]
    cross <- bi != bj

    if (any(cross)) {
      # Aggregate per ordered block pair. Matrix assignment with repeated
      # indices would silently drop additions, so summarize explicitly with
      # tapply, then symmetrize: every record pair between two blocks is
      # counted once regardless of orientation.
      lin <- (bj[cross] - 1L) * n_blocks + bi[cross]
      agg <- function(vals) {
        m <- matrix(0L, n_blocks, n_blocks)
        sums <- tapply(vals, lin, sum)
        idx <- as.integer(names(sums))
        m[idx] <- as.integer(sums)
        m + t(m)
      }
      merge_cost <- agg(penalty$merge_penalty[cross])
      split_cost <- agg(penalty$split_penalty[cross])
    }
  }

  list(merge_cost = merge_cost, split_cost = split_cost)
}

# Penalty incurred by record pairs that are forced together inside must-link
# blocks (they cannot be split, so merge penalties always apply).
forced_within_cost <- function(penalty, block) {
  if (nrow(penalty) == 0L) {
    return(0L)
  }
  same <- block[penalty$.pos_i] == block[penalty$.pos_j]
  sum(penalty$merge_penalty[same])
}

# Translate record-level cannot-links into an undirected graph over blocks.
# Throws an informative error if a cannot-link is contradicted by a must-link.
build_cannot_graph <- function(cannot_link, block, ids, call) {
  n_blocks <- length(unique(block))
  forbidden <- matrix(FALSE, n_blocks, n_blocks)
  if (is.null(cannot_link) || nrow(cannot_link) == 0L) {
    return(forbidden)
  }

  id_pos <- stats::setNames(seq_along(ids), ids)
  for (k in seq_len(nrow(cannot_link))) {
    i <- id_pos[[cannot_link[[1L]][[k]]]]
    j <- id_pos[[cannot_link[[2L]][[k]]]]
    bi <- block[[i]]
    bj <- block[[j]]
    if (bi == bj) {
      cli::cli_abort(
        c(
          "Hard constraints are inconsistent.",
          x = paste0(
            "Records {.val {cannot_link[[1L]][[k]]}} and ",
            "{.val {cannot_link[[2L]][[k]]}} carry a cannot-link but are ",
            "forced together by must-link constraints (transitive closure)."
          )
        ),
        call = call
      )
    }
    forbidden[[bi, bj]] <- TRUE
    forbidden[[bj, bi]] <- TRUE
  }
  forbidden
}

# Exact branch-and-bound over block-to-entity assignments.
#
# Blocks are processed in fixed order 1..B. A state assigns each processed
# block to a cluster id; cluster ids are reused across branches. For each
# unprocessed block we branch on every existing (allowed) cluster plus a fresh
# cluster. The lower bound is the sum, over every not-yet-decided block pair,
# of the cheaper of its merge and split penalties, plus the best-case cost of
# attaching each pending block to an already-open cluster. It is an
# admissible (never over-estimating) bound, so pruning never discards an
# optimum.
solve_bb <- function(
  merge_cost,
  split_cost,
  forbidden,
  n_blocks,
  within_cost,
  max_nodes,
  call
) {
  # Trivial case: every block is forced into the single entity.
  if (n_blocks == 1L) {
    return(list(assign = 1L, cost = within_cost, nodes = 1L))
  }

  # Per-pair cheapest possible cost used in the admissible lower bound.
  min_pair <- pmin(merge_cost, split_cost)

  # Prefix row sums: prefix_*[b, k] = sum of row b over columns 1..k. These
  # turn the per-node cluster-attachment and lower-bound arithmetic into
  # vectorized lookups rather than nested R loops.
  prefix_split <- row_prefix_sums(split_cost)
  prefix_min <- row_prefix_sums(min_pair)

  # Deterministic feasible incumbent: assign blocks in order to the cheapest
  # legal option (an existing cluster, or a fresh cluster). This is only a
  # starting upper bound; the search proves optimality and may replace it.
  incumbent <- greedy_seed(
    merge_cost, split_cost, forbidden, n_blocks, prefix_split
  )
  best_cost <- incumbent$cost
  best_assign <- incumbent$assign

  nodes <- 0L

  # Each stack frame: list(assign = integer vector of cluster labels for
  # blocks 1..k, k = number of assigned blocks, realized = cost already fixed
  # among assigned blocks).
  stack <- list(list(assign = 1L, k = 1L, realized = 0L))

  while (length(stack) > 0L) {
    nodes <- nodes + 1L
    if (nodes > max_nodes) {
      cli::cli_abort(
        c(
          "Entity resolution search exceeded its node budget of \\
           {format(max_nodes, big.mark = ',')} without proving optimality.",
          i = "The problem is NP-hard; raise `max_nodes` or supply tighter \\
               constraints. No approximate partition is returned."
        ),
        call = call
      )
    }

    frame <- stack[[length(stack)]]
    stack[[length(stack)]] <- NULL
    assign <- frame$assign
    k <- frame$k
    realized <- frame$realized

    # Lower bound for this partial assignment.
    lb <- bb_lower_bound(
      assign, k, n_blocks, merge_cost, split_cost, prefix_split, prefix_min,
      forbidden, realized
    )
    if (lb >= best_cost) {
      next
    }

    if (k == n_blocks) {
      # Complete assignment. `realized` already holds the full objective.
      if (realized < best_cost) {
        best_cost <- realized
        best_assign <- assign
      }
      next
    }

    next_block <- k + 1L
    open_clusters <- unique(assign)
    split_total <- prefix_split[next_block, k]

    # Candidate destination clusters: every open cluster not forbidden, plus a
    # brand new cluster. For cluster c with members M among 1..k:
    #   delta = sum_M merge + sum_(1..k \\ M) split
    #         = sum_M (merge - split) + sum_(1..k) split
    merge_minus_split <- merge_cost[next_block, seq_len(k)] -
      split_cost[next_block, seq_len(k)]

    candidates <- integer(0L)
    merge_delta <- integer(0L)
    for (c in open_clusters) {
      members <- which(assign == c)
      if (any(forbidden[next_block, members])) {
        next
      }
      delta <- split_total + sum(merge_minus_split[members])
      candidates <- c(candidates, c)
      merge_delta <- c(merge_delta, delta)
    }
    # fresh cluster: next_block is split from every assigned block
    candidates <- c(candidates, max(open_clusters) + 1L)
    merge_delta <- c(merge_delta, split_total)

    # Explore the cheapest branch first (best-first ordering tightens the
    # incumbent quickly, which makes pruning more effective). Ties keep the
    # smallest cluster id so the result is deterministic.
    ord <- order(merge_delta, candidates)
    for (idx in rev(ord)) {
      c <- candidates[[idx]]
      stack[[length(stack) + 1L]] <- list(
        assign = c(assign, c),
        k = next_block,
        realized = realized + merge_delta[[idx]]
      )
    }
  }

  list(
    assign = best_assign,
    cost = best_cost + within_cost,
    nodes = nodes
  )
}

row_prefix_sums <- function(m) {
  t(apply(m, 1L, cumsum))
}

# Admissible lower bound for a partial assignment.
bb_lower_bound <- function(
  assign,
  k,
  n_blocks,
  merge_cost,
  split_cost,
  prefix_split,
  prefix_min,
  forbidden,
  realized
) {
  if (k == n_blocks) {
    return(realized)
  }
  pending <- (k + 1L):n_blocks

  # (1) Pairs among pending blocks: relax to the cheaper option per pair.
  #     Sum the min-cost rows over the pending columns once each and halve.
  pending_min <- if (length(pending) >= 2L) {
    sum(prefix_min[pending, n_blocks] - prefix_min[pending, k]) %/% 2L
  } else {
    0L
  }

  # (2) Each pending block must either join one open cluster or be split from
  #     the whole prefix. The minimum realizable attachment cost is a
  #     relaxation that never exceeds the true branch cost, so the bound stays
  #     admissible. Using the merge/split identity
  #       sum_M merge + sum_(prefix\\M) split
  #         = sum_prefix split + sum_M (merge - split)
  open_clusters <- unique(assign)
  prefix_idx <- seq_len(k)
  attach <- 0L
  for (b in pending) {
    split_total <- prefix_split[b, k]
    best <- split_total # split from every prefix block
    gap <- merge_cost[b, prefix_idx] - split_cost[b, prefix_idx]
    for (c in open_clusters) {
      members <- which(assign == c)
      if (any(forbidden[b, members])) {
        next
      }
      cand <- split_total + sum(gap[members])
      if (cand < best) {
        best <- cand
      }
    }
    attach <- attach + best
  }

  realized + pending_min + attach
}

# Feasible deterministic seed assignment (greedy; used only as an initial
# upper bound, never as the answer).
greedy_seed <- function(
  merge_cost, split_cost, forbidden, n_blocks, prefix_split
) {
  assign <- integer(n_blocks)
  assign[[1L]] <- 1L
  realized <- 0L

  for (b in 2:n_blocks) {
    k <- b - 1L
    open_clusters <- unique(assign[seq_len(k)])
    best_c <- NA_integer_
    best_delta <- Inf
    split_total <- prefix_split[b, k]
    gap <- merge_cost[b, seq_len(k)] - split_cost[b, seq_len(k)]

    for (c in open_clusters) {
      members <- which(assign[seq_len(k)] == c)
      if (any(forbidden[b, members])) {
        next
      }
      delta <- split_total + sum(gap[members])
      if (delta < best_delta ||
        (isTRUE(delta == best_delta) && isTRUE(c < best_c))) {
        best_delta <- delta
        best_c <- c
      }
    }
    fresh_delta <- split_total
    if (fresh_delta < best_delta || is.na(best_c)) {
      best_delta <- fresh_delta
      best_c <- max(open_clusters) + 1L
    }
    assign[[b]] <- best_c
    realized <- realized + best_delta
  }

  list(assign = assign, cost = realized)
}

# Relabel cluster labels into dense, deterministic entity ids ordered by the
# smallest block (and hence smallest original record position) they contain.
relabel_entities <- function(assign) {
  first_block <- tapply(seq_along(assign), assign, min)
  old <- names(sort(first_block))
  new_id <- stats::setNames(seq_along(old), old)
  as.integer(new_id[as.character(assign)])
}
