use aiken/collection/dict
use aiken/collection/list
use aiken/collection/pairs
use aiken/fuzz
use aiken/primitive/bytearray
use cardano/assets.{AssetName}
use cardano/fuzz as cardano
use tokens.{Tokens}

// -------------------------------------------------------------- fuzzers

fn any_tokens() -> Fuzzer<Tokens> {
  let tokens <- fuzz.map(fuzz.list_between(any_token(), 0, 3))
  dict.from_pairs(tokens)
}

/// Quantities are >= 1 since the van Rossem rewire: `tokens.contains` is now
/// the `valueContains` builtin, which has no representation for a zero
/// quantity and rejects one fail-closed.
///
/// The bound was `0`, and dropping the zero draw is the ONE behavioural
/// narrowing of that rewire, so it is stated rather than buried:
///
///   * A zero-quantity token map is not constructible from ledger data (the
///     ledger emits no zero quantities) and `tokens.union` cannot produce one
///     (a name summing to zero is dropped, before and after).
///   * Where the two implementations disagree, the new one ABORTS on an input
///     the old one accepted. That is fail-closed: the divergence can only
///     refuse a transaction, never admit one. For a validator holding custody
///     of other people's tokens that is the correct side to err on.
///
/// `contains_aborts_on_a_zero_quantity` below pins this, so the narrowing is
/// tested rather than merely asserted here.
fn any_token() -> Fuzzer<Pair<AssetName, Int>> {
  let asset_name <- fuzz.and_then(cardano.asset_name())
  let quantity <- fuzz.map(fuzz.int_between(1, 3))
  Pair(asset_name, quantity)
}

fn any_mutation() -> Fuzzer<Mutation> {
  let ix <- fuzz.and_then(fuzz.byte())
  let quantity <- fuzz.and_then(fuzz.int_between(1, 3))
  let name <- fuzz.and_then(cardano.asset_name())
  fuzz.one_of(
    [
      ReduceQuantity(ix, quantity),
      IncreaseQuantity(ix, quantity),
      InsertAsset(Pair(name, quantity)),
      DeleteAsset(ix),
    ],
  )
}

type Mutation {
  ReduceQuantity(Int, Int)
  IncreaseQuantity(Int, Int)
  InsertAsset(Pair<AssetName, Int>)
  DeleteAsset(Int)
}

// Invariant: assume 'tokens' is not empty.
fn apply_mutation(mutation: Mutation, pairs: Pairs<AssetName, Int>) {
  let len = list.length(pairs)
  when mutation is {
    ReduceQuantity(ix, n) | IncreaseQuantity(ix, n) -> {
      let prefix = list.take(pairs, ix % len)
      expect [Pair(name, quantity), ..tail] = list.drop(pairs, ix % len)
      let new_quantity = if mutation == ReduceQuantity(ix, n) {
        quantity - n
      } else {
        quantity + n
      }
      list.concat(prefix, [Pair(name, new_quantity), ..tail])
    }
    InsertAsset(Pair(name, quantity)) ->
      pairs.insert_with_by_ascending_key(
        pairs,
        name,
        quantity,
        bytearray.compare,
        fn(left, right) { left + right },
      )
    DeleteAsset(ix) -> {
      let prefix = list.take(pairs, ix % len)
      expect [_, ..tail] = list.drop(pairs, ix % len)
      list.concat(prefix, tail)
    }
  }
}

// ------------------------------------------------------------- contains

const fixture_asset_name: AssetName = #"746f6b656e"

const fixture_superset: Pairs<AssetName, Int> = [Pair(fixture_asset_name, 100)]

const fixture_superset_with_ada: Pairs<AssetName, Int> =
  [Pair(fixture_asset_name, 100)]

const fixture_subset: Pairs<AssetName, Int> = [Pair(fixture_asset_name, 50)]

test tokens_exact_match() {
  tokens.contains(fixture_superset, fixture_superset)
}

test tokens_subset() {
  and {
    tokens.contains(fixture_superset, fixture_subset)?,
    tokens.contains(fixture_superset_with_ada, fixture_subset)?,
  }
}

test tokens_insufficient() {
  !tokens.contains(fixture_subset, fixture_superset)
}

test prop_contains_reflexive(tokens via any_tokens()) {
  tokens.contains(dict.to_pairs(tokens), dict.to_pairs(tokens))
}

test prop_contains_monoid(tokens via any_tokens()) {
  tokens.contains(dict.to_pairs(tokens), [])
}

test prop_contains_subset_mutation(
  (superset, mutation) via fuzz.both(any_tokens(), any_mutation()),
) fail {
  let superset = dict.to_pairs(superset)
  if superset != [] {
    let subset = apply_mutation(mutation, superset)
    when mutation is {
      IncreaseQuantity(..) -> {
        fuzz.label(@"non-empty superset, increase quantity")
        tokens.contains(superset, subset)
      }
      InsertAsset(..) -> {
        fuzz.label(@"non-empty superset, insert new asset")
        tokens.contains(superset, subset)
      }
      ReduceQuantity(..) -> {
        fuzz.label(@"non-empty superset, reduce quantity")
        !tokens.contains(superset, subset)
      }
      DeleteAsset(..) -> {
        fuzz.label(@"non-empty superset, remove asset")
        !tokens.contains(superset, subset)
      }
    }
  } else {
    fuzz.label(@"empty superset, skipped")
    False
  }
}

test prop_contains_superset_mutation(
  (subset, mutation) via fuzz.both(any_tokens(), any_mutation()),
) fail {
  let subset = dict.to_pairs(subset)
  if subset != [] {
    let superset = apply_mutation(mutation, subset)
    when mutation is {
      IncreaseQuantity(..) -> {
        fuzz.label(@"non-empty subset, increase quantity")
        !tokens.contains(superset, subset)
      }
      InsertAsset(..) -> {
        fuzz.label(@"non-empty subset, insert new asset")
        !tokens.contains(superset, subset)
      }
      ReduceQuantity(..) -> {
        fuzz.label(@"non-empty subset, reduce quantity")
        tokens.contains(superset, subset)
      }
      DeleteAsset(..) -> {
        fuzz.label(@"non-empty subset, remove asset")
        tokens.contains(superset, subset)
      }
    }
  } else {
    fuzz.label(@"empty subset, skipped")
    False
  }
}

// ------------------------------------- the rewire's narrowed contract

/// A zero quantity aborts rather than answering. Not reachable from ledger
/// data; pinned so that a future change to `wrap` cannot silently restore
/// tolerance (or silently widen the abort to a case that matters).
/// This is an ABORT, not a `False`, hence `fail` rather than `!contains(..)`.
test contains_aborts_on_a_zero_quantity() fail {
  tokens.contains([Pair(fixture_asset_name, 0)], [Pair(fixture_asset_name, 0)])
}

/// ...but only when the zero is actually inspected. An empty subset still
/// short-circuits to True without ever looking at the superset, exactly as the
/// interpreted implementation's first clause did.
test contains_empty_subset_ignores_a_malformed_superset() {
  tokens.contains([Pair(fixture_asset_name, 0)], [])
}

/// The singleton fast path must agree with the builtin it bypasses.
test union_singletons_match_the_builtin() {
  let a = dict.from_ascending_pairs([Pair(#"6161", 3)])
  let b = dict.from_ascending_pairs([Pair(#"6262", 5)])
  let same = dict.from_ascending_pairs([Pair(#"6161", 4)])
  and {
    dict.to_pairs(tokens.union(a, b)) == [Pair(#"6161", 3), Pair(#"6262", 5)],
    dict.to_pairs(tokens.union(b, a)) == [Pair(#"6161", 3), Pair(#"6262", 5)],
    dict.to_pairs(tokens.union(a, same)) == [Pair(#"6161", 7)],
  }
}

/// A name whose quantities cancel is dropped, as `sum_if_non_zero` did.
test union_singletons_drop_a_cancelling_name() {
  let a = dict.from_ascending_pairs([Pair(#"6161", 3)])
  let b = dict.from_ascending_pairs([Pair(#"6161", -3)])
  dict.to_pairs(tokens.union(a, b)) == []
}
