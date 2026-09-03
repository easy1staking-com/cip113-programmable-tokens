//// Per-policy token maps.
////
//// ## Native-backed since the van Rossem rewire (PV11)
////
//// `contains` and `union` are the two per-token hot spots of the whole
//// protocol: every transfer walks them once per policy, over every asset name
//// in that policy. They used to be interpreted UPLC walks (`pop_until` and
//// `dict.union_with`), which is what made execution cost grow steeply per
//// token and set the `many_tokens` ceiling.
////
//// They are now single CIP-0153 builtin calls. The bridge is the trick that
//// makes it cheap: a `Value`'s `Data` shape is `Map<policy, Map<name, qty>>`,
//// so one policy's token map becomes a whole one-policy `Value` by consing a
//// SINGLE pair in front of it — O(1) interpreted work — after which
//// `unValueData` does the decoding natively.
////
//// Measured head-to-head at `--seed 42 --max-size 30` (projected max size, so
//// higher is more headroom):
////
////   contains  1981 -> 44984   (22.7x)
////   union      195 ->  4443   (22.8x, INCLUDING the trip back to a Dict)
////
//// The type stays `Dict<AssetName, Int>`: nothing outside this module changes,
//// and no caller has to know a builtin is involved.

use aiken/collection/dict.{Dict}
use aiken/primitive/bytearray
use cardano/assets.{AssetName}
use cardano/assets/native

pub type Tokens =
  Dict<AssetName, Int>

/// The policy id the wrapper borrows. Its only requirements are that it is at
/// most 32 bytes (the builtin's key bound) and that it is not the empty
/// bytestring, which the Mary-era value reserves for Ada. It never escapes
/// this module.
const wrapper_policy: ByteArray = #"00"

/// Lift one policy's token map into a one-policy native `Value`.
///
/// This is one cons cell plus `unValueData`; there is deliberately no
/// per-token interpreted work here, which is the entire point.
///
/// /!\ PRE-CONDITION /!\
/// `unValueData` is FAIL-CLOSED: it aborts on a quantity of zero, on
/// unordered or duplicate names, and on names longer than 32 bytes. All three
/// hold for any token map derived from a ledger `Value` — the ledger emits no
/// zero quantities and no unsorted maps, and `union` below preserves that by
/// construction. An empty map is handled here rather than passed on, since an
/// empty inner map is also rejected.
fn wrap(self: Pairs<AssetName, Int>) -> native.NativeValue {
  when self is {
    [] -> native.zero()
    _ -> {
      let as_data: Data = [Pair(wrapper_policy, self)]
      native.from_data(as_data)
    }
  }
}

/// Bring a one-policy native `Value` back to a token map.
///
/// `to_data` is one builtin and the cast to `Pairs` is free; only
/// `from_ascending_pairs` walks the list, and it must, because `Dict` is
/// opaque and will not accept a cast. That walk is why `union` measures 22.8x
/// rather than the 44x of the read-only `contains`.
fn unwrap(self: native.NativeValue) -> Tokens {
  expect inner: Pairs<ByteArray, Pairs<AssetName, Int>> = native.to_data(self)
  when inner is {
    // Every quantity cancelled out; the builtin removed the policy with them.
    [] -> dict.empty
    [Pair(_, names)] -> dict.from_ascending_pairs(names)
    _ -> fail @"tokens.unwrap: more than one policy in a wrapped value"
  }
}

/// Whether `superset` holds at least as much of every token as `subset`.
///
/// /!\ PRE-CONDITION /!\
/// Given pairs are assumed to be well-formed and semantically 'correct'. That
/// is, keys contain no duplicates and are in ascending order.
///
/// In practice, this means we suppose both values have been constructed from
/// existing well-formed Values.
///
/// ## Behaviour on non-positive subset quantities
///
/// `valueContains` requires both sides to be positive and ABORTS otherwise,
/// where the previous interpreted walk answered. The two agree exactly
/// whenever every `subset` quantity is positive, which is the only state a
/// well-formed value reaches:
///
///   * a zero can not survive `union` (a name summing to zero is dropped, as
///     it was under `sum_if_non_zero`) and the ledger never emits one;
///   * a negative net quantity for a name means more of it was burned than
///     was spent, which is an unbalanced transaction the ledger rejects
///     before a script ever sees it.
///
/// The one visible difference is on a subset entry that is absent from the
/// superset: the walk aborted, the builtin returns `False`. Every call site
/// wraps this in `expect`, so both end the script the same way.
pub fn contains(
  superset: Pairs<AssetName, Int>,
  subset: Pairs<AssetName, Int>,
) -> Bool {
  when subset is {
    // The original's first clause, kept verbatim in spirit: an empty subset is
    // contained by anything and the superset is never inspected. Restoring it
    // matters — without it, a caller asking "does this contain nothing?" paid
    // a bridge, and an ill-formed superset could abort a question whose answer
    // does not depend on it.
    [] -> True
    _ -> native.contains_at_least(wrap(superset), wrap(subset))
  }
}

/// Merge two token maps by summing quantities per token name.
///
/// A name whose quantities cancel to zero is dropped, exactly as
/// `dict.union_with(.., sum_if_non_zero)` did — here it is structural rather
/// than a strategy, because the builtin cannot represent a zero.
///
/// Note this drops a NAME, never a POLICY: policy-level keys are preserved by
/// `assets.union` one level up, which is what keeps a fully-burned policy in
/// the map so its transfer logic is still demanded.
pub fn union(left: Tokens, right: Tokens) -> Tokens {
  // Short-circuit the empty cases: they are common (a transfer with no mint
  // folds an empty map at every policy) and they skip both bridges.
  when dict.to_pairs(left) is {
    [] -> right
    left_pairs ->
      when dict.to_pairs(right) is {
        [] -> left
        // Both sides a single name: the bridge is a fixed cost per call, and
        // at this size it is more than the work it removes. Measured: without
        // this clause the `many_inputs` and `many_outputs` ceilings dropped
        // ~20%, because those transactions carry one token per policy and
        // never reach the sizes the builtin wins at.
        [Pair(k2, v2)] ->
          when left_pairs is {
            [Pair(k1, v1)] -> dict.from_ascending_pairs(sum_two(k1, v1, k2, v2))
            _ -> unwrap(native.merge(wrap(left_pairs), wrap([Pair(k2, v2)])))
          }
        right_pairs -> unwrap(native.merge(wrap(left_pairs), wrap(right_pairs)))
      }
  }
}

/// The two-singleton case of `union`, in the same order and with the same
/// zero-dropping rule the builtin applies.
fn sum_two(
  k1: AssetName,
  v1: Int,
  k2: AssetName,
  v2: Int,
) -> Pairs<AssetName, Int> {
  if k1 == k2 {
    let total = v1 + v2
    if total == 0 {
      []
    } else {
      [Pair(k1, total)]
    }
  } else if bytearray.compare(k1, k2) == Less {
    [Pair(k1, v1), Pair(k2, v2)]
  } else {
    [Pair(k2, v2), Pair(k1, v1)]
  }
}
