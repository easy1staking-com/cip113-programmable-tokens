//// Head-to-head: the CIP-0153 native `Value` builtins (van Rossem / PV11)
//// against stdlib's `Dict`-backed `cardano/assets.Value`, doing the same
//// logical work.
////
//// This exists to answer one question with a number rather than an opinion:
//// **would making stdlib's `Value` natively backed (the "S1 unify") pay for
//// itself?** Each pair below performs identical work in the two
//// representations, so the delta is the intrinsic gain from the builtins —
//// the ceiling a unify could deliver.
////
//// Deliberately NOT measured: converting an existing stdlib `Value` into a
//// native one. Under a unify no conversion exists, so pricing it here would
//// understate the ceiling. It is discussed in the report instead.
////
//// Run with `aiken bench -m native_value_bench`.

use aiken/builtin
use aiken/collection/list
use aiken/fuzz
use cardano/assets
use cardano/assets/native

const policy: ByteArray = #"00000000000000000000000000000000000000000000000000000f00"

/// `size` distinct one-byte token names, quantity 10 each.
fn names(size: Int) -> List<ByteArray> {
  list.range(0, size) |> list.map(fn(i) { builtin.cons_bytearray(i % 256, "") })
}

fn build_stdlib(size: Int) -> assets.Value {
  names(size)
    |> list.foldl(assets.zero, fn(n, acc) { assets.add(acc, policy, n, 10) })
}

fn build_native(size: Int) -> native.NativeValue {
  names(size)
    |> list.foldl(
        native.zero(),
        fn(n, acc) { native.insert_coin(acc, policy, n, 10) },
      )
}

fn size_sampler(size: Int) -> Fuzzer<Int> {
  fuzz.constant(size)
}

// ## Construction — `assets.add` vs the `insertCoin` builtin

bench stdlib_build(size via size_sampler) {
  assets.quantity_of(build_stdlib(size), policy, "") >= 0
}

bench native_build(size via size_sampler) {
  native.quantity_of(build_native(size), policy, "") >= 0
}

// ## Containment over N token names — dictionary walk vs `valueContains`

bench stdlib_contains(size via size_sampler) {
  let big = build_stdlib(size)
  let small = build_stdlib(1)
  assets.contains(assets.tokens(big, policy), assets.tokens(small, policy))
}

bench native_contains(size via size_sampler) {
  let big = build_native(size)
  let small = build_native(1)
  native.contains_at_least(big, small)
}

// ## Addition of two N-token values — `merge` vs `unionValue`

bench stdlib_merge(size via size_sampler) {
  let a = build_stdlib(size)
  let b = build_stdlib(size)
  assets.quantity_of(assets.merge(a, b), policy, "") >= 0
}

bench native_merge(size via size_sampler) {
  let a = build_native(size)
  let b = build_native(size)
  native.quantity_of(native.merge(a, b), policy, "") >= 0
}
