# The Lean Mini-Kernel

A minimal, self-contained implementation of the Lean 4 type checker kernel, written in Lean. This is an **experimental project** for learning about and tinkering with Lean's type theory -- it is **not suitable for serious use**.

For an overview of Lean type checker implementations and a test suite, see the [Lean Kernel Arena](https://arena.lean-lang.org).

## Design goals

This kernel strives to be **as simple as possible**:

- **Self-contained data types.** It defines its own `Name`, `Level`, and `Expr` types from scratch, rather than reusing Lean's built-in data structures.
- **Pure de Bruijn indices throughout.** No locally nameless representation -- bound variables are always de Bruijn indices, even in the local context.
- **No performance optimizations.** No expression caching, no hash-consing, no sharing.
Because of this, the kernel cannot check real-world Lean proofs that depend on the standard library.
- **No native `Nat` execution.** Natural number literals are represented but there is no kernel-level `Nat` reduction (no fast evaluation of `Nat.add`, `Nat.ble`, etc.).
- **Single file kernel.** The core type checker logic lives in `MiniKernel/Kernel.lean`.
- **Sound.** On the supported fragment (see below), it should be sound. If you can prove `False` with it, please let me know! 

## What's (intentionally) missing

- **Mutual inductives**
- **Nested inductives**
- **String literals** (the `Expr` type has the constructor, but no reduction rules)
- **Large `Nat` literal** reduction (literals >10 cause the input to be declined)

## Deliberately omitted checks

Some checks that the official Lean kernel performs are intentionally omitted here, to keep the code simple and to explore what is actually necessary for soundness. For example:

- In **proof irrelevance**, the kernel does not verify that the compared terms actually have `Prop` type -- it only checks whether the inferred types are definitionally equal to each other.
- In **projection type-checking**, the kernel does not fully verify that the major premise has the expected inductive type.

**If you can construct a soundness exploit** (a proof of `False` or a type error that slips through) that relies on one of these omitted checks, I'd love to hear about it! Please open an issue.

## Building

Requires a [Lean 4 installation](https://lean-lang.org/lean4/doc/setup.html).

```
lake build
```

The resulting binary reads `.ndjson` export files (as produced by [`lean4export`](https://github.com/leanprover/lean4export)):

```
.lake/build/bin/mini-kernel file.ndjson
```
