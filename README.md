# Essential vectors and rank

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24475596.svg)](https://doi.org/10.5281/zenodo.24475596)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)
[![Lean 4](https://img.shields.io/badge/Lean-v4.36.0-blue.svg)](https://lean-lang.org)
[![Mathlib](https://img.shields.io/badge/Mathlib-fc4f59e-blue.svg)](https://github.com/leanprover-community/mathlib4)
[![paper (PDF)](https://img.shields.io/badge/paper-PDF-B31B1B.svg)](NOTE.pdf)
[![proof](https://img.shields.io/badge/proof-no%20sorry%2C%203%20axioms-brightgreen.svg)](NOTE.pdf)

Code and data © 2026 Ella Agnes Puerto (MIT).

A machine-checked Lean 4 proof of one small fact in linear algebra.

Take a finite family of nonzero vectors in a vector space over a field, and suppose at least one of them is redundant: it lies in the span of the others. Call a vector **essential** when it is not in the span of the rest. Then the number of essential vectors, plus one, is at most the rank of the family.

## The statement

```lean
theorem card_essential_add_one_le_finrank_span
    {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]
    (r : ι → V)
    (hne : ∀ i, r i ≠ 0)
    (hred : ∃ j : ι, r j ∈ Submodule.span K (r '' {l | l ≠ j})) :
    Nat.card {i : ι // r i ∉ Submodule.span K (r '' {j | j ≠ i})} + 1 ≤
      Module.finrank K (Submodule.span K (Set.range r))
```

It holds over any field, for any vector space, with the family indexed by any finite type. The span of a finite family is finite-dimensional, so the ambient space need not be.

## The proof

Two steps. The full write-up is in [NOTE.md](NOTE.md), typeset as a short paper in [paper.tex](paper.tex) (compiled to [NOTE.pdf](NOTE.pdf)).

1. The essential vectors are linearly independent, so the rank of their span is their count `e`, and `e ≤ finrank`.
2. A nonzero redundant vector cannot be in the span of the essentials, so the essentials do not span the whole family. The inclusion is strict, which raises the rank by at least one.

## Checking it

The proof is in [EssentialVectorsRank.lean](EssentialVectorsRank.lean). It was checked against Lean `v4.36.0` with Mathlib pinned to commit `fc4f59e` (the v4.36.0 release). It has no `sorry` and no `native_decide`, and `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`.

To build it yourself:

```sh
lake exe cache get
lake build
```

## Provenance

The lemma first appeared as an open "gap" in the public pequalnp.com attempt at P versus NP, stated there over the rationals. That gap was retired before it was merged, so I generalized the proof to any field and kept it here on its own.

## License

MIT. See [LICENSE](LICENSE).

Co-created with Claude Opus 4.8
