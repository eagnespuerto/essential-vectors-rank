# Essential vectors and rank

*Ella Agnes Puerto, independent researcher &middot; November 2026*

A machine-checked note. The typeset version is [paper.tex](paper.tex), compiled to [NOTE.pdf](NOTE.pdf).

## Abstract

Take a finite family of nonzero vectors over a field, and suppose at least one is redundant, that is, it lies in the span of the others. Call a vector **essential** when the others cannot reproduce it. The number of essential vectors, plus one, is at most the rank of the family. In matroid language the essential vectors are the coloops, and the statement is that a representable matroid with a circuit has strictly fewer coloops than its rank. The proof is formalized in Lean 4 against Mathlib and uses only the axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Introduction

The fact is elementary, so I lead with the picture.

Think of the vectors as people on a small crew, each able to pull in some direction of work. A person is redundant when the rest of the crew together already covers everything they do. A person is essential when no mix of the others can stand in for them. No essential person wastes a slot, so each one adds a direction the rest did not have; that is why their count is at most the rank. And once some person is redundant, the crew has slack: the essential people alone do not use up all the room, so the reach beats their count by at least one.

The same idea works with roads. Each vector is a road out of town, and the rank is how many different places I can reach by combining roads. An essential road goes somewhere the others cannot. If one road is redundant, meaning I could already reach its end another way, then the roads together reach strictly more places than there are essential roads.

**Relation to matroid theory.** An essential vector is a *coloop* of the matroid the family represents: an element lying in every basis, equivalently a vector outside the span of the rest [3]. The coloops of a matroid form an independent set, and a matroid is free exactly when every element is a coloop. The theorem is the quantitative form: once the family carries a circuit (a redundant vector), its coloops fall short of a basis, so their number drops below the rank. The argument is standard; the contribution is a short, fully checked proof in a shape that drops into a larger formal development.

## Statement

Let `K` be a field and `V` a vector space over `K`. Let `r : ι → V` be a family indexed by a finite type `ι`. Assume every `r i` is nonzero, and assume one is redundant: some `r j` lies in `span K { r l : l ≠ j }`. An index `i` is **essential** when `r i ∉ span K { r l : l ≠ i }`. Write `e` for the number of essential indices and `V₀ = span K (range r)`, which is finite-dimensional since a finite set spans it.

**Theorem.** `e + 1 ≤ dim V₀`.

## Proof

**The essential vectors are independent.** If a combination `∑ c_t · r t = 0` of the essentials has a nonzero coefficient `c_{t0}`, then `r t0 = −c_{t0}⁻¹ ∑_{t ≠ t0} c_t · r t ∈ span K { r l : l ≠ t0 }`, contradicting that `t0` is essential. So the essentials are independent, `dim (span of essentials) = e`, and `e ≤ dim V₀`.

**The essentials do not span.** The redundant `r j` is nonzero. If `r j = ∑ c_t · r t` over the essentials, some `c_{t0} ≠ 0` (else `r j = 0`), and `r t0 = c_{t0}⁻¹ ( r j − ∑_{t ≠ t0} c_t · r t ) ∈ span K { r l : l ≠ t0 }` (since `j ≠ t0`), contradicting that `t0` is essential. So `r j ∈ V₀` lies outside the span of the essentials, that span is a proper subspace of `V₀`, and a strict inclusion of finite-dimensional subspaces loses a dimension: `e < dim V₀`, i.e. `e + 1 ≤ dim V₀`.

## Formalization

Formalized in Lean 4 [1] with Mathlib [2] as `card_essential_add_one_le_finrank_span`. The two steps reuse one move: solve a single vector out of a dependence and show it lands in the span of the family with that index removed — `Fintype.linearIndependent_iff` and `mem_span_range_iff_exists_fun`, each with `Finset.sum_erase_add`. The finish uses `finrank_span_eq_card`, `Submodule.finrank_lt_finrank_of_lt`, and `FiniteDimensional.span_of_finite`. Mathlib also carries a matroid library (Nelson and contributors [4]) in which this could be phrased with coloops; I kept it in direct linear-algebra terms so it imports into any development using `finrank`.

**Provenance.** This lemma began as an open gap in the public pequalnp.com collaboration [5], an attempt at P versus NP, stated over the rationals. The thread for that gap was closed before the proof could be merged, so I generalized it to an arbitrary field and record it here.

## Acknowledgements and use of AI

This note and its Lean proof were prepared by the author with extensive use of the AI assistant Claude (Anthropic; model Claude Opus 4.8), through Claude Code: the formalization, the write-up, and the checking of references against primary sources.

## References

1. L. de Moura and S. Ullrich. *The Lean 4 theorem prover and programming language*. In Automated Deduction — CADE 28, Lecture Notes in Computer Science, Springer, 2021, pp. 625–635. [doi:10.1007/978-3-030-79876-5_37](https://doi.org/10.1007/978-3-030-79876-5_37)
2. The mathlib Community. *The Lean mathematical library*. In Proc. CPP 2020, pp. 367–381. [doi:10.1145/3372885.3373824](https://doi.org/10.1145/3372885.3373824). arXiv:1910.09336
3. J. G. Oxley. *Matroid Theory*, 2nd ed. Oxford Graduate Texts in Mathematics 21, Oxford University Press, 2011.
4. P. Nelson and contributors. *A formalization of matroids in Lean*. <https://github.com/apnelson1/Matroid> (much of it integrated into Mathlib).
5. The pequalnp collaboration. *A public attempt at P versus NP*. <https://pequalnp.com>; <https://github.com/brilliant-hq/pequalnp-proofs>
6. E. A. Puerto. *Essential vectors and rank: a machine-checked Lean 4 proof*. Zenodo, 2026. [doi:10.5281/zenodo.24475596](https://doi.org/10.5281/zenodo.24475596)
