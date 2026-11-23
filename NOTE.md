# Essential vectors and rank

*Ella Agnes Puerto, independent researcher &middot; 24 November 2026*

## Abstract

I prove a small fact in linear algebra and check it by machine. Take a finite list of nonzero vectors over a field, and suppose at least one is redundant, meaning it lies in the span of the others. Call a vector essential when the others cannot reproduce it. Then the number of essential vectors, plus one, is at most the rank of the list. The proof is formalized in Lean 4 against Mathlib and uses only the axioms `propext`, `Classical.choice`, and `Quot.sound`. The full Lean file is in the repository cited at the end; this note gives the mathematics.

## 1. Introduction

The fact is elementary, so I lead with the picture.

Think of the vectors as people on a small crew, each able to pull in some direction of work. A person is redundant when the rest of the crew together already covers everything they do. A person is essential when no mix of the others can stand in for them. The essential people are the ones I cannot drop without losing reach.

Two things follow. No essential person wastes a slot, so each one adds a direction the rest did not have; that is why their count is at most the rank. And once some person is redundant, the crew has slack: the essential people alone do not use up all the room, so the reach beats their count by at least one. That extra one is the whole point.

Here is the same idea with roads. Each vector is a road out of town, and the rank is how many different places I can reach by combining roads. An essential road goes somewhere the others cannot. If one road is redundant, meaning I could already reach its end another way, then the roads together reach strictly more places than there are essential roads.

## 2. Statement

Let `K` be a field and `V` a vector space over `K`. Let `r : ι → V` be vectors indexed by a finite type `ι`. Assume every `r i` is nonzero, and assume one is redundant: some `r j` lies in the span of the others.

An index `i` is **essential** when

    r i ∉ span K { r l : l ≠ i }.

Write `e` for the number of essential indices and `V₀ = span K (range r)` for the span of the whole list. Since a finite set spans `V₀`, it is finite-dimensional, so no assumption on the ambient space is needed.

**Theorem.** `e + 1 ≤ dim V₀`.

In Lean:

    theorem card_essential_add_one_le_finrank_span
        {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]
        (r : ι → V)
        (hne : ∀ i, r i ≠ 0)
        (hred : ∃ j : ι, r j ∈ Submodule.span K (r '' {l | l ≠ j})) :
        Nat.card {i : ι // r i ∉ Submodule.span K (r '' {j | j ≠ i})} + 1 ≤
          Module.finrank K (Submodule.span K (Set.range r))

## 3. Proof

### 3.1 The essential vectors are independent

Suppose a combination of the essential vectors is zero:

    ∑ c_t · r t = 0,   t over the essential indices.

If some coefficient `c_{t0}` is nonzero, solve for `r t0`:

    r t0 = −c_{t0}⁻¹ · ∑_{t ≠ t0} c_t · r t.

Every term on the right is a scalar times `r t` with `t ≠ t0`, so `r t0` lands in `span K { r l : l ≠ t0 }`. That contradicts `t0` being essential. So all coefficients are zero, and the essential vectors are independent.

Independence gives `dim (span of essentials) = e`. That span sits inside `V₀`, so `e ≤ dim V₀`.

### 3.2 The essentials do not span

Let `r j` be the redundant vector from the hypothesis. It is nonzero. Suppose it were in the span of the essentials:

    r j = ∑ c_t · r t,   t over the essential indices.

Not every `c_t` is zero, because `r j ≠ 0`. Pick `t0` with `c_{t0} ≠ 0` and solve for `r t0`:

    r t0 = c_{t0}⁻¹ · ( r j − ∑_{t ≠ t0} c_t · r t ).

The index `j` is not essential, so `j ≠ t0`, and every index on the right differs from `t0`. So `r t0 ∈ span K { r l : l ≠ t0 }`, again contradicting that `t0` is essential.

So `r j` lives in `V₀` but outside the span of the essentials. That makes the span of the essentials a proper subspace of `V₀`. A strict inclusion of finite-dimensional subspaces loses at least one dimension, so

    e = dim (span of essentials) < dim V₀,

which is `e + 1 ≤ dim V₀`. ∎

## 4. Formalization

The two steps reuse one move: solve a single vector out of a dependence and show it lands in the span of the list with that index removed. In Lean that is `Fintype.linearIndependent_iff` for step 3.1 and `mem_span_range_iff_exists_fun` for step 3.2, each followed by `Finset.sum_erase_add` to split off the chosen term. The finish uses `finrank_span_eq_card` for the rank of the independent essentials, `Submodule.finrank_lt_finrank_of_lt` for the strict drop, and `FiniteDimensional.span_of_finite` to know `V₀` is finite-dimensional.

I checked the file against Lean `v4.36.0` with Mathlib pinned to commit `fc4f59e` (the v4.36.0 release). It has no `sorry` and no `native_decide`, and `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`.

The lemma first appeared as an open gap in the public pequalnp.com attempt at P versus NP, stated over the rationals. That gap was retired before it was merged, so I generalized the proof to any field and kept it on its own.

## References and availability

Source code: https://github.com/eagnespuerto/essential-vectors-rank

Archived: Zenodo, DOI [10.5281/zenodo.24475597](https://doi.org/10.5281/zenodo.24475597)

Built on the Lean 4 theorem prover and the Mathlib library.

Co-created with Claude Opus 4.8
