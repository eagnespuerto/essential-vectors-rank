# Essential vectors and rank

## Setup

Let `K` be a field and `V` a vector space over `K`. Let `r : ι → V` be a family of vectors indexed by a finite type `ι`. Assume every `r i` is nonzero, and assume the family has a redundancy: some `r j` lies in the span of the other vectors.

Call an index `i` **essential** when `r i` is not in the span of the family with `i` removed:

    r i ∉ span K { r l : l ≠ i }.

Write `e` for the number of essential indices and `V₀ = span K (range r)` for the span of the whole family. `V₀` is finite-dimensional, since a finite set spans it.

**Claim.** `e + 1 ≤ dim V₀`.

## Step 1: the essential vectors are independent

Suppose a linear combination of the essential vectors is zero:

    ∑ c_t · r t = 0,   t over the essential indices.

If some coefficient `c_{t0}` is nonzero, solve for `r t0`:

    r t0 = −c_{t0}⁻¹ · ∑_{t ≠ t0} c_t · r t.

Every term on the right is a scalar times `r t` with `t ≠ t0`, so `r t0` lies in `span K { r l : l ≠ t0 }`. That contradicts `t0` being essential. So all coefficients are zero, and the essential vectors are linearly independent.

Independence gives `dim (span of essentials) = e`. That span sits inside `V₀`, so `e ≤ dim V₀`.

## Step 2: the essentials do not span

Let `r j` be the redundant vector from the hypothesis. It is nonzero. Suppose it were in the span of the essentials:

    r j = ∑ c_t · r t,   t over the essential indices.

Not every `c_t` is zero, because `r j ≠ 0`. Pick `t0` with `c_{t0} ≠ 0` and solve for `r t0`:

    r t0 = c_{t0}⁻¹ · ( r j − ∑_{t ≠ t0} c_t · r t ).

The index `j` is not essential (it is redundant), so `j ≠ t0`, and every index on the right differs from `t0`. Hence `r t0 ∈ span K { r l : l ≠ t0 }`, contradicting that `t0` is essential.

So `r j` lies in `V₀` but outside the span of the essentials. The span of the essentials is a proper subspace of `V₀`. A strict inclusion of finite-dimensional subspaces drops the dimension by at least one, so

    e = dim (span of essentials) < dim V₀,

that is, `e + 1 ≤ dim V₀`.

## Notes on the formalization

The two steps reuse one move: solve a single vector out of a dependence and show it lands in the span of the family with that index removed. In Lean that is `Fintype.linearIndependent_iff` for step 1 and `mem_span_range_iff_exists_fun` for step 2, each followed by `Finset.sum_erase_add` to split off the chosen term.

The finish uses `finrank_span_eq_card` for the rank of the independent essentials, `Submodule.finrank_lt_finrank_of_lt` for the strict drop, and `FiniteDimensional.span_of_finite` to know `V₀` is finite-dimensional.

Co-created with Claude Opus 4.8
