/-
Essential vectors and rank.

Take a finite family of nonzero vectors in a vector space over a field, and
suppose at least one of them lies in the span of the others. Call a vector
"essential" when it is not in the span of the rest. This file checks that the
number of essential vectors, plus one, is at most the dimension of the span of
the whole family.

The proof has two steps.

  1. The essential vectors are linearly independent. If a combination of them
     vanishes with a nonzero coefficient at index t0, then r t0 is a combination
     of the others, so r t0 lies in the span of the family with t0 removed. That
     contradicts t0 being essential. So the rank of their span equals their
     count e, and e is at most the rank of the whole family.

  2. The essential vectors do not span everything, which gives the extra one.
     The redundant vector from the hypothesis is nonzero. If it were in the span
     of the essentials, writing it with a nonzero coefficient at some essential
     t0 again places r t0 in the span of the family with t0 removed, a
     contradiction. So that vector sits in the span of the family but outside the
     span of the essentials. The inclusion is strict, and a strict inclusion of
     finite-dimensional subspaces drops the rank by at least one.

The span of a finite family is finite-dimensional, so no dimension assumption on
the ambient space is needed.

Checked against Lean v4.36.0 with Mathlib. Axioms: propext, Classical.choice,
Quot.sound. No sorry, no native_decide.
-/
import Mathlib

open Submodule Set

/-- In a finite family `r` of nonzero vectors over a field, where some vector is
redundant (it lies in the span of the others), the number of essential vectors
-- those not in the span of the rest -- plus one is at most the rank of the
family. -/
theorem card_essential_add_one_le_finrank_span
    {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]
    (r : ι → V)
    (hne : ∀ i, r i ≠ 0)
    (hred : ∃ j : ι, r j ∈ Submodule.span K (r '' {l | l ≠ j})) :
    Nat.card {i : ι // r i ∉ Submodule.span K (r '' {j | j ≠ i})} + 1 ≤
      Module.finrank K (Submodule.span K (Set.range r)) := by
  classical
  obtain ⟨jr, hjr⟩ := hred
  set T := {i : ι // r i ∉ Submodule.span K (r '' {j | j ≠ i})} with hTdef
  let g : T → V := fun t => r t.1
  have hLI : LinearIndependent K g := by
    rw [Fintype.linearIndependent_iff]
    intro c hc t0
    by_contra hct0
    refine t0.2 ?_
    have h1 : c t0 • g t0 + ∑ t ∈ Finset.univ.erase t0, c t • g t = 0 := by
      rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ t0)] at hc
      simpa [add_comm] using hc
    have hsolve : g t0 = - (c t0)⁻¹ • ∑ t ∈ Finset.univ.erase t0, c t • g t := by
      have h2 : c t0 • g t0 = - ∑ t ∈ Finset.univ.erase t0, c t • g t := by
        rw [eq_neg_iff_add_eq_zero]; exact h1
      rw [show g t0 = (c t0)⁻¹ • (c t0 • g t0) by
            rw [smul_smul, inv_mul_cancel₀ hct0, one_smul], h2, smul_neg, neg_smul]
    have key : g t0 ∈ Submodule.span K (r '' {j | j ≠ t0.1}) := by
      rw [hsolve]
      apply Submodule.smul_mem
      apply Submodule.sum_mem
      intro t ht
      apply Submodule.smul_mem
      apply Submodule.subset_span
      exact ⟨t.1, fun hEq => (Finset.mem_erase.mp ht).1 (Subtype.ext hEq), rfl⟩
    exact key
  have hle : Submodule.span K (Set.range g) ≤ Submodule.span K (Set.range r) := by
    apply Submodule.span_mono
    rintro x ⟨t, rfl⟩
    exact ⟨t.1, rfl⟩
  have hjr_not : r jr ∉ Submodule.span K (Set.range g) := by
    intro hmem
    rw [mem_span_range_iff_exists_fun] at hmem
    obtain ⟨c, hc⟩ := hmem
    by_cases hall : ∀ t, c t = 0
    · exact hne jr (by rw [← hc]; simp [hall])
    · rw [not_forall] at hall
      obtain ⟨t0, hct0⟩ := hall
      refine t0.2 ?_
      have h1 : c t0 • g t0 + ∑ t ∈ Finset.univ.erase t0, c t • g t = r jr := by
        rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ t0)] at hc
        simpa [add_comm] using hc
      have hsolve : g t0 = (c t0)⁻¹ • (r jr - ∑ t ∈ Finset.univ.erase t0, c t • g t) := by
        have h2 : c t0 • g t0 = r jr - ∑ t ∈ Finset.univ.erase t0, c t • g t := by
          rw [eq_sub_iff_add_eq]; exact h1
        rw [← h2, smul_smul, inv_mul_cancel₀ hct0, one_smul]
      have key : g t0 ∈ Submodule.span K (r '' {j | j ≠ t0.1}) := by
        rw [hsolve]
        apply Submodule.smul_mem
        apply Submodule.sub_mem
        · by_cases hEq : jr = t0.1
          · exact absurd hjr (by rw [hEq]; exact t0.2)
          · exact Submodule.subset_span ⟨jr, hEq, rfl⟩
        · apply Submodule.sum_mem
          intro t ht
          apply Submodule.smul_mem
          apply Submodule.subset_span
          exact ⟨t.1, fun hEq => (Finset.mem_erase.mp ht).1 (Subtype.ext hEq), rfl⟩
      exact key
  have : FiniteDimensional K (Submodule.span K (Set.range r)) :=
    FiniteDimensional.span_of_finite K (Set.finite_range r)
  have hlt : Submodule.span K (Set.range g) < Submodule.span K (Set.range r) := by
    refine lt_of_le_of_ne hle ?_
    intro hEqSub
    exact hjr_not (by rw [hEqSub]; exact Submodule.subset_span ⟨jr, rfl⟩)
  have hcard : Module.finrank K (Submodule.span K (Set.range g)) = Fintype.card T :=
    finrank_span_eq_card hLI
  have hfin_lt : Module.finrank K (Submodule.span K (Set.range g)) <
      Module.finrank K (Submodule.span K (Set.range r)) :=
    Submodule.finrank_lt_finrank_of_lt hlt
  rw [hcard] at hfin_lt
  rw [Nat.card_eq_fintype_card]
  omega

#print axioms card_essential_add_one_le_finrank_span
