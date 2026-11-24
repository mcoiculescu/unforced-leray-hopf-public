import Mathlib.Analysis.InnerProductSpace.Adjoint
import UnforcedLeray.Infra.FiniteRankApprox

/-!
# B0104, helper: compactness tools

Helper for blueprint unit `B0104` (`lem:compact-duhamel`, `paper/main.tex` lines 1586-1621), the
step "A finite norm-net for the compact family `A_0(r)`, followed by finite-rank approximation of
its members, makes this uniform in `r` and the auxiliary parameters" (lines 1613-1615).

* `eventually_forall_mem_of_totallyBounded`: a uniformly bounded family of operators that tends to
  zero strongly, uniformly in an index, tends to zero uniformly on every totally bounded set.
* `totallyBounded_biUnion_image`: for a norm-totally-bounded set `𝒦` of compact operators, the union
  `⋃ K ∈ 𝒦, K '' closedBall 0 R` is totally bounded.
* `isCompactOperator_adjoint`: the Hilbert adjoint of a compact operator is compact (Schauder), by
  finite-rank approximation `K ≈ P K` with `P` a finite-rank orthogonal projection
  (`UnforcedLeray.Infra.FiniteRankApprox.exists_starProjection_comp_norm_sub_le`).
* `totallyBounded_adjoint_image`: the adjoints of a norm-totally-bounded family form a
  norm-totally-bounded family.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped InnerProductSpace InnerProduct

namespace UnforcedLeray.B0104

section Normed

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- **Uniform strong convergence on totally bounded sets.** If `‖G n j‖ ≤ M` for the indices with
`P j`, and `G n j x → 0` uniformly in those `j` for every `x`, then `G n j v → 0` uniformly in
those `j` and in `v ∈ S` for every totally bounded `S`. -/
theorem eventually_forall_mem_of_totallyBounded {J : Type*} {P : J → Prop}
    {G : ℕ → J → H →L[ℂ] H} {M : ℝ} (hG : ∀ n j, P j → ‖G n j‖ ≤ M)
    (hconv : ∀ x : H, ∀ ε > 0, ∀ᶠ n in atTop, ∀ j, P j → ‖G n j x‖ < ε)
    {S : Set H} (hS : TotallyBounded S) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ j, P j → ∀ v ∈ S, ‖G n j v‖ < ε := by
  intro ε hε
  have hM' : 0 ≤ max M 0 := le_max_right _ _
  have hδ : 0 < ε / (2 * (max M 0 + 1)) := by positivity
  obtain ⟨t, -, htfin, hcov⟩ := finite_approx_of_totallyBounded hS _ hδ
  have hev : ∀ᶠ n in atTop, ∀ y ∈ t, ∀ j, P j → ‖G n j y‖ < ε / 2 :=
    (eventually_all_finite htfin).2 fun y _ => hconv y (ε / 2) (half_pos hε)
  filter_upwards [hev] with n hn j hj v hv
  obtain ⟨y, hyt, hvy⟩ := mem_iUnion₂.1 (hcov hv)
  have hvy' : ‖v - y‖ < ε / (2 * (max M 0 + 1)) := by rwa [← dist_eq_norm]
  have h1 : ‖G n j (v - y)‖ ≤ max M 0 * (ε / (2 * (max M 0 + 1))) :=
    ((G n j).le_opNorm _).trans
      (mul_le_mul ((hG n j hj).trans (le_max_left _ _)) hvy'.le (norm_nonneg _) hM')
  have h2 : max M 0 * (ε / (2 * (max M 0 + 1))) < ε / 2 := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  calc ‖G n j v‖ = ‖G n j (v - y) + G n j y‖ := by rw [← map_add, sub_add_cancel]
    _ ≤ ‖G n j (v - y)‖ + ‖G n j y‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt (h1.trans h2.le) (hn y hyt j hj)
    _ = ε := add_halves ε

/-- **Union of images of a ball under a totally bounded family of compact operators.** -/
theorem totallyBounded_biUnion_image {𝒦 : Set (H →L[ℂ] H)} (h𝒦 : TotallyBounded 𝒦)
    (hc : ∀ K ∈ 𝒦, IsCompactOperator K) (R : ℝ) :
    TotallyBounded (⋃ K ∈ 𝒦, K '' closedBall (0 : H) R) := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  have hR' : 0 ≤ max R 0 := le_max_right _ _
  have hδ : 0 < ε / (2 * (max R 0 + 1)) := by positivity
  obtain ⟨t, ht𝒦, htfin, hcov⟩ := finite_approx_of_totallyBounded h𝒦 _ hδ
  have himg : ∀ K ∈ t, ∃ u : Set H, u.Finite ∧ K '' closedBall (0 : H) R ⊆ ⋃ y ∈ u, ball y (ε / 2) := by
    intro K hK
    have hK' : IsCompactOperator (K : H →ₗ[ℂ] H) := hc K (ht𝒦 hK)
    have htb : TotallyBounded (K '' closedBall (0 : H) R) :=
      (hK'.isCompact_closure_image_closedBall R).totallyBounded.subset subset_closure
    exact Metric.totallyBounded_iff.1 htb _ (half_pos hε)
  choose! u hufin hucov using himg
  refine ⟨⋃ K ∈ t, u K, htfin.biUnion fun K hK => hufin K hK, ?_⟩
  intro v hv
  obtain ⟨K, hK, x, hx, rfl⟩ : ∃ K ∈ 𝒦, ∃ x ∈ closedBall (0 : H) R, K x = v := by
    simpa only [mem_iUnion, mem_image, exists_prop] using hv
  obtain ⟨K', hK't, hKK'⟩ := mem_iUnion₂.1 (hcov hK)
  obtain ⟨y, hyu, hy⟩ := mem_iUnion₂.1 (hucov K' hK't ⟨x, hx, rfl⟩)
  refine mem_iUnion₂.2 ⟨y, mem_iUnion₂.2 ⟨K', hK't, hyu⟩, ?_⟩
  have hxR : ‖x‖ ≤ max R 0 := (mem_closedBall_zero_iff.1 hx).trans (le_max_left _ _)
  have hKK'' : ‖K - K'‖ < ε / (2 * (max R 0 + 1)) := by rwa [← dist_eq_norm]
  have h1 : dist (K x) (K' x) ≤ ε / (2 * (max R 0 + 1)) * max R 0 := by
    rw [dist_eq_norm, ← sub_apply]
    exact ((K - K').le_opNorm _).trans (mul_le_mul hKK''.le hxR (norm_nonneg _) hδ.le)
  have h2 : ε / (2 * (max R 0 + 1)) * max R 0 < ε / 2 := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  rw [mem_ball] at hy ⊢
  calc dist (K x) y ≤ dist (K x) (K' x) + dist (K' x) y := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt (h1.trans h2.le) hy
    _ = ε := add_halves ε

end Normed

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open UnforcedLeray.Infra.FiniteRankApprox

/-- **Schauder's theorem on Hilbert space.** The adjoint of a compact operator is compact. -/
theorem isCompactOperator_adjoint {K : H →L[ℂ] H} (hK : IsCompactOperator K) :
    IsCompactOperator (K†) := by
  refine isCompactOperator_of_mem_approximable (mem_approximable_iff_le.2 fun ε hε => ?_)
  obtain ⟨V, hV, hnorm⟩ := exists_starProjection_comp_norm_sub_le hK hε
  have := hV
  refine ⟨(K†).comp V.starProjection, ?_, ?_⟩
  · have h : LinearMap.range (((K†).comp V.starProjection : H →L[ℂ] H) : H →ₗ[ℂ] H) ≤
        Submodule.map ((K† : H →L[ℂ] H) : H →ₗ[ℂ] H) V := by
      rintro _ ⟨x, rfl⟩
      exact ⟨V.starProjection x, Submodule.starProjection_apply_mem V x, rfl⟩
    exact Submodule.finiteDimensional_of_le h
  · have hP : (V.starProjection)† = V.starProjection :=
      (isSelfAdjoint_starProjection V).adjoint_eq
    have heq : K† - (K†).comp V.starProjection = (K - V.starProjection.comp K)† := by
      rw [map_sub, ContinuousLinearMap.adjoint_comp, hP]
    rw [heq, LinearIsometryEquiv.norm_map]
    exact hnorm

/-- The adjoints of a norm-totally-bounded family of operators form a norm-totally-bounded
family (the adjoint is an isometry). -/
theorem totallyBounded_adjoint_image {𝒦 : Set (H →L[ℂ] H)} (h𝒦 : TotallyBounded 𝒦) :
    TotallyBounded (ContinuousLinearMap.adjoint '' 𝒦) :=
  h𝒦.image (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := H) (F := H)).isometry.uniformContinuous

end Hilbert

end UnforcedLeray.B0104
