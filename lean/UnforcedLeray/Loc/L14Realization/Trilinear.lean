import UnforcedLeray.Loc.L14Realization.PressureDiv

/-!
# Step L14, helpers: `-𝔓 div(u ⊗ u) = -𝔓((u·∇)u)` and the trilinear cancellation

Support for `Loc/L14Realization.lean` (step L14 `RealizationStep`, `paper/main.tex`
lines 545–550, blueprint unit B1030, infrastructure "trilinear cancellation
`⟨𝔓 div(u⊗u), u⟩ = 0` for `u ∈ H²_div`").

For a solenoidal `u ∈ L²` with `L²` weak derivatives, forcing `F = (u·∇)u ∈ L²` and columns
`uⱼu ∈ L²`:

* `sum_inner_columns_testPartial`: `Σⱼ ⟨uⱼu, ∂ⱼφ⟩ = -⟨F, φ⟩` (weak `div(u ⊗ u) = F`);
* `integral_velocityPressure_div_eq_inner`: `∫ p div φ = ⟨(I - 𝔓)F, φ⟩` (the `L²` form of the
  compiled `RieszLp.velocityPressure_pressure_identity`);
* `isMinusLerayDiv_eq_neg_projection`: every `N` with `IsMinusLerayDiv (u ⊗ u) N` equals
  `-𝔓F`; the proof combines the two identities with `velocityPressure_div_identity`;
* `inner_isMinusLerayDiv_eq_zero`: `⟨N, u⟩ = -⟨𝔓F, u⟩ = -⟨F, u⟩ = 0`
  (`integral_coord_mul_forcing_eq_zero`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology InnerProductSpace

namespace UnforcedLeray.Blueprint.L14

open PressureAnalysis RieszLp

theorem inner_space_eq_sum (a b : Space) : inner ℝ a b = ∑ i : Fin 3, a i * b i := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_eq_re_inner, RCLike.inner_apply]
  simp [mul_comm]

section Identities

variable {u : SpatialField} {g : Fin 3 → SpatialField}

/-- Weak `div(u ⊗ u) = (u·∇)u` against vector tests. -/
theorem sum_inner_columns_testPartial (hu : MemLp u 2 volume) (hg : ∀ j, MemLp (g j) 2 volume)
    (hderiv : ∀ j, HasWeakSpatialDerivative j u (g j)) (hs : IsSolenoidal u)
    (hF : ∀ i, MemLp (velocityForcing u g i) 2 volume)
    (hcol : ∀ j, MemLp (tensorColumns u u j) 2 volume)
    {φ : Space → Space} (hφ : IsVectorTest φ) :
    ∑ j : Fin 3, inner ℝ (toL2 (tensorColumns u u j)) (toL2 (testPartial φ j)) =
      -inner ℝ (forcingL2 u g) (toL2 φ) := by
  have hf : ∀ i, IsSpatialTest (fun x => φ x i) := fun i => L10.isSpatialTest_testComponent hφ i
  have hFv := memLp_vecField_of_components hF
  have hφm : MemLp φ 2 volume := L10.vectorTest_memLp hφ 2
  -- left side
  have hL : ∀ j, inner ℝ (toL2 (tensorColumns u u j)) (toL2 (testPartial φ j)) =
      ∑ i : Fin 3, ∫ x, spatialTestDerivative j (fun y => φ y i) x * u x j * u x i := by
    intro j
    have hint : ∀ i, Integrable (fun x => spatialTestDerivative j (fun y => φ y i) x *
        u x j * u x i) := fun i =>
      weighted_product_integrable hu hu (((hf i).derivative j).memLp ⊤) j i
    rw [inner_toL2_eq_integral (hcol j) (L10.testPartial_memLp hφ j 2),
      ← integral_finsetSum _ fun i _ => hint i]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [inner_space_eq_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [tensorColumns_apply, ← L10.spatialTestDerivative_testComponent hφ i j x,
      show L10.testComponent φ i = fun y => φ y i from rfl]
    ring
  -- right side
  have hR : inner ℝ (forcingL2 u g) (toL2 φ) =
      ∑ i : Fin 3, ∫ x, (fun y => φ y i) x * velocityForcing u g i x := by
    have hint : ∀ i, Integrable (fun x => (fun y => φ y i) x * velocityForcing u g i x) :=
      fun i => memLp_one_iff_integrable.mp ((hF i).mul' ((hf i).memLp 2))
    rw [forcingL2, inner_toL2_eq_integral hFv hφm, ← integral_finsetSum _ fun i _ => hint i]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [inner_space_eq_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [vecField_apply]
    ring
  rw [Finset.sum_congr rfl fun j _ => hL j, hR,
    Finset.sum_congr rfl fun i _ => velocityForcing_test_identity hu hg hderiv hs (hf i) i,
    Finset.sum_neg_distrib, neg_neg, Finset.sum_comm]

/-- The `L²` form of the compiled pressure identity: `∫ p div φ = ⟨(I - 𝔓)F, φ⟩`. -/
theorem integral_velocityPressure_div_eq_inner (hu : MemLp u 2 volume)
    (hg : ∀ j, MemLp (g j) 2 volume) (hF : ∀ i, MemLp (velocityForcing u g i) 2 volume)
    {φ : Space → Space} (hφ : IsVectorTest φ) :
    ∫ x, velocityPressure u g x * ∑ i : Fin 3, testPartial φ i x i =
      inner ℝ (forcingL2 u g - Leray.projection (forcingL2 u g)) (toL2 φ) := by
  have hf : ∀ j, IsSpatialTest (fun x => φ x j) := fun j => L10.isSpatialTest_testComponent hφ j
  have hdiv : ∀ x, ∑ i : Fin 3, testPartial φ i x i =
      ∑ j : Fin 3, spatialTestDerivative j (fun y => φ y j) x := fun x =>
    Finset.sum_congr rfl fun i _ => (L10.spatialTestDerivative_testComponent hφ i i x).symm
  have hLHS : ∫ x, velocityPressure u g x * ∑ i : Fin 3, testPartial φ i x i =
      ∫ x, velocityPressure u g x *
        ∑ j : Fin 3, spatialTestDerivative j (fun y => φ y j) x :=
    integral_congr_ae (Eventually.of_forall fun x => by simp only [hdiv x])
  rw [hLHS, velocityPressure_pressure_identity hu hg hF φ hf, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_toL2 (L10.vectorTest_memLp hφ 2)] with x hx
  rw [hx]

/-- **`-𝔓 div(u ⊗ u) = -𝔓((u·∇)u)`.** -/
theorem isMinusLerayDiv_eq_neg_projection (hu : MemLp u 2 volume)
    (hg : ∀ j, MemLp (g j) 2 volume)
    (hderiv : ∀ j, HasWeakSpatialDerivative j u (g j)) (hs : IsSolenoidal u)
    (hF : ∀ i, MemLp (velocityForcing u g i) 2 volume)
    (hcol : ∀ j, MemLp (tensorColumns u u j) 2 volume)
    {N : L2Space} (hN : IsMinusLerayDiv (tensorColumns u u) N) :
    N = -Leray.projection (forcingL2 u g) := by
  have h : N - -Leray.projection (forcingL2 u g) = 0 := by
    refine L10.eq_zero_of_forall_vectorTest fun φ hφ => ?_
    have hN' := hN.2 φ hφ
    unfold lerayDivPairing at hN'
    rw [neg_neg] at hN'
    have hsplit : ∀ j, inner ℝ (toL2 (tensorColumns u u j))
        (Leray.projection (toL2 (testPartial φ j))) =
        inner ℝ (toL2 (tensorColumns u u j)) (toL2 (testPartial φ j)) -
          inner ℝ (toL2 (tensorColumns u u j))
            (toL2 (testPartial φ j) - Leray.projection (toL2 (testPartial φ j))) := by
      intro j
      rw [inner_sub_right]
      ring
    rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_sub_distrib,
      sum_inner_columns_testPartial hu hg hderiv hs hF hcol hφ] at hN'
    have hp := velocityPressure_div_identity hu hg hderiv hs hF hcol hφ
    rw [integral_velocityPressure_div_eq_inner hu hg hF hφ, inner_sub_left] at hp
    rw [inner_sub_left, inner_neg_left, hN']
    linarith
  rwa [sub_eq_zero] at h

/-- **Trilinear cancellation** `⟨-𝔓 div(u ⊗ u), u⟩ = 0`. -/
theorem inner_isMinusLerayDiv_eq_zero (hu : MemLp u 2 volume)
    (hg : ∀ j, MemLp (g j) 2 volume)
    (hderiv : ∀ j, HasWeakSpatialDerivative j u (g j)) (hs : IsSolenoidal u)
    (hF : ∀ i, MemLp (velocityForcing u g i) 2 volume)
    (hcol : ∀ j, MemLp (tensorColumns u u j) 2 volume)
    {N : L2Space} (hN : IsMinusLerayDiv (tensorColumns u u) N) :
    inner ℝ N (toL2 u) = 0 := by
  have hFv := memLp_vecField_of_components hF
  rw [isMinusLerayDiv_eq_neg_projection hu hg hderiv hs hF hcol hN, inner_neg_left,
    Leray.projection_selfadjoint, Leray.projection_toL2_eq_self hu hs, forcingL2,
    inner_toL2_eq_integral hFv hu]
  have hint : ∀ i, Integrable (fun x => velocityForcing u g i x * u x i) := fun i =>
    memLp_one_iff_integrable.mp ((EnergyInterpolation.coordinate_memLp hu i).mul' (hF i))
  have he : ∫ x, inner ℝ (vecField (velocityForcing u g) x) (u x) =
      ∑ i : Fin 3, ∫ x, velocityForcing u g i x * u x i := by
    rw [← integral_finsetSum _ fun i _ => hint i]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [inner_space_eq_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [vecField_apply]
  rw [he, Finset.sum_congr rfl fun i _ =>
    integral_coord_mul_forcing_eq_zero hu hg hderiv hs hF hcol i]
  simp

end Identities

end UnforcedLeray.Blueprint.L14
