import UnforcedLeray.Short.Interface.Leaf2_Integrability.CouplingBound

/-!
# Interface I10, part 3: the coupling pairing is integrable in phase

Helper for `Short/Interface/Leaf2_Integrability.lean`. Combines the measurability and bound
lemmas of `CouplingBound.lean`: for a continuous background `V` with `‖V‖ ≤ C` (jointly
measurable), a `𝒯`-periodic `b ∈ 𝒴_{2,div}` and a similarity test `ψ`,
`τ ↦ weakCoupling V b ψ τ` is integrable on `ℝ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.Interface.Leaf2_Integrability

open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Cons.C08

/-- **The coupling pairing is integrable in phase** (`ModeSolutionIntegrability`, last clause). -/
theorem integrable_weakCoupling {P : ℝ} (hP : 0 < P) {V b : ℝ → SpatialField}
    (hVc : ∀ τ, Continuous (V τ)) {C : ℝ} (hVC : ∀ τ y, ‖V τ y‖ ≤ C)
    (hVm : AEStronglyMeasurable (fun z : SpaceTime => V z.1 z.2) volume)
    (hb : IsY2Div P b) {ψ : SpaceTime → Space} (hψ : IsSimilarityTest ψ) :
    Integrable (weakCoupling V b ψ) := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hVC 0 0)
  obtain ⟨R, -, hRT, -⟩ := B0005.exists_window_of_hasCompactSupport hψ.compact
  have hbL2 : ∀ᵐ τ : ℝ, MemLp (b τ) 2 volume := ModeId.Y2.ae_memLp hP hb
  have hcolL2 : ∀ᵐ τ : ℝ, ColumnsL2 (symTensorColumns (V τ) (b τ)) :=
    hbL2.mono fun τ hτ => columnsL2_symTensor (hVc τ) (hVC τ) hτ
  choose M hM using fun j : Fin 3 => exists_slice_bound hψ j
  -- joint representatives of the projected derivative slices
  have hrep : ∀ j : Fin 3, ∃ F : ℝ × Space → Space, StronglyMeasurable F ∧
      ∀ᵐ τ : ℝ, (fun y => F (τ, y)) =ᵐ[volume]
        (Blueprint.projectedPartial (Blueprint.slice ψ τ) j : Space → Space) := by
    intro j
    have hD : MemLp (UnforcedLeray.PhaseSpace.dy j ψ) 2 (volume : Measure (ℝ × Space)) :=
      (dy_continuous_hasCompactSupport hψ j).1.memLp_of_hasCompactSupport
        (dy_continuous_hasCompactSupport hψ j).2
    obtain ⟨F, hFm, hF⟩ := exists_joint_projection hD
    refine ⟨F, hFm, ?_⟩
    filter_upwards [hF] with τ hτ
    have hfun : (fun y => UnforcedLeray.PhaseSpace.dy j ψ (τ, y)) =
        Blueprint.testPartial (Blueprint.slice ψ τ) j := by
      funext y
      exact (testPartial_slice_eq hψ.smooth j τ y).symm
    rw [hfun] at hτ
    exact hτ
  choose Fj hFjm hFj using hrep
  -- measurability in phase, by Fubini in space
  have hcolm : ∀ j : Fin 3, AEStronglyMeasurable
      (fun z : SpaceTime => symTensorColumns (V z.1) (b z.1) j z.2) volume := by
    intro j
    have hbm : AEStronglyMeasurable (fun z : SpaceTime => b z.1 z.2) volume := hb.measurable
    have h1 : AEStronglyMeasurable (fun z : SpaceTime => (b z.1 z.2) j) volume :=
      (PiLp.continuous_apply 2 _ j).comp_aestronglyMeasurable hbm
    have h2 : AEStronglyMeasurable (fun z : SpaceTime => (V z.1 z.2) j) volume :=
      (PiLp.continuous_apply 2 _ j).comp_aestronglyMeasurable hVm
    exact (h1.smul hVm).add (h2.smul hbm)
  have hHm : ∀ j : Fin 3, AEStronglyMeasurable
      (fun z : SpaceTime => inner ℝ (symTensorColumns (V z.1) (b z.1) j z.2) (Fj j z)) volume :=
    fun j => (hcolm j).inner (hFjm j).aestronglyMeasurable
  have hIm : ∀ j : Fin 3, AEStronglyMeasurable
      (fun τ : ℝ => ∫ y, inner ℝ (symTensorColumns (V τ) (b τ) j y) (Fj j (τ, y))) volume := by
    intro j
    have hprod : AEStronglyMeasurable
        (fun z : SpaceTime => inner ℝ (symTensorColumns (V z.1) (b z.1) j z.2) (Fj j z))
        ((volume : Measure ℝ).prod (volume : Measure Space)) := by
      rw [← Measure.volume_eq_prod]
      exact hHm j
    exact AEStronglyMeasurable.integral_prod_right' (ν := (volume : Measure Space)) hprod
  -- the coupling is a.e. the Fubini integral of the projected representatives
  have hWC : (fun τ : ℝ => -∑ j : Fin 3,
      ∫ y, inner ℝ (symTensorColumns (V τ) (b τ) j y) (Fj j (τ, y)))
      =ᵐ[volume] weakCoupling V b ψ := by
    filter_upwards [ae_all_iff.2 hFj] with τ hτ
    unfold weakCoupling lerayDivIntegral
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    have hae : (fun y => inner ℝ (symTensorColumns (V τ) (b τ) j y) (Fj j (τ, y))) =ᵐ[volume]
        (fun y => lerayDivIntegrand (symTensorColumns (V τ) (b τ)) (Blueprint.slice ψ τ) j y) := by
      filter_upwards [hτ j] with y hy
      have hy' : Fj j (τ, y) = Blueprint.projectedPartial (Blueprint.slice ψ τ) j y := hy
      simp only [lerayDivIntegrand]
      rw [hy']
    exact integral_congr_ae hae
  have hWCm : AEStronglyMeasurable (weakCoupling V b ψ) volume :=
    AEStronglyMeasurable.congr
      ((Finset.aestronglyMeasurable_fun_sum Finset.univ fun j _ => hIm j).neg) hWC
  -- the majorant
  have hIcc : IntegrableOn (fun τ : ℝ => ‖toL2 (b τ)‖) (Icc (-R) R) := by
    have h1 : IntegrableOn (fun τ : ℝ => toL2 (b τ)) (Icc (-R) R) :=
      (ModeId.Y2.integrableOn hP hb (-R - 1) (R + 1)).mono_set
        (Icc_subset_Ioo (by linarith) (by linarith))
    exact Integrable.norm h1
  have hmaj : Integrable (fun τ : ℝ => (2 * C * ∑ j : Fin 3, M j) *
      Set.indicator (Icc (-R) R) (fun τ : ℝ => ‖toL2 (b τ)‖) τ) :=
    (hIcc.integrable_indicator measurableSet_Icc).const_mul _
  have hbound : ∀ᵐ τ : ℝ, ‖weakCoupling V b ψ τ‖ ≤
      (2 * C * ∑ j : Fin 3, M j) * Set.indicator (Icc (-R) R) (fun τ : ℝ => ‖toL2 (b τ)‖) τ := by
    filter_upwards [hcolL2, hbL2] with τ hcol hv
    have hc : 0 ≤ 2 * C * ‖toL2 (b τ)‖ := mul_nonneg (mul_nonneg (by norm_num) hC0) (norm_nonneg _)
    have hW : ‖weakCoupling V b ψ τ‖ ≤
        ∑ j : Fin 3, (2 * C * ‖toL2 (b τ)‖) *
          ‖toL2 (Blueprint.testPartial (Blueprint.slice ψ τ) j)‖ := by
      have e : weakCoupling V b ψ τ =
          lerayDivPairing (symTensorColumns (V τ) (b τ)) (Blueprint.slice ψ τ) :=
        lerayDivIntegral_eq_lerayDivPairing hcol (Blueprint.slice ψ τ)
      rw [e]
      refine (norm_lerayDivPairing_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      exact mul_le_mul_of_nonneg_right
        (norm_toL2_symTensorColumns_le (hVc τ) (hVC τ) hv j) (norm_nonneg _)
    by_cases hτI : τ ∈ Icc (-R) R
    · rw [Set.indicator_apply, if_pos hτI]
      refine hW.trans ?_
      calc ∑ j : Fin 3, (2 * C * ‖toL2 (b τ)‖) *
            ‖toL2 (Blueprint.testPartial (Blueprint.slice ψ τ) j)‖
          ≤ ∑ j : Fin 3, (2 * C * ‖toL2 (b τ)‖) * M j :=
            Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hM j τ) hc
        _ = (2 * C * ‖toL2 (b τ)‖) * ∑ j : Fin 3, M j := by rw [Finset.mul_sum]
        _ = (2 * C * ∑ j : Fin 3, M j) * ‖toL2 (b τ)‖ := by ring
    · rw [Set.indicator_apply, if_neg hτI, mul_zero]
      have hz : ∀ j : Fin 3, (2 * C * ‖toL2 (b τ)‖) *
          ‖toL2 (Blueprint.testPartial (Blueprint.slice ψ τ) j)‖ ≤ 0 := fun j =>
        (mul_le_mul_of_nonneg_left (slice_norm_le_zero hψ hRT j hτI) hc).trans
          (le_of_eq (mul_zero _))
      exact hW.trans (Finset.sum_nonpos fun j _ => hz j)
  exact hmaj.mono' hWCm hbound

end UnforcedLeray.Short.Interface.Leaf2_Integrability
