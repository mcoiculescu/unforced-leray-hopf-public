import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_1_2_11
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.MeanMomentumU

/-!


Source: `the November 2 reference manuscript`, lines 3056-3057.
`k = 0`: for each `η`, the `q`-integral over one period of `∂_q ψ` vanishes
(`UnforcedLeray.Short.PartI.mm_integral_partialQ_zero`), and Fubini gives the cell integral.
`k = 1`: for each `q`, `η ↦ ∂_η ψ(q, η)` is continuous with compact support and is the
derivative of the compactly supported `η ↦ ψ(q, η)`, so its `η`-integral vanishes; Fubini.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The cell as a product set, with the product of the two restricted measures. -/
theorem vdm_cell_prod (a b : ℝ) :
    ((volume : Measure ℝ).restrict (Ico a b)).prod ((volume : Measure ℝ).restrict (univ : Set ℝ)) =
      (volume : Measure (ℝ × ℝ)).restrict (Ico a b ×ˢ univ) := by
  rw [Measure.prod_restrict]
  rfl

theorem vdm_cell_integral (c : ℝ) (f : ℝ × ℝ → ℝ) :
    ∫ y in B0579.cell c, f y =
      ∫ y, f y ∂(((volume : Measure ℝ).restrict (Ico (-(c / 2)) (c / 2))).prod
        ((volume : Measure ℝ).restrict (univ : Set ℝ))) := by
  rw [vdm_cell_prod]
  rfl

theorem vdm_integrable_prod (c : ℝ) (f : ℝ × ℝ → ℝ) (hf : IntegrableOn f (B0579.cell c)) :
    Integrable f (((volume : Measure ℝ).restrict (Ico (-(c / 2)) (c / 2))).prod
      ((volume : Measure ℝ).restrict (univ : Set ℝ))) := by
  rw [vdm_cell_prod]
  exact hf

/-- A function of one real variable vanishing for `|η| > R` tends to `0` at both ends. -/
theorem vdm_tendsto_zero {f : ℝ → ℝ} {R : ℝ} (hR : ∀ η : ℝ, R < |η| → f η = 0) :
    Tendsto f atBot (𝓝 0) ∧ Tendsto f atTop (𝓝 0) := by
  constructor
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_lt_atBot (-|R|)] with η hη
    have hneg : η < 0 := lt_of_lt_of_le hη (by linarith [abs_nonneg R])
    have hRη : R < |η| := by
      rw [abs_of_neg hneg]
      linarith [le_abs_self R]
    exact (hR η hRη).symm
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (|R|)] with η hη
    have hpos : 0 < η := lt_of_le_of_lt (abs_nonneg R) hη
    have hRη : R < |η| := by
      rw [abs_of_pos hpos]
      linarith [le_abs_self R]
    exact (hR η hRη).symm

/-- For a cylinder test `ψ`, the `η`-integral of `∂_η ψ(q, ·)` vanishes for every `q`. -/
theorem vdm_eta_integral_zero {c : ℝ} {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest c ψ) (q : ℝ) :
    ∫ η, B0579.pd 1 ψ (q, η) = 0 := by
  obtain ⟨R, hR⟩ := hψ.band
  obtain ⟨R', hR'⟩ := (hψ.pd 1).band
  have hderiv : ∀ η : ℝ, HasDerivAt (fun t => ψ (q, t)) (B0579.pd 1 ψ (q, η)) η :=
    fun η => B0579.hasDerivAt_snd hψ.differentiable q η
  have hcont : Continuous (fun η => B0579.pd 1 ψ (q, η)) :=
    (hψ.pd 1).continuous.comp (continuous_const.prodMk continuous_id)
  have hcs : HasCompactSupport (fun η => B0579.pd 1 ψ (q, η)) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -|R'|) (b := |R'|)) ?_
    intro η hη
    have h1 : |R'| < |η| := by
      by_contra h
      exact hη ⟨(abs_le.1 (not_lt.1 h)).1, (abs_le.1 (not_lt.1 h)).2⟩
    exact hR' (q, η) (lt_of_le_of_lt (le_abs_self R') h1)
  have hint : Integrable (fun η => B0579.pd 1 ψ (q, η)) :=
    hcont.integrable_of_hasCompactSupport hcs
  obtain ⟨hbot, htop⟩ :=
    vdm_tendsto_zero (f := fun η => ψ (q, η)) (R := R) (fun η hη => hR (q, η) hη)
  have key : ∫ η, B0579.pd 1 ψ (q, η) = 0 - 0 :=
    integral_of_hasDerivAt_of_tendsto (f := fun η => ψ (q, η))
      (f' := fun η => B0579.pd 1 ψ (q, η)) hderiv hint hbot htop
  rw [key, sub_self]

/-- For a cylinder test `ψ`, the `q`-integral of `∂_q ψ(·, η)` over one period vanishes. -/
theorem vdm_pd_zero_q {c : ℝ} (hc : 0 < c) {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest c ψ)
    (η : ℝ) :
    ∫ q in Ico (-(c / 2)) (c / 2), B0579.pd 0 ψ (q, η) = 0 := by
  have hfun : ∀ q : ℝ, B0579.pd 0 ψ (q, η) = UnforcedLeray.Cyl.partialQ ψ (q, η) :=
    fun q => (B0579.hasDerivAt_fst hψ.differentiable q η).deriv.symm
  simp only [hfun]
  rw [integral_Ico_eq_integral_Ioc, show -(c / 2) = -c / 2 by ring]
  exact UnforcedLeray.Short.PartI.mm_integral_partialQ_zero hc hψ.smooth hψ.periodic η

theorem vdm_k0 (c : ℝ) (hc : 0 < c) {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest c ψ) :
    ∫ y in B0579.cell c, B0579.pd 0 ψ y = 0 := by
  have hint : IntegrableOn (B0579.pd 0 ψ) (B0579.cell c) := (hψ.pd 0).integrableOn
  rw [vdm_cell_integral, integral_prod_symm _ (vdm_integrable_prod c _ hint)]
  have hz : ∀ η : ℝ, ∫ q in Ico (-(c / 2)) (c / 2), B0579.pd 0 ψ (q, η) = 0 :=
    fun η => vdm_pd_zero_q hc hψ η
  simp only [hz]
  simp

theorem vdm_k1 (c : ℝ) {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest c ψ) :
    ∫ y in B0579.cell c, B0579.pd 1 ψ y = 0 := by
  have hint : IntegrableOn (B0579.pd 1 ψ) (B0579.cell c) := (hψ.pd 1).integrableOn
  rw [vdm_cell_integral, integral_prod _ (vdm_integrable_prod c _ hint)]
  simp only [Measure.restrict_univ, vdm_eta_integral_zero hψ]
  simp

theorem kerVelDerivMeanZero : UnforcedLeray.Short.IIIa.KerVelDerivMeanZero := by
  intro d hd ψ hψ k
  have hc : 0 < d := by linarith
  fin_cases k
  · exact vdm_k0 d hc hψ
  · exact vdm_k1 d hψ

end UnforcedLeray.Short.IIIa
