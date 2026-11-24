import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.LeavesOf

/-!
# Part III-a, `PartIII-a:T21/2/7/1/8/5/1/1`: unfolding the periodic lift against a test

Source of record: `the November 2 reference manuscript` (SP), lines 2819-2836.
`adjKerUnfold_of_integrable` proves the unfolding identity from the absolute integrability of
`(x, y) ↦ k(x - y) f̃(y) ψ(x)` on `C_c × ℝ²` (the leaf `AdjKerUnfoldInt`): the substitution
`y = x - z`, Fubini, the translation invariance of cell integrals of periodic functions.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem adjUnf_cell_eq (c : ℝ) : B0579.cell c = UnforcedLeray.Cyl.cell c := by
  simp only [B0579.cell, UnforcedLeray.Cyl.cell, neg_div]

theorem adjUnf_periodic_shift {c : ℝ} {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest c ψ) (z : ℝ × ℝ) :
    UnforcedLeray.Cyl.IsPeriodic c (fun y => ψ (y + z)) := by
  intro y
  have hx : (y.1 + c, y.2) + z = ((y + z).1 + c, (y + z).2) := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
  show ψ ((y.1 + c, y.2) + z) = ψ (y + z)
  rw [hx]
  exact hψ.periodic (y + z)

theorem adjKerUnfold_of_integrable {c : ℝ} (hc : 0 < c) {k : ℝ × ℝ → ℝ} (hk : Continuous k)
    {f : ℝ × ℝ → ℂ} (hf : StronglyMeasurable f) {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest c ψ)
    (hint : Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      (k (p.1 - p.2) : ℂ) * perRep c f p.2 * (ψ p.1 : ℂ))
      ((volume.restrict (B0579.cell c)).prod volume)) :
    ∫ x in B0579.cell c, adjKerOp c k f x * (ψ x : ℂ) =
      ∫ x in B0579.cell c, f x * ((∫ z, k z * ψ (x + z) : ℝ) : ℂ) := by
  classical
  have hgm : StronglyMeasurable (perRep c f) := stronglyMeasurable_perRep hc hf
  have hgper : UnforcedLeray.Cyl.IsPeriodic c (perRep c f) := fun z => perRep_periodic hc f z
  have hψc : Continuous ψ := hψ.continuous
  have hψm : Measurable ψ := hψc.measurable
  have hkm : Measurable k := hk.measurable
  have hμ : volume.restrict (B0579.cell c) = volume.restrict (UnforcedLeray.Cyl.cell c) := by
    rw [adjUnf_cell_eq]
  -- the substituted integrand
  have hG : Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      (k p.2 : ℂ) * perRep c f (p.1 - p.2) * (ψ p.1 : ℂ))
      ((volume.restrict (B0579.cell c)).prod volume) := by
    have hmp1 := measurePreserving_prod_sub (volume.restrict (B0579.cell c))
      (volume : Measure (ℝ × ℝ))
    have hmp2 : MeasurePreserving (Prod.map (id : ℝ × ℝ → ℝ × ℝ) (Neg.neg : ℝ × ℝ → ℝ × ℝ))
        ((volume.restrict (B0579.cell c)).prod volume)
        ((volume.restrict (B0579.cell c)).prod volume) :=
      (MeasurePreserving.id _).prod (Measure.measurePreserving_neg _)
    have h := (hmp2.comp hmp1).integrable_comp_of_integrable hint
    refine h.congr (Eventually.of_forall fun p => ?_)
    simp [Function.comp, Prod.map, sub_sub_cancel, neg_sub]
  -- the shifted integrand
  have hH : Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      (k p.2 : ℂ) * perRep c f p.1 * (ψ (p.1 + p.2) : ℂ))
      ((volume.restrict (B0579.cell c)).prod volume) := by
    refine ⟨?_, ?_⟩
    · have h1 : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => (k p.2 : ℂ)) :=
        (Complex.measurable_ofReal.comp (hkm.comp measurable_snd))
      have h2 : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => (ψ (p.1 + p.2) : ℂ)) :=
        Complex.measurable_ofReal.comp (hψm.comp (measurable_fst.add measurable_snd))
      exact ((h1.aestronglyMeasurable.mul
        (hgm.measurable.comp measurable_fst).aestronglyMeasurable).mul h2.aestronglyMeasurable)
    · have hmeasH : AEMeasurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
          ‖(k p.2 : ℂ) * perRep c f p.1 * (ψ (p.1 + p.2) : ℂ)‖ₑ)
          ((volume.restrict (B0579.cell c)).prod volume) := by
        have h1 : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => (k p.2 : ℂ)) :=
          (Complex.measurable_ofReal.comp (hkm.comp measurable_snd))
        have h2 : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => (ψ (p.1 + p.2) : ℂ)) :=
          Complex.measurable_ofReal.comp (hψm.comp (measurable_fst.add measurable_snd))
        exact ((h1.mul (hgm.measurable.comp measurable_fst)).mul h2).enorm.aemeasurable
      have hmeasG : AEMeasurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
          ‖(k p.2 : ℂ) * perRep c f (p.1 - p.2) * (ψ p.1 : ℂ)‖ₑ)
          ((volume.restrict (B0579.cell c)).prod volume) := hG.aestronglyMeasurable.enorm
      unfold HasFiniteIntegral
      rw [lintegral_prod_symm _ hmeasH]
      have hGfin := hG.hasFiniteIntegral
      unfold HasFiniteIntegral at hGfin
      rw [lintegral_prod_symm _ hmeasG] at hGfin
      refine lt_of_le_of_lt (le_of_eq ?_) hGfin
      refine lintegral_congr fun z => ?_
      have hper : UnforcedLeray.Cyl.IsPeriodic c (fun y =>
          ‖(k z : ℂ) * perRep c f y * (ψ (y + z) : ℂ)‖ₑ) := by
        intro y
        have h1 := hgper y
        have h2 := adjUnf_periodic_shift hψ z y
        simp only at h2
        simp only [h1, h2]
      have h : ∫⁻ x in UnforcedLeray.Cyl.cell c,
          ‖(k z : ℂ) * perRep c f (x + -z) * (ψ (x + -z + z) : ℂ)‖ₑ =
          ∫⁻ x in UnforcedLeray.Cyl.cell c, ‖(k z : ℂ) * perRep c f x * (ψ (x + z) : ℂ)‖ₑ :=
        UnforcedLeray.Cyl.lintegral_cell_comp_add hc hper (-z)
      have e1 : ∫⁻ x in B0579.cell c, ‖(k z : ℂ) * perRep c f x * (ψ (x + z) : ℂ)‖ₑ =
          ∫⁻ x in UnforcedLeray.Cyl.cell c, ‖(k z : ℂ) * perRep c f x * (ψ (x + z) : ℂ)‖ₑ := by
        rw [adjUnf_cell_eq]
      have e2 : ∫⁻ x in B0579.cell c, ‖(k z : ℂ) * perRep c f (x - z) * (ψ x : ℂ)‖ₑ =
          ∫⁻ x in UnforcedLeray.Cyl.cell c,
            ‖(k z : ℂ) * perRep c f (x + -z) * (ψ (x + -z + z) : ℂ)‖ₑ := by
        rw [adjUnf_cell_eq]
        refine lintegral_congr fun x => ?_
        simp [sub_eq_add_neg]
      exact e1.trans (h.symm.trans e2.symm)
  have step1 : ∀ x : ℝ × ℝ, adjKerOp c k f x * (ψ x : ℂ) =
      ∫ z, (k z : ℂ) * perRep c f (x - z) * (ψ x : ℂ) := by
    intro x
    have h := integral_sub_left_eq_self
      (fun y => (k (x - y) : ℂ) * perRep c f y * (ψ x : ℂ)) volume x
    unfold adjKerOp
    rw [← integral_mul_const, ← h]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp [sub_sub_cancel]
  have hshift : ∀ z : ℝ × ℝ, ∫ x in B0579.cell c, (k z : ℂ) * perRep c f (x - z) * (ψ x : ℂ) =
      ∫ x in B0579.cell c, (k z : ℂ) * perRep c f x * (ψ (x + z) : ℂ) := by
    intro z
    have hper : UnforcedLeray.Cyl.IsPeriodic c (fun y =>
        (k z : ℂ) * perRep c f y * (ψ (y + z) : ℂ)) := by
      intro y
      have h1 := hgper y
      have h2 := adjUnf_periodic_shift hψ z y
      simp only at h2
      simp only [h1, h2]
    have h : ∫ x in UnforcedLeray.Cyl.cell c,
        (k z : ℂ) * perRep c f (x + -z) * (ψ (x + -z + z) : ℂ) =
        ∫ x in UnforcedLeray.Cyl.cell c, (k z : ℂ) * perRep c f x * (ψ (x + z) : ℂ) :=
      UnforcedLeray.Cyl.integral_cell_comp_add hc hper (-z)
    rw [adjUnf_cell_eq, ← h]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [sub_eq_add_neg]
  have hrhs : ∀ x : ℝ × ℝ, ∫ z, (k z : ℂ) * perRep c f x * (ψ (x + z) : ℂ) =
      perRep c f x * ((∫ z, k z * ψ (x + z) : ℝ) : ℂ) := by
    intro x
    rw [← integral_complex_ofReal, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    push_cast
    ring
  calc ∫ x in B0579.cell c, adjKerOp c k f x * (ψ x : ℂ)
      = ∫ x in B0579.cell c, ∫ z, (k z : ℂ) * perRep c f (x - z) * (ψ x : ℂ) :=
        integral_congr_ae (Eventually.of_forall step1)
    _ = ∫ z, ∫ x in B0579.cell c, (k z : ℂ) * perRep c f (x - z) * (ψ x : ℂ) :=
        integral_integral_swap (f := fun x z => (k z : ℂ) * perRep c f (x - z) * (ψ x : ℂ)) hG
    _ = ∫ z, ∫ x in B0579.cell c, (k z : ℂ) * perRep c f x * (ψ (x + z) : ℂ) :=
        integral_congr_ae (Eventually.of_forall hshift)
    _ = ∫ x in B0579.cell c, ∫ z, (k z : ℂ) * perRep c f x * (ψ (x + z) : ℂ) :=
        (integral_integral_swap
          (f := fun x z => (k z : ℂ) * perRep c f x * (ψ (x + z) : ℂ)) hH).symm
    _ = ∫ x in B0579.cell c, f x * ((∫ z, k z * ψ (x + z) : ℝ) : ℂ) := by
        refine integral_congr_ae ?_
        filter_upwards [perRep_ae_cell hc f] with x hx
        rw [hrhs, hx]

end UnforcedLeray.Short.IIIa
