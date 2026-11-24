import UnforcedLeray.Short.PartI.Sub.C09
import UnforcedLeray.Short.PartI.Sub.C09.RadialGreenIdentity
import UnforcedLeray.Short.PartI.Sub.C09.PolarReduction

/-!
# Part I, task `PartI:C09`, Step 1: the punctured weak Green equation

Source of record: `the November 2 reference manuscript`, lines 1139-1140
("the radial Green formula for `Δ₂⁻¹`"). This file proves `greenWeakPunctured : GreenWeakPunctured`
from `radialGreenIdentity` (Step 1a) and `polarReduction` (Step 1b). The glue is local integrability
on `(0, ∞)` of the profile `f` and of `R f`:

* `f ∈ X_G` is integrable on every `[a, b] ⊂ (0, ∞)` (`gwp_integrableOn_Icc`), using the AM-GM
  bound `2 r |f(r)| ≤ |f(r)|² G(r)⁻¹ r + r G(r)` (`B0011.two_mul_pow_le`) and `G ≤ (4π)⁻¹`.
* `R f` is continuous on `(0, ∞)` (`B0012.continuousOn_R`), hence locally integrable there.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartI

/-- An `X_G` profile is integrable on every compact subinterval `[a, b]` of `(0, ∞)`. -/
theorem gwp_integrableOn_Icc {f : ℝ → ℂ} (hf : B0011.MemXG f) {a b : ℝ} (ha : 0 < a) :
    IntegrableOn f (Icc a b) volume := by
  have hsub : Icc a b ⊆ Ioi 0 := fun r hr => lt_of_lt_of_le ha hr.1
  have hg : IntegrableOn (fun r : ℝ => ‖f r‖ ^ 2 * (B0011.gaussG r)⁻¹ * r) (Icc a b) volume :=
    IntegrableOn.mono_set hf.2 hsub
  have hgI : Integrable (fun r : ℝ => ‖f r‖ ^ 2 * (B0011.gaussG r)⁻¹ * r)
      (volume.restrict (Icc a b)) := hg
  have hc : IntegrableOn (fun _ : ℝ => b * (4 * Real.pi)⁻¹ / (2 * a)) (Icc a b) volume :=
    integrableOn_const measure_Icc_lt_top.ne
  have hbound : Integrable (fun r : ℝ => b * (4 * Real.pi)⁻¹ / (2 * a) +
      1 / (2 * a) * (‖f r‖ ^ 2 * (B0011.gaussG r)⁻¹ * r)) (volume.restrict (Icc a b)) :=
    Integrable.add hc (Integrable.const_mul hgI _)
  have hmeas : AEStronglyMeasurable f (volume.restrict (Icc a b)) :=
    hf.1.mono_measure (Measure.restrict_mono hsub le_rfl)
  show Integrable f (volume.restrict (Icc a b))
  refine Integrable.mono' hbound hmeas ?_
  refine ae_restrict_of_forall_mem measurableSet_Icc fun r hr => ?_
  have hr0 : 0 < r := lt_of_lt_of_le ha hr.1
  have hH := B0011.two_mul_pow_le (x := ‖f r‖) (B0011.gaussG_pos r) hr0.le 0
  simp only [zero_add, pow_one, mul_zero] at hH
  have hGc : B0011.gaussG r ≤ (4 * Real.pi)⁻¹ := by
    unfold B0011.gaussG
    exact mul_le_of_le_one_right (by positivity) (B0012.radialOmega_le_one r)
  have hrG : r * B0011.gaussG r ≤ b * (4 * Real.pi)⁻¹ :=
    calc r * B0011.gaussG r ≤ r * (4 * Real.pi)⁻¹ := mul_le_mul_of_nonneg_left hGc hr0.le
      _ ≤ b * (4 * Real.pi)⁻¹ := mul_le_mul_of_nonneg_right hr.2 (by positivity)
  have hax : a * ‖f r‖ ≤ r * ‖f r‖ := mul_le_mul_of_nonneg_right hr.1 (norm_nonneg _)
  have h2a : (0 : ℝ) < 2 * a := by linarith
  have h3 : ‖f r‖ * (2 * a) ≤ ‖f r‖ ^ 2 * (B0011.gaussG r)⁻¹ * r + b * (4 * Real.pi)⁻¹ := by
    linarith
  have hfin : ‖f r‖ ≤ (‖f r‖ ^ 2 * (B0011.gaussG r)⁻¹ * r + b * (4 * Real.pi)⁻¹) / (2 * a) :=
    (le_div_iff₀ h2a).2 h3
  calc ‖f r‖ ≤ (‖f r‖ ^ 2 * (B0011.gaussG r)⁻¹ * r + b * (4 * Real.pi)⁻¹) / (2 * a) := hfin
    _ = b * (4 * Real.pi)⁻¹ / (2 * a) +
          1 / (2 * a) * (‖f r‖ ^ 2 * (B0011.gaussG r)⁻¹ * r) := by ring

/-- An `X_G` profile is locally integrable on `(0, ∞)`. -/
theorem gwp_locInt {f : ℝ → ℂ} (hf : B0011.MemXG f) :
    LocallyIntegrableOn f (Ioi 0) volume := by
  unfold LocallyIntegrableOn IntegrableAtFilter
  intro x hx
  have hx0 : (0 : ℝ) < x := hx
  exact ⟨Icc (x / 2) (2 * x),
    mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds (by linarith) (by linarith)),
    gwp_integrableOn_Icc hf (by linarith)⟩

/-- **Step 1** (source lines 1139-1140, "the radial Green formula for `Δ₂⁻¹`"): for `f ∈ X_G`,
the planar function `u = Rf(r)e^{2iϑ}` solves `Δu = f(r)e^{2iϑ}` weakly on `ℝ² \ {0}`. -/
theorem greenWeakPunctured : GreenWeakPunctured := by
  unfold GreenWeakPunctured
  intro f
  have hf : B0011.MemXG ⇑f := B0012.memXG_coe f
  have hfloc : LocallyIntegrableOn (⇑f) (Ioi 0) volume := gwp_locInt hf
  have hRloc : LocallyIntegrableOn (B0011.R ⇑f) (Ioi 0) volume :=
    (B0012.continuousOn_R f).locallyIntegrableOn measurableSet_Ioi
  have hrad := radialGreenIdentity (⇑f) (B0011.R ⇑f) hfloc (B0012.isDelta2Sol_R_coe f)
  exact polarReduction (B0011.R ⇑f) (⇑f) hRloc hfloc hrad

end UnforcedLeray.Short.PartI

end
