import UnforcedLeray.Short.PartIIb.Tasks.QuadraticEstimate
import UnforcedLeray.Short.PartIIa.Sub.F03Rep
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GradL2pIBP

/-!
# Cell `L^{q₀}` norms versus `Y_{q₀}` norms (helper for `PartII-b:S1/1/2`)

Source `the November 2 reference manuscript`, lines
1478-1480 (`Y_p` is normalized by the period): on the period cell `(0,P] × ℝ³`, a representative of
`a ∈ Y_{q₀}` has `L^{q₀}` norm `P^{1/q₀} ‖a‖`, and a field with `phaseLpNorm ≤ B` has cell norm
`≤ P^{1/q₀} B`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb.QuadBoundSub

open UnforcedLeray.PhaseSpace
open UnforcedLeray.Cons.C03.Concrete (rep stronglyMeasurable_rep rep_slice)
open UnforcedLeray.Short.PartIIa.Rep
open UnforcedLeray.Short.PartIIIb.Concrete (phaseμ)
open UnforcedLeray.B0412 (q0E q0E_ne_top)

/-- The cell `L^q` integral of a representative. -/
theorem cell_lintegral' {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : q ≠ ⊤)
    {a : Yq P q} {Λ : ℝ × Space → CVec3} (hΛ : IsRep a Λ) :
    ∫⁻ x in Ioc (0 : ℝ) P ×ˢ (univ : Set Space), ‖Λ x‖ₑ ^ q.toReal =
      ENNReal.ofReal P * ‖a‖ₑ ^ q.toReal := by
  have hprod : (volume : Measure (ℝ × Space)).restrict (Ioc (0 : ℝ) P ×ˢ (univ : Set Space)) =
      ((volume : Measure ℝ).restrict (Ioc 0 P)).prod (volume : Measure Space) := by
    simpa only [Measure.volume_eq_prod] using
      (Measure.restrict_prod_eq_prod_univ (μ := (volume : Measure ℝ))
        (ν := (volume : Measure Space)) (Ioc 0 P)).symm
  have hmeas : AEMeasurable (fun x : ℝ × Space => ‖Λ x‖ₑ ^ q.toReal)
      (((volume : Measure ℝ).restrict (Ioc 0 P)).prod (volume : Measure Space)) :=
    (hΛ.meas.measurable.enorm.pow_const _).aemeasurable
  rw [hprod, lintegral_prod _ hmeas]
  have h1 : ∫⁻ τ in Ioc (0 : ℝ) P, ∫⁻ y, ‖Λ (τ, y)‖ₑ ^ q.toReal =
      ∫⁻ τ in Ioc (0 : ℝ) P, ‖a (τ : AddCircle P)‖ₑ ^ q.toReal := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_of_ae hΛ.slice] with τ hτ
    rw [← UnforcedLeray.PhaseSpace.lintegral_enorm_rpow_Lp _ hq]
    refine lintegral_congr_ae ?_
    filter_upwards [hτ] with y hy
    rw [hy]
  rw [h1]
  have h2 := UnforcedLeray.PhaseSpace.lintegral_Ioc_period (P := P)
    (fun θ : AddCircle P => ‖a θ‖ₑ ^ q.toReal) 0 0
  simp only [zero_add] at h2
  rw [h2, AddCircle.volume_eq_smul_haarAddCircle, lintegral_smul_measure,
    UnforcedLeray.PhaseSpace.lintegral_enorm_rpow_Yq a hq]
  rfl

/-- The cell `L^{q₀}` norm of a representative, on the phase measure. -/
theorem eLpNorm_phaseμ_rep {P : ℝ} [Fact (0 < P)] {a : Yq P q0E} {Λ : ℝ × Space → CVec3}
    (hΛ : IsRep a Λ) :
    eLpNorm Λ q0E (phaseμ P) = ENNReal.ofReal P ^ (1 / q0E.toReal) * ‖a‖ₑ := by
  have hprod : (volume : Measure (ℝ × Space)).restrict (Ioc (0 : ℝ) P ×ˢ (univ : Set Space)) =
      phaseμ P := by
    simpa only [Measure.volume_eq_prod] using
      (Measure.restrict_prod_eq_prod_univ (μ := (volume : Measure ℝ))
        (ν := (volume : Measure Space)) (Ioc 0 P)).symm
  have hq0 : q0E ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)
  have ht : 0 < q0E.toReal := ENNReal.toReal_pos hq0 q0E_ne_top
  rw [← hprod, eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 q0E_ne_top, cell_lintegral' q0E_ne_top hΛ,
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul]
  rw [mul_one_div_cancel ht.ne', ENNReal.rpow_one]

/-- The representative of `a ∈ Y_{q₀}` itself. -/
theorem eLpNorm_phaseμ_rep_self {P : ℝ} [Fact (0 < P)] (a : Yq P q0E) :
    eLpNorm (fun x : ℝ × Space => rep a x.1 x.2) q0E (phaseμ P) =
      ENNReal.ofReal P ^ (1 / q0E.toReal) * ‖a‖ₑ :=
  eLpNorm_phaseμ_rep ⟨stronglyMeasurable_rep a, ae_of_all _ (fun τ => rep_slice a τ)⟩

theorem ofReal_bgp_eq : ENNReal.ofReal bgp = q0E := by
  rw [q0E, UnforcedLeray.B0281.q0_eq]
  rfl

theorem q0E_toReal_eq_bgp : q0E.toReal = bgp := by
  rw [UnforcedLeray.B0412.q0E_toReal]
  rfl

/-- From a `phaseLpNorm` bound to a cell `L^{q₀}` bound. -/
theorem eLpNorm_le_of_phaseLpNorm {P : ℝ} (hP : 0 < P) {f : ℝ × Space → CVec3}
    (hf : AEStronglyMeasurable f volume) {B : ℝ} (h : phaseLpNorm P bgp f ≤ ENNReal.ofReal B) :
    eLpNorm f q0E (phaseμ P) ≤ ENNReal.ofReal P ^ (1 / q0E.toReal) * ENNReal.ofReal B := by
  rw [QuadLeaf.phaseLpNorm_eq_eLpNorm' P bgp QuadLeaf.bgp_pos' hf, ofReal_bgp_eq] at h
  have hc : ENNReal.ofReal P ^ (1 / bgp) * (ENNReal.ofReal P⁻¹) ^ (1 / bgp) = 1 := by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num [bgp]), ← ENNReal.ofReal_mul hP.le,
      mul_inv_cancel₀ hP.ne', ENNReal.ofReal_one, ENNReal.one_rpow]
  rw [q0E_toReal_eq_bgp]
  calc eLpNorm f q0E (phaseμ P)
      = (ENNReal.ofReal P ^ (1 / bgp) * (ENNReal.ofReal P⁻¹) ^ (1 / bgp)) *
          eLpNorm f q0E (phaseμ P) := by rw [hc, one_mul]
    _ = ENNReal.ofReal P ^ (1 / bgp) *
          ((ENNReal.ofReal P⁻¹) ^ (1 / bgp) * eLpNorm f q0E (phaseμ P)) := by ring
    _ ≤ ENNReal.ofReal P ^ (1 / bgp) * ENNReal.ofReal B := by gcongr

end UnforcedLeray.Short.IIb.QuadBoundSub
