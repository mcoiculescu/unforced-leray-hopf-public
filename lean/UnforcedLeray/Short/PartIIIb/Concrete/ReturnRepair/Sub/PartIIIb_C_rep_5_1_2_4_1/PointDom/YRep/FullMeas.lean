import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.YRep.KerMeas

/-!
# Measurability of `fullKer` in the source variable (source 4171, 4180-4186)
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped Classical

namespace UnforcedLeray.Short.PartIIIb.Concrete

lemma yr_xKer_zero (ν μ h : ℝ) (x : Space) : xKer ν μ h x 0 = 0 := by
  ext i
  simp [xKer, gradKCon]

lemma yr_sKer_zero (ν μ h r y3 : ℝ) (z : Space) : sKer ν μ h r y3 z 0 = 0 := by
  simp [sKer, yr_xKer_zero]

lemma yr_fullKer_zero (ν μ R : ℝ) (χy : ℝ → ℝ) (h : ℝ) (y z : Space) :
    fullKer ν μ R χy h y z 0 = 0 := by
  simp [fullKer, yr_xKer_zero, yr_sKer_zero]

lemma yr_fullKer_meas (ν μ R c : ℝ) (χy : ℝ → ℝ) (g : Chart → Ten3) (hg : Measurable g) (τ : ℝ)
    (y : Space) (hy : ∀ σ z, oldPhys R c g σ z ≠ 0 → ϱ z < ϱ y) :
    Measurable fun e : ℝ × Space =>
      if e.1 < τ then fullKer ν μ R χy (τ - e.1) y e.2 (oldPhys R c g e.1 e.2) else 0 := by
  have hS : MeasurableSet {e : ℝ × Space | e.1 < τ} := measurableSet_lt measurable_fst measurable_const
  have hxK := yr_xKer_meas ν μ {e : ℝ × Space | e.1 < τ} hS (fun e => τ - e.1)
    (measurable_const.sub measurable_fst) (fun e => y - pdLam (τ - e.1) • e.2)
    (by
      have hlam : Measurable fun e : ℝ × Space => pdLam (τ - e.1) := by unfold pdLam; fun_prop
      exact measurable_const.sub (hlam.smul measurable_snd))
    (fun e => oldPhys R c g e.1 e.2) (fun i j => yr_meas_oldPhys_entry R c g hg i j)
    (fun e he hW => yr_zero_of_eq (sub_pos.2 he) (sub_eq_zero.mp hW) _ (hy _ _))
  have hsK := yr_sKer_meas ν μ R c g hg τ (ϱ y) (y 2) hy
  have : (fun e : ℝ × Space =>
      if e.1 < τ then fullKer ν μ R χy (τ - e.1) y e.2 (oldPhys R c g e.1 e.2) else 0) =
      fun e => χy (ν * age R y) • (if e ∈ {e : ℝ × Space | e.1 < τ} then
          xKer ν μ (τ - e.1) (y - pdLam (τ - e.1) • e.2) (oldPhys R c g e.1 e.2) else 0) +
        (deriv χy (ν * age R y) * (-2 * ν * R ^ 2 / ϱ y ^ 3) / ϱ y *
          (if e.1 < τ then sKer ν μ (τ - e.1) (ϱ y) (y 2) e.2 (oldPhys R c g e.1 e.2) else 0)) •
          coordinateVector 2 := by
    funext e
    by_cases h : e.1 < τ
    · simp [fullKer, h]
    · simp [h]
  rw [this]
  exact (hxK.const_smul (χy (ν * age R y))).add ((measurable_const.mul hsK).smul_const (coordinateVector 2 : Space))

end UnforcedLeray.Short.PartIIIb.Concrete

end
