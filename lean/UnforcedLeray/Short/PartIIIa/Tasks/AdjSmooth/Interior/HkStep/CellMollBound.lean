import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Shared
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.CellConvBound

/-!
# `PartIII-a:T21/2/7/2/1/1/5/9`: mollification is bounded on the periodic `X_{-m,c}`, uniformly in `n`

Source of record: `the November 2 reference manuscript` (SP), lines 3044-3047.

Proof: `cellMoll n f = cellConv (molKer n) f` (definitionally). The mollifier `molKer n` is
continuous, nonnegative, vanishes outside the closed ball of radius `1/(n+1) ≤ 1`, and has
integral one. So `CellConvBound` applies with `K = molKer n` and the constant `C * ∫|K| = C`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The mollifier `molKer n` is continuous. -/
theorem cmb_molKer_continuous (n : ℕ) : Continuous (molKer n) :=
  (molBump n).continuous_normed (μ := volume)

/-- The mollifier `molKer n` vanishes outside the unit sup-norm ball. -/
theorem cmb_molKer_eq_zero (n : ℕ) (y : ℝ × ℝ) (hy : 1 < ‖y‖) : molKer n y = 0 := by
  by_contra hne
  have hmem : y ∈ Function.support (molKer n) := hne
  have hsupp : Function.support (molKer n) = Metric.ball (0 : ℝ × ℝ) (molBump n).rOut :=
    (molBump n).support_normed_eq (μ := volume)
  rw [hsupp, mem_ball_zero_iff] at hmem
  have hr : (molBump n).rOut ≤ 1 := by
    show 1 / ((n : ℝ) + 1) ≤ 1
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [div_le_one (by positivity)]
    linarith
  linarith

/-- The mollifier `molKer n` has absolute integral one. -/
theorem cmb_molKer_integral_abs (n : ℕ) : ∫ y, |molKer n y| = 1 := by
  have h : ∀ y, |molKer n y| = molKer n y := fun y =>
    abs_of_nonneg ((molBump n).nonneg_normed (μ := volume) y)
  simp only [h]
  exact (molBump n).integral_normed (μ := volume)

/-- **Mollification is bounded on the periodic `X_{-m,c}`, uniformly in `n`** (SP 3044-3047). -/
theorem cellMollBound : UnforcedLeray.Short.IIIa.CellMollBound := by
  intro c m hc
  obtain ⟨C, hC0, hC⟩ := cellConvBound c m hc
  refine ⟨C, hC0, fun n f hper hf => ?_⟩
  obtain ⟨_, hbd⟩ := hC (molKer n) f (cmb_molKer_continuous n)
    (fun y hy => cmb_molKer_eq_zero n y hy) hper hf
  have hcm : ENNReal.ofReal (C * ∫ y, |molKer n y|) = ENNReal.ofReal C := by
    rw [cmb_molKer_integral_abs, mul_one]
  rw [hcm] at hbd
  exact hbd

end UnforcedLeray.Short.IIIa
