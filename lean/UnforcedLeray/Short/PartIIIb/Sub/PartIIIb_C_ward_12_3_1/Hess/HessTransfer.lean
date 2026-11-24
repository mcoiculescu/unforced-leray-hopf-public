import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.Hess.HessTest
import UnforcedLeray.Short.PartIIa.Tasks.F03cWindowBackEquation.Transfer

/-!
# Pull-back of a test: transfer of the Hessian pairing (source 1429-1431)

Task `PartIII-b:C/ward/12/3/1/2/2/2`.  Hessian analogue of
`UnforcedLeray.Short.PartIIa.WinBack.integral_windowField_sLap_t`: the change of variables back
from `(θ, x)` to `(t, y)` for `∫ u · sD2 i j (lapTest φ)`, with `sD2 i j` in place of `sLap`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.Short.PartIIa.Rep
open UnforcedLeray.Parabolic (PS IsSTTest sD2)
open UnforcedLeray.Short.PartIIa (WindowCutoff windowField windowLap winSet)

private theorem hsTr_sD2_lapTest_expDil {ψ : PS 3 → ℝ} (hψ : IsSTTest ψ) {τ₀ : ℝ}
    (hψw : tsupport ψ ⊆ Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space)) (i j : Fin 3)
    (t : ℝ) (y : Space) :
    sD2 i j (UnforcedLeray.B0424.lapTest τ₀ ψ : PS 3 → ℝ) (Real.exp t, Real.exp (t / 2) • y) =
      Real.exp (-t) * Real.exp (-(t / 2)) ^ 2 * sD2 i j ψ (τ₀ + t, y) := by
  simp only [sD2_lapTest hψ hψw i j, Real.exp_pos, ite_true, Real.log_exp, neg_div,
    UnforcedLeray.Short.PartIIa.WinBack.expNeg_smul_expPos]

private theorem hsTr_abs_lt_of_sD2_ne {ψ : PS 3 → ℝ} {τ₀ : ℝ} (i j : Fin 3)
    (hψw : tsupport ψ ⊆ Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space)) {t : ℝ} {y : Space}
    (h : sD2 i j ψ (τ₀ + t, y) ≠ 0) : |t| < 1 := by
  have hm := hψw (UnforcedLeray.Short.PartIIa.WinBack.sD2_tsupport_subset i j ψ
    (subset_tsupport _ (Function.mem_support.2 h)))
  have h1 : τ₀ + t ∈ Ioo (τ₀ - 1) (τ₀ + 1) := hm.1
  rw [abs_lt]
  constructor <;> linarith [h1.1, h1.2]

theorem integral_windowField_sD2_t (χ : ℝ → ℝ) (hχ : WindowCutoff χ) (τ₀ : ℝ) (W : ℝ × Space → CVec3) (c : Fin 3) {ψ : PS 3 → ℝ} (hψ : IsSTTest ψ) (hψw : tsupport ψ ⊆ Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space)) (i j : Fin 3) : ∫ X, windowField χ τ₀ W c X * ((sD2 i j (UnforcedLeray.B0424.lapTest τ₀ ψ) X : ℝ) : ℂ) = ∫ p : ℝ × Space, W (τ₀ + p.1, p.2) c * ((sD2 i j ψ (τ₀ + p.1, p.2) : ℝ) : ℂ) := by
  have hzero : ∀ X ∉ Ioi (0 : ℝ) ×ˢ (univ : Set Space),
      windowField χ τ₀ W c X * ((sD2 i j (UnforcedLeray.B0424.lapTest τ₀ ψ) X : ℝ) : ℂ) = 0 := by
    intro X hX
    have hX1 : ¬ (0 < X.1) := fun h => hX ⟨h, trivial⟩
    simp only [windowField, if_neg hX1, zero_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    UnforcedLeray.B0424.integral_expChart]
  refine (UnforcedLeray.B0424.integral_dilChart _).trans ?_
  congr 1
  funext p
  obtain ⟨t, y⟩ := p
  simp only [UnforcedLeray.B0424.dilChart, UnforcedLeray.B0424.expChart]
  rw [UnforcedLeray.Short.PartIIa.WinBack.windowField_expDil, hsTr_sD2_lapTest_expDil hψ hψw i j]
  by_cases h0 : sD2 i j ψ (τ₀ + t, y) = 0
  · simp [h0]
  · have ht : |t| < 1 := hsTr_abs_lt_of_sD2_ne i j hψw h0
    have hχ1 : χ t = 1 := hχ.one t ⟨(abs_lt.1 ht).1.le, (abs_lt.1 ht).2.le⟩
    have hc : ((Real.exp (3 * t / 2) * Real.exp t * Real.exp (-(t / 2)) * Real.exp (-t) *
        Real.exp (-(t / 2)) ^ 2 : ℝ) : ℂ) = 1 := by
      rw [UnforcedLeray.Short.PartIIa.WinBack.exp_scalar_identity t]; simp
    rw [hχ1]
    simp only [Complex.real_smul]
    push_cast at hc ⊢
    linear_combination (W (τ₀ + t, y) c * (sD2 i j ψ (τ₀ + t, y) : ℂ)) * hc

end UnforcedLeray.Short.PartIIIb.Concrete
