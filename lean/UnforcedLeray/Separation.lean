import UnforcedLeray.Statement
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Integrating the quantitative separation

The integrated lower bound in Theorem A follows from its pointwise lower
bound and integrability of the squared difference. The power integral is
computed here from Mathlib's real-power integration theorem; it is not an
additional premise. These implications do not establish the existence of
the pair of solutions in `MainClaim`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace UnforcedLeray

/-- Squared power-law lower density for the L² distance. -/
def separationDensity (c σ t : ℝ) : ℝ := c ^ 2 * Real.rpow t (2 * σ + 1 / 2)

/-- The exact integral of the squared lower density from zero to T. -/
def separationLowerBound (c σ T : ℝ) : ℝ :=
  c ^ 2 * Real.rpow T (2 * σ + 3 / 2) / (2 * σ + 3 / 2)

theorem separationDensity_eq_sq {c σ t : ℝ} (ht : 0 ≤ t) :
    separationDensity c σ t = (c * Real.rpow t (σ + 1 / 4)) ^ 2 := by
  unfold separationDensity
  simp only [Real.rpow_eq_pow]
  rw [mul_pow, ← Real.rpow_mul_natCast ht (σ + 1 / 4) 2]
  congr 2
  ring

/-- The integrability threshold is checked, rather than assumed for the model power. -/
theorem separationDensity_integrable {T σ : ℝ} (hT : 0 < T) (hσ : 0 < σ) (c : ℝ) :
    IntegrableOn (separationDensity c σ) (Ioo (0 : ℝ) T) := by
  have hp : -1 < 2 * σ + 1 / 2 := by linarith
  exact ((intervalIntegral.integrableOn_Ioo_rpow_iff hT).mpr hp).const_mul (c ^ 2)

/-- Exact Lebesgue integral over the open time interval. -/
theorem integral_separationDensity {T σ : ℝ} (hT : 0 < T) (hσ : 0 < σ) (c : ℝ) :
    (∫ t in Ioo (0 : ℝ) T, separationDensity c σ t) = separationLowerBound c σ T := by
  have hp : -1 < 2 * σ + 1 / 2 := by linarith
  have hexp : (2 * σ + 1 / 2) + 1 = 2 * σ + 3 / 2 := by ring
  have hne : 2 * σ + 3 / 2 ≠ 0 := by linarith
  unfold separationDensity separationLowerBound
  simp only [Real.rpow_eq_pow]
  rw [integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hT.le,
    integral_rpow (Or.inl hp), hexp,
    Real.zero_rpow hne, sub_zero]
  ring

theorem separationLowerBound_pos {T c σ : ℝ} (hT : 0 < T) (hc : 0 < c) (hσ : 0 < σ) :
    0 < separationLowerBound c σ T := by
  unfold separationLowerBound
  exact div_pos (mul_pos (sq_pos_of_pos hc) (Real.rpow_pos_of_pos hT _)) (by linarith)

/-- Generic real-valued distance version. The pointwise hypothesis forces
`f` to be positive on (0,T), so no separate nonnegativity premise is needed. -/
theorem integrated_quantitative_separation {T c σ : ℝ} {f : ℝ → ℝ}
    (hT : 0 < T) (hc : 0 < c) (hσ : 0 < σ)
    (hf : IntegrableOn (fun t => f t ^ 2) (Ioo (0 : ℝ) T))
    (hsep : ∀ t ∈ Ioo (0 : ℝ) T, c * Real.rpow t (σ + 1 / 4) ≤ f t) :
    separationLowerBound c σ T ≤ (∫ t in Ioo (0 : ℝ) T, f t ^ 2) ∧
      0 < separationLowerBound c σ T := by
  have hbound : ∀ t ∈ Ioo (0 : ℝ) T, separationDensity c σ t ≤ f t ^ 2 := by
    intro t ht
    rw [separationDensity_eq_sq ht.1.le]
    have hl : 0 < c * Real.rpow t (σ + 1 / 4) :=
      mul_pos hc (Real.rpow_pos_of_pos ht.1 _)
    have hs := hsep t ht
    nlinarith
  have hi := setIntegral_mono_on (separationDensity_integrable hT hσ c)
    hf measurableSet_Ioo hbound
  rw [integral_separationDensity hT hσ c] at hi
  exact ⟨hi, separationLowerBound_pos hT hc hσ⟩

/-- The manuscript's concrete L² separation implies exactly its integrated
positive lower bound. No Navier–Stokes existence or regularity is assumed beyond
the explicitly stated integrability needed for this consequence. -/
theorem integrated_l2_separation {T c σ : ℝ} {u₁ u₂ : Velocity}
    (hT : 0 < T) (hc : 0 < c) (hσ : 0 < σ)
    (hf : IntegrableOn (fun t => l2Norm (u₂ t - u₁ t) ^ 2) (Ioo (0 : ℝ) T))
    (hsep : ∀ t ∈ Ioc (0 : ℝ) T,
      c * Real.rpow t (σ + 1 / 4) ≤ l2Norm (u₂ t - u₁ t)) :
    c ^ 2 * Real.rpow T (2 * σ + 3 / 2) / (2 * σ + 3 / 2) ≤
        (∫ t in Ioo (0 : ℝ) T, l2Norm (u₂ t - u₁ t) ^ 2) ∧
      0 < c ^ 2 * Real.rpow T (2 * σ + 3 / 2) / (2 * σ + 3 / 2) := by
  exact integrated_quantitative_separation hT hc hσ hf
    (fun t ht => hsep t ⟨ht.1, ht.2.le⟩)

theorem integrated_l2_separation_pos {T c σ : ℝ} {u₁ u₂ : Velocity}
    (hT : 0 < T) (hc : 0 < c) (hσ : 0 < σ)
    (hf : IntegrableOn (fun t => l2Norm (u₂ t - u₁ t) ^ 2) (Ioo (0 : ℝ) T))
    (hsep : ∀ t ∈ Ioc (0 : ℝ) T,
      c * Real.rpow t (σ + 1 / 4) ≤ l2Norm (u₂ t - u₁ t)) :
    0 < ∫ t in Ioo (0 : ℝ) T, l2Norm (u₂ t - u₁ t) ^ 2 := by
  obtain ⟨hbound, hpos⟩ := integrated_l2_separation hT hc hσ hf hsep
  exact hpos.trans_le hbound

end UnforcedLeray
