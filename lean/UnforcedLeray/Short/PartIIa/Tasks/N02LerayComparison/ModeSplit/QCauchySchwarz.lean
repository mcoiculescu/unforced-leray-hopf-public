import UnforcedLeray.Short.PartIIa.Sub.N02_5

/-!
# Part II-a, task `PartII-a:N02/5/2`: Jensen (Cauchy-Schwarz) for the `q`-average

Target: `AvgQCauchySchwarz` (`Short/PartII-a/Sub/N02_5.lean`), source of record
`the November 2 reference manuscript`, lines 1738-1750.

Proof. For a continuous `v : ℝ → ℂ²` and `c > 0`, `‖∫_0^c v‖ ≤ ∫_0^c ‖v‖` (triangle inequality for
integrals), so it suffices to show `(∫_0^c f)² ≤ c ∫_0^c f²` for the continuous real `f = ‖v‖`.
For `f`, with mean `m = I / c` (`I = ∫_0^c f`), `0 ≤ ∫_0^c (f - m)²` and this integral expands to
`∫ f² - 2 m I + c m² = ∫ f² - I² / c`; multiplying by `c` gives the claim.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-- Expansion of `∫_0^c (f - m)²` about a constant `m`, for continuous real `f`. -/
theorem qcsExpand (c m : ℝ) (f : ℝ → ℝ) (hf : Continuous f) :
    ∫ q in (0 : ℝ)..c, (f q - m) ^ 2
      = (∫ q in (0 : ℝ)..c, f q ^ 2) - 2 * m * (∫ q in (0 : ℝ)..c, f q) + c * m ^ 2 := by
  have hI : IntervalIntegrable f MeasureTheory.volume 0 c := hf.intervalIntegrable 0 c
  have hI2 : IntervalIntegrable (fun q => f q ^ 2) MeasureTheory.volume 0 c :=
    (hf.pow 2).intervalIntegrable 0 c
  have hlin : IntervalIntegrable (fun q => 2 * m * f q) MeasureTheory.volume 0 c :=
    hI.const_mul (2 * m)
  have hconst : IntervalIntegrable (fun _ : ℝ => m ^ 2) MeasureTheory.volume 0 c :=
    intervalIntegrable_const
  have hfun : (fun q => (f q - m) ^ 2) = fun q => (f q ^ 2 - 2 * m * f q) + m ^ 2 := by
    funext q
    ring
  rw [hfun, intervalIntegral.integral_add (hI2.sub hlin) hconst,
    intervalIntegral.integral_sub hI2 hlin, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- Algebra step: from `0 ≤ S₂ - 2 m I + c m²` with `m c = I` and `c > 0`, get `I² ≤ c S₂`. -/
theorem qcsAlg (c I S2 m : ℝ) (hc : 0 < c) (hmc : m * c = I)
    (h : 0 ≤ S2 - 2 * m * I + c * m ^ 2) : I ^ 2 ≤ c * S2 := by
  subst hmc
  nlinarith [mul_nonneg hc.le h]

/-- Jensen for a continuous real function on `[0, c]`: `(∫_0^c f)² ≤ c ∫_0^c f²`. -/
theorem qcsSqLe (c : ℝ) (hc : 0 < c) (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ q in (0 : ℝ)..c, f q) ^ 2 ≤ c * ∫ q in (0 : ℝ)..c, f q ^ 2 := by
  have hnonneg : 0 ≤ ∫ q in (0 : ℝ)..c, (f q - (∫ r in (0 : ℝ)..c, f r) / c) ^ 2 :=
    intervalIntegral.integral_nonneg hc.le (fun q _ => sq_nonneg _)
  rw [qcsExpand c ((∫ r in (0 : ℝ)..c, f r) / c) f hf] at hnonneg
  have hmc : (∫ r in (0 : ℝ)..c, f r) / c * c = ∫ r in (0 : ℝ)..c, f r :=
    div_mul_cancel₀ _ hc.ne'
  exact qcsAlg c _ _ _ hc hmc hnonneg

/-- **Target `avgQCauchySchwarz_proof`**: `‖∫_0^c v‖² ≤ c ∫_0^c ‖v‖²` for continuous `v`. -/
theorem avgQCauchySchwarz_proof : AvgQCauchySchwarz := by
  intro c hc v hv
  have h1 : ‖∫ q in (0 : ℝ)..c, v q‖ ≤ ∫ q in (0 : ℝ)..c, ‖v q‖ :=
    intervalIntegral.norm_integral_le_integral_norm hc.le
  have h2 : ‖∫ q in (0 : ℝ)..c, v q‖ ^ 2 ≤ (∫ q in (0 : ℝ)..c, ‖v q‖) ^ 2 := by
    gcongr
  exact le_trans h2 (qcsSqLe c hc (fun q => ‖v q‖) hv.norm)

end UnforcedLeray.Short.PartIIa
