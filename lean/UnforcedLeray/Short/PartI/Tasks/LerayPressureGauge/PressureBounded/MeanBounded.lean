import UnforcedLeray.Short.PartI.Sub.T02_2_3
import UnforcedLeray.Short.PartI.Tasks.LerayPressureGauge.PressureMeanIdentity

/-!
# Part I, task `PartI:T02/2/3`, leaf `PbMeanBounded` (mean part of `PressureBounded`)

Source of record: `the November 2 reference manuscript`, line 447 (`p̄ + \overline{v₂²}`
is constant in `η`) and line 277.

Statement: for `s ∈ [0,T]` the `q`-average `hmean c (p s)` of the pressure is bounded in `η`.

Proof.  `pressureMeanIdentity` gives `hmean c (p s) η = hmean c (p s) 0 + hmean c (v₂²) 0 -
hmean c (v₂²) η`.  Since `‖v s z‖ ≤ M₀` (`h.bounded 0`), `|v₂²| ≤ M₀²` pointwise, so every `q`-average
of `v₂²` is bounded by `M₀²` (`pbMB_abs_hmean_le`, the integral estimate of `gg_hmean_tendsto`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)

/-- A pointwise bound `|f| ≤ K` on the plane gives the same bound on every `q`-average `hmean c f η`. -/
theorem pbMB_abs_hmean_le {c : ℝ} (hc : 0 < c) {f : Plane → ℝ} {K : ℝ}
    (hf : ∀ z : Plane, |f z| ≤ K) (η : ℝ) :
    |hmean c f η| ≤ K := by
  rw [← Real.norm_eq_abs]
  unfold hmean
  rw [norm_smul, norm_inv, Real.norm_of_nonneg hc.le]
  have hint := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (-c / 2) (c / 2))
    (f := fun q => f (q, η)) (C := K) (by simp)
    (fun q _ => by rw [Real.norm_eq_abs]; exact hf (q, η))
  have hvol : (volume : Measure ℝ).real (Ioc (-c / 2) (c / 2)) = c := by
    rw [Measure.real, Real.volume_Ioc]
    rw [ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [hvol] at hint
  calc c⁻¹ * ‖∫ q in Ioc (-c / 2) (c / 2), f (q, η)‖ ≤ c⁻¹ * (K * c) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = K := by field_simp

/-- **`PbMeanBounded`** (source line 447, `p̄ + \overline{v₂²}` is constant in `η`): for every
`s ∈ [0,T]` the `q`-average of `p(s)` is bounded uniformly in `η`. -/
theorem pbMeanBounded : PbMeanBounded := by
  unfold PbMeanBounded
  intro ν c T v p h s hs
  have hc : 0 < c := zero_lt_one.trans_le h.one_le
  obtain ⟨M0, hM0⟩ := h.bounded 0
  have hbd : ∀ z : Plane, |v s z 1 ^ 2| ≤ M0 ^ 2 := by
    intro z
    have hz : ‖v s z‖ ≤ M0 := by
      have := hM0 s hs z
      rwa [norm_iteratedFDeriv_zero] at this
    have h1 : |v s z 1| ≤ M0 := by
      rw [← Real.norm_eq_abs]
      exact (PiLp.norm_apply_le (v s z) 1).trans hz
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  refine ⟨|hmean c (p s) 0| + 2 * M0 ^ 2, fun η => ?_⟩
  have hid := pressureMeanIdentity ν c T v p h s hs η
  have hsq := pbMB_abs_hmean_le (f := fun z => v s z 1 ^ 2) hc hbd η
  have hsq0 := pbMB_abs_hmean_le (f := fun z => v s z 1 ^ 2) hc hbd 0
  obtain ⟨hC1, hC2⟩ := abs_le.mp hsq
  obtain ⟨hB1, hB2⟩ := abs_le.mp hsq0
  have hA1 : -|hmean c (p s) 0| ≤ hmean c (p s) 0 := neg_abs_le _
  have hA2 : hmean c (p s) 0 ≤ |hmean c (p s) 0| := le_abs_self _
  rw [abs_le]
  constructor <;> linarith
