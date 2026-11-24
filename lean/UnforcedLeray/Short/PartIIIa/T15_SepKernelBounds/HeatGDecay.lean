import UnforcedLeray.Short.PartIIIa.Sub.T15
import UnforcedLeray.Short.PartIIIa.T14_HeatGBound
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds.GaussSup

/-!
# Part III-a, task `PartIII-a:T15/2`: decay of the heat kernel and its derivatives (SP 3604-3610)

Proves `heatGDecay : HeatGDecay` (`Sub/T15.lean`). For each `m : ℕ` put
`C = C0 * max S1 S2`, where `C0` comes from `heatGBound m` (T14) and `S1`, `S2` are the
Gaussian suprema of `gaussSup` at `s = (3+m)/2` and `s = (5+m)/2`.

1. `‖D^m G_t x‖ ≤ C0 t^{-(3+m)/2} e^{-‖x‖²/(8t)}`, and `gaussSup` with `s = (3+m)/2`
   bounds `t^{-(3+m)/2} e^{-‖x‖²/(8t)} ≤ S1 ‖x‖^{-(3+m)}`.
2. `t^{-(3+m)/2} = t · t^{-(5+m)/2}`, and `gaussSup` with `s = (5+m)/2` gives
   `t^{-(5+m)/2} e^{-‖x‖²/(8t)} ≤ S2 ‖x‖^{-(5+m)}`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

/-- **Decay of the heat kernel and its derivatives** (`PartIII-a:T15/2`; SP 3604-3610): for each
`m` there is `C ≥ 0` with, for `t > 0` and `x ≠ 0`, `‖D^m G_t(x)‖ ≤ C ‖x‖^{-3-m}` and
`‖D^m G_t(x)‖ ≤ C t ‖x‖^{-5-m}`. -/
theorem heatGDecay : UnforcedLeray.Short.IIIa.HeatGDecay := by
  unfold UnforcedLeray.Short.IIIa.HeatGDecay
  intro m
  obtain ⟨C0, hC0, hC0b⟩ := heatGBound m
  obtain ⟨S1, hS1, hS1b⟩ := gaussSup ((3 + (m : ℝ)) / 2) (by positivity)
  obtain ⟨S2, _hS2, hS2b⟩ := gaussSup ((5 + (m : ℝ)) / 2) (by positivity)
  refine ⟨C0 * max S1 S2, mul_nonneg hC0 (hS1.trans (le_max_left S1 S2)), ?_⟩
  intro t ht x hx
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hG := hC0b t ht x
  constructor
  · have e1 : (-(3 + (m : ℝ)) / 2) = -((3 + (m : ℝ)) / 2) := by ring
    have e2 : (-2 * ((3 + (m : ℝ)) / 2)) = -3 - (m : ℝ) := by ring
    have h1 := hS1b t ‖x‖ ht hr
    calc ‖iteratedFDeriv ℝ m (heatG t) x‖
        ≤ C0 * t ^ (-(3 + (m : ℝ)) / 2) * Real.exp (-‖x‖ ^ 2 / (8 * t)) := hG
      _ = C0 * (t ^ (-((3 + (m : ℝ)) / 2)) * Real.exp (-‖x‖ ^ 2 / (8 * t))) := by
          rw [e1]; ring
      _ ≤ C0 * (S1 * ‖x‖ ^ (-2 * ((3 + (m : ℝ)) / 2))) :=
          mul_le_mul_of_nonneg_left h1 hC0
      _ = (C0 * S1) * ‖x‖ ^ (-3 - (m : ℝ)) := by
          rw [e2]; ring
      _ ≤ (C0 * max S1 S2) * ‖x‖ ^ (-3 - (m : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_left S1 S2) hC0)
            (Real.rpow_nonneg hr.le _)
  · have e3 : t ^ (-(3 + (m : ℝ)) / 2) = t * t ^ (-((5 + (m : ℝ)) / 2)) := by
      have e4 : (-(3 + (m : ℝ)) / 2) = 1 + (-((5 + (m : ℝ)) / 2)) := by ring
      rw [e4, Real.rpow_add ht, Real.rpow_one]
    have e5 : (-2 * ((5 + (m : ℝ)) / 2)) = -5 - (m : ℝ) := by ring
    have h2 := hS2b t ‖x‖ ht hr
    calc ‖iteratedFDeriv ℝ m (heatG t) x‖
        ≤ C0 * t ^ (-(3 + (m : ℝ)) / 2) * Real.exp (-‖x‖ ^ 2 / (8 * t)) := hG
      _ = C0 * t * (t ^ (-((5 + (m : ℝ)) / 2)) * Real.exp (-‖x‖ ^ 2 / (8 * t))) := by
          rw [e3]; ring
      _ ≤ C0 * t * (S2 * ‖x‖ ^ (-2 * ((5 + (m : ℝ)) / 2))) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hC0 ht.le)
      _ = (C0 * S2) * t * ‖x‖ ^ (-5 - (m : ℝ)) := by
          rw [e5]; ring
      _ ≤ (C0 * max S1 S2) * t * ‖x‖ ^ (-5 - (m : ℝ)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (le_max_right S1 S2) hC0) ht.le)
            (Real.rpow_nonneg hr.le _)

end UnforcedLeray.Short.IIIa
