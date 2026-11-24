import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.Adjoint
import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.WeightLogBounds.Calc

/-!
# Part III-a weak smoothing: log-derivative bounds of the periodic weight (SP 3044-3050)

Proof of `PeriodicWeightLogBounds` (`Adjoint.lean`). The calculus is in
`WeightLogBounds/Calc.lean`: `p_d = Q_d^m` with `Q_d = 1 + y₂² + (d/π)² sin²(π y₁/d)`, the
partial derivatives of `log Q_d` are computed on coordinate lines, and the constant is
`C = (5 + π)|m|`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa

open WLB in
theorem periodicWeightLogBounds : PeriodicWeightLogBounds := by
  unfold PeriodicWeightLogBounds
  intro m
  refine ⟨(5 + Real.pi) * |m|, fun d hd => ?_⟩
  have hd0 : d ≠ 0 := hd.ne'
  have hlog : (fun x : ℝ × ℝ => Real.log (periodicWeight m d x))
      = fun x => m * Real.log (Qf d x) := funext (logW m d)
  have E0 : B0579.pd 0 (fun z : ℝ × ℝ => m * Real.log (Qf d z))
      = fun z => m * (Pf d z / Qf d z) := funext (F1 m d hd0)
  have E1 : B0579.pd 1 (fun z : ℝ × ℝ => m * Real.log (Qf d z))
      = fun z => m * (2 * z.2 / Qf d z) := funext (F2 m d)
  have hd4 : ∀ y : ℝ × ℝ, (fun d' : ℝ => Real.log (periodicWeight m d' y))
      = fun d' => m * Real.log (Qf d' y) := fun y => funext fun d' => logW m d' y
  have hpi5 : (3 : ℝ) ≤ 5 + Real.pi := by linarith [Real.pi_pos]
  rw [hlog]
  simp only [Fin.forall_fin_two]
  refine ⟨fun y => ⟨?_, ?_⟩, fun y => ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, fun y hy => ?_, fun y hy => ?_⟩
  · -- first derivatives in y₁
    rw [F1 m d hd0 y]
    exact abs_mul_le_of (K := 1)
      (abs_div_le_of (K := 1) (Qf_pos d y) (by rw [one_mul]; exact abs_Pf_le d y))
      (by linarith [Real.pi_pos])
  · -- first derivatives in y₂
    rw [F2 m d y]
    exact abs_mul_le_of (K := 1)
      (abs_div_le_of (K := 1) (Qf_pos d y)
        (by rw [one_mul]; exact abs_two_mul_le _ _ (one_add_sq_le_Qf d y)))
      (by linarith [Real.pi_pos])
  · -- second derivative (0,0)
    rw [E0, S00 m d hd0 y]
    exact abs_mul_le_of (K := 3)
      (abs_div_le_of (K := 3) (pow_pos (Qf_pos d y) 2)
        (bound_S00 (one_le_Qf d y) (cs_eq d y) (sq_Pf_le d y)))
      hpi5
  · -- second derivative (0,1)
    rw [E1, S10 m d hd0 y]
    exact abs_mul_le_of (K := 1)
      (abs_div_le_of (K := 1) (pow_pos (Qf_pos d y) 2)
        (bound_mixed (abs_Pf_le d y) (abs_two_mul_le _ _ (one_add_sq_le_Qf d y))))
      (by linarith [Real.pi_pos])
  · -- second derivative (1,0)
    rw [E0, S01 m d hd0 y]
    exact abs_mul_le_of (K := 1)
      (abs_div_le_of (K := 1) (pow_pos (Qf_pos d y) 2)
        (bound_mixed (abs_Pf_le d y) (abs_two_mul_le _ _ (one_add_sq_le_Qf d y))))
      (by linarith [Real.pi_pos])
  · -- second derivative (1,1)
    rw [E1, S11 m d hd0 y]
    exact abs_mul_le_of (K := 3)
      (abs_div_le_of (K := 3) (pow_pos (Qf_pos d y) 2)
        (bound_S11 (abs_two_mul_le _ _ (one_add_sq_le_Qf d y)) (one_le_Qf d y)))
      hpi5
  · -- the cell bound y·∇ log p_d
    rw [F1 m d hd0 y, F2 m d y]
    have e : y.1 * (m * (Pf d y / Qf d y)) + y.2 * (m * (2 * y.2 / Qf d y))
        = m * (y.1 * Pf d y / Qf d y + 2 * y.2 ^ 2 / Qf d y) := by ring
    rw [e]
    have hcell := abs_le_of_mem_cell hy
    have hA : |y.1 * Pf d y / Qf d y| ≤ Real.pi :=
      abs_div_le_of (K := Real.pi) (Qf_pos d y) (abs_y1_Pf_le d hd y hcell)
    have hB : |2 * y.2 ^ 2 / Qf d y| ≤ 2 :=
      abs_div_le_of (K := 2) (Qf_pos d y) (by
        rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * y.2 ^ 2)]
        linarith [one_add_sq_le_Qf d y])
    have hsum : |y.1 * Pf d y / Qf d y + 2 * y.2 ^ 2 / Qf d y| ≤ Real.pi + 2 := by
      rw [abs_le] at hA hB ⊢
      constructor <;> linarith [hA.1, hA.2, hB.1, hB.2]
    exact abs_mul_le_of (K := Real.pi + 2) hsum (by linarith)
  · -- the d-derivative bound d ∂_d log p_d
    rw [hd4 y]
    have hder : HasDerivAt (fun e : ℝ => m * Real.log (Qf e y)) (m * (DQ d y / Qf d y)) d :=
      ((Qf_d d hd0 y).log (Qf_pos d y).ne').const_mul m
    rw [hder.deriv]
    have hk := d_DQ d hd y
    have e : d * (m * (DQ d y / Qf d y))
        = m * ((2 * (d / Real.pi) ^ 2 * Real.sin (Real.pi * y.1 / d) ^ 2 - y.1 * Pf d y)
            / Qf d y) := by
      rw [← hk]; ring
    rw [e]
    have hcell := abs_le_of_mem_cell hy
    have h1 : |2 * (d / Real.pi) ^ 2 * Real.sin (Real.pi * y.1 / d) ^ 2| ≤ 2 * Qf d y := by
      rw [abs_of_nonneg (by positivity :
        (0:ℝ) ≤ 2 * (d / Real.pi) ^ 2 * Real.sin (Real.pi * y.1 / d) ^ 2)]
      nlinarith [tsq_le_Qf d y]
    have h2 := abs_y1_Pf_le d hd y hcell
    have h3 : |2 * (d / Real.pi) ^ 2 * Real.sin (Real.pi * y.1 / d) ^ 2 - y.1 * Pf d y|
        ≤ (2 + Real.pi) * Qf d y := by
      rw [abs_le] at h1 h2 ⊢
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    exact abs_mul_le_of (K := 2 + Real.pi) (abs_div_le_of (K := 2 + Real.pi) (Qf_pos d y) h3)
      (by linarith)

end UnforcedLeray.Short.IIIa
