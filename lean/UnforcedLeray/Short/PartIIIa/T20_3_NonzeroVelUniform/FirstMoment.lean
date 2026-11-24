import UnforcedLeray.Short.PartIIIa.Sub.T20_3
import UnforcedLeray.Short.PartIIIa.T20_3_NonzeroVelUniform.WeightedHolder

/-!
# Part III-a, task `PartIII-a:T20/3/2`: the first-moment bound (`FirstMomentBound`)

Source of record: `the November 2 reference manuscript`, lines 3239-3240
("the moment bound is weighted Cauchy-Schwarz", first moment bounded by `‖ω‖_{X_m}`).
Target: `FirstMomentBound` in `Sub/T20_3.lean`.

Proof. Let `h x = (|x.1| + |x.2|)^2 * jb x ^ (-m)`.
* `h` is integrable on `ℝ²` for `m > 2`. Indeed `(|a| + |b|)^2 ≤ 2 jb x`, so
  `h x ≤ 2 jb x ^ (1 - m)`, and `jb x ^ (1 - m) ≤ (1 + ‖x‖^2) ^ (1 - m)` because
  `1 + ‖x‖^2 ≤ jb x` and `1 - m < 0`. Mathlib's `integrable_rpow_neg_one_add_norm_sq` with
  `r = 2 (m - 1)` (its hypothesis `finrank ℝ (ℝ × ℝ) < r` is `2 < 2 (m - 1)`, i.e. `m > 2`)
  gives integrability of `(1 + ‖x‖^2)^(-(m-1))`.
* `K := (∫ h)^(1/2)` is nonnegative. For `c > 0` and `ω ∈ X_{m,c}`, the weighted Cauchy-Schwarz
  `WeightedHolder` with `g = |x.1| + |x.2|` gives integrability of `g |ω|` on the cell and
  `∫_cell g |ω| ≤ (∫_cell h)^(1/2) ‖ω‖`. Finally `∫_cell h ≤ ∫ h` (the cell measure is at most
  Lebesgue measure and `h ≥ 0`), and `rpow` is monotone.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology FourierTransform
open scoped ENNReal InnerProductSpace Real

namespace UnforcedLeray.Short.IIIa.CTE.T20_3

namespace FirstMomentProof

/-- `‖x‖² ≤ x₁² + x₂²` for the sup norm on `ℝ × ℝ`. -/
lemma norm_sq_le_sum (x : B0579.Plane) : ‖x‖ ^ 2 ≤ x.1 ^ 2 + x.2 ^ 2 := by
  rw [Prod.norm_def]
  rcases max_choice ‖x.1‖ ‖x.2‖ with h | h <;> rw [h, Real.norm_eq_abs, sq_abs] <;>
    nlinarith [sq_nonneg x.1, sq_nonneg x.2]

/-- `1 + ‖x‖² ≤ jb x`. -/
lemma one_add_norm_sq_le_jb (x : B0579.Plane) : 1 + ‖x‖ ^ 2 ≤ B0579.jb x := by
  unfold B0579.jb
  linarith [norm_sq_le_sum x]

/-- The weighted first-moment integrand `(|x₁| + |x₂|)² jb^{-m}` is integrable on `ℝ²` for
`m > 2`. -/
lemma integrable_sq_weight (m : ℝ) (hm : 2 < m) :
    Integrable (fun x : B0579.Plane => (|x.1| + |x.2|) ^ 2 * B0579.jb x ^ (-m)) volume := by
  have hd : ((Module.finrank ℝ (ℝ × ℝ) : ℕ) : ℝ) = 2 := by simp
  have hr : ((Module.finrank ℝ (ℝ × ℝ) : ℕ) : ℝ) < 2 * (m - 1) := by
    rw [hd]
    linarith
  have hI := integrable_rpow_neg_one_add_norm_sq (E := ℝ × ℝ) (μ := volume) hr
  refine (hI.const_mul 2).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · have hc1 : Continuous fun x : B0579.Plane => (|x.1| + |x.2|) ^ 2 := by
      fun_prop
    exact (hc1.mul (B0579.continuous_jb_rpow (-m))).aestronglyMeasurable
  · show ‖(|x.1| + |x.2|) ^ 2 * B0579.jb x ^ (-m)‖ ≤
      2 * (1 + ‖x‖ ^ 2) ^ (-(2 * (m - 1)) / 2)
    have hjpow : 0 < B0579.jb x ^ (-m) := Real.rpow_pos_of_pos (B0579.jb_pos x) _
    have hnn : 0 ≤ (|x.1| + |x.2|) ^ 2 * B0579.jb x ^ (-m) :=
      mul_nonneg (sq_nonneg _) hjpow.le
    rw [Real.norm_of_nonneg hnn]
    have hA : (|x.1| + |x.2|) ^ 2 ≤ 2 * B0579.jb x := by
      unfold B0579.jb
      nlinarith [sq_abs x.1, sq_abs x.2, sq_nonneg (|x.1| - |x.2|)]
    have e1 : B0579.jb x * B0579.jb x ^ (-m) = B0579.jb x ^ (1 - m) := by
      rw [show (1 - m) = 1 + (-m) by ring, Real.rpow_add (B0579.jb_pos x), Real.rpow_one]
    have e2 : B0579.jb x ^ (1 - m) ≤ (1 + ‖x‖ ^ 2) ^ (1 - m) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (one_add_norm_sq_le_jb x) (by linarith)
    have e4 : (1 + ‖x‖ ^ 2) ^ (-(2 * (m - 1)) / 2) = (1 + ‖x‖ ^ 2) ^ (1 - m) := by
      rw [show (-(2 * (m - 1)) / 2 : ℝ) = 1 - m by ring]
    rw [e4]
    calc (|x.1| + |x.2|) ^ 2 * B0579.jb x ^ (-m)
        ≤ (2 * B0579.jb x) * B0579.jb x ^ (-m) := mul_le_mul_of_nonneg_right hA hjpow.le
      _ = 2 * (B0579.jb x * B0579.jb x ^ (-m)) := by ring
      _ = 2 * B0579.jb x ^ (1 - m) := by rw [e1]
      _ ≤ 2 * (1 + ‖x‖ ^ 2) ^ (1 - m) := by linarith [e2]

end FirstMomentProof

/-- **First-moment bound** (task `PartIII-a:T20/3/2`; SP 3239-3240; uses `m > 2`). Proves the
`Prop` `FirstMomentBound` of `Sub/T20_3.lean`: `K = (∫_{ℝ²} (|q|+|η|)² jb^{-m})^{1/2}` works,
using `WeightedHolder` with `g = |q| + |η|` on each cell and `cellVol ≤ volume`. -/
theorem firstMomentBound : FirstMomentBound := by
  intro m hm
  have hI : Integrable (fun x : B0579.Plane => (|x.1| + |x.2|) ^ 2 * B0579.jb x ^ (-m)) volume :=
    FirstMomentProof.integrable_sq_weight m hm
  have hnn : ∀ x : B0579.Plane, 0 ≤ (|x.1| + |x.2|) ^ 2 * B0579.jb x ^ (-m) := fun x =>
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (B0579.jb_pos x).le _)
  refine ⟨(∫ x, (|x.1| + |x.2|) ^ 2 * B0579.jb x ^ (-m)) ^ (1 / 2 : ℝ),
    Real.rpow_nonneg (integral_nonneg hnn) _, ?_⟩
  intro c _hc ω
  have hgm : Measurable (fun x : B0579.Plane => |x.1| + |x.2|) :=
    Continuous.measurable (by fun_prop)
  have hgnn : ∀ x : B0579.Plane, 0 ≤ |x.1| + |x.2| := fun x => by positivity
  have hcell : Integrable (fun x : B0579.Plane => (|x.1| + |x.2|) ^ 2 * B0579.jb x ^ (-m))
      (B0581.cellVol c) :=
    hI.mono_measure Measure.restrict_le_self
  obtain ⟨hint, hbound⟩ :=
    weightedHolder c m ω (fun x => |x.1| + |x.2|) (by linarith) hgnn hgm hcell
  refine ⟨hint, ?_⟩
  have hcell_le : ∫ x, (|x.1| + |x.2|) ^ 2 * B0579.jb x ^ (-m) ∂(B0581.cellVol c) ≤
      ∫ x, (|x.1| + |x.2|) ^ 2 * B0579.jb x ^ (-m) :=
    integral_mono_measure Measure.restrict_le_self (Filter.Eventually.of_forall hnn) hI
  have hpow := Real.rpow_le_rpow (integral_nonneg hnn) hcell_le (by norm_num : (0 : ℝ) ≤ 1 / 2)
  unfold firstMoment
  calc ∫ x, (|x.1| + |x.2|) * |(ω : B0579.Plane → ℝ) x| ∂(B0581.cellVol c)
      ≤ (∫ x, (|x.1| + |x.2|) ^ 2 * B0579.jb x ^ (-m) ∂(B0581.cellVol c)) ^ (1 / 2 : ℝ) * ‖ω‖ :=
        hbound
    _ ≤ (∫ x, (|x.1| + |x.2|) ^ 2 * B0579.jb x ^ (-m)) ^ (1 / 2 : ℝ) * ‖ω‖ :=
        mul_le_mul_of_nonneg_right hpow (norm_nonneg _)

end UnforcedLeray.Short.IIIa.CTE.T20_3
