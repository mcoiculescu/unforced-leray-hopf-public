import NonUniqueEuler.H.Infra.SobolevOneD.Energy.Kernel

/-!
# Local weighted bounds for the actual one-dimensional Green kernel

On a fixed unit neighbourhood of a centre `x₀`, both the kernel and its
Lipschitz bound retain the integrable exponential weight `exp(-L|x₀-y|)`.
These estimates support differentiation under the integral for L² inputs,
without requiring the inputs to belong to L¹ or have compact support.
-/

noncomputable section
namespace UnforcedLeray.Sturm
open NonUniqueEuler.Sob.EnergyAux

/-- Exponentials below a common upper exponent have a weighted Lipschitz bound. -/
theorem abs_exp_sub_le_exp_upper {u v A : ℝ} (hu : u ≤ A) (hv : v ≤ A) :
    |Real.exp u - Real.exp v| ≤ Real.exp A * |u - v| := by
  have h := abs_exp_neg_sub_le (sub_nonneg.mpr hu) (sub_nonneg.mpr hv)
  have hu' : Real.exp u = Real.exp A * Real.exp (-(A - u)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hv' : Real.exp v = Real.exp A * Real.exp (-(A - v)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hu', hv', ← mul_sub, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hdist : |(A - u) - (A - v)| = |u - v| := by
    rw [show (A - u) - (A - v) = -(u - v) by ring, abs_neg]
  rw [hdist] at h
  exact mul_le_mul_of_nonneg_left h (Real.exp_pos _).le

/-- The exponent of the shifted kernel is uniformly bounded on a unit neighbourhood. -/
theorem k0_local_exponent_bound {L : ℝ} (hL : 0 ≤ L) (x x0 y : ℝ)
    (hx : |x - x0| ≤ 1) : -L * |x - y| ≤ L - L * |x0 - y| := by
  have ht : |x0 - y| ≤ |x0 - x| + |x - y| := abs_sub_le x0 x y
  rw [abs_sub_comm x0 x] at ht
  have hdist : |x0 - y| ≤ 1 + |x - y| := by linarith
  have hm := mul_le_mul_of_nonneg_left hdist hL
  nlinarith

/-- The actual Green kernel has a common exponentially weighted local bound. -/
theorem k0_local_bound {L : ℝ} (hL : 0 ≤ L) (x x0 y : ℝ)
    (hx : |x - x0| ≤ 1) :
    k0 L (x - y) ≤ Real.exp L * k0 L (x0 - y) := by
  unfold k0
  rw [← Real.exp_add, Real.exp_le_exp]
  simpa only [neg_mul, sub_eq_add_neg] using k0_local_exponent_bound hL x x0 y hx

/-- The derivative-sign kernel has the same weighted local bound. -/
theorem k1_local_bound {L : ℝ} (hL : 0 ≤ L) (x x0 y : ℝ)
    (hx : |x - x0| ≤ 1) :
    |k1 L (x - y)| ≤ Real.exp L * k0 L (x0 - y) := by
  rw [abs_k1]
  exact k0_local_bound hL x x0 y hx

/-- The actual exponential kernel is locally Lipschitz with its centre's decay weight. -/
theorem k0_local_lipschitz {L : ℝ} (hL : 0 ≤ L) (x x' x0 y : ℝ)
    (hx : |x - x0| ≤ 1) (hx' : |x' - x0| ≤ 1) :
    |k0 L (x - y) - k0 L (x' - y)| ≤
      L * Real.exp L * k0 L (x0 - y) * |x - x'| := by
  have he := abs_exp_sub_le_exp_upper
    (k0_local_exponent_bound hL x x0 y hx)
    (k0_local_exponent_bound hL x' x0 y hx')
  have hdist : |(-L * |x - y|) - (-L * |x' - y|)| ≤ L * |x - x'| := by
    rw [← mul_sub, abs_mul, abs_neg, abs_of_nonneg hL]
    have h := abs_abs_sub_abs_le_abs_sub (x - y) (x' - y)
    have hsub : (x - y) - (x' - y) = x - x' := by ring
    rw [hsub] at h
    exact mul_le_mul_of_nonneg_left h hL
  have hweight : Real.exp (L - L * |x0 - y|) = Real.exp L * k0 L (x0 - y) := by
    unfold k0
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    |k0 L (x - y) - k0 L (x' - y)| ≤
        Real.exp (L - L * |x0 - y|) * |(-L * |x - y|) - (-L * |x' - y|)| := he
    _ ≤ Real.exp (L - L * |x0 - y|) * (L * |x - x'|) :=
      mul_le_mul_of_nonneg_left hdist (Real.exp_pos _).le
    _ = L * Real.exp L * k0 L (x0 - y) * |x - x'| := by
      rw [hweight]
      ring

end UnforcedLeray.Sturm
