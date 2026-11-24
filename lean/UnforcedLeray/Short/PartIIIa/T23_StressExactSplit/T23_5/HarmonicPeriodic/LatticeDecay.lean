import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T23_5_1_1
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.UpperHalfPlane.Exp

/-!
# Part III-a, `PartIII-a:T23/5/1/1/2`: `LatticeSumDecay` (source 2354-2356)

For `|Im w| ≥ 1`, the lattice sums `S₂(w) = ∑_n (w+n)⁻²` and `S₃(w) = ∑_n (w+n)⁻³` are bounded by
`C₀ exp(-2π|Im w|)`.  Route: `π cot(πz) = -πi - 2πi H(z)` with `H(z) = (1 - q)⁻¹ - 1`,
`q = exp(2πiz)`, on the upper half plane; Mathlib's
`iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow` identifies the derivatives of `π cot(πz)` with
the lattice sums; Cauchy's estimates on the disc of radius `1/2` bound the derivatives of `H`.
The lower half plane follows from `S_k(-w) = (-1)^k S_k(w)`.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Metric

namespace UnforcedLeray.Short.IIIa

/-- The nome `q(z) = exp(2πi z)`. -/
def ldQ (x : ℂ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * x)

/-- `H(z) = (1 - q)⁻¹ - 1`, holomorphic on the upper half plane. -/
def ldH (x : ℂ) : ℂ := (1 - ldQ x)⁻¹ - 1

theorem ld_norm_q (x : ℂ) : ‖ldQ x‖ = Real.exp (-(2 * Real.pi * x.im)) := by
  unfold ldQ
  rw [Complex.norm_exp]
  congr 1
  simp

theorem ld_norm_q_lt (x : ℂ) (hx : 0 < x.im) : ‖ldQ x‖ < 1 := by
  rw [ld_norm_q, Real.exp_lt_one_iff]
  have := Real.pi_pos
  nlinarith

theorem ld_one_sub_ne (x : ℂ) (hx : 0 < x.im) : 1 - ldQ x ≠ 0 := by
  intro h
  have h1 : ldQ x = 1 := by linear_combination -h
  have h2 := ld_norm_q_lt x hx
  rw [h1, norm_one] at h2
  exact lt_irrefl _ h2

theorem ld_diff (x : ℂ) (hx : 0 < x.im) : DifferentiableAt ℂ ldH x := by
  have h1 : DifferentiableAt ℂ (fun y : ℂ => 1 - ldQ y) x := by
    unfold ldQ
    fun_prop
  exact (h1.inv (ld_one_sub_ne x hx)).sub_const 1

/-- The cotangent identity `π cot(πz) = -πi - 2πi H(z)` on the upper half plane. -/
theorem ld_cot_identity (z : ℂ) (hz : 0 < z.im) :
    (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z) =
      -((Real.pi : ℂ) * Complex.I) + (-(2 * (Real.pi : ℂ) * Complex.I)) * ldH z := by
  have hm : (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z) =
      (Real.pi : ℂ) * Complex.I - 2 * (Real.pi : ℂ) * Complex.I * ∑' n : ℕ, ldQ z ^ n :=
    pi_mul_cot_pi_q_exp (⟨z, hz⟩ : UpperHalfPlane)
  rw [hm, tsum_geometric_of_norm_lt_one (ld_norm_q_lt z hz)]
  unfold ldH
  ring

/-- Derivatives of `π cot(πz)` of order `k ≥ 1` are those of `-2πi H`. -/
theorem ld_iter (k : ℕ) (hk : 0 < k) (z : ℂ) (hz : 0 < z.im) :
    iteratedDeriv k (fun x : ℂ => (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * x)) z =
      (-(2 * (Real.pi : ℂ) * Complex.I)) * iteratedDeriv k ldH z := by
  have hopen : IsOpen {x : ℂ | 0 < x.im} := isOpen_lt continuous_const Complex.continuous_im
  have hev : (fun x : ℂ => (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * x)) =ᶠ[𝓝 z]
      (fun x : ℂ => -((Real.pi : ℂ) * Complex.I) + (-(2 * (Real.pi : ℂ) * Complex.I)) * ldH x) :=
    Filter.eventually_of_mem (hopen.mem_nhds hz) (fun x hx => ld_cot_identity x hx)
  rw [hev.iteratedDeriv_eq k, iteratedDeriv_const_add hk, iteratedDeriv_const_mul_field]

theorem ld_im_ge (z x : ℂ) (hx : dist x z ≤ 1 / 2) : z.im - 1 / 2 ≤ x.im := by
  have h1 : ‖x - z‖ ≤ 1 / 2 := by rw [← dist_eq_norm]; exact hx
  have h2 : |(x - z).im| ≤ ‖x - z‖ := Complex.abs_im_le_norm (x - z)
  rw [Complex.sub_im] at h2
  have h3 := (abs_le.mp (h2.trans h1)).1
  linarith

theorem ld_H_bound (x : ℂ) (hx : 1 / 2 ≤ x.im) :
    ‖ldH x‖ ≤ 2 * Real.exp (-(2 * Real.pi * x.im)) := by
  have hx0 : 0 < x.im := by linarith
  have hq : ‖ldQ x‖ ≤ 1 / 2 := by
    rw [ld_norm_q]
    have h1 : Real.exp (-(2 * Real.pi * x.im)) ≤ Real.exp (-Real.pi) := by
      apply Real.exp_le_exp.2
      nlinarith [Real.pi_pos]
    have h2 : 2 ≤ Real.exp Real.pi := by
      have := Real.add_one_le_exp Real.pi
      linarith [Real.pi_gt_three]
    have h3 : Real.exp (-Real.pi) ≤ 1 / 2 := by
      rw [Real.exp_neg]
      have := inv_anti₀ (by norm_num : (0 : ℝ) < 2) h2
      norm_num at this ⊢
      linarith
    linarith
  have hid : ldH x = ldQ x * (1 - ldQ x)⁻¹ := by
    unfold ldH
    have hne := ld_one_sub_ne x hx0
    field_simp
    ring
  have hn : (1 : ℝ) / 2 ≤ ‖1 - ldQ x‖ := by
    have := norm_sub_norm_le (1 : ℂ) (ldQ x)
    rw [norm_one] at this
    linarith
  have hnpos : 0 < ‖1 - ldQ x‖ := by linarith
  have hinv : ‖(1 - ldQ x)⁻¹‖ ≤ 2 := by
    rw [norm_inv, inv_eq_one_div, div_le_iff₀ hnpos]
    linarith
  rw [hid, norm_mul]
  calc ‖ldQ x‖ * ‖(1 - ldQ x)⁻¹‖ ≤ ‖ldQ x‖ * 2 :=
        mul_le_mul_of_nonneg_left hinv (norm_nonneg _)
    _ = 2 * Real.exp (-(2 * Real.pi * x.im)) := by rw [ld_norm_q]; ring

theorem ld_sphere_bound (z : ℂ) (hz : 1 ≤ z.im) (x : ℂ) (hx : dist x z ≤ 1 / 2) :
    ‖ldH x‖ ≤ 2 * (Real.exp Real.pi * Real.exp (-(2 * Real.pi * z.im))) := by
  have hxim := ld_im_ge z x hx
  have hpi := Real.pi_pos
  have hx' : 1 / 2 ≤ x.im := by linarith
  have key : Real.exp (-(2 * Real.pi * x.im)) ≤
      Real.exp Real.pi * Real.exp (-(2 * Real.pi * z.im)) := by
    calc Real.exp (-(2 * Real.pi * x.im)) ≤ Real.exp (-(2 * Real.pi * z.im) + Real.pi) :=
          Real.exp_le_exp.2 (by nlinarith)
      _ = Real.exp (-(2 * Real.pi * z.im)) * Real.exp Real.pi := Real.exp_add _ _
      _ = Real.exp Real.pi * Real.exp (-(2 * Real.pi * z.im)) := mul_comm _ _
  exact (ld_H_bound x hx').trans (mul_le_mul_of_nonneg_left key (by norm_num))

/-- Cauchy estimates for `H` on the disc of radius `1/2` about `z` with `Im z ≥ 1`. -/
theorem ld_cauchy (z : ℂ) (hz : 1 ≤ z.im) :
    ‖iteratedDeriv 1 ldH z‖ ≤ 2 * (2 * (Real.exp Real.pi * Real.exp (-(2 * Real.pi * z.im)))) ∧
      ‖iteratedDeriv 2 ldH z‖ ≤ 8 * (2 * (Real.exp Real.pi * Real.exp (-(2 * Real.pi * z.im)))) := by
  have hDCO : DiffContOnCl ℂ ldH (ball z (1 / 2)) := by
    apply DifferentiableOn.diffContOnCl
    intro x hx
    have hx' : dist x z ≤ 1 / 2 := Metric.mem_closedBall.mp (closure_ball_subset_closedBall hx)
    have hxim := ld_im_ge z x hx'
    exact (ld_diff x (by linarith)).differentiableWithinAt
  have hC : ∀ x ∈ sphere z (1 / 2),
      ‖ldH x‖ ≤ 2 * (Real.exp Real.pi * Real.exp (-(2 * Real.pi * z.im))) := by
    intro x hx
    exact ld_sphere_bound z hz x (le_of_eq (Metric.mem_sphere.mp hx))
  have c1 := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 1 (by norm_num) hDCO hC
  have c2 := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 (by norm_num) hDCO hC
  constructor
  · calc ‖iteratedDeriv 1 ldH z‖ ≤ _ := c1
      _ = 2 * (2 * (Real.exp Real.pi * Real.exp (-(2 * Real.pi * z.im)))) := by
          norm_num [Nat.factorial] <;> ring
  · calc ‖iteratedDeriv 2 ldH z‖ ≤ _ := c2
      _ = 8 * (2 * (Real.exp Real.pi * Real.exp (-(2 * Real.pi * z.im)))) := by
          norm_num [Nat.factorial] <;> ring

/-- Decay of the two lattice sums in the upper half plane. -/
theorem ld_main (z : ℂ) (hz : 1 ≤ z.im) :
    ‖latticeSum 2 z‖ ≤ 8 * Real.pi * (Real.exp Real.pi * Real.exp (-(2 * Real.pi * z.im))) ∧
      ‖latticeSum 3 z‖ ≤ 16 * Real.pi * (Real.exp Real.pi * Real.exp (-(2 * Real.pi * z.im))) := by
  have hz0 : 0 < z.im := by linarith
  have hz' : z ∈ UpperHalfPlane.upperHalfPlaneSet := hz0
  have hopen := UpperHalfPlane.isOpen_upperHalfPlaneSet
  have hm1 := iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow (k := 1) le_rfl hz'
  have hm2 := iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow (k := 2) (by norm_num) hz'
  rw [iteratedDerivWithin_of_isOpen hopen hz'] at hm1 hm2
  rw [ld_iter 1 one_pos z hz0] at hm1
  rw [ld_iter 2 two_pos z hz0] at hm2
  have hf1 : ((Nat.factorial 1 : ℕ) : ℂ) = 1 := by norm_num
  have hf2 : ((Nat.factorial 2 : ℕ) : ℂ) = 2 := by norm_num [Nat.factorial]
  have hs2 : ∑' n : ℤ, 1 / ((z + (n : ℂ)) ^ (1 + 1)) = latticeSum 2 z := by
    unfold latticeSum
    apply tsum_congr
    intro n
    norm_num [one_div]
  have hs3 : ∑' n : ℤ, 1 / ((z + (n : ℂ)) ^ (2 + 1)) = latticeSum 3 z := by
    unfold latticeSum
    apply tsum_congr
    intro n
    norm_num [one_div]
  rw [hf1, hs2] at hm1
  rw [hf2, hs3] at hm2
  set E := Real.exp (-(2 * Real.pi * z.im)) with hE
  have hEp : 0 ≤ E := (Real.exp_pos _).le
  obtain ⟨c1, c2⟩ := ld_cauchy z hz
  have hpi : 0 < Real.pi := Real.pi_pos
  have hnI : ‖2 * (Real.pi : ℂ) * Complex.I‖ = 2 * Real.pi := by
    simp [abs_of_pos hpi]
  have hnI3 : ‖-(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
    rw [norm_neg, hnI]
  -- lattice sum 2
  have e2 : latticeSum 2 z = (2 * (Real.pi : ℂ) * Complex.I) * iteratedDeriv 1 ldH z := by
    linear_combination hm1
  have e3 : latticeSum 3 z = -((Real.pi : ℂ) * Complex.I) * iteratedDeriv 2 ldH z := by
    linear_combination -hm2 / 2
  have b2 : ‖latticeSum 2 z‖ ≤ 8 * Real.pi * (Real.exp Real.pi * E) := by
    rw [e2, norm_mul, hnI]
    have := mul_le_mul_of_nonneg_left c1 (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    nlinarith [this]
  have b3 : ‖latticeSum 3 z‖ ≤ 16 * Real.pi * (Real.exp Real.pi * E) := by
    rw [e3, norm_mul, norm_neg, norm_mul, Complex.norm_I, mul_one]
    have hr : ‖(Real.pi : ℂ)‖ = Real.pi := by
      rw [Complex.norm_real, Real.norm_of_nonneg hpi.le]
    rw [hr]
    have := mul_le_mul_of_nonneg_left c2 hpi.le
    nlinarith [this]
  exact ⟨b2, b3⟩

/-- Reflection `S_k(-w) = (-1)^k S_k(w)`. -/
theorem ld_latticeSum_neg (k : ℕ) (w : ℂ) : latticeSum k (-w) = (-1) ^ k * latticeSum k w := by
  unfold latticeSum
  have hsq : ((-1 : ℂ) ^ k) * ((-1 : ℂ) ^ k) = 1 := by
    rw [← mul_pow]
    norm_num
  have hinv : ((-1 : ℂ) ^ k)⁻¹ = (-1) ^ k := inv_eq_of_mul_eq_one_right hsq
  rw [← tsum_mul_left]
  calc ∑' n : ℤ, ((-w + (n : ℂ)) ^ k)⁻¹
      = ∑' n : ℤ, (-1 : ℂ) ^ k * ((w + ((-n : ℤ) : ℂ)) ^ k)⁻¹ := by
        apply tsum_congr
        intro n
        have e : -w + (n : ℂ) = -(w + ((-n : ℤ) : ℂ)) := by
          push_cast
          ring
        rw [e, neg_pow, mul_inv, hinv]
    _ = ∑' n : ℤ, (-1 : ℂ) ^ k * ((w + (n : ℂ)) ^ k)⁻¹ :=
        Equiv.tsum_eq (Equiv.neg ℤ) (fun n : ℤ => (-1 : ℂ) ^ k * ((w + (n : ℂ)) ^ k)⁻¹)

theorem ld_norm_neg (k : ℕ) (w : ℂ) : ‖latticeSum k w‖ = ‖latticeSum k (-w)‖ := by
  have h := ld_latticeSum_neg k (-w)
  rw [neg_neg] at h
  rw [h, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]

theorem latticeSumDecay : UnforcedLeray.Short.IIIa.LatticeSumDecay := by
  refine ⟨16 * Real.pi * Real.exp Real.pi, fun w hw => ?_⟩
  have hP : 0 ≤ Real.pi * Real.exp Real.pi := by positivity
  rcases le_abs'.mp hw with h | h
  · -- `w.im ≤ -1`: reflect to `-w`
    have hu : 1 ≤ (-w).im := by
      rw [Complex.neg_im]
      linarith
    obtain ⟨h2, h3⟩ := ld_main (-w) hu
    simp only [Complex.neg_im] at h2 h3
    have habs : |w.im| = -w.im := abs_of_neg (by linarith)
    rw [habs, ld_norm_neg 2 w, ld_norm_neg 3 w]
    have hE : 0 ≤ Real.exp (-(2 * Real.pi * -w.im)) := (Real.exp_pos _).le
    have hPE : 0 ≤ Real.pi * Real.exp Real.pi * Real.exp (-(2 * Real.pi * -w.im)) := by positivity
    constructor
    · nlinarith
    · nlinarith
  · -- `w.im ≥ 1`
    have habs : |w.im| = w.im := abs_of_pos (by linarith)
    obtain ⟨h2, h3⟩ := ld_main w h
    rw [habs]
    have hPE : 0 ≤ Real.pi * Real.exp Real.pi * Real.exp (-(2 * Real.pi * w.im)) := by positivity
    constructor
    · nlinarith
    · nlinarith

end UnforcedLeray.Short.IIIa
