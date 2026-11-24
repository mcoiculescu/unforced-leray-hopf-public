import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Order.CompletePartialOrder
import Std.Tactic.BVDecide.LRAT.Internal.Formula.RupAddResult

/-!
# The csc² lattice sum and its transverse tails (INF22 G10, BP10)


target G10 and bypass BP10; decision D14 (built once, through Mathlib `Cotangent.lean`, without
INF20 T20.5). Units B0233 (tex 3989–4008) and B0297 (tex 5264–5280).

Main results:
* `tsum_inv_sq_eq_csc_sq`: `∑_{n∈ℤ} (z+n)^{-2} = π² / sin²(πz)` for `Im z > 0`, from the `k = 1`
  case of Mathlib's `iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow`;
* `latticeInvSq_eq` (tex 3991–3995): `∑_{n∈ℤ} (w+nℓ)^{-2} = (π/ℓ)² csc²(πw/ℓ)` for every `ℓ > 0`
  and every `w` off the real axis (both half planes, by `w ↦ -w` and `n ↦ -n`);
* `norm_iteratedDeriv_latticeInvSq_le` (tex 3998–4000): for every `j` there is `C` with
  `‖∂_w^j ∑_n (w+nℓ)^{-2}‖ ≤ C ℓ^{-2-j} e^{-2π|η|/ℓ}` at `w = q + iη`, `|η| ≥ ℓ > 0`
  (the derivative is the complex derivative of the series as a function of `w`; the identity
  above shows the series is holomorphic off the real axis). Proof: `|sin(x+iy)| ≥ sinh|y|` and
  Cauchy's estimate on the disc of radius `ℓ/2`.

No junk values occur: every `tsum` used is summable at the points where it is evaluated
(`Im w ≠ 0`), and `sin(πw/ℓ) ≠ 0` there.
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.Gaussian

open Complex Filter Topology Metric Set
open scoped Real Nat

/-- The derivative of `π cot(πz)` is `-π²/sin²(πz)` where `sin(πz) ≠ 0`. -/
theorem hasDerivAt_pi_mul_cot_pi_mul {z : ℂ} (hz : Complex.sin (π * z) ≠ 0) :
    HasDerivAt (fun x : ℂ => (π : ℂ) * Complex.cot (π * x))
      (-(π : ℂ) ^ 2 / Complex.sin (π * z) ^ 2) z := by
  have h1 : HasDerivAt (fun x : ℂ => (π : ℂ) * x) π z := by
    simpa using (hasDerivAt_id z).const_mul (π : ℂ)
  have hc : HasDerivAt (fun x : ℂ => Complex.cos (π * x)) (-Complex.sin (π * z) * π) z :=
    (Complex.hasDerivAt_cos (π * z)).comp z h1
  have hs : HasDerivAt (fun x : ℂ => Complex.sin (π * x)) (Complex.cos (π * z) * π) z :=
    (Complex.hasDerivAt_sin (π * z)).comp z h1
  have hq := (hc.div hs hz).const_mul (π : ℂ)
  have hderiv : (π : ℂ) * ((-Complex.sin (π * z) * π * Complex.sin (π * z) -
      Complex.cos (π * z) * (Complex.cos (π * z) * π)) / Complex.sin (π * z) ^ 2) =
      -(π : ℂ) ^ 2 / Complex.sin (π * z) ^ 2 := by
    rw [mul_div_assoc', div_left_inj' (pow_ne_zero 2 hz)]
    linear_combination (-(π : ℂ) ^ 2) * Complex.sin_sq_add_cos_sq (π * z)
  rw [hderiv] at hq
  refine hq.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
  simp [Complex.cot_eq_cos_div_sin]

/-- **G10 (B0233).** `∑_{n∈ℤ} (z+n)^{-2} = π²/sin²(πz)` on the upper half plane. -/
theorem tsum_inv_sq_eq_csc_sq {z : ℂ} (hz : 0 < z.im) :
    ∑' n : ℤ, (z + n)⁻¹ ^ 2 = π ^ 2 / Complex.sin (π * z) ^ 2 := by
  have hmem : z ∈ UpperHalfPlane.upperHalfPlaneSet := hz
  have h := iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow (k := 1) le_rfl hmem
  rw [iteratedDerivWithin_of_isOpen UpperHalfPlane.isOpen_upperHalfPlaneSet hmem,
    iteratedDeriv_one] at h
  have hs : Complex.sin (π * z) ≠ 0 :=
    sin_pi_mul_ne_zero (UpperHalfPlane.coe_mem_integerComplement ⟨z, hz⟩)
  rw [(hasDerivAt_pi_mul_cot_pi_mul hs).deriv] at h
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, mul_one, neg_one_mul, neg_div] at h
  have key := neg_injective h
  rw [key]
  congr 1
  funext n
  rw [one_div, inv_pow]

/-- The csc² lattice sum with period `ℓ`, as a function of `w ∈ ℂ` (tex 3991). -/
def latticeInvSq (ℓ : ℝ) (w : ℂ) : ℂ := ∑' n : ℤ, (w + n * ℓ)⁻¹ ^ 2

/-- Its closed form `(π/ℓ)² csc²(πw/ℓ)`. -/
def cscSqLattice (ℓ : ℝ) (w : ℂ) : ℂ := ((π : ℂ) / ℓ) ^ 2 / Complex.sin (π * w / ℓ) ^ 2

theorem latticeInvSq_eq_of_im_pos {ℓ : ℝ} (hℓ : 0 < ℓ) {w : ℂ} (hw : 0 < w.im) :
    latticeInvSq ℓ w = cscSqLattice ℓ w := by
  have hℓ0 : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne'
  have him : 0 < (w / ℓ).im := by rw [div_ofReal_im]; exact div_pos hw hℓ
  have hterm : ∀ n : ℤ, (w + n * ℓ)⁻¹ ^ 2 = ((ℓ : ℂ) ^ 2)⁻¹ * (w / ℓ + n)⁻¹ ^ 2 := by
    intro n
    rw [show w + n * ℓ = ℓ * (w / ℓ + n) by field_simp]
    rw [mul_inv, mul_pow, inv_pow]
  unfold latticeInvSq cscSqLattice
  simp_rw [hterm]
  rw [tsum_mul_left, tsum_inv_sq_eq_csc_sq him]
  rw [show (π : ℂ) * (w / ℓ) = π * w / ℓ by ring]
  field_simp

/-- **G10 (B0233, tex 3991–3995).** `∑_{n∈ℤ}(w+nℓ)^{-2} = (π/ℓ)² csc²(πw/ℓ)` off the real
axis. -/
theorem latticeInvSq_eq {ℓ : ℝ} (hℓ : 0 < ℓ) {w : ℂ} (hw : w.im ≠ 0) :
    latticeInvSq ℓ w = cscSqLattice ℓ w := by
  rcases hw.lt_or_gt with hneg | hpos
  · have h' := latticeInvSq_eq_of_im_pos hℓ (w := -w) (by simpa using hneg)
    have hL : latticeInvSq ℓ w = latticeInvSq ℓ (-w) := by
      unfold latticeInvSq
      rw [← (Equiv.neg ℤ).tsum_eq (fun n : ℤ => (-w + n * ℓ)⁻¹ ^ 2)]
      congr 1
      funext n
      simp only [Equiv.neg_apply, Int.cast_neg]
      have e : ∀ u v : ℂ, v = -u → u⁻¹ ^ 2 = v⁻¹ ^ 2 := by
        intro u v h; rw [h, inv_neg, neg_sq]
      exact e _ _ (by ring)
    have hR : cscSqLattice ℓ (-w) = cscSqLattice ℓ w := by
      unfold cscSqLattice
      rw [show (π : ℂ) * -w / ℓ = -(π * w / ℓ) by ring, Complex.sin_neg, neg_sq]
    rw [hL, h', hR]
  · exact latticeInvSq_eq_of_im_pos hℓ hpos

/-- `|sin w| ≥ (e^{|Im w|} - e^{-|Im w|})/2`. -/
theorem sinh_abs_im_le_norm_sin (w : ℂ) :
    (Real.exp |w.im| - Real.exp (-|w.im|)) / 2 ≤ ‖Complex.sin w‖ := by
  have h2 : ‖(2 : ℂ) * Complex.sin w‖ = ‖Complex.exp (-w * I) - Complex.exp (w * I)‖ := by
    rw [Complex.two_sin, norm_mul, Complex.norm_I, mul_one]
  have hre1 : (-w * I).re = w.im := by simp [Complex.mul_re]
  have hre2 : (w * I).re = -w.im := by simp [Complex.mul_re]
  have hrev := abs_norm_sub_norm_le (Complex.exp (-w * I)) (Complex.exp (w * I))
  rw [Complex.norm_exp, Complex.norm_exp, hre1, hre2, ← h2, norm_mul] at hrev
  have hn2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [hn2] at hrev
  have habs : Real.exp |w.im| - Real.exp (-|w.im|) ≤ |Real.exp w.im - Real.exp (-w.im)| := by
    rcases abs_cases w.im with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]; exact le_abs_self _
    · rw [h, neg_neg, abs_sub_comm]; exact le_abs_self _
  linarith

/-- The constant `K = 4/(1 - e^{-π})²` of the csc² tail. -/
def cscTailConst : ℝ := 4 / (1 - Real.exp (-π)) ^ 2

theorem one_sub_exp_neg_pi_pos : 0 < 1 - Real.exp (-π) := by
  have : Real.exp (-π) < 1 := Real.exp_lt_one_iff.2 (by linarith [Real.pi_pos])
  linarith

theorem cscTailConst_pos : 0 < cscTailConst := by
  unfold cscTailConst; have := one_sub_exp_neg_pi_pos; positivity

/-- `‖1/sin² w‖ ≤ K e^{-2|Im w|}` when `|Im w| ≥ π/2`. -/
theorem norm_inv_sin_sq_le {w : ℂ} (hw : π / 2 ≤ |w.im|) :
    ‖(Complex.sin w ^ 2)⁻¹‖ ≤ cscTailConst * Real.exp (-2 * |w.im|) := by
  set y := |w.im| with hy
  have hδ := one_sub_exp_neg_pi_pos
  have hey : 0 < Real.exp y := Real.exp_pos y
  have hlow : Real.exp y * (1 - Real.exp (-π)) / 2 ≤ ‖Complex.sin w‖ := by
    refine le_trans ?_ (sinh_abs_im_le_norm_sin w)
    have h1 : Real.exp (-y) = Real.exp y * Real.exp (-2 * y) := by
      rw [← Real.exp_add]; ring_nf
    have h2 : Real.exp (-2 * y) ≤ Real.exp (-π) := Real.exp_le_exp.2 (by linarith)
    rw [h1]
    have : Real.exp y * Real.exp (-2 * y) ≤ Real.exp y * Real.exp (-π) :=
      mul_le_mul_of_nonneg_left h2 hey.le
    linarith
  have hpos : 0 < Real.exp y * (1 - Real.exp (-π)) / 2 := by positivity
  have hsn : 0 < ‖Complex.sin w‖ := lt_of_lt_of_le hpos hlow
  rw [norm_inv, norm_pow]
  have hsq : (Real.exp y * (1 - Real.exp (-π)) / 2) ^ 2 ≤ ‖Complex.sin w‖ ^ 2 :=
    pow_le_pow_left₀ hpos.le hlow 2
  rw [inv_le_iff_one_le_mul₀ (by positivity)]
  have hE : Real.exp (-2 * y) * Real.exp y ^ 2 = 1 := by
    rw [sq, ← Real.exp_add, ← Real.exp_add, show -2 * y + (y + y) = 0 by ring, Real.exp_zero]
  have : cscTailConst * Real.exp (-2 * y) * (Real.exp y * (1 - Real.exp (-π)) / 2) ^ 2 = 1 := by
    unfold cscTailConst
    have hδ2 : (1 - Real.exp (-π)) ^ 2 ≠ 0 := by positivity
    calc 4 / (1 - Real.exp (-π)) ^ 2 * Real.exp (-2 * y) * (Real.exp y * (1 - Real.exp (-π)) / 2) ^ 2
        = (Real.exp (-2 * y) * Real.exp y ^ 2) *
            (4 / (1 - Real.exp (-π)) ^ 2 * ((1 - Real.exp (-π)) ^ 2 / 4)) := by ring
      _ = 1 := by rw [hE, one_mul, div_mul_div_comm, mul_comm 4, div_self (by positivity)]
  calc 1 = cscTailConst * Real.exp (-2 * y) * (Real.exp y * (1 - Real.exp (-π)) / 2) ^ 2 :=
        this.symm
    _ ≤ cscTailConst * Real.exp (-2 * y) * ‖Complex.sin w‖ ^ 2 := by
        gcongr
        exact mul_nonneg cscTailConst_pos.le (Real.exp_pos _).le

/-- Pointwise transverse tail: for `|Im w| ≥ ℓ/2`,
`‖(π/ℓ)² csc²(πw/ℓ)‖ ≤ π² K ℓ^{-2} e^{-2π|Im w|/ℓ}`. -/
theorem norm_cscSqLattice_le {ℓ : ℝ} (hℓ : 0 < ℓ) {w : ℂ} (hw : ℓ / 2 ≤ |w.im|) :
    ‖cscSqLattice ℓ w‖ ≤ π ^ 2 * cscTailConst * (ℓ ^ 2)⁻¹ *
      Real.exp (-2 * π * |w.im| / ℓ) := by
  have him : (π * w / ℓ : ℂ).im = π * w.im / ℓ := by
    rw [div_ofReal_im]; simp [Complex.mul_im]
  have habs : |(π * w / ℓ : ℂ).im| = π * |w.im| / ℓ := by
    rw [him, abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hℓ]
  have hge : π / 2 ≤ |(π * w / ℓ : ℂ).im| := by
    rw [habs, le_div_iff₀ hℓ]
    nlinarith [Real.pi_pos]
  have hb := norm_inv_sin_sq_le hge
  rw [habs] at hb
  unfold cscSqLattice
  rw [div_eq_mul_inv, norm_mul, norm_pow, norm_div, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le, Real.norm_of_nonneg hℓ.le]
  have hexp : Real.exp (-2 * (π * |w.im| / ℓ)) = Real.exp (-2 * π * |w.im| / ℓ) := by
    congr 1; ring
  rw [hexp] at hb
  calc (π / ℓ) ^ 2 * ‖(Complex.sin (π * w / ℓ) ^ 2)⁻¹‖
      ≤ (π / ℓ) ^ 2 * (cscTailConst * Real.exp (-2 * π * |w.im| / ℓ)) := by gcongr
    _ = π ^ 2 * cscTailConst * (ℓ ^ 2)⁻¹ * Real.exp (-2 * π * |w.im| / ℓ) := by
        field_simp

theorem sin_pi_mul_div_ne_zero {ℓ : ℝ} (hℓ : 0 < ℓ) {w : ℂ} (hw : w.im ≠ 0) :
    Complex.sin (π * w / ℓ) ≠ 0 := by
  intro h0
  have hpos : 0 < (Real.exp |(π * w / ℓ : ℂ).im| - Real.exp (-|(π * w / ℓ : ℂ).im|)) / 2 := by
    have : 0 < |(π * w / ℓ : ℂ).im| := by
      rw [div_ofReal_im]
      refine abs_pos.2 (div_ne_zero ?_ hℓ.ne')
      simp [Complex.mul_im, Real.pi_ne_zero, hw]
    have : Real.exp (-|(π * w / ℓ : ℂ).im|) < Real.exp |(π * w / ℓ : ℂ).im| :=
      Real.exp_lt_exp.2 (by linarith)
    linarith
  have := sinh_abs_im_le_norm_sin (π * w / ℓ)
  rw [h0, norm_zero] at this
  linarith

theorem differentiableAt_cscSqLattice {ℓ : ℝ} (hℓ : 0 < ℓ) {w : ℂ} (hw : w.im ≠ 0) :
    DifferentiableAt ℂ (cscSqLattice ℓ) w := by
  have hs := sin_pi_mul_div_ne_zero hℓ hw
  unfold cscSqLattice
  refine DifferentiableAt.div (differentiableAt_const _) ?_ (pow_ne_zero 2 hs)
  refine DifferentiableAt.pow ?_ 2
  refine Complex.differentiableAt_sin.comp w ?_
  exact ((differentiableAt_id.const_mul _).div_const _)

/-- **G10 (B0233, B0297; tex 3996–4000).** Exponential transverse decay of the csc² lattice sum
and of all its complex derivatives: for every `j` there is `C > 0` such that, for all
`0 < ℓ ≤ |η|` and all `q`,
`‖∂^j_w ∑_{n∈ℤ}(w+nℓ)^{-2}‖ ≤ C ℓ^{-2-j} e^{-2π|η|/ℓ}` at `w = q + iη`. -/
theorem norm_iteratedDeriv_latticeInvSq_le (j : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ {ℓ q η : ℝ}, 0 < ℓ → ℓ ≤ |η| →
      ‖iteratedDeriv j (fun w : ℂ => ∑' n : ℤ, (w + n * ℓ)⁻¹ ^ 2) (q + η * Complex.I)‖ ≤
        C * ℓ ^ (-2 - (j : ℝ)) * Real.exp (-2 * π * |η| / ℓ) := by
  refine ⟨j ! * 2 ^ j * (π ^ 2 * cscTailConst * Real.exp π), by
    have := cscTailConst_pos; have := Real.pi_pos; positivity, ?_⟩
  intro ℓ q η hℓ hη
  set z0 : ℂ := q + η * Complex.I with hz0
  have hz0im : z0.im = η := by simp [hz0]
  have hR : 0 < ℓ / 2 := half_pos hℓ
  -- points of the closed disc of radius ℓ/2 stay at height ≥ ℓ/2
  have hball : ∀ w ∈ closedBall z0 (ℓ / 2), |η| - ℓ / 2 ≤ |w.im| := by
    intro w hw
    have h1 : |(w - z0).im| ≤ ‖w - z0‖ := Complex.abs_im_le_norm _
    rw [Complex.sub_im, hz0im] at h1
    have h2 : ‖w - z0‖ ≤ ℓ / 2 := by rwa [mem_closedBall, dist_eq_norm] at hw
    have h3 : |η| - |w.im| ≤ |w.im - η| := by
      rw [abs_sub_comm]; exact abs_sub_abs_le_abs_sub η w.im
    linarith
  have hball' : ∀ w ∈ closedBall z0 (ℓ / 2), w.im ≠ 0 := by
    intro w hw h0
    have := hball w hw
    rw [h0, abs_zero] at this
    linarith
  -- the series agrees with the closed form near z0
  have hz0ne : z0.im ≠ 0 := by
    rw [hz0im]; intro h; rw [h, abs_zero] at hη; linarith
  have hopen : IsOpen {w : ℂ | w.im ≠ 0} :=
    isOpen_ne_fun Complex.continuous_im continuous_const
  have hev : (fun w : ℂ => ∑' n : ℤ, (w + n * ℓ)⁻¹ ^ 2) =ᶠ[𝓝 z0] cscSqLattice ℓ := by
    filter_upwards [hopen.mem_nhds hz0ne] with w hw
    exact latticeInvSq_eq hℓ hw
  rw [hev.iteratedDeriv_eq j]
  -- Cauchy's estimate on the disc of radius ℓ/2
  have hdiff : DiffContOnCl ℂ (cscSqLattice ℓ) (ball z0 (ℓ / 2)) := by
    refine DifferentiableOn.diffContOnCl_ball (U := closedBall z0 (ℓ / 2)) ?_ subset_rfl
    exact fun w hw => (differentiableAt_cscSqLattice hℓ (hball' w hw)).differentiableWithinAt
  set M : ℝ := π ^ 2 * cscTailConst * (ℓ ^ 2)⁻¹ * Real.exp π * Real.exp (-2 * π * |η| / ℓ)
    with hM
  have hsphere : ∀ w ∈ sphere z0 (ℓ / 2), ‖cscSqLattice ℓ w‖ ≤ M := by
    intro w hw
    have hwb : w ∈ closedBall z0 (ℓ / 2) := sphere_subset_closedBall hw
    have h1 := hball w hwb
    have h2 : ℓ / 2 ≤ |w.im| := by linarith
    refine (norm_cscSqLattice_le hℓ h2).trans ?_
    have hexp : Real.exp (-2 * π * |w.im| / ℓ) ≤ Real.exp π * Real.exp (-2 * π * |η| / ℓ) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have hk : π + -2 * π * |η| / ℓ - (-2 * π * |w.im| / ℓ) =
          (2 * π / ℓ) * (ℓ / 2 + |w.im| - |η|) := by
        field_simp; ring
      rw [← sub_nonneg, hk]
      exact mul_nonneg (by positivity) (by linarith)
    have hc : 0 ≤ π ^ 2 * cscTailConst * (ℓ ^ 2)⁻¹ := by
      have := cscTailConst_pos; positivity
    calc π ^ 2 * cscTailConst * (ℓ ^ 2)⁻¹ * Real.exp (-2 * π * |w.im| / ℓ)
        ≤ π ^ 2 * cscTailConst * (ℓ ^ 2)⁻¹ * (Real.exp π * Real.exp (-2 * π * |η| / ℓ)) :=
          mul_le_mul_of_nonneg_left hexp hc
      _ = M := by rw [hM]; ring
  have hC := norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hR hdiff hsphere
  refine hC.trans (le_of_eq ?_)
  have hrpow : ℓ ^ (-2 - (j : ℝ)) = ((ℓ ^ 2)⁻¹) * ((ℓ ^ j)⁻¹) := by
    rw [show (-2 - (j : ℝ)) = -((2 : ℕ) + (j : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_neg hℓ.le, ← Nat.cast_add, Real.rpow_natCast, pow_add, mul_inv]
  rw [hrpow, hM, div_pow]
  field_simp

end UnforcedLeray.Gaussian
