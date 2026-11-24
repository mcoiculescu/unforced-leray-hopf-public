import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_6_1_4
import UnforcedLeray.Lib.Gaussian.Periodization
import UnforcedLeray.Lib.Gaussian.Absorb

/-!
# Part II-b, `VcSmooth` leaves: smoothness of the lattice Gaussian sums (SP 2205)

Proves `ThetaSmooth0`, `ThetaSmooth1` (hence `VcSmooth`) without any several-variable complex
analysis.  With `u = (4(1+νs))⁻¹ > 0` the sums are `T_j(u,q) = ∑ₙ (q-nc)^j e^{-u(q-nc)²}`, `j = 0, 1`,
and for every `j` the family satisfies `∂_u T_j = -T_{j+2}`, `∂_q T_j = j T_{j-1} - 2u T_{j+1}`
(termwise differentiation, locally uniform Gaussian bounds), so induction on the order `k` shows
every `T_j` is `C^k` on `u > 0`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

/-- `|y|^p e^{-m y²} ≤ C (1+|y|)^{-2}`. -/
theorem gauss_poly_le (p : ℕ) {m : ℝ} (hm : 0 < m) : ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ,
    |y| ^ p * Real.exp (-(m * y ^ 2)) ≤ C * (1 + |y|) ^ (-2 : ℝ) := by
  have key : ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, |y| ^ k * Real.exp (-(m * y ^ 2)) ≤ C := by
    intro k
    obtain ⟨C, hC, h⟩ := UnforcedLeray.Gaussian.rpow_mul_exp_neg_mul_sq_le (m := (k : ℝ))
      (b := m) (Nat.cast_nonneg k) hm
    refine ⟨C, hC, fun y => ?_⟩
    have := h |y| (abs_nonneg y)
    rwa [Real.rpow_natCast, sq_abs] at this
  obtain ⟨C0, h0, b0⟩ := key p
  obtain ⟨C1, h1, b1⟩ := key (p + 1)
  obtain ⟨C2, h2, b2⟩ := key (p + 2)
  refine ⟨C0 + 2 * C1 + C2, by positivity, fun y => ?_⟩
  have hp : 0 < (1 + |y|) ^ (2 : ℕ) := by positivity
  rw [Real.rpow_neg (by positivity), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    ← div_eq_mul_inv, le_div_iff₀ hp]
  have e : |y| ^ p * Real.exp (-(m * y ^ 2)) * (1 + |y|) ^ (2 : ℕ) =
      |y| ^ p * Real.exp (-(m * y ^ 2)) + 2 * (|y| ^ (p + 1) * Real.exp (-(m * y ^ 2))) +
        |y| ^ (p + 2) * Real.exp (-(m * y ^ 2)) := by ring
  rw [e]
  simp only [Nat.cast_ofNat]
  linarith [b0 y, b1 y, b2 y]

/-- Bound uniform in `u ≥ m`. -/
theorem gauss_poly_le' (p : ℕ) {m : ℝ} (hm : 0 < m) : ∃ C : ℝ, 0 < C ∧ ∀ u y : ℝ, m ≤ u →
    |y| ^ p * Real.exp (-u * y ^ 2) ≤ C * (1 + |y|) ^ (-2 : ℝ) := by
  obtain ⟨C, hC, h⟩ := gauss_poly_le p hm
  refine ⟨C, hC, fun u y hu => le_trans ?_ (h y)⟩
  have : -u * y ^ 2 ≤ -(m * y ^ 2) := by nlinarith [sq_nonneg y]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 this) (by positivity)

/-- The `n`-th term of the lattice sum `T_j(u,q)`, `x = (u,q)`. -/
def ttTerm (c : ℝ) (j : ℕ) (n : ℤ) (x : ℝ × ℝ) : ℝ :=
  (x.2 - n * c) ^ j * Real.exp (-x.1 * (x.2 - n * c) ^ 2)

/-- `T_j(u,q) = ∑ₙ (q-nc)^j e^{-u(q-nc)²}`. -/
def tt (c : ℝ) (j : ℕ) (x : ℝ × ℝ) : ℝ := ∑' n : ℤ, ttTerm c j n x

theorem norm_ttTerm (c : ℝ) (j : ℕ) (n : ℤ) (x : ℝ × ℝ) :
    ‖ttTerm c j n x‖ = |x.2 - n * c| ^ j * Real.exp (-x.1 * (x.2 - n * c) ^ 2) := by
  unfold ttTerm
  rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_of_nonneg (Real.exp_pos _).le]

theorem summable_ttTerm {c : ℝ} (hc : c ≠ 0) (j : ℕ) {x : ℝ × ℝ} (hx : 0 < x.1) :
    Summable (fun n : ℤ => ttTerm c j n x) := by
  obtain ⟨C, hC, h⟩ := gauss_poly_le' j hx
  refine Summable.of_norm_bounded
    ((UnforcedLeray.Gaussian.summable_translate (by norm_num : (1 : ℝ) < 2) hc x.2).mul_left C)
    fun n => ?_
  rw [norm_ttTerm]
  exact h x.1 _ le_rfl

/-- The derivative of the `n`-th term. -/
def ttDeriv (c : ℝ) (j : ℕ) (n : ℤ) (x : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  (-(ttTerm c (j + 2) n x)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
    ((j : ℝ) * ttTerm c (j - 1) n x - 2 * x.1 * ttTerm c (j + 1) n x) •
      ContinuousLinearMap.snd ℝ ℝ ℝ

theorem hasFDerivAt_ttTerm (c : ℝ) (j : ℕ) (n : ℤ) (x : ℝ × ℝ) :
    HasFDerivAt (fun x : ℝ × ℝ => ttTerm c j n x) (ttDeriv c j n x) x := by
  have hy : HasFDerivAt (fun x : ℝ × ℝ => x.2 - n * c) (ContinuousLinearMap.snd ℝ ℝ ℝ) x :=
    (hasFDerivAt_snd).sub_const _
  have h1 := hy.pow j
  have h2 := (hasFDerivAt_fst (𝕜 := ℝ) (p := x)).neg.mul (hy.pow 2)
  have h3 := h2.exp
  have h4 := h1.mul h3
  refine h4.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun p => ?_
  simp only [ttDeriv, ttTerm, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply, nsmul_eq_mul]
  simp
  ring

theorem hasFDerivAt_tt {c : ℝ} (hc : c ≠ 0) (j : ℕ) {x : ℝ × ℝ} (hx : 0 < x.1) :
    HasFDerivAt (tt c j)
      ((-(tt c (j + 2) x)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        ((j : ℝ) * tt c (j - 1) x - 2 * x.1 * tt c (j + 1) x) •
          ContinuousLinearMap.snd ℝ ℝ ℝ) x := by
  set u0 := x.1 with hu0
  obtain ⟨C1, hC1, b1⟩ := gauss_poly_le' (j + 2) (by positivity : 0 < u0 / 2)
  obtain ⟨C2, hC2, b2⟩ := gauss_poly_le' (j - 1) (by positivity : 0 < u0 / 2)
  obtain ⟨C3, hC3, b3⟩ := gauss_poly_le' (j + 1) (by positivity : 0 < u0 / 2)
  set K : ℝ := C1 + j * C2 + 4 * u0 * C3 with hK
  have hK0 : 0 ≤ K := by positivity
  let S : Set (ℝ × ℝ) := Ioo (u0 / 2) (2 * u0) ×ˢ Metric.ball x.2 1
  have hSo : IsOpen S := isOpen_Ioo.prod Metric.isOpen_ball
  have hSc : IsPreconnected S := ((convex_Ioo _ _).prod (convex_ball _ _)).isPreconnected
  have hxS : x ∈ S := ⟨⟨by linarith, by linarith⟩, Metric.mem_ball_self one_pos⟩
  have hbd : ∀ (n : ℤ) (y : ℝ × ℝ), y ∈ S →
      ‖ttDeriv c j n y‖ ≤ K * 4 * (1 + |x.2 - n * c|) ^ (-2 : ℝ) := by
    intro n y hy
    have hy1 : u0 / 2 ≤ y.1 := hy.1.1.le
    have hy2 : y.1 ≤ 2 * u0 := hy.1.2.le
    have hy3 : |y.2 - x.2| < 1 := by simpa [Real.dist_eq] using hy.2
    have tr : (1 + |y.2 - n * c|) ^ (-2 : ℝ) ≤ 2 ^ (2 : ℝ) * (1 + |x.2 - n * c|) ^ (-2 : ℝ) :=
      UnforcedLeray.Gaussian.translate_rpow_le_on_strip (by norm_num) hy3 _
    have t4 : (2 : ℝ) ^ (2 : ℝ) = 4 := by norm_num
    rw [t4] at tr
    set W := (1 + |x.2 - n * c|) ^ (-2 : ℝ) with hW
    have hW0 : 0 ≤ W := by positivity
    set Y := y.2 - n * c
    have e1 := b1 y.1 Y hy1
    have e2 := b2 y.1 Y hy1
    have e3 := b3 y.1 Y hy1
    have hE : 0 ≤ Real.exp (-y.1 * Y ^ 2) := (Real.exp_pos _).le
    unfold ttDeriv
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul]
    have hf := ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ
    have hs := ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ
    have hn1 : ‖(-(ttTerm c (j + 2) n y))‖ = |Y| ^ (j + 2) * Real.exp (-y.1 * Y ^ 2) := by
      rw [norm_neg, norm_ttTerm]
    have hn2 : ‖((j : ℝ) * ttTerm c (j - 1) n y - 2 * y.1 * ttTerm c (j + 1) n y)‖ ≤
        j * (|Y| ^ (j - 1) * Real.exp (-y.1 * Y ^ 2)) +
          2 * y.1 * (|Y| ^ (j + 1) * Real.exp (-y.1 * Y ^ 2)) := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, norm_mul, norm_ttTerm, norm_ttTerm, Real.norm_natCast,
        Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * y.1)]
    have hyp : 0 ≤ y.1 := by linarith
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    calc _ ≤ ‖(-(ttTerm c (j + 2) n y))‖ * 1 +
          ‖((j : ℝ) * ttTerm c (j - 1) n y - 2 * y.1 * ttTerm c (j + 1) n y)‖ * 1 := by
          gcongr
      _ ≤ (C1 * (1 + |Y|) ^ (-2 : ℝ)) + (j * (C2 * (1 + |Y|) ^ (-2 : ℝ)) +
            2 * y.1 * (C3 * (1 + |Y|) ^ (-2 : ℝ))) := by
          rw [mul_one, mul_one, hn1]
          refine add_le_add e1 (hn2.trans ?_)
          gcongr
      _ ≤ K * (1 + |Y|) ^ (-2 : ℝ) := by
          have h0 : 0 ≤ (1 + |Y|) ^ (-2 : ℝ) := by positivity
          have : 2 * y.1 * C3 ≤ 4 * u0 * C3 := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_right this h0]
      _ ≤ K * (4 * W) := by gcongr
      _ = K * 4 * W := by ring
  have hsum : Summable (fun n : ℤ => K * 4 * (1 + |x.2 - n * c|) ^ (-2 : ℝ)) :=
    (UnforcedLeray.Gaussian.summable_translate (by norm_num : (1 : ℝ) < 2) hc x.2).mul_left _
  have := hasFDerivAt_tsum_of_isPreconnected (f := fun n : ℤ => fun y : ℝ × ℝ => ttTerm c j n y)
    (f' := fun n y => ttDeriv c j n y) hsum hSo hSc (fun n y _ => hasFDerivAt_ttTerm c j n y) hbd
    hxS (summable_ttTerm hc j hx) hxS
  refine this.congr_fderiv ?_
  have s1 := summable_ttTerm hc (j + 2) hx
  have s2 := summable_ttTerm hc (j - 1) hx
  have s3 := summable_ttTerm hc (j + 1) hx
  unfold ttDeriv tt
  have hA : Summable (fun n : ℤ => -(ttTerm c (j + 2) n x)) := s1.neg
  have hB : Summable (fun n : ℤ => (j : ℝ) * ttTerm c (j - 1) n x - 2 * x.1 * ttTerm c (j + 1) n x) :=
    (s2.mul_left _).sub (s3.mul_left _)
  have hAf : Summable (fun n : ℤ => (-(ttTerm c (j + 2) n x)) • ContinuousLinearMap.fst ℝ ℝ ℝ) :=
    hA.smul_const _
  have hBf : Summable (fun n : ℤ => ((j : ℝ) * ttTerm c (j - 1) n x - 2 * x.1 * ttTerm c (j + 1) n x) •
      ContinuousLinearMap.snd ℝ ℝ ℝ) := hB.smul_const _
  rw [Summable.tsum_add hAf hBf, hA.tsum_smul_const, hB.tsum_smul_const, tsum_neg,
    Summable.tsum_sub (s2.mul_left _) (s3.mul_left _), tsum_mul_left, tsum_mul_left]

theorem fderiv_tt {c : ℝ} (hc : c ≠ 0) (j : ℕ) {x : ℝ × ℝ} (hx : 0 < x.1) :
    fderiv ℝ (tt c j) x =
      (-(tt c (j + 2) x)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        ((j : ℝ) * tt c (j - 1) x - 2 * x.1 * tt c (j + 1) x) •
          ContinuousLinearMap.snd ℝ ℝ ℝ :=
  (hasFDerivAt_tt hc j hx).fderiv

/-- Every `T_j` is `C^k` on `u > 0`. -/
theorem contDiffOn_tt {c : ℝ} (hc : c ≠ 0) :
    ∀ k : ℕ, ∀ j : ℕ, ContDiffOn ℝ (k : WithTop ℕ∞) (tt c j) {x : ℝ × ℝ | 0 < x.1} := by
  have hU : IsOpen {x : ℝ × ℝ | 0 < x.1} := isOpen_lt continuous_const continuous_fst
  intro k
  induction k with
  | zero =>
    intro j
    have : DifferentiableOn ℝ (tt c j) {x : ℝ × ℝ | 0 < x.1} := fun x hx =>
      (hasFDerivAt_tt hc j hx).differentiableAt.differentiableWithinAt
    simpa using this.continuousOn
  | succ k ih =>
    intro j
    have e : (((k + 1 : ℕ) : WithTop ℕ∞)) = (k : WithTop ℕ∞) + 1 := by push_cast; rfl
    rw [e, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun x hx => (hasFDerivAt_tt hc j hx).differentiableAt.differentiableWithinAt,
      fun h => absurd h (by simp), ?_⟩
    have hD : ContDiffOn ℝ (k : WithTop ℕ∞) (fun x : ℝ × ℝ =>
        (-(tt c (j + 2) x)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
          ((j : ℝ) * tt c (j - 1) x - 2 * x.1 * tt c (j + 1) x) •
            ContinuousLinearMap.snd ℝ ℝ ℝ) {x : ℝ × ℝ | 0 < x.1} := by
      refine ContDiffOn.add ((ih (j + 2)).neg.smul_const (ContinuousLinearMap.fst ℝ ℝ ℝ)) ?_
      refine ContDiffOn.smul_const ?_ (ContinuousLinearMap.snd ℝ ℝ ℝ)
      have hf : ContDiffOn ℝ (k : WithTop ℕ∞) (fun x : ℝ × ℝ => 2 * x.1)
          {x : ℝ × ℝ | 0 < x.1} := by fun_prop
      exact (contDiffOn_const.mul (ih (j - 1))).sub (hf.mul (ih (j + 1)))
    exact hD.congr fun x hx => fderiv_tt hc j hx

theorem contDiffOn_tt_infty {c : ℝ} (hc : c ≠ 0) (j : ℕ) :
    ContDiffOn ℝ ∞ (tt c j) {x : ℝ × ℝ | 0 < x.1} :=
  contDiffOn_infty.2 fun k => contDiffOn_tt hc k j

/-- Reparametrisation `x = (s,q) ↦ (u,q)`, `u = (4(1+νs))⁻¹`. -/
theorem contDiffOn_thetaChange {ν : ℝ} (hν : 0 < ν) :
    ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => ((4 * (1 + ν * x.1))⁻¹, x.2)) (Ioi 0 ×ˢ univ) := by
  refine ContDiffOn.prodMk ?_ (by fun_prop)
  refine ContDiffOn.inv (by fun_prop) fun x hx => ?_
  have : 0 < x.1 := hx.1
  nlinarith

theorem mapsTo_thetaChange {ν : ℝ} (hν : 0 < ν) :
    MapsTo (fun x : ℝ × ℝ => ((4 * (1 + ν * x.1))⁻¹, x.2)) (Ioi 0 ×ˢ univ)
      {x : ℝ × ℝ | 0 < x.1} := by
  intro x hx
  have : 0 < x.1 := hx.1
  show 0 < (4 * (1 + ν * x.1))⁻¹
  positivity

theorem thetaSum0_eq_tt (ν c : ℝ) (x : ℝ × ℝ) :
    thetaSum0 ν c x = tt c 0 ((4 * (1 + ν * x.1))⁻¹, x.2) := by
  unfold thetaSum0 tt ttTerm
  refine tsum_congr fun n => ?_
  simp only [pow_zero, one_mul]
  congr 1; ring

theorem thetaSum1_eq_tt (ν c : ℝ) (x : ℝ × ℝ) :
    thetaSum1 ν c x = tt c 1 ((4 * (1 + ν * x.1))⁻¹, x.2) := by
  unfold thetaSum1 tt ttTerm
  refine tsum_congr fun n => ?_
  simp only [pow_one]
  congr 2; ring

/-- `ThetaSmooth0` (SP 2205). -/
theorem thetaSmooth0 : ThetaSmooth0 := by
  intro ν c hν hc
  have := (contDiffOn_tt_infty hc.ne' 0).comp (contDiffOn_thetaChange hν) (mapsTo_thetaChange hν)
  exact this.congr fun x _ => thetaSum0_eq_tt ν c x

/-- `ThetaSmooth1` (SP 2205). -/
theorem thetaSmooth1 : ThetaSmooth1 := by
  intro ν c hν hc
  have := (contDiffOn_tt_infty hc.ne' 1).comp (contDiffOn_thetaChange hν) (mapsTo_thetaChange hν)
  exact this.congr fun x _ => thetaSum1_eq_tt ν c x

/-- `VcSmooth` (SP 2205), unconditionally. -/
theorem vcSmooth_unconditional : VcSmooth := vcSmooth_of_theta thetaSmooth0 thetaSmooth1

end UnforcedLeray.Short.IIb
