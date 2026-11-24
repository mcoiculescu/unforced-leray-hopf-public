import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_5
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# `hardySmooth`: the Hardy inequality for smooth compactly supported fields

Source `the November 2 reference manuscript` lines 1351-1362.

Proof: for `ε > 0` the field `V = y / (|y|² + ε)` has divergence `W_ε = 3h - 2|y|²h²` with
`h = (|y|² + ε)⁻¹`. Integrating `|φ|² W_ε` by parts against `C_c^∞` fields and absorbing the
cross term gives `∫ |φ|² W_ε ≤ 4 ∑ⱼ ∫ |∂ⱼφ|²`. Letting `ε → 0` (Fatou, `W_ε → 1/|y|²`)
gives the Hardy inequality with constant `4`, with no singularity at the origin.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open UnforcedLeray.PhaseSpace

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `h ε y = (|y|² + ε)⁻¹`. -/
def hsH (ε : ℝ) (y : Space) : ℝ := (‖y‖ ^ 2 + ε)⁻¹

/-- `V_j = y_j h`, the `j`-th component of `y / (|y|² + ε)`. -/
def hsV (ε : ℝ) (j : Fin 3) (y : Space) : ℝ := y j * hsH ε y

/-- `W = div V = 3h - 2 |y|² h²`. -/
def hsW (ε : ℝ) (y : Space) : ℝ := 3 * hsH ε y - 2 * ‖y‖ ^ 2 * hsH ε y ^ 2

lemma hs_den_pos {ε : ℝ} (hε : 0 < ε) (y : Space) : 0 < ‖y‖ ^ 2 + ε := by positivity

lemma hs_hasFDerivAt_den (ε : ℝ) (y : Space) :
    HasFDerivAt (fun z : Space => ‖z‖ ^ 2 + ε) (2 • innerSL ℝ y) y :=
  (hasStrictFDerivAt_norm_sq y).hasFDerivAt.add_const ε

lemma hs_hasFDerivAt_H {ε : ℝ} (hε : 0 < ε) (y : Space) :
    HasFDerivAt (hsH ε) (-(hsH ε y) ^ 2 • (2 • innerSL ℝ y)) y := by
  have hne : ‖y‖ ^ 2 + ε ≠ 0 := (hs_den_pos hε y).ne'
  have h1 := (hasFDerivAt_inv hne).comp y (hs_hasFDerivAt_den ε y)
  refine h1.congr_fderiv ?_
  ext v
  simp [hsH, inv_pow] <;> ring

lemma hs_hasFDerivAt_V {ε : ℝ} (hε : 0 < ε) (j : Fin 3) (y : Space) :
    HasFDerivAt (hsV ε j)
      (y j • (-(hsH ε y) ^ 2 • (2 • innerSL ℝ y)) + hsH ε y • (EuclideanSpace.proj j : Space →L[ℝ] ℝ)) y := by
  have hp : HasFDerivAt (fun z : Space => z j) (EuclideanSpace.proj j : Space →L[ℝ] ℝ) y := by
    have h0 := (EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt (x := y)
    convert h0 using 1
    funext z
    simp
  exact hp.mul (hs_hasFDerivAt_H hε y)

lemma hs_continuous_H {ε : ℝ} (hε : 0 < ε) : Continuous (hsH ε) :=
  continuous_iff_continuousAt.2 fun y => (hs_hasFDerivAt_H hε y).continuousAt

lemma hs_continuous_V {ε : ℝ} (hε : 0 < ε) (j : Fin 3) : Continuous (hsV ε j) :=
  continuous_iff_continuousAt.2 fun y => (hs_hasFDerivAt_V hε j y).continuousAt

lemma hs_continuous_W {ε : ℝ} (hε : 0 < ε) : Continuous (hsW ε) := by
  unfold hsW
  have := hs_continuous_H hε
  fun_prop

lemma hs_fderiv_V_diag {ε : ℝ} (hε : 0 < ε) (j : Fin 3) (y : Space) :
    fderiv ℝ (hsV ε j) y (EuclideanSpace.single j (1 : ℝ))
      = hsH ε y - 2 * y j ^ 2 * hsH ε y ^ 2 := by
  rw [(hs_hasFDerivAt_V hε j y).fderiv]
  simp [EuclideanSpace.inner_single_right] <;> ring

lemma hs_sum_eq {ε : ℝ} (hε : 0 < ε) (y : Space) :
    hsW ε y = ∑ j : Fin 3, fderiv ℝ (hsV ε j) y (EuclideanSpace.single j (1 : ℝ)) := by
  rw [Fin.sum_univ_three, hs_fderiv_V_diag hε 0 y, hs_fderiv_V_diag hε 1 y,
    hs_fderiv_V_diag hε 2 y]
  have hn : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  unfold hsW
  rw [hn]
  ring

lemma hs_sumV {ε : ℝ} (y : Space) : ∑ j : Fin 3, hsV ε j y ^ 2 = hsH ε y ^ 2 * ‖y‖ ^ 2 := by
  simp only [hsV, mul_pow]
  rw [← Finset.sum_mul, ← EuclideanSpace.real_norm_sq_eq y]
  ring

lemma hs_key {ε : ℝ} (hε : 0 < ε) (y : Space) :
    hsH ε y ^ 2 * ‖y‖ ^ 2 ≤ hsW ε y ∧ 0 < hsW ε y := by
  have hh : hsH ε y * (‖y‖ ^ 2 + ε) = 1 := inv_mul_cancel₀ (hs_den_pos hε y).ne'
  have hpos : 0 < hsH ε y := inv_pos.2 (hs_den_pos hε y)
  have key : hsW ε y - hsH ε y ^ 2 * ‖y‖ ^ 2 = 3 * ε * hsH ε y ^ 2 := by
    unfold hsW
    linear_combination (-3 * hsH ε y) * hh
  have h3 : 0 < 3 * ε * hsH ε y ^ 2 := mul_pos (mul_pos (by norm_num) hε) (pow_pos hpos 2)
  have hT : 0 ≤ hsH ε y ^ 2 * ‖y‖ ^ 2 := by positivity
  exact ⟨by linarith, by linarith⟩

lemma hs_amgm {X A G W : ℝ} (hX : 0 ≤ X) (hA : 0 ≤ A) (hG : 0 ≤ G) (hW : 0 < W)
    (h : A ^ 2 ≤ G * W) : 2 * X * A ≤ X ^ 2 * W / 2 + 2 * G := by
  nlinarith [sq_nonneg (X * W - 2 * A), hW, h]

lemma hs_pw {X W : ℝ} (hX : 0 ≤ X) (hW : 0 < W) {a D b : Fin 3 → ℝ} (ha : ∀ j, 0 ≤ a j)
    (hD : ∀ j, |D j| ≤ 2 * X * a j) (hT : ∑ j, b j ^ 2 ≤ W) :
    -∑ j, D j * b j ≤ X ^ 2 * W / 2 + 2 * ∑ j, a j ^ 2 := by
  have h1 : -∑ j, D j * b j ≤ 2 * X * ∑ j, a j * |b j| := by
    have h2 : -∑ j, D j * b j ≤ |∑ j, D j * b j| := neg_le_abs _
    have h3 : |∑ j, D j * b j| ≤ ∑ j, |D j * b j| := Finset.abs_sum_le_sum_abs _ _
    have h4 : ∑ j, |D j * b j| ≤ ∑ j, 2 * X * (a j * |b j|) := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      have := mul_le_mul_of_nonneg_right (hD j) (abs_nonneg (b j))
      linarith
    have h5 : ∑ j, 2 * X * (a j * |b j|) = 2 * X * ∑ j, a j * |b j| := by
      rw [Finset.mul_sum]
    linarith
  have h6 : (∑ j, a j * |b j|) ^ 2 ≤ (∑ j, a j ^ 2) * ∑ j, b j ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a (fun j => |b j|)
    simpa [sq_abs] using this
  have hG : 0 ≤ ∑ j, a j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have h7 : (∑ j, a j * |b j|) ^ 2 ≤ (∑ j, a j ^ 2) * W :=
    h6.trans (mul_le_mul_of_nonneg_left hT hG)
  have hA : 0 ≤ ∑ j, a j * |b j| := Finset.sum_nonneg fun j _ => mul_nonneg (ha j) (abs_nonneg _)
  have h8 := hs_amgm hX hA hG hW h7
  linarith

/-- The componentwise derivative of `V_j` is continuous (explicit formula). -/
lemma hs_int_DV {Φ : Space → ℝ} (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hc : HasCompactSupport Φ) {ε : ℝ} (hε : 0 < ε) (j : Fin 3) :
    Integrable (fun y => fderiv ℝ Φ y (EuclideanSpace.single j (1 : ℝ)) * hsV ε j y) := by
  have hD : Continuous (fun y => fderiv ℝ Φ y (EuclideanSpace.single j (1 : ℝ))) :=
    (hΦ.continuous_fderiv (by simp)).clm_apply continuous_const
  exact Continuous.integrable_of_hasCompactSupport (hD.mul (hs_continuous_V hε j))
    (hc.fderiv_apply ℝ (EuclideanSpace.single j (1 : ℝ))).mul_right

/-- Integration by parts for `∫ Φ W_ε` against `V_ε`. -/
lemma hs_ibp {Φ : Space → ℝ} (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hc : HasCompactSupport Φ) {ε : ℝ} (hε : 0 < ε) :
    ∫ y, Φ y * hsW ε y
      = -∫ y, ∑ j : Fin 3, fderiv ℝ Φ y (EuclideanSpace.single j (1 : ℝ)) * hsV ε j y := by
  have hdiff : Differentiable ℝ Φ := hΦ.differentiable (by simp)
  have hΦc : Continuous Φ := hdiff.continuous
  have hD : ∀ j : Fin 3, Continuous (fun y => fderiv ℝ Φ y (EuclideanSpace.single j (1 : ℝ))) :=
    fun j => (hΦ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hVd : ∀ j : Fin 3, Continuous
      (fun y => fderiv ℝ (hsV ε j) y (EuclideanSpace.single j (1 : ℝ))) := by
    intro j
    have heq : (fun y => fderiv ℝ (hsV ε j) y (EuclideanSpace.single j (1 : ℝ)))
        = fun y => hsH ε y - 2 * y j ^ 2 * hsH ε y ^ 2 :=
      funext fun y => hs_fderiv_V_diag hε j y
    rw [heq]
    have hc1 : Continuous (fun y : Space => y j) := (EuclideanSpace.proj j : Space →L[ℝ] ℝ).continuous
    exact (hs_continuous_H hε).sub ((((continuous_const.mul (hc1.pow 2))).mul
      ((hs_continuous_H hε).pow 2)))
  have hint : ∀ j : Fin 3, Integrable (fun y => Φ y * fderiv ℝ (hsV ε j) y (EuclideanSpace.single j (1 : ℝ))) :=
    fun j => Continuous.integrable_of_hasCompactSupport (hΦc.mul (hVd j)) hc.mul_right
  have hibp : ∀ j : Fin 3, ∫ y, Φ y * fderiv ℝ (hsV ε j) y (EuclideanSpace.single j (1 : ℝ))
      = -∫ y, fderiv ℝ Φ y (EuclideanSpace.single j (1 : ℝ)) * hsV ε j y := fun j =>
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (hs_int_DV hΦ hc hε j) (hint j)
      (Continuous.integrable_of_hasCompactSupport (hΦc.mul (hs_continuous_V hε j)) hc.mul_right)
      (fun x _ => hdiff x) (fun x _ => (hs_hasFDerivAt_V hε j x).differentiableAt)
  calc ∫ y, Φ y * hsW ε y
      = ∫ y, ∑ j : Fin 3, Φ y * fderiv ℝ (hsV ε j) y (EuclideanSpace.single j (1 : ℝ)) := by
        simp only [hs_sum_eq hε, Finset.mul_sum]
    _ = ∑ j : Fin 3, ∫ y, Φ y * fderiv ℝ (hsV ε j) y (EuclideanSpace.single j (1 : ℝ)) :=
        integral_finsetSum _ fun j _ => hint j
    _ = ∑ j : Fin 3, -∫ y, fderiv ℝ Φ y (EuclideanSpace.single j (1 : ℝ)) * hsV ε j y :=
        Finset.sum_congr rfl fun j _ => hibp j
    _ = -∑ j : Fin 3, ∫ y, fderiv ℝ Φ y (EuclideanSpace.single j (1 : ℝ)) * hsV ε j y := by
        rw [Finset.sum_neg_distrib]
    _ = -∫ y, ∑ j : Fin 3, fderiv ℝ Φ y (EuclideanSpace.single j (1 : ℝ)) * hsV ε j y := by
        rw [integral_finsetSum _ fun j _ => hs_int_DV hΦ hc hε j]

lemma hs_fderiv_normsq (φ : Space → CVec3) (hφd : Differentiable ℝ φ) (y v : Space) :
    fderiv ℝ (fun z => ‖φ z‖ ^ 2) y v = 2 * inner ℝ (φ y) (fderiv ℝ φ y v) := by
  rw [((hφd y).hasFDerivAt.norm_sq).fderiv]
  simp

/-- Main estimate for the regularized weight. -/
lemma hs_main {φ : Space → CVec3} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hc : HasCompactSupport φ) {ε : ℝ} (hε : 0 < ε) :
    ∫ y, ‖φ y‖ ^ 2 * hsW ε y ≤
      4 * ∑ j : Fin 3, ∫ y, ‖fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := by
  have hdφ : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hΦs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => ‖φ y‖ ^ 2) := hφ.norm_sq ℝ
  have hΦc : HasCompactSupport (fun y => ‖φ y‖ ^ 2) :=
    hc.comp_left (g := fun z : CVec3 => ‖z‖ ^ 2) (by simp)
  have hDb : ∀ (y : Space) (j : Fin 3),
      |fderiv ℝ (fun z => ‖φ z‖ ^ 2) y (EuclideanSpace.single j (1 : ℝ))|
        ≤ 2 * ‖φ y‖ * ‖fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))‖ := by
    intro y j
    rw [hs_fderiv_normsq φ hdφ y, abs_mul, abs_two]
    have := abs_real_inner_le_norm (φ y) (fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ)))
    nlinarith [this]
  have hpt : ∀ y : Space,
      -∑ j : Fin 3, fderiv ℝ (fun z => ‖φ z‖ ^ 2) y (EuclideanSpace.single j (1 : ℝ)) * hsV ε j y
        ≤ 1 / 2 * (‖φ y‖ ^ 2 * hsW ε y)
          + 2 * ∑ j : Fin 3, ‖fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := by
    intro y
    have hK := (hs_key hε y)
    have hT' : ∑ j : Fin 3, hsV ε j y ^ 2 ≤ hsW ε y := by
      rw [hs_sumV]
      exact hK.1
    have := hs_pw (norm_nonneg (φ y)) hK.2 (a := fun j => ‖fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))‖)
      (fun j => norm_nonneg _) (fun j => hDb y j) hT'
    linarith
  have hDj : ∀ j : Fin 3, Continuous (fun y => ‖fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) := by
    intro j
    exact (((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).norm).pow 2
  have hDjc : ∀ j : Fin 3, HasCompactSupport (fun y => ‖fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) := by
    intro j
    exact (hc.fderiv_apply ℝ (EuclideanSpace.single j (1 : ℝ))).comp_left (g := fun z : CVec3 => ‖z‖ ^ 2) (by simp)
  have hGint : Integrable (fun y => ∑ j : Fin 3, ‖fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) := by
    apply integrable_finsetSum
    intro j _
    refine Continuous.integrable_of_hasCompactSupport (hDj j) (hDjc j)
  have hΦW : Integrable (fun y => ‖φ y‖ ^ 2 * hsW ε y) :=
    Continuous.integrable_of_hasCompactSupport
      ((hΦs.continuous).mul (hs_continuous_W hε)) hΦc.mul_right
  have hPint : Integrable (fun y => -∑ j : Fin 3,
      fderiv ℝ (fun z => ‖φ z‖ ^ 2) y (EuclideanSpace.single j (1 : ℝ)) * hsV ε j y) := by
    apply Integrable.neg
    apply integrable_finsetSum
    intro j _
    exact hs_int_DV hΦs hΦc hε j
  have hRint : Integrable (fun y => 1 / 2 * (‖φ y‖ ^ 2 * hsW ε y)
      + 2 * ∑ j : Fin 3, ‖fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) :=
    (hΦW.const_mul _).add (hGint.const_mul _)
  have hmono := integral_mono hPint hRint hpt
  have hI := hs_ibp hΦs hΦc hε
  rw [integral_neg, ← hI] at hmono
  have hDji : ∀ j : Fin 3, Integrable (fun y => ‖fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) :=
    fun j => Continuous.integrable_of_hasCompactSupport (hDj j) (hDjc j)
  rw [integral_add (hΦW.const_mul _) (hGint.const_mul _), integral_const_mul,
    integral_const_mul, integral_finsetSum _ fun j _ => hDji j] at hmono
  have hsum : (∑ j : Fin 3, ∫ y, ‖fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) ≥ 0 :=
    Finset.sum_nonneg fun j _ => integral_nonneg fun y => sq_nonneg _
  linarith

lemma hs_enorm_sq {E : Type*} [NormedAddCommGroup E] (x : E) :
    ‖x‖ₑ ^ 2 = ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

lemma hs_intW {φ : Space → CVec3} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hc : HasCompactSupport φ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun y => ‖φ y‖ ^ 2 * hsW ε y) := by
  have hΦs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => ‖φ y‖ ^ 2) := hφ.norm_sq ℝ
  have hΦc : HasCompactSupport (fun y => ‖φ y‖ ^ 2) :=
    hc.comp_left (g := fun z : CVec3 => ‖z‖ ^ 2) (by simp)
  exact Continuous.integrable_of_hasCompactSupport
    ((hΦs.continuous).mul (hs_continuous_W hε)) hΦc.mul_right

/-- The `ENNReal` bound for each regularization parameter. -/
lemma hs_lintegral_bound {φ : Space → CVec3} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hc : HasCompactSupport φ) {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ y, ‖φ y‖ₑ ^ 2 * ENNReal.ofReal (hsW ε y)
      ≤ ENNReal.ofReal (4 * ∑ j : Fin 3, ∫ y, ‖fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) := by
  have hnn : ∀ y, 0 ≤ ‖φ y‖ ^ 2 * hsW ε y := fun y => mul_nonneg (sq_nonneg _) (hs_key hε y).2.le
  have hconv : ∀ y, ‖φ y‖ₑ ^ 2 * ENNReal.ofReal (hsW ε y) = ENNReal.ofReal (‖φ y‖ ^ 2 * hsW ε y) := by
    intro y
    rw [ENNReal.ofReal_mul (sq_nonneg _), hs_enorm_sq]
  rw [lintegral_congr hconv, ← ofReal_integral_eq_lintegral_ofReal (hs_intW hφ hc hε)
    (Filter.Eventually.of_forall hnn)]
  exact ENNReal.ofReal_le_ofReal (hs_main hφ hc hε)

theorem hardySmooth : HardySmooth := by
  intro φ hφ hc
  have hDji : ∀ j : Fin 3, Integrable
      (fun y => ‖fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) := by
    intro j
    have hD : Continuous (fun y => fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))) :=
      (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hDc : HasCompactSupport (fun y => fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))) :=
      hc.fderiv_apply ℝ (EuclideanSpace.single j (1 : ℝ))
    exact Continuous.integrable_of_hasCompactSupport (hD.norm.pow 2)
      (hDc.comp_left (g := fun z : CVec3 => ‖z‖ ^ 2) (by simp))
  have hj : ∀ j : Fin 3, ∫⁻ y, ‖fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))‖ₑ ^ 2
      = ENNReal.ofReal (∫ y, ‖fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) := by
    intro j
    rw [lintegral_congr (fun y => hs_enorm_sq _),
      ofReal_integral_eq_lintegral_ofReal (hDji j) (Filter.Eventually.of_forall fun y => sq_nonneg _)]
  have hRHS : 4 * ∑ j : Fin 3, ∫⁻ y, ‖fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))‖ₑ ^ 2
      = ENNReal.ofReal (4 * ∑ j : Fin 3, ∫ y, ‖fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_sum_of_nonneg (fun j _ => integral_nonneg fun y => sq_nonneg _)]
    rw [Finset.sum_congr rfl (fun j _ => hj j)]
  -- the Fatou family
  let F : ℕ → Space → ℝ≥0∞ := fun n y =>
    ‖φ y‖ₑ ^ 2 * ENNReal.ofReal (hsW (1 / ((n : ℝ) + 1)) y)
  have hFm : ∀ n, Measurable (F n) := by
    intro n
    have h1 : Measurable (fun y => ‖φ y‖ₑ ^ 2) :=
      (hφ.continuous.enorm.measurable).pow_const 2
    have h2 : Continuous (fun y => ENNReal.ofReal (hsW (1 / ((n : ℝ) + 1)) y)) :=
      ENNReal.continuous_ofReal.comp (hs_continuous_W (ε := 1 / ((n : ℝ) + 1)) (by positivity))
    exact h1.mul h2.measurable
  have hlim_val : ∀ y : Space, y ≠ 0 →
      Tendsto (fun n : ℕ => F n y) atTop
        (𝓝 (‖φ y‖ₑ ^ 2 * ENNReal.ofReal (1 / ‖y‖ ^ 2))) := by
    intro y hy
    have hs : 0 < ‖y‖ ^ 2 := by positivity
    have hne : ‖y‖ ^ 2 + 0 ≠ 0 := by simpa using hs.ne'
    have hc0 : ContinuousAt (fun ε : ℝ => (‖y‖ ^ 2 + ε)⁻¹) 0 :=
      ContinuousAt.inv₀ (by fun_prop) hne
    have hg : ContinuousAt (fun ε : ℝ => 3 * (‖y‖ ^ 2 + ε)⁻¹
        - 2 * ‖y‖ ^ 2 * ((‖y‖ ^ 2 + ε)⁻¹) ^ 2) 0 :=
      (continuousAt_const.mul hc0).sub (continuousAt_const.mul (hc0.pow 2))
    have hR : Tendsto (fun n : ℕ => hsW (1 / ((n : ℝ) + 1)) y) atTop (𝓝 (1 / ‖y‖ ^ 2)) := by
      have h2 := hg.tendsto.comp tendsto_one_div_add_atTop_nhds_zero_nat
      have hval : 3 * (‖y‖ ^ 2 + 0)⁻¹ - 2 * ‖y‖ ^ 2 * ((‖y‖ ^ 2 + 0)⁻¹) ^ 2 = 1 / ‖y‖ ^ 2 := by
        have hs' : ‖y‖ ^ 2 ≠ 0 := hs.ne'
        field_simp
        ring
      rw [hval] at h2
      exact h2
    have hpos : ENNReal.ofReal (1 / ‖y‖ ^ 2) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
    exact ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal hR) (Or.inl hpos)
  have hident : ∀ y : Space, y ≠ 0 →
      ‖φ y‖ₑ ^ 2 / ‖y‖ₑ ^ 2 = ‖φ y‖ₑ ^ 2 * ENNReal.ofReal (1 / ‖y‖ ^ 2) := by
    intro y hy
    have hs : 0 < ‖y‖ ^ 2 := by positivity
    rw [div_eq_mul_inv, hs_enorm_sq y, one_div, ENNReal.ofReal_inv_of_pos hs]
  have hne0 : ∀ᵐ y : Space, y ≠ 0 := by
    have : (volume : Measure Space) {0} = 0 := measure_singleton 0
    rw [ae_iff]
    simpa using this
  have hfin : ∀ᵐ y : Space, ‖φ y‖ₑ ^ 2 / ‖y‖ₑ ^ 2 ≤ liminf (fun n => F n y) atTop := by
    filter_upwards [hne0] with y hy
    rw [(hlim_val y hy).liminf_eq, hident y hy]
  calc ∫⁻ y : Space, ‖φ y‖ₑ ^ 2 / ‖y‖ₑ ^ 2
      ≤ ∫⁻ y, liminf (fun n => F n y) atTop := lintegral_mono_ae hfin
    _ ≤ liminf (fun n => ∫⁻ y, F n y) atTop := lintegral_liminf_le hFm
    _ ≤ liminf (fun _ : ℕ => ENNReal.ofReal (4 * ∑ j : Fin 3, ∫ y, ‖fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)) atTop :=
        liminf_le_liminf (Filter.Eventually.of_forall fun n =>
          hs_lintegral_bound hφ hc (by positivity))
    _ = ENNReal.ofReal (4 * ∑ j : Fin 3, ∫ y, ‖fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) :=
        liminf_const _
    _ = 4 * ∑ j : Fin 3, ∫⁻ y, ‖fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))‖ₑ ^ 2 := hRHS.symm

end UnforcedLeray.Short.PartIIIb.Concrete
