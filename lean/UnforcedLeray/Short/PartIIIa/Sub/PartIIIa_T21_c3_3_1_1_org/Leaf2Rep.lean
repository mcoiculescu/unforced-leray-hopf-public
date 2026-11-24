import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.DuhamelSplit
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2Dual
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2Duality
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2WeakEq
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2Regular
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf4
import UnforcedLeray.Lib.Kernels.PlanarBS.P.Infra.ConvMinkowski.Minkowski
import UnforcedLeray.Short.PartI.Sub.PartI_T20

/-!
# `PartIII-a:T21/c3/3/1/1/2/2`: `ComplDuhamelRep`

Source of record: `the November 2 reference manuscript` (SP), lines 2905-2925,
2937-2958.

Assembles the mild Duhamel representation `ComplDuhamelRep` of the moving complement
`W⊥ = compl F w` from `complForcingMeasurable`, `complSourceRegular`, `freeMovingDuality`,
`complWeakEq`, Fubini on `(t₁, s] × cell (dd ν s)`, and `dualUniq`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub ComplCouplingSub PerturbDuhamelSub

namespace ComplFreeRateSub

namespace Leaf2RepAux

/-! ### 1. Time-local weighted train bounds `LadTrainBdd` for `0 < ν` and `1 ≤ c` -/

private theorem nu_le_one_of_theta {ν b r : ℝ} (hν : 0 < ν) (hb : 1 ≤ b) (hr : 0 ≤ r)
    (hθ : b ≤ clockTheta ν r) : ν ≤ 1 := by
  have ha1 : 1 ≤ clockA ν r := one_le_clockA hν.le hr
  have hθ1 : 1 ≤ clockTheta ν r := hb.trans hθ
  have hle : clockTheta ν r ≤ ν⁻¹ := by
    unfold clockTheta
    exact inv_anti₀ hν (le_mul_of_one_le_right hν.le ha1)
  have h1 : (1 : ℝ) ≤ ν⁻¹ := hθ1.trans hle
  rw [← inv_inv ν]
  exact inv_le_one_of_one_le₀ h1

private theorem dd_ge_one_of_theta {ν b r : ℝ} (hν : 0 < ν) (hb : 1 ≤ b) (hr : 0 ≤ r)
    (hθ : b ≤ clockTheta ν r) : 1 ≤ dd ν r := by
  have ha1 : 1 ≤ clockA ν r := one_le_clockA hν.le hr
  have ha0 : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one ha1
  have hν1 : ν ≤ 1 := nu_le_one_of_theta hν hb hr hθ
  have hsq_le : Real.sqrt (clockA ν r) ≤ clockA ν r := by
    calc Real.sqrt (clockA ν r)
        ≤ Real.sqrt (clockA ν r * clockA ν r) :=
          Real.sqrt_le_sqrt (le_mul_of_one_le_right ha0.le ha1)
      _ = clockA ν r := Real.sqrt_mul_self ha0.le
  have htheta_le : clockTheta ν r ≤ ν⁻¹ * clockTheta ν r :=
    le_mul_of_one_le_left (by unfold clockTheta; positivity) ((one_le_inv₀ hν).mpr hν1)
  have hcl : ν⁻¹ * clockTheta ν r ≤ dd ν r := by
    unfold dd cellLen clockTheta
    have hpow : ν ^ (-2 : ℝ) = ν⁻¹ * ν⁻¹ := by
      rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hν.le, Real.rpow_natCast, sq,
        mul_inv]
    rw [hpow, div_eq_mul_inv, mul_inv, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (inv_anti₀ (Real.sqrt_pos.2 ha0) hsq_le) (inv_nonneg.2 hν.le))
      (inv_nonneg.2 hν.le)
  exact (hb.trans hθ).trans (htheta_le.trans hcl)

/-- Initial vorticity tilt bound valid for all `1 ≤ c`. -/
private theorem gaussSupersol_datum_le_one_le {ν c : ℝ} (hc1 : 1 ≤ c)
    (tr : UnforcedLeray.B0140.TrainSol ν c) (K_v lam τ : ℝ) (hτ : τ ^ 2 = 1)
    (z : UnforcedLeray.Cyl.Plane) :
    |UnforcedLeray.Cyl.curl (tr.v 0) z| ≤ PartI.gaussSupersol 80 K_v ν lam τ 0 z := by
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  rw [UnforcedLeray.B0169.curl_train_initial tr.isTrain hc0.ne' z]
  set f : ℤ → ℝ := fun n => Real.exp (-(z.1 - (n : ℝ) * c) ^ 2 / 8)
  set N : ℤ := ⌈z.1 / c⌉
  have hNy : z.1 ≤ (N : ℝ) * c := (div_le_iff₀ hc0).1 (Int.le_ceil (z.1 / c))
  have hNy' : ((N : ℝ) - 1) * c < z.1 := by
    have h := Int.ceil_lt_add_one (z.1 / c)
    rwa [← sub_lt_iff_lt_add, lt_div_iff₀ hc0] at h
  have hkey : ∀ (x : ℝ) (k : ℕ), (k : ℝ) * c ≤ |z.1 - x| →
      Real.exp (-(z.1 - x) ^ 2 / 8) ≤ Real.exp (-(1 / 8 : ℝ) * (k : ℝ)) := by
    intro x k hk
    refine Real.exp_le_exp.2 ?_
    have hsq : ((k : ℝ) * c) ^ 2 ≤ (z.1 - x) ^ 2 := by
      rw [← sq_abs (z.1 - x)]
      exact pow_le_pow_left₀ (by positivity) hk 2
    have hkc : (k : ℝ) ≤ ((k : ℝ) * c) ^ 2 := by
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · simp
      · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk0
        have hkc1 : (k : ℝ) ≤ (k : ℝ) * c := le_mul_of_one_le_right (by positivity) hc1
        nlinarith
    linarith
  have hshift : Summable (fun n : ℤ => f (N + n)) ∧
      ∑' n : ℤ, f (N + n) ≤ 2 * ∑' k : ℕ, Real.exp (-(1 / 8 : ℝ) * (k : ℝ)) := by
    refine UnforcedLeray.Gaussian.tsum_int_le_of_le_two_sides
      (fun _ => (Real.exp_pos _).le)
      (UnforcedLeray.Gaussian.summable_exp_neg_mul_nat (by norm_num))
      (fun k => ?_) (fun k => ?_)
    · refine hkey _ k ?_
      push_cast
      have h1 : (k : ℝ) * c ≤ ((N : ℝ) + (k : ℝ)) * c - z.1 := by nlinarith
      rw [abs_sub_comm, abs_of_nonneg (by nlinarith [Nat.cast_nonneg (α := ℝ) k])]
      exact h1
    · refine hkey _ k ?_
      push_cast
      have hkc0 : (0 : ℝ) ≤ (k : ℝ) * c := by positivity
      have h1 : (k : ℝ) * c ≤ z.1 - ((N : ℝ) + -((k : ℝ) + 1)) * c := by nlinarith
      rw [abs_of_nonneg (by linarith)]
      exact h1
  have hsum_f : Summable f :=
    (hshift.1.comp_injective (add_right_injective (-N))).congr fun n => by simp
  have htsum_f : ∑' n : ℤ, f n ≤ 18 := by
    have heq : ∑' n : ℤ, f n = ∑' n : ℤ, f (N + n) := ((Equiv.addLeft N).tsum_eq f).symm
    rw [heq]
    refine hshift.2.trans ?_
    rw [UnforcedLeray.Gaussian.tsum_exp_neg_mul_nat (by norm_num)]
    have hinv := UnforcedLeray.Gaussian.inv_one_sub_exp_neg_le (β := (1 / 8 : ℝ)) (by norm_num)
    linarith
  have hpt : ∀ n : ℤ,
      ‖UnforcedLeray.GaussianVortex.vorticity (z.1 - (n : ℝ) * c, z.2)‖ ≤
        (4 * Real.exp (-z.2 ^ 2 / 8)) * f n := by
    intro n
    rw [Real.norm_eq_abs]
    refine (UnforcedLeray.B0169.abs_vorticity_le (z.1 - (n : ℝ) * c, z.2)).trans (le_of_eq ?_)
    dsimp only [f]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hmaj : Summable (fun n : ℤ => (4 * Real.exp (-z.2 ^ 2 / 8)) * f n) :=
    hsum_f.mul_left _
  have hsum_v : Summable (fun n : ℤ =>
      ‖UnforcedLeray.GaussianVortex.vorticity (z.1 - (n : ℝ) * c, z.2)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt hmaj
  have hinit : |UnforcedLeray.B0169.initialVorticity c z| ≤ 80 * Real.exp (-z.2 ^ 2 / 8) := by
    rw [UnforcedLeray.B0169.initialVorticity_apply, ← Real.norm_eq_abs]
    calc ‖∑' n : ℤ, UnforcedLeray.GaussianVortex.vorticity (z.1 - (n : ℝ) * c, z.2)‖
        ≤ ∑' n : ℤ, ‖UnforcedLeray.GaussianVortex.vorticity (z.1 - (n : ℝ) * c, z.2)‖ :=
          norm_tsum_le_tsum_norm hsum_v
      _ ≤ ∑' n : ℤ, (4 * Real.exp (-z.2 ^ 2 / 8)) * f n :=
          hsum_v.tsum_le_tsum hpt hmaj
      _ = (4 * Real.exp (-z.2 ^ 2 / 8)) * ∑' n : ℤ, f n := tsum_mul_left
      _ ≤ (4 * Real.exp (-z.2 ^ 2 / 8)) * 18 :=
          mul_le_mul_of_nonneg_left htsum_f (by positivity)
      _ ≤ 80 * Real.exp (-z.2 ^ 2 / 8) := by
          nlinarith [Real.exp_pos (-z.2 ^ 2 / 8)]
  have htilt := UnforcedLeray.B0169.exp_neg_sq_div_eight_le_tilt z.2 (lam * τ)
  have hτ2 : (lam * τ) ^ 2 = lam ^ 2 := by
    calc (lam * τ) ^ 2 = lam ^ 2 * τ ^ 2 := by ring
      _ = lam ^ 2 * 1 := by rw [hτ]
      _ = lam ^ 2 := mul_one _
  rw [hτ2] at htilt
  refine hinit.trans ((mul_le_mul_of_nonneg_left htilt (by norm_num)).trans (le_of_eq ?_))
  rw [PartI.gaussSupersol_eq_exp, PartI.driftPrimitive_zero]
  congr 2
  ring

/-- Gaussian transverse tail of `Cyl.curl (tr.v ρ)` on `[0, S]` for any `0 < ν`, `1 ≤ c`, and
`IsBUCTrain tr`. -/
private theorem curl_gaussian_tail_on_Icc {ν c S : ℝ} (hν : 0 < ν) (hc1 : 1 ≤ c) (hS : 0 ≤ S)
    (tr : UnforcedLeray.B0140.TrainSol ν c) (htr : PartI.IsBUCTrain tr) :
    ∃ K_v : ℝ, 0 < K_v ∧
      ∀ ρ ∈ Icc (0 : ℝ) S, ∀ z : UnforcedLeray.Cyl.Plane,
        |UnforcedLeray.Cyl.curl (tr.v ρ) z| ≤
          80 * Real.exp (-((1 / 4 : ℝ) * (max (|z.2| - 2 * K_v / ν) 0) ^ 2 / (2 + ν * S))) := by
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  let T : ℝ := S + 1
  have hT : 0 < T := by dsimp [T]; linarith
  have cl := PartI.trainSol_isClassicalOn tr T
  obtain ⟨hcont, hC2, ⟨Mw, hMw⟩, hper⟩ :=
    PartI.curlRegularity c T tr.v hc0 hT cl.smooth_v cl.periodic_v (htr T hT.le)
  obtain ⟨β0, hβ0⟩ := PartI.vfm_sup_bound (htr T hT.le)
  have hwT_pos : 0 < UnforcedLeray.Train.width ν T := by
    unfold UnforcedLeray.Train.width
    positivity
  let K_v : ℝ := (|β0| + 1) * (UnforcedLeray.Train.width ν T) ^ (3 / 2 : ℝ)
  have hK_v : 0 < K_v := by dsimp [K_v]; positivity
  refine ⟨K_v, hK_v, fun ρ hρ z => ?_⟩
  have hop : ∀ r ∈ Ioo (0 : ℝ) T, ∀ w : UnforcedLeray.Cyl.Plane,
      PartI.vorticityOp ν tr.v (fun t u => UnforcedLeray.Cyl.curl (tr.v t) u) r w = 0 :=
    fun r hr w => PartI.localVorticityEquation ν c T tr.v tr.p hν hc1 hT cl r hr w
  have hb : ∀ r ∈ Icc (0 : ℝ) T, ∀ w : UnforcedLeray.Cyl.Plane, ‖tr.v r w‖ ≤ |β0| :=
    fun r hr w => (hβ0 r hr w).trans (le_abs_self β0)
  have hb1 : ∀ r ∈ Icc (0 : ℝ) T, ∀ w : UnforcedLeray.Cyl.Plane,
      |tr.v r w 1| ≤ K_v * (UnforcedLeray.Train.width ν r) ^ (-(3 / 2 : ℝ)) := by
    intro r hr w
    have hwr_pos : 0 < UnforcedLeray.Train.width ν r := by
      unfold UnforcedLeray.Train.width
      have : 0 ≤ ν * r := mul_nonneg hν.le hr.1
      linarith
    have hwr_le : UnforcedLeray.Train.width ν r ≤ UnforcedLeray.Train.width ν T := by
      unfold UnforcedLeray.Train.width
      nlinarith [hr.2]
    have hrpow_le : (UnforcedLeray.Train.width ν T) ^ (-(3 / 2 : ℝ)) ≤
        (UnforcedLeray.Train.width ν r) ^ (-(3 / 2 : ℝ)) := by
      rw [Real.rpow_neg hwT_pos.le, Real.rpow_neg hwr_pos.le]
      exact inv_anti₀ (Real.rpow_pos_of_pos hwr_pos _)
        (Real.rpow_le_rpow hwr_pos.le hwr_le (by norm_num))
    have hprod1 : (UnforcedLeray.Train.width ν T) ^ (3 / 2 : ℝ) *
        (UnforcedLeray.Train.width ν T) ^ (-(3 / 2 : ℝ)) = 1 := by
      rw [← Real.rpow_add hwT_pos, add_neg_cancel, Real.rpow_zero]
    have hv1 : |tr.v r w 1| ≤ |β0| + 1 := by
      have h1 : |tr.v r w 1| ≤ ‖tr.v r w‖ := by simpa using PiLp.norm_apply_le (tr.v r w) 1
      linarith [hb r hr w]
    calc |tr.v r w 1|
        ≤ (|β0| + 1) * 1 := by linarith
      _ = K_v * (UnforcedLeray.Train.width ν T) ^ (-(3 / 2 : ℝ)) := by
          dsimp [K_v]; rw [mul_assoc, hprod1]
      _ ≤ K_v * (UnforcedLeray.Train.width ν r) ^ (-(3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hrpow_le hK_v.le
  let d : ℝ := max (|z.2| - 2 * K_v / ν) 0
  have hd_nn : 0 ≤ d := le_max_right _ _
  have hden_pos : 0 < 2 + ν * S := by nlinarith
  let lam : ℝ := d / (2 * (2 + ν * S))
  have hlam_nn : 0 ≤ lam := div_nonneg hd_nn (by positivity)
  obtain ⟨τ, hτ_sq, hτ_z⟩ : ∃ τ : ℝ, τ ^ 2 = 1 ∧ τ * z.2 = |z.2| := by
    rcases le_total 0 z.2 with hz | hz
    · exact ⟨1, by norm_num, by rw [one_mul, abs_of_nonneg hz]⟩
    · refine ⟨-1, by norm_num, ?_⟩
      rw [abs_of_nonpos hz]
      ring
  have hG0 : ∀ w : UnforcedLeray.Cyl.Plane,
      |UnforcedLeray.Cyl.curl (tr.v 0) w| ≤ PartI.gaussSupersol 80 K_v ν lam τ 0 w :=
    gaussSupersol_datum_le_one_le hc1 tr K_v lam τ hτ_sq
  let K_bar : ℝ := |β0| + ν + 1
  have hK_bar : |β0| + ν < K_bar := by dsimp [K_bar]; linarith
  have hρ_Ico : ρ ∈ Ico (0 : ℝ) T := ⟨hρ.1, by dsimp [T]; linarith [hρ.2]⟩
  have hlim : ∀ σ : ℝ, |σ| ≤ 1 →
      σ * UnforcedLeray.Cyl.curl (tr.v ρ) z ≤ PartI.gaussSupersol 80 K_v ν lam τ ρ z := by
    intro σ hσ
    refine PartI.linf_limit _ (PartI.gaussSupersol 80 K_v ν lam τ ρ z)
      (Real.exp (K_bar * ρ) * Real.cosh (1 * z.2))
      (mul_nonneg (Real.exp_pos _).le (Real.cosh_pos _).le) fun ε hε => ?_
    have hcore := PartI.gaussSupersol_core ν c T |β0| 80 K_v lam τ Mw K_bar tr.v
      (fun t u => UnforcedLeray.Cyl.curl (tr.v t) u) hν hc0 hT (by norm_num) hlam_nn hτ_sq
      hK_bar hb hb1 hcont hC2 hper hMw hop hG0 σ hσ ε hε ρ hρ_Ico z
    have he : PartI.coshBarrier ε K_bar 1 ρ z = ε * (Real.exp (K_bar * ρ) * Real.cosh (1 * z.2)) := by
      unfold PartI.coshBarrier
      ring
    rwa [he] at hcore
  have hcomp : |UnforcedLeray.Cyl.curl (tr.v ρ) z| ≤ PartI.gaussSupersol 80 K_v ν lam τ ρ z := by
    rw [abs_le]
    exact ⟨by linarith [hlim (-1) (by norm_num)], by linarith [hlim 1 (by norm_num)]⟩
  rw [PartI.gaussSupersol_eq_exp, hτ_z] at hcomp
  have hA_le : PartI.driftPrimitive K_v ν ρ ≤ 2 * K_v / ν :=
    PartI.driftPrimitive_le hK_v.le hν hρ.1
  have h_sub_ge : -(lam * (|z.2| - PartI.driftPrimitive K_v ν ρ)) ≤ -(lam * d) := by
    apply neg_le_neg
    by_cases hd0 : |z.2| - 2 * K_v / ν ≤ 0
    · have hd_eq0 : d = 0 := max_eq_right hd0
      have hlam_eq0 : lam = 0 := by dsimp [lam]; rw [hd_eq0, zero_div]
      rw [hlam_eq0, zero_mul, zero_mul]
    · have hd_eq : d = |z.2| - 2 * K_v / ν := max_eq_left (not_le.mp hd0).le
      exact mul_le_mul_of_nonneg_left (by linarith) hlam_nn
  have h_quad : (2 + ν * ρ) * lam ^ 2 ≤ (2 + ν * S) * lam ^ 2 :=
    mul_le_mul_of_nonneg_right (by nlinarith [hρ.2]) (sq_nonneg lam)
  have hexp_alg : -(lam * d) + (2 + ν * S) * lam ^ 2 =
      -((1 / 4 : ℝ) * d ^ 2 / (2 + ν * S)) := by
    dsimp [lam]
    have hden_ne : 2 + ν * S ≠ 0 := hden_pos.ne'
    field_simp
    ring
  calc |UnforcedLeray.Cyl.curl (tr.v ρ) z|
      ≤ 80 * Real.exp (-(lam * (|z.2| - PartI.driftPrimitive K_v ν ρ)) + (2 + ν * ρ) * lam ^ 2) :=
        hcomp
    _ ≤ 80 * Real.exp (-(lam * d) + (2 + ν * S) * lam ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (add_le_add h_sub_ge h_quad)) (by norm_num)
    _ = 80 * Real.exp (-((1 / 4 : ℝ) * d ^ 2 / (2 + ν * S))) := by rw [hexp_alg]

/-- Unconditional time-local `LadTrainBdd` for any `0 < ν`, `1 ≤ c`, and `IsBUCTrain tr`. -/
theorem ladTrainBdd_of_buc {ν c : ℝ} (hν : 0 < ν) (hc1 : 1 ≤ c)
    (tr : UnforcedLeray.B0140.TrainSol ν c) (htr : PartI.IsBUCTrain tr) (m S : ℝ) (hS : 0 ≤ S) :
    ∃ C : ℝ, LadTrainBdd tr m S C := by
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  obtain ⟨M₀, hM₀⟩ := htr.sup_bound hS
  obtain ⟨K_v, hK_v, hcurl0⟩ := curl_gaussian_tail_on_Icc hν hc1 hS tr htr
  -- Uniform bounds on second coordinate derivatives of `curl (tr.v ρ)` on `[0, S]`
  obtain ⟨M_tt1, hM_tt1⟩ := PartI.vjl_wordBoundedOn htr hS [true, true, true] 1
  obtain ⟨M_tt0, hM_tt0⟩ := PartI.vjl_wordBoundedOn htr hS [true, true, false] 0
  obtain ⟨M_ff1, hM_ff1⟩ := PartI.vjl_wordBoundedOn htr hS [false, false, true] 1
  obtain ⟨M_ff0, hM_ff0⟩ := PartI.vjl_wordBoundedOn htr hS [false, false, false] 0
  let B₂ : ℝ := |M_tt1| + |M_tt0| + |M_ff1| + |M_ff0| + 1
  have hB₂_pos : 0 < B₂ := by dsimp [B₂]; positivity
  let K_g : ℝ := 2 * K_v / ν
  have hK_g0 : 0 ≤ K_g := by dsimp [K_g]; positivity
  let D_S : ℝ := 2 + ν * S
  have hD_S : 0 < D_S := by dsimp [D_S]; nlinarith
  have hgrad_tail : ∀ ρ ∈ Icc (0 : ℝ) S, ∀ x : ℝ × ℝ, ∀ j : Fin 2,
      |B0579.pd j (UnforcedLeray.B0238.Ec tr ρ) x| ≤
        (3 * Real.sqrt (80 * B₂)) *
          Real.exp (-((1 / 8 : ℝ) * (max (|x.2| - K_g) 0) ^ 2 / D_S)) := by
    intro ρ hρ x j
    have hv_sm : ContDiff ℝ ∞ (tr.v ρ) := PartI.PartI_T20.contDiff_train_v_slice tr hρ.1
    have hg_sm : ContDiff ℝ ∞ (UnforcedLeray.Cyl.curl (tr.v ρ)) :=
      PartI.PartI_T20.contDiff_curl_of_contDiff hv_sm
    have hg_diff : Differentiable ℝ (UnforcedLeray.Cyl.curl (tr.v ρ)) :=
      hg_sm.differentiable (by simp)
    have hpoly80 : PartI.polyP 80 0 ν c = 80 := by unfold PartI.polyP; simp
    have hpolyB2 : PartI.polyP B₂ 0 ν c = B₂ := by unfold PartI.polyP; simp
    have hpolyOut : PartI.polyP (3 * Real.sqrt (80 * B₂)) (0 + 0) ν c =
        3 * Real.sqrt (80 * B₂) := by unfold PartI.polyP; simp
    have h0_bd : ∀ z : UnforcedLeray.Cyl.Plane,
        |UnforcedLeray.Cyl.curl (tr.v ρ) z| ≤
          PartI.polyP 80 0 ν c * Real.exp (-((1 / 4 : ℝ) * (max (|z.2| - K_g) 0) ^ 2 / D_S)) := by
      intro z
      rw [hpoly80]
      exact hcurl0 ρ hρ z
    fin_cases j
    · have h2_tt : ∀ z : UnforcedLeray.Cyl.Plane,
          |UnforcedLeray.B0151.derivWord [true, true] (UnforcedLeray.Cyl.curl (tr.v ρ)) z| ≤
            PartI.polyP B₂ 0 ν c := by
        intro z
        rw [hpolyB2]
        have heq := PartI.vortWord_eq tr hρ.1 [true, true] z
        unfold PartI.vortWord at heq
        rw [heq]
        have h1 := (hM_tt1 ρ hρ z).trans (le_abs_self M_tt1)
        have h0 := (hM_tt0 ρ hρ z).trans (le_abs_self M_tt0)
        calc |PartI.wordComp [true, true, true] (tr.v ρ) 1 z -
              PartI.wordComp [true, true, false] (tr.v ρ) 0 z|
            ≤ |PartI.wordComp [true, true, true] (tr.v ρ) 1 z| +
              |PartI.wordComp [true, true, false] (tr.v ρ) 0 z| := abs_sub _ _
          _ ≤ B₂ := by dsimp [B₂]; linarith [abs_nonneg M_ff1, abs_nonneg M_ff0]
      have hstep := PartI.PartI_T20.spatial_step_gaussian_tail hg_sm
        (by norm_num : (0 : ℝ) < 80) hB₂_pos (by norm_num : (0 : ℝ) < 1 / 4) hD_S hν hc0
        h0_bd true h2_tt x
      dsimp only at hstep
      have hpd0 : B0579.pd 0 (UnforcedLeray.B0238.Ec tr ρ) x =
          UnforcedLeray.B0151.derivWord [true] (UnforcedLeray.Cyl.curl (tr.v ρ)) x := by
        change fderiv ℝ (UnforcedLeray.Cyl.curl (tr.v ρ)) x (1, 0) =
          UnforcedLeray.Cyl.partialQ (UnforcedLeray.Cyl.curl (tr.v ρ)) x
        exact (UnforcedLeray.Cyl.partialQ_eq_fderiv hg_diff x).symm
      change |B0579.pd 0 (UnforcedLeray.B0238.Ec tr ρ) x| ≤ _
      rw [hpd0]
      rw [hpolyOut, show ((1 / 4 : ℝ) / 2) = (1 / 8 : ℝ) by norm_num] at hstep
      exact hstep
    · have h2_ff : ∀ z : UnforcedLeray.Cyl.Plane,
          |UnforcedLeray.B0151.derivWord [false, false] (UnforcedLeray.Cyl.curl (tr.v ρ)) z| ≤
            PartI.polyP B₂ 0 ν c := by
        intro z
        rw [hpolyB2]
        have heq := PartI.vortWord_eq tr hρ.1 [false, false] z
        unfold PartI.vortWord at heq
        rw [heq]
        have h1 := (hM_ff1 ρ hρ z).trans (le_abs_self M_ff1)
        have h0 := (hM_ff0 ρ hρ z).trans (le_abs_self M_ff0)
        calc |PartI.wordComp [false, false, true] (tr.v ρ) 1 z -
              PartI.wordComp [false, false, false] (tr.v ρ) 0 z|
            ≤ |PartI.wordComp [false, false, true] (tr.v ρ) 1 z| +
              |PartI.wordComp [false, false, false] (tr.v ρ) 0 z| := abs_sub _ _
          _ ≤ B₂ := by dsimp [B₂]; linarith [abs_nonneg M_tt1, abs_nonneg M_tt0]
      have hstep := PartI.PartI_T20.spatial_step_gaussian_tail hg_sm
        (by norm_num : (0 : ℝ) < 80) hB₂_pos (by norm_num : (0 : ℝ) < 1 / 4) hD_S hν hc0
        h0_bd false h2_ff x
      dsimp only at hstep
      have hpd1 : B0579.pd 1 (UnforcedLeray.B0238.Ec tr ρ) x =
          UnforcedLeray.B0151.derivWord [false] (UnforcedLeray.Cyl.curl (tr.v ρ)) x := by
        change fderiv ℝ (UnforcedLeray.Cyl.curl (tr.v ρ)) x (0, 1) =
          UnforcedLeray.Cyl.partialEta (UnforcedLeray.Cyl.curl (tr.v ρ)) x
        exact (UnforcedLeray.Cyl.partialEta_eq_fderiv hg_diff x).symm
      change |B0579.pd 1 (UnforcedLeray.B0238.Ec tr ρ) x| ≤ _
      rw [hpd1]
      rw [hpolyOut, show ((1 / 4 : ℝ) / 2) = (1 / 8 : ℝ) by norm_num] at hstep
      exact hstep
  -- Absorb polynomial weight `jb x ^ ((m + 2) / 2)` against shifted Gaussian
  set k : ℕ := ⌈max 0 ((m + 2) / 2)⌉₊
  let α : ℝ := (1 / 8 : ℝ) / D_S
  have hα_pos : 0 < α := by dsimp [α]; positivity
  obtain ⟨C_abs, hC_abs_pos, hC_abs⟩ := UnforcedLeray.Gaussian.rpow_mul_exp_neg_mul_sq_le
    (m := ((2 * k : ℕ) : ℝ)) (b := α) (Nat.cast_nonneg _) hα_pos
  let C_poly : ℝ := (1 + c ^ 2 / 4) ^ k * (2 + 2 * K_g ^ 2) ^ k *
    ((2 : ℝ) ^ (2 * k) * (1 + C_abs)) * (3 * Real.sqrt (80 * B₂))
  refine ⟨max M₀ C_poly, fun ρ hρ x hx => ⟨fun j => ?_, fun j => ?_⟩⟩
  · have h1 : ‖tr.v ρ x‖ ≤ M₀ := hM₀ ρ hρ x
    have h2 : ‖tr.v ρ x j‖ ≤ ‖tr.v ρ x‖ := PiLp.norm_apply_le (tr.v ρ x) j
    rw [Real.norm_eq_abs] at h2
    exact h2.trans (h1.trans (le_max_left _ _))
  · have hjb1 : 1 ≤ B0579.jb x := by
      unfold B0579.jb
      nlinarith [sq_nonneg x.1, sq_nonneg x.2]
    have hcell := TrainBddAux.jb_le_cell hx
    have hjbe : B0579.jb x ^ ((m + 2) / 2) ≤ (1 + c ^ 2 / 4) ^ k * (1 + x.2 ^ 2) ^ k := by
      have he : (m + 2) / 2 ≤ (k : ℝ) := le_trans (le_max_right _ _) (Nat.le_ceil _)
      calc B0579.jb x ^ ((m + 2) / 2)
          ≤ B0579.jb x ^ (k : ℝ) := Real.rpow_le_rpow_of_exponent_le hjb1 he
        _ = B0579.jb x ^ k := Real.rpow_natCast _ _
        _ ≤ ((1 + c ^ 2 / 4) * (1 + x.2 ^ 2)) ^ k :=
            pow_le_pow_left₀ (B0579.jb_pos x).le hcell k
        _ = (1 + c ^ 2 / 4) ^ k * (1 + x.2 ^ 2) ^ k := mul_pow _ _ _
    let d : ℝ := max (|x.2| - K_g) 0
    have hd0 : 0 ≤ d := le_max_right _ _
    have hx2_le : |x.2| ≤ K_g + d := by
      have : |x.2| - K_g ≤ d := le_max_left _ _
      linarith
    have hx2_sq : 1 + x.2 ^ 2 ≤ (2 + 2 * K_g ^ 2) * (1 + d) ^ 2 := by
      have h1 : x.2 ^ 2 ≤ (K_g + d) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hx2_le 2
      nlinarith [sq_nonneg (K_g - d), mul_nonneg hK_g0 hd0, sq_nonneg K_g, sq_nonneg d]
    have hx2_pow : (1 + x.2 ^ 2) ^ k ≤ (2 + 2 * K_g ^ 2) ^ k * (1 + d) ^ (2 * k) := by
      calc (1 + x.2 ^ 2) ^ k
          ≤ ((2 + 2 * K_g ^ 2) * (1 + d) ^ 2) ^ k := pow_le_pow_left₀ (by positivity) hx2_sq k
        _ = (2 + 2 * K_g ^ 2) ^ k * (1 + d) ^ (2 * k) := by rw [mul_pow, ← pow_mul]
    have hpow_1d : (1 + d) ^ (2 * k) ≤ (2 : ℝ) ^ (2 * k) * (1 + d ^ (2 * k)) := by
      rcases le_total d 1 with hd1 | hd1
      · have : (1 + d) ^ (2 * k) ≤ (2 : ℝ) ^ (2 * k) :=
          pow_le_pow_left₀ (by positivity) (by linarith) (2 * k)
        have : (0 : ℝ) ≤ (2 : ℝ) ^ (2 * k) * d ^ (2 * k) := by positivity
        linarith
      · have : (1 + d) ^ (2 * k) ≤ (2 * d) ^ (2 * k) :=
          pow_le_pow_left₀ (by positivity) (by linarith) (2 * k)
        rw [mul_pow] at this
        have : (0 : ℝ) ≤ (2 : ℝ) ^ (2 * k) := by positivity
        linarith
    have habs_d : (1 + d) ^ (2 * k) * Real.exp (-(α * d ^ 2)) ≤
        (2 : ℝ) ^ (2 * k) * (1 + C_abs) := by
      have hd_rpow := hC_abs d hd0
      rw [Real.rpow_natCast] at hd_rpow
      have hexp_le1 : Real.exp (-(α * d ^ 2)) ≤ 1 :=
        Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg d])
      calc (1 + d) ^ (2 * k) * Real.exp (-(α * d ^ 2))
          ≤ ((2 : ℝ) ^ (2 * k) * (1 + d ^ (2 * k))) * Real.exp (-(α * d ^ 2)) :=
            mul_le_mul_of_nonneg_right hpow_1d (Real.exp_pos _).le
        _ = (2 : ℝ) ^ (2 * k) * (Real.exp (-(α * d ^ 2)) + d ^ (2 * k) * Real.exp (-(α * d ^ 2))) := by
            ring
        _ ≤ (2 : ℝ) ^ (2 * k) * (1 + C_abs) :=
            mul_le_mul_of_nonneg_left (add_le_add hexp_le1 hd_rpow) (by positivity)
    have hgrad_x := hgrad_tail ρ hρ x j
    have hexp_eq : -((1 / 8 : ℝ) * d ^ 2 / D_S) = -(α * d ^ 2) := by
      dsimp [α]; ring
    rw [hexp_eq] at hgrad_x
    have hprod_le : B0579.jb x ^ ((m + 2) / 2) * |B0579.pd j (UnforcedLeray.B0238.Ec tr ρ) x| ≤
        C_poly := by
      calc B0579.jb x ^ ((m + 2) / 2) * |B0579.pd j (UnforcedLeray.B0238.Ec tr ρ) x|
          ≤ ((1 + c ^ 2 / 4) ^ k * ((2 + 2 * K_g ^ 2) ^ k * (1 + d) ^ (2 * k))) *
              ((3 * Real.sqrt (80 * B₂)) * Real.exp (-(α * d ^ 2))) :=
            mul_le_mul (hjbe.trans (mul_le_mul_of_nonneg_left hx2_pow (by positivity))) hgrad_x
              (abs_nonneg _) (by positivity)
        _ = (1 + c ^ 2 / 4) ^ k * (2 + 2 * K_g ^ 2) ^ k *
              ((1 + d) ^ (2 * k) * Real.exp (-(α * d ^ 2))) * (3 * Real.sqrt (80 * B₂)) := by ring
        _ ≤ C_poly := by
            dsimp [C_poly]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left habs_d (by positivity)) (by positivity)
    exact hprod_le.trans (le_max_right _ _)

/-! ### 2. Unnormalised amplitude FTC on `[t₁, t₂]` -/

open CutFTCSmooth CutFTCDual CutFTCAux ComplCouplingHeat WeakFTCSub

private theorem contDiffOn_perGram_inv_Icc
    (κ : PlanarFrameKernels) (hκ : IsSeedKernels κ)
    {ν m b K t₁ s : ℝ} (hν : 0 < ν) (_hm : 8 < m) (_hb : 1 ≤ b)
    (hF : PerFrameFacts κ ν m b K) (ht₁ : 0 ≤ t₁) (_hts : t₁ ≤ s) (hθs : b ≤ clockTheta ν s)
    (i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun r : ℝ => (perGram κ (dd ν r))⁻¹ i j) (Icc t₁ s) := by
  have hG : ∀ a' b' : Fin 2, ContDiffOn ℝ ∞ (fun d : ℝ => perGram κ d a' b') (Ici 1) :=
    perGramSmooth κ hκ
  have hdd_cd : ContDiffOn ℝ ∞ (fun r : ℝ => dd ν r) (Icc t₁ s) :=
    (contDiffOn_cellLen_clockA (ν ^ (-2 : ℝ)) hν.le).mono fun r hr => ht₁.trans hr.1
  have hdd_ge : MapsTo (fun r : ℝ => dd ν r) (Icc t₁ s) (Ici 1) := by
    intro r hr
    have hr0 : 0 ≤ r := ht₁.trans hr.1
    exact dd_ge_one_of_theta hν _hb hr0 (hθs.trans (theta_anti hν hr0 hr.2))
  have hG_r : ∀ a' b' : Fin 2, ContDiffOn ℝ ∞ (fun r : ℝ => perGram κ (dd ν r) a' b') (Icc t₁ s) :=
    fun a' b' => (hG a' b').comp hdd_cd hdd_ge
  have hdet : ContDiffOn ℝ ∞ (fun r : ℝ => (perGram κ (dd ν r)).det) (Icc t₁ s) := by
    have heq : (fun r : ℝ => (perGram κ (dd ν r)).det) =
        fun r => perGram κ (dd ν r) 0 0 * perGram κ (dd ν r) 1 1 -
          perGram κ (dd ν r) 0 1 * perGram κ (dd ν r) 1 0 := by
      funext r; exact Matrix.det_fin_two _
    rw [heq]
    exact ((hG_r 0 0).mul (hG_r 1 1)).sub ((hG_r 0 1).mul (hG_r 1 0))
  have hdet_ne : ∀ r ∈ Icc t₁ s, (perGram κ (dd ν r)).det ≠ 0 :=
    Leaf2RegularAux.perGram_det_ne_zero_of_facts κ hν ht₁ hθs hF
  have hdet_inv : ContDiffOn ℝ ∞ (fun r : ℝ => ((perGram κ (dd ν r)).det)⁻¹) (Icc t₁ s) :=
    hdet.inv hdet_ne
  fin_cases i <;> fin_cases j
  · change ContDiffOn ℝ ∞ (fun r : ℝ => (perGram κ (dd ν r))⁻¹ 0 0) (Icc t₁ s)
    have hentry : (fun r : ℝ => (perGram κ (dd ν r))⁻¹ 0 0) =
        fun r => ((perGram κ (dd ν r)).det)⁻¹ * perGram κ (dd ν r) 1 1 := by
      funext r; rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]; rfl
    rw [hentry]; exact hdet_inv.mul (hG_r 1 1)
  · change ContDiffOn ℝ ∞ (fun r : ℝ => (perGram κ (dd ν r))⁻¹ 0 1) (Icc t₁ s)
    have hentry : (fun r : ℝ => (perGram κ (dd ν r))⁻¹ 0 1) =
        fun r => ((perGram κ (dd ν r)).det)⁻¹ * (-perGram κ (dd ν r) 0 1) := by
      funext r; rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]; rfl
    rw [hentry]; exact hdet_inv.mul (hG_r 0 1).neg
  · change ContDiffOn ℝ ∞ (fun r : ℝ => (perGram κ (dd ν r))⁻¹ 1 0) (Icc t₁ s)
    have hentry : (fun r : ℝ => (perGram κ (dd ν r))⁻¹ 1 0) =
        fun r => ((perGram κ (dd ν r)).det)⁻¹ * (-perGram κ (dd ν r) 1 0) := by
      funext r; rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]; rfl
    rw [hentry]; exact hdet_inv.mul (hG_r 1 0).neg
  · change ContDiffOn ℝ ∞ (fun r : ℝ => (perGram κ (dd ν r))⁻¹ 1 1) (Icc t₁ s)
    have hentry : (fun r : ℝ => (perGram κ (dd ν r))⁻¹ 1 1) =
        fun r => ((perGram κ (dd ν r)).det)⁻¹ * perGram κ (dd ν r) 0 0 := by
      funext r; rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]; rfl
    rw [hentry]; exact hdet_inv.mul (hG_r 0 0)

private theorem contDiffOn_physFrameLam_Ico
    (κ : PlanarFrameKernels) (hκ : IsSeedKernels κ)
    {ν m b K t₁ s : ℝ} (hν : 0 < ν) (hm : 8 < m) (hb : 1 ≤ b)
    (hF : PerFrameFacts κ ν m b K) (ht₁ : 0 ≤ t₁) (hts : t₁ ≤ s) (hθs : b ≤ clockTheta ν s)
    (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => physFrameLam κ ν p.1 i p.2) (Ico t₁ s ×ˢ univ) := by
  have hLam0 := physFrameLam0Smooth κ hκ hν ht₁
  have hGinv : ∀ j : Fin 2,
      ContDiffOn ℝ ∞ (fun r : ℝ => (perGram κ (dd ν r))⁻¹ i j) (Icc t₁ s) :=
    contDiffOn_perGram_inv_Icc κ hκ hν hm hb hF ht₁ hts hθs i
  have hsub : Ico t₁ s ×ˢ (univ : Set (ℝ × ℝ)) ⊆ Ici t₁ ×ˢ univ :=
    prod_mono Ico_subset_Ici_self Subset.rfl
  have hterm : ∀ j : Fin 2,
      ContDiffOn ℝ ∞
        (fun p : ℝ × (ℝ × ℝ) =>
          (perGram κ (dd ν p.1))⁻¹ i j *
            perSum (ν ^ (-2 : ℝ)) (physAdj (clockA ν p.1) (κ.lamP j)) p.2)
        (Ico t₁ s ×ˢ univ) := fun j =>
    ((hGinv j).comp contDiff_fst.contDiffOn (fun p hp => Ico_subset_Icc_self hp.1)).mul
      ((hLam0 j).mono hsub)
  refine ((hterm 0).add (hterm 1)).congr fun p hp => ?_
  have hp0 : 0 ≤ p.1 := ht₁.trans hp.1.1
  rw [physFrameLam_eq_sum_perGram_inv κ ν p.1 i p.2, Fin.sum_univ_two]
  congr 1
  · rw [physFrameLam0_eq_perSum_physAdj κ hν hp0 0 p.2]
  · rw [physFrameLam0_eq_perSum_physAdj κ hν hp0 1 p.2]

private theorem perPhys_bdd_on_cell {ν t₁ s : ℝ} (hν : 0 < ν) (ht₁ : 0 ≤ t₁) (hts : t₁ ≤ s)
    {L : ℝ × ℝ → ℂ} (hL : LamJetInf.Good L) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r ∈ Icc t₁ s, ∀ x ∈ B0579.cell (ν ^ (-2 : ℝ)),
      ‖LamJetInf.perPhys ν (ν ^ (-2 : ℝ)) L (r, x)‖ ≤ B := by
  set c : ℝ := ν ^ (-2 : ℝ)
  have hc0 : 0 < c := Real.rpow_pos_of_pos hν _
  obtain ⟨C, hC0, hC⟩ := hL.norm_le
  have ha_s : 1 ≤ clockA ν s := one_le_clockA hν.le (ht₁.trans hts)
  have hsum_nat : Summable (fun n : ℕ => ((1 + (n : ℝ) * c) ^ 2)⁻¹) := by
    have hpow2 : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹) := by
      have h := (Real.summable_nat_pow_inv.2 one_lt_two).comp_injective Nat.succ_injective
      simpa [Function.comp_def, Nat.cast_succ] using h
    refine Summable.of_norm_bounded (hpow2.mul_left ((min 1 c) ^ 2)⁻¹) fun n => ?_
    rw [Real.norm_of_nonneg (by positivity)]
    have hle : min 1 c * ((n : ℝ) + 1) ≤ 1 + (n : ℝ) * c := by
      have h1 : min 1 c ≤ 1 := min_le_left _ _
      have h2 : min 1 c ≤ c := min_le_right _ _
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hsq : (min 1 c * ((n : ℝ) + 1)) ^ 2 ≤ (1 + (n : ℝ) * c) ^ 2 :=
      pow_le_pow_left₀ (by have : 0 < min 1 c := lt_min zero_lt_one hc0; positivity) hle 2
    have hpos_min : 0 < (min 1 c * ((n : ℝ) + 1)) ^ 2 := by
      have : 0 < min 1 c := lt_min zero_lt_one hc0
      positivity
    calc ((1 + (n : ℝ) * c) ^ 2)⁻¹ ≤ ((min 1 c * ((n : ℝ) + 1)) ^ 2)⁻¹ := inv_anti₀ hpos_min hsq
      _ = ((min 1 c) ^ 2)⁻¹ * (((n : ℝ) + 1) ^ 2)⁻¹ := by rw [mul_pow, mul_inv]
  set S_nat : ℝ := ∑' n : ℕ, ((1 + (n : ℝ) * c) ^ 2)⁻¹
  have hS_nat0 : 0 ≤ S_nat := tsum_nonneg fun _ => by positivity
  set B : ℝ := clockA ν s * (C * (4 * max 1 (clockA ν s)) * (2 * S_nat + 1))
  refine ⟨B, by positivity, fun r hr x hx => ?_⟩
  have hr0 : 0 ≤ r := ht₁.trans hr.1
  have ha_r : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le hr0)
  have ha_rs : clockA ν r ≤ clockA ν s := clockA_mono hν.le hr.2
  rw [LamJetInf.perPhys_eq]
  have hsumm := LamJetInf.summable_good_shift (ν := ν) hc0.ne' hL (p := (r, x)) ha_r
  have hterm_eq : ∀ n : ℤ,
      LamJetInf.physTerm ν L ((r, x) + LamJetInf.shiftV c n) =
        ((clockA ν r : ℝ) : ℂ) * L (LamJetInf.iotaP ν ((r, x) + LamJetInf.shiftV c n)) := by
    intro n
    rw [LamJetInf.physTerm_eq]
    dsimp only
    rw [LamJetInf.shiftV_fst]
    rfl
  have htsum : ‖∑' n : ℤ, LamJetInf.physTerm ν L ((r, x) + LamJetInf.shiftV c n)‖ ≤
      clockA ν s * ∑' n : ℤ, C * (4 * max 1 (clockA ν s)) * ((1 + |x.1 + n * c|) ^ 2)⁻¹ := by
    calc ‖∑' n : ℤ, LamJetInf.physTerm ν L ((r, x) + LamJetInf.shiftV c n)‖
        ≤ ∑' n : ℤ, ‖LamJetInf.physTerm ν L ((r, x) + LamJetInf.shiftV c n)‖ := by
          refine norm_tsum_le_tsum_norm ?_
          simp_rw [hterm_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg ha_r.le]
          exact hsumm.norm.mul_left _
      _ ≤ ∑' n : ℤ, clockA ν s * (C * (4 * max 1 (clockA ν s)) * ((1 + |x.1 + n * c|) ^ 2)⁻¹) := by
          refine Summable.tsum_le_tsum (fun n => ?_) ?_ ?_
          · rw [hterm_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg ha_r.le]
            have h1 := hC (LamJetInf.iotaP ν ((r, x) + LamJetInf.shiftV c n))
            have hp : 0 < (1 + ‖LamJetInf.iotaP ν ((r, x) + LamJetInf.shiftV c n)‖) ^ 2 := by positivity
            have h2 : ‖L (LamJetInf.iotaP ν ((r, x) + LamJetInf.shiftV c n))‖ ≤
                C * ((1 + ‖LamJetInf.iotaP ν ((r, x) + LamJetInf.shiftV c n)‖) ^ 2)⁻¹ := by
              rw [← div_eq_mul_inv, le_div_iff₀ hp]; exact h1
            have hι := LamJetInf.inv_sq_iota_le (ν := ν) (q := (r, x) + LamJetInf.shiftV c n)
              (x₀ := x.1 + n * c) (A := clockA ν s)
              (by rw [LamJetInf.shiftV_fst]; exact ha_r)
              (by rw [LamJetInf.shiftV_fst]; exact ha_rs)
              (by rw [LamJetInf.shiftV_snd_fst]; simp)
            calc clockA ν r * ‖L (LamJetInf.iotaP ν ((r, x) + LamJetInf.shiftV c n))‖
                ≤ clockA ν s * (C * (4 * max 1 (clockA ν s) * ((1 + |x.1 + n * c|) ^ 2)⁻¹)) := by
                  gcongr
                  exact h2.trans (mul_le_mul_of_nonneg_left hι hC0)
              _ = clockA ν s * (C * (4 * max 1 (clockA ν s)) * ((1 + |x.1 + n * c|) ^ 2)⁻¹) := by ring
          · simp_rw [hterm_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg ha_r.le]
            exact hsumm.norm.mul_left _
          · exact ((LamJetInf.summable_inv_sq_shift hc0.ne' x.1).mul_left _).mul_left _
      _ = clockA ν s * ∑' n : ℤ, C * (4 * max 1 (clockA ν s)) * ((1 + |x.1 + n * c|) ^ 2)⁻¹ :=
          tsum_mul_left
  refine htsum.trans ?_
  rw [tsum_mul_left]
  have hZ : (∑' n : ℤ, ((1 + |x.1 + (n : ℝ) * c|) ^ 2)⁻¹) ≤ 2 * S_nat + 1 := by
    have hxn : -(c / 2) ≤ x.1 := hx.1.1
    have hxp : x.1 < c / 2 := hx.1.2
    have hsumZ := LamJetInf.summable_inv_sq_shift hc0.ne' x.1
    have hs_pos : Summable (fun n : ℕ => ((1 + |x.1 + (n : ℝ) * c|) ^ 2)⁻¹) :=
      hsumZ.comp_injective Nat.cast_injective
    have hs_neg : Summable (fun n : ℕ => ((1 + |x.1 + ((-(n + 1 : ℕ) : ℤ) : ℝ) * c|) ^ 2)⁻¹) :=
      hsumZ.comp_injective fun _ _ h => by omega
    have hsplit : (∑' n : ℤ, ((1 + |x.1 + (n : ℝ) * c|) ^ 2)⁻¹) =
        (∑' n : ℕ, ((1 + |x.1 + (n : ℝ) * c|) ^ 2)⁻¹) +
          (∑' n : ℕ, ((1 + |x.1 + ((-(n + 1 : ℕ) : ℤ) : ℝ) * c|) ^ 2)⁻¹) := by
      have hh := (hs_pos.hasSum.int_rec hs_neg.hasSum).tsum_eq
      rw [← hh]
      refine tsum_congr fun b' => ?_
      cases b' <;> rfl
    rw [hsplit]
    have hpos : (∑' n : ℕ, ((1 + |x.1 + (n : ℝ) * c|) ^ 2)⁻¹) ≤ S_nat + 1 := by
      rw [hs_pos.tsum_eq_zero_add]
      have h0 : ((1 + |x.1 + ((0 : ℕ) : ℝ) * c|) ^ 2)⁻¹ ≤ 1 := by
        rw [inv_le_one_iff₀]; right
        have : 0 ≤ |x.1 + ((0 : ℕ) : ℝ) * c| := abs_nonneg _
        nlinarith
      have hsucc : (∑' n : ℕ, ((1 + |x.1 + ((n + 1 : ℕ) : ℝ) * c|) ^ 2)⁻¹) ≤ S_nat := by
        refine Summable.tsum_le_tsum (fun n => ?_) (hs_pos.comp_injective Nat.succ_injective) hsum_nat
        gcongr
        have hnn : 0 ≤ x.1 + ((n + 1 : ℕ) : ℝ) * c := by
          push_cast
          have hn0 : 0 ≤ (n : ℝ) * c := mul_nonneg (Nat.cast_nonneg n) hc0.le
          linarith
        rw [abs_of_nonneg hnn]
        push_cast; linarith
      linarith
    have hneg : (∑' n : ℕ, ((1 + |x.1 + ((-(n + 1 : ℕ) : ℤ) : ℝ) * c|) ^ 2)⁻¹) ≤ S_nat := by
      refine Summable.tsum_le_tsum (fun n => ?_) hs_neg hsum_nat
      gcongr
      have h1 : x.1 + ((-(n + 1 : ℕ) : ℤ) : ℝ) * c ≤ -(n : ℝ) * c := by
        push_cast; linarith
      calc (n : ℝ) * c = -(-(n : ℝ) * c) := by ring
        _ ≤ -(x.1 + ((-(n + 1 : ℕ) : ℤ) : ℝ) * c) := neg_le_neg h1
        _ ≤ |x.1 + ((-(n + 1 : ℕ) : ℤ) : ℝ) * c| := neg_le_abs _
    linarith
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hZ (by positivity)) (zero_le_one.trans ha_s)

private theorem memLp_and_xNorm_cell_bdd_of_cont {m c B : ℝ} (hm : 1 < m) (hB0 : 0 ≤ B)
    {F : ℝ × ℝ → ℂ} (hFc : Continuous F) (hB : ∀ y ∈ B0579.cell c, ‖F y‖ ≤ B) :
    MemLp F 2 (B0579.cellMeasure c (-m)) ∧
    xNorm c (-m) F ≤ ENNReal.ofReal ((B0592.weightConst m).toReal * B) :=
  ComplCouplingHeat.memLp_and_xNorm_neg_le_of_cell_bdd hm hB0
    hFc.aestronglyMeasurable.restrict hB

private theorem continuousOn_indef_Ioc {t₁ s : ℝ} (hts : t₁ ≤ s) {f : ℝ → ℂ}
    (hf : IntegrableOn f (Ioc t₁ s)) :
    ContinuousOn (fun r => ∫ q in Ioc t₁ r, f q) (Icc t₁ s) := by
  have hf_u : IntegrableOn f (Set.uIcc t₁ s) := by
    rw [Set.uIcc_of_le hts]
    exact (integrableOn_Icc_iff_integrableOn_Ioc).2 hf
  have hcont := intervalIntegral.continuousOn_primitive_interval hf_u
  rw [Set.uIcc_of_le hts] at hcont
  refine hcont.congr fun r hr => ?_
  rw [← intervalIntegral.integral_of_le hr.1]

set_option maxHeartbeats 1200000 in
/-- Unnormalised amplitude FTC on `[t₁, t₂]` for all `0 < ν` and `1 ≤ b ≤ clockTheta ν t₂`. -/
theorem amplFTC_unconditional
    (κ : PlanarFrameKernels) (hκ : IsSeedKernels κ)
    {ν m b K : ℝ} (hm : 8 < m) (hν : 0 < ν) (hb : 1 ≤ b)
    (hF : PerFrameFacts κ ν m b K)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (htr : PartI.IsBUCTrain tr)
    (hBddAll : ∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C)
    {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁) (ht12 : t₁ ≤ t₂) (hbt₂ : b ≤ clockTheta ν t₂)
    {f : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u)
    (hf0 : HasZeroCirculation (ν ^ (-2 : ℝ)) f) :
    ∀ r ∈ Icc t₁ t₂, ∀ s' ∈ Icc r t₂, ∀ i : Fin 2,
      ampl (periodizedFrame κ ν m b K hν hF) w s' i -
          ampl (periodizedFrame κ ν m b K hν hF) w r i =
        ∫ q in Ioc r s', (((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) * movH0 κ tr q i (movingW ν w q) := by
  intro r hr s' hs' i
  let F := periodizedFrame κ ν m b K hν hF
  let g_lim : ℝ → ℂ := fun q =>
    (((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) * movH0 κ tr q i (movingW ν w q)
  rcases eq_or_lt_of_le ht12 with rfl | ht₁t₂
  · have hr_eq : r = t₁ := le_antisymm hr.2 hr.1
    have hs'_eq : s' = t₁ := le_antisymm hs'.2 (hr.1.trans hs'.1)
    subst hr_eq; subst hs'_eq
    rw [sub_self, Ioc_self, Measure.restrict_empty, integral_zero_measure]
  have ht₂0 : 0 ≤ t₂ := ht₁.trans ht12
  have hν1 : ν ≤ 1 := nu_le_one_of_theta hν hb ht₂0 hbt₂
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc1 : 1 ≤ c := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by norm_num)
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  -- Step 1: prove `ampl F w r' i - ampl F w t₁ i = ∫ q in Ioc t₁ r', g_lim q` for `r' ∈ Ico t₁ t₂`
  have hIco : ∀ r' ∈ Ico t₁ t₂, ampl F w r' i - ampl F w t₁ i = ∫ q in Ioc t₁ r', g_lim q := by
    obtain ⟨C_tr, hBdd⟩ := hBddAll t₂ ht₂0
    have hC_tr0 : 0 ≤ C_tr :=
      le_trans (abs_nonneg _) ((hBdd t₂ ⟨ht₂0, le_rfl⟩ (0, 0) ⟨⟨by linarith, by linarith⟩, trivial⟩).1 0)
    have hwc : ContinuousOn (fun ρ => (xNorm c m (w ρ)).toReal) (Ici t₁) :=
      RateBoundAux.contOn_norm w (fun ρ h => hw.memX ρ h) (fun ρ h => hw.strongCont ρ h)
    obtain ⟨A_w, hA_w0, hA_w⟩ :=
      RateBoundAux.bdd_of_cont (hwc.mono (Icc_subset_Ici_self : Icc t₁ t₂ ⊆ Ici t₁))
    obtain ⟨Cl, hCl⟩ := ladVelLip m hm ν c tr t₁ f w u hc1 hf0 hw
    have hu2 : ∀ ρ, t₁ ≤ ρ → ∀ j : Fin 2,
        MemLp (fun x => u ρ x j) 2 (volume.restrict (B0579.cell c)) :=
      fun ρ h j => (hw.biotSavart ρ h).1 j
    have hAe : ∀ ρ ∈ Icc t₁ t₂, xNorm c m (w ρ) ≤ ENNReal.ofReal A_w := fun ρ hρ =>
      RateBoundAux.ofReal_toReal_le (hw.memX ρ hρ.1).eLpNorm_ne_top hA_w0 (hA_w ρ hρ)
    have hU_bd : ∀ ρ ∈ Icc t₁ t₂, ∀ j : Fin 2,
        eLpNorm (fun x => u ρ x j) 2 (volume.restrict (B0579.cell c)) ≤
          ENNReal.ofReal Cl * (ENNReal.ofReal A_w + ENNReal.ofReal A_w) +
            eLpNorm (fun x => u t₁ x j) 2 (volume.restrict (B0579.cell c)) := by
      intro ρ hρ j
      have h1 := eLpNorm_add_le (p := 2) (μ := volume.restrict (B0579.cell c))
        ((hu2 ρ hρ.1 j).1.sub (hu2 t₁ le_rfl j).1) (hu2 t₁ le_rfl j).1 one_le_two
      rw [sub_add_cancel] at h1
      have h2 := hCl ρ t₁ hρ.1 le_rfl j
      have h3 : xNorm c m (w ρ - w t₁) ≤ xNorm c m (w ρ) + xNorm c m (w t₁) :=
        eLpNorm_sub_le (hw.memX ρ hρ.1).1 (hw.memX t₁ le_rfl).1 one_le_two
      have h4 : xNorm c m (w ρ - w t₁) ≤ ENNReal.ofReal A_w + ENNReal.ofReal A_w :=
        h3.trans (add_le_add (hAe ρ hρ) (hAe t₁ ⟨le_rfl, ht12⟩))
      exact h1.trans (add_le_add (h2.trans (mul_le_mul' le_rfl h4)) le_rfl)
    set Fe : ℝ≥0∞ := ENNReal.ofReal C_tr *
      ((ENNReal.ofReal Cl * (ENNReal.ofReal A_w + ENNReal.ofReal A_w) +
          eLpNorm (fun x => u t₁ x 0) 2 (volume.restrict (B0579.cell c))) +
        (ENNReal.ofReal Cl * (ENNReal.ofReal A_w + ENNReal.ofReal A_w) +
          eLpNorm (fun x => u t₁ x 1) 2 (volume.restrict (B0579.cell c))))
    have hFe : Fe ≠ ⊤ := by
      refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.2 ⟨?_, ?_⟩) <;>
        exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩),
          (hu2 t₁ le_rfl _).eLpNorm_ne_top⟩
    have hforce : ∀ ρ ∈ Icc t₁ t₂, MemLp (ladForce tr (u ρ) ρ) 2 (B0579.cellMeasure c m) ∧
        (xNorm c m (ladForce tr (u ρ) ρ)).toReal ≤ Fe.toReal := by
      intro ρ hρ
      obtain ⟨h1, h2⟩ := ladForceMemX m ν c tr t₂ C_tr ρ hBdd ⟨ht₁.trans hρ.1, hρ.2⟩ (u ρ)
        (fun j => hu2 ρ hρ.1 j)
      exact ⟨h1, ENNReal.toReal_mono hFe
        (h2.trans (mul_le_mul' le_rfl (add_le_add (hU_bd ρ hρ 0) (hU_bd ρ hρ 1))))⟩
    have hSmooth : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => physFrameLam κ ν p.1 i p.2)
        (Ico t₁ t₂ ×ˢ univ) :=
      contDiffOn_physFrameLam_Ico κ hκ hν hm hb hF ht₁ ht12 hbt₂ i
    have hGinv_bd : ∃ M_G : ℝ, 0 ≤ M_G ∧ ∀ ρ ∈ Icc t₁ t₂, ∀ j : Fin 2,
        ‖(perGram κ (dd ν ρ))⁻¹ i j‖ ≤ M_G := by
      have h0 : ContinuousOn (fun ρ => ‖(perGram κ (dd ν ρ))⁻¹ i 0‖) (Icc t₁ t₂) :=
        (contDiffOn_perGram_inv_Icc κ hκ hν hm hb hF ht₁ ht12 hbt₂ i 0).continuousOn.norm
      have h1 : ContinuousOn (fun ρ => ‖(perGram κ (dd ν ρ))⁻¹ i 1‖) (Icc t₁ t₂) :=
        (contDiffOn_perGram_inv_Icc κ hκ hν hm hb hF ht₁ ht12 hbt₂ i 1).continuousOn.norm
      obtain ⟨B0, hB0⟩ := isCompact_Icc.bddAbove_image h0
      obtain ⟨B1, hB1⟩ := isCompact_Icc.bddAbove_image h1
      refine ⟨max (max B0 B1) 0, le_max_right _ _, fun ρ hρ j => ?_⟩
      fin_cases j
      · exact (hB0 ⟨ρ, hρ, rfl⟩).trans ((le_max_left _ _).trans (le_max_left _ _))
      · exact (hB1 ⟨ρ, hρ, rfl⟩).trans ((le_max_right _ _).trans (le_max_left _ _))
    obtain ⟨M_G, hM_G0, hGinv⟩ := hGinv_bd
    have hGder_bd : ∃ M_Gd : ℝ, 0 ≤ M_Gd ∧ ∀ ρ ∈ Ioo t₁ t₂, ∀ j : Fin 2,
        ‖derivWithin (fun r' => (perGram κ (dd ν r'))⁻¹ i j) (Ici ρ) ρ‖ ≤ M_Gd := by
      have hfd : ∀ j : Fin 2, ContinuousOn
          (fun ρ => ‖fderivWithin ℝ (fun r' => (perGram κ (dd ν r'))⁻¹ i j) (Icc t₁ t₂) ρ 1‖)
          (Icc t₁ t₂) := by
        intro j
        have hcd := (contDiffOn_perGram_inv_Icc κ hκ hν hm hb hF ht₁ ht12 hbt₂ i j).continuousOn_fderivWithin
          (uniqueDiffOn_Icc ht₁t₂) (by simp)
        exact (hcd.clm_apply continuousOn_const).norm
      obtain ⟨B0, hB0⟩ := isCompact_Icc.bddAbove_image (hfd 0)
      obtain ⟨B1, hB1⟩ := isCompact_Icc.bddAbove_image (hfd 1)
      refine ⟨max (max B0 B1) 0, le_max_right _ _, fun ρ hρ j => ?_⟩
      have hρ_Icc : ρ ∈ Icc t₁ t₂ := Ioo_subset_Icc_self hρ
      have hcd := (contDiffOn_perGram_inv_Icc κ hκ hν hm hb hF ht₁ ht12 hbt₂ i j).differentiableOn
        (by simp)
      have hd_at : DifferentiableAt ℝ (fun r' => (perGram κ (dd ν r'))⁻¹ i j) ρ :=
        hcd.differentiableAt (Icc_mem_nhds hρ.1 hρ.2)
      have h_eq : derivWithin (fun r' => (perGram κ (dd ν r'))⁻¹ i j) (Ici ρ) ρ =
          fderivWithin ℝ (fun r' => (perGram κ (dd ν r'))⁻¹ i j) (Icc t₁ t₂) ρ 1 := by
        rw [hd_at.hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici ρ),
          hd_at.hasDerivAt.hasFDerivAt.hasFDerivWithinAt.fderivWithin (uniqueDiffOn_Icc ht₁t₂ ρ hρ_Icc)]
        simp
      rw [h_eq]
      fin_cases j
      · exact (hB0 ⟨ρ, hρ_Icc, rfl⟩).trans ((le_max_left _ _).trans (le_max_left _ _))
      · exact (hB1 ⟨ρ, hρ_Icc, rfl⟩).trans ((le_max_right _ _).trans (le_max_left _ _))
    obtain ⟨M_Gd, hM_Gd0, hGder⟩ := hGder_bd
    have hGood : ∀ j : Fin 2, LamJetInf.Good (κ.lamP j) := fun j => LamJetInf.good_lamP hκ j
    have hB0 : ∀ j : Fin 2, ∃ B, 0 ≤ B ∧ ∀ q ∈ Icc t₁ t₂, ∀ x ∈ B0579.cell c,
        ‖LamJetInf.perPhys ν c (κ.lamP j) (q, x)‖ ≤ B :=
      fun j => perPhys_bdd_on_cell hν ht₁ ht12 (hGood j)
    have hB1 : ∀ j k : Fin 2, ∃ B, 0 ≤ B ∧ ∀ q ∈ Icc t₁ t₂, ∀ x ∈ B0579.cell c,
        ‖LamJetInf.perPhys ν c (fun z => fderiv ℝ (κ.lamP j) z (B0579.dir k)) (q, x)‖ ≤ B :=
      fun j k => perPhys_bdd_on_cell hν ht₁ ht12 ((hGood j).fderiv_apply (B0579.dir k))
    have hB2 : ∀ j k : Fin 2, ∃ B, 0 ≤ B ∧ ∀ q ∈ Icc t₁ t₂, ∀ x ∈ B0579.cell c,
        ‖LamJetInf.perPhys ν c
          (fun z => fderiv ℝ (fun z' => fderiv ℝ (κ.lamP j) z' (B0579.dir k)) z (B0579.dir k))
          (q, x)‖ ≤ B :=
      fun j k => perPhys_bdd_on_cell hν ht₁ ht12
        (((hGood j).fderiv_apply (B0579.dir k)).fderiv_apply (B0579.dir k))
    have hBE : ∀ j : Fin 2, ∃ B, 0 ≤ B ∧ ∀ q ∈ Icc t₁ t₂, ∀ x ∈ B0579.cell c,
        ‖LamJetInf.perPhys ν c (LamJetInf.eulerK (κ.lamP j)) (q, x)‖ ≤ B :=
      fun j => perPhys_bdd_on_cell hν ht₁ ht12 (hGood j).eulerK
    choose B0 hB0_pos hB0_le using hB0
    choose B1 hB1_pos hB1_le using hB1
    choose B2 hB2_pos hB2_le using hB2
    choose BE hBE_pos hBE_le using hBE
    set B_lam : ℝ := M_G * (B0 0 + B0 1)
    set B_g : ℝ := M_G * (max (B1 0 0) (B1 0 1) + max (B1 1 0) (B1 1 1))
    set B_lap : ℝ := M_G * ((B2 0 0 + B2 0 1) + (B2 1 0 + B2 1 1))
    set B_dt : ℝ := M_G * (|ν| * (BE 0 + BE 1)) + M_Gd * (B0 0 + B0 1)
    set B_tr : ℝ := 2 * C_tr * B_g
    have hB_lam0 : 0 ≤ B_lam := mul_nonneg hM_G0 (add_nonneg (hB0_pos 0) (hB0_pos 1))
    have hB_g0 : 0 ≤ B_g := mul_nonneg hM_G0 (add_nonneg (le_max_of_le_left (hB1_pos 0 0)) (le_max_of_le_left (hB1_pos 1 0)))
    have hB_lap0 : 0 ≤ B_lap := mul_nonneg hM_G0 (add_nonneg (add_nonneg (hB2_pos 0 0) (hB2_pos 0 1)) (add_nonneg (hB2_pos 1 0) (hB2_pos 1 1)))
    have hB_dt0 : 0 ≤ B_dt := add_nonneg (mul_nonneg hM_G0 (mul_nonneg (abs_nonneg ν) (add_nonneg (hBE_pos 0) (hBE_pos 1)))) (mul_nonneg hM_Gd0 (add_nonneg (hB0_pos 0) (hB0_pos 1)))
    have hB_tr0 : 0 ≤ B_tr := mul_nonneg (mul_nonneg (by norm_num) hC_tr0) hB_g0
    set W_c : ℝ := (B0592.weightConst m).toReal
    have hW_c0 : 0 ≤ W_c := ENNReal.toReal_nonneg
    set M_φ : ℝ := W_c * B_lam
    set M_g : ℝ := W_c * B_g
    have hM_φ0 : 0 ≤ M_φ := mul_nonneg hW_c0 hB_lam0
    have hM_g0 : 0 ≤ M_g := mul_nonneg hW_c0 hB_g0
    obtain ⟨M_ker, hM_ker0, hKerAll⟩ := kerAdj_memLp_and_transposition (K_Φ := M_φ)
      hm hc1 hC_tr0 hM_φ0 hBdd
    set M_ND : ℝ := W_c * (B_dt + |ν| * B_lap + B_tr) + M_ker
    have hM_ND0 : 0 ≤ M_ND := add_nonneg (mul_nonneg hW_c0 (add_nonneg (add_nonneg hB_dt0 (mul_nonneg (abs_nonneg ν) hB_lap0)) hB_tr0)) hM_ker0
    let φ : ℝ → ℝ × ℝ → ℂ := fun r' x' => physFrameLam κ ν r' i x'
    have hφ_per : ∀ ρ ∈ Ico t₁ t₂, ∀ x : ℝ × ℝ, φ ρ (x.1 + c, x.2) = φ ρ x := fun ρ hρ x =>
      physFrameLam_periodic κ hν (ht₁.trans hρ.1) i x
    obtain ⟨K_cut, hK_cut0, hK_cut⟩ := ladCutProps
    have hLam_Ico : ∀ ρ ∈ Ico t₁ t₂,
        MemLp (physFrameLam κ ν ρ i) 2 (B0579.cellMeasure c (-m)) ∧
        xNorm c (-m) (physFrameLam κ ν ρ i) ≤ ENNReal.ofReal M_φ := by
      intro ρ hρ
      have hρ_Icc : ρ ∈ Icc t₁ t₂ := Ico_subset_Icc_self hρ
      have hρ0 : 0 ≤ ρ := ht₁.trans hρ.1
      have hslice : ContDiff ℝ ∞ (physFrameLam κ ν ρ i) :=
        RateSplitAux.contDiff_slice (φ := fun r' x' => physFrameLam κ ν r' i x') hρ hSmooth
      refine memLp_and_xNorm_cell_bdd_of_cont (by linarith) (by positivity)
        hslice.continuous fun x hx => ?_
      rw [physFrameLam_eq_sum_perGram_inv κ ν ρ i x, Fin.sum_univ_two,
        physFrameLam0_eq_perSum_physAdj κ hν hρ0 0 x,
        physFrameLam0_eq_perSum_physAdj κ hν hρ0 1 x]
      calc ‖(perGram κ (dd ν ρ))⁻¹ i 0 * LamJetInf.perPhys ν c (κ.lamP 0) (ρ, x) +
            (perGram κ (dd ν ρ))⁻¹ i 1 * LamJetInf.perPhys ν c (κ.lamP 1) (ρ, x)‖
          ≤ ‖(perGram κ (dd ν ρ))⁻¹ i 0‖ * ‖LamJetInf.perPhys ν c (κ.lamP 0) (ρ, x)‖ +
            ‖(perGram κ (dd ν ρ))⁻¹ i 1‖ * ‖LamJetInf.perPhys ν c (κ.lamP 1) (ρ, x)‖ :=
            (norm_add_le _ _).trans (by rw [norm_mul, norm_mul])
        _ ≤ M_G * B0 0 + M_G * B0 1 :=
            add_le_add (mul_le_mul (hGinv ρ hρ_Icc 0) (hB0_le 0 ρ hρ_Icc x hx) (norm_nonneg _) hM_G0)
              (mul_le_mul (hGinv ρ hρ_Icc 1) (hB0_le 1 ρ hρ_Icc x hx) (norm_nonneg _) hM_G0)
        _ = B_lam := by ring
    have hpd_bd : ∀ ρ ∈ Ioo t₁ t₂, ∀ k : Fin 2,
        MemLp (pdCx k (physFrameLam κ ν ρ i)) 2 (B0579.cellMeasure c (-m)) ∧
        xNorm c (-m) (pdCx k (physFrameLam κ ν ρ i)) ≤ ENNReal.ofReal M_g := by
      intro ρ hρ k
      have hρ_Icc : ρ ∈ Icc t₁ t₂ := Ioo_subset_Icc_self hρ
      have hρ0 : 0 ≤ ρ := ht₁.trans hρ_Icc.1
      have ha_r : 0 < clockA ν ρ := lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le hρ0)
      have ha_inv_sqrt : (Real.sqrt (clockA ν ρ))⁻¹ ≤ 1 :=
        inv_le_one_of_one_le₀ (by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (one_le_clockA hν.le hρ0))
      have hslice : ContDiff ℝ ∞ (physFrameLam κ ν ρ i) :=
        RateSplitAux.contDiff_slice (φ := fun r' x' => physFrameLam κ ν r' i x')
          (Ioo_subset_Ico_self hρ) hSmooth
      refine memLp_and_xNorm_cell_bdd_of_cont (by linarith) (by positivity)
        (RateSplitAux.contDiff_pdCx hslice k).continuous fun x hx => ?_
      have hsum_fn : physFrameLam κ ν ρ i = fun x' =>
          (perGram κ (dd ν ρ))⁻¹ i 0 * LamJetInf.perPhys ν c (κ.lamP 0) (ρ, x') +
          (perGram κ (dd ν ρ))⁻¹ i 1 * LamJetInf.perPhys ν c (κ.lamP 1) (ρ, x') := by
        funext x'
        rw [physFrameLam_eq_sum_perGram_inv κ ν ρ i x', Fin.sum_univ_two,
          physFrameLam0_eq_perSum_physAdj κ hν hρ0 0 x',
          physFrameLam0_eq_perSum_physAdj κ hν hρ0 1 x']
        rfl
      have hcd_lam : ∀ j : Fin 2, Differentiable ℝ (fun x' => LamJetInf.perPhys ν c (κ.lamP j) (ρ, x')) := by
        intro j x'
        have hd := ((LamJetInf.contDiffOn_perPhys hν hc0.ne' (hGood j)).differentiableOn
          (by simp)).differentiableAt ((LamJetInf.isOpen_physU ν).mem_nhds
            (show (ρ, x') ∈ LamJetInf.physU ν from ha_r))
        exact hd.comp x' (differentiableAt_const ρ |>.prodMk differentiableAt_id)
      rw [hsum_fn, RateSplitAux.pdCx_add k ((hcd_lam 0 x).const_mul _) ((hcd_lam 1 x).const_mul _),
        pdCx_const_mul _ _ k x (hcd_lam 0 x), pdCx_const_mul _ _ k x (hcd_lam 1 x)]
      have hpd_per : ∀ j : Fin 2,
          pdCx k (fun x' => LamJetInf.perPhys ν c (κ.lamP j) (ρ, x')) x =
            ((Real.sqrt (clockA ν ρ)⁻¹ : ℝ) : ℂ) *
              LamJetInf.perPhys ν c (fun z => fderiv ℝ (κ.lamP j) z (B0579.dir k)) (ρ, x) := by
        intro j
        have hd := ((LamJetInf.contDiffOn_perPhys hν hc0.ne' (hGood j)).differentiableOn
          (by simp)).differentiableAt ((LamJetInf.isOpen_physU ν).mem_nhds
            (show (ρ, x) ∈ LamJetInf.physU ν from ha_r))
        have hfd : pdCx k (fun x' => LamJetInf.perPhys ν c (κ.lamP j) (ρ, x')) x =
            fderiv ℝ (LamJetInf.perPhys ν c (κ.lamP j)) (ρ, x) (0, B0579.dir k) := by
          unfold pdCx
          have hcomp : HasFDerivAt (fun x' => LamJetInf.perPhys ν c (κ.lamP j) (ρ, x'))
              ((fderiv ℝ (LamJetInf.perPhys ν c (κ.lamP j)) (ρ, x)).comp
                (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) x :=
            hd.hasFDerivAt.comp x (hasFDerivAt_const ρ x |>.prodMk (hasFDerivAt_id x))
          rw [hcomp.fderiv]; rfl
        rw [hfd, LamJetInf.fderiv_perPhys_apply hν hc0.ne' (hGood j) ha_r]
        simp only [mul_zero, zero_mul, Complex.ofReal_zero, zero_add, Real.sqrt_inv]
        congr 2
        field_simp [(Real.sqrt_pos.2 ha_r).ne']
        rw [Real.sq_sqrt ha_r.le]
      rw [hpd_per 0, hpd_per 1]
      have hnorm0 : ‖((Real.sqrt (clockA ν ρ)⁻¹ : ℝ) : ℂ) *
          LamJetInf.perPhys ν c (fun z => fderiv ℝ (κ.lamP 0) z (B0579.dir k)) (ρ, x)‖ ≤
          max (B1 0 0) (B1 0 1) := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), Real.sqrt_inv]
        calc (Real.sqrt (clockA ν ρ))⁻¹ * _
            ≤ 1 * B1 0 k := mul_le_mul ha_inv_sqrt (hB1_le 0 k ρ hρ_Icc x hx) (norm_nonneg _) zero_le_one
          _ ≤ max (B1 0 0) (B1 0 1) := by fin_cases k <;> simp
      have hnorm1 : ‖((Real.sqrt (clockA ν ρ)⁻¹ : ℝ) : ℂ) *
          LamJetInf.perPhys ν c (fun z => fderiv ℝ (κ.lamP 1) z (B0579.dir k)) (ρ, x)‖ ≤
          max (B1 1 0) (B1 1 1) := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), Real.sqrt_inv]
        calc (Real.sqrt (clockA ν ρ))⁻¹ * _
            ≤ 1 * B1 1 k := mul_le_mul ha_inv_sqrt (hB1_le 1 k ρ hρ_Icc x hx) (norm_nonneg _) zero_le_one
          _ ≤ max (B1 1 0) (B1 1 1) := by fin_cases k <;> simp
      calc ‖(perGram κ (dd ν ρ))⁻¹ i 0 * _ + (perGram κ (dd ν ρ))⁻¹ i 1 * _‖
          ≤ ‖(perGram κ (dd ν ρ))⁻¹ i 0‖ * ‖_‖ + ‖(perGram κ (dd ν ρ))⁻¹ i 1‖ * ‖_‖ :=
            (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
        _ ≤ M_G * max (B1 0 0) (B1 0 1) + M_G * max (B1 1 0) (B1 1 1) :=
            add_le_add (mul_le_mul (hGinv ρ hρ_Icc 0) hnorm0 (norm_nonneg _) hM_G0)
              (mul_le_mul (hGinv ρ hρ_Icc 1) hnorm1 (norm_nonneg _) hM_G0)
        _ = B_g := by ring
    have hDual_bd : ∀ ρ ∈ Ioo t₁ t₂,
        MemLp (physLamDual κ tr ρ i) 2 (B0579.cellMeasure c (-m)) ∧
        xNorm c (-m) (physLamDual κ tr ρ i) ≤ ENNReal.ofReal M_ND := by
      intro ρ hρ
      have hρ_Icc : ρ ∈ Icc t₁ t₂ := Ioo_subset_Icc_self hρ
      have hρ0 : 0 ≤ ρ := ht₁.trans hρ_Icc.1
      have hρS : ρ ∈ Icc (0 : ℝ) t₂ := ⟨hρ0, hρ_Icc.2⟩
      have ha_r : 0 < clockA ν ρ := lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le hρ0)
      have ha_inv_le : (clockA ν ρ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_clockA hν.le hρ0)
      have hslice : ContDiff ℝ ∞ (physFrameLam κ ν ρ i) :=
        RateSplitAux.contDiff_slice (φ := fun r' x' => physFrameLam κ ν r' i x')
          (Ioo_subset_Ico_self hρ) hSmooth
      have hKer := hKerAll hρS (hLam_Ico ρ (Ioo_subset_Ico_self hρ)).1
        (hLam_Ico ρ (Ioo_subset_Ico_self hρ)).2
      have hMain_cont : Continuous (fun x =>
          ladDt (fun r' x' => physFrameLam κ ν r' i x') ρ x +
            (ν : ℂ) * ladLapCx (physFrameLam κ ν ρ i) x) := by
        have hU_open : IsOpen (Ioo t₁ t₂ ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioo.prod isOpen_univ
        have hsub : Ioo t₁ t₂ ×ˢ (univ : Set (ℝ × ℝ)) ⊆ Ico t₁ t₂ ×ˢ univ :=
          prod_mono Ioo_subset_Ico_self Subset.rfl
        have hdt_cont : Continuous (fun x => ladDt (fun r' x' => physFrameLam κ ν r' i x') ρ x) := by
          have hcd := ((hSmooth.mono hsub).continuousOn_fderiv_of_isOpen hU_open (by simp))
          have heq : (fun x => ladDt (fun r' x' => physFrameLam κ ν r' i x') ρ x) =
              fun x => fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => physFrameLam κ ν p.1 i p.2) (ρ, x) (1, 0) := by
            funext x
            have hd := ((hSmooth.mono hsub).differentiableOn (by simp)).differentiableAt
              (hU_open.mem_nhds (show (ρ, x) ∈ Ioo t₁ t₂ ×ˢ (univ : Set (ℝ × ℝ)) from ⟨hρ, mem_univ _⟩))
            have h1 : HasDerivAt (fun r' => physFrameLam κ ν r' i x)
                (fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => physFrameLam κ ν p.1 i p.2) (ρ, x) (1, 0)) ρ := by
              simpa [Function.comp_def] using
                hd.hasFDerivAt.comp_hasDerivAt ρ ((hasDerivAt_id ρ).prodMk (hasDerivAt_const ρ x))
            exact h1.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici ρ)
          rw [heq]
          exact (hcd.clm_apply continuousOn_const).comp_continuous
            (continuous_const.prodMk continuous_id) fun x => ⟨hρ, mem_univ x⟩
        have hlap_cont : Continuous (ladLapCx (physFrameLam κ ν ρ i)) :=
          (RateSplitAux.contDiff_pdCx (RateSplitAux.contDiff_pdCx hslice 0) 0).continuous.add
            (RateSplitAux.contDiff_pdCx (RateSplitAux.contDiff_pdCx hslice 1) 1).continuous
        exact hdt_cont.add (continuous_const.mul hlap_cont)
      have hMain_bd : ∀ x ∈ B0579.cell c,
          ‖ladDt (fun r' x' => physFrameLam κ ν r' i x') ρ x +
            (ν : ℂ) * ladLapCx (physFrameLam κ ν ρ i) x‖ ≤ B_dt + |ν| * B_lap := by
        intro x hx
        have hcd_per : ∀ j : Fin 2, Differentiable ℝ
            (fun x' => LamJetInf.perPhys ν c (κ.lamP j) (ρ, x')) := by
          intro j x'
          have hd := ((LamJetInf.contDiffOn_perPhys hν hc0.ne' (hGood j)).differentiableOn
            (by simp)).differentiableAt ((LamJetInf.isOpen_physU ν).mem_nhds
              (show (ρ, x') ∈ LamJetInf.physU ν from ha_r))
          exact hd.comp x' (differentiableAt_const ρ |>.prodMk differentiableAt_id)
        have hcd_per1 : ∀ j k : Fin 2, Differentiable ℝ
            (fun x' => LamJetInf.perPhys ν c (fun z => fderiv ℝ (κ.lamP j) z (B0579.dir k)) (ρ, x')) := by
          intro j k x'
          have hd := ((LamJetInf.contDiffOn_perPhys hν hc0.ne'
            ((hGood j).fderiv_apply (B0579.dir k))).differentiableOn
            (by simp)).differentiableAt ((LamJetInf.isOpen_physU ν).mem_nhds
              (show (ρ, x') ∈ LamJetInf.physU ν from ha_r))
          exact hd.comp x' (differentiableAt_const ρ |>.prodMk differentiableAt_id)
        have hdt_eq : ladDt (fun r' x' => physFrameLam κ ν r' i x') ρ x =
            ∑ j : Fin 2,
              (deriv (fun r' => (perGram κ (dd ν r'))⁻¹ i j) ρ *
                LamJetInf.perPhys ν c (κ.lamP j) (ρ, x) +
              (perGram κ (dd ν ρ))⁻¹ i j *
                (((ν * (clockA ν ρ)⁻¹ : ℝ) : ℂ) *
                  LamJetInf.perPhys ν c (LamJetInf.eulerK (κ.lamP j)) (ρ, x))) := by
          have ht_nhds : Ioo t₁ t₂ ∈ 𝓝 ρ := Ioo_mem_nhds hρ.1 hρ.2
          have hfn_ev : (fun r' => physFrameLam κ ν r' i x) =ᶠ[𝓝 ρ] fun r' =>
              ∑ j : Fin 2, (perGram κ (dd ν r'))⁻¹ i j * LamJetInf.perPhys ν c (κ.lamP j) (r', x) := by
            refine Filter.eventually_of_mem ht_nhds fun r' hr' => ?_
            dsimp only [dd]
            rw [physFrameLam_eq_sum_perGram_inv κ ν r' i x]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [physFrameLam0_eq_perSum_physAdj κ hν (ht₁.trans hr'.1.le) j x]
            rfl
          have hdG : ∀ j : Fin 2, DifferentiableAt ℝ (fun r' => (perGram κ (dd ν r'))⁻¹ i j) ρ := by
            intro j
            exact ((contDiffOn_perGram_inv_Icc κ hκ hν hm hb hF ht₁ ht12 hbt₂ i j).differentiableOn
              (by simp)).differentiableAt (Icc_mem_nhds hρ.1 hρ.2)
          have hdP : ∀ j : Fin 2, HasDerivAt (fun r' => LamJetInf.perPhys ν c (κ.lamP j) (r', x))
              (((ν * (clockA ν ρ)⁻¹ : ℝ) : ℂ) *
                LamJetInf.perPhys ν c (LamJetInf.eulerK (κ.lamP j)) (ρ, x)) ρ := by
            intro j
            have hd := ((LamJetInf.contDiffOn_perPhys hν hc0.ne' (hGood j)).differentiableOn
              (by simp)).differentiableAt ((LamJetInf.isOpen_physU ν).mem_nhds
                (show (ρ, x) ∈ LamJetInf.physU ν from ha_r))
            have hcomp := hd.hasFDerivAt.comp_hasDerivAt ρ
              ((hasDerivAt_id ρ).prodMk (hasDerivAt_const ρ x))
            have hfd := LamJetInf.fderiv_perPhys_apply hν hc0.ne' (hGood j) (p := (ρ, x)) ha_r (1, (0 : ℝ × ℝ))
            have h0_per : LamJetInf.perPhys ν c (fun _ : ℝ × ℝ => (0 : ℂ)) (ρ, x) = 0 := by
              simp [LamJetInf.perPhys, perSum, physAdj]
            simp only [mul_one, map_zero, h0_per, mul_zero, add_zero] at hfd
            rw [hfd] at hcomp
            exact hcomp
          have hsum_der := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin 2))) fun j _ =>
            (hdG j).hasDerivAt.mul (hdP j)
          unfold ladDt
          exact (hsum_der.congr_of_eventuallyEq hfn_ev).hasDerivWithinAt.derivWithin
            (uniqueDiffWithinAt_Ici ρ)
        have hdt_bd : ‖ladDt (fun r' x' => physFrameLam κ ν r' i x') ρ x‖ ≤ B_dt := by
          rw [hdt_eq, Fin.sum_univ_two]
          have hGder' : ∀ j : Fin 2, ‖deriv (fun r' => (perGram κ (dd ν r'))⁻¹ i j) ρ‖ ≤ M_Gd := by
            intro j
            have hd_at := ((contDiffOn_perGram_inv_Icc κ hκ hν hm hb hF ht₁ ht12 hbt₂ i j).differentiableOn
              (by simp)).differentiableAt (Icc_mem_nhds hρ.1 hρ.2)
            rw [← hd_at.hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici ρ)]
            exact hGder ρ hρ j
          have hνa : ‖((ν * (clockA ν ρ)⁻¹ : ℝ) : ℂ)‖ ≤ |ν| := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (inv_nonneg.2 ha_r.le)]
            exact mul_le_of_le_one_right (abs_nonneg ν) ha_inv_le
          have ht0 : ‖deriv (fun r' => (perGram κ (dd ν r'))⁻¹ i 0) ρ *
                LamJetInf.perPhys ν c (κ.lamP 0) (ρ, x) +
              (perGram κ (dd ν ρ))⁻¹ i 0 * (((ν * (clockA ν ρ)⁻¹ : ℝ) : ℂ) *
                LamJetInf.perPhys ν c (LamJetInf.eulerK (κ.lamP 0)) (ρ, x))‖ ≤
              M_Gd * B0 0 + M_G * (|ν| * BE 0) := by
            refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
            · rw [norm_mul]
              exact mul_le_mul (hGder' 0) (hB0_le 0 ρ hρ_Icc x hx) (norm_nonneg _) hM_Gd0
            · rw [norm_mul, norm_mul]
              exact mul_le_mul (hGinv ρ hρ_Icc 0)
                (mul_le_mul hνa (hBE_le 0 ρ hρ_Icc x hx) (norm_nonneg _) (abs_nonneg ν))
                (by positivity) hM_G0
          have ht1 : ‖deriv (fun r' => (perGram κ (dd ν r'))⁻¹ i 1) ρ *
                LamJetInf.perPhys ν c (κ.lamP 1) (ρ, x) +
              (perGram κ (dd ν ρ))⁻¹ i 1 * (((ν * (clockA ν ρ)⁻¹ : ℝ) : ℂ) *
                LamJetInf.perPhys ν c (LamJetInf.eulerK (κ.lamP 1)) (ρ, x))‖ ≤
              M_Gd * B0 1 + M_G * (|ν| * BE 1) := by
            refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
            · rw [norm_mul]
              exact mul_le_mul (hGder' 1) (hB0_le 1 ρ hρ_Icc x hx) (norm_nonneg _) hM_Gd0
            · rw [norm_mul, norm_mul]
              exact mul_le_mul (hGinv ρ hρ_Icc 1)
                (mul_le_mul hνa (hBE_le 1 ρ hρ_Icc x hx) (norm_nonneg _) (abs_nonneg ν))
                (by positivity) hM_G0
          calc ‖_ + _‖ ≤ _ + _ := norm_add_le _ _
            _ ≤ (M_Gd * B0 0 + M_G * (|ν| * BE 0)) + (M_Gd * B0 1 + M_G * (|ν| * BE 1)) :=
                add_le_add ht0 ht1
            _ = B_dt := by ring
        have hlap_bd : ‖ladLapCx (physFrameLam κ ν ρ i) x‖ ≤ B_lap := by
          have ha_inv_sqrt : (Real.sqrt (clockA ν ρ))⁻¹ ≤ 1 :=
            inv_le_one_of_one_le₀ (by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (one_le_clockA hν.le hρ0))
          have hsum_fn : physFrameLam κ ν ρ i = fun x' =>
              (perGram κ (dd ν ρ))⁻¹ i 0 * LamJetInf.perPhys ν c (κ.lamP 0) (ρ, x') +
              (perGram κ (dd ν ρ))⁻¹ i 1 * LamJetInf.perPhys ν c (κ.lamP 1) (ρ, x') := by
            funext x'
            rw [physFrameLam_eq_sum_perGram_inv κ ν ρ i x', Fin.sum_univ_two,
              physFrameLam0_eq_perSum_physAdj κ hν hρ0 0 x',
              physFrameLam0_eq_perSum_physAdj κ hν hρ0 1 x']
            rfl
          have hpd_per : ∀ (L : ℝ × ℝ → ℂ) (hL : LamJetInf.Good L) (k : Fin 2) (x' : ℝ × ℝ),
              pdCx k (fun y => LamJetInf.perPhys ν c L (ρ, y)) x' =
                ((Real.sqrt (clockA ν ρ)⁻¹ : ℝ) : ℂ) *
                  LamJetInf.perPhys ν c (fun z => fderiv ℝ L z (B0579.dir k)) (ρ, x') := by
            intro L hL k x'
            have hd := ((LamJetInf.contDiffOn_perPhys hν hc0.ne' hL).differentiableOn
              (by simp)).differentiableAt ((LamJetInf.isOpen_physU ν).mem_nhds
                (show (ρ, x') ∈ LamJetInf.physU ν from ha_r))
            have hfd : pdCx k (fun y => LamJetInf.perPhys ν c L (ρ, y)) x' =
                fderiv ℝ (LamJetInf.perPhys ν c L) (ρ, x') (0, B0579.dir k) := by
              unfold pdCx
              have hcomp : HasFDerivAt (fun y => LamJetInf.perPhys ν c L (ρ, y))
                  ((fderiv ℝ (LamJetInf.perPhys ν c L) (ρ, x')).comp
                    (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) x' :=
                hd.hasFDerivAt.comp x' (hasFDerivAt_const ρ x' |>.prodMk (hasFDerivAt_id x'))
              rw [hcomp.fderiv]; rfl
            rw [hfd, LamJetInf.fderiv_perPhys_apply hν hc0.ne' hL ha_r]
            simp only [mul_zero, zero_mul, Complex.ofReal_zero, zero_add, Real.sqrt_inv]
            congr 2
            field_simp [(Real.sqrt_pos.2 ha_r).ne']
            rw [Real.sq_sqrt ha_r.le]
          have hpd2_bd : ∀ k : Fin 2,
              ‖pdCx k (pdCx k (physFrameLam κ ν ρ i)) x‖ ≤ M_G * (B2 0 k + B2 1 k) := by
            intro k
            have hpd1_fn : pdCx k (physFrameLam κ ν ρ i) = fun x' =>
                ((perGram κ (dd ν ρ))⁻¹ i 0 * ((Real.sqrt (clockA ν ρ)⁻¹ : ℝ) : ℂ)) *
                  LamJetInf.perPhys ν c (fun z => fderiv ℝ (κ.lamP 0) z (B0579.dir k)) (ρ, x') +
                ((perGram κ (dd ν ρ))⁻¹ i 1 * ((Real.sqrt (clockA ν ρ)⁻¹ : ℝ) : ℂ)) *
                  LamJetInf.perPhys ν c (fun z => fderiv ℝ (κ.lamP 1) z (B0579.dir k)) (ρ, x') := by
              funext x'
              rw [hsum_fn, RateSplitAux.pdCx_add k ((hcd_per 0 x').const_mul _) ((hcd_per 1 x').const_mul _),
                pdCx_const_mul _ _ k x' (hcd_per 0 x'), pdCx_const_mul _ _ k x' (hcd_per 1 x'),
                hpd_per _ (hGood 0) k x', hpd_per _ (hGood 1) k x', mul_assoc, mul_assoc]
            rw [hpd1_fn,
              RateSplitAux.pdCx_add k ((hcd_per1 0 k x).const_mul _) ((hcd_per1 1 k x).const_mul _),
              pdCx_const_mul _ _ k x (hcd_per1 0 k x), pdCx_const_mul _ _ k x (hcd_per1 1 k x),
              hpd_per _ ((hGood 0).fderiv_apply (B0579.dir k)) k x,
              hpd_per _ ((hGood 1).fderiv_apply (B0579.dir k)) k x]
            have hsc : ‖((Real.sqrt (clockA ν ρ)⁻¹ : ℝ) : ℂ)‖ ≤ 1 := by
              rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), Real.sqrt_inv]
              exact ha_inv_sqrt
            have h0 : ‖((perGram κ (dd ν ρ))⁻¹ i 0 * ((Real.sqrt (clockA ν ρ)⁻¹ : ℝ) : ℂ)) *
                (((Real.sqrt (clockA ν ρ)⁻¹ : ℝ) : ℂ) *
                  LamJetInf.perPhys ν c
                    (fun z => fderiv ℝ (fun z' => fderiv ℝ (κ.lamP 0) z' (B0579.dir k)) z (B0579.dir k))
                    (ρ, x))‖ ≤ M_G * B2 0 k := by
              rw [norm_mul, norm_mul, norm_mul]
              calc ‖(perGram κ (dd ν ρ))⁻¹ i 0‖ * ‖((Real.sqrt (clockA ν ρ)⁻¹ : ℝ) : ℂ)‖ *
                    (‖((Real.sqrt (clockA ν ρ)⁻¹ : ℝ) : ℂ)‖ * ‖_‖)
                  ≤ M_G * 1 * (1 * B2 0 k) :=
                    mul_le_mul (mul_le_mul (hGinv ρ hρ_Icc 0) hsc (norm_nonneg _) hM_G0)
                      (mul_le_mul hsc (hB2_le 0 k ρ hρ_Icc x hx) (norm_nonneg _) zero_le_one)
                      (by positivity) (by positivity)
                _ = M_G * B2 0 k := by ring
            have h1 : ‖((perGram κ (dd ν ρ))⁻¹ i 1 * ((Real.sqrt (clockA ν ρ)⁻¹ : ℝ) : ℂ)) *
                (((Real.sqrt (clockA ν ρ)⁻¹ : ℝ) : ℂ) *
                  LamJetInf.perPhys ν c
                    (fun z => fderiv ℝ (fun z' => fderiv ℝ (κ.lamP 1) z' (B0579.dir k)) z (B0579.dir k))
                    (ρ, x))‖ ≤ M_G * B2 1 k := by
              rw [norm_mul, norm_mul, norm_mul]
              calc ‖(perGram κ (dd ν ρ))⁻¹ i 1‖ * ‖((Real.sqrt (clockA ν ρ)⁻¹ : ℝ) : ℂ)‖ *
                    (‖((Real.sqrt (clockA ν ρ)⁻¹ : ℝ) : ℂ)‖ * ‖_‖)
                  ≤ M_G * 1 * (1 * B2 1 k) :=
                    mul_le_mul (mul_le_mul (hGinv ρ hρ_Icc 1) hsc (norm_nonneg _) hM_G0)
                      (mul_le_mul hsc (hB2_le 1 k ρ hρ_Icc x hx) (norm_nonneg _) zero_le_one)
                      (by positivity) (by positivity)
                _ = M_G * B2 1 k := by ring
            calc ‖_ + _‖ ≤ _ + _ := norm_add_le _ _
              _ ≤ M_G * B2 0 k + M_G * B2 1 k := add_le_add h0 h1
              _ = M_G * (B2 0 k + B2 1 k) := by ring
          unfold ladLapCx
          calc ‖pdCx 0 (pdCx 0 (physFrameLam κ ν ρ i)) x +
                pdCx 1 (pdCx 1 (physFrameLam κ ν ρ i)) x‖
              ≤ ‖pdCx 0 (pdCx 0 (physFrameLam κ ν ρ i)) x‖ +
                ‖pdCx 1 (pdCx 1 (physFrameLam κ ν ρ i)) x‖ := norm_add_le _ _
            _ ≤ M_G * (B2 0 0 + B2 1 0) + M_G * (B2 0 1 + B2 1 1) :=
                add_le_add (hpd2_bd 0) (hpd2_bd 1)
            _ = B_lap := by ring
        calc ‖ladDt (fun r' x' => physFrameLam κ ν r' i x') ρ x +
              (ν : ℂ) * ladLapCx (physFrameLam κ ν ρ i) x‖
            ≤ ‖ladDt (fun r' x' => physFrameLam κ ν r' i x') ρ x‖ +
              ‖(ν : ℂ)‖ * ‖ladLapCx (physFrameLam κ ν ρ i) x‖ := by
                rw [← norm_mul]; exact norm_add_le _ _
          _ ≤ B_dt + |ν| * B_lap := by
              rw [Complex.norm_real, Real.norm_eq_abs]
              exact add_le_add hdt_bd (mul_le_mul_of_nonneg_left hlap_bd (abs_nonneg ν))
      have hMain_mem :=
        memLp_and_xNorm_cell_bdd_of_cont (m := m) (by linarith) (by positivity) hMain_cont hMain_bd
      have hTr_mem : MemLp (ladTransport tr ρ (physFrameLam κ ν ρ i)) 2 (B0579.cellMeasure c (-m)) ∧
          xNorm c (-m) (ladTransport tr ρ (physFrameLam κ ν ρ i)) ≤ ENNReal.ofReal (W_c * B_tr) := by
        have hv_cd : ContDiff ℝ ∞ (tr.v ρ) := UnforcedLeray.B0238.contDiff_Vc tr hρ0
        have hv_cont : ∀ k : Fin 2, Continuous (fun x => tr.v ρ x k) := fun k =>
          ((EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hv_cd).continuous
        have hTr_cont : Continuous (ladTransport tr ρ (physFrameLam κ ν ρ i)) := by
          have hsum_tr : ladTransport tr ρ (physFrameLam κ ν ρ i) =
              fun x => ((tr.v ρ x 0 : ℝ) : ℂ) * pdCx 0 (physFrameLam κ ν ρ i) x +
                ((tr.v ρ x 1 : ℝ) : ℂ) * pdCx 1 (physFrameLam κ ν ρ i) x := by
            funext x; unfold ladTransport; rfl
          rw [hsum_tr]
          exact ((Complex.continuous_ofReal.comp (hv_cont 0)).mul
              (RateSplitAux.contDiff_pdCx hslice 0).continuous).add
            ((Complex.continuous_ofReal.comp (hv_cont 1)).mul
              (RateSplitAux.contDiff_pdCx hslice 1).continuous)
        refine memLp_and_xNorm_cell_bdd_of_cont (by linarith) (by positivity) hTr_cont fun x hx => ?_
        have hpd_pt : ∀ k : Fin 2, ‖pdCx k (physFrameLam κ ν ρ i) x‖ ≤ B_g := by
          intro k
          have ha_inv_sqrt : (Real.sqrt (clockA ν ρ))⁻¹ ≤ 1 :=
            inv_le_one_of_one_le₀ (by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (one_le_clockA hν.le hρ0))
          have hcd_lam : ∀ j : Fin 2, Differentiable ℝ (fun x' => LamJetInf.perPhys ν c (κ.lamP j) (ρ, x')) := by
            intro j x'
            have hd := ((LamJetInf.contDiffOn_perPhys hν hc0.ne' (hGood j)).differentiableOn
              (by simp)).differentiableAt ((LamJetInf.isOpen_physU ν).mem_nhds
                (show (ρ, x') ∈ LamJetInf.physU ν from ha_r))
            exact hd.comp x' (differentiableAt_const ρ |>.prodMk differentiableAt_id)
          have hsum_fn : physFrameLam κ ν ρ i = fun x' =>
              (perGram κ (dd ν ρ))⁻¹ i 0 * LamJetInf.perPhys ν c (κ.lamP 0) (ρ, x') +
              (perGram κ (dd ν ρ))⁻¹ i 1 * LamJetInf.perPhys ν c (κ.lamP 1) (ρ, x') := by
            funext x'
            rw [physFrameLam_eq_sum_perGram_inv κ ν ρ i x', Fin.sum_univ_two,
              physFrameLam0_eq_perSum_physAdj κ hν hρ0 0 x',
              physFrameLam0_eq_perSum_physAdj κ hν hρ0 1 x']
            rfl
          have hpd_per : ∀ j : Fin 2,
              pdCx k (fun x' => LamJetInf.perPhys ν c (κ.lamP j) (ρ, x')) x =
                ((Real.sqrt (clockA ν ρ)⁻¹ : ℝ) : ℂ) *
                  LamJetInf.perPhys ν c (fun z => fderiv ℝ (κ.lamP j) z (B0579.dir k)) (ρ, x) := by
            intro j
            have hd := ((LamJetInf.contDiffOn_perPhys hν hc0.ne' (hGood j)).differentiableOn
              (by simp)).differentiableAt ((LamJetInf.isOpen_physU ν).mem_nhds
                (show (ρ, x) ∈ LamJetInf.physU ν from ha_r))
            have hfd : pdCx k (fun x' => LamJetInf.perPhys ν c (κ.lamP j) (ρ, x')) x =
                fderiv ℝ (LamJetInf.perPhys ν c (κ.lamP j)) (ρ, x) (0, B0579.dir k) := by
              unfold pdCx
              have hcomp : HasFDerivAt (fun x' => LamJetInf.perPhys ν c (κ.lamP j) (ρ, x'))
                  ((fderiv ℝ (LamJetInf.perPhys ν c (κ.lamP j)) (ρ, x)).comp
                    (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) x :=
                hd.hasFDerivAt.comp x (hasFDerivAt_const ρ x |>.prodMk (hasFDerivAt_id x))
              rw [hcomp.fderiv]; rfl
            rw [hfd, LamJetInf.fderiv_perPhys_apply hν hc0.ne' (hGood j) ha_r]
            simp only [mul_zero, zero_mul, Complex.ofReal_zero, zero_add, Real.sqrt_inv]
            congr 2
            field_simp [(Real.sqrt_pos.2 ha_r).ne']
            rw [Real.sq_sqrt ha_r.le]
          rw [hsum_fn, RateSplitAux.pdCx_add k ((hcd_lam 0 x).const_mul _) ((hcd_lam 1 x).const_mul _),
            pdCx_const_mul _ _ k x (hcd_lam 0 x), pdCx_const_mul _ _ k x (hcd_lam 1 x),
            hpd_per 0, hpd_per 1]
          have hnorm0 : ‖((Real.sqrt (clockA ν ρ)⁻¹ : ℝ) : ℂ) *
              LamJetInf.perPhys ν c (fun z => fderiv ℝ (κ.lamP 0) z (B0579.dir k)) (ρ, x)‖ ≤
              max (B1 0 0) (B1 0 1) := by
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), Real.sqrt_inv]
            calc (Real.sqrt (clockA ν ρ))⁻¹ * _
                ≤ 1 * B1 0 k := mul_le_mul ha_inv_sqrt (hB1_le 0 k ρ hρ_Icc x hx) (norm_nonneg _) zero_le_one
              _ ≤ max (B1 0 0) (B1 0 1) := by fin_cases k <;> simp
          have hnorm1 : ‖((Real.sqrt (clockA ν ρ)⁻¹ : ℝ) : ℂ) *
              LamJetInf.perPhys ν c (fun z => fderiv ℝ (κ.lamP 1) z (B0579.dir k)) (ρ, x)‖ ≤
              max (B1 1 0) (B1 1 1) := by
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), Real.sqrt_inv]
            calc (Real.sqrt (clockA ν ρ))⁻¹ * _
                ≤ 1 * B1 1 k := mul_le_mul ha_inv_sqrt (hB1_le 1 k ρ hρ_Icc x hx) (norm_nonneg _) zero_le_one
              _ ≤ max (B1 1 0) (B1 1 1) := by fin_cases k <;> simp
          calc ‖(perGram κ (dd ν ρ))⁻¹ i 0 * _ + (perGram κ (dd ν ρ))⁻¹ i 1 * _‖
              ≤ ‖(perGram κ (dd ν ρ))⁻¹ i 0‖ * ‖_‖ + ‖(perGram κ (dd ν ρ))⁻¹ i 1‖ * ‖_‖ :=
                (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
            _ ≤ M_G * max (B1 0 0) (B1 0 1) + M_G * max (B1 1 0) (B1 1 1) :=
                add_le_add (mul_le_mul (hGinv ρ hρ_Icc 0) hnorm0 (norm_nonneg _) hM_G0)
                  (mul_le_mul (hGinv ρ hρ_Icc 1) hnorm1 (norm_nonneg _) hM_G0)
            _ = B_g := by ring
        unfold ladTransport
        have hv0 : ‖((tr.v ρ x 0 : ℝ) : ℂ)‖ ≤ C_tr := by
          rw [Complex.norm_real, Real.norm_eq_abs]; exact (hBdd ρ hρS x hx).1 0
        have hv1 : ‖((tr.v ρ x 1 : ℝ) : ℂ)‖ ≤ C_tr := by
          rw [Complex.norm_real, Real.norm_eq_abs]; exact (hBdd ρ hρS x hx).1 1
        calc ‖((tr.v ρ x 0 : ℝ) : ℂ) * pdCx 0 (physFrameLam κ ν ρ i) x +
              ((tr.v ρ x 1 : ℝ) : ℂ) * pdCx 1 (physFrameLam κ ν ρ i) x‖
            ≤ ‖((tr.v ρ x 0 : ℝ) : ℂ)‖ * ‖pdCx 0 (physFrameLam κ ν ρ i) x‖ +
              ‖((tr.v ρ x 1 : ℝ) : ℂ)‖ * ‖pdCx 1 (physFrameLam κ ν ρ i) x‖ :=
              (norm_add_le _ _).trans (by rw [norm_mul, norm_mul])
          _ ≤ C_tr * B_g + C_tr * B_g :=
              add_le_add (mul_le_mul hv0 (hpd_pt 0) (norm_nonneg _) hC_tr0)
                (mul_le_mul hv1 (hpd_pt 1) (norm_nonneg _) hC_tr0)
          _ = B_tr := by ring
      obtain ⟨hMainTr_mem, hMainTr_x⟩ :=
        ComplCouplingHeat.memLp_and_xNorm_add_le (by positivity) (by positivity)
          hMain_mem.1 hTr_mem.1 hMain_mem.2 hTr_mem.2
      have hDual_eq : physLamDual κ tr ρ i =
          fun x => (ladDt (fun r' x' => physFrameLam κ ν r' i x') ρ x +
              (ν : ℂ) * ladLapCx (physFrameLam κ ν ρ i) x +
              ladTransport tr ρ (physFrameLam κ ν ρ i) x) -
            kerAdj c (fun k y => physFrameLam κ ν ρ i y *
              ((B0579.pd k (UnforcedLeray.B0238.Ec tr ρ) y : ℝ) : ℂ)) x := rfl
      rw [hDual_eq]
      refine ⟨hMainTr_mem.sub hKer.1.1, ?_⟩
      refine (eLpNorm_sub_le hMainTr_mem.1 hKer.1.1.1 one_le_two).trans
        ((add_le_add hMainTr_x hKer.1.2).trans (le_of_eq ?_))
      rw [← ENNReal.ofReal_add (by positivity) hM_ker0]
      congr 1
      ring
    set F_u : ℝ := Fe.toReal
    have hF_u0 : 0 ≤ F_u := ENNReal.toReal_nonneg
    set M_rate : ℝ := A_w * (M_ND + M_ker) + F_u * M_φ +
      (3 * |ν| * K_cut + 2 * C_tr * K_cut) * (A_w * M_φ + 2 * (A_w * M_g))
    have hTendsto_and_bd : ∀ ρ ∈ Ioo t₁ t₂,
        (∀ R : ℝ, 1 ≤ R → ‖ladRate tr w u φ R ρ‖ ≤ M_rate) ∧
        Tendsto (fun R : ℝ => ladRate tr w u φ R ρ) atTop (𝓝 (g_lim ρ)) := by
      intro ρ hρ
      have hρ_Icc : ρ ∈ Icc t₁ t₂ := Ioo_subset_Icc_self hρ
      have hρ0 : 0 ≤ ρ := ht₁.trans hρ_Icc.1
      have hρS : ρ ∈ Icc (0 : ℝ) t₂ := ⟨hρ0, hρ_Icc.2⟩
      have hv : ∀ x ∈ B0579.cell c, ∀ j : Fin 2, |tr.v ρ x j| ≤ C_tr :=
        fun x hx j => (hBdd ρ hρS x hx).1 j
      have hw_mem := hw.memX ρ hρ_Icc.1
      have hw_norm := hA_w ρ hρ_Icc
      obtain ⟨hforce_mem, hforce_norm⟩ := hforce ρ hρ_Icc
      obtain ⟨hLam_mem, hLam_x⟩ := hLam_Ico ρ (Ioo_subset_Ico_self hρ)
      obtain ⟨hDual_mem, hDual_x⟩ := hDual_bd ρ hρ
      have hφ_mem : MemLp (φ ρ) 2 (B0579.cellMeasure c (-m)) := hLam_mem
      have hφ_norm : (xNorm c (-m) (φ ρ)).toReal ≤ M_φ :=
        ENNReal.toReal_le_of_le_ofReal hM_φ0 hLam_x
      have hND_norm : (xNorm c (-m) (physLamDual κ tr ρ i)).toReal ≤ M_ND :=
        ENNReal.toReal_le_of_le_ofReal hM_ND0 hDual_x
      have hgrad_mem : ∀ k : Fin 2, MemLp (pdCx k (φ ρ)) 2 (B0579.cellMeasure c (-m)) :=
        fun k => (hpd_bd ρ hρ k).1
      have hgrad_norm : ∀ k : Fin 2, (xNorm c (-m) (pdCx k (φ ρ))).toReal ≤ M_g :=
        fun k => ENNReal.toReal_le_of_le_ofReal hM_g0 (hpd_bd ρ hρ k).2
      have hKer := hKerAll hρS hLam_mem hLam_x
      have hKer_mem := hKer.1.1
      have hKer_norm : (xNorm c (-m) (kerAdj c (fun k y => φ ρ y *
          ((B0579.pd k (UnforcedLeray.B0238.Ec tr ρ) y : ℝ) : ℂ)))).toReal ≤ M_ker :=
        ENNReal.toReal_le_of_le_ofReal hM_ker0 hKer.1.2
      have hchi_eq : ladChi tr φ ρ = fun x => physLamDual κ tr ρ i x +
          kerAdj c (fun k y => φ ρ y * ((B0579.pd k (UnforcedLeray.B0238.Ec tr ρ) y : ℝ) : ℂ)) x := by
        funext x; unfold ladChi physLamDual; ring
      have hχ_mem : MemLp (ladChi tr φ ρ) 2 (B0579.cellMeasure c (-m)) := by
        rw [hchi_eq]; exact hDual_mem.add hKer_mem
      have hχ_norm : (xNorm c (-m) (ladChi tr φ ρ)).toReal ≤ M_ND + M_ker := by
        rw [hchi_eq]
        have hadd_x := eLpNorm_add_le hDual_mem.1 hKer_mem.1 one_le_two
        have hto : (xNorm c (-m) (fun x => physLamDual κ tr ρ i x +
              kerAdj c (fun k y => φ ρ y * ((B0579.pd k (UnforcedLeray.B0238.Ec tr ρ) y : ℝ) : ℂ)) x)).toReal ≤
            (xNorm c (-m) (physLamDual κ tr ρ i)).toReal +
              (xNorm c (-m) (kerAdj c (fun k y => φ ρ y *
                ((B0579.pd k (UnforcedLeray.B0238.Ec tr ρ) y : ℝ) : ℂ)))).toReal := by
          calc _ ≤ (xNorm c (-m) (physLamDual κ tr ρ i) +
                xNorm c (-m) (kerAdj c (fun k y => φ ρ y *
                  ((B0579.pd k (UnforcedLeray.B0238.Ec tr ρ) y : ℝ) : ℂ)))).toReal :=
                ENNReal.toReal_mono
                  (ENNReal.add_ne_top.2 ⟨hDual_mem.eLpNorm_ne_top, hKer_mem.eLpNorm_ne_top⟩) hadd_x
            _ = _ := ENNReal.toReal_add hDual_mem.eLpNorm_ne_top hKer_mem.eLpNorm_ne_top
        linarith
      obtain ⟨hcomm_bd, hcomm_lim⟩ := ladComm_bound_and_vanish hc0 hC_tr0 hA_w0 hM_φ0 hM_g0
        hv hw_mem hw_norm hφ_mem hφ_norm hgrad_mem hgrad_norm hK_cut0
        (fun R hR => (hK_cut R hR).2.2.2.2.1) (fun R hR => (hK_cut R hR).2.2.2.2.2)
      refine ⟨fun R hR1 => ?_, ?_⟩
      · have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR1
        rw [ladRateSplit ν c m tr t₁ t₂ f w u φ hc0 ht₁ ht₁t₂ hw hSmooth R hR0 ρ hρ]
        have hcut := hK_cut R hR0
        have hcont : Continuous (ladCut R) := (hcut.1 c).continuous
        have hcb : ∀ x, |ladCut R x| ≤ 1 := fun x => by
          rw [abs_of_nonneg (hcut.2.1 x).1]; exact (hcut.2.1 x).2
        have ea : ‖∫ x in B0579.cell c, w ρ x * ((ladCut R x : ℂ) * ladChi tr φ ρ x)‖ ≤
            A_w * (M_ND + M_ker) :=
          (RateBoundAux.cs_cut c m hcont hcb hw_mem hχ_mem).trans
            (mul_le_mul hw_norm hχ_norm ENNReal.toReal_nonneg hA_w0)
        have eb : ‖∫ x in B0579.cell c, ladForce tr (u ρ) ρ x * ladCutPhi φ R ρ x‖ ≤
            F_u * M_φ :=
          (RateBoundAux.cs_cut c m hcont hcb hforce_mem hφ_mem).trans
            (mul_le_mul hforce_norm hφ_norm ENNReal.toReal_nonneg hF_u0)
        have ec := hcomm_bd R hR1
        have hsub := norm_add_le
          ((∫ x in B0579.cell c, w ρ x * ((ladCut R x : ℂ) * ladChi tr φ ρ x)) -
            ∫ x in B0579.cell c, ladForce tr (u ρ) ρ x * ladCutPhi φ R ρ x)
          (ladComm tr w φ R ρ)
        have hsub2 := norm_sub_le
          (∫ x in B0579.cell c, w ρ x * ((ladCut R x : ℂ) * ladChi tr φ ρ x))
          (∫ x in B0579.cell c, ladForce tr (u ρ) ρ x * ladCutPhi φ R ρ x)
        unfold M_rate
        linarith [hsub, hsub2, ea, eb, ec]
      · have hsplit_ev : (fun R : ℝ => ladRate tr w u φ R ρ) =ᶠ[atTop] fun R : ℝ =>
            (∫ x in B0579.cell c, w ρ x * ((ladCut R x : ℂ) * ladChi tr φ ρ x)) -
              (∫ x in B0579.cell c, ladForce tr (u ρ) ρ x * ladCutPhi φ R ρ x) +
                ladComm tr w φ R ρ :=
          Filter.eventually_atTop.2 ⟨1, fun R hR =>
            ladRateSplit ν c m tr t₁ t₂ f w u φ hc0 ht₁ ht₁t₂ hw hSmooth R (by linarith) ρ hρ⟩
        have hlim1 := ladCutLimit c m (w ρ) (ladChi tr φ ρ) hw_mem hχ_mem
        have hlim2 : Tendsto (fun R : ℝ => ∫ x in B0579.cell c,
            ladForce tr (u ρ) ρ x * ladCutPhi φ R ρ x) atTop
            (𝓝 (∫ x in B0579.cell c, ladForce tr (u ρ) ρ x * φ ρ x)) := by
          have hcut_eq : ∀ R, (fun x => ladForce tr (u ρ) ρ x * ladCutPhi φ R ρ x) =
              fun x => ladForce tr (u ρ) ρ x * ((ladCut R x : ℂ) * φ ρ x) := by
            intro R; funext x; unfold ladCutPhi; rfl
          simp_rw [hcut_eq]
          exact ladCutLimit c m (ladForce tr (u ρ) ρ) (φ ρ) hforce_mem hφ_mem
        have hTransp : ∫ x in B0579.cell c, w ρ x *
              kerAdj c (fun k y => φ ρ y * ((B0579.pd k (UnforcedLeray.B0238.Ec tr ρ) y : ℝ) : ℂ)) x =
            ∫ x in B0579.cell c, ladForce tr (u ρ) ρ x * φ ρ x := by
          have hz_ρ : HasZeroCirculation c (w ρ) :=
            ladFlowZeroCirc m (by linarith) ν c tr t₁ f w u hc1 hf0 hw ρ hρ_Icc.1
          exact hKer.2 (w ρ) (u ρ) hw_mem hz_ρ (hw.biotSavart ρ hρ_Icc.1)
        have hlim_sub : (∫ x in B0579.cell c, w ρ x * ladChi tr φ ρ x) -
            (∫ x in B0579.cell c, ladForce tr (u ρ) ρ x * φ ρ x) + 0 = g_lim ρ := by
          have hi1 := CommVanishAux.integrableOn_cell_norm_mul c m hw_mem hDual_mem
          have hi2 := CommVanishAux.integrableOn_cell_norm_mul c m hw_mem hKer_mem
          have hm1 : IntegrableOn (fun x => w ρ x * physLamDual κ tr ρ i x) (B0579.cell c) :=
            hi1.mono' ((hw_mem.1.mono_ac (B0579.ac_cellMeasure c m)).mul
              (hDual_mem.1.mono_ac (B0579.ac_cellMeasure c (-m))))
              (Filter.Eventually.of_forall fun x => by rw [norm_mul])
          have hm2 : IntegrableOn (fun x => w ρ x *
              kerAdj c (fun k y => φ ρ y * ((B0579.pd k (UnforcedLeray.B0238.Ec tr ρ) y : ℝ) : ℂ)) x)
              (B0579.cell c) :=
            hi2.mono' ((hw_mem.1.mono_ac (B0579.ac_cellMeasure c m)).mul
              (hKer_mem.1.mono_ac (B0579.ac_cellMeasure c (-m))))
              (Filter.Eventually.of_forall fun x => by rw [norm_mul])
          have hfn : (fun x => w ρ x * ladChi tr φ ρ x) =
              fun x => w ρ x * physLamDual κ tr ρ i x +
                w ρ x * kerAdj c (fun k y => φ ρ y *
                  ((B0579.pd k (UnforcedLeray.B0238.Ec tr ρ) y : ℝ) : ℂ)) x := by
            funext x; rw [hchi_eq, mul_add]
          rw [hfn, integral_add hm1 hm2, hTransp,
            FrameAmplSub.physLamDual_pairing_eq_movH0 κ hν hρ0 tr w i]
          dsimp [g_lim]
          ring
        rw [← hlim_sub]
        exact ((hlim1.sub hlim2).add hcomm_lim).congr' hsplit_ev.symm
    intro r' hr'
    rcases eq_or_lt_of_le hr'.1 with rfl | ht₁r'
    · rw [sub_self, Ioc_self, Measure.restrict_empty, integral_zero_measure]
    have hprod_r' := fun R (hR : 0 < R) =>
      ladProductRule ν c m tr t₁ t₂ f w u φ hν hc0 ht₁ ht₁t₂ hw ⟨Cl, hCl⟩
        hSmooth hφ_per R hR r' hr'
    have hI : Ι t₁ r' = Ioc t₁ r' := Set.uIoc_of_le hr'.1
    have hlimInt : Tendsto (fun R : ℝ => ∫ ρ in t₁..r', ladRate tr w u φ R ρ) atTop
        (𝓝 (∫ ρ in t₁..r', g_lim ρ)) := by
      refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        (μ := volume) (l := atTop) (f := g_lim)
        (F := fun R ρ => ladRate tr w u φ R ρ) (fun _ => M_rate) ?_ ?_
        intervalIntegrable_const ?_
      · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
        exact (intervalIntegrable_iff.mp (hprod_r' R hR).1).aestronglyMeasurable
      · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
        refine Filter.Eventually.of_forall fun ρ hρI => ?_
        rw [hI] at hρI
        exact (hTendsto_and_bd ρ ⟨hρI.1, lt_of_le_of_lt hρI.2 hr'.2⟩).1 R hR
      · refine Filter.Eventually.of_forall fun ρ hρI => ?_
        rw [hI] at hρI
        exact (hTendsto_and_bd ρ ⟨hρI.1, lt_of_le_of_lt hρI.2 hr'.2⟩).2
    have hcut_r' : Tendsto (fun R : ℝ => ladCutPair c R w φ r') atTop (𝓝 (ladPair c w φ r')) :=
      ladCutLimit c m (w r') (φ r') (hw.memX r' hr'.1) (hLam_Ico r' hr').1
    have hcut_t1 : Tendsto (fun R : ℝ => ladCutPair c R w φ t₁) atTop (𝓝 (ladPair c w φ t₁)) :=
      ladCutLimit c m (w t₁) (φ t₁) (hw.memX t₁ le_rfl) (hLam_Ico t₁ ⟨le_rfl, ht₁t₂⟩).1
    have hdiff_lim : Tendsto (fun R : ℝ => ladCutPair c R w φ r' - ladCutPair c R w φ t₁) atTop
        (𝓝 (∫ ρ in t₁..r', g_lim ρ)) :=
      hlimInt.congr' (by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
        exact ((hprod_r' R hR).2).symm)
    have heq_pair : ladPair c w φ r' - ladPair c w φ t₁ = ∫ ρ in t₁..r', g_lim ρ :=
      tendsto_nhds_unique (hcut_r'.sub hcut_t1) hdiff_lim
    unfold ladPair at heq_pair
    dsimp only [c, φ] at heq_pair
    rw [← FrameAmplSub.ampl_eq_phys_pairing κ hν (ht₁.trans hr'.1) hF w i,
      ← FrameAmplSub.ampl_eq_phys_pairing κ hν ht₁ hF w i,
      intervalIntegral.integral_of_le hr'.1] at heq_pair
    exact heq_pair
  -- Step 2: extend from `Ico t₁ t₂` to `Icc t₁ t₂` by continuity and subtract at `s'` and `r`
  have hg_int : IntegrableOn g_lim (Ioc t₁ t₂) :=
    Leaf2WeakEqAmplInt.integrableOn_amplRate κ hκ hm hν hb hF tr htr hBddAll ht₁
      ⟨ht12, le_rfl⟩ hbt₂ hw hf0 i
  have hd1_all : ∀ q ∈ Icc t₁ t₂, 1 ≤ cellLen c (clockA ν q) := fun q hq =>
    dd_ge_one_of_theta hν hb (ht₁.trans hq.1) (hbt₂.trans (theta_anti hν (ht₁.trans hq.1) hq.2))
  have hdet_all := Leaf2RegularAux.perGram_det_ne_zero_of_facts κ hν ht₁ hbt₂ hF
  have hL_cont : ContinuousOn (fun q => ampl F w q i - ampl F w t₁ i) (Icc t₁ t₂) :=
    (FlowMeas.continuousOn_ampl' κ hm hν ht₁ ht12 hbt₂ hF hd1_all hdet_all hw i).sub
      continuousOn_const
  have hR_cont : ContinuousOn (fun q => ∫ τ in Ioc t₁ q, g_lim τ) (Icc t₁ t₂) :=
    continuousOn_indef_Ioc ht12 hg_int
  have hIcc : ∀ q ∈ Icc t₁ t₂, ampl F w q i - ampl F w t₁ i = ∫ τ in Ioc t₁ q, g_lim τ := by
    intro q hq
    rcases eq_or_lt_of_le hq.2 with hq_eq | hqt₂
    · rw [hq_eq]
      let seq : ℕ → ℝ := fun n => t₂ - (t₂ - t₁) / ((n : ℝ) + 2)
      have hseq_Ico : ∀ n : ℕ, seq n ∈ Ico t₁ t₂ := by
        intro n
        have hn0 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
        have hn1 : (1 : ℝ) < (n : ℝ) + 2 := by linarith
        have hdiv_pos : 0 < (t₂ - t₁) / ((n : ℝ) + 2) := div_pos (sub_pos.2 ht₁t₂) hn0
        have hdiv_lt : (t₂ - t₁) / ((n : ℝ) + 2) < t₂ - t₁ := div_lt_self (sub_pos.2 ht₁t₂) hn1
        exact ⟨by dsimp [seq]; linarith, by dsimp [seq]; linarith⟩
      have hseq_lim : Tendsto seq atTop (𝓝 t₂) := by
        have h0 : Tendsto (fun n : ℕ => (t₂ - t₁) / ((n : ℝ) + 2)) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop
            (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
        simpa [seq] using tendsto_const_nhds.sub h0
      have hseq_nhds : Tendsto seq atTop (𝓝[Icc t₁ t₂] t₂) :=
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within seq hseq_lim
          (Filter.Eventually.of_forall fun n => Ico_subset_Icc_self (hseq_Ico n))
      have hL_lim := (hL_cont t₂ ⟨ht12, le_rfl⟩).tendsto.comp hseq_nhds
      have hR_lim := (hR_cont t₂ ⟨ht12, le_rfl⟩).tendsto.comp hseq_nhds
      exact tendsto_nhds_unique hL_lim (hR_lim.congr fun n => (hIco (seq n) (hseq_Ico n)).symm)
    · exact hIco q ⟨hq.1, hqt₂⟩
  have hs'_Icc : s' ∈ Icc t₁ t₂ := ⟨hr.1.trans hs'.1, hs'.2⟩
  have h1 := hIcc s' hs'_Icc
  have h2 := hIcc r hr
  have hi_t1_r : IntervalIntegrable g_lim volume t₁ r :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hr.1).2
      (hg_int.mono_set (Ioc_subset_Ioc_right hr.2))
  have hi_r_s' : IntervalIntegrable g_lim volume r s' :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hs'.1).2
      (hg_int.mono_set (Ioc_subset_Ioc hr.1 hs'.2))
  have hadj : (∫ τ in Ioc t₁ r, g_lim τ) + (∫ τ in Ioc r s', g_lim τ) =
      ∫ τ in Ioc t₁ s', g_lim τ := by
    rw [← intervalIntegral.integral_of_le hr.1, ← intervalIntegral.integral_of_le hs'.1,
      ← intervalIntegral.integral_of_le hs'_Icc.1]
    exact intervalIntegral.integral_add_adjacent_intervals hi_t1_r hi_r_s'
  linear_combination h1 - h2 - hadj

end Leaf2RepAux

/-! ### 3. Main assembly of `ComplDuhamelRep` -/

theorem complDuhamelRep (κ : PlanarFrameKernels) (P : PlanarData) (ν m b K : ℝ) (hν : 0 < ν)
    (hF : PerFrameFacts κ ν m b K)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t₁ t₂ C_loc C_H0 : ℝ) :
    UnforcedLeray.Short.IIIa.ComplFreeRateSub.ComplDuhamelRep κ P ν m b K hν hF tr t₁ t₂
      C_loc C_H0 := by
  intro hSeed hP hm hb htr ht₁ h12 hbt₂ f w u U hU hAvail hFlow hCirc hInt hH0 s hs
  have hm0 : 0 ≤ m := by linarith
  let F := periodizedFrame κ ν m b K hν hF
  let S := complSource κ P F tr w
  obtain ⟨hSrcMem, hRegS⟩ :=
    complSourceRegular κ P ν m b K hν hF tr t₁ t₂ C_loc C_H0
      (complForcingMeasurable κ P ν m b K hν hF tr t₁ t₂)
      hSeed hP hm hb htr ht₁ h12 hbt₂ f w u U hU hAvail hFlow hCirc hInt hH0
  obtain ⟨hm1, G, hGe, hm2⟩ := hRegS s hs
  refine ⟨hm1, G, hGe, hm2, fun hfin => ?_⟩
  -- `A := compl F w s` and `B := U s t₁ (compl F w t₁) + ∫ r in Ioc t₁ s, G r ·` lie in `X_{m, dd ν s}`
  have hbs : b ≤ clockTheta ν s := hbt₂.trans (theta_anti hν (ht₁.trans hs.1) hs.2)
  have hbt₁ : b ≤ clockTheta ν t₁ := hbt₂.trans (theta_anti hν ht₁ h12)
  have hA_mem : MemLp (compl F w s) 2 (B0579.cellMeasure (dd ν s) m) :=
    memLp_compl F hm0 hν ht₁ hs.1 hbs hFlow
  have hWt₁_mem : MemLp (compl F w t₁) 2 (B0579.cellMeasure (dd ν t₁) m) :=
    memLp_compl F hm0 hν ht₁ le_rfl hbt₁ hFlow
  have hB1_mem : MemLp (U s t₁ (compl F w t₁)) 2 (B0579.cellMeasure (dd ν s) m) :=
    ⟨hm1, lt_of_le_of_lt (hU.1 t₁ s le_rfl hs.1 hs.2 (compl F w t₁))
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hWt₁_mem.2)⟩
  have hSF : SFinite (B0579.cellMeasure (dd ν s) m) := by
    unfold B0579.cellMeasure; infer_instance
  have hSG : SigmaFinite (B0579.cellMeasure (dd ν s) m) := by
    unfold B0579.cellMeasure; infer_instance
  have hint_aesm : AEStronglyMeasurable (fun y => ∫ r in Ioc t₁ s, G r y)
      (B0579.cellMeasure (dd ν s) m) :=
    hm2.prod_swap.integral_prod_right' (ν := volume.restrict (Ioc t₁ s))
  have hint_xNorm : xNorm (dd ν s) m (fun y => ∫ r in Ioc t₁ s, G r y) ≤
      ∫⁻ r in Ioc t₁ s, xNorm (dd ν s) m (G r) :=
    UnforcedLeray.PlanarBS.Conv.eLpNorm_integral_le
      (μ := B0579.cellMeasure (dd ν s) m) (ν := volume.restrict (Ioc t₁ s))
      (F := fun y r => G r y) hm2.prod_swap (p := 2) (by norm_num) (by norm_num)
  have hB2_mem : MemLp (fun y => ∫ r in Ioc t₁ s, G r y) 2 (B0579.cellMeasure (dd ν s) m) :=
    ⟨hint_aesm, lt_of_le_of_lt hint_xNorm (lt_top_iff_ne_top.2 hfin)⟩
  have hB_mem : MemLp (fun y => U s t₁ (compl F w t₁) y + ∫ r in Ioc t₁ s, G r y) 2
      (B0579.cellMeasure (dd ν s) m) := hB1_mem.add hB2_mem
  -- Auxiliary hypotheses for `complWeakEq`
  have hν1 : ν ≤ 1 := Leaf2RepAux.nu_le_one_of_theta hν hb (ht₁.trans h12) hbt₂
  have hc1 : 1 ≤ ν ^ (-2 : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by norm_num)
  have hBddAll : ∀ S' : ℝ, 0 ≤ S' → ∃ C : ℝ, LadTrainBdd tr m S' C :=
    fun S' hS' => Leaf2RepAux.ladTrainBdd_of_buc hν hc1 tr htr m S' hS'
  have hForceFin := Leaf2RegularAux.forceFinite_of hSeed P hν hm hb hF htr ht₁ h12 hbt₂
  have hAmplFTC := Leaf2RepAux.amplFTC_unconditional κ hSeed hm hν hb hF tr htr hBddAll
    ht₁ h12 hbt₂ hFlow hCirc
  -- Compare pairings against every `Γ ∈ X_{-m, dd ν s}` via `dualUniq`
  refine dualUniq (dd ν s) m (compl F w s)
    (fun y => U s t₁ (compl F w t₁) y + ∫ r in Ioc t₁ s, G r y) hA_mem hB_mem fun Γ hΓ => ?_
  obtain ⟨Φ, hΦ_adj, hΦ_dual⟩ :=
    freeMovingDuality ν m tr t₁ t₂ hm hν ht₁ h12 htr U hU hAvail s hs Γ hΓ
  let μ_t : Measure ℝ := volume.restrict (Ioc t₁ s)
  let μ_y : Measure (ℝ × ℝ) := volume.restrict (B0579.cell (dd ν s))
  -- Product absolute continuity `μ_t.prod μ_y ≪ μ_t.prod (cellMeasure (dd ν s) m)`
  have hac_prod : μ_t.prod μ_y ≪ μ_t.prod (B0579.cellMeasure (dd ν s) m) := by
    refine Measure.AbsolutelyContinuous.mk fun E hE hE0 => ?_
    rw [Measure.prod_apply hE] at hE0 ⊢
    have hae0 : ∀ᵐ r ∂μ_t, B0579.cellMeasure (dd ν s) m (Prod.mk r ⁻¹' E) = 0 :=
      (lintegral_eq_zero_iff (measurable_measure_prodMk_left hE)).1 hE0
    refine lintegral_eq_zero_iff (measurable_measure_prodMk_left hE) |>.2 ?_
    filter_upwards [hae0] with r hr0
    exact B0579.ac_cellMeasure (dd ν s) m hr0
  have hG_aesm_prod : AEStronglyMeasurable (Function.uncurry G) (μ_t.prod μ_y) :=
    hm2.mono_ac hac_prod
  have hΓ_aesm_prod : AEStronglyMeasurable (fun p : ℝ × (ℝ × ℝ) => Γ p.2) (μ_t.prod μ_y) :=
    (hΓ.1.mono_ac (B0579.ac_cellMeasure (dd ν s) (-m))).comp_snd
  have hProd_aesm : AEStronglyMeasurable (fun p : ℝ × (ℝ × ℝ) => G p.1 p.2 * Γ p.2)
      (μ_t.prod μ_y) := hG_aesm_prod.mul hΓ_aesm_prod
  -- Slice `AEStronglyMeasurable` and weighted Cauchy-Schwarz bound for `r ∈ Ioc t₁ s`
  have hGr_aesm : ∀ r ∈ Ioc t₁ s, AEStronglyMeasurable (G r) (B0579.cellMeasure (dd ν s) m) := by
    intro r hr
    have hSr_mem := hSrcMem r ⟨hr.1.le, hr.2.trans hs.2⟩
    have hUsr_aesm : AEStronglyMeasurable (U s r (S r)) (B0579.cellMeasure (dd ν s) m) :=
      hU.2.2.2.2 r s hr.1.le hr.2 hs.2 (S r) hSr_mem
    exact (hUsr_aesm.const_mul (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ)).congr (hGe r hr).symm
  have hProd_fin : HasFiniteIntegral (fun p : ℝ × (ℝ × ℝ) => G p.1 p.2 * Γ p.2)
      (μ_t.prod μ_y) := by
    rw [HasFiniteIntegral, lintegral_prod _ hProd_aesm.enorm]
    have hslice_le : ∀ r ∈ Ioc t₁ s,
        (∫⁻ y, ‖G r y * Γ y‖ₑ ∂μ_y) ≤ xNorm (dd ν s) m (G r) * xNorm (dd ν s) (-m) Γ := by
      intro r hr
      have hcs := _root_.weightedCS (dd ν s) m Γ (fun y => ‖G r y‖)
        hΓ.1 (hGr_aesm r hr).norm
      rw [eLpNorm_norm] at hcs
      have heq : (∫⁻ y, ‖G r y * Γ y‖ₑ ∂μ_y) = ∫⁻ y, ‖Γ y‖ₑ * ‖‖G r y‖‖ₑ ∂μ_y := by
        congr 1; funext y; rw [enorm_mul, enorm_norm, mul_comm]
      rw [heq, mul_comm (xNorm (dd ν s) m (G r))]
      exact hcs
    calc (∫⁻ r, ∫⁻ y, ‖G r y * Γ y‖ₑ ∂μ_y ∂μ_t)
        ≤ ∫⁻ r, xNorm (dd ν s) m (G r) * xNorm (dd ν s) (-m) Γ ∂μ_t :=
          setLIntegral_mono' measurableSet_Ioc hslice_le
      _ = (∫⁻ r in Ioc t₁ s, xNorm (dd ν s) m (G r)) * xNorm (dd ν s) (-m) Γ :=
          lintegral_mul_const' (xNorm (dd ν s) (-m) Γ) (fun r => xNorm (dd ν s) m (G r)) hΓ.2.ne
      _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hfin) hΓ.2
  have hProdInt : Integrable (fun p : ℝ × (ℝ × ℝ) => G p.1 p.2 * Γ p.2) (μ_t.prod μ_y) :=
    ⟨hProd_aesm, hProd_fin⟩
  -- Identify each `r`-slice pairing with `a(r)⁻² * ⟨S r, Φ r⟩`
  have hSliceEq : ∀ r ∈ Ioc t₁ s,
      (∫ y in B0579.cell (dd ν s), G r y * Γ y) =
        (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) *
          ∫ y in B0579.cell (dd ν r), S r y * Φ r y := by
    intro r hr
    have hae_y : (fun y => G r y * Γ y) =ᵐ[μ_y]
        fun y => (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) * (U s r (S r) y * Γ y) := by
      filter_upwards [(B0579.ac_cellMeasure (dd ν s) m).ae_le (hGe r hr)] with y hy
      rw [hy, mul_assoc]
    rw [show (∫ y in B0579.cell (dd ν s), G r y * Γ y) = ∫ y, G r y * Γ y ∂μ_y from rfl,
      integral_congr_ae hae_y, integral_const_mul]
    congr 1
    exact hΦ_dual r ⟨hr.1.le, hr.2⟩ (S r) (hSrcMem r ⟨hr.1.le, hr.2.trans hs.2⟩)
  -- Time integrability for `complWeakEq`
  have hG_timeInt : IntegrableOn (fun r => ∫ y in B0579.cell (dd ν s), G r y * Γ y) (Ioc t₁ s) :=
    hProdInt.integral_prod_left
  have hWeakTimeInt : IntegrableOn (fun r => (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) *
      ∫ y in B0579.cell (dd ν r), S r y * Φ r y) (Ioc t₁ s) :=
    hG_timeInt.congr_fun hSliceEq measurableSet_Ioc
  -- Apply `complWeakEq` to compute `⟨compl F w s, Γ⟩`
  have hLHS := complWeakEq κ P ν m b K hν hF tr t₁ t₂ C_loc C_H0
    hSeed hP hm hb htr ht₁ h12 hbt₂ hBddAll hForceFin f w u hFlow hCirc hAmplFTC hInt hH0
    s hs Γ Φ hΓ hΦ_adj hWeakTimeInt
  -- Compute `⟨B, Γ⟩` via Fubini and `freeMovingDuality`
  have hB1_int : IntegrableOn (fun y => U s t₁ (compl F w t₁) y * Γ y) (B0579.cell (dd ν s)) :=
    (Leaf2DualityNeeded.pair_bound hB1_mem hΓ).1
  have hB2_int : IntegrableOn (fun y => (∫ r in Ioc t₁ s, G r y) * Γ y) (B0579.cell (dd ν s)) :=
    (Leaf2DualityNeeded.pair_bound hB2_mem hΓ).1
  have hFubini : (∫ y in B0579.cell (dd ν s), (∫ r in Ioc t₁ s, G r y) * Γ y) =
      ∫ r in Ioc t₁ s, (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) *
        ∫ y in B0579.cell (dd ν r), S r y * Φ r y := by
    have hmul_in : (∫ y in B0579.cell (dd ν s), (∫ r in Ioc t₁ s, G r y) * Γ y) =
        ∫ y, (∫ r, G r y * Γ y ∂μ_t) ∂μ_y := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      exact (integral_mul_const (Γ y) (fun r => G r y)).symm
    rw [hmul_in, ← integral_prod_symm _ hProdInt, integral_prod _ hProdInt]
    exact setIntegral_congr_fun measurableSet_Ioc hSliceEq
  have hRHS : (∫ y in B0579.cell (dd ν s),
      (U s t₁ (compl F w t₁) y + ∫ r in Ioc t₁ s, G r y) * Γ y) =
      (∫ y in B0579.cell (dd ν t₁), compl F w t₁ y * Φ t₁ y) +
        ∫ r in Ioc t₁ s, (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) *
          ∫ y in B0579.cell (dd ν r), S r y * Φ r y := by
    have hadd_fn : (fun y => (U s t₁ (compl F w t₁) y + ∫ r in Ioc t₁ s, G r y) * Γ y) =
        fun y => U s t₁ (compl F w t₁) y * Γ y + (∫ r in Ioc t₁ s, G r y) * Γ y := by
      funext y; ring
    rw [hadd_fn, integral_add hB1_int hB2_int,
      hΦ_dual t₁ ⟨le_rfl, hs.1⟩ (compl F w t₁) hWt₁_mem, hFubini]
  exact hLHS.trans hRHS.symm

end ComplFreeRateSub

end UnforcedLeray.Short.IIIa
