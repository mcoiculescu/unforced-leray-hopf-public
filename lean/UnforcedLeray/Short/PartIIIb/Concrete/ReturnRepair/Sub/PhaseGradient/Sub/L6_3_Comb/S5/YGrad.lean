import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_5
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2.L2.PhiDeriv
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L4
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L5
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_1_1_2_3.L1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_1_1_2_3.L2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_1_1_2_3.L3
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds

/-!
# `gkerYGradInt` (`PartIII-b:C/rep/2/6/3/5/1`)

Source `the November 2 reference manuscript` 3603-3626, 3631-3646, 3800-3807.
With `l = e^{-h/2}` the `(h,z)`-integrand of `kerIntegrandS` with `Φ = ∂_y Gker(·)(y)` equals
`-(l/2) · D_y sepPhi(l,z)(y)(y)`, which is dominated by `(l/2) · sepMajorant _ _ _ 1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Directional derivative of `sepPhi` in an arbitrary direction `v` (generalizes
`sepPhi_fderiv_apply`, which is the case `v = e_i`). -/
theorem sepPhi_fderiv_gen (ν : ℝ) (μ : ℂ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ)
    (i : Fin 3) (l : ℝ) (z y v : Space) (hν : 0 < ν) (hl : l ∈ Ioo (0 : ℝ) 1) :
    fderiv ℝ (sepPhi ν μ T τ i (l, z)) y v =
      -2 * (l : ℂ) ^ (2 * μ + 2) * ∑ j : Fin 3, ∑ k : Fin 3,
        ((fderiv ℝ (fun x => fderiv ℝ (fun x' => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x') x
          (coordinateVector k)) (y - l • z) v : ℝ) : ℂ) *
          ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ) := by
  have ht : 0 < ν * (1 - l ^ 2) := by
    have := hl.1; have := hl.2; nlinarith [mul_pos hν (sub_pos.2 (show l ^ 2 < 1 by nlinarith))]
  have hg : ∀ j k : Fin 3, ContDiff ℝ 2 (fun x : Space =>
      fderiv ℝ (fun x' => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x') x (coordinateVector k)) :=
    fun j k => ((heatLerayKSmooth _ ht i j).fderiv_right (by norm_num)).clm_apply contDiff_const
  have hH : ∀ j k : Fin 3, HasFDerivAt (fun y' : Space =>
      ((fderiv ℝ (fun x' => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x') (y' - l • z)
        (coordinateVector k) : ℝ) : ℂ) * ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ))
      (((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ) • (Complex.ofRealCLM.comp (fderiv ℝ (fun x : Space =>
        fderiv ℝ (fun x' => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x') x
          (coordinateVector k)) (y - l • z)))) y := by
    intro j k
    have h1 : HasFDerivAt (fun y' : Space => y' - l • z) (ContinuousLinearMap.id ℝ Space) y :=
      (hasFDerivAt_id y).sub_const (l • z)
    have h2 := ((hg j k).differentiable (by norm_num) (y - l • z)).hasFDerivAt.comp y h1
    have h3 := Complex.ofRealCLM.hasFDerivAt.comp y h2
    have h4 := h3.mul_const ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ)
    refine h4.congr_fderiv ?_
    ext w
    simp [mul_comm]
  have hS : HasFDerivAt (fun y' : Space => ∑ j : Fin 3, ∑ k : Fin 3,
      ((fderiv ℝ (fun x' => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x') (y' - l • z)
        (coordinateVector k) : ℝ) : ℂ) * ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ))
      (∑ j : Fin 3, ∑ k : Fin 3,
        (((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ) • (Complex.ofRealCLM.comp (fderiv ℝ
          (fun x : Space => fderiv ℝ (fun x' => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x') x
            (coordinateVector k)) (y - l • z))))) y :=
    HasFDerivAt.fun_sum fun j _ => HasFDerivAt.fun_sum fun k _ => hH j k
  have hF := hS.const_mul (-2 * (l : ℂ) ^ (2 * μ + 2))
  unfold sepPhi
  simp only
  rw [hF.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/-- Directional derivative of `y ↦ Gker` (chain rule for the translation `y ↦ y - e^{-h/2} z`). -/
theorem gker_fderiv_dir (ν : ℝ) (m : ℂ) (h : ℝ) (hh : 0 < h) (hν : 0 < ν) (y z v : Space)
    (i j k : Fin 3) :
    fderiv ℝ (fun y'' => Gker ν m h y'' z i j k) y v =
      Complex.exp (-(m + 3 / 2) * (h : ℂ)) *
        ((fderiv ℝ (fun x => fderiv ℝ (fun x' => IIIa.heatLerayK (ν * (1 - Real.exp (-h))) i j x') x
          (UnforcedLeray.coordinateVector k)) (y - Real.exp (-h / 2) • z) v : ℝ) : ℂ) := by
  have ht : 0 < ν * (1 - Real.exp (-h)) := by
    have : Real.exp (-h) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    exact mul_pos hν (by linarith)
  have hg : ContDiff ℝ 2 (fun x : Space =>
      fderiv ℝ (fun x' => IIIa.heatLerayK (ν * (1 - Real.exp (-h))) i j x') x
        (UnforcedLeray.coordinateVector k)) :=
    ((heatLerayKSmooth _ ht i j).fderiv_right (by norm_num)).clm_apply contDiff_const
  have h1 : HasFDerivAt (fun y' : Space => y' - Real.exp (-h / 2) • z)
      (ContinuousLinearMap.id ℝ Space) y :=
    (hasFDerivAt_id y).sub_const _
  have h2 := ((hg.differentiable (by norm_num)) (y - Real.exp (-h / 2) • z)).hasFDerivAt.comp y h1
  have h3 := Complex.ofRealCLM.hasFDerivAt.comp y h2
  have h4 := h3.const_mul (Complex.exp (-(m + 3 / 2) * (h : ℂ)))
  have key : fderiv ℝ (fun y'' => Gker ν m h y'' z i j k) y =
      Complex.exp (-(m + 3 / 2) * (h : ℂ)) • (Complex.ofRealCLM.comp
        ((fderiv ℝ (fun x => fderiv ℝ (fun x' => IIIa.heatLerayK (ν * (1 - Real.exp (-h))) i j x') x
          (UnforcedLeray.coordinateVector k)) (y - Real.exp (-h / 2) • z)).comp
          (ContinuousLinearMap.id ℝ Space))) := by
    unfold Gker
    exact h4.fderiv
  rw [key]
  simp

/-- Derivative in `y` of `∂_k K` at `x` in direction `v`, as the second Fréchet derivative. -/
theorem fderiv_fderiv_apply_eq (f : Space → ℝ) (hf : ContDiff ℝ 2 f) (x v w : Space) :
    fderiv ℝ (fun x' => fderiv ℝ f x' w) x v = iteratedFDeriv ℝ 2 f x ![v, w] := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
  rw [(hd.hasFDerivAt.clm_apply (hasFDerivAt_const w x)).fderiv]
  rw [iteratedFDeriv_two_apply]
  simp

/-- The `(h,z)`-integrand `∂_y² K` of the `y`-gradient (as an `iteratedFDeriv 2`), `0` at `h ≤ 0`. -/
def gkerYD (ν : ℝ) (y : Space) (i j k : Fin 3) (p : ℝ × Space) : ℝ :=
  if 0 < ν * (1 - Real.exp (-p.1)) then
    iteratedFDeriv ℝ 2 (fun x => IIIa.heatLerayK (ν * (1 - Real.exp (-p.1))) i j x)
      (y - Real.exp (-p.1 / 2) • p.2) ![y, UnforcedLeray.coordinateVector k]
  else 0

theorem gkerYD_eq (ν : ℝ) (h : ℝ) (z y : Space) (i j k : Fin 3) (hν : 0 < ν) (hh : 0 < h) :
    gkerYD ν y i j k (h, z) =
      fderiv ℝ (fun x => fderiv ℝ (fun x' => IIIa.heatLerayK (ν * (1 - Real.exp (-h))) i j x') x
        (UnforcedLeray.coordinateVector k)) (y - Real.exp (-h / 2) • z) y := by
  have ht : 0 < ν * (1 - Real.exp (-h)) := by
    have : Real.exp (-h) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    exact mul_pos hν (by linarith)
  have hf : ContDiff ℝ 2 (fun x' => IIIa.heatLerayK (ν * (1 - Real.exp (-h))) i j x') :=
    (heatLerayKSmooth _ ht i j).of_le (by norm_num)
  dsimp only [gkerYD]
  rw [if_pos ht, fderiv_fderiv_apply_eq _ hf]

/-- Measurability of `(h,z) ↦ ∂_y²K` on `(0,∞)×ℝ³`, from joint measurability of the kernel. -/
theorem gkerYD_measurable (ν : ℝ) (y : Space) (i j k : Fin 3) :
    Measurable (gkerYD ν y i j k) := by
  have hJ : HeatLerayJointMeas :=
    heatLerayJointMeas_of (heatLerayScale_of heatGTailScale) heatLerayKSmooth
  have hq : Measurable (fun p : ℝ × Space =>
      (ν * (1 - Real.exp (-p.1)), y - Real.exp (-p.1 / 2) • p.2)) := by
    fun_prop
  have hA := (hJ i j 2 (by norm_num)).comp_measurable hq
  have hc : Continuous (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Space) ℝ =>
      A ![y, UnforcedLeray.coordinateVector k]) := continuous_eval_const _
  have hm := (hc.comp_stronglyMeasurable hA).measurable
  convert hm using 1
  funext p
  simp only [gkerYD, Function.comp]
  split_ifs <;> simp_all

/-- The `(h,z)`-integrand of the `y`-gradient as a sum over `j,k`. -/
def gkerH (ν : ℝ) (m : ℂ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (i : Fin 3)
    (y : Space) (p : ℝ × Space) : ℂ :=
  ∑ j : Fin 3, ∑ k : Fin 3, Complex.exp (-(m + 3 / 2) * (p.1 : ℂ)) *
    ((gkerYD ν y i j k p : ℝ) : ℂ) * ((T (τ - p.1) p.2 j k : ℝ) : ℂ)

theorem gkerH_measurable (ν : ℝ) (m : ℂ) (P rOut : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hT : IIIa.IsSepSource P rOut T) (τ : ℝ) (i : Fin 3) (y : Space) :
    Measurable (gkerH ν m T τ i y) := by
  unfold gkerH
  refine Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun k _ => ?_
  refine ((Complex.continuous_exp.measurable.comp ?_).mul
    (Complex.measurable_ofReal.comp (gkerYD_measurable ν y i j k))).mul (Complex.measurable_ofReal.comp ?_)
  · exact (by fun_prop : Continuous fun p : ℝ × Space => -(m + 3 / 2) * (p.1 : ℂ)).measurable
  · exact (hT.measurable j k).comp (by fun_prop : Measurable fun p : ℝ × Space => (τ - p.1, p.2))

/-- Pointwise identity: the `(h,z)`-integrand equals `-(l/2) · D_y sepPhi(l,z)(y)(y)`, `l = e^{-h/2}`. -/
theorem gkerH_eq_sepPhi (ν : ℝ) (m : ℂ) (hν : 0 < ν) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (τ : ℝ) (i : Fin 3) (y z : Space) (h : ℝ) (hh : 0 < h) :
    gkerH ν m T τ i y (h, z) =
      -((Real.exp (-h / 2) / 2 : ℝ) : ℂ) *
        fderiv ℝ (sepPhi ν m T τ i (Real.exp (-h / 2), z)) y y := by
  have hl : Real.exp (-h / 2) ∈ Ioo (0 : ℝ) 1 :=
    ⟨Real.exp_pos _, Real.exp_lt_one_iff.2 (by linarith)⟩
  rw [sepPhi_fderiv_gen ν m T τ i _ z y y hν hl]
  have hsq : Real.exp (-h / 2) ^ 2 = Real.exp (-h) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hτ : τ + 2 * Real.log (Real.exp (-h / 2)) = τ - h := by
    rw [Real.log_exp]
    ring
  have hE : Complex.exp (-(m + 3 / 2) * (h : ℂ)) =
      ((Real.exp (-h / 2) : ℝ) : ℂ) ^ (2 * m + 2) * ((Real.exp (-h / 2) : ℝ) : ℂ) := by
    have hpow : ((Real.exp (-h / 2) : ℝ) : ℂ) ^ (2 * m + 2) =
        Complex.exp ((2 * m + 2) * ((-h / 2 : ℝ) : ℂ)) :=
      cpow_exp_real_h _ _
    rw [hpow, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hsq, hτ]
  have hD : ∀ j k : Fin 3, gkerYD ν y i j k (h, z) =
      fderiv ℝ (fun x => fderiv ℝ (fun x' => IIIa.heatLerayK (ν * (1 - Real.exp (-h))) i j x') x
        (UnforcedLeray.coordinateVector k)) (y - Real.exp (-h / 2) • z) y :=
    fun j k => gkerYD_eq ν h z y i j k hν hh
  simp only [gkerH, hD]
  rw [hE]
  simp only [mul_assoc, ← Finset.mul_sum]
  push_cast
  ring

/-- The `h`-majorant `(l/2) · sepMajorant (l,z)` for a general order `n`. -/
def gkerMajN (m : ℂ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (n : ℕ) (p : ℝ × Space) : ℝ :=
  Real.exp (-p.1 / 2) / 2 * sepMajorant m T τ n (Real.exp (-p.1 / 2), p.2)

theorem sepMajorant_measurable_n (m : ℂ) (P rOut : ℝ)
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (hT : IIIa.IsSepSource P rOut T) (τ : ℝ) (n : ℕ) :
    Measurable (sepMajorant m T τ n) := by
  have hTij : ∀ i j : Fin 3, Measurable (fun p : ℝ × Space => T (τ + 2 * Real.log p.1) p.2 i j) :=
    fun i j => (hT.measurable i j).comp
      (by fun_prop : Measurable fun p : ℝ × Space => (τ + 2 * Real.log p.1, p.2))
  have hTN : Measurable (fun p : ℝ × Space => IIIa.tensorNorm (T (τ + 2 * Real.log p.1) p.2)) := by
    unfold IIIa.tensorNorm
    exact Measurable.sqrt
      (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => (hTij i j).pow_const 2)
  unfold sepMajorant
  exact ((measurable_fst.pow_const _).mul
    ((measurable_const.add (measurable_fst.mul measurable_snd.norm)).pow_const _)).mul hTN

theorem gkerMajN_measurable (m : ℂ) (P rOut : ℝ)
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (hT : IIIa.IsSepSource P rOut T) (τ : ℝ) (n : ℕ) :
    Measurable (gkerMajN m T τ n) := by
  have hE : Measurable (fun p : ℝ × Space => (Real.exp (-p.1 / 2), p.2)) := by fun_prop
  unfold gkerMajN
  exact (by fun_prop : Measurable fun p : ℝ × Space => Real.exp (-p.1 / 2) / 2).mul
    ((sepMajorant_measurable_n m P rOut T hT τ n).comp hE)

theorem gkerMajN_lintegral_lt_top (m : ℂ) (P rOut : ℝ)
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (hT : IIIa.IsSepSource P rOut T) (τ : ℝ) (n : ℕ)
    (hM : Integrable (sepMajorant m T τ n) sepRho) :
    ∫⁻ p, ‖gkerMajN m T τ n p‖ₑ ∂((volume.restrict (Ioi (0 : ℝ))).prod volume) < ⊤ := by
  have hMm : Measurable (sepMajorant m T τ n) := sepMajorant_measurable_n m P rOut T hT τ n
  have hN : ∫⁻ l in Ioo (0 : ℝ) 1, ∫⁻ z, ‖sepMajorant m T τ n (l, z)‖ₑ < ⊤ := by
    have hfin := hM.2
    unfold HasFiniteIntegral sepRho at hfin
    rw [lintegral_prod _ hMm.enorm.aemeasurable] at hfin
    exact hfin
  have himg : (fun h : ℝ => Real.exp (-h / 2)) '' Ioi (0 : ℝ) = Ioo (0 : ℝ) 1 := by
    ext l
    constructor
    · rintro ⟨h, hh, rfl⟩
      refine ⟨Real.exp_pos _, ?_⟩
      rw [Real.exp_lt_one_iff]
      have : (0 : ℝ) < h := hh
      linarith
    · rintro ⟨hl0, hl1⟩
      refine ⟨-2 * Real.log l, ?_, ?_⟩
      · have : Real.log l < 0 := Real.log_neg hl0 hl1
        show (0 : ℝ) < -2 * Real.log l
        linarith
      · show Real.exp (-(-2 * Real.log l) / 2) = l
        rw [show -(-2 * Real.log l) / 2 = Real.log l by ring, Real.exp_log hl0]
  have hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun h : ℝ => Real.exp (-h / 2))
      (Real.exp (-x / 2) * (-1 / 2)) (Ioi 0) x := by
    intro x _
    have h1 : HasDerivAt (fun h : ℝ => -h / 2) (-1 / 2) x := by
      simpa using ((hasDerivAt_id x).neg).div_const 2
    exact (h1.exp).hasDerivWithinAt
  have hinj : InjOn (fun h : ℝ => Real.exp (-h / 2)) (Ioi 0) := by
    intro a _ b _ hab
    have := Real.exp_injective hab
    linarith
  have hcov := lintegral_image_eq_lintegral_abs_deriv_mul (f := fun h : ℝ => Real.exp (-h / 2))
    (f' := fun x : ℝ => Real.exp (-x / 2) * (-1 / 2)) measurableSet_Ioi hderiv hinj
    (fun l => ∫⁻ z, ‖sepMajorant m T τ n (l, z)‖ₑ)
  rw [himg] at hcov
  have habs : ∀ x : ℝ, |Real.exp (-x / 2) * (-1 / 2)| = Real.exp (-x / 2) / 2 := by
    intro x
    rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_div, abs_neg, abs_one, abs_two]
    ring
  have hmain : ∫⁻ p, ‖gkerMajN m T τ n p‖ₑ ∂((volume.restrict (Ioi (0 : ℝ))).prod volume)
      = ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-x / 2) / 2) *
          ∫⁻ z, ‖sepMajorant m T τ n (Real.exp (-x / 2), z)‖ₑ := by
    rw [lintegral_prod _ (gkerMajN_measurable m P rOut T hT τ n).enorm.aemeasurable]
    refine lintegral_congr fun h => ?_
    have hz : ∀ z : Space, ‖gkerMajN m T τ n (h, z)‖ₑ =
        ENNReal.ofReal (Real.exp (-h / 2) / 2) * ‖sepMajorant m T τ n (Real.exp (-h / 2), z)‖ₑ := by
      intro z
      simp only [gkerMajN]
      rw [enorm_mul, Real.enorm_eq_ofReal (by positivity)]
    simp only [hz]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  rw [hmain]
  calc ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-x / 2) / 2) *
          ∫⁻ z, ‖sepMajorant m T τ n (Real.exp (-x / 2), z)‖ₑ
      = ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (|Real.exp (-x / 2) * (-1 / 2)|) *
          ∫⁻ z, ‖sepMajorant m T τ n (Real.exp (-x / 2), z)‖ₑ := by
        refine lintegral_congr fun x => ?_
        rw [habs x]
    _ = ∫⁻ x in Ioo (0 : ℝ) 1, ∫⁻ z, ‖sepMajorant m T τ n (x, z)‖ₑ := hcov.symm
    _ < ⊤ := hN

theorem gker_sum_eq_gkerH (ν : ℝ) (m : ℂ) (hν : 0 < ν) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (τ : ℝ) (i : Fin 3) (y z : Space) (h : ℝ) (hh : 0 < h) :
    ∑ j : Fin 3, ∑ k : Fin 3, fderiv ℝ (fun y'' => Gker ν m h y'' z i j k) y y *
      ((T (τ - h) z j k : ℝ) : ℂ) = gkerH ν m T τ i y (h, z) := by
  unfold gkerH
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [gker_fderiv_dir ν m h hh hν y z y i j k, gkerYD_eq ν h z y i j k hν hh]

/-- **`gkerYGradInt` (`PartIII-b:C/rep/2/6/3/5/1`)**: joint integrability of the `y`-gradient
kernel integrand on `(vol|_{(0,∞)}) ⊗ vol`. -/
theorem gkerYGradInt : GkerYGradInt := by
  intro ν m hν hm rOut P hr hP T hT hS τ y hy i
  obtain ⟨ε, hε, C, hC0, hb⟩ :=
    sepGapPointwise IIIa.sepKernelBounds ν m rOut P T hν hm hr hP hT τ i y hy
  have hM : Integrable (sepMajorant m T τ 1) sepRho :=
    sepGapMajorantIntegrable m P rOut T hm hP hT hS τ 1 (by norm_num)
  have hgI : Integrable (gkerMajN m T τ 1) ((volume.restrict (Ioi (0 : ℝ))).prod volume) :=
    ⟨(gkerMajN_measurable m P rOut T hT τ 1).aestronglyMeasurable,
      gkerMajN_lintegral_lt_top m P rOut T hT τ 1 hM⟩
  have hHm : Measurable (gkerH ν m T τ i y) := gkerH_measurable ν m P rOut T hT τ i y
  have hae : ∀ᵐ p : ℝ × Space ∂((volume.restrict (Ioi (0 : ℝ))).prod volume), 0 < p.1 :=
    ae_pos_sepMeas
  have hFH : (fun p : ℝ × Space => kerIntegrandS T
      (fun h y' z i j k => fderiv ℝ (fun y'' => Gker ν m h y'' z i j k) y' y) τ y i p) =ᵐ[sepMeas]
      gkerH ν m T τ i y := by
    filter_upwards [hae] with p hp
    exact gker_sum_eq_gkerH ν m hν T τ i y p.2 p.1 hp
  have hHint : Integrable (gkerH ν m T τ i y) sepMeas := by
    refine Integrable.mono' (hgI.const_mul (C * ‖y‖)) hHm.aestronglyMeasurable ?_
    filter_upwards [hae] with p hp
    show ‖gkerH ν m T τ i y p‖ ≤ (C * ‖y‖) * gkerMajN m T τ 1 p
    have hl : Real.exp (-p.1 / 2) ∈ Ioo (0 : ℝ) 1 :=
      ⟨Real.exp_pos _, Real.exp_lt_one_iff.2 (by linarith)⟩
    have hn := hb y (Metric.mem_ball_self hε) _ hl p.2 1 (by norm_num)
    rw [norm_iteratedFDeriv_one] at hn
    have hid : gkerH ν m T τ i y p = -((Real.exp (-p.1 / 2) / 2 : ℝ) : ℂ) *
        fderiv ℝ (sepPhi ν m T τ i (Real.exp (-p.1 / 2), p.2)) y y :=
      gkerH_eq_sepPhi ν m hν T τ i y p.2 p.1 hp
    rw [hid, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hop := ContinuousLinearMap.le_opNorm
      (fderiv ℝ (sepPhi ν m T τ i (Real.exp (-p.1 / 2), p.2)) y) y
    have hpos : 0 ≤ Real.exp (-p.1 / 2) / 2 := by positivity
    calc Real.exp (-p.1 / 2) / 2 * ‖fderiv ℝ (sepPhi ν m T τ i (Real.exp (-p.1 / 2), p.2)) y y‖
        ≤ Real.exp (-p.1 / 2) / 2 * (C * sepMajorant m T τ 1 (Real.exp (-p.1 / 2), p.2) * ‖y‖) := by
          apply mul_le_mul_of_nonneg_left _ hpos
          exact hop.trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
      _ = (C * ‖y‖) * gkerMajN m T τ 1 p := by simp only [gkerMajN]; ring
  exact hHint.congr hFH.symm

end UnforcedLeray.Short.PartIIIb.Concrete
