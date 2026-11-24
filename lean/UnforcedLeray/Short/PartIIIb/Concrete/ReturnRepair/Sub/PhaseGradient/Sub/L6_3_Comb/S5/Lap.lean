import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_3_Comb.S5.YGrad

/-!
# `gkerLapInt` (`PartIII-b:C/rep/2/6/3/5/2`)

Source `the November 2 reference manuscript` 3603-3626, 3631-3646, 3800-3807,
4171-4200.  Same scheme as `gkerYGradInt`, with two `y`-derivatives: the `(h,z)`-integrand equals
`-(l/2) · ∂_a∂_a sepPhi(l,z)(y)` with `l = e^{-h/2}`, which is dominated by `(l/2) · sepMajorant _ _ _ 2`
through `sepGapPointwise` at order `2`.  The kernel side uses `D³K[e_a,e_a,e_k]`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Second derivative of a (`C²`) function `f` in directions `w` (outer) and `v` (inner). -/
theorem fderivApply2_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Space → F) (hf : ContDiff ℝ 2 f) (x v w : Space) :
    fderiv ℝ (fun x' => fderiv ℝ f x' w) x v = iteratedFDeriv ℝ 2 f x ![v, w] := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
  rw [(hd.hasFDerivAt.clm_apply (hasFDerivAt_const w x)).fderiv]
  rw [iteratedFDeriv_two_apply]
  simp

/-- Third-order identity: `∂_a ∂_a ∂_k K` as `D³K[e_a,e_a,e_k]`. -/
theorem K3_eq (t : ℝ) (ht : 0 < t) (i j k a : Fin 3) (x0 : Space) :
    fderiv ℝ (fun x => fderiv ℝ (fun x' => fderiv ℝ (fun x'' => IIIa.heatLerayK t i j x'') x'
        (UnforcedLeray.coordinateVector k)) x (UnforcedLeray.coordinateVector a)) x0
        (UnforcedLeray.coordinateVector a) =
      iteratedFDeriv ℝ 3 (fun x => IIIa.heatLerayK t i j x) x0
        ![UnforcedLeray.coordinateVector a, UnforcedLeray.coordinateVector a,
          UnforcedLeray.coordinateVector k] := by
  have hK : ContDiff ℝ 3 (fun x => IIIa.heatLerayK t i j x) := heatLerayKSmooth _ ht i j
  have hc : ContDiff ℝ 2 (fderiv ℝ (fun x => IIIa.heatLerayK t i j x)) :=
    hK.fderiv_right (m := 2) (by norm_num)
  have hg : ContDiff ℝ 2 (fun x' => fderiv ℝ (fun x => IIIa.heatLerayK t i j x) x'
      (UnforcedLeray.coordinateVector k)) :=
    hc.clm_apply contDiff_const
  rw [fderivApply2_eq _ hg, iteratedFDeriv_clm_apply_const_apply hc le_rfl,
    iteratedFDeriv_succ_apply_right (𝕜 := ℝ) (f := fun x => IIIa.heatLerayK t i j x) (n := 2)]
  have hinit : Fin.init ![UnforcedLeray.coordinateVector a, UnforcedLeray.coordinateVector a,
      UnforcedLeray.coordinateVector k] =
      ![UnforcedLeray.coordinateVector a, UnforcedLeray.coordinateVector a] := by
    funext i
    fin_cases i <;> rfl
  rw [hinit]
  rfl

/-- `(h,z)`-integrand `∂_a∂_a ∂_k K` of the `y`-Hessian, `0` at `h ≤ 0`. -/
def gkerLapD (ν : ℝ) (y : Space) (i j k a : Fin 3) (p : ℝ × Space) : ℝ :=
  if 0 < ν * (1 - Real.exp (-p.1)) then
    iteratedFDeriv ℝ 3 (fun x => IIIa.heatLerayK (ν * (1 - Real.exp (-p.1))) i j x)
      (y - Real.exp (-p.1 / 2) • p.2)
      ![UnforcedLeray.coordinateVector a, UnforcedLeray.coordinateVector a,
        UnforcedLeray.coordinateVector k]
  else 0

theorem gkerLapD_measurable (ν : ℝ) (y : Space) (i j k a : Fin 3) :
    Measurable (gkerLapD ν y i j k a) := by
  have hJ : HeatLerayJointMeas :=
    heatLerayJointMeas_of (heatLerayScale_of heatGTailScale) heatLerayKSmooth
  have hq : Measurable (fun p : ℝ × Space =>
      (ν * (1 - Real.exp (-p.1)), y - Real.exp (-p.1 / 2) • p.2)) := by
    fun_prop
  have hA := (hJ i j 3 (by norm_num)).comp_measurable hq
  have hc : Continuous (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Space) ℝ =>
      A ![UnforcedLeray.coordinateVector a, UnforcedLeray.coordinateVector a,
        UnforcedLeray.coordinateVector k]) := continuous_eval_const _
  have hm := (hc.comp_stronglyMeasurable hA).measurable
  convert hm using 1
  funext p
  simp only [gkerLapD, Function.comp]
  split_ifs <;> simp_all

/-- Derivative of `y ↦ ∂_v g(y - c)` (real `C²` function `g`). -/
theorem hasFDerivAt_shift_fderiv (G : Space → ℝ) (hG : ContDiff ℝ 2 G) (c y v : Space) :
    HasFDerivAt (fun y' => fderiv ℝ G (y' - c) v)
      (fderiv ℝ (fun x => fderiv ℝ G x v) (y - c)) y := by
  have hd : DifferentiableAt ℝ (fun x => fderiv ℝ G x v) (y - c) :=
    (((hG.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
      (by norm_num)) _
  have h1 : HasFDerivAt (fun y' : Space => y' - c) (ContinuousLinearMap.id ℝ Space) y :=
    (hasFDerivAt_id y).sub_const c
  have h2 := hd.hasFDerivAt.comp y h1
  have h3 : HasFDerivAt (fun y' => fderiv ℝ G (y' - c) v)
      ((fderiv ℝ (fun x => fderiv ℝ G x v) (y - c)).comp (ContinuousLinearMap.id ℝ Space)) y := h2
  rwa [ContinuousLinearMap.comp_id] at h3

/-- Second `y`-derivative of the `Gker` kernel in direction `e_a` (chain rule twice). -/
theorem gker_fderiv_dir2 (ν : ℝ) (m : ℂ) (h : ℝ) (hh : 0 < h) (hν : 0 < ν) (y z : Space)
    (i j k a : Fin 3) :
    fderiv ℝ (fun y'' => fderiv ℝ (fun y''' => Gker ν m h y''' z i j k) y''
        (UnforcedLeray.coordinateVector a)) y (UnforcedLeray.coordinateVector a) =
      Complex.exp (-(m + 3 / 2) * (h : ℂ)) * ((gkerLapD ν y i j k a (h, z) : ℝ) : ℂ) := by
  have ht : 0 < ν * (1 - Real.exp (-h)) := by
    have : Real.exp (-h) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    exact mul_pos hν (by linarith)
  have hG : ContDiff ℝ 2 (fun x : Space =>
      fderiv ℝ (fun x' => IIIa.heatLerayK (ν * (1 - Real.exp (-h))) i j x') x
        (UnforcedLeray.coordinateVector k)) :=
    ((heatLerayKSmooth _ ht i j).fderiv_right (by norm_num)).clm_apply contDiff_const
  have hfun : (fun y'' => fderiv ℝ (fun y''' => Gker ν m h y''' z i j k) y''
        (UnforcedLeray.coordinateVector a)) =
      fun y'' => Complex.exp (-(m + 3 / 2) * (h : ℂ)) *
        ((fderiv ℝ (fun x => fderiv ℝ (fun x' => IIIa.heatLerayK (ν * (1 - Real.exp (-h))) i j x') x
          (UnforcedLeray.coordinateVector k)) (y'' - Real.exp (-h / 2) • z)
          (UnforcedLeray.coordinateVector a) : ℝ) : ℂ) := by
    funext y''
    exact gker_fderiv_dir ν m h hh hν y'' z (UnforcedLeray.coordinateVector a) i j k
  rw [hfun]
  have hD := Complex.ofRealCLM.hasFDerivAt.comp y
    (hasFDerivAt_shift_fderiv _ hG (Real.exp (-h / 2) • z) y (UnforcedLeray.coordinateVector a))
  have h4 := hD.const_mul (Complex.exp (-(m + 3 / 2) * (h : ℂ)))
  have h5 : HasFDerivAt (fun y'' : Space => Complex.exp (-(m + 3 / 2) * (h : ℂ)) *
      ((fderiv ℝ (fun x => fderiv ℝ (fun x' => IIIa.heatLerayK (ν * (1 - Real.exp (-h))) i j x') x
          (UnforcedLeray.coordinateVector k)) (y'' - Real.exp (-h / 2) • z)
          (UnforcedLeray.coordinateVector a) : ℝ) : ℂ))
      (Complex.exp (-(m + 3 / 2) * (h : ℂ)) • (Complex.ofRealCLM.comp
        (fderiv ℝ (fun x => fderiv ℝ (fun x' => fderiv ℝ (fun x'' =>
            IIIa.heatLerayK (ν * (1 - Real.exp (-h))) i j x'') x' (UnforcedLeray.coordinateVector k)) x
            (UnforcedLeray.coordinateVector a)) (y - Real.exp (-h / 2) • z)))) y := h4
  rw [h5.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, Complex.ofRealCLM_apply, smul_eq_mul]
  unfold gkerLapD
  dsimp only
  rw [if_pos ht, K3_eq _ ht i j k a]

/-- The `(h,z)`-integrand of the `y`-Hessian as a sum over `j,k`. -/
def gkerHL (ν : ℝ) (m : ℂ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (i : Fin 3)
    (y : Space) (a : Fin 3) (p : ℝ × Space) : ℂ :=
  ∑ j : Fin 3, ∑ k : Fin 3, Complex.exp (-(m + 3 / 2) * (p.1 : ℂ)) *
    ((gkerLapD ν y i j k a p : ℝ) : ℂ) * ((T (τ - p.1) p.2 j k : ℝ) : ℂ)

theorem gkerHL_measurable (ν : ℝ) (m : ℂ) (P rOut : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hT : IIIa.IsSepSource P rOut T) (τ : ℝ) (i : Fin 3) (y : Space) (a : Fin 3) :
    Measurable (gkerHL ν m T τ i y a) := by
  unfold gkerHL
  refine Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun k _ => ?_
  refine ((Complex.continuous_exp.measurable.comp ?_).mul
    (Complex.measurable_ofReal.comp (gkerLapD_measurable ν y i j k a))).mul
      (Complex.measurable_ofReal.comp ?_)
  · exact (by fun_prop : Continuous fun p : ℝ × Space => -(m + 3 / 2) * (p.1 : ℂ)).measurable
  · exact (hT.measurable j k).comp (by fun_prop : Measurable fun p : ℝ × Space => (τ - p.1, p.2))

theorem gkerLap_sum_eq (ν : ℝ) (m : ℂ) (hν : 0 < ν) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (τ : ℝ) (i : Fin 3) (y z : Space) (a : Fin 3) (h : ℝ) (hh : 0 < h) :
    ∑ j : Fin 3, ∑ k : Fin 3, fderiv ℝ (fun y'' => fderiv ℝ (fun y''' => Gker ν m h y''' z i j k) y''
        (UnforcedLeray.coordinateVector a)) y (UnforcedLeray.coordinateVector a) *
      ((T (τ - h) z j k : ℝ) : ℂ) = gkerHL ν m T τ i y a (h, z) := by
  unfold gkerHL
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [gker_fderiv_dir2 ν m h hh hν y z i j k a]


/-- Second `y`-derivative of `sepPhi` in direction `e_a` (chain rule through the explicit formula). -/
theorem sepPhi_deriv2 (ν : ℝ) (μ : ℂ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ)
    (i : Fin 3) (l : ℝ) (z y : Space) (a : Fin 3) (hν : 0 < ν) (hl : l ∈ Ioo (0 : ℝ) 1) :
    fderiv ℝ (fun y' => fderiv ℝ (sepPhi ν μ T τ i (l, z)) y' (UnforcedLeray.coordinateVector a))
        y (UnforcedLeray.coordinateVector a) =
      -2 * (l : ℂ) ^ (2 * μ + 2) * ∑ j : Fin 3, ∑ k : Fin 3,
        ((fderiv ℝ (fun x => fderiv ℝ (fun x' => fderiv ℝ (fun x'' =>
            IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x'') x' (UnforcedLeray.coordinateVector k)) x
            (UnforcedLeray.coordinateVector a)) (y - l • z) (UnforcedLeray.coordinateVector a) : ℝ) : ℂ) *
          ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ) := by
  have ht : 0 < ν * (1 - l ^ 2) := by
    have := hl.1; have := hl.2; nlinarith [mul_pos hν (sub_pos.2 (show l ^ 2 < 1 by nlinarith))]
  have hG : ∀ j k : Fin 3, ContDiff ℝ 2 (fun x' : Space =>
      fderiv ℝ (fun x'' => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x'') x'
        (UnforcedLeray.coordinateVector k)) :=
    fun j k => ((heatLerayKSmooth _ ht i j).fderiv_right (by norm_num)).clm_apply contDiff_const
  have hfun : (fun y' => fderiv ℝ (sepPhi ν μ T τ i (l, z)) y' (UnforcedLeray.coordinateVector a)) =
      fun y' => -2 * (l : ℂ) ^ (2 * μ + 2) * ∑ j : Fin 3, ∑ k : Fin 3,
        ((fderiv ℝ (fun x' => fderiv ℝ (fun x'' => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x'') x'
          (UnforcedLeray.coordinateVector k)) (y' - l • z) (UnforcedLeray.coordinateVector a) : ℝ) : ℂ) *
          ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ) := by
    funext y'
    exact sepPhi_fderiv_gen ν μ T τ i l z y' (UnforcedLeray.coordinateVector a) hν hl
  rw [hfun]
  have hH : ∀ j k : Fin 3, HasFDerivAt (fun y' : Space =>
      ((fderiv ℝ (fun x' => fderiv ℝ (fun x'' => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x'') x'
          (UnforcedLeray.coordinateVector k)) (y' - l • z) (UnforcedLeray.coordinateVector a) : ℝ) : ℂ) *
        ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ))
      (((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ) • (Complex.ofRealCLM.comp (fderiv ℝ (fun x : Space =>
        fderiv ℝ (fun x' => fderiv ℝ (fun x'' => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x'') x'
          (UnforcedLeray.coordinateVector k)) x (UnforcedLeray.coordinateVector a))
          (y - l • z)))) y := by
    intro j k
    have h3 := Complex.ofRealCLM.hasFDerivAt.comp y
      (hasFDerivAt_shift_fderiv _ (hG j k) (l • z) y (UnforcedLeray.coordinateVector a))
    have h4 := h3.mul_const ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ)
    refine h4.congr_fderiv ?_
    ext w
    simp [mul_comm]
  have hS : HasFDerivAt (fun y' : Space => ∑ j : Fin 3, ∑ k : Fin 3,
      ((fderiv ℝ (fun x' => fderiv ℝ (fun x'' => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x'') x'
          (UnforcedLeray.coordinateVector k)) (y' - l • z) (UnforcedLeray.coordinateVector a) : ℝ) : ℂ) *
        ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ))
      (∑ j : Fin 3, ∑ k : Fin 3,
        (((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ) • (Complex.ofRealCLM.comp (fderiv ℝ (fun x : Space =>
          fderiv ℝ (fun x' => fderiv ℝ (fun x'' => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x'') x'
            (UnforcedLeray.coordinateVector k)) x (UnforcedLeray.coordinateVector a))
            (y - l • z))))) y :=
    HasFDerivAt.fun_sum fun j _ => HasFDerivAt.fun_sum fun k _ => hH j k
  have hF := hS.const_mul (-2 * (l : ℂ) ^ (2 * μ + 2))
  rw [hF.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/-- Pointwise identity for the `(h,z)`-integrand of the `y`-Hessian, `l = e^{-h/2}`. -/
theorem gkerHL_eq_sepPhi (ν : ℝ) (m : ℂ) (hν : 0 < ν) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (τ : ℝ) (i : Fin 3) (y z : Space) (a : Fin 3) (h : ℝ) (hh : 0 < h) :
    gkerHL ν m T τ i y a (h, z) =
      -((Real.exp (-h / 2) / 2 : ℝ) : ℂ) *
        fderiv ℝ (fun y' => fderiv ℝ (sepPhi ν m T τ i (Real.exp (-h / 2), z)) y'
          (UnforcedLeray.coordinateVector a)) y (UnforcedLeray.coordinateVector a) := by
  have hl : Real.exp (-h / 2) ∈ Ioo (0 : ℝ) 1 :=
    ⟨Real.exp_pos _, Real.exp_lt_one_iff.2 (by linarith)⟩
  have ht : 0 < ν * (1 - Real.exp (-h)) := by
    have : Real.exp (-h) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    exact mul_pos hν (by linarith)
  rw [sepPhi_deriv2 ν m T τ i _ z y a hν hl]
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
  have hD : ∀ j k : Fin 3, gkerLapD ν y i j k a (h, z) =
      fderiv ℝ (fun x => fderiv ℝ (fun x' => fderiv ℝ (fun x'' =>
          IIIa.heatLerayK (ν * (1 - Real.exp (-h))) i j x'') x'
          (UnforcedLeray.coordinateVector k)) x (UnforcedLeray.coordinateVector a))
        (y - Real.exp (-h / 2) • z) (UnforcedLeray.coordinateVector a) := by
    intro j k
    unfold gkerLapD
    dsimp only
    rw [if_pos ht, K3_eq _ ht i j k a]
  simp only [gkerHL, hD]
  rw [hE]
  simp only [mul_assoc, ← Finset.mul_sum]
  push_cast
  ring

/-- **`gkerLapInt` (`PartIII-b:C/rep/2/6/3/5/2`)**: joint integrability of the second
`y`-derivative kernel integrand on `(vol|_{(0,∞)}) ⊗ vol`. -/
theorem gkerLapInt : GkerLapInt := by
  intro ν m hν hm rOut P hr hP T hT hS τ y hy i a
  obtain ⟨ε, hε, C, hC0, hb⟩ :=
    sepGapPointwise IIIa.sepKernelBounds ν m rOut P T hν hm hr hP hT τ i y hy
  have hM : Integrable (sepMajorant m T τ 2) sepRho :=
    sepGapMajorantIntegrable m P rOut T hm hP hT hS τ 2 (by norm_num)
  have hgI : Integrable (gkerMajN m T τ 2) ((volume.restrict (Ioi (0 : ℝ))).prod volume) :=
    ⟨(gkerMajN_measurable m P rOut T hT τ 2).aestronglyMeasurable,
      gkerMajN_lintegral_lt_top m P rOut T hT τ 2 hM⟩
  have hHm : Measurable (gkerHL ν m T τ i y a) := gkerHL_measurable ν m P rOut T hT τ i y a
  have hae : ∀ᵐ p : ℝ × Space ∂((volume.restrict (Ioi (0 : ℝ))).prod volume), 0 < p.1 :=
    ae_pos_sepMeas
  have hFH : (fun p : ℝ × Space => kerIntegrandS T
      (fun h y' z i j k => fderiv ℝ (fun y'' => fderiv ℝ (fun y''' => Gker ν m h y''' z i j k) y''
        (UnforcedLeray.coordinateVector a)) y' (UnforcedLeray.coordinateVector a)) τ y i p) =ᵐ[sepMeas]
      gkerHL ν m T τ i y a := by
    filter_upwards [hae] with p hp
    exact gkerLap_sum_eq ν m hν T τ i y p.2 a p.1 hp
  have hHint : Integrable (gkerHL ν m T τ i y a) sepMeas := by
    refine Integrable.mono' (hgI.const_mul C) hHm.aestronglyMeasurable ?_
    filter_upwards [hae] with p hp
    show ‖gkerHL ν m T τ i y a p‖ ≤ C * gkerMajN m T τ 2 p
    have hl : Real.exp (-p.1 / 2) ∈ Ioo (0 : ℝ) 1 :=
      ⟨Real.exp_pos _, Real.exp_lt_one_iff.2 (by linarith)⟩
    have hn := hb y (Metric.mem_ball_self hε) _ hl p.2 2 le_rfl
    have hid : gkerHL ν m T τ i y a p = -((Real.exp (-p.1 / 2) / 2 : ℝ) : ℂ) *
        fderiv ℝ (fun y' => fderiv ℝ (sepPhi ν m T τ i (Real.exp (-p.1 / 2), p.2)) y'
          (UnforcedLeray.coordinateVector a)) y (UnforcedLeray.coordinateVector a) :=
      gkerHL_eq_sepPhi ν m hν T τ i y p.2 a p.1 hp
    rw [hid, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hsP : ContDiff ℝ 2 (sepPhi ν m T τ i (Real.exp (-p.1 / 2), p.2)) :=
      sepPhi_contDiff heatLerayKSmooth ν m T τ i _ _ hν hl
    have hbr : ‖fderiv ℝ (fun y' => fderiv ℝ (sepPhi ν m T τ i (Real.exp (-p.1 / 2), p.2)) y'
        (UnforcedLeray.coordinateVector a)) y (UnforcedLeray.coordinateVector a)‖ ≤
        ‖iteratedFDeriv ℝ 2 (sepPhi ν m T τ i (Real.exp (-p.1 / 2), p.2)) y‖ := by
      rw [fderivApply2_eq _ hsP]
      have hop := (iteratedFDeriv ℝ 2 (sepPhi ν m T τ i (Real.exp (-p.1 / 2), p.2)) y).le_opNorm
        ![UnforcedLeray.coordinateVector a, UnforcedLeray.coordinateVector a]
      have he : ‖UnforcedLeray.coordinateVector a‖ = 1 := by
        simp [UnforcedLeray.coordinateVector]
      simpa [Fin.prod_univ_two, he] using hop
    have hpos : 0 ≤ Real.exp (-p.1 / 2) / 2 := by positivity
    calc Real.exp (-p.1 / 2) / 2 * ‖fderiv ℝ (fun y' => fderiv ℝ
            (sepPhi ν m T τ i (Real.exp (-p.1 / 2), p.2)) y' (UnforcedLeray.coordinateVector a))
            y (UnforcedLeray.coordinateVector a)‖
        ≤ Real.exp (-p.1 / 2) / 2 * (C * sepMajorant m T τ 2 (Real.exp (-p.1 / 2), p.2)) :=
          mul_le_mul_of_nonneg_left (hbr.trans hn) hpos
      _ = C * gkerMajN m T τ 2 p := by simp only [gkerMajN]; ring
  exact hHint.congr hFH.symm

end UnforcedLeray.Short.PartIIIb.Concrete
