import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.TaylorWidth.SepComm.Defs

/-!
# `PartIII-b:C/rep/8/1/1/2/5/2/1/3`: Order-2 difference bound `YBWidth.sepCommMainDiff2`

Source `the November 2 reference manuscript`
lines 5415-5427, SP 3735-3766. Proves `YBWidth.SepCommMainDiff2` on the transition annulus
`ν ≤ xo 0 ^ 2 + xo 1 ^ 2 ≤ 5 * ν / 4` by differentiating `sepW` and `sepVmu0` twice under the
integral sign (`L09.iteratedFDeriv_integral_eq`) and comparing their integrands at kernel
derivative order `j = 3` via `YBWidth.sepKernelDiffIter 3`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short.IIIa

namespace YBWidth

open YBComm PhasePrim

/-! ## 1. Kernel scaling and shifted directional derivative operators at arbitrary order -/

private theorem scale_iter (m : ℕ) (i j : Fin 3) (t ε : ℝ) (ht : 0 < t) (hε : 0 < ε) (u : Space) :
    iteratedFDeriv ℝ m (fun x => IIIa.heatLerayK t i j x) (ε⁻¹ • u) =
      ε ^ (3 + m) • iteratedFDeriv ℝ m (fun x => IIIa.heatLerayK (t * ε ^ 2) i j x) u := by
  have hK1 : ContDiff ℝ ((m : ℕ) : WithTop ℕ∞) (fun x => IIIa.heatLerayK 1 i j x) :=
    (IIIa.heatLerayKSmoothAll 1 one_pos i j).of_le (by exact_mod_cast le_top)
  have hs : 0 < t * ε ^ 2 := by positivity
  rw [IIIa.l2_iteratedFDeriv_scale i j m t ht _ hK1,
    IIIa.l2_iteratedFDeriv_scale i j m (t * ε ^ 2) hs u hK1, smul_smul]
  have hsq : Real.sqrt (t * ε ^ 2) = Real.sqrt t * ε := by
    rw [Real.sqrt_mul ht.le, Real.sqrt_sq hε.le]
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have harg : ((Real.sqrt t)⁻¹ * ε⁻¹) • u = (Real.sqrt (t * ε ^ 2))⁻¹ • u := by
    rw [hsq, mul_inv]
  rw [harg]
  have h1 : ((ε : ℝ) ^ 2) ^ (-(3 / 2 : ℝ)) = (ε ^ 3)⁻¹ := by
    rw [← Real.rpow_natCast ε 2, ← Real.rpow_mul hε.le]
    have : (((2 : ℕ) : ℝ) * (-(3 / 2 : ℝ))) = -((3 : ℕ) : ℝ) := by norm_num
    rw [this, Real.rpow_neg hε.le, Real.rpow_natCast]
  have hcoef : t ^ (-(3 / 2 : ℝ)) * (Real.sqrt t)⁻¹ ^ m =
      ε ^ (3 + m) * ((t * ε ^ 2) ^ (-(3 / 2 : ℝ)) * (Real.sqrt (t * ε ^ 2))⁻¹ ^ m) := by
    rw [hsq, mul_inv, mul_pow, Real.mul_rpow ht.le (sq_nonneg ε), h1, pow_add]
    have hεm : ε ^ m ≠ 0 := pow_ne_zero m hε.ne'
    have hε3 : ε ^ 3 ≠ 0 := pow_ne_zero 3 hε.ne'
    field_simp
    rw [one_div, inv_pow, mul_inv_cancel₀ hεm]
  rw [hcoef, smul_smul]

private def derivShiftCLM (n : ℕ) (v : Space) :
    ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => Space) ℝ →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin n => Space) ℂ :=
  (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin n => Space) ℝ ℂ
      Complex.ofRealCLM).comp
    ((ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin n => Space) (Space →L[ℝ] ℝ) ℝ
      (ContinuousLinearMap.apply ℝ ℝ v)).comp
      (continuousMultilinearCurryRightEquiv' ℝ n Space ℝ).toContinuousLinearEquiv.toContinuousLinearMap)

private theorem derivShiftCLM_apply (n : ℕ) (v : Space)
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => Space) ℝ) (m : Fin n → Space) :
    derivShiftCLM n v M m = ((M (Fin.snoc m v) : ℝ) : ℂ) := by
  simp [derivShiftCLM, continuousMultilinearCurryRightEquiv_apply']

private theorem norm_derivShiftCLM_le (n : ℕ) (k : Fin 3)
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => Space) ℝ) :
    ‖derivShiftCLM n (coordinateVector k) M‖ ≤ ‖M‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg M) fun m => ?_
  rw [derivShiftCLM_apply, Complex.norm_real, Real.norm_eq_abs]
  have h := M.le_opNorm (Fin.snoc m (coordinateVector k))
  rw [Fin.prod_univ_castSucc] at h
  simp only [Fin.snoc_castSucc, Fin.snoc_last, IIIa.mp_norm_e, mul_one] at h
  exact (Real.norm_eq_abs _).symm ▸ h

private theorem iteratedFDeriv_fderiv_shift (n : ℕ) (v a x : Space) {f : Space → ℝ}
    (hf : ContDiffAt ℝ ∞ f (x - a)) :
    iteratedFDeriv ℝ n (fun y => ((fderiv ℝ f (y - a) v : ℝ) : ℂ)) x =
      derivShiftCLM n v (iteratedFDeriv ℝ (n + 1) f (x - a)) := by
  rw [iteratedFDeriv_comp_sub (f := fun z : Space => ((fderiv ℝ f z v : ℝ) : ℂ))]
  have h1 : iteratedFDeriv ℝ n (fderiv ℝ f) (x - a) =
      (continuousMultilinearCurryRightEquiv' ℝ n Space ℝ) (iteratedFDeriv ℝ (n + 1) f (x - a)) := by
    rw [iteratedFDeriv_succ_eq_comp_right]; simp
  have hd : ContDiffAt ℝ n (fderiv ℝ f) (x - a) :=
    hf.fderiv_right (m := n) (by exact_mod_cast le_top)
  have h2 : iteratedFDeriv ℝ n (fun y => fderiv ℝ f y v) (x - a) =
      (ContinuousLinearMap.apply ℝ ℝ v).compContinuousMultilinearMap
        (iteratedFDeriv ℝ n (fderiv ℝ f) (x - a)) :=
    (ContinuousLinearMap.apply ℝ ℝ v).iteratedFDeriv_comp_left (f := fderiv ℝ f) hd le_rfl
  have h3 : ContDiffAt ℝ n (fun y => fderiv ℝ f y v) (x - a) :=
    (ContinuousLinearMap.apply ℝ ℝ v).contDiff.contDiffAt.comp (x - a) hd
  have h4 : iteratedFDeriv ℝ n (fun y => ((fderiv ℝ f y v : ℝ) : ℂ)) (x - a) =
      Complex.ofRealCLM.compContinuousMultilinearMap
        (iteratedFDeriv ℝ n (fun y => fderiv ℝ f y v) (x - a)) :=
    Complex.ofRealCLM.iteratedFDeriv_comp_left (f := fun y => fderiv ℝ f y v) h3 le_rfl
  rw [h4, h2, h1]
  rfl

private theorem contDiffAt_fderiv_shift (n : ℕ∞) (v a x : Space) {f : Space → ℝ}
    (hf : ContDiffAt ℝ ∞ f (x - a)) :
    ContDiffAt ℝ n (fun y => ((fderiv ℝ f (y - a) v : ℝ) : ℂ)) x := by
  have hd : ContDiffAt ℝ n (fderiv ℝ f) (x - a) :=
    hf.fderiv_right (m := n) (by exact_mod_cast (le_top : n + 1 ≤ ⊤))
  have hsub : ContDiffAt ℝ n (fun y : Space => y - a) x :=
    (contDiff_id.sub contDiff_const).contDiffAt
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp x
    ((ContinuousLinearMap.apply ℝ ℝ v).contDiff.contDiffAt.comp x (hd.comp x hsub))

private theorem iteratedFDeriv_sum_fderiv_shift (n : ℕ) (K : Fin 3 → Space → ℝ) (a x : Space)
    (hK : ∀ j, ContDiffAt ℝ ∞ (K j) (x - a)) (b : ℂ) (c : Fin 3 → Fin 3 → ℝ) :
    iteratedFDeriv ℝ n (fun x' : Space => b * ∑ j : Fin 3, ∑ k : Fin 3,
      ((fderiv ℝ (K j) (x' - a) (coordinateVector k) : ℝ) : ℂ) * (c j k : ℂ)) x =
    ∑ j : Fin 3, ∑ k : Fin 3, (b * (c j k : ℂ)) •
      derivShiftCLM n (coordinateVector k) (iteratedFDeriv ℝ (n + 1) (K j) (x - a)) := by
  let g : Fin 3 → Fin 3 → Space → ℂ := fun j k x' =>
    ((fderiv ℝ (K j) (x' - a) (coordinateVector k) : ℝ) : ℂ)
  have hfun : (fun x' : Space => b * ∑ j : Fin 3, ∑ k : Fin 3,
      g j k x' * (c j k : ℂ)) =
      fun x' : Space => ∑ j : Fin 3, ∑ k : Fin 3, (b * (c j k : ℂ)) • g j k x' := by
    funext x'
    simp only [smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  have hg : ∀ j k, ContDiffAt ℝ n (g j k) x :=
    fun j k => contDiffAt_fderiv_shift n (coordinateVector k) a x (hK j)
  have hk : ∀ j k, ContDiffAt ℝ n (fun x' => (b * (c j k : ℂ)) • g j k x') x :=
    fun j k => (hg j k).const_smul _
  have hj : ∀ j, ContDiffAt ℝ n (fun x' => ∑ k : Fin 3, (b * (c j k : ℂ)) • g j k x') x :=
    fun j => ContDiffAt.sum fun k _ => hk j k
  change iteratedFDeriv ℝ n (fun x' : Space => b * ∑ j : Fin 3, ∑ k : Fin 3,
      g j k x' * (c j k : ℂ)) x = _
  rw [hfun, iteratedFDeriv_fun_sum_apply (fun j _ => hj j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [iteratedFDeriv_fun_sum_apply (fun k _ => hk j k)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [iteratedFDeriv_const_smul_apply' (hg j k),
    iteratedFDeriv_fderiv_shift n (coordinateVector k) a x (hK j)]

private theorem iteratedFDeriv_pi_apply {n : ℕ} {f : Space → Fin 3 → ℂ} {y : Space}
    (hf : ∀ i', ContDiffAt ℝ n (fun y' => f y' i') y) (m : Fin n → Space) (i : Fin 3) :
    (iteratedFDeriv ℝ n f y m) i = iteratedFDeriv ℝ n (fun y' => f y' i) y m := by
  have hcd : ContDiffAt ℝ n f y := contDiffAt_pi.2 hf
  have h := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℂ) i).iteratedFDeriv_comp_left
    hcd le_rfl
  exact (congrArg (fun M => M m) h).symm

/-! ## 2. Higher-order integrands and rescaling -/

def mpHWIter (n : ℕ) (ν ε : ℝ) (μ : ℂ) (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (xo : Space) (m : Fin n → Space) (i : Fin 3) (p : ℝ × ((ℝ × ℝ) × ℝ)) : ℂ :=
  -2 * ((p.1 : ℂ) ^ (2 * μ + 2) * ∑ j : Fin 3, ∑ k : Fin 3,
    ((iteratedFDeriv ℝ (n + 1) (fun x => IIIa.heatLerayK (ν * (1 - p.1 ^ 2) * ε ^ 2) i j x)
      (xo - p.1 • (!₂[p.2.1.1, p.2.1.2, ε * p.2.2] : Space))
      (Fin.snoc m (coordinateVector k)) : ℝ) : ℂ) * ((G p.2.1 p.2.2 j k : ℝ) : ℂ))

def mpVdIter (n : ℕ) (μ : ℂ) (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (p : ℝ × ((ℝ × ℝ) × ℝ)) (x : Space) (m : Fin n → Space) (i : Fin 3) : ℂ :=
  -2 * ((p.1 : ℂ) ^ (2 * μ + 2) * ∑ j : Fin 3, ∑ k : Fin 3,
    ((iteratedFDeriv ℝ (n + 1) (fun x => IIIa.heatLerayK0 i j x) (x - p.1 • IIIa.mpV3 p.2)
      (Fin.snoc m (coordinateVector k)) : ℝ) : ℂ) * ((G p.2.1 p.2.2 j k : ℝ) : ℂ))

private theorem iteratedFDeriv_sepDiffF_apply (n : ℕ) (ν : ℝ) (hν : 0 < ν) (μ : ℂ)
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (l : ℝ) (hl : l ∈ Ioo (0 : ℝ) 1)
    (z y : Space) (m : Fin n → Space) (i : Fin 3) :
    (iteratedFDeriv ℝ n (IIIa.sepDiffF ν μ T τ (l, z)) y m) i =
      -2 * ((l : ℂ) ^ (2 * μ + 2) * ∑ j : Fin 3, ∑ k : Fin 3,
        ((iteratedFDeriv ℝ (n + 1) (fun x => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x) (y - l • z)
          (Fin.snoc m (coordinateVector k)) : ℝ) : ℂ) *
          ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ)) := by
  have ht : 0 < ν * (1 - l ^ 2) := mul_pos hν (by nlinarith [hl.1, hl.2])
  have hsm : ∀ i', ContDiffAt ℝ n (fun y' => IIIa.sepDiffF ν μ T τ (l, z) y' i') y :=
    fun i' => ((IIIa.sepDiffF_contDiff IIIa.heatLerayKSmoothAll ν μ T τ hν (l, z) hl i').of_le
      (by exact_mod_cast le_top)).contDiffAt
  rw [iteratedFDeriv_pi_apply hsm m i]
  have hK : ∀ j, ContDiffAt ℝ ∞ (fun x => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x) (y - l • z) :=
    fun j => (IIIa.heatLerayKSmoothAll _ ht i j).contDiffAt
  have heq : (fun y' => IIIa.sepDiffF ν μ T τ (l, z) y' i) =
      fun y' => (-2 * (l : ℂ) ^ (2 * μ + 2)) * ∑ j : Fin 3, ∑ k : Fin 3,
        ((fderiv ℝ (fun x => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x) (y' - l • z)
          (coordinateVector k) : ℝ) : ℂ) * ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ) := by
    funext y'; unfold IIIa.sepDiffF; ring
  have hsum := iteratedFDeriv_sum_fderiv_shift n
    (fun j x => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x) (l • z) y hK
    (-2 * (l : ℂ) ^ (2 * μ + 2)) (fun j k => T (τ + 2 * Real.log l) z j k)
  rw [heq, hsum]
  simp only [sum_apply, smul_apply, derivShiftCLM_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

private theorem mpHWIter_scale (n : ℕ) (ν ε : ℝ) (hν : 0 < ν) (hε : 0 < ε) (μ : ℂ)
    (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (xo : Space) (m : Fin n → Space)
    (i : Fin 3) (l : ℝ) (hl : l ∈ Ioo (0 : ℝ) 1) (z : Space) :
    (iteratedFDeriv ℝ n (IIIa.sepDiffF ν μ (IIIa.thinSource ε (IIIa.meanLift G)) τ (l, z))
        (ε⁻¹ • xo) m) i =
      (ε : ℂ) ^ (4 + n) * mpHWIter n ν ε μ G xo m i (l, ((ε * z 0, ε * z 1), z 2)) := by
  rw [iteratedFDeriv_sepDiffF_apply n ν hν μ _ τ l hl z (ε⁻¹ • xo) m i]
  have ht : 0 < ν * (1 - l ^ 2) := mul_pos hν (by nlinarith [hl.1, hl.2])
  have harg : ε⁻¹ • xo - l • z = ε⁻¹ • (xo - l • (!₂[ε * z 0, ε * z 1, ε * z 2] : Space)) := by
    ext idx
    fin_cases idx <;> simp <;> field_simp
  unfold mpHWIter
  simp only
  rw [harg]
  have hsrc : ∀ j k : Fin 3,
      IIIa.thinSource ε (IIIa.meanLift G) (τ + 2 * Real.log l) z j k =
        G (ε * z 0, ε * z 1) (z 2) j k := fun _ _ => rfl
  have key : ∀ (j k : Fin 3),
      (iteratedFDeriv ℝ (n + 1) (fun x => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x)
        (ε⁻¹ • (xo - l • (!₂[ε * z 0, ε * z 1, ε * z 2] : Space)))
        (Fin.snoc m (coordinateVector k)) : ℝ) =
      ε ^ (4 + n) * iteratedFDeriv ℝ (n + 1)
        (fun x => IIIa.heatLerayK (ν * (1 - l ^ 2) * ε ^ 2) i j x)
        (xo - l • (!₂[ε * z 0, ε * z 1, ε * z 2] : Space))
        (Fin.snoc m (coordinateVector k)) := by
    intro j k
    have hsc := congrArg (fun M => M (Fin.snoc m (coordinateVector k)))
      (scale_iter (n + 1) i j (ν * (1 - l ^ 2)) ε ht hε
        (xo - l • (!₂[ε * z 0, ε * z 1, ε * z 2] : Space)))
    have hpow : 3 + (n + 1) = 4 + n := by omega
    rw [hpow] at hsc
    simpa using hsc
  simp only [hsrc, key, Complex.ofReal_mul, Complex.ofReal_pow]
  have hs : ∀ (a : ℂ) (f : Fin 3 → Fin 3 → ℂ), ∑ j : Fin 3, ∑ k : Fin 3, a * f j k =
      a * ∑ j : Fin 3, ∑ k : Fin 3, f j k := by
    intro a f; simp [Finset.mul_sum]
  simp only [mul_assoc, hs]
  ring

/-! ## 3. Iterated derivatives of `sepW` via `L09.iteratedFDeriv_integral_eq` -/

set_option maxHeartbeats 1000000 in
private theorem mp_W_iter_local (n : ℕ) (ν : ℝ) (hν : 0 < ν) (μ : ℂ)
    (rOut rIn P : ℝ) (hrO : 0 ≤ rOut) (hrr : rOut < rIn)
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (hT : IIIa.IsSepSource P rOut T) (τ : ℝ) (y : Space)
    (hy : rIn ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2))
    (hfin : IIIa.sepDom (2 * μ.re + 2) 0 (rIn - rOut) (IIIa.srcNorm T) τ y < ⊤) :
    ContDiffAt ℝ ∞ (fun y' => IIIa.sepW ν μ T y' τ) y ∧
      iteratedFDeriv ℝ n (fun y' => IIIa.sepW ν μ T y' τ) y =
        ∫ p, iteratedFDeriv ℝ n (IIIa.sepDiffF ν μ T τ p) y ∂IIIa.sepDiffRho ∧
      Integrable (fun p => iteratedFDeriv ℝ n (IIIa.sepDiffF ν μ T τ p) y) IIIa.sepDiffRho := by
  have h1 := IIIa.heatLerayKSmoothAll
  have h3 := IIIa.sepDiffFMeas
  have h4 := IIIa.sepDiffFDerivBound
  have h5 := IIIa.sepDiffWEqIntegral
  have h6 := IIIa.sepDiffMajIntegrable
  choose C hC0 hC using h4 IIIa.sepKernelBounds
  have hD : 0 < rIn - rOut := by linarith
  set D := rIn - rOut
  set U : Set Space := Metric.ball y (D / 2)
  have hU : IsOpen U := Metric.isOpen_ball
  have hyU : y ∈ U := Metric.mem_ball_self (by linarith)
  set F := IIIa.sepDiffF ν μ T τ
  have hsm : ∀ p : ℝ × Space, p.1 ∈ Ioo (0 : ℝ) 1 → ∀ i, ContDiff ℝ ∞ (fun y' => F p y' i) :=
    fun p hp i => IIIa.sepDiffF_contDiff h1 ν μ T τ hν p hp i
  have hsmAt : ∀ (m : ℕ) (p : ℝ × Space), p.1 ∈ Ioo (0 : ℝ) 1 → ∀ (y' : Space) (i : Fin 3),
      ContDiffAt ℝ m (fun y' => F p y' i) y' := fun m p hp y' i =>
    ((hsm p hp i).of_le (by exact_mod_cast le_top)).contDiffAt
  have hoff : ∀ p : ℝ × Space, rOut < Real.sqrt (p.2 0 ^ 2 + p.2 1 ^ 2) → F p = 0 :=
    fun p hp => IIIa.sepDiffF_eq_zero ν μ T τ p (hT.support _ _ hp)
  have hpi : ∀ (m : ℕ) (p : ℝ × Space), p.1 ∈ Ioo (0 : ℝ) 1 → ∀ y' : Space,
      y' - p.1 • p.2 ≠ 0 → ‖iteratedFDeriv ℝ m (F p) y'‖ ≤ 3 * C m *
        (p.1 ^ (2 * μ.re + 2) * ‖y' - p.1 • p.2‖ ^ (-4 - (m : ℝ)) *
          IIIa.tensorNorm (T (τ + 2 * Real.log p.1) p.2)) := by
    intro m p hp y' hne
    rw [IIIa.sepDiff_iteratedFDeriv_pi (fun i => hsmAt m p hp y' i)]
    refine (norm_sum_le _ _).trans ?_
    have hb : ∀ i : Fin 3,
        ‖(ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i).compContinuousMultilinearMap
          (iteratedFDeriv ℝ m (fun y'' => F p y'' i) y')‖ ≤ C m *
          (p.1 ^ (2 * μ.re + 2) * ‖y' - p.1 • p.2‖ ^ (-4 - (m : ℝ)) *
            IIIa.tensorNorm (T (τ + 2 * Real.log p.1) p.2)) := by
      intro i
      refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
      have h1i := ContinuousLinearMap.norm_single_le_one ℝ (E := fun _ : Fin 3 => ℂ) i
      have h2i := hC m ν μ T τ hν p.1 p.2 y' hp hne i
      calc ‖ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i‖ *
            ‖iteratedFDeriv ℝ m (fun y'' => F p y'' i) y'‖
          ≤ 1 * ‖iteratedFDeriv ℝ m (fun y'' => F p y'' i) y'‖ := by gcongr
        _ ≤ _ := by rw [one_mul]; exact h2i
    calc ∑ i : Fin 3,
          ‖(ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i).compContinuousMultilinearMap
            (iteratedFDeriv ℝ m (fun y'' => F p y'' i) y')‖
        ≤ ∑ _i : Fin 3, C m * (p.1 ^ (2 * μ.re + 2) * ‖y' - p.1 • p.2‖ ^ (-4 - (m : ℝ)) *
            IIIa.tensorNorm (T (τ + 2 * Real.log p.1) p.2)) := Finset.sum_le_sum fun i _ => hb i
      _ = _ := by simp [Finset.sum_const]; ring
  have hgapU : ∀ p : ℝ × Space, p.1 ∈ Ioo (0 : ℝ) 1 → Real.sqrt (p.2 0 ^ 2 + p.2 1 ^ 2) ≤ rOut →
      ∀ y' ∈ U, D ≤ ‖y - p.1 • p.2‖ ∧ ‖y - p.1 • p.2‖ ≤ 2 * ‖y' - p.1 • p.2‖ := by
    intro p hp hz y' hy'
    have hg := IIIa.radial_gap y p.2 p.1 rOut rIn hp hz hy
    have hd : ‖y - y'‖ < D / 2 := by
      rw [← dist_eq_norm, dist_comm]; exact hy'
    have ht := norm_sub_le_norm_sub_add_norm_sub y y' (p.1 • p.2)
    exact ⟨hg, by linarith⟩
  have hdom : ∀ (m : ℕ) (p : ℝ × Space), p.1 ∈ Ioo (0 : ℝ) 1 → ∀ y' ∈ U,
      ‖iteratedFDeriv ℝ m (F p) y'‖ ≤
        (3 * C m * 2 ^ (4 + (m : ℝ)) * D ^ (-(m : ℝ))) * IIIa.sepDiffMaj μ T τ y p := by
    intro m p hp y' hy'
    have hl0 : 0 ≤ p.1 ^ (2 * μ.re + 2) := Real.rpow_nonneg hp.1.le _
    have htn : 0 ≤ IIIa.tensorNorm (T (τ + 2 * Real.log p.1) p.2) := Real.sqrt_nonneg _
    by_cases hz : Real.sqrt (p.2 0 ^ 2 + p.2 1 ^ 2) ≤ rOut
    · obtain ⟨hg1, hg2⟩ := hgapU p hp hz y' hy'
      have hne : y' - p.1 • p.2 ≠ 0 := by
        intro h0; rw [h0, norm_zero] at hg2; linarith
      have hw := IIIa.sepDiff_gapWeight D ‖y - p.1 • p.2‖ ‖y' - p.1 • p.2‖ m hD hg1 hg2
      refine (hpi m p hp y' hne).trans ?_
      unfold IIIa.sepDiffMaj
      have hC3 : 0 ≤ 3 * C m := by linarith [hC0 m]
      calc 3 * C m * (p.1 ^ (2 * μ.re + 2) * ‖y' - p.1 • p.2‖ ^ (-4 - (m : ℝ)) *
            IIIa.tensorNorm (T (τ + 2 * Real.log p.1) p.2))
          ≤ 3 * C m * (p.1 ^ (2 * μ.re + 2) * (2 ^ (4 + (m : ℝ)) * D ^ (-(m : ℝ)) *
              ‖y - p.1 • p.2‖ ^ (-4 : ℝ)) * IIIa.tensorNorm (T (τ + 2 * Real.log p.1) p.2)) := by
            gcongr
        _ = _ := by ring
    · have hz' : rOut < Real.sqrt (p.2 0 ^ 2 + p.2 1 ^ 2) := lt_of_not_ge hz
      rw [hoff p hz']
      have h0 : iteratedFDeriv ℝ m (0 : Space → Fin 3 → ℂ) y' = 0 := by simp
      rw [h0, norm_zero]
      have hTz : T (τ + 2 * Real.log p.1) p.2 = 0 := hT.support _ _ hz'
      unfold IIIa.sepDiffMaj
      rw [hTz]
      simp [IIIa.tensorNorm]
  have hInt : Integrable (IIIa.sepDiffMaj μ T τ y) IIIa.sepDiffRho :=
    h6 μ rOut rIn P T hrO hrr hT τ y hy hfin
  have hLoc : UnforcedLeray.L09.LocDominated IIIa.sepDiffRho F U := by
    intro m x hx
    refine ⟨U, hU.mem_nhds hx,
      fun p => (3 * C m * 2 ^ (4 + (m : ℝ)) * D ^ (-(m : ℝ))) * IIIa.sepDiffMaj μ T τ y p,
      hInt.const_mul _, ?_⟩
    filter_upwards [IIIa.sepDiffRho_ae_mem] with p hp y' hy'
    exact hdom m p hp y' hy'
  have hsmooth : ∀ᵐ p ∂IIIa.sepDiffRho, ContDiffOn ℝ ∞ (F p) U := by
    filter_upwards [IIIa.sepDiffRho_ae_mem] with p hp
    exact (contDiff_pi.2 (hsm p hp)).contDiffOn
  have hmeas : ∀ (m : ℕ), ∀ x ∈ U,
      AEStronglyMeasurable (fun p => iteratedFDeriv ℝ m (F p) x) IIIa.sepDiffRho := by
    intro m x _
    have hR : AEStronglyMeasurable (fun p => ∑ i : Fin 3,
        (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin m => Space) ℂ
          (Fin 3 → ℂ) (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i))
          (iteratedFDeriv ℝ m (fun y' => F p y' i) x)) IIIa.sepDiffRho := by
      refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
      exact (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin m => Space) ℂ
        (Fin 3 → ℂ) (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i)).continuous
          |>.comp_aestronglyMeasurable (h3 ν μ P rOut T hν hT τ i m x)
    refine hR.congr ?_
    filter_upwards [IIIa.sepDiffRho_ae_mem] with p hp
    rw [IIIa.sepDiff_iteratedFDeriv_pi (fun i => hsmAt m p hp x i)]
    rfl
  have hFint : ∀ y' ∈ U, Integrable (fun p => F p y') IIIa.sepDiffRho := by
    intro y' hy'
    have hm : AEStronglyMeasurable (fun p => F p y') IIIa.sepDiffRho := by
      have := (continuousMultilinearCurryFin0 ℝ Space (Fin 3 → ℂ)).continuous
        |>.comp_aestronglyMeasurable (hmeas 0 y' hy')
      refine this.congr (Eventually.of_forall fun p => ?_)
      simp
    refine Integrable.mono' (hInt.const_mul (3 * C 0 * 2 ^ (4 + ((0 : ℕ) : ℝ)) *
      D ^ (-((0 : ℕ) : ℝ)))) hm ?_
    filter_upwards [IIIa.sepDiffRho_ae_mem] with p hp
    rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ)]
    exact hdom 0 p hp y' hy'
  have hEq : (fun y' => IIIa.sepW ν μ T y' τ) =ᶠ[𝓝 y] fun y' => ∫ p, F p y' ∂IIIa.sepDiffRho := by
    filter_upwards [hU.mem_nhds hyU] with y' hy' using h5 ν μ T τ y' (hFint y' hy')
  refine ⟨?_, ?_, hLoc.integrable hmeas n hyU⟩
  · exact ((UnforcedLeray.L09.contDiffOn_integral hU hsmooth hmeas hLoc).contDiffAt
      (hU.mem_nhds hyU)).congr_of_eventuallyEq hEq
  · rw [(hEq.iteratedFDeriv ℝ n).eq_of_nhds]
    exact UnforcedLeray.L09.iteratedFDeriv_integral_eq hU hsmooth hmeas hLoc n hyU

theorem mp_W_iter_eval (n : ℕ) (ν c ε ρo ρi : ℝ) (μ : ℂ) (hν : 0 < ν) (hc : 0 < c)
    (hε : 0 < ε) (hρo : 0 ≤ ρo) (hρ : ρo < ρi) (hμ : -(1 / 4) < μ.re)
    (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hGm : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ => G w.1 w.2 i j)
    (hGs : ∀ x' Y, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → G x' Y = 0)
    (hint : Integrable (fun w : (ℝ × ℝ) × ℝ => IIIa.tensorNorm (G w.1 w.2)) volume)
    (xo : Space) (hxo : ρi ≤ Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2)) (τ : ℝ) :
    ContDiffAt ℝ ∞ (fun y => IIIa.sepW ν μ (IIIa.thinSource ε (IIIa.meanLift G)) y τ) (ε⁻¹ • xo) ∧
      ∀ (m : Fin n → Space) (i : Fin 3),
        (iteratedFDeriv ℝ n (fun y => IIIa.sepW ν μ (IIIa.thinSource ε (IIIa.meanLift G)) y τ)
          (ε⁻¹ • xo) m) i =
          (ε : ℂ) ^ (2 + n) * ∫ p, mpHWIter n ν ε μ G xo m i p ∂IIIa.mpRho2 ∧
        Integrable (mpHWIter n ν ε μ G xo m i) IIIa.mpRho2 := by
  set T := IIIa.thinSource ε (IIIa.meanLift G)
  have hsrc : IIIa.IsSepSource (2 * ε * c) (ρo / ε) T :=
    IIIa.t17s_isSepSource ε c ρo hε hc _ (fun i' j' =>
      (hGm i' j').comp (f := fun w : (ℝ × ℝ) × ℝ × ℝ => (w.1, w.2.1)) (by fun_prop))
      (fun _ _ _ => rfl) (fun x' Y q h => hGs x' Y h)
  have hD : 0 < ρi / ε - ρo / ε := by
    have : 0 < ρi - ρo := by linarith
    rw [← sub_div]; positivity
  have hy : ρi / ε ≤ Real.sqrt ((ε⁻¹ • xo) 0 ^ 2 + (ε⁻¹ • xo) 1 ^ 2) := by
    have h2 : Real.sqrt ((ε⁻¹ • xo) 0 ^ 2 + (ε⁻¹ • xo) 1 ^ 2) =
        ε⁻¹ * Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) := by
      have : (ε⁻¹ • xo) 0 ^ 2 + (ε⁻¹ • xo) 1 ^ 2 = (ε⁻¹) ^ 2 * (xo 0 ^ 2 + xo 1 ^ 2) := by
        simp only [PiLp.smul_apply, smul_eq_mul]; ring
      rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_nonneg.2 hε.le)]
    rw [h2, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hxo (inv_nonneg.2 hε.le)
  have hfinN : ∫⁻ w : (ℝ × ℝ) × ℝ, ENNReal.ofReal (IIIa.tensorNorm (G w.1 w.2)) < ⊤ :=
    hint.lintegral_lt_top
  have hfin : IIIa.sepDom (2 * μ.re + 2) 0 (ρi / ε - ρo / ε) (IIIa.srcNorm T) τ (ε⁻¹ • xo) < ⊤ := by
    refine IIIa.t17s_sepDom_lt_top (2 * μ.re + 2) (by linarith) _ hD _ τ _ ?_
    simp_rw [show T = IIIa.thinSource ε (IIIa.meanLift G) from rfl,
      IIIa.mp_src_lintegral ε hε G hGm]
    rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one,
      mul_one]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) hfinN
  obtain ⟨hcd, hWeq, hI⟩ := mp_W_iter_local n ν hν μ (ρo / ε) (ρi / ε) (2 * ε * c)
    (div_nonneg hρo hε.le) (div_lt_div_of_pos_right hρ hε) T hsrc τ (ε⁻¹ • xo) hy hfin
  refine ⟨hcd, fun m i => ?_⟩
  set Λ : (Space [×n]→L[ℝ] (Fin 3 → ℂ)) →L[ℝ] ℂ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℂ) i).comp
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Space) (Fin 3 → ℂ) m)
  have h1 : (iteratedFDeriv ℝ n (fun y => IIIa.sepW ν μ T y τ) (ε⁻¹ • xo) m) i =
      ∫ p, Λ (iteratedFDeriv ℝ n (IIIa.sepDiffF ν μ T τ p) (ε⁻¹ • xo)) ∂IIIa.sepDiffRho := by
    rw [hWeq, Λ.integral_comp_comm hI]
    rfl
  have h2 : ∀ᵐ p ∂IIIa.sepDiffRho,
      Λ (iteratedFDeriv ℝ n (IIIa.sepDiffF ν μ T τ p) (ε⁻¹ • xo)) =
        (ε : ℂ) ^ (4 + n) * mpHWIter n ν ε μ G xo m i (Prod.map (id : ℝ → ℝ) (IIIa.mpPsi ε hε) p) := by
    filter_upwards [IIIa.sepDiffRho_ae_mem] with p hp
    exact mpHWIter_scale n ν ε hν hε μ G τ xo m i p.1 hp p.2
  have hΛint : Integrable (fun p => Λ (iteratedFDeriv ℝ n (IIIa.sepDiffF ν μ T τ p) (ε⁻¹ • xo)))
      IIIa.sepDiffRho := Λ.integrable_comp hI
  have hc2 : ENNReal.ofReal (ε⁻¹) ^ 2 ≠ 0 := by
    have : ENNReal.ofReal ε⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 hε)).ne'
    exact pow_ne_zero _ this
  have hc2' : ENNReal.ofReal (ε⁻¹) ^ 2 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hεp : (ε : ℂ) ^ (4 + n) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hε.ne')
  have hmapint : Integrable (mpHWIter n ν ε μ G xo m i) IIIa.mpRho2 := by
    have h3 : Integrable (fun p => mpHWIter n ν ε μ G xo m i
        (Prod.map (id : ℝ → ℝ) (IIIa.mpPsi ε hε) p)) IIIa.sepDiffRho := by
      have := hΛint.const_mul ((ε : ℂ) ^ (4 + n))⁻¹
      refine this.congr ?_
      filter_upwards [h2] with p hp
      rw [hp, ← mul_assoc, inv_mul_cancel₀ hεp, one_mul]
    have h4 := (IIIa.mp_Psi_embedding ε hε).integrable_map_iff
      (g := mpHWIter n ν ε μ G xo m i) (μ := IIIa.sepDiffRho) |>.2 h3
    rw [IIIa.mp_Psi_map ε hε, integrable_smul_measure hc2 hc2'] at h4
    exact h4
  refine ⟨?_, hmapint⟩
  rw [h1, integral_congr_ae h2, integral_const_mul]
  have h5 := (IIIa.mp_Psi_embedding ε hε).integral_map
    (μ := IIIa.sepDiffRho) (mpHWIter n ν ε μ G xo m i)
  rw [IIIa.mp_Psi_map ε hε, integral_smul_measure] at h5
  have h6 : (ENNReal.ofReal (ε⁻¹) ^ 2).toReal = (ε⁻¹) ^ 2 := by
    rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (inv_nonneg.2 hε.le)]
  rw [h6] at h5
  have h7 : ∫ p, mpHWIter n ν ε μ G xo m i
        (Prod.map (id : ℝ → ℝ) (IIIa.mpPsi ε hε) p) ∂IIIa.sepDiffRho =
      ((ε⁻¹ : ℝ) : ℂ) ^ 2 * ∫ p, mpHWIter n ν ε μ G xo m i p ∂IIIa.mpRho2 := by
    rw [← h5, Complex.real_smul]
    push_cast
    ring
  rw [h7]
  have hεc : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  have hpow : (ε : ℂ) ^ (4 + n) * ((ε⁻¹ : ℝ) : ℂ) ^ 2 = (ε : ℂ) ^ (2 + n) := by
    have : (4 + n : ℕ) = 2 + (2 + n) := by omega
    rw [this, pow_add]
    push_cast
    field_simp
  rw [← mul_assoc, hpow]

/-! ## 4. Iterated derivatives of `sepVmu0` via `L09.iteratedFDeriv_integral_eq` -/

private theorem mpVF_iteratedFDeriv_eq (n : ℕ) (μ : ℂ) (ρo : ℝ)
    (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hGs : ∀ x' Y, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → G x' Y = 0)
    (p : ℝ × ((ℝ × ℝ) × ℝ)) (x : Space)
    (hne : Real.sqrt (p.2.1.1 ^ 2 + p.2.1.2 ^ 2) ≤ ρo → x - p.1 • IIIa.mpV3 p.2 ≠ 0)
    (i : Fin 3) :
    iteratedFDeriv ℝ n (fun x' => IIIa.mpVF μ G p x' i) x =
      ∑ j : Fin 3, ∑ k : Fin 3,
        ((-2 * (p.1 : ℂ) ^ (2 * μ + 2)) * ((G p.2.1 p.2.2 j k : ℝ) : ℂ)) •
          derivShiftCLM n (coordinateVector k)
            (iteratedFDeriv ℝ (n + 1) (fun y => IIIa.heatLerayK0 i j y)
              (x - p.1 • IIIa.mpV3 p.2)) := by
  by_cases hw : Real.sqrt (p.2.1.1 ^ 2 + p.2.1.2 ^ 2) ≤ ρo
  · have hK : ∀ j, ContDiffAt ℝ ∞ (fun y => IIIa.heatLerayK0 i j y) (x - p.1 • IIIa.mpV3 p.2) :=
      fun j => IIIa.mp_K0_contDiffAt _ (hne hw) i j
    have heq : (fun x' => IIIa.mpVF μ G p x' i) =
        fun x' => (-2 * (p.1 : ℂ) ^ (2 * μ + 2)) * ∑ j : Fin 3, ∑ k : Fin 3,
          ((fderiv ℝ (fun y => IIIa.heatLerayK0 i j y) (x' - p.1 • IIIa.mpV3 p.2)
            (coordinateVector k) : ℝ) : ℂ) * ((G p.2.1 p.2.2 j k : ℝ) : ℂ) := by
      funext x'; unfold IIIa.mpVF; ring
    rw [heq]
    exact iteratedFDeriv_sum_fderiv_shift n (fun j y => IIIa.heatLerayK0 i j y)
      (p.1 • IIIa.mpV3 p.2) x hK (-2 * (p.1 : ℂ) ^ (2 * μ + 2)) (fun j k => G p.2.1 p.2.2 j k)
  · have hw' : ρo < Real.sqrt (p.2.1.1 ^ 2 + p.2.1.2 ^ 2) := lt_of_not_ge hw
    have h0 : G p.2.1 p.2.2 = 0 := hGs _ _ hw'
    have hf : (fun x' => IIIa.mpVF μ G p x' i) = 0 := funext fun x' => IIIa.mpVF_zero μ G p h0 x' i
    rw [hf]
    have h0' : iteratedFDeriv ℝ n (0 : Space → ℂ) x = 0 := by simp
    have h0_smul : ∀ (M : Space [×n]→L[ℝ] ℂ), (0 : ℂ) • M = 0 := fun M => by ext v; simp
    rw [h0', h0]
    simp [Matrix.zero_apply, h0_smul]

set_option maxHeartbeats 1000000 in
theorem mp_V_iter_comp (n : ℕ) (μ : ℂ) (hμ : -(1 / 4) < μ.re) (ρo ρi : ℝ)
    (hρo : 0 ≤ ρo) (hρ : ρo < ρi) (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hGm : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ => G w.1 w.2 i j)
    (hGs : ∀ x' Y, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → G x' Y = 0)
    (hint : Integrable (fun w : (ℝ × ℝ) × ℝ => IIIa.tensorNorm (G w.1 w.2)) volume)
    (xo : Space) (hxo : ρi ≤ Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2)) (i : Fin 3) :
    ContDiffAt ℝ ∞ (fun x => IIIa.sepVmu0 μ G x i) xo ∧
      ∀ (m : Fin n → Space),
        iteratedFDeriv ℝ n (fun x => IIIa.sepVmu0 μ G x i) xo m =
          ∫ p, mpVdIter n μ G p xo m i ∂IIIa.mpRho2 ∧
        Integrable (fun p => mpVdIter n μ G p xo m i) IIIa.mpRho2 := by
  choose CK hCK using IIIa.sepKernelBounds
  set D1 := (ρi - ρo) / 2 with hD1
  have hD1pos : 0 < D1 := by rw [hD1]; linarith
  set U : Set Space := Metric.ball xo D1
  have hU : IsOpen U := Metric.isOpen_ball
  have hxoU : xo ∈ U := Metric.mem_ball_self hD1pos
  set F : ℝ × ((ℝ × ℝ) × ℝ) → Space → ℂ := fun p x => IIIa.mpVF μ G p x i
  have hgapU : ∀ p : ℝ × ((ℝ × ℝ) × ℝ), p.1 ∈ Ioo (0 : ℝ) 1 →
      Real.sqrt (p.2.1.1 ^ 2 + p.2.1.2 ^ 2) ≤ ρo →
      ∀ x ∈ U, D1 ≤ ‖x - p.1 • IIIa.mpV3 p.2‖ ∧ x - p.1 • IIIa.mpV3 p.2 ≠ 0 := by
    intro p hp hw x hx
    have hxn : ‖xo - x‖ < D1 := by rw [← dist_eq_norm, dist_comm]; exact hx
    have hg := IIIa.mp_gap ρo ρi xo x hxo p.1 hp p.2 hw
    have hnorm : D1 ≤ ‖x - p.1 • IIIa.mpV3 p.2‖ :=
      le_trans (by rw [hD1]; linarith) (IIIa.rho_le_norm _)
    refine ⟨hnorm, fun h0 => ?_⟩
    rw [h0, norm_zero] at hnorm; linarith
  have hsmooth : ∀ᵐ p ∂IIIa.mpRho2, ContDiffOn ℝ ∞ (F p) U := by
    filter_upwards [IIIa.mpRho2_ae_mem] with p hp
    by_cases hw : Real.sqrt (p.2.1.1 ^ 2 + p.2.1.2 ^ 2) ≤ ρo
    · intro x hx
      refine (ContDiffAt.mul contDiffAt_const (ContDiffAt.mul contDiffAt_const
        (ContDiffAt.sum fun j _ => ContDiffAt.sum fun k _ => ?_))).contDiffWithinAt
      refine ContDiffAt.mul ?_ contDiffAt_const
      have hne := (hgapU p hp hw x hx).2
      have hK := IIIa.mp_K0_contDiffAt _ hne i j
      exact contDiffAt_fderiv_shift ⊤ (coordinateVector k) (p.1 • IIIa.mpV3 p.2) x hK
    · have hw' : ρo < Real.sqrt (p.2.1.1 ^ 2 + p.2.1.2 ^ 2) := lt_of_not_ge hw
      have h0 : G p.2.1 p.2.2 = 0 := hGs _ _ hw'
      have hf : F p = 0 := funext fun x' => IIIa.mpVF_zero μ G p h0 x' i
      rw [hf]
      exact contDiffOn_const
  have hmeas : ∀ (m : ℕ), ∀ x ∈ U,
      AEStronglyMeasurable (fun p => iteratedFDeriv ℝ m (F p) x) IIIa.mpRho2 := by
    intro m x hx
    set S : Set (ℝ × ((ℝ × ℝ) × ℝ)) :=
      {p | p.1 ∈ Ioo (0 : ℝ) 1 ∧ Real.sqrt (p.2.1.1 ^ 2 + p.2.1.2 ^ 2) ≤ ρo}
    have hS : MeasurableSet S := by
      have hS1 : MeasurableSet {p : ℝ × ((ℝ × ℝ) × ℝ) | p.1 ∈ Ioo (0 : ℝ) 1} :=
        measurableSet_Ioo.preimage measurable_fst
      have hS2 : MeasurableSet {p : ℝ × ((ℝ × ℝ) × ℝ) |
          Real.sqrt (p.2.1.1 ^ 2 + p.2.1.2 ^ 2) ≤ ρo} :=
        (isClosed_le (by fun_prop) continuous_const).measurableSet
      exact hS1.inter hS2
    have hu_cont : Continuous fun p : ℝ × ((ℝ × ℝ) × ℝ) => x - p.1 • IIIa.mpV3 p.2 :=
      continuous_const.sub (continuous_fst.smul (IIIa.mpV3_continuous.comp continuous_snd))
    have hu_maps : MapsTo (fun p : ℝ × ((ℝ × ℝ) × ℝ) => x - p.1 • IIIa.mpV3 p.2) S {0}ᶜ :=
      fun p hp => (hgapU p hp.1 hp.2 x hx).2
    have hcp : Measurable fun p : ℝ × ((ℝ × ℝ) × ℝ) => -2 * (p.1 : ℂ) ^ (2 * μ + 2) :=
      measurable_const.mul ((Complex.measurable_ofReal.comp measurable_fst).pow_const _)
    have hR : AEStronglyMeasurable (fun p : ℝ × ((ℝ × ℝ) × ℝ) =>
        ∑ j : Fin 3, ∑ k : Fin 3,
          ((-2 * (p.1 : ℂ) ^ (2 * μ + 2)) * ((G p.2.1 p.2.2 j k : ℝ) : ℂ)) •
            S.indicator (fun q => derivShiftCLM m (coordinateVector k)
              (iteratedFDeriv ℝ (m + 1) (fun y => IIIa.heatLerayK0 i j y)
                (x - q.1 • IIIa.mpV3 q.2))) p) IIIa.mpRho2 := by
      refine Finset.aestronglyMeasurable_fun_sum _ fun j _ =>
        Finset.aestronglyMeasurable_fun_sum _ fun k _ => ?_
      have hc : Measurable fun p : ℝ × ((ℝ × ℝ) × ℝ) =>
          (-2 * (p.1 : ℂ) ^ (2 * μ + 2)) * ((G p.2.1 p.2.2 j k : ℝ) : ℂ) :=
        hcp.mul (Complex.measurable_ofReal.comp ((hGm j k).comp measurable_snd))
      have hK0_cd : ContDiffOn ℝ ∞ (fun y => IIIa.heatLerayK0 i j y) {0}ᶜ :=
        fun y hy => (IIIa.mp_K0_contDiffAt y hy i j).contDiffWithinAt
      have hK0_cont : ContinuousOn
          (iteratedFDeriv ℝ (m + 1) (fun y => IIIa.heatLerayK0 i j y)) {0}ᶜ :=
        ContinuousOn.continuousOn_iteratedFDeriv hK0_cd isOpen_compl_singleton
          (by exact_mod_cast le_top)
      have hg_cont : ContinuousOn (fun q : ℝ × ((ℝ × ℝ) × ℝ) =>
          derivShiftCLM m (coordinateVector k)
            (iteratedFDeriv ℝ (m + 1) (fun y => IIIa.heatLerayK0 i j y)
              (x - q.1 • IIIa.mpV3 q.2))) S :=
        (derivShiftCLM m (coordinateVector k)).continuous.comp_continuousOn
          (hK0_cont.comp hu_cont.continuousOn hu_maps)
      have hg_ind : AEStronglyMeasurable (S.indicator (fun q : ℝ × ((ℝ × ℝ) × ℝ) =>
          derivShiftCLM m (coordinateVector k)
            (iteratedFDeriv ℝ (m + 1) (fun y => IIIa.heatLerayK0 i j y)
              (x - q.1 • IIIa.mpV3 q.2)))) IIIa.mpRho2 :=
        (aestronglyMeasurable_indicator_iff hS).2 (hg_cont.aestronglyMeasurable hS)
      exact hc.aestronglyMeasurable.smul hg_ind
    refine hR.congr ?_
    have h0_smul : ∀ (M : Space [×m]→L[ℝ] ℂ), (0 : ℂ) • M = 0 := fun M => by ext v; simp
    filter_upwards [IIIa.mpRho2_ae_mem] with p hp
    rw [mpVF_iteratedFDeriv_eq m μ ρo G hGs p x (fun hw => (hgapU p hp hw x hx).2) i]
    by_cases hw : Real.sqrt (p.2.1.1 ^ 2 + p.2.1.2 ^ 2) ≤ ρo
    · have hpS : p ∈ S := ⟨hp, hw⟩
      simp [Set.indicator_of_mem hpS]
    · have hw' : ρo < Real.sqrt (p.2.1.1 ^ 2 + p.2.1.2 ^ 2) := lt_of_not_ge hw
      have h0 : G p.2.1 p.2.2 = 0 := hGs _ _ hw'
      simp [h0, Matrix.zero_apply, h0_smul]
  have hdom : ∀ (m : ℕ) (p : ℝ × ((ℝ × ℝ) × ℝ)), p.1 ∈ Ioo (0 : ℝ) 1 → ∀ x ∈ U,
      ‖iteratedFDeriv ℝ m (F p) x‖ ≤
        (18 * max (CK m) 0 * D1 ^ (-4 - (m : ℝ))) * IIIa.tensorNorm (G p.2.1 p.2.2) := by
    intro m p hp x hx
    rw [mpVF_iteratedFDeriv_eq m μ ρo G hGs p x (fun hw => (hgapU p hp hw x hx).2) i]
    have hCM0 : 0 ≤ max (CK m) 0 := le_max_right _ _
    have hD1p : 0 ≤ D1 ^ (-4 - (m : ℝ)) := Real.rpow_nonneg hD1pos.le _
    have htn : 0 ≤ IIIa.tensorNorm (G p.2.1 p.2.2) := tn_nonneg _
    by_cases hw : Real.sqrt (p.2.1.1 ^ 2 + p.2.1.2 ^ 2) ≤ ρo
    · obtain ⟨hnorm, hne⟩ := hgapU p hp hw x hx
      have hw1 := IIIa.mp_norm_cpow_le μ hμ p.1 hp
      have hterm : ∀ j k : Fin 3,
          ‖((-2 * (p.1 : ℂ) ^ (2 * μ + 2)) * ((G p.2.1 p.2.2 j k : ℝ) : ℂ)) •
            derivShiftCLM m (coordinateVector k)
              (iteratedFDeriv ℝ (m + 1) (fun y => IIIa.heatLerayK0 i j y)
                (x - p.1 • IIIa.mpV3 p.2))‖ ≤
            2 * (max (CK m) 0 * D1 ^ (-4 - (m : ℝ))) * IIIa.tensorNorm (G p.2.1 p.2.2) := by
        intro j k
        rw [norm_smul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have hn2 : ‖(-2 : ℂ)‖ = 2 := by simp
        rw [hn2]
        have hc : 2 * ‖(p.1 : ℂ) ^ (2 * μ + 2)‖ * |G p.2.1 p.2.2 j k| ≤
            2 * 1 * IIIa.tensorNorm (G p.2.1 p.2.2) := by
          gcongr
          exact IIIa.mp_entry_le _ j k
        have hd1 := norm_derivShiftCLM_le m k
          (iteratedFDeriv ℝ (m + 1) (fun y => IIIa.heatLerayK0 i j y) (x - p.1 • IIIa.mpV3 p.2))
        have hd2 : ‖iteratedFDeriv ℝ (m + 1) (fun y => IIIa.heatLerayK0 i j y)
            (x - p.1 • IIIa.mpV3 p.2)‖ ≤ max (CK m) 0 * D1 ^ (-4 - (m : ℝ)) := by
          refine ((hCK m _ hne i j).2.1).trans ?_
          have hpow : ‖x - p.1 • IIIa.mpV3 p.2‖ ^ (-4 - (m : ℝ)) ≤ D1 ^ (-4 - (m : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos hD1pos hnorm (by have := m.cast_nonneg (α := ℝ); linarith)
          calc CK m * ‖x - p.1 • IIIa.mpV3 p.2‖ ^ (-4 - (m : ℝ))
              ≤ max (CK m) 0 * ‖x - p.1 • IIIa.mpV3 p.2‖ ^ (-4 - (m : ℝ)) :=
                mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) _)
            _ ≤ max (CK m) 0 * D1 ^ (-4 - (m : ℝ)) :=
                mul_le_mul_of_nonneg_left hpow hCM0
        calc (2 * ‖(p.1 : ℂ) ^ (2 * μ + 2)‖ * |G p.2.1 p.2.2 j k|) *
              ‖derivShiftCLM m (coordinateVector k) _‖
            ≤ (2 * 1 * IIIa.tensorNorm (G p.2.1 p.2.2)) * (max (CK m) 0 * D1 ^ (-4 - (m : ℝ))) :=
              mul_le_mul hc (hd1.trans hd2) (norm_nonneg _) (by positivity)
          _ = 2 * (max (CK m) 0 * D1 ^ (-4 - (m : ℝ))) * IIIa.tensorNorm (G p.2.1 p.2.2) := by ring
      refine (norm_sum_le _ _).trans ?_
      have hj : ∀ j : Fin 3,
          ‖∑ k : Fin 3, ((-2 * (p.1 : ℂ) ^ (2 * μ + 2)) * ((G p.2.1 p.2.2 j k : ℝ) : ℂ)) •
            derivShiftCLM m (coordinateVector k)
              (iteratedFDeriv ℝ (m + 1) (fun y => IIIa.heatLerayK0 i j y)
                (x - p.1 • IIIa.mpV3 p.2))‖ ≤
          3 * (2 * (max (CK m) 0 * D1 ^ (-4 - (m : ℝ))) * IIIa.tensorNorm (G p.2.1 p.2.2)) := by
        intro j
        refine (norm_sum_le _ _).trans ?_
        calc ∑ k : Fin 3, _ ≤ ∑ _k : Fin 3, _ := Finset.sum_le_sum fun k _ => hterm j k
          _ = _ := by simp [Finset.sum_const]
      calc ∑ j : Fin 3, _ ≤ ∑ _j : Fin 3, _ := Finset.sum_le_sum fun j _ => hj j
        _ = _ := by simp [Finset.sum_const]; ring
    · have hw' : ρo < Real.sqrt (p.2.1.1 ^ 2 + p.2.1.2 ^ 2) := lt_of_not_ge hw
      have h0 : G p.2.1 p.2.2 = 0 := hGs _ _ hw'
      have h0_smul : ∀ (M : Space [×m]→L[ℝ] ℂ), (0 : ℂ) • M = 0 := fun M => by ext v; simp
      simp [h0, Matrix.zero_apply, h0_smul, IIIa.tensorNorm]
  have hTn := IIIa.mp_tn_integrable G hint
  have hLoc : UnforcedLeray.L09.LocDominated IIIa.mpRho2 F U := by
    intro m x hx
    refine ⟨U, hU.mem_nhds hx,
      fun p => (18 * max (CK m) 0 * D1 ^ (-4 - (m : ℝ))) * IIIa.tensorNorm (G p.2.1 p.2.2),
      hTn.const_mul _, ?_⟩
    filter_upwards [IIIa.mpRho2_ae_mem] with p hp y' hy'
    exact hdom m p hp y' hy'
  obtain ⟨_, hi0, _⟩ := IIIa.mp_V_diff IIIa.sepKernelBounds μ hμ ρo ρi hρo hρ G hGm hGs hint xo hxo i
  have hEq : (fun x => IIIa.sepVmu0 μ G x i) =ᶠ[𝓝 xo] fun x => ∫ p, F p x ∂IIIa.mpRho2 := by
    filter_upwards [hU.mem_nhds hxoU] with x hx
    exact IIIa.mp_V_link μ G x i (hi0 x hx)
  have hcd : ContDiffAt ℝ ∞ (fun x => IIIa.sepVmu0 μ G x i) xo :=
    ((UnforcedLeray.L09.contDiffOn_integral hU hsmooth hmeas hLoc).contDiffAt
      (hU.mem_nhds hxoU)).congr_of_eventuallyEq hEq
  have hItEq : iteratedFDeriv ℝ n (fun x => IIIa.sepVmu0 μ G x i) xo =
      ∫ p, iteratedFDeriv ℝ n (F p) xo ∂IIIa.mpRho2 := by
    rw [(hEq.iteratedFDeriv ℝ n).eq_of_nhds]
    exact UnforcedLeray.L09.iteratedFDeriv_integral_eq hU hsmooth hmeas hLoc n hxoU
  have hItInt : Integrable (fun p => iteratedFDeriv ℝ n (F p) xo) IIIa.mpRho2 :=
    hLoc.integrable hmeas n hxoU
  refine ⟨hcd, fun m => ?_⟩
  set Λm : (Space [×n]→L[ℝ] ℂ) →L[ℝ] ℂ :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Space) ℂ m
  have hpt : ∀ p : ℝ × ((ℝ × ℝ) × ℝ), p.1 ∈ Ioo (0 : ℝ) 1 →
      Λm (iteratedFDeriv ℝ n (F p) xo) = mpVdIter n μ G p xo m i := by
    intro p hp
    change iteratedFDeriv ℝ n (F p) xo m = mpVdIter n μ G p xo m i
    rw [mpVF_iteratedFDeriv_eq n μ ρo G hGs p xo (fun hw => (hgapU p hp hw xo hxoU).2) i]
    unfold mpVdIter
    simp only [sum_apply, smul_apply, derivShiftCLM_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  have hInt_m : Integrable (fun p => mpVdIter n μ G p xo m i) IIIa.mpRho2 := by
    refine (Λm.integrable_comp hItInt).congr ?_
    filter_upwards [IIIa.mpRho2_ae_mem] with p hp using hpt p hp
  refine ⟨?_, hInt_m⟩
  have h1 : iteratedFDeriv ℝ n (fun x => IIIa.sepVmu0 μ G x i) xo m =
      ∫ p, Λm (iteratedFDeriv ℝ n (F p) xo) ∂IIIa.mpRho2 := by
    rw [hItEq, Λm.integral_comp_comm hItInt]
    rfl
  rw [h1]
  refine integral_congr_ae ?_
  filter_upwards [IIIa.mpRho2_ae_mem] with p hp using hpt p hp

theorem mp_V_iter_eval (n : ℕ) (μ : ℂ) (hμ : -(1 / 4) < μ.re) (ρo ρi : ℝ)
    (hρo : 0 ≤ ρo) (hρ : ρo < ρi) (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hGm : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ => G w.1 w.2 i j)
    (hGs : ∀ x' Y, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → G x' Y = 0)
    (hint : Integrable (fun w : (ℝ × ℝ) × ℝ => IIIa.tensorNorm (G w.1 w.2)) volume)
    (xo : Space) (hxo : ρi ≤ Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2)) :
    ContDiffAt ℝ ∞ (IIIa.sepVmu0 μ G) xo ∧
      ∀ (m : Fin n → Space) (i : Fin 3),
        (iteratedFDeriv ℝ n (IIIa.sepVmu0 μ G) xo m) i =
          ∫ p, mpVdIter n μ G p xo m i ∂IIIa.mpRho2 ∧
        Integrable (fun p => mpVdIter n μ G p xo m i) IIIa.mpRho2 := by
  have hcomp := fun i => mp_V_iter_comp n μ hμ ρo ρi hρo hρ G hGm hGs hint xo hxo i
  have hcd : ContDiffAt ℝ ∞ (IIIa.sepVmu0 μ G) xo :=
    contDiffAt_pi.2 fun i => (hcomp i).1
  refine ⟨hcd, fun m i => ?_⟩
  rw [iteratedFDeriv_pi_apply (fun i' => ((hcomp i').1.of_le (by exact_mod_cast le_top))) m i]
  exact (hcomp i).2 m

/-! ## 5. Pointwise and integral comparison of `mpHWIter n` and `mpVdIter n` -/

theorem mp_diff_iter_pointwise (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν ε : ℝ) (μ : ℂ) (ρo ρi : ℝ), 0 < ν → ν ≤ 1 → 0 < ε → ε ≤ 1 →
      -(1 / 4) < μ.re → 0 ≤ ρo → ρo < ρi →
      ∀ (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ),
        (∀ x' Y, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → G x' Y = 0) →
      ∀ (xo : Space), ρi ≤ Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) → ∀ (m : Fin n → Space) (i : Fin 3)
        (p : ℝ × ((ℝ × ℝ) × ℝ)), p.1 ∈ Ioo (0 : ℝ) 1 →
        ‖mpHWIter n ν ε μ G xo m i p - mpVdIter n μ G p xo m i‖ ≤
          C * ε * (1 + |p.2.2|) *
            ((ρi - ρo) ^ (-6 - (n : ℝ)) + (ρi - ρo) ^ (-5 - (n : ℝ))) *
            (∏ l : Fin n, ‖m l‖) * IIIa.tensorNorm (G p.2.1 p.2.2) := by
  obtain ⟨Ck, hCk0, hCk⟩ := sepKernelDiffIter (n + 1)
  refine ⟨18 * Ck, by positivity, ?_⟩
  intro ν ε μ ρo ρi hν hν1 hε hε1 hμ hρo hρ G hGs xo hxo m i p hp
  obtain ⟨l, w⟩ := p
  simp only at hp
  have hD : 0 < ρi - ρo := by linarith
  have hD1 : 0 ≤ (ρi - ρo) ^ (-6 - (n : ℝ)) := Real.rpow_nonneg hD.le _
  have hD2 : 0 ≤ (ρi - ρo) ^ (-5 - (n : ℝ)) := Real.rpow_nonneg hD.le _
  have hprod0 : 0 ≤ ∏ idx : Fin n, ‖m idx‖ :=
    Finset.prod_nonneg fun _ _ => norm_nonneg _
  by_cases hw : Real.sqrt (w.1.1 ^ 2 + w.1.2 ^ 2) ≤ ρo
  · have hs : 0 < ν * (1 - l ^ 2) * ε ^ 2 :=
      mul_pos (mul_pos hν (by nlinarith [hp.1, hp.2])) (by positivity)
    have hgap := IIIa.mp_gap ρo ρi xo xo hxo l hp w hw
    simp only [sub_self, norm_zero, sub_zero] at hgap
    set u0 : Space := xo - l • IIIa.mpV3 w with hu0
    set u : Space := xo - l • (!₂[w.1.1, w.1.2, ε * w.2] : Space) with hu
    have hu0c : u 0 = u0 0 := by simp [hu, hu0, IIIa.mpV3]
    have hu1c : u 1 = u0 1 := by simp [hu, hu0, IIIa.mpV3]
    have hnorm : ‖u - u0‖ ≤ ε * |w.2| := by
      have : u - u0 = (-(l * (ε * w.2))) • coordinateVector 2 := by
        ext idx
        fin_cases idx <;> simp [hu, hu0, IIIa.mpV3, coordinateVector]
      rw [this, norm_smul, IIIa.mp_norm_e, mul_one, Real.norm_eq_abs, abs_neg, abs_mul, abs_mul,
        abs_of_pos hp.1, abs_of_pos hε]
      calc l * (ε * |w.2|) ≤ 1 * (ε * |w.2|) := by gcongr; exact hp.2.le
        _ = ε * |w.2| := one_mul _
    have hsle : ν * (1 - l ^ 2) * ε ^ 2 ≤ ε := by
      have h1 : ν * (1 - l ^ 2) ≤ 1 := by nlinarith [hp.1, hp.2]
      have h2 : ε ^ 2 ≤ ε := by nlinarith
      calc ν * (1 - l ^ 2) * ε ^ 2 ≤ 1 * ε ^ 2 := by gcongr
        _ ≤ ε := by linarith
    have hdiff : mpHWIter n ν ε μ G xo m i (l, w) - mpVdIter n μ G (l, w) xo m i =
        -2 * ((l : ℂ) ^ (2 * μ + 2) * ∑ j : Fin 3, ∑ k : Fin 3,
          ((((iteratedFDeriv ℝ (n + 1) (fun x => IIIa.heatLerayK (ν * (1 - l ^ 2) * ε ^ 2) i j x) u -
              iteratedFDeriv ℝ (n + 1) (fun x => IIIa.heatLerayK0 i j x) u0)
                (Fin.snoc m (coordinateVector k)) : ℝ) : ℂ) *
            ((G w.1 w.2 j k : ℝ) : ℂ))) := by
      unfold mpHWIter mpVdIter
      simp only [sub_apply, Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib]
      ring
    rw [hdiff]
    have hb : ∀ j k : Fin 3,
        ‖((((iteratedFDeriv ℝ (n + 1) (fun x => IIIa.heatLerayK (ν * (1 - l ^ 2) * ε ^ 2) i j x) u -
            iteratedFDeriv ℝ (n + 1) (fun x => IIIa.heatLerayK0 i j x) u0)
              (Fin.snoc m (coordinateVector k)) : ℝ) : ℂ) *
          ((G w.1 w.2 j k : ℝ) : ℂ))‖ ≤
        (Ck * (ε + ε * |w.2|) *
          ((ρi - ρo) ^ (-6 - (n : ℝ)) + (ρi - ρo) ^ (-5 - (n : ℝ))) *
          (∏ idx : Fin n, ‖m idx‖)) * IIIa.tensorNorm (G w.1 w.2) := by
      intro j k
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
      set M := iteratedFDeriv ℝ (n + 1) (fun x => IIIa.heatLerayK (ν * (1 - l ^ 2) * ε ^ 2) i j x) u -
        iteratedFDeriv ℝ (n + 1) (fun x => IIIa.heatLerayK0 i j x) u0
      have h1 : |M (Fin.snoc m (coordinateVector k))| ≤ ‖M‖ * ∏ idx : Fin n, ‖m idx‖ := by
        have h := M.le_opNorm (Fin.snoc m (coordinateVector k))
        rw [Fin.prod_univ_castSucc] at h
        simp only [Fin.snoc_castSucc, Fin.snoc_last, IIIa.mp_norm_e, mul_one] at h
        exact (Real.norm_eq_abs _).symm ▸ h
      have h2 := hCk i j (ν * (1 - l ^ 2) * ε ^ 2) hs u0 u (ρi - ρo) hD hgap hu0c hu1c
      have he1 : (-5 - (((n + 1 : ℕ) : ℝ))) = -6 - (n : ℝ) := by push_cast; ring
      have he2 : (-4 - (((n + 1 : ℕ) : ℝ))) = -5 - (n : ℝ) := by push_cast; ring
      rw [he1, he2] at h2
      have h3 : ‖M‖ ≤
          Ck * (ε + ε * |w.2|) * ((ρi - ρo) ^ (-6 - (n : ℝ)) + (ρi - ρo) ^ (-5 - (n : ℝ))) := by
        refine h2.trans ?_
        have hsum : ν * (1 - l ^ 2) * ε ^ 2 + ‖u - u0‖ ≤ ε + ε * |w.2| := add_le_add hsle hnorm
        have hDD : 0 ≤ (ρi - ρo) ^ (-6 - (n : ℝ)) + (ρi - ρo) ^ (-5 - (n : ℝ)) := add_nonneg hD1 hD2
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hCk0) hDD
      have h4 : |M (Fin.snoc m (coordinateVector k))| ≤
          (Ck * (ε + ε * |w.2|) *
            ((ρi - ρo) ^ (-6 - (n : ℝ)) + (ρi - ρo) ^ (-5 - (n : ℝ)))) *
          (∏ idx : Fin n, ‖m idx‖) :=
        h1.trans (mul_le_mul_of_nonneg_right h3 hprod0)
      exact mul_le_mul h4 (IIIa.mp_entry_le _ j k) (abs_nonneg _) (by positivity)
    have hs9 := IIIa.mp_sum9 _ _ hb
    have hw1 := IIIa.mp_norm_cpow_le μ hμ l hp
    rw [norm_mul, norm_mul]
    have hn2 : ‖(-2 : ℂ)‖ = 2 := by simp
    rw [hn2]
    calc 2 * (‖(l : ℂ) ^ (2 * μ + 2)‖ * ‖∑ j : Fin 3, ∑ k : Fin 3, _‖)
        ≤ 2 * (1 * (9 * ((Ck * (ε + ε * |w.2|) *
            ((ρi - ρo) ^ (-6 - (n : ℝ)) + (ρi - ρo) ^ (-5 - (n : ℝ))) *
            (∏ idx : Fin n, ‖m idx‖)) * IIIa.tensorNorm (G w.1 w.2)))) := by gcongr
      _ = _ := by ring
  · have hw' : ρo < Real.sqrt (w.1.1 ^ 2 + w.1.2 ^ 2) := lt_of_not_ge hw
    have h0 : G w.1 w.2 = 0 := hGs _ _ hw'
    have : mpHWIter n ν ε μ G xo m i (l, w) - mpVdIter n μ G (l, w) xo m i = 0 := by
      simp [mpHWIter, mpVdIter, h0]
    rw [this, norm_zero]
    have : 0 ≤ IIIa.tensorNorm (G w.1 w.2) := Real.sqrt_nonneg _
    positivity

theorem iteratedFDeriv_sepW_sub_sepVmu0_le (n : ℕ) (C0 : ℝ) (hC0 : 0 ≤ C0)
    (hdiff : ∀ (ν ε : ℝ) (μ : ℂ) (ρo ρi : ℝ), 0 < ν → ν ≤ 1 → 0 < ε → ε ≤ 1 →
      -(1 / 4) < μ.re → 0 ≤ ρo → ρo < ρi →
      ∀ (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ),
        (∀ x' Y, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → G x' Y = 0) →
      ∀ (xo : Space), ρi ≤ Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) → ∀ (m : Fin n → Space) (i : Fin 3)
        (p : ℝ × ((ℝ × ℝ) × ℝ)), p.1 ∈ Ioo (0 : ℝ) 1 →
        ‖mpHWIter n ν ε μ G xo m i p - mpVdIter n μ G p xo m i‖ ≤
          C0 * ε * (1 + |p.2.2|) *
            ((ρi - ρo) ^ (-6 - (n : ℝ)) + (ρi - ρo) ^ (-5 - (n : ℝ))) *
            (∏ l : Fin n, ‖m l‖) * IIIa.tensorNorm (G p.2.1 p.2.2))
    (ν c ε ρo ρi : ℝ) (μ : ℂ) (hν : 0 < ν) (hν1 : ν ≤ 1) (hc : 0 < c)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hρo : 0 ≤ ρo) (hρ : ρo < ρi) (hμ : -(1 / 4) < μ.re)
    (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hGm : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ => G w.1 w.2 i j)
    (hGs : ∀ x' Y, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → G x' Y = 0)
    (hwint : Integrable (fun w : (ℝ × ℝ) × ℝ => (1 + |w.2|) * IIIa.tensorNorm (G w.1 w.2)) volume)
    (hint : Integrable (fun w : (ℝ × ℝ) × ℝ => IIIa.tensorNorm (G w.1 w.2)) volume)
    (xo : Space) (hxo : ρi ≤ Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2)) (τ : ℝ) :
    ‖iteratedFDeriv ℝ n (fun y => IIIa.sepW ν μ (IIIa.thinSource ε (IIIa.meanLift G)) y τ)
        (ε⁻¹ • xo) -
      (ε ^ (2 + n) : ℝ) • iteratedFDeriv ℝ n (IIIa.sepVmu0 μ G) xo‖ ≤
      C0 * ε ^ (3 + n) * ((ρi - ρo) ^ (-6 - (n : ℝ)) + (ρi - ρo) ^ (-5 - (n : ℝ))) *
        ∫ w : (ℝ × ℝ) × ℝ, (1 + |w.2|) * IIIa.tensorNorm (G w.1 w.2) := by
  have hD : 0 < ρi - ρo := by linarith
  have hD1 : 0 ≤ (ρi - ρo) ^ (-6 - (n : ℝ)) := Real.rpow_nonneg hD.le _
  have hD2 : 0 ≤ (ρi - ρo) ^ (-5 - (n : ℝ)) := Real.rpow_nonneg hD.le _
  set Nr : ℝ := ∫ w : (ℝ × ℝ) × ℝ, (1 + |w.2|) * IIIa.tensorNorm (G w.1 w.2) with hNr
  have hNr0 : 0 ≤ Nr := integral_nonneg fun w => mul_nonneg (by positivity) (tn_nonneg _)
  obtain ⟨_, hWf⟩ := mp_W_iter_eval n ν c ε ρo ρi μ hν hc hε hρo hρ hμ G hGm hGs hint xo hxo τ
  obtain ⟨_, hVf⟩ := mp_V_iter_eval n μ hμ ρo ρi hρo hρ G hGm hGs hint xo hxo
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => ?_
  have hprod0 : 0 ≤ ∏ l : Fin n, ‖m l‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  obtain ⟨hWe, hWi⟩ := hWf m i
  obtain ⟨hVe, hVi⟩ := hVf m i
  simp only [sub_apply, smul_apply, Pi.sub_apply, Pi.smul_apply]
  rw [hWe, hVe, Complex.real_smul]
  push_cast
  rw [← mul_sub, ← integral_sub hWi hVi, norm_mul]
  set K := C0 * ε * ((ρi - ρo) ^ (-6 - (n : ℝ)) + (ρi - ρo) ^ (-5 - (n : ℝ))) *
    (∏ l : Fin n, ‖m l‖)
  have hB : Integrable (fun p : ℝ × ((ℝ × ℝ) × ℝ) =>
      K * ((1 + |p.2.2|) * IIIa.tensorNorm (G p.2.1 p.2.2))) IIIa.mpRho2 := by
    have h := (integrable_const (1 : ℝ) (μ := volume.restrict (Ioo (0 : ℝ) 1))).mul_prod hwint
    exact (h.congr (Eventually.of_forall fun p => by simp)).const_mul _
  have hnorm : ‖∫ p, (mpHWIter n ν ε μ G xo m i p - mpVdIter n μ G p xo m i) ∂IIIa.mpRho2‖ ≤
      ∫ p, K * ((1 + |p.2.2|) * IIIa.tensorNorm (G p.2.1 p.2.2)) ∂IIIa.mpRho2 := by
    refine norm_integral_le_of_norm_le hB ?_
    filter_upwards [IIIa.mpRho2_ae_mem] with p hp
    have := hdiff ν ε μ ρo ρi hν hν1 hε hε1 hμ hρo hρ G hGs xo hxo m i p hp
    calc _ ≤ _ := this
      _ = _ := by ring
  have hI : ∫ p, K * ((1 + |p.2.2|) * IIIa.tensorNorm (G p.2.1 p.2.2)) ∂IIIa.mpRho2 = K * Nr := by
    rw [integral_const_mul]
    congr 1
    have := integral_prod_mul (μ := volume.restrict (Ioo (0 : ℝ) 1))
      (ν := (volume : Measure ((ℝ × ℝ) × ℝ)))
      (fun _ => (1 : ℝ)) (fun w : (ℝ × ℝ) × ℝ => (1 + |w.2|) * IIIa.tensorNorm (G w.1 w.2))
    simp only [one_mul, integral_const, smul_eq_mul] at this
    unfold IIIa.mpRho2
    rw [hNr]
    simpa using this
  have hpow : ‖(ε : ℂ) ^ (2 + n)‖ = ε ^ (2 + n) := by
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hε.le]
  rw [hpow]
  calc ε ^ (2 + n) * ‖∫ p, (mpHWIter n ν ε μ G xo m i p - mpVdIter n μ G p xo m i) ∂IIIa.mpRho2‖
      ≤ ε ^ (2 + n) * (K * Nr) := by rw [← hI]; gcongr
    _ = C0 * ε ^ (3 + n) * ((ρi - ρo) ^ (-6 - (n : ℝ)) + (ρi - ρo) ^ (-5 - (n : ℝ))) *
          Nr * ∏ l : Fin n, ‖m l‖ := by
        have : ε ^ (2 + n) * ε = ε ^ (3 + n) := by
          have : 3 + n = (2 + n) + 1 := by omega
          rw [this, pow_succ]
        unfold K
        calc ε ^ (2 + n) * (C0 * ε * ((ρi - ρo) ^ (-6 - (n : ℝ)) + (ρi - ρo) ^ (-5 - (n : ℝ))) *
              (∏ l : Fin n, ‖m l‖) * Nr)
            = C0 * (ε ^ (2 + n) * ε) * ((ρi - ρo) ^ (-6 - (n : ℝ)) + (ρi - ρo) ^ (-5 - (n : ℝ))) *
              Nr * ∏ l : Fin n, ‖m l‖ := by ring
          _ = _ := by rw [this]

/-! ## 6. Iterated derivatives of `srcX0` and `newtonX0` -/

theorem iteratedFDeriv_srcX0 (n : ℕ) (ν μ : ℝ)
    (src : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (y : Space)
    (hA : ContDiffAt ℝ ∞ (fun y => IIIa.sepW ν (μ : ℂ) src y τ) y)
    (hB : ContDiffAt ℝ ∞ (fun y => IIIa.sepW ν ((μ : ℂ) + 1) src y τ) y) :
    iteratedFDeriv ℝ n (srcX0 ν μ src τ) y =
      PhasePrim.reMap.compContinuousMultilinearMap
        (iteratedFDeriv ℝ n (fun y => IIIa.sepW ν (μ : ℂ) src y τ) y -
          iteratedFDeriv ℝ n (fun y => IIIa.sepW ν ((μ : ℂ) + 1) src y τ) y) := by
  have hAn : ContDiffAt ℝ n (fun y => IIIa.sepW ν (μ : ℂ) src y τ) y :=
    hA.of_le (by exact_mod_cast le_top)
  have hBn : ContDiffAt ℝ n (fun y => IIIa.sepW ν ((μ : ℂ) + 1) src y τ) y :=
    hB.of_le (by exact_mod_cast le_top)
  have hw : srcX0 ν μ src τ = ⇑PhasePrim.reMap ∘
      fun x => IIIa.sepW ν (μ : ℂ) src x τ - IIIa.sepW ν ((μ : ℂ) + 1) src x τ := rfl
  rw [hw, PhasePrim.reMap.iteratedFDeriv_comp_left (hAn.sub hBn) le_rfl]
  change PhasePrim.reMap.compContinuousMultilinearMap
      (iteratedFDeriv ℝ n ((fun x => IIIa.sepW ν (μ : ℂ) src x τ) -
        (fun x => IIIa.sepW ν ((μ : ℂ) + 1) src x τ)) y) = _
  rw [iteratedFDeriv_sub_apply hAn hBn]

theorem iteratedFDeriv_comp_smul (n : ℕ) {ε : ℝ} (hε : 0 < ε) (f : Space → Fin 3 → ℂ)
    (xo : Space) :
    iteratedFDeriv ℝ n (fun y : Space => f (ε • y)) (ε⁻¹ • xo) =
      (ε ^ n : ℝ) • iteratedFDeriv ℝ n f xo := by
  let g : Space ≃L[ℝ] Space := ContinuousLinearEquiv.smulLeft (Units.mk0 ε hε.ne')
  have h1 := g.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (mem_univ (g (ε⁻¹ • xo))) n
  simp only [preimage_univ, iteratedFDerivWithin_univ] at h1
  have hg : g (ε⁻¹ • xo) = xo := smul_inv_smul₀ hε.ne' xo
  change iteratedFDeriv ℝ n (f ∘ ⇑g) (ε⁻¹ • xo) = _
  rw [h1, hg]
  ext m i
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    smul_apply, Pi.smul_apply]
  have hm : (fun idx : Fin n => (g : Space →L[ℝ] Space) (m idx)) = fun idx => ε • m idx := rfl
  rw [hm, ContinuousMultilinearMap.map_smul_univ]
  simp [Finset.prod_const]

theorem iteratedFDeriv_newtonX0 (n : ℕ) {ε μ : ℝ} (hε : 0 < ε)
    (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) {xo : Space}
    (hV0 : ContDiffAt ℝ ∞ (IIIa.sepVmu0 (μ : ℂ) G) xo)
    (hV1 : ContDiffAt ℝ ∞ (IIIa.sepVmu0 ((μ : ℂ) + 1) G) xo) :
    iteratedFDeriv ℝ n (newtonX0 ε μ G τ) (ε⁻¹ • xo) =
      PhasePrim.reMap.compContinuousMultilinearMap
        ((ε ^ (2 + n) : ℝ) • iteratedFDeriv ℝ n (IIIa.sepVmu0 (μ : ℂ) G) xo -
          (ε ^ (2 + n) : ℝ) • iteratedFDeriv ℝ n (IIIa.sepVmu0 ((μ : ℂ) + 1) G) xo) := by
  have hsmul : ContDiffAt ℝ n (fun y : Space => ε • y) (ε⁻¹ • xo) :=
    (contDiff_const_smul ε).contDiffAt
  have h0n : ContDiffAt ℝ n (fun y : Space => IIIa.sepVmu0 (μ : ℂ) G (ε • y)) (ε⁻¹ • xo) := by
    have hV0' : ContDiffAt ℝ n (IIIa.sepVmu0 (μ : ℂ) G) (ε • (ε⁻¹ • xo)) := by
      rw [smul_inv_smul₀ hε.ne']
      exact hV0.of_le (by exact_mod_cast le_top)
    exact hV0'.comp (ε⁻¹ • xo) hsmul
  have h1n : ContDiffAt ℝ n (fun y : Space => IIIa.sepVmu0 ((μ : ℂ) + 1) G (ε • y)) (ε⁻¹ • xo) := by
    have hV1' : ContDiffAt ℝ n (IIIa.sepVmu0 ((μ : ℂ) + 1) G) (ε • (ε⁻¹ • xo)) := by
      rw [smul_inv_smul₀ hε.ne']
      exact hV1.of_le (by exact_mod_cast le_top)
    exact hV1'.comp (ε⁻¹ • xo) hsmul
  have hfn : newtonX0 ε μ G τ = ⇑PhasePrim.reMap ∘
      fun y => (ε ^ 2 : ℝ) • (IIIa.sepVmu0 (μ : ℂ) G (ε • y) -
        IIIa.sepVmu0 ((μ : ℂ) + 1) G (ε • y)) := by
    funext y
    simp [newtonX0, map_smul]
  rw [hfn, PhasePrim.reMap.iteratedFDeriv_comp_left ((h0n.sub h1n).const_smul (ε ^ 2 : ℝ)) le_rfl,
    iteratedFDeriv_const_smul_apply' (h0n.sub h1n)]
  change PhasePrim.reMap.compContinuousMultilinearMap
      ((ε ^ 2 : ℝ) • iteratedFDeriv ℝ n ((fun y' => IIIa.sepVmu0 (μ : ℂ) G (ε • y')) -
        (fun y' => IIIa.sepVmu0 ((μ : ℂ) + 1) G (ε • y'))) (ε⁻¹ • xo)) = _
  rw [iteratedFDeriv_sub_apply h0n h1n,
    iteratedFDeriv_comp_smul n hε _ xo, iteratedFDeriv_comp_smul n hε _ xo,
    smul_sub, smul_smul, smul_smul, ← pow_add]

/-! ## 7. Proof of `YBWidth.sepCommMainDiff2` -/

private theorem annulus_gap_rpow2_le (ν c r : ℝ) (hν : 0 < ν) (hν1 : ν ≤ 1) (hc : 0 < c)
    (hr1 : Real.sqrt ν ≤ r) (hr2 : r ≤ Real.sqrt (5 * ν / 4)) :
    ν * r⁻¹ * ((Real.sqrt ν - Real.sqrt (5 * ν / 6)) ^ (-8 : ℝ) +
        (Real.sqrt ν - Real.sqrt (5 * ν / 6)) ^ (-7 : ℝ)) ≤
      2 * 32 * 12 ^ 8 * (1 + ν⁻¹ + c) ^ 9 * r ^ (-5 : ℝ) := by
  set D := Real.sqrt ν - Real.sqrt (5 * ν / 6)
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hr0 : 0 < r := lt_of_lt_of_le hsν hr1
  have hg := PhasePrim.gap_le ν hν
  have hD : 0 < D := by linarith
  have hν_le_sν : ν ≤ Real.sqrt ν := by
    have := Real.sqrt_le_sqrt (mul_le_of_le_one_left hν.le hν1 : ν * ν ≤ ν)
    rwa [Real.sqrt_mul_self hν.le] at this
  have hM1 : 1 ≤ 1 + ν⁻¹ + c := by
    have : 0 < ν⁻¹ := inv_pos.2 hν
    linarith
  have hM0 : 0 ≤ 1 + ν⁻¹ + c := by linarith
  have hDinv : D⁻¹ ≤ 12 * (1 + ν⁻¹ + c) := by
    have h1 : D⁻¹ ≤ 12 * (Real.sqrt ν)⁻¹ := by
      rw [inv_le_iff_one_le_mul₀' hD]
      have : D * (12 * (Real.sqrt ν)⁻¹) = 12 * D / Real.sqrt ν := by ring
      rw [this, one_le_div hsν]
      linarith
    have h2 : (Real.sqrt ν)⁻¹ ≤ ν⁻¹ := inv_anti₀ hν hν_le_sν
    linarith
  have hrinv : ν * r⁻¹ ≤ 1 + ν⁻¹ + c := by
    have h1 : r⁻¹ ≤ (Real.sqrt ν)⁻¹ := inv_anti₀ hsν hr1
    have h2 : (Real.sqrt ν)⁻¹ ≤ ν⁻¹ := inv_anti₀ hν hν_le_sν
    have h3 : ν * r⁻¹ ≤ 1 * r⁻¹ := mul_le_mul_of_nonneg_right hν1 (inv_nonneg.2 hr0.le)
    linarith
  have hr_le_2 : r ≤ 2 := by
    refine hr2.trans ?_
    have : 5 * ν / 4 ≤ 4 := by linarith
    calc Real.sqrt (5 * ν / 4) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt this
      _ = 2 := by norm_num
  have hr5_bound : 1 ≤ 32 * r ^ (-5 : ℝ) := by
    have e5 : r ^ (-5 : ℝ) = (r ^ 5)⁻¹ := by
      rw [Real.rpow_neg hr0.le, show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [e5, ← div_eq_mul_inv, one_le_div (pow_pos hr0 5)]
    calc r ^ 5 ≤ 2 ^ 5 := pow_le_pow_left₀ hr0.le hr_le_2 5
      _ = 32 := by norm_num
  have e8 : D ^ (-8 : ℝ) = (D⁻¹) ^ 8 := by
    rw [Real.rpow_neg hD.le, show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, inv_pow]
  have e7 : D ^ (-7 : ℝ) = (D⁻¹) ^ 7 := by
    rw [Real.rpow_neg hD.le, show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, inv_pow]
  rw [e8, e7]
  have hp8 : (D⁻¹) ^ 8 ≤ (12 * (1 + ν⁻¹ + c)) ^ 8 :=
    pow_le_pow_left₀ (inv_nonneg.2 hD.le) hDinv 8
  have hp7 : (D⁻¹) ^ 7 ≤ (12 * (1 + ν⁻¹ + c)) ^ 8 := by
    calc (D⁻¹) ^ 7 ≤ (12 * (1 + ν⁻¹ + c)) ^ 7 :=
          pow_le_pow_left₀ (inv_nonneg.2 hD.le) hDinv 7
      _ ≤ (12 * (1 + ν⁻¹ + c)) ^ 8 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hsum : (D⁻¹) ^ 8 + (D⁻¹) ^ 7 ≤ 2 * 12 ^ 8 * (1 + ν⁻¹ + c) ^ 8 := by
    have : (12 * (1 + ν⁻¹ + c)) ^ 8 = 12 ^ 8 * (1 + ν⁻¹ + c) ^ 8 := by ring
    linarith
  have hmul : ν * r⁻¹ * ((D⁻¹) ^ 8 + (D⁻¹) ^ 7) ≤ 2 * 12 ^ 8 * (1 + ν⁻¹ + c) ^ 9 := by
    calc ν * r⁻¹ * ((D⁻¹) ^ 8 + (D⁻¹) ^ 7)
        ≤ (1 + ν⁻¹ + c) * (2 * 12 ^ 8 * (1 + ν⁻¹ + c) ^ 8) :=
          mul_le_mul hrinv hsum (by positivity) hM0
      _ = 2 * 12 ^ 8 * (1 + ν⁻¹ + c) ^ 9 := by ring
  calc ν * r⁻¹ * ((D⁻¹) ^ 8 + (D⁻¹) ^ 7)
      = (ν * r⁻¹ * ((D⁻¹) ^ 8 + (D⁻¹) ^ 7)) * 1 := by ring
    _ ≤ (2 * 12 ^ 8 * (1 + ν⁻¹ + c) ^ 9) * (32 * r ^ (-5 : ℝ)) :=
        mul_le_mul hmul hr5_bound zero_le_one (by positivity)
    _ = 2 * 32 * 12 ^ 8 * (1 + ν⁻¹ + c) ^ 9 * r ^ (-5 : ℝ) := by ring

/-- **Proof of `YBWidth.SepCommMainDiff2`** (`PartIII-b:C/rep/8/1/1/2/5/2/1/3`). -/
theorem sepCommMainDiff2 : YBWidth.SepCommMainDiff2 := by
  obtain ⟨C0, hC0, hdiff⟩ := mp_diff_iter_pointwise 2
  refine ⟨4 * C0 * (2 * 32 * 12 ^ 8), 9, by positivity, ?_⟩
  intro ν c ε μ hν hν1 hc hε hε1 hμ0 hμ1 G hGm hGs hwint τ xo hxo hle
  set ρo := Real.sqrt (5 * ν / 6)
  set ρi := Real.sqrt ν
  have hρo : 0 ≤ ρo := Real.sqrt_nonneg _
  have hρ : ρo < ρi := Real.sqrt_lt_sqrt (by positivity) (by linarith)
  set r := Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2)
  have hρi_xo : ρi ≤ r := Real.sqrt_le_sqrt hxo
  have hr_le : r ≤ Real.sqrt (5 * ν / 4) := Real.sqrt_le_sqrt hle
  have hr : 0 < r := lt_of_lt_of_le (Real.sqrt_pos.2 hν) hρi_xo
  have hreμ : -(1 / 4) < ((μ : ℝ) : ℂ).re := by simp; linarith
  have hreμ1 : -(1 / 4) < ((μ : ℂ) + 1).re := by simp; linarith
  have hmeas : Measurable fun w : (ℝ × ℝ) × ℝ => IIIa.tensorNorm (G w.1 w.2) := by
    unfold IIIa.tensorNorm
    exact Measurable.sqrt (Finset.measurable_sum _ fun i _ =>
      Finset.measurable_sum _ fun j _ => (hGm i j).pow_const 2)
  have hint : Integrable (fun w : (ℝ × ℝ) × ℝ => IIIa.tensorNorm (G w.1 w.2)) volume := by
    refine Integrable.mono' hwint hmeas.aestronglyMeasurable (Eventually.of_forall fun w => ?_)
    rw [Real.norm_of_nonneg (tn_nonneg _)]
    exact le_mul_of_one_le_left (tn_nonneg _) (by linarith [abs_nonneg w.2])
  set T := IIIa.thinSource ε (IIIa.meanLift G)
  have hW0 := (mp_W_iter_eval 2 ν c ε ρo ρi (μ : ℂ) hν hc hε hρo hρ hreμ G hGm hGs hint xo hρi_xo τ).1
  have hW1 := (mp_W_iter_eval 2 ν c ε ρo ρi ((μ : ℂ) + 1) hν hc hε hρo hρ hreμ1 G hGm hGs hint xo hρi_xo τ).1
  have hV0 := (mp_V_iter_eval 2 (μ : ℂ) hreμ ρo ρi hρo hρ G hGm hGs hint xo hρi_xo).1
  have hV1 := (mp_V_iter_eval 2 ((μ : ℂ) + 1) hreμ1 ρo ρi hρo hρ G hGm hGs hint xo hρi_xo).1
  rw [iteratedFDeriv_srcX0 2 ν μ T τ (ε⁻¹ • xo) hW0 hW1,
    iteratedFDeriv_newtonX0 2 hε G τ hV0 hV1]
  set A0 := iteratedFDeriv ℝ 2 (fun y => IIIa.sepW ν (μ : ℂ) T y τ) (ε⁻¹ • xo)
  set A1 := iteratedFDeriv ℝ 2 (fun y => IIIa.sepW ν ((μ : ℂ) + 1) T y τ) (ε⁻¹ • xo)
  set B0 := (ε ^ (2 + 2) : ℝ) • iteratedFDeriv ℝ 2 (IIIa.sepVmu0 (μ : ℂ) G) xo
  set B1 := (ε ^ (2 + 2) : ℝ) • iteratedFDeriv ℝ 2 (IIIa.sepVmu0 ((μ : ℂ) + 1) G) xo
  have hsub : PhasePrim.reMap.compContinuousMultilinearMap (A0 - A1) -
      PhasePrim.reMap.compContinuousMultilinearMap (B0 - B1) =
      PhasePrim.reMap.compContinuousMultilinearMap ((A0 - B0) - (A1 - B1)) := by
    refine ContinuousMultilinearMap.ext fun m => ?_
    change PhasePrim.reMap (A0 m - A1 m) - PhasePrim.reMap (B0 m - B1 m) =
      PhasePrim.reMap ((A0 m - B0 m) - (A1 m - B1 m))
    rw [← map_sub]
    congr 1; abel
  rw [hsub]
  have h_re : ‖PhasePrim.reMap.compContinuousMultilinearMap ((A0 - B0) - (A1 - B1))‖ ≤
      2 * (‖A0 - B0‖ + ‖A1 - B1‖) := by
    calc ‖PhasePrim.reMap.compContinuousMultilinearMap ((A0 - B0) - (A1 - B1))‖
        ≤ ‖PhasePrim.reMap‖ * ‖(A0 - B0) - (A1 - B1)‖ :=
          ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
      _ ≤ 2 * (‖A0 - B0‖ + ‖A1 - B1‖) :=
          mul_le_mul PhasePrim.opNorm_reMap_le (norm_sub_le _ _) (norm_nonneg _) (by norm_num)
  set Nr : ℝ := ∫ w : (ℝ × ℝ) × ℝ, (1 + |w.2|) * IIIa.tensorNorm (G w.1 w.2)
  have hNr0 : 0 ≤ Nr := integral_nonneg fun w => mul_nonneg (by positivity) (tn_nonneg _)
  have hB0 := iteratedFDeriv_sepW_sub_sepVmu0_le 2 C0 hC0 hdiff ν c ε ρo ρi (μ : ℂ)
    hν hν1 hc hε hε1 hρo hρ hreμ G hGm hGs hwint hint xo hρi_xo τ
  have hB1 := iteratedFDeriv_sepW_sub_sepVmu0_le 2 C0 hC0 hdiff ν c ε ρo ρi ((μ : ℂ) + 1)
    hν hν1 hc hε hε1 hρo hρ hreμ1 G hGm hGs hwint hint xo hρi_xo τ
  have he8 : (-6 - ((2 : ℕ) : ℝ)) = (-8 : ℝ) := by norm_num
  have he7 : (-5 - ((2 : ℕ) : ℝ)) = (-7 : ℝ) := by norm_num
  have he5 : (3 + 2 : ℕ) = 5 := rfl
  rw [he8, he7, he5] at hB0 hB1
  have hsum : ‖PhasePrim.reMap.compContinuousMultilinearMap ((A0 - B0) - (A1 - B1))‖ ≤
      4 * C0 * ε ^ 5 * ((ρi - ρo) ^ (-8 : ℝ) + (ρi - ρo) ^ (-7 : ℝ)) * Nr := by
    linarith
  have hε6 : ε ^ 6 ≤ ε ^ 4 := by
    calc ε ^ 6 = ε ^ 4 * ε ^ 2 := by ring
      _ ≤ ε ^ 4 * 1 := mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
      _ = ε ^ 4 := mul_one _
  have hgap_pow := annulus_gap_rpow2_le ν c r hν hν1 hc hρi_xo hr_le
  have hD : 0 < ρi - ρo := by linarith
  have hD87 : 0 ≤ (ρi - ρo) ^ (-8 : ℝ) + (ρi - ρo) ^ (-7 : ℝ) :=
    add_nonneg (Real.rpow_nonneg hD.le _) (Real.rpow_nonneg hD.le _)
  calc ν * ε * r⁻¹ * ‖PhasePrim.reMap.compContinuousMultilinearMap ((A0 - B0) - (A1 - B1))‖
      ≤ ν * ε * r⁻¹ * (4 * C0 * ε ^ 5 * ((ρi - ρo) ^ (-8 : ℝ) + (ρi - ρo) ^ (-7 : ℝ)) * Nr) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 4 * C0 * (ν * r⁻¹ * ((ρi - ρo) ^ (-8 : ℝ) + (ρi - ρo) ^ (-7 : ℝ))) * ε ^ 6 * Nr := by ring
    _ ≤ 4 * C0 * (2 * 32 * 12 ^ 8 * (1 + ν⁻¹ + c) ^ 9 * r ^ (-5 : ℝ)) * ε ^ 4 * Nr := by
        gcongr
    _ = 4 * C0 * (2 * 32 * 12 ^ 8) * (1 + ν⁻¹ + c) ^ 9 * ε ^ 4 * r ^ (-5 : ℝ) * Nr := by ring

end YBWidth

end UnforcedLeray.Short.PartIIIb.Concrete
