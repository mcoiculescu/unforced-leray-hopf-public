import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F1
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.TrainGap.Lattice
import UnforcedLeray.Short.Spine.Proofs.EstVcRegularity

/-!
# `PartII-b:F1/2` — Train vs. planar vorticity gradient coefficient comparison (`TrainGradCoeffStep`)

Proves `trainGradCoeffStep_proof : Short.PartIIb.TrainGradCoeffStep` (`Sub/PartII-b_F1.lean`).

Given `m > 8` and `Sg > 0`, we produce `C_tr > 0` such that under `BgRegime p d dm dp`, `1 ≤ p.c`,
`δ ≥ 0`, `TrainCloseM m p.train Sg δ`, and `σ ∈ Icc 0 Sg`:
1. `IsCylWeightedCoeff p.c m C_tr (planarGradE σ)`;
2. `IsCylWeightedCoeff p.c m (C_tr * (p.c ^ (-2 : ℝ) + δ))`
   `(fun x => trainGradE p.train (σ / p.ν) x - planarGradE σ x)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.B0579 (Plane cell jb pd dir)
open UnforcedLeray.Cons.C03.Concrete (Params)

/-! ## 1. Continuity and weighted sup bound of `planarGradE σ` -/

theorem continuous_planarGradE (σ : ℝ) : Continuous (planarGradE σ) := by
  have hsc : Continuous fun x : Plane => ofPlane (scalePlane (1 + σ) x) := by
    have h1 : (fun x : Plane => ofPlane (scalePlane (1 + σ) x)) =
        fun x => ((x.1 / Real.sqrt (1 + σ) : ℝ) : ℂ) +
          ((x.2 / Real.sqrt (1 + σ) : ℝ) : ℂ) * Complex.I := by
      funext x
      exact ofPlane_eq_add_mul_I (scalePlane (1 + σ) x)
    rw [h1]
    fun_prop
  unfold planarGradE
  exact (continuous_const.mul (B0009.continuous_gradE0_fst.comp hsc)).prodMk
    (continuous_const.mul (B0009.continuous_gradE0_snd.comp hsc))

/-- Polynomial-times-Gaussian absorption: `(1 + s)^r e^{-β s} ≤ C` for `s ≥ 0` and `β > 0`. -/
private theorem rpow_mul_exp_neg_le (r : ℝ) (_hr : 0 ≤ r) {β : ℝ} (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 0 ≤ s → (1 + s) ^ r * Real.exp (-(β * s)) ≤ C := by
  set k : ℕ := ⌈r⌉₊ + 1
  have hrk : r ≤ (k : ℝ) := by
    dsimp [k]
    push_cast
    linarith [Nat.le_ceil r]
  refine ⟨(k.factorial : ℝ) * (1 / β) ^ k * Real.exp β + 1, by positivity, fun s hs => ?_⟩
  have h1s : 1 ≤ 1 + s := by linarith
  have hrpow : (1 + s) ^ r ≤ (1 + s) ^ k := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le h1s hrk
  set x : ℝ := β * (1 + s)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have h1 : x ^ k / (k.factorial : ℝ) ≤ Real.exp x := Real.pow_div_factorial_le_exp x hx k
  have hfac : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have h2 : x ^ k ≤ (k.factorial : ℝ) * Real.exp x := by
    have h3 := (div_le_iff₀ hfac).mp h1
    linarith [mul_comm (Real.exp x) (k.factorial : ℝ)]
  have h3 : x ^ k = β ^ k * (1 + s) ^ k := by dsimp [x]; rw [mul_pow]
  have hc : (1 / β) ^ k * β ^ k = 1 := by
    rw [← mul_pow, one_div_mul_cancel hβ.ne', one_pow]
  have h4 : (1 + s) ^ k ≤ ((k.factorial : ℝ) * (1 / β) ^ k) * Real.exp x := by
    calc (1 + s) ^ k = (1 / β) ^ k * (β ^ k * (1 + s) ^ k) := by rw [← mul_assoc, hc, one_mul]
      _ ≤ (1 / β) ^ k * ((k.factorial : ℝ) * Real.exp x) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [← h3]; exact h2
      _ = ((k.factorial : ℝ) * (1 / β) ^ k) * Real.exp x := by ring
  have hexp : Real.exp x * Real.exp (-(β * s)) = Real.exp β := by
    rw [← Real.exp_add]
    congr 1
    dsimp [x]; ring
  calc (1 + s) ^ r * Real.exp (-(β * s))
      ≤ (1 + s) ^ k * Real.exp (-(β * s)) :=
        mul_le_mul_of_nonneg_right hrpow (Real.exp_pos _).le
    _ ≤ (((k.factorial : ℝ) * (1 / β) ^ k) * Real.exp x) * Real.exp (-(β * s)) :=
        mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
    _ = ((k.factorial : ℝ) * (1 / β) ^ k) * (Real.exp x * Real.exp (-(β * s))) := by ring
    _ = (k.factorial : ℝ) * (1 / β) ^ k * Real.exp β := by rw [hexp]
    _ ≤ (k.factorial : ℝ) * (1 / β) ^ k * Real.exp β + 1 := by linarith

theorem planarGradE_sup_bound (k : ℝ) (hk : 0 ≤ k) (Sg : ℝ) (hSg : 0 < Sg) :
    ∃ M : ℝ, 0 < M ∧ ∀ σ ∈ Icc 0 Sg, ∀ x : Plane,
      (|(planarGradE σ x).1| + |(planarGradE σ x).2|) * jb x ^ k ≤ M := by
  obtain ⟨C, hC, hC_bd⟩ := rpow_mul_exp_neg_le (k + 2) (by linarith) (by norm_num : (0 : ℝ) < 1 / 4)
  refine ⟨4 * (1 + Sg) ^ k * C, by positivity, fun σ hσ x => ?_⟩
  set a : ℝ := 1 + σ
  have ha1 : 1 ≤ a := by dsimp [a]; linarith [hσ.1]
  have haSg : a ≤ 1 + Sg := by dsimp [a]; linarith [hσ.2]
  have ha0 : 0 < a := by linarith
  set y : ℂ := ofPlane (scalePlane a x)
  have hy_sq : ‖y‖ ^ 2 = (x.1 ^ 2 + x.2 ^ 2) / a := by
    rw [norm_ofPlane_sq, scalePlane, div_pow, div_pow, ← add_div, Real.sq_sqrt ha0.le]
  have hjb_le : jb x ≤ (1 + Sg) * (1 + ‖y‖ ^ 2) := by
    have hxy : x.1 ^ 2 + x.2 ^ 2 = a * ‖y‖ ^ 2 := by
      rw [hy_sq, mul_div_cancel₀ _ ha0.ne']
    unfold jb
    calc 1 + x.1 ^ 2 + x.2 ^ 2 = 1 + a * ‖y‖ ^ 2 := by linarith
      _ ≤ (1 + Sg) + (1 + Sg) * ‖y‖ ^ 2 := by nlinarith [sq_nonneg ‖y‖]
      _ = (1 + Sg) * (1 + ‖y‖ ^ 2) := by ring
  have hjb_rpow : jb x ^ k ≤ (1 + Sg) ^ k * (1 + ‖y‖ ^ 2) ^ k := by
    calc jb x ^ k
        ≤ ((1 + Sg) * (1 + ‖y‖ ^ 2)) ^ k :=
          Real.rpow_le_rpow (B0579.jb_pos x).le hjb_le hk
      _ = (1 + Sg) ^ k * (1 + ‖y‖ ^ 2) ^ k :=
          Real.mul_rpow (by positivity) (by positivity)
  have ha_pow : a ^ (-5 / 2 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos ha1 (by norm_num)
  have ha_pow_nn : 0 ≤ a ^ (-5 / 2 : ℝ) := Real.rpow_nonneg ha0.le _
  have hgrad : |(planarGradE σ x).1| + |(planarGradE σ x).2| =
      a ^ (-5 / 2 : ℝ) * |GaussianVortex.radialK ‖y‖| * (|y.re| + |y.im|) := by
    unfold planarGradE
    change |a ^ (-5 / 2 : ℝ) * (B0009.gradE0 y).1| +
      |a ^ (-5 / 2 : ℝ) * (B0009.gradE0 y).2| = _
    rw [B0009.gradE0_eq y]
    simp only [abs_mul, abs_of_nonneg ha_pow_nn]
    ring
  have hre_im : |y.re| + |y.im| ≤ 1 + ‖y‖ ^ 2 := by
    have hre : |y.re| ≤ ‖y‖ := Complex.abs_re_le_norm y
    have him : |y.im| ≤ ‖y‖ := Complex.abs_im_le_norm y
    nlinarith [sq_nonneg (‖y‖ - 1)]
  have hradK : |GaussianVortex.radialK ‖y‖| ≤ 2 * (1 + ‖y‖ ^ 2) * Real.exp (-(1 / 4 * ‖y‖ ^ 2)) := by
    unfold GaussianVortex.radialK GaussianVortex.radialOmega
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have h1 : |‖y‖ ^ 2 / 4 - 2| ≤ 2 * (1 + ‖y‖ ^ 2) := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg ‖y‖]
    have heq : -(‖y‖ ^ 2 / 4) = -(1 / 4 * ‖y‖ ^ 2) := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  have hgrad_le : |(planarGradE σ x).1| + |(planarGradE σ x).2| ≤
      4 * (1 + ‖y‖ ^ 2) ^ (2 : ℝ) * Real.exp (-(1 / 4 * ‖y‖ ^ 2)) := by
    rw [hgrad]
    have h1 : a ^ (-5 / 2 : ℝ) * |GaussianVortex.radialK ‖y‖| * (|y.re| + |y.im|) ≤
        1 * (2 * (1 + ‖y‖ ^ 2) * Real.exp (-(1 / 4 * ‖y‖ ^ 2))) * (1 + ‖y‖ ^ 2) := by
      refine mul_le_mul (mul_le_mul ha_pow hradK (abs_nonneg _) zero_le_one) hre_im
        (by positivity) (by positivity)
    have h2 : (1 + ‖y‖ ^ 2) ^ (2 : ℝ) = (1 + ‖y‖ ^ 2) * (1 + ‖y‖ ^ 2) := by
      rw [Real.rpow_two, sq]
    rw [h2]
    nlinarith [Real.exp_pos (-(1 / 4 * ‖y‖ ^ 2)), sq_nonneg ‖y‖]
  calc (|(planarGradE σ x).1| + |(planarGradE σ x).2|) * jb x ^ k
      ≤ (4 * (1 + ‖y‖ ^ 2) ^ (2 : ℝ) * Real.exp (-(1 / 4 * ‖y‖ ^ 2))) *
          ((1 + Sg) ^ k * (1 + ‖y‖ ^ 2) ^ k) :=
        mul_le_mul hgrad_le hjb_rpow (Real.rpow_nonneg (B0579.jb_pos x).le _) (by positivity)
    _ = 4 * (1 + Sg) ^ k * ((1 + ‖y‖ ^ 2) ^ k * (1 + ‖y‖ ^ 2) ^ (2 : ℝ) *
          Real.exp (-(1 / 4 * ‖y‖ ^ 2))) := by ring
    _ = 4 * (1 + Sg) ^ k * ((1 + ‖y‖ ^ 2) ^ (k + 2) * Real.exp (-(1 / 4 * ‖y‖ ^ 2))) := by
        rw [← Real.rpow_add (by positivity)]
    _ ≤ 4 * (1 + Sg) ^ k * C :=
        mul_le_mul_of_nonneg_left (hC_bd (‖y‖ ^ 2) (sq_nonneg _)) (by positivity)

/-! ## 2. Curl calculus and `TrainCloseM` bound on `∇(E_c - curl V_c^p)` -/

/-- The linear functional `T ↦ T(1,0)₁ - T(0,1)₀` realizing `Cyl.curl u = curlLam ∘ fderiv ℝ u`. -/
def curlLam : (Plane →L[ℝ] Cyl.Vec2) →L[ℝ] ℝ :=
  (EuclideanSpace.proj (1 : Fin 2) : Cyl.Vec2 →L[ℝ] ℝ).comp
      (ContinuousLinearMap.apply ℝ Cyl.Vec2 ((1 : ℝ), (0 : ℝ))) -
    (EuclideanSpace.proj (0 : Fin 2) : Cyl.Vec2 →L[ℝ] ℝ).comp
      (ContinuousLinearMap.apply ℝ Cyl.Vec2 ((0 : ℝ), (1 : ℝ)))

theorem curlLam_apply (T : Plane →L[ℝ] Cyl.Vec2) :
    curlLam T = T (1, 0) 1 - T (0, 1) 0 := rfl

theorem norm_curlLam_le : ‖curlLam‖ ≤ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun T => ?_)
  have h10 : ‖((1 : ℝ), (0 : ℝ))‖ ≤ 1 := by rw [Prod.norm_def]; simp
  have h01 : ‖((0 : ℝ), (1 : ℝ))‖ ≤ 1 := by rw [Prod.norm_def]; simp
  have ha : |T (1, 0) 1| ≤ ‖T‖ := by
    have h1 := PiLp.norm_apply_le (T (1, 0)) 1
    rw [Real.norm_eq_abs] at h1
    have h2 := T.le_opNorm ((1 : ℝ), (0 : ℝ))
    have h3 : ‖T‖ * ‖((1 : ℝ), (0 : ℝ))‖ ≤ ‖T‖ * 1 :=
      mul_le_mul_of_nonneg_left h10 (norm_nonneg _)
    linarith
  have hb : |T (0, 1) 0| ≤ ‖T‖ := by
    have h1 := PiLp.norm_apply_le (T (0, 1)) 0
    rw [Real.norm_eq_abs] at h1
    have h2 := T.le_opNorm ((0 : ℝ), (1 : ℝ))
    have h3 : ‖T‖ * ‖((0 : ℝ), (1 : ℝ))‖ ≤ ‖T‖ * 1 :=
      mul_le_mul_of_nonneg_left h01 (norm_nonneg _)
    linarith
  rw [curlLam_apply, Real.norm_eq_abs]
  linarith [abs_sub (T (1, 0) 1) (T (0, 1) 0)]

theorem curl_eq_curlLam_fderiv {u : Plane → Cyl.Vec2} (hu : ContDiff ℝ ∞ u) :
    Cyl.curl u = fun z => curlLam (fderiv ℝ u z) := by
  have hdiff : Differentiable ℝ u := hu.differentiable (by simp)
  funext z
  have h0 : HasDerivAt (fun q : ℝ => (q, z.2)) ((1 : ℝ), (0 : ℝ)) z.1 :=
    (hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2)
  have h0' : HasDerivAt (fun η : ℝ => (z.1, η)) ((0 : ℝ), (1 : ℝ)) z.2 :=
    (hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2)
  have h1 : HasDerivAt (fun q : ℝ => u (q, z.2)) (fderiv ℝ u (z.1, z.2) (1, 0)) z.1 :=
    (hdiff (z.1, z.2)).hasFDerivAt.comp_hasDerivAt z.1 h0
  have h1' : HasDerivAt (fun η : ℝ => u (z.1, η)) (fderiv ℝ u (z.1, z.2) (0, 1)) z.2 :=
    (hdiff (z.1, z.2)).hasFDerivAt.comp_hasDerivAt z.2 h0'
  have h2 : HasDerivAt (fun q : ℝ => u (q, z.2) 1)
      ((EuclideanSpace.proj (1 : Fin 2) : Cyl.Vec2 →L[ℝ] ℝ)
        (fderiv ℝ u (z.1, z.2) (1, 0))) z.1 :=
    (EuclideanSpace.proj (1 : Fin 2) : Cyl.Vec2 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt z.1 h1
  have h2' : HasDerivAt (fun η : ℝ => u (z.1, η) 0)
      ((EuclideanSpace.proj (0 : Fin 2) : Cyl.Vec2 →L[ℝ] ℝ)
        (fderiv ℝ u (z.1, z.2) (0, 1))) z.2 :=
    (EuclideanSpace.proj (0 : Fin 2) : Cyl.Vec2 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt z.2 h1'
  unfold Cyl.curl Cyl.partialQ Cyl.partialEta
  rw [h2.deriv, h2'.deriv, curlLam_apply]
  rfl

theorem contDiff_curl {u : Plane → Cyl.Vec2} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (Cyl.curl u) := by
  rw [curl_eq_curlLam_fderiv hu]
  exact curlLam.contDiff.comp (contDiff_infty_iff_fderiv.mp hu).2

theorem curl_add_smooth {u w : Plane → Cyl.Vec2} (hu : ContDiff ℝ ∞ u) (hw : ContDiff ℝ ∞ w) :
    Cyl.curl (fun x => u x + w x) = fun z => Cyl.curl u z + Cyl.curl w z := by
  rw [curl_eq_curlLam_fderiv (hu.add hw), curl_eq_curlLam_fderiv hu, curl_eq_curlLam_fderiv hw]
  funext z
  have hdu : DifferentiableAt ℝ u z := (hu.differentiable (by simp)) z
  have hdw : DifferentiableAt ℝ w z := (hw.differentiable (by simp)) z
  have heq : (fun x => u x + w x) = u + w := rfl
  rw [heq, fderiv_add hdu hdw, map_add]

theorem norm_fderiv_curl_le {u : Plane → Cyl.Vec2} (hu : ContDiff ℝ ∞ u) (x : Plane) :
    ‖fderiv ℝ (Cyl.curl u) x‖ ≤ 2 * ‖iteratedFDeriv ℝ 2 u x‖ := by
  have hg : ContDiff ℝ ∞ (fderiv ℝ u) := (contDiff_infty_iff_fderiv.mp hu).2
  have hcomp : (curlLam ∘ fderiv ℝ u) = Cyl.curl u := (curl_eq_curlLam_fderiv hu).symm
  have hiter : iteratedFDeriv ℝ 1 (Cyl.curl u) x =
      curlLam.compContinuousMultilinearMap (iteratedFDeriv ℝ 1 (fderiv ℝ u) x) := by
    rw [← hcomp]
    exact ContinuousLinearMap.iteratedFDeriv_comp_left curlLam
      hg.contDiffAt (by exact_mod_cast le_top)
  rw [← norm_iteratedFDeriv_one, hiter]
  have hnorm := ContinuousLinearMap.norm_compContinuousMultilinearMap_le curlLam
    (iteratedFDeriv ℝ 1 (fderiv ℝ u) x)
  rw [norm_iteratedFDeriv_fderiv] at hnorm
  exact hnorm.trans (mul_le_mul_of_nonneg_right norm_curlLam_le (norm_nonneg _))

theorem abs_pd_add_le_two_norm_fderiv (g : Plane → ℝ) (x : Plane) :
    |pd 0 g x| + |pd 1 g x| ≤ 2 * ‖fderiv ℝ g x‖ := by
  have hdir0 : ‖dir 0‖ ≤ 1 := by
    change ‖((1 : ℝ), (0 : ℝ))‖ ≤ 1
    rw [Prod.norm_def]; simp
  have hdir1 : ‖dir 1‖ ≤ 1 := by
    change ‖((0 : ℝ), (1 : ℝ))‖ ≤ 1
    rw [Prod.norm_def]; simp
  have h0 : |pd 0 g x| ≤ ‖fderiv ℝ g x‖ := by
    have h := (fderiv ℝ g x).le_opNorm (dir 0)
    rw [ ← pd, Real.norm_eq_abs] at h
    exact h.trans (mul_le_of_le_one_right (norm_nonneg _) hdir0)
  have h1 : |pd 1 g x| ≤ ‖fderiv ℝ g x‖ := by
    have h := (fderiv ℝ g x).le_opNorm (dir 1)
    rw [← pd, Real.norm_eq_abs] at h
    exact h.trans (mul_le_of_le_one_right (norm_nonneg _) hdir1)
  linarith

theorem continuous_trainGradE {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s) :
    Continuous (trainGradE tr s) := by
  have hsm : ContDiff ℝ ∞ (B0238.Ec tr s) := contDiff_curl (B0238.contDiff_Vc tr hs)
  have hf : Continuous (fderiv ℝ (B0238.Ec tr s)) :=
    (contDiff_infty_iff_fderiv.mp hsm).2.continuous
  unfold trainGradE pd
  exact (hf.clm_apply continuous_const).prodMk (hf.clm_apply continuous_const)

theorem pd_Ec_sub_curl_Vc {ν c : ℝ} (tr : B0140.TrainSol ν c) (hc : 0 < c)
    {s : ℝ} (hs : 0 ≤ s) (hν : 0 < ν) (j : Fin 2) (x : Plane) :
    pd j (B0238.Ec tr s) x - pd j (Cyl.curl (Train.Vc ν c s)) x =
      pd j (Cyl.curl (fun z => tr.v s z - Train.Vc ν c s z)) x := by
  have hsmV : ContDiff ℝ ∞ (tr.v s) := B0238.contDiff_Vc tr hs
  have hsmVc : ContDiff ℝ ∞ (Train.Vc ν c s) :=
    UnforcedLeray.Short.Spine.vcReg_contDiff_Vc hc
      (UnforcedLeray.Short.Spine.vcReg_width_pos hν hs)
  have hW : ContDiff ℝ ∞ (fun z => tr.v s z - Train.Vc ν c s z) := hsmV.sub hsmVc
  have hv : tr.v s = fun z => Train.Vc ν c s z + (tr.v s z - Train.Vc ν c s z) := by
    funext z; abel
  have hEc : B0238.Ec tr s =
      fun z => Cyl.curl (Train.Vc ν c s) z +
        Cyl.curl (fun w => tr.v s w - Train.Vc ν c s w) z := by
    show Cyl.curl (tr.v s) = _
    conv_lhs => rw [hv]
    exact curl_add_smooth hsmVc hW
  have hd1 : DifferentiableAt ℝ (Cyl.curl (Train.Vc ν c s)) x :=
    ((contDiff_curl hsmVc).differentiable (by simp)) x
  have hd2 : DifferentiableAt ℝ (Cyl.curl (fun w => tr.v s w - Train.Vc ν c s w)) x :=
    ((contDiff_curl hW).differentiable (by simp)) x
  rw [hEc]
  unfold pd
  have heq : (fun z => Cyl.curl (Train.Vc ν c s) z +
      Cyl.curl (fun w => tr.v s w - Train.Vc ν c s w) z) =
      Cyl.curl (Train.Vc ν c s) + Cyl.curl (fun w => tr.v s w - Train.Vc ν c s w) := rfl
  rw [heq, fderiv_add hd1 hd2, add_apply, add_sub_cancel_left]

theorem trainCloseM_curl_grad_bound {ν c m Sg δ : ℝ} (hν : 0 < ν) (hc : 0 < c)
    {tr : B0140.TrainSol ν c} (htr : TrainCloseM m tr Sg δ)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ Sg / ν) {x : Plane} (hx : x ∈ cell c) :
    (|pd 0 (Cyl.curl (fun z => tr.v s z - Train.Vc ν c s z)) x| +
      |pd 1 (Cyl.curl (fun z => tr.v s z - Train.Vc ν c s z)) x|) *
        jb x ^ (m / 2 + 1) ≤ 4 * δ := by
  set w : Plane → Cyl.Vec2 := fun z => tr.v s z - Train.Vc ν c s z
  have hsmW : ContDiff ℝ ∞ w :=
    (B0238.contDiff_Vc tr hs0).sub
      (UnforcedLeray.Short.Spine.vcReg_contDiff_Vc hc
        (UnforcedLeray.Short.Spine.vcReg_width_pos hν hs0))
  have h1 := abs_pd_add_le_two_norm_fderiv (Cyl.curl w) x
  have h2 := norm_fderiv_curl_le hsmW x
  have h3 : |pd 0 (Cyl.curl w) x| + |pd 1 (Cyl.curl w) x| ≤ 4 * ‖iteratedFDeriv ℝ 2 w x‖ := by
    linarith
  have hjb : 0 ≤ jb x ^ (m / 2 + 1) := Real.rpow_nonneg (B0579.jb_pos x).le _
  have hclose := htr s hs0 hs1 x hx 2 (by norm_num)
  calc (|pd 0 (Cyl.curl w) x| + |pd 1 (Cyl.curl w) x|) * jb x ^ (m / 2 + 1)
      ≤ (4 * ‖iteratedFDeriv ℝ 2 w x‖) * jb x ^ (m / 2 + 1) :=
        mul_le_mul_of_nonneg_right h3 hjb
    _ = 4 * (‖iteratedFDeriv ℝ 2 w x‖ * jb x ^ (m / 2 + 1)) := by ring
    _ ≤ 4 * δ := mul_le_mul_of_nonneg_left hclose (by norm_num)

/-! ## 3. Lattice representation of `∇(curl V_c^p)` and `n = 0` identification -/

/-- Explicit `q`-partial of `B0113.eExp a`. -/
def eExpX (a : ℝ) (z : Plane) : ℝ :=
  a⁻¹ ^ 3 * z.1 * (a⁻¹ * GaussianVortex.radiusSq z / 4 - 2) * B0113.gw a z

/-- Explicit `η`-partial of `B0113.eExp a`. -/
def eExpY (a : ℝ) (z : Plane) : ℝ :=
  a⁻¹ ^ 3 * z.2 * (a⁻¹ * GaussianVortex.radiusSq z / 4 - 2) * B0113.gw a z

theorem hx_eExp (a : ℝ) (z : Plane) :
    HasDerivAt (fun t => B0113.eExp a (t, z.2)) (eExpX a z) z.1 :=
  (B0113.hasDerivAt_mul_gw_x a z (((((B0113.hasDerivAt_sq' z.1).add_const (z.2 ^ 2)).const_mul
    a⁻¹).div_const 2).const_sub 2 |>.const_mul (a⁻¹ ^ 2))).congr_deriv
    (by unfold eExpX GaussianVortex.radiusSq; ring)

theorem hy_eExp (a : ℝ) (z : Plane) :
    HasDerivAt (fun t => B0113.eExp a (z.1, t)) (eExpY a z) z.2 :=
  (B0113.hasDerivAt_mul_gw_y a z (((((B0113.hasDerivAt_sq' z.2).const_add (z.1 ^ 2)).const_mul
    a⁻¹).div_const 2).const_sub 2 |>.const_mul (a⁻¹ ^ 2))).congr_deriv
    (by unfold eExpY GaussianVortex.radiusSq; ring)

theorem gf_eExp {A₂ : ℝ} : B0146.GF 1 A₂ B0113.eExp := by
  unfold B0113.eExp
  exact B0146.GF.mul_left
    ((B0146.PG.pow (B0146.PG.inv one_pos) 2).mul
      ((B0146.PG.const 2).sub (((B0146.PG.inv one_pos).mul B0146.PG.rsq).div_const 2)))
    (B0146.GF.gw one_pos)

theorem gf_eExpX {A₂ : ℝ} : B0146.GF 1 A₂ eExpX := by
  unfold eExpX
  exact B0146.GF.mul_left
    (((B0146.PG.pow (B0146.PG.inv one_pos) 3).mul B0146.PG.fst).mul
      ((((B0146.PG.inv one_pos).mul B0146.PG.rsq).div_const 4).sub (B0146.PG.const 2)))
    (B0146.GF.gw one_pos)

theorem gf_eExpY {A₂ : ℝ} : B0146.GF 1 A₂ eExpY := by
  unfold eExpY
  exact B0146.GF.mul_left
    (((B0146.PG.pow (B0146.PG.inv one_pos) 3).mul B0146.PG.snd).mul
      ((((B0146.PG.inv one_pos).mul B0146.PG.rsq).div_const 4).sub (B0146.PG.const 2)))
    (B0146.GF.gw one_pos)

theorem pd_zero_curl_Vc_eq_latticeSum {ν c σ Sg : ℝ} (hν : 0 < ν) (hc : 1 ≤ c)
    (hσ : σ ∈ Icc 0 Sg) (x : Plane) :
    pd 0 (Cyl.curl (Train.Vc ν c (σ / ν))) x =
      B0146.latticeSum c (eExpX (1 + σ)) x := by
  have hcpos : 0 < c := lt_of_lt_of_le one_pos hc
  have hs0 : 0 ≤ σ / ν := div_nonneg hσ.1 hν.le
  have hwidth : Train.width ν (σ / ν) = 1 + σ := by
    unfold Train.width
    rw [mul_div_cancel₀ _ hν.ne']
  have ha_mem : 1 + σ ∈ Icc 1 (1 + Sg) := ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  have hsmVc : ContDiff ℝ ∞ (Train.Vc ν c (σ / ν)) :=
    UnforcedLeray.Short.Spine.vcReg_contDiff_Vc hcpos
      (UnforcedLeray.Short.Spine.vcReg_width_pos hν hs0)
  have hdiff : DifferentiableAt ℝ (Cyl.curl (Train.Vc ν c (σ / ν))) x :=
    ((contDiff_curl hsmVc).differentiable (by simp)) x
  have hcurl : Cyl.curl (Train.Vc ν c (σ / ν)) = B0146.latticeSum c (B0113.eExp (1 + σ)) := by
    funext z
    rw [Train.Vc_curl hν hcpos.ne' hs0 z, hwidth]
    rfl
  change fderiv ℝ (Cyl.curl (Train.Vc ν c (σ / ν))) x (1, 0) = _
  rw [← B0238.partialQ_eq_fderiv hdiff, Cyl.partialQ_eq_partialX, hcurl,
    B0146.partialX_latticeSum hcpos.ne' (hx_eExp (1 + σ))
      (gf_eExp.xdecay ha_mem) (gf_eExpX.xdecay ha_mem)]

theorem pd_one_curl_Vc_eq_latticeSum {ν c σ Sg : ℝ} (hν : 0 < ν) (hc : 1 ≤ c)
    (hσ : σ ∈ Icc 0 Sg) (x : Plane) :
    pd 1 (Cyl.curl (Train.Vc ν c (σ / ν))) x =
      B0146.latticeSum c (eExpY (1 + σ)) x := by
  have hcpos : 0 < c := lt_of_lt_of_le one_pos hc
  have hs0 : 0 ≤ σ / ν := div_nonneg hσ.1 hν.le
  have hwidth : Train.width ν (σ / ν) = 1 + σ := by
    unfold Train.width
    rw [mul_div_cancel₀ _ hν.ne']
  have ha_mem : 1 + σ ∈ Icc 1 (1 + Sg) := ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  have hsmVc : ContDiff ℝ ∞ (Train.Vc ν c (σ / ν)) :=
    UnforcedLeray.Short.Spine.vcReg_contDiff_Vc hcpos
      (UnforcedLeray.Short.Spine.vcReg_width_pos hν hs0)
  have hdiff : DifferentiableAt ℝ (Cyl.curl (Train.Vc ν c (σ / ν))) x :=
    ((contDiff_curl hsmVc).differentiable (by simp)) x
  have hcurl : Cyl.curl (Train.Vc ν c (σ / ν)) = B0146.latticeSum c (B0113.eExp (1 + σ)) := by
    funext z
    rw [Train.Vc_curl hν hcpos.ne' hs0 z, hwidth]
    rfl
  change fderiv ℝ (Cyl.curl (Train.Vc ν c (σ / ν))) x (0, 1) = _
  rw [← B0238.partialEta_eq_fderiv hdiff, Cyl.partialEta_eq_partialY, hcurl,
    B0146.partialY_latticeSum hcpos.ne' (hy_eExp (1 + σ))
      (gf_eExp.xdecay ha_mem) (gf_eExpY.xdecay ha_mem)]

private theorem rpow_neg_five_half_div_sqrt {a : ℝ} (ha : 0 < a) :
    a ^ (-5 / 2 : ℝ) / Real.sqrt a = a⁻¹ ^ 3 := by
  rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg ha.le, ← Real.rpow_add ha]
  have hexp : (-5 / 2 : ℝ) + -(1 / 2) = -((3 : ℕ) : ℝ) := by norm_num
  rw [hexp, Real.rpow_neg ha.le, Real.rpow_natCast, inv_pow]

theorem eExpX_shift_zero_eq_planarGradE_fst {c σ : ℝ} (hσ : 0 ≤ σ) (x : Plane) :
    eExpX (1 + σ) (B0146.shift c 0 x) = (planarGradE σ x).1 := by
  have hsh : B0146.shift c 0 x = x := by
    ext <;> simp [B0146.shift]
  rw [hsh]
  set a : ℝ := 1 + σ
  have ha0 : 0 < a := by dsimp [a]; linarith
  set y : ℂ := ofPlane (scalePlane a x)
  have hy_sq : ‖y‖ ^ 2 = a⁻¹ * GaussianVortex.radiusSq x := by
    rw [norm_ofPlane_sq, scalePlane, div_pow, div_pow, ← add_div, Real.sq_sqrt ha0.le,
      GaussianVortex.radiusSq, div_eq_inv_mul]
  have hy_re : y.re = x.1 / Real.sqrt a := rfl
  unfold planarGradE
  change eExpX a x = a ^ (-5 / 2 : ℝ) * (B0009.gradE0 y).1
  rw [B0009.gradE0_eq y]
  dsimp only
  unfold eExpX GaussianVortex.radialK GaussianVortex.radialOmega B0113.gw
  rw [hy_sq, hy_re]
  have hpow := rpow_neg_five_half_div_sqrt ha0
  calc a⁻¹ ^ 3 * x.1 * (a⁻¹ * GaussianVortex.radiusSq x / 4 - 2) *
          Real.exp (-(a⁻¹ * GaussianVortex.radiusSq x / 4))
      = (a ^ (-5 / 2 : ℝ) / Real.sqrt a) * x.1 * (a⁻¹ * GaussianVortex.radiusSq x / 4 - 2) *
          Real.exp (-(a⁻¹ * GaussianVortex.radiusSq x / 4)) := by rw [hpow]
    _ = a ^ (-5 / 2 : ℝ) *
          ((a⁻¹ * GaussianVortex.radiusSq x / 4 - 2) *
            Real.exp (-(a⁻¹ * GaussianVortex.radiusSq x / 4)) * (x.1 / Real.sqrt a)) := by
          ring

theorem eExpY_shift_zero_eq_planarGradE_snd {c σ : ℝ} (hσ : 0 ≤ σ) (x : Plane) :
    eExpY (1 + σ) (B0146.shift c 0 x) = (planarGradE σ x).2 := by
  have hsh : B0146.shift c 0 x = x := by
    ext <;> simp [B0146.shift]
  rw [hsh]
  set a : ℝ := 1 + σ
  have ha0 : 0 < a := by dsimp [a]; linarith
  set y : ℂ := ofPlane (scalePlane a x)
  have hy_sq : ‖y‖ ^ 2 = a⁻¹ * GaussianVortex.radiusSq x := by
    rw [norm_ofPlane_sq, scalePlane, div_pow, div_pow, ← add_div, Real.sq_sqrt ha0.le,
      GaussianVortex.radiusSq, div_eq_inv_mul]
  have hy_im : y.im = x.2 / Real.sqrt a := rfl
  unfold planarGradE
  change eExpY a x = a ^ (-5 / 2 : ℝ) * (B0009.gradE0 y).2
  rw [B0009.gradE0_eq y]
  dsimp only
  unfold eExpY GaussianVortex.radialK GaussianVortex.radialOmega B0113.gw
  rw [hy_sq, hy_im]
  have hpow := rpow_neg_five_half_div_sqrt ha0
  calc a⁻¹ ^ 3 * x.2 * (a⁻¹ * GaussianVortex.radiusSq x / 4 - 2) *
          Real.exp (-(a⁻¹ * GaussianVortex.radiusSq x / 4))
      = (a ^ (-5 / 2 : ℝ) / Real.sqrt a) * x.2 * (a⁻¹ * GaussianVortex.radiusSq x / 4 - 2) *
          Real.exp (-(a⁻¹ * GaussianVortex.radiusSq x / 4)) := by rw [hpow]
    _ = a ^ (-5 / 2 : ℝ) *
          ((a⁻¹ * GaussianVortex.radiusSq x / 4 - 2) *
            Real.exp (-(a⁻¹ * GaussianVortex.radiusSq x / 4)) * (x.2 / Real.sqrt a)) := by
          ring

/-! ## 4. Weighted `c^{-2}` tail bound on `B0579.cell c` for `n ≠ 0` lattice terms -/

/-- On the centered cell `x.1 ∈ [-c/2, c/2)` with `c ≥ 1`, `x.1² ≤ (x.1 - n c)²` for all `n : ℤ`. -/
private theorem cell_fst_sq_le_shift_sq {c : ℝ} (hc : 1 ≤ c) {x1 : ℝ}
    (h1 : -(c / 2) ≤ x1) (h2 : x1 < c / 2) (n : ℤ) :
    x1 ^ 2 ≤ (x1 - n * c) ^ 2 := by
  obtain h | h | h : n = 0 ∨ 1 ≤ n ∨ n ≤ -1 := by omega
  · subst h; simp
  · have hn : (1 : ℝ) ≤ n := by exact_mod_cast h
    have hA : (0 : ℝ) ≤ (n : ℝ) * c - 2 * x1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hn) (by linarith : (0 : ℝ) ≤ c)]
    have hB : (0 : ℝ) ≤ (n : ℝ) * c := by nlinarith
    nlinarith [mul_nonneg hB hA]
  · have hn : (n : ℝ) ≤ -1 := by exact_mod_cast h
    have hB : (n : ℝ) * c ≤ 0 := by nlinarith
    have hA : (n : ℝ) * c - 2 * x1 ≤ 0 := by nlinarith
    nlinarith [mul_nonneg (neg_nonneg.mpr hB) (neg_nonneg.mpr hA)]

private theorem exp_neg_mul_sq_le_rpow_neg_two {γ c : ℝ} (hγ : 0 < γ) (hc : 1 ≤ c) :
    Real.exp (-(γ * c ^ 2)) ≤ (1 / γ) * c ^ (-2 : ℝ) := by
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc
  have hγc : 0 < γ * c ^ 2 := by positivity
  have h1 : γ * c ^ 2 ≤ Real.exp (γ * c ^ 2) := by
    linarith [Real.add_one_le_exp (γ * c ^ 2)]
  have h2 : (Real.exp (γ * c ^ 2))⁻¹ ≤ (γ * c ^ 2)⁻¹ := inv_anti₀ hγc h1
  rw [Real.exp_neg]
  refine h2.trans (le_of_eq ?_)
  rw [mul_inv, one_div, Real.rpow_neg hc0.le, Real.rpow_two]

theorem gf_cell_tail_weighted_bound {Sg k : ℝ} (hk : 0 ≤ k) {F : ℝ → Plane → ℝ}
    (hF : B0146.GF 1 (1 + Sg) F) :
    ∃ C_tail : ℝ, 0 < C_tail ∧ ∀ c : ℝ, 1 ≤ c → ∀ a ∈ Icc 1 (1 + Sg), ∀ x ∈ cell c,
      |B0146.latticeSum c (F a) x - F a (B0146.shift c 0 x)| * jb x ^ k ≤
        C_tail * c ^ (-2 : ℝ) := by
  obtain ⟨K, β, hK, hβ, hbd⟩ := hF
  have hβ2 : 0 < β / 2 := half_pos hβ
  have hβ8 : 0 < β / 8 := by linarith
  obtain ⟨C_wt, hC_wt, hwt_bd⟩ := rpow_mul_exp_neg_le k hk hβ2
  set L : ℝ := ∑' m : ℤ, Real.exp (-((β / 8) * (m : ℝ) ^ 2))
  have hL_nn : 0 ≤ L := tsum_nonneg fun _ => (Real.exp_pos _).le
  set C_tail : ℝ := (K + 1) * C_wt * Real.exp (β / 8) * (L + 1) * (1 / (β / 8))
  have hC_tail_pos : 0 < C_tail := by dsimp [C_tail]; positivity
  refine ⟨C_tail, hC_tail_pos, fun c hc a ha x hx => ?_⟩
  have hc0 : c ≠ 0 := (lt_of_lt_of_le one_pos hc).ne'
  have hx1_mem : x.1 ∈ Ico (-(c / 2)) (c / 2) := hx.1
  have hx1_abs : |x.1| ≤ c / 2 := abs_le.mpr ⟨hx1_mem.1, hx1_mem.2.le⟩
  set C₀ : ℝ := K * Real.exp (-((β / 2) * (x.1 ^ 2 + x.2 ^ 2)))
  have hC₀_nn : 0 ≤ C₀ := by dsimp [C₀]; positivity
  have hterm : ∀ n : ℤ,
      |F a (B0146.shift c n x)| ≤ C₀ * Real.exp (-((β / 2) * (x.1 - n * c) ^ 2)) := by
    intro n
    have h1 := hbd a ha (B0146.shift c n x)
    have hsq := cell_fst_sq_le_shift_sq hc hx1_mem.1 hx1_mem.2 n
    have hrad : β * GaussianVortex.radiusSq (B0146.shift c n x) ≥
        (β / 2) * (x.1 ^ 2 + x.2 ^ 2) + (β / 2) * (x.1 - n * c) ^ 2 := by
      unfold GaussianVortex.radiusSq B0146.shift
      nlinarith
    have hexp : Real.exp (-(β * GaussianVortex.radiusSq (B0146.shift c n x))) ≤
        Real.exp (-((β / 2) * (x.1 ^ 2 + x.2 ^ 2))) *
          Real.exp (-((β / 2) * (x.1 - n * c) ^ 2)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith
    calc |F a (B0146.shift c n x)|
        ≤ K * Real.exp (-(β * GaussianVortex.radiusSq (B0146.shift c n x))) := h1
      _ ≤ K * (Real.exp (-((β / 2) * (x.1 ^ 2 + x.2 ^ 2))) *
            Real.exp (-((β / 2) * (x.1 - n * c) ^ 2))) :=
          mul_le_mul_of_nonneg_left hexp hK
      _ = C₀ * Real.exp (-((β / 2) * (x.1 - n * c) ^ 2)) := by dsimp [C₀]; ring
  have hsum : Summable (fun n : ℤ => F a (B0146.shift c n x)) :=
    TrainGap.summable_of_gauss_bound hβ2 hc0 hterm
  have hH_sum : Summable (fun m : ℤ =>
      (C₀ * (Real.exp (β / 8) * Real.exp (-((β / 8) * c ^ 2)))) *
        Real.exp (-((β / 8) * (m : ℝ) ^ 2))) :=
    (TrainGap.summable_gauss_int hβ8).mul_left _
  have hb_tail : ∀ n : ℤ, n ≠ 0 → |F a (B0146.shift c n x)| ≤
      (C₀ * (Real.exp (β / 8) * Real.exp (-((β / 8) * c ^ 2)))) *
        Real.exp (-((β / 8) * (n : ℝ) ^ 2)) := by
    intro n hn
    have h1 := hterm n
    have h2 := TrainGap.tail_exp_le hβ2 hc hx1_abs hn
    have heq8 : β / 2 / 4 = β / 8 := by ring
    rw [heq8] at h2
    calc |F a (B0146.shift c n x)|
        ≤ C₀ * Real.exp (-((β / 2) * (x.1 - n * c) ^ 2)) := h1
      _ ≤ C₀ * (Real.exp (β / 8) * Real.exp (-((β / 8) * c ^ 2)) *
            Real.exp (-((β / 8) * (n : ℝ) ^ 2))) :=
          mul_le_mul_of_nonneg_left h2 hC₀_nn
      _ = (C₀ * (Real.exp (β / 8) * Real.exp (-((β / 8) * c ^ 2)))) *
            Real.exp (-((β / 8) * (n : ℝ) ^ 2)) := by ring
  have hH0 : ∀ n : ℤ, 0 ≤
      (C₀ * (Real.exp (β / 8) * Real.exp (-((β / 8) * c ^ 2)))) *
        Real.exp (-((β / 8) * (n : ℝ) ^ 2)) := fun n => by positivity
  have htsum := (TrainGap.tsum_ite_zero_bound hsum hH_sum hH0 hb_tail).trans
    (le_of_eq (tsum_mul_left (a := C₀ * (Real.exp (β / 8) * Real.exp (-((β / 8) * c ^ 2))))))
  have hjb_eq : jb x = 1 + (x.1 ^ 2 + x.2 ^ 2) := by unfold jb; ring
  have hC₀_jb : C₀ * jb x ^ k ≤ (K + 1) * C_wt := by
    dsimp [C₀]
    rw [hjb_eq, mul_assoc]
    have h1 : Real.exp (-((β / 2) * (x.1 ^ 2 + x.2 ^ 2))) *
        (1 + (x.1 ^ 2 + x.2 ^ 2)) ^ k ≤ C_wt := by
      rw [mul_comm]
      exact hwt_bd (x.1 ^ 2 + x.2 ^ 2) (by positivity)
    exact mul_le_mul (by linarith) h1 (by positivity) (by positivity)
  have hexp_c : Real.exp (-((β / 8) * c ^ 2)) ≤ (1 / (β / 8)) * c ^ (-2 : ℝ) :=
    exp_neg_mul_sq_le_rpow_neg_two hβ8 hc
  have hjb_nn : 0 ≤ jb x ^ k := Real.rpow_nonneg (B0579.jb_pos x).le k
  rw [B0146.latticeSum]
  calc |∑' n : ℤ, F a (B0146.shift c n x) - F a (B0146.shift c 0 x)| * jb x ^ k
      ≤ ((C₀ * (Real.exp (β / 8) * Real.exp (-((β / 8) * c ^ 2)))) * L) * jb x ^ k :=
        mul_le_mul_of_nonneg_right htsum hjb_nn
    _ = (C₀ * jb x ^ k) * Real.exp (β / 8) * L * Real.exp (-((β / 8) * c ^ 2)) := by ring
    _ ≤ ((K + 1) * C_wt) * Real.exp (β / 8) * (L + 1) * ((1 / (β / 8)) * c ^ (-2 : ℝ)) := by
        refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right hC₀_jb (Real.exp_pos _).le)
          (by linarith) hL_nn (by positivity)) hexp_c (Real.exp_pos _).le (by positivity)
    _ = C_tail * c ^ (-2 : ℝ) := by dsimp [C_tail]; ring

/-! ## 5. Main theorem: `trainGradCoeffStep_proof` -/

theorem trainGradCoeffStep_proof : TrainGradCoeffStep := by
  intro m hm Sg hSg
  have hk_nn : 0 ≤ m / 2 + 1 := by linarith
  obtain ⟨M₀, hM₀, hpl_bd⟩ := planarGradE_sup_bound (m / 2 + 1) hk_nn Sg hSg
  obtain ⟨C_X, hC_X, htail_X⟩ := gf_cell_tail_weighted_bound (Sg := Sg) hk_nn gf_eExpX
  obtain ⟨C_Y, hC_Y, htail_Y⟩ := gf_cell_tail_weighted_bound (Sg := Sg) hk_nn gf_eExpY
  set C_tr : ℝ := M₀ + C_X + C_Y + 4
  have hC_tr_pos : 0 < C_tr := by dsimp [C_tr]; positivity
  refine ⟨C_tr, hC_tr_pos, fun p d dm dp _hbg hc δ hδ htr σ hσ => ⟨?_, ?_⟩⟩
  · -- Part 1: `IsCylWeightedCoeff p.c m C_tr (planarGradE σ)`
    refine ⟨continuous_planarGradE σ, fun x _hx => ?_⟩
    exact (hpl_bd σ hσ x).trans (by dsimp [C_tr]; linarith)
  · -- Part 2: `IsCylWeightedCoeff p.c m (C_tr * (p.c ^ (-2 : ℝ) + δ)) (trainGradE - planarGradE)`
    have hν : 0 < p.ν := p.ν_pos
    have hc_pos : 0 < p.c := p.c_pos
    have hs0 : 0 ≤ σ / p.ν := div_nonneg hσ.1 hν.le
    have hs1 : σ / p.ν ≤ Sg / p.ν := div_le_div_of_nonneg_right hσ.2 hν.le
    have ha_mem : 1 + σ ∈ Icc 1 (1 + Sg) := ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
    refine ⟨(continuous_trainGradE p.train hs0).sub (continuous_planarGradE σ), fun x hx => ?_⟩
    set w : Plane → Cyl.Vec2 := fun z => p.train.v (σ / p.ν) z - Train.Vc p.ν p.c (σ / p.ν) z
    have hsplit0 : (trainGradE p.train (σ / p.ν) x - planarGradE σ x).1 =
        (B0146.latticeSum p.c (eExpX (1 + σ)) x - eExpX (1 + σ) (B0146.shift p.c 0 x)) +
          pd 0 (Cyl.curl w) x := by
      simp only [trainGradE, Prod.fst_sub]
      rw [← eExpX_shift_zero_eq_planarGradE_fst hσ.1 x,
        ← pd_zero_curl_Vc_eq_latticeSum hν hc hσ x,
        ← pd_Ec_sub_curl_Vc p.train hc_pos hs0 hν 0 x]
      ring
    have hsplit1 : (trainGradE p.train (σ / p.ν) x - planarGradE σ x).2 =
        (B0146.latticeSum p.c (eExpY (1 + σ)) x - eExpY (1 + σ) (B0146.shift p.c 0 x)) +
          pd 1 (Cyl.curl w) x := by
      simp only [trainGradE, Prod.snd_sub]
      rw [← eExpY_shift_zero_eq_planarGradE_snd hσ.1 x,
        ← pd_one_curl_Vc_eq_latticeSum hν hc hσ x,
        ← pd_Ec_sub_curl_Vc p.train hc_pos hs0 hν 1 x]
      ring
    have habs :
        |(trainGradE p.train (σ / p.ν) x - planarGradE σ x).1| +
          |(trainGradE p.train (σ / p.ν) x - planarGradE σ x).2| ≤
        |B0146.latticeSum p.c (eExpX (1 + σ)) x - eExpX (1 + σ) (B0146.shift p.c 0 x)| +
          |B0146.latticeSum p.c (eExpY (1 + σ)) x - eExpY (1 + σ) (B0146.shift p.c 0 x)| +
          (|pd 0 (Cyl.curl w) x| + |pd 1 (Cyl.curl w) x|) := by
      rw [hsplit0, hsplit1]
      linarith [abs_add_le
          (B0146.latticeSum p.c (eExpX (1 + σ)) x - eExpX (1 + σ) (B0146.shift p.c 0 x))
          (pd 0 (Cyl.curl w) x),
        abs_add_le
          (B0146.latticeSum p.c (eExpY (1 + σ)) x - eExpY (1 + σ) (B0146.shift p.c 0 x))
          (pd 1 (Cyl.curl w) x)]
    have hjb_nn : 0 ≤ jb x ^ (m / 2 + 1) := Real.rpow_nonneg (B0579.jb_pos x).le _
    have hX := htail_X p.c hc (1 + σ) ha_mem x hx
    have hY := htail_Y p.c hc (1 + σ) ha_mem x hx
    have hW := trainCloseM_curl_grad_bound hν hc_pos htr hs0 hs1 hx
    have hc_inv_nn : 0 ≤ p.c ^ (-2 : ℝ) := Real.rpow_nonneg hc_pos.le _
    calc (|(trainGradE p.train (σ / p.ν) x - planarGradE σ x).1| +
            |(trainGradE p.train (σ / p.ν) x - planarGradE σ x).2|) * jb x ^ (m / 2 + 1)
        ≤ (|B0146.latticeSum p.c (eExpX (1 + σ)) x - eExpX (1 + σ) (B0146.shift p.c 0 x)| +
            |B0146.latticeSum p.c (eExpY (1 + σ)) x - eExpY (1 + σ) (B0146.shift p.c 0 x)| +
            (|pd 0 (Cyl.curl w) x| + |pd 1 (Cyl.curl w) x|)) * jb x ^ (m / 2 + 1) :=
          mul_le_mul_of_nonneg_right habs hjb_nn
      _ = |B0146.latticeSum p.c (eExpX (1 + σ)) x - eExpX (1 + σ) (B0146.shift p.c 0 x)| *
            jb x ^ (m / 2 + 1) +
          |B0146.latticeSum p.c (eExpY (1 + σ)) x - eExpY (1 + σ) (B0146.shift p.c 0 x)| *
            jb x ^ (m / 2 + 1) +
          (|pd 0 (Cyl.curl w) x| + |pd 1 (Cyl.curl w) x|) * jb x ^ (m / 2 + 1) := by ring
      _ ≤ C_X * p.c ^ (-2 : ℝ) + C_Y * p.c ^ (-2 : ℝ) + 4 * δ := by linarith
      _ ≤ C_tr * (p.c ^ (-2 : ℝ) + δ) := by
          dsimp [C_tr]
          nlinarith

end UnforcedLeray.Short.IIb

namespace Short.PartIIb

abbrev TrainGradCoeffStep : Prop :=
  UnforcedLeray.Short.IIb.TrainGradCoeffStep

theorem trainGradCoeffStep_proof : TrainGradCoeffStep :=
  UnforcedLeray.Short.IIb.trainGradCoeffStep_proof

end Short.PartIIb
