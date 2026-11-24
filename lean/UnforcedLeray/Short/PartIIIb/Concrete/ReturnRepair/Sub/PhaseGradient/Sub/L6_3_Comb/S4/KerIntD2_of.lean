import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_3

/-!
# `kerIntD2_of` (`PartIII-b:C/rep/2/6/3/4/1`)

Differentiation of `kerInt` under the integral, second order (source 3603-3626, 3800-3807,
4171-4200, 5223).  Helper layer: the kernels `phiL` (`∂_e Kd`, the kernel of `KerIntD2`) and
`phiPsi` (`∂_v ∂_e Kd`), the family `famE p w = ∂_e (kerF Kd p) w`, its `iteratedFDeriv` bounds
through `ContinuousLinearMap.apply e`, and the glue through `ParamHasFDeriv1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The kernel `(h,w,z) ↦ ∂_e Kd(h,·,z)(w)` of the first `y`-derivative in `KerIntD2`. -/
def phiL (ν μ : ℝ) (e : Space) : ℝ → Space → Space → Fin 3 → Fin 3 → Fin 3 → ℂ :=
  fun h w z i j k => fderiv ℝ (fun y'' => Kd ν μ h y'' z i j k) w e

/-- The kernel `(h,w,z) ↦ ∂_v ∂_e Kd(h,·,z)(w)` of the second `y`-derivative in `KerIntD2`. -/
def phiPsi (ν μ : ℝ) (e v : Space) : ℝ → Space → Space → Fin 3 → Fin 3 → Fin 3 → ℂ :=
  fun h w z i j k => fderiv ℝ (fun y' => fderiv ℝ (fun y'' => Kd ν μ h y'' z i j k) y' e) w v

/-- The `y`-family `p ↦ (w ↦ ∂_e (kerF Kd p) w)`. -/
def famE (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (i : Fin 3) (ν μ : ℝ) (e : Space)
    (p : ℝ × Space) (w : Space) : ℂ :=
  fderiv ℝ (kerF T τ i (Kd ν μ) p) w e

/-- The dominating family `n ↦ ‖e‖_{op} · C · gMaj(n+1)`. -/
def ggDom (μ : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (C : ℝ) (e : Space)
    (n : ℕ) (p : ℝ × Space) : ℝ :=
  ‖ContinuousLinearMap.apply ℝ ℂ e‖ * (C * gMaj μ T τ (n + 1) p)

/-- The `ℝ × Space` measure `mHZ` is a.e. supported on `0 < h`. -/
lemma ae_mHZ_pos : ∀ᵐ p ∂mHZ, 0 < p.1 := by
  unfold mHZ
  rw [MeasureTheory.Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const measurable_fst)]
  exact (ae_restrict_mem measurableSet_Ioi).mono fun x hx =>
    Filter.Eventually.of_forall fun y => mem_Ioi.mp hx

/-- Components of `Kd` are `C²` for `h > 0`, extracted from `KdGapSmooth` with the indicator
test data `T'`. -/
lemma kd_contDiff_of (hSm : KdGapSmooth) (ν μ : ℝ) (hν : 0 < ν) (τ : ℝ) (i : Fin 3)
    (h : ℝ) (hh : 0 < h) (z : Space) (j k : Fin 3) :
    ContDiff ℝ 2 (fun w => Kd ν μ h w z i j k) := by
  let T' : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ := fun s w' =>
    Matrix.of fun a b => if (s = τ - h ∧ w' = z) ∧ (a = j ∧ b = k) then 1 else 0
  have hK := hSm ν μ hν T' τ i (h, z) hh
  have heq : kerF T' τ i (Kd ν μ) (h, z) = fun w => Kd ν μ h w z i j k := by
    funext w
    simp [kerF, T', Matrix.of_apply, apply_ite Complex.ofReal, mul_ite, ite_and]
  rw [← heq]
  exact hK

lemma contDiff_fam {K : Space → ℂ} (hK : ContDiff ℝ 2 K) (e : Space) :
    ContDiff ℝ 1 (fun w => fderiv ℝ K w e) := by
  have h1 : ContDiff ℝ 1 (fun w => fderiv ℝ K w) := hK.fderiv_right (m := 1) (by norm_num)
  exact h1.clm_apply contDiff_const

lemma diff_fderiv_e' {K : Space → ℂ} (hK : ContDiff ℝ 2 K) (e : Space) :
    Differentiable ℝ (fun w => fderiv ℝ K w e) :=
  (contDiff_fam hK e).differentiable (by norm_num)

lemma norm_fam_le {K : Space → ℂ} (hK : ContDiff ℝ 2 K) (e : Space) (n : ℕ) (hn : n ≤ 1)
    (y : Space) :
    ‖iteratedFDeriv ℝ n (fun w => fderiv ℝ K w e) y‖ ≤
      ‖ContinuousLinearMap.apply ℝ ℂ e‖ * ‖iteratedFDeriv ℝ (n + 1) K y‖ := by
  have h1 : ContDiff ℝ 1 (fun w => fderiv ℝ K w) := hK.fderiv_right (m := 1) (by norm_num)
  have h2 := ContinuousLinearMap.norm_iteratedFDeriv_comp_left (ContinuousLinearMap.apply ℝ ℂ e)
    (h1.contDiffAt : ContDiffAt ℝ 1 (fun w => fderiv ℝ K w) y) (by exact_mod_cast hn)
  rw [← norm_iteratedFDeriv_fderiv]
  exact h2

lemma aesm_fderiv_iter {α : Type*} [MeasurableSpace α] {m : Measure α} (f : α → Space → ℂ)
    (n : ℕ) (y : Space) (hf : AEStronglyMeasurable (fun a => iteratedFDeriv ℝ (n + 1) (f a) y) m) :
    AEStronglyMeasurable (fun a => iteratedFDeriv ℝ n (fun w => fderiv ℝ (f a) w) y) m := by
  refine ((continuousMultilinearCurryRightEquiv' ℝ n Space ℂ).continuous.comp_aestronglyMeasurable
    hf).congr (Filter.Eventually.of_forall fun a => ?_)
  dsimp only
  rw [iteratedFDeriv_succ_eq_comp_right]
  simp

lemma aesm_fam {α : Type*} [MeasurableSpace α] {m : Measure α} (K : α → Space → ℂ) (e : Space)
    (n : ℕ) (hn : n ≤ 1) (y : Space)
    (hK : ∀ᵐ a ∂m, ContDiff ℝ 2 (K a))
    (hm : AEStronglyMeasurable (fun a => iteratedFDeriv ℝ (n + 1) (K a) y) m) :
    AEStronglyMeasurable (fun a => iteratedFDeriv ℝ n (fun w => fderiv ℝ (K a) w e) y) m := by
  have h1 := (ContinuousLinearMap.continuous_postcomp_continuousMultilinearMap
    (ContinuousLinearMap.apply ℝ ℂ e)).comp_aestronglyMeasurable (aesm_fderiv_iter K n y hm)
  refine h1.congr ?_
  filter_upwards [hK] with a ha
  have hd : ContDiff ℝ 1 (fun w => fderiv ℝ (K a) w) := ha.fderiv_right (m := 1) (by norm_num)
  have h2 := ContinuousLinearMap.iteratedFDeriv_comp_left (ContinuousLinearMap.apply ℝ ℂ e)
    (hd.contDiffAt : ContDiffAt ℝ 1 (fun w => fderiv ℝ (K a) w) y) (i := n) (by exact_mod_cast hn)
  exact h2.symm

lemma fderiv_eq_curry_iter (f : Space → ℂ) (y : Space) :
    continuousMultilinearCurryFin1 ℝ Space ℂ (iteratedFDeriv ℝ 1 f y) = fderiv ℝ f y := by
  ext v
  simp [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]

lemma aesm_fderiv_clm {α : Type*} [MeasurableSpace α] {m : Measure α} (K : α → Space → ℂ)
    (y : Space) (hm : AEStronglyMeasurable (fun a => iteratedFDeriv ℝ 1 (K a) y) m) :
    AEStronglyMeasurable (fun a => fderiv ℝ (K a) y) m := by
  refine ((continuousMultilinearCurryFin1 ℝ Space ℂ).continuous.comp_aestronglyMeasurable hm).congr
    (Filter.Eventually.of_forall fun a => ?_)
  exact fderiv_eq_curry_iter (K a) y

/-- Auxiliary form of `kerIntD2_of` with the direction `e` arbitrary. -/
theorem kerIntD2_aux (hP : ParamHasFDeriv1) (hPt : KdGapPt) (hInt : KdGapInt)
    (hMeas : KdGapMeas) (hSm : KdGapSmooth) (hProd : KerIntProd) (hF : KerFFderiv)
    (ν μ rOut P : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (hd : SepData ν μ rOut P T)
    (τ : ℝ) (y : Space) (hy : rOut < ϱ y) (e : Space) (i : Fin 3) :
    DifferentiableAt ℝ (fun y' => kerInt T (phiL ν μ e) τ y' i) y ∧
      ∀ v : Space, fderiv ℝ (fun y' => kerInt T (phiL ν μ e) τ y' i) y v =
        kerInt T (phiPsi ν μ e v) τ y i := by
  have hν : 0 < ν := hd.1
  obtain ⟨ε, hε, -, C, hC0, hbd⟩ := hPt ν μ rOut P T hd τ y hy i
  have hball : IsOpen (Metric.ball y ε) := Metric.isOpen_ball
  have hyU : y ∈ Metric.ball y ε := Metric.mem_ball_self hε
  have hpos := ae_mHZ_pos
  have hG2 : ∀ p : ℝ × Space, 0 < p.1 → ContDiff ℝ 2 (kerF T τ i (Kd ν μ) p) :=
    fun p hp => hSm ν μ hν T τ i p hp
  have hcomp : ∀ (h : ℝ), 0 < h → ∀ (z : Space) (j k : Fin 3),
      ContDiff ℝ 2 (fun w => Kd ν μ h w z i j k) :=
    fun h hh z j k => kd_contDiff_of hSm ν μ hν τ i h hh z j k
  -- identification of the family with the kernel integrand
  have hFeq : ∀ p : ℝ × Space, 0 < p.1 → ∀ w : Space,
      famE T τ i ν μ e p w = kerF T τ i (phiL ν μ e) p w := by
    intro p hp w
    have hdiff : ∀ j k : Fin 3, DifferentiableAt ℝ (fun w' => Kd ν μ p.1 w' p.2 i j k) w :=
      fun j k => ((hcomp p.1 hp p.2 j k).differentiable (by norm_num)) w
    exact hF T τ i (Kd ν μ) p w e hdiff
  have hdiffL : ∀ (p : ℝ × Space), 0 < p.1 → ∀ (w : Space) (j k : Fin 3),
      DifferentiableAt ℝ (fun w'' => phiL ν μ e p.1 w'' p.2 i j k) w := by
    intro p hp w j k
    exact (diff_fderiv_e' (hcomp p.1 hp p.2 j k) e) w
  -- derivative identity for the family
  have hΨ : ∀ p : ℝ × Space, 0 < p.1 → ∀ v : Space,
      fderiv ℝ (famE T τ i ν μ e p) y v = kerF T τ i (phiPsi ν μ e v) p y := by
    intro p hp v
    have hfun : famE T τ i ν μ e p = kerF T τ i (phiL ν μ e) p :=
      funext fun w => hFeq p hp w
    rw [hfun]
    exact hF T τ i (phiL ν μ e) p y v (fun j k => hdiffL p hp y j k)
  -- bounds, measurability, and integrability of the family
  have hgI : ∀ n : ℕ, n ≤ 1 → Integrable (ggDom μ T τ C e n) mHZ := fun n hn =>
    ((hInt ν μ rOut P T hd τ (n + 1) (by omega)).const_mul C).const_mul _
  have hbdPt : ∀ n : ℕ, n ≤ 1 → ∀ p : ℝ × Space, 0 < p.1 → ∀ w ∈ Metric.ball y ε,
      ‖iteratedFDeriv ℝ n (famE T τ i ν μ e p) w‖ ≤ ggDom μ T τ C e n p := by
    intro n hn p hp w hw
    have h1 := norm_fam_le (hG2 p hp) e n hn w
    have h2 := hbd (n + 1) (by omega) p hp w hw
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg (ContinuousLinearMap.apply ℝ ℂ e)))
  have hBd : ∀ n : ℕ, n ≤ 1 → ∀ᵐ p ∂mHZ, ∀ w ∈ Metric.ball y ε,
      ‖iteratedFDeriv ℝ n (famE T τ i ν μ e p) w‖ ≤ ggDom μ T τ C e n p :=
    fun n hn => hpos.mono fun p hp w hw => hbdPt n hn p hp w hw
  have hCD : ∀ᵐ p ∂mHZ, ContDiffOn ℝ 1 (famE T τ i ν μ e p) (Metric.ball y ε) :=
    hpos.mono fun p hp => (contDiff_fam (hG2 p hp) e).contDiffOn
  have hMeasP : ∀ n : ℕ, n ≤ 1 → ∀ w ∈ Metric.ball y ε,
      AEStronglyMeasurable (fun p => iteratedFDeriv ℝ n (famE T τ i ν μ e p) w) mHZ :=
    fun n hn w _ => aesm_fam (fun p => kerF T τ i (Kd ν μ) p) e n hn w
      (hpos.mono fun p hp => hG2 p hp) (hMeas ν μ rOut P T hd τ i (n + 1) (by omega) w)
  -- the first-order derivative of the parametric integral
  have hkey := hP mHZ (famE T τ i ν μ e) (Metric.ball y ε) (ggDom μ T τ C e) hball hCD
    (fun n hn => hgI n hn) (fun n hn => hBd n hn) (fun n hn => fun w hw => hMeasP n hn w hw)
    y hyU
  have hIntV : ∀ w ∈ Metric.ball y ε, Integrable (fun p => famE T τ i ν μ e p w) mHZ := by
    intro w hw
    refine Integrable.mono' (hgI 0 (by norm_num)) ?_ ?_
    · have hm0 := hMeasP 0 (by norm_num) w hw
      refine ((continuous_eval_const (0 : Fin 0 → Space)).comp_aestronglyMeasurable hm0).congr
        (Filter.Eventually.of_forall fun p => ?_)
      simp [iteratedFDeriv_zero_apply]
    · filter_upwards [hBd 0 (by norm_num)] with p hp
      have := hp w hw
      rwa [norm_iteratedFDeriv_zero] at this
  have hIntD : Integrable (fun p => fderiv ℝ (famE T τ i ν μ e p) y) mHZ := by
    refine Integrable.mono' (hgI 1 (by norm_num)) ?_ ?_
    · exact aesm_fderiv_clm (famE T τ i ν μ e) y (hMeasP 1 (by norm_num) y hyU)
    · filter_upwards [hBd 1 (by norm_num)] with p hp
      have := hp y hyU
      rwa [norm_iteratedFDeriv_one] at this
  -- left-hand side
  have hLHS : ∀ w ∈ Metric.ball y ε,
      kerInt T (phiL ν μ e) τ w i = -∫ p, famE T τ i ν μ e p w ∂mHZ := by
    intro w hw
    have hfe : (fun p => famE T τ i ν μ e p w) =ᵐ[mHZ]
        (fun p => kerF T τ i (phiL ν μ e) p w) := by
      filter_upwards [hpos] with p hp
      exact hFeq p hp w
    rw [hProd T τ i (phiL ν μ e) w ((hIntV w hw).congr hfe)]
    congr 1
    exact integral_congr_ae hfe.symm
  have hmain : HasFDerivAt (fun w => kerInt T (phiL ν μ e) τ w i)
      (-∫ p, fderiv ℝ (famE T τ i ν μ e p) y ∂mHZ) y := by
    refine (hkey.neg).congr_of_eventuallyEq ?_
    filter_upwards [hball.mem_nhds hyU] with w hw
    exact hLHS w hw
  refine ⟨hmain.differentiableAt, fun v => ?_⟩
  rw [hmain.fderiv, neg_apply, ContinuousLinearMap.integral_apply hIntD v]
  have hΨint : Integrable (fun p => kerF T τ i (phiPsi ν μ e v) p y) mHZ := by
    refine (ContinuousLinearMap.integrable_comp (ContinuousLinearMap.apply ℝ ℂ v) hIntD).congr ?_
    filter_upwards [hpos] with p hp
    exact hΨ p hp v
  rw [hProd T τ i (phiPsi ν μ e v) y hΨint]
  congr 1
  exact integral_congr_ae (hpos.mono fun p hp => hΨ p hp v)

/-- **(D2)** second `y`-derivative of `kerInt` under the integral (`KerIntD2`). -/
theorem kerIntD2_of (hP : ParamHasFDeriv1) (hPt : KdGapPt) (hInt : KdGapInt) (hMeas : KdGapMeas)
    (hSm : KdGapSmooth) (hProd : KerIntProd) (hF : KerFFderiv) : KerIntD2 := by
  intro ν μ rOut P T hd τ y hy l i
  exact kerIntD2_aux hP hPt hInt hMeas hSm hProd hF ν μ rOut P T hd τ y hy
    (UnforcedLeray.coordinateVector l) i

end UnforcedLeray.Short.PartIIIb.Concrete
