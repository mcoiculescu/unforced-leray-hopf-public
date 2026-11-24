import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1_1_2_3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_5.Pointwise.Decay
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_5.Pointwise.Calc
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_5.Pointwise.Cutoff

/-!
# `PartIII-b:C/rep/8/1/1/2/3/1`: the stream cut of `Re W_μ` of a separated source

Source `the November 2 reference manuscript` 4177-4186.  The single separated
response `Re W_μ` is `C²` off the source disk, divergence free, axisymmetric without swirl and has
the decay of `StreamDecay`; hence (as for `X₀ = W_μ - W_{μ+1}`) the outward primitive and the stream
cut are differentiable (`wgx_outPrim_hasFDerivAt`).  These are the single-response analogues of
`wgx_sepX0_div`, `wgx_sepX0_axi`, `wgx_sepX0_farBound`, `wgx_sepX0_streamDecay`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete.Sub8_1_1_2_3

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem wre_re_fderiv_le (g : Space → ℂ) (y v : Space) (hg : DifferentiableAt ℝ g y) :
    ‖fderiv ℝ (fun x => (g x).re) y v‖ ≤ ‖fderiv ℝ g y‖ * ‖v‖ := by
  have hd : HasFDerivAt (fun x => (g x).re) (Complex.reCLM.comp (fderiv ℝ g y)) y :=
    Complex.reCLM.hasFDerivAt.comp y hg.hasFDerivAt
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, Complex.reCLM_apply]
  rw [Real.norm_eq_abs]
  exact (Complex.abs_re_le_norm _).trans ((fderiv ℝ g y).le_opNorm v)

theorem wre_re_fderiv (g : Space → ℂ) (y v : Space) (hg : DifferentiableAt ℝ g y) :
    fderiv ℝ (fun x => (g x).re) y v = (fderiv ℝ g y v).re := by
  have hd : HasFDerivAt (fun x => (g x).re) (Complex.reCLM.comp (fderiv ℝ g y)) y :=
    Complex.reCLM.hasFDerivAt.comp y hg.hasFDerivAt
  rw [hd.fderiv]
  simp

theorem wre_contDiffOn {ν μ rOut P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hr : 0 ≤ rOut) (hP : 0 < P)
    (hS : IIIa.IsSepSource P rOut T) (hM : SepMoment P T) (τ : ℝ) :
    ContDiffOn ℝ 2 (sepWre ν μ T τ) {y : Space | rOut < ϱ y} :=
  tcd_Wre_cd hν hμ hr hP hS hM τ

/-- `Re W_μ` is divergence free off the source disk. -/
theorem wre_div {ν μ rOut P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hr : 0 ≤ rOut) (hP : 0 < P)
    (hS : IIIa.IsSepSource P rOut T) (hM : SepMoment P T) (τ : ℝ) (y : Space)
    (hyr : rOut < ϱ y) :
    ∑ j : Fin 3, physPd (sepWre ν μ T τ) j y j = 0 := by
  have hμ0 : -(1 / 4) < (μ : ℂ).re := by simpa using hμ
  have hD0 := sepWDivFree_all ν (μ : ℂ) rOut P T hν hμ0 hr hP hS hM τ y hyr
  have hsm0 := sepWSmoothOn_of IIIa.sepKernelBounds ν (μ : ℂ) rOut P T hν hμ0 hr hP hS hM τ
  have hopen : IsOpen {y : Space | rOut < ϱ y} :=
    isOpen_lt continuous_const (by unfold ϱ; fun_prop)
  have hdA : ∀ i, DifferentiableAt ℝ (fun y' => IIIa.sepW ν (μ : ℂ) T y' τ i) y := fun i =>
    ((hsm0 i).differentiableOn (by norm_num)).differentiableAt (hopen.mem_nhds hyr)
  have hF : DifferentiableAt ℝ (fun y' => sepWre ν μ T τ y') y := by
    rw [differentiableAt_piLp]
    intro i
    exact Complex.reCLM.differentiableAt.comp y (hdA i)
  have hcomp : ∀ j : Fin 3, physPd (sepWre ν μ T τ) j y j =
      (fderiv ℝ (fun y' => IIIa.sepW ν (μ : ℂ) T y' τ j) y (coordinateVector j)).re := by
    intro j
    unfold physPd
    rw [wgx_coord_fderiv _ y hF _ j]
    exact wre_re_fderiv _ y _ (hdA j)
  calc ∑ j : Fin 3, physPd (sepWre ν μ T τ) j y j
      = ∑ j : Fin 3, (fderiv ℝ (fun y' => IIIa.sepW ν (μ : ℂ) T y' τ j) y
          (coordinateVector j)).re := Finset.sum_congr rfl fun j _ => hcomp j
    _ = 0 := by
        rw [← Complex.re_sum, hD0]
        simp

theorem wre_equivariant (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : M * M.transpose = 1)
    (ν μ : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hT : ∀ τ z, T τ (actM M z) = M * T τ z * M.transpose) (y : Space) (τ : ℝ)
    (hI1 : SepIntegrableAt ν (μ : ℂ) T y τ) :
    sepWre ν μ T τ (actM M y) = actM M (sepWre ν μ T τ y) := by
  have h1 := sepWEquivariance M hM ν (μ : ℂ) T hT y τ hI1
  unfold sepWre
  ext i
  simp only [h1]
  simp only [actM, Matrix.mulVec, dotProduct, PiLp.toLp_apply, WithLp.ofLp_toLp]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp

/-- Frame form of `Re W_μ` at points of the young region. -/
theorem wre_axi {ν μ rOut P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hr : 0 ≤ rOut) (hP : 0 < P)
    (hS : IIIa.IsSepSource P rOut T) (hM : SepMoment P T) (hAx : IsAxiSource T)
    (τ : ℝ) (y : Space) (hyr : rOut < ϱ y) :
    sepWre ν μ T τ y = frameL y !₂[sepWre ν μ T τ (meridPt y) 0, sepWre ν μ T τ (meridPt y) 2] := by
  have hρ : 0 < ϱ y := lt_of_le_of_lt hr hyr
  obtain ⟨hco, hmer⟩ := wgx_rot_meridPt hρ
  have hmr : rOut < ϱ (meridPt y) := by rw [varrho_meridPt]; exact hyr
  have hI1 := sepIntegrableOfSource_all ν (μ : ℂ) rOut P T hν (by simpa using hμ) hr hP hS hM τ
    (meridPt y) hmr
  have hfix : actM reflM (meridPt y) = meridPt y := by
    ext i
    fin_cases i <;> simp [actM, reflM, meridPt, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have e1 := wre_equivariant _ (rotM_orth hco) ν μ T (fun τ z => hAx.1 _ _ hco τ z)
    (meridPt y) τ hI1
  have e2 := wre_equivariant _ reflM_orth ν μ T (fun τ z => hAx.2 τ z) (meridPt y) τ hI1
  rw [hmer] at e1
  rw [hfix] at e2
  have h1 : sepWre ν μ T τ (meridPt y) 1 = 0 := by
    have := congrArg (fun w : Space => w 1) e2
    simp [actM, reflM, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at this
    linarith
  rw [e1]
  ext i
  fin_cases i <;>
    simp [actM, rotM, frameL_apply, eR, hor, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h1] <;>
    field_simp

/-- Far-field and compact bounds for `Re W_μ` along the half plane (single-response analogue of
`wgx_sepX0_farBound`). -/
theorem wre_farBound {ν μ R P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hR : 0 < R) (hμ : -(1 / 4) < μ) (hP : 0 < P)
    (hS : IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T) (hM : SepMoment P T) (τ r z : ℝ)
    (hr : R * Real.sqrt (5 * ν / 6) < r) :
    ∃ a C : ℝ, 1 < a ∧ ∀ ρ ∈ Ioi r, ∀ z' ∈ Metric.ball z 1,
      ‖ρ * sepWre ν μ T τ !₂[ρ, 0, z'] 2‖ ≤ C * ρ ^ (-a) ∧
      ‖ρ * fderiv ℝ (sepWre ν μ T τ) !₂[ρ, 0, z'] (coordinateVector 2) 2‖ ≤ C * ρ ^ (-a) ∧
      ‖ρ * sepWre ν μ T τ !₂[ρ, 0, z'] 0‖ ≤ C * ρ ^ (-a) := by
  have hW := sepWSmoothOn_of IIIa.sepKernelBounds
  have hfar := sepFarDecay
  have hr0pos : 0 < R * Real.sqrt (5 * ν / 6) := by positivity
  set r0 : ℝ := R * Real.sqrt (5 * ν / 6) with hr0def
  have hμ' : -(1 / 4 : ℝ) < ((μ : ℝ) : ℂ).re := by
    simp only [Complex.ofReal_re]
    exact hμ
  have hSm : ContDiffOn ℝ 2 (sepWre ν μ T τ) (youngOpen ν R) :=
    wre_contDiffOn hν hμ hr0pos.le hP hS hM τ
  have hOpen : IsOpen (youngOpen ν R) := by
    unfold youngOpen
    exact isOpen_lt continuous_const Axi.continuous_ϱ
  have hG : ∀ i : Fin 3, ContDiffOn ℝ 2 (fun y => IIIa.sepW ν (μ : ℂ) T y τ i)
      (youngOpen ν R) :=
    fun i => hW ν (μ : ℂ) r0 P T hν hμ' hr0pos.le hP hS hM τ i
  have K1 : ∀ (y : Space) (i : Fin 3),
      sepWre ν μ T τ y i = (IIIa.sepW ν (μ : ℂ) T y τ i).re := by
    intro y i
    simp only [sepWre, PiLp.toLp_apply]
  have hFd : ∀ y : Space, y ∈ youngOpen ν R →
      DifferentiableAt ℝ (sepWre ν μ T τ) y := fun y hy =>
    (hSm.contDiffAt (hOpen.mem_nhds hy)).differentiableAt (by norm_num)
  have hGd : ∀ (i : Fin 3) (y : Space), y ∈ youngOpen ν R →
      DifferentiableAt ℝ (fun x => IIIa.sepW ν (μ : ℂ) T x τ i) y := fun i y hy =>
    ((hG i).contDiffAt (hOpen.mem_nhds hy)).differentiableAt (by norm_num)
  have Dcomp : ∀ (y v : Space) (i : Fin 3), y ∈ youngOpen ν R →
      fderiv ℝ (sepWre ν μ T τ) y v i =
        fderiv ℝ (fun x => (IIIa.sepW ν (μ : ℂ) T x τ i).re) y v := by
    intro y v i hy
    have hfun : (fun x => sepWre ν μ T τ x i) =
        (fun x => (IIIa.sepW ν (μ : ℂ) T x τ i).re) :=
      funext fun x => K1 x i
    rw [← wardFar_proj_fderiv _ y v i (hFd y hy), hfun]
  obtain ⟨C1, hC1⟩ := hfar ν (μ : ℂ) r0 P T hν hμ' hr0pos.le hP hS hM τ
  have hcv : ‖coordinateVector (2 : Fin 3)‖ = 1 := by
    first
    | exact UnforcedLeray.RieszLp.norm_coordinateVector 2
    | simp [coordinateVector]
  have hLval : ∀ (y : Space) (i : Fin 3), y ∈ youngOpen ν R → 2 * r0 ≤ ϱ y →
      |sepWre ν μ T τ y i| ≤ C1 * ϱ y ^ (-3:ℝ) := by
    intro y i _ h2
    calc |sepWre ν μ T τ y i|
        = |(IIIa.sepW ν (μ : ℂ) T y τ i).re| := by rw [K1 y i]
      _ ≤ ‖IIIa.sepW ν (μ : ℂ) T y τ i‖ := Complex.abs_re_le_norm _
      _ ≤ C1 * ϱ y ^ (-3:ℝ) := (hC1 i y h2).1
  have hLder : ∀ (y : Space), y ∈ youngOpen ν R → 2 * r0 ≤ ϱ y →
      |fderiv ℝ (sepWre ν μ T τ) y (coordinateVector 2) 2| ≤ C1 * ϱ y ^ (-3:ℝ) := by
    intro y hyU h2
    calc |fderiv ℝ (sepWre ν μ T τ) y (coordinateVector 2) 2|
        = ‖fderiv ℝ (sepWre ν μ T τ) y (coordinateVector 2) 2‖ :=
          (Real.norm_eq_abs _).symm
      _ = ‖fderiv ℝ (fun x => (IIIa.sepW ν (μ : ℂ) T x τ 2).re) y (coordinateVector 2)‖ := by
          rw [Dcomp y (coordinateVector 2) 2 hyU]
      _ ≤ ‖fderiv ℝ (fun x => IIIa.sepW ν (μ : ℂ) T x τ 2) y‖ * ‖coordinateVector 2‖ :=
          wre_re_fderiv_le _ y _ (hGd 2 y hyU)
      _ ≤ C1 * ϱ y ^ (-3:ℝ) * 1 := by
          rw [hcv]
          exact mul_le_mul_of_nonneg_right (hC1 2 y h2).2 zero_le_one
      _ = C1 * ϱ y ^ (-3:ℝ) := by ring
  -- the compact range and its continuity
  have hφ : Continuous (fun p : ℝ × ℝ => (!₂[p.1, 0, p.2] : Space)) := by
    fun_prop
  have hmaps : MapsTo (fun p : ℝ × ℝ => (!₂[p.1, 0, p.2] : Space))
      (Icc r (2 * r0) ×ˢ Metric.closedBall z 1) (youngOpen ν R) := by
    rintro ⟨a, b⟩ hp
    have ha : r ≤ a := hp.1.1
    have hpos : 0 ≤ a := by linarith
    show r0 < ϱ (!₂[a, 0, b] : Space)
    rw [wardFar_varrho a b hpos]
    linarith
  have hFc : ContinuousOn (fun p : ℝ × ℝ => sepWre ν μ T τ (!₂[p.1, 0, p.2] : Space))
      (Icc r (2 * r0) ×ˢ Metric.closedBall z 1) :=
    hSm.continuousOn.comp hφ.continuousOn hmaps
  have hDc : ContinuousOn (fun p : ℝ × ℝ =>
      fderiv ℝ (sepWre ν μ T τ) (!₂[p.1, 0, p.2] : Space))
      (Icc r (2 * r0) ×ˢ Metric.closedBall z 1) :=
    (hSm.continuousOn_fderiv_of_isOpen hOpen (by norm_num)).comp hφ.continuousOn hmaps
  have hSc : IsCompact (Icc r (2 * r0) ×ˢ Metric.closedBall z 1) :=
    isCompact_Icc.prod (ProperSpace.isCompact_closedBall z 1)
  obtain ⟨M1, hM1⟩ := hSc.exists_bound_of_continuousOn hFc
  obtain ⟨M2, hM2⟩ := hSc.exists_bound_of_continuousOn hDc.norm
  obtain ⟨Cc, hCc⟩ : ∃ Cc : ℝ, Cc = |C1| + (2 * r0) ^ 3 * (|M1| + |M2|) :=
    ⟨_, rfl⟩
  refine ⟨2, Cc, by norm_num, ?_⟩
  intro ρ hρ z' hz'
  have hρr : r < ρ := hρ
  have hρpos : 0 < ρ := lt_trans (lt_trans hr0pos hr) hρr
  set y0 : Space := (!₂[ρ, 0, z'] : Space) with hy0
  have hyρ : ϱ y0 = ρ := by
    rw [hy0]
    exact wardFar_varrho ρ z' hρpos.le
  have hy0U : y0 ∈ youngOpen ν R := by
    show r0 < ϱ y0
    rw [hyρ]
    linarith
  have hnn : 0 ≤ (2 * r0) ^ 3 * (|M1| + |M2|) := by positivity
  rcases le_total (2 * r0) ρ with h2 | h2
  · -- far regime `2 r_o ≤ ρ`
    have h2' : 2 * r0 ≤ ϱ y0 := by
      rw [hyρ]
      exact h2
    have hKL : C1 ≤ Cc := by
      rw [hCc]
      linarith [le_abs_self C1]
    have hA := hLval y0 2 hy0U h2'
    have hB := hLder y0 hy0U h2'
    have hD := hLval y0 0 hy0U h2'
    rw [hyρ] at hA hB hD
    exact ⟨wardFar_arith ρ _ _ _ hρpos hKL hA, wardFar_arith ρ _ _ _ hρpos hKL hB,
      wardFar_arith ρ _ _ _ hρpos hKL hD⟩
  · -- near regime `r < ρ ≤ 2 r_o`: compact bound
    have hmem : (ρ, z') ∈ Icc r (2 * r0) ×ˢ Metric.closedBall z 1 :=
      ⟨⟨hρr.le, h2⟩, Metric.ball_subset_closedBall hz'⟩
    have hVn : ‖sepWre ν μ T τ y0‖ ≤ M1 := hM1 (ρ, z') hmem
    have hDn : ‖fderiv ℝ (sepWre ν μ T τ) y0‖ ≤ M2 := by
      simpa only [norm_norm] using hM2 (ρ, z') hmem
    have hMM : |M1| + |M2| ≥ 0 := by positivity
    have hVal : ∀ i : Fin 3, |sepWre ν μ T τ y0 i| ≤ |M1| + |M2| := by
      intro i
      rw [← Real.norm_eq_abs]
      refine (PiLp.norm_apply_le _ i).trans (hVn.trans ?_)
      linarith [le_abs_self M1, abs_nonneg M2]
    have hDer : |fderiv ℝ (sepWre ν μ T τ) y0 (coordinateVector 2) 2|
        ≤ |M1| + |M2| := by
      rw [← Real.norm_eq_abs]
      refine (PiLp.norm_apply_le _ 2).trans ?_
      refine ((fderiv ℝ (sepWre ν μ T τ) y0).le_opNorm _).trans ?_
      rw [hcv, mul_one]
      linarith [le_abs_self M2, abs_nonneg M1]
    have hKS : (2 * r0) ^ 3 * (|M1| + |M2|) ≤ Cc := by
      rw [hCc]
      linarith [abs_nonneg C1]
    exact ⟨wardFar_arith ρ _ _ _ hρpos hKS
        (wardFar_small_bound ρ (2 * r0) (|M1| + |M2|) _ hρpos h2 hMM (hVal 2)),
      wardFar_arith ρ _ _ _ hρpos hKS
        (wardFar_small_bound ρ (2 * r0) (|M1| + |M2|) _ hρpos h2 hMM hDer),
      wardFar_arith ρ _ _ _ hρpos hKS
        (wardFar_small_bound ρ (2 * r0) (|M1| + |M2|) _ hρpos h2 hMM (hVal 0))⟩

theorem wre_streamDecay {ν μ R P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hR : 0 < R) (hμ : -(1 / 4) < μ) (hP : 0 < P)
    (hS : IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T) (hM : SepMoment P T) (τ : ℝ) :
    StreamDecay ν R (sepWre ν μ T) τ := by
  intro r z hr
  obtain ⟨a, C, ha, h⟩ := wre_farBound hν hR hμ hP hS hM τ r z hr
  refine ⟨⟨fun ρ => C * ρ ^ (-a), ?_, fun ρ hρ z' hz' =>
    ⟨(h ρ hρ z' hz').1, (h ρ hρ z' hz').2.1⟩⟩, ?_⟩
  · have hr0 : 0 < R * Real.sqrt (5 * ν / 6) := by positivity
    exact (integrableOn_Ioi_rpow_of_lt (by linarith) (hr0.trans hr)).const_mul C
  · have hz : Tendsto (fun ρ : ℝ => C * ρ ^ (-a)) atTop (nhds 0) := by
      simpa using (tendsto_rpow_neg_atTop (by linarith : 0 < a)).const_mul C
    refine squeeze_zero_norm' ?_ hz
    filter_upwards [eventually_gt_atTop r] with ρ hρ
    exact (h ρ hρ z (Metric.mem_ball_self one_pos)).2.2

/-- The two partial derivatives of the outward primitive of `Re W_μ`. -/
theorem wre_partials {ν μ R P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hR : 0 < R) (hμ : -(1 / 4) < μ) (hP : 0 < P)
    (hS : IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T) (hM : SepMoment P T)
    (hAx : IsAxiSource T) (τ : ℝ) (r z : ℝ) (hr : R * Real.sqrt (5 * ν / 6) < r) :
    HasDerivAt (fun r' => outPrim (sepWre ν μ T) τ r' z) (r * sepWre ν μ T τ !₂[r, 0, z] 2) r ∧
      HasDerivAt (fun z' => outPrim (sepWre ν μ T) τ r z')
        (-(r * sepWre ν μ T τ !₂[r, 0, z] 0)) z := by
  have hr0 : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hZc : ContDiffOn ℝ 2 (sepWre ν μ T τ) (youngOpen ν R) :=
    wre_contDiffOn hν hμ hr0 hP hS hM τ
  have hdec := wre_streamDecay hν hR hμ hP hS hM τ
  refine ⟨outPrimDerivR ν R (sepWre ν μ T) τ hZc hdec r z hr,
    outPrimDerivZ ν R (sepWre ν μ T) τ hZc ?_ ?_ hdec r z hr⟩
  · intro y hy
    exact wre_div hν hμ hr0 hP hS hM τ y hy
  · intro τ' y hy _
    exact wre_axi hν hμ hr0 hP hS hM hAx τ' y hy

/-- The outward primitive of `Re W_μ` is differentiable in `y` off the source disk. -/
theorem wre_outPrim_hasFDerivAt {ν μ R P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hR : 0 < R) (hμ : -(1 / 4) < μ) (hP : 0 < P)
    (hS : IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T) (hM : SepMoment P T)
    (hAx : IsAxiSource T) (τ : ℝ) {y : Space} (hy : R * Real.sqrt (5 * ν / 6) < ϱ y) :
    ∃ Ψd : Space →L[ℝ] ℝ,
      HasFDerivAt (fun y : Space => outPrim (sepWre ν μ T) τ (ϱ y) (y 2)) Ψd y := by
  have hr0 : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  exact ⟨_, wgx_outPrim_hasFDerivAt hν hR (wre_contDiffOn hν hμ hr0 hP hS hM τ)
    (fun r z hr => wre_partials hν hR hμ hP hS hM hAx τ r z hr) hy⟩

end UnforcedLeray.Short.PartIIIb.Concrete.Sub8_1_1_2_3
