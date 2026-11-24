import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_3
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L2

/-!
# `kerIntD1_of` (`PartIII-b:C/rep/2/6/3/3/9`)

First `y`-derivative of `kerInt Kd` under the integral, from the leaf Props `ParamHasFDeriv1`,
`KdGapPt`, `KdGapInt`, `KdGapMeas`, `KdGapSmooth`, `KerIntProd`, `KerFFderiv`.
Source 3603-3626, 3800-3807, 4171-4200, 5223.
The componentwise `y`-differentiability of `Kd` (for `h > 0`) comes from `heatLerayKSmooth`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `y`-differentiability of the `Gker` components for `h > 0`, `ν > 0`. -/
lemma gker_diffY (ν : ℝ) (m : ℂ) (h : ℝ) (hν : 0 < ν) (hh : 0 < h) (y z : Space)
    (i j k : Fin 3) : DifferentiableAt ℝ (fun y' => Gker ν m h y' z i j k) y := by
  have hexp : Real.exp (-h) < 1 := by
    have := Real.exp_lt_exp.2 (show -h < 0 by linarith)
    simpa using this
  have ht : 0 < ν * (1 - Real.exp (-h)) := mul_pos hν (by linarith)
  have hK : ContDiff ℝ 3 (fun x => IIIa.heatLerayK (ν * (1 - Real.exp (-h))) i j x) :=
    heatLerayKSmooth _ ht i j
  have h2 : ContDiff ℝ 2 (fderiv ℝ (fun x => IIIa.heatLerayK (ν * (1 - Real.exp (-h))) i j x)) :=
    hK.fderiv_right (m := 2) (by norm_num)
  have h2' : ContDiff ℝ 2 (fun y' : Space => fderiv ℝ
      (fun x => IIIa.heatLerayK (ν * (1 - Real.exp (-h))) i j x) (y' - Real.exp (-h / 2) • z)) :=
    h2.comp (by fun_prop)
  have h4 : DifferentiableAt ℝ (fun y' : Space => fderiv ℝ
      (fun x => IIIa.heatLerayK (ν * (1 - Real.exp (-h))) i j x) (y' - Real.exp (-h / 2) • z)
        (UnforcedLeray.coordinateVector k)) y :=
    (h2'.differentiable (by norm_num) y).clm_apply (differentiableAt_const _)
  have h5 : DifferentiableAt ℝ (fun y' : Space => ((fderiv ℝ
      (fun x => IIIa.heatLerayK (ν * (1 - Real.exp (-h))) i j x) (y' - Real.exp (-h / 2) • z)
        (UnforcedLeray.coordinateVector k) : ℝ) : ℂ)) y :=
    Complex.ofRealCLM.differentiableAt.comp y h4
  unfold Gker
  exact (differentiableAt_const _).mul h5

/-- `y`-differentiability of the components of `Kd` for `h > 0`, `ν > 0`. -/
lemma kd_diffY (ν μ h : ℝ) (hν : 0 < ν) (hh : 0 < h) (y z : Space) (i j k : Fin 3) :
    DifferentiableAt ℝ (fun y' => Kd ν μ h y' z i j k) y := by
  unfold Kd
  exact (gker_diffY ν (μ : ℂ) h hν hh y z i j k).sub
    (gker_diffY ν ((μ : ℂ) + 1) h hν hh y z i j k)

/-- The `h`-integral runs over `Ioi 0`: `mHZ`-a.e. `h > 0`. -/
lemma ae_pos_mHZ : ∀ᵐ p ∂mHZ, 0 < p.1 := by
  unfold mHZ
  have hq := (Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Ioi (0 : ℝ)))
    (ν := (volume : Measure Space)))
  exact hq.ae (ae_restrict_mem measurableSet_Ioi)

theorem kerIntD1_of (hP : ParamHasFDeriv1) (hPt : KdGapPt) (hInt : KdGapInt)
    (hMeas : KdGapMeas) (hSm : KdGapSmooth) (hProd : KerIntProd) (hF : KerFFderiv) :
    KerIntD1 := by
  intro ν μ rOut P T hd τ y hy i
  have hd' := hd
  obtain ⟨hν, -, -, -, -, -⟩ := hd'
  obtain ⟨ε, hε, -, C, hC0, hbd⟩ := hPt ν μ rOut P T hd τ y hy i
  set U : Set Space := Metric.ball y ε with hUdef
  have hU : IsOpen U := Metric.isOpen_ball
  have hyU : y ∈ U := Metric.mem_ball_self hε
  have hpos : ∀ᵐ p ∂mHZ, 0 < p.1 := ae_pos_mHZ
  have hconv : ∀ᵐ p ∂mHZ, ContDiffOn ℝ 1 (kerF T τ i (Kd ν μ) p) U := by
    filter_upwards [hpos] with p hp
    exact ((hSm ν μ hν T τ i p hp).of_le (by norm_num)).contDiffOn
  have hgint : ∀ n, n ≤ 1 → Integrable (fun p : ℝ × Space => C * gMaj μ T τ n p) mHZ :=
    fun n hn => (hInt ν μ rOut P T hd τ n (by omega)).const_mul C
  have hb : ∀ n, n ≤ 1 → ∀ᵐ p ∂mHZ, ∀ y' ∈ U,
      ‖iteratedFDeriv ℝ n (kerF T τ i (Kd ν μ) p) y'‖ ≤ C * gMaj μ T τ n p := by
    intro n hn
    filter_upwards [hpos] with p hp
    intro y' hy'
    exact hbd n (by omega) p hp y' hy'
  have hmeasG : ∀ n, n ≤ 1 → ∀ y' ∈ U,
      AEStronglyMeasurable (fun p => iteratedFDeriv ℝ n (kerF T τ i (Kd ν μ) p) y') mHZ :=
    fun n hn y' _ => hMeas ν μ rOut P T hd τ i n (by omega) y'
  have hm0 : ∀ y' ∈ U, AEStronglyMeasurable (fun p => kerF T τ i (Kd ν μ) p y') mHZ := by
    intro y' hy'
    have h := (continuousMultilinearCurryFin0 ℝ Space ℂ).continuous.comp_aestronglyMeasurable
      (hmeasG 0 (by norm_num) y' hy')
    refine h.congr (Filter.Eventually.of_forall fun a => ?_)
    simp [iteratedFDeriv_zero_eq_comp]
  have hcurry1 : ∀ (G : Space → ℂ) (z : Space),
      continuousMultilinearCurryFin1 ℝ Space ℂ (iteratedFDeriv ℝ 1 G z) = fderiv ℝ G z := by
    intro G z
    ext v
    simp [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
  have hm1 : AEStronglyMeasurable (fun p => fderiv ℝ (kerF T τ i (Kd ν μ) p) y) mHZ := by
    have h := (continuousMultilinearCurryFin1 ℝ Space ℂ).continuous.comp_aestronglyMeasurable
      (hmeasG 1 (by norm_num) y hyU)
    refine h.congr (Filter.Eventually.of_forall fun a => ?_)
    exact hcurry1 _ y
  have hint0 : ∀ y' ∈ U, Integrable (fun p => kerF T τ i (Kd ν μ) p y') mHZ := by
    intro y' hy'
    refine (hgint 0 (by norm_num)).mono' (hm0 y' hy') ?_
    filter_upwards [hb 0 (by norm_num)] with p hp
    have := hp y' hy'
    simpa [norm_iteratedFDeriv_zero] using this
  have hb1y : ∀ᵐ p ∂mHZ, ‖fderiv ℝ (kerF T τ i (Kd ν μ) p) y‖ ≤ C * gMaj μ T τ 1 p := by
    filter_upwards [hb 1 (by norm_num)] with p hp
    have := hp y hyU
    simpa [norm_iteratedFDeriv_one] using this
  have hint1 : Integrable (fun p => fderiv ℝ (kerF T τ i (Kd ν μ) p) y) mHZ :=
    (hgint 1 (by norm_num)).mono' hm1 hb1y
  have E1 : ∀ y' ∈ U, kerInt T (Kd ν μ) τ y' i = -∫ p, kerF T τ i (Kd ν μ) p y' ∂mHZ :=
    fun y' hy' => hProd T τ i (Kd ν μ) y' (hint0 y' hy')
  have hasD := hP (α := ℝ × Space) mHZ (kerF T τ i (Kd ν μ)) U
    (fun n p => C * gMaj μ T τ n p) hU hconv hgint hb hmeasG y hyU
  have hev : (fun y' => kerInt T (Kd ν μ) τ y' i) =ᶠ[nhds y]
      (fun y' => -∫ p, kerF T τ i (Kd ν μ) p y' ∂mHZ) :=
    Filter.eventually_of_mem (hU.mem_nhds hyU) (fun y' hy' => E1 y' hy')
  have hD : HasFDerivAt (fun y' => kerInt T (Kd ν μ) τ y' i)
      (-∫ p, fderiv ℝ (kerF T τ i (Kd ν μ) p) y ∂mHZ) y :=
    (hasD.neg).congr_of_eventuallyEq hev
  refine ⟨hD.differentiableAt, fun v => ?_⟩
  have hintv : Integrable (fun p => fderiv ℝ (kerF T τ i (Kd ν μ) p) y v) mHZ :=
    (ContinuousLinearMap.apply ℝ ℂ v).integrable_comp hint1
  have hcomm : (∫ p, fderiv ℝ (kerF T τ i (Kd ν μ) p) y ∂mHZ) v
      = ∫ p, fderiv ℝ (kerF T τ i (Kd ν μ) p) y v ∂mHZ :=
    ((ContinuousLinearMap.apply ℝ ℂ v).integral_comp_comm hint1).symm
  have hae : (fun p => fderiv ℝ (kerF T τ i (Kd ν μ) p) y v) =ᵐ[mHZ]
      (fun p => kerF T τ i (fun h y' z i' j k => fderiv ℝ (fun y'' => Kd ν μ h y'' z i' j k) y' v)
        p y) := by
    filter_upwards [hpos] with p hp
    exact hF T τ i (Kd ν μ) p y v (fun j k => kd_diffY ν μ p.1 hν hp y p.2 i j k)
  have hIntΨ : Integrable (fun p => kerF T τ i
      (fun h y' z i' j k => fderiv ℝ (fun y'' => Kd ν μ h y'' z i' j k) y' v) p y) mHZ :=
    hintv.congr hae
  rw [hD.fderiv, neg_apply, hcomm,
    hProd T τ i (fun h y' z i' j k => fderiv ℝ (fun y'' => Kd ν μ h y'' z i' j k) y' v) y hIntΨ,
    integral_congr_ae hae]

end UnforcedLeray.Short.PartIIIb.Concrete
