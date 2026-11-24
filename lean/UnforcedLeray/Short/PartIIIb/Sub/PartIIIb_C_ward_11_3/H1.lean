import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.YBound
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.EMeas
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9.L4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9_3.S1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_10_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_10_3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.ActYDiff.Cut

/-!
# Helpers for `wardDYYoungL2_proved` (1): regularity, measurability, and `∂_j(χ_yW_μ)`
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- `wardW` of old `L²` data equals `sepWre` of the cut old source. -/
theorem w113_W_eq {ν μ R c : ℝ} (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) {g : Chart → Ten3}
    (hg : IsOldL2 c ν g) :
    wardW ν μ R c g = sepWre ν μ (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) := by
  obtain ⟨-, -, hae⟩ := xa_oldReg hc hν hR hg
  funext τ y
  simp only [wardW, sepWre, sepWCongrAE ν (μ : ℂ) _ _ hae y τ]

/-- `transField` of old `L²` data equals `streamCorr (sepWre) + sepComm`. -/
theorem w113_transField_eq {ν μ R c : ℝ} {χy : ℝ → ℝ} (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c)
    {g : Chart → Ten3} (hg : IsOldL2 c ν g) (τ : ℝ) (y : Space) :
    transField ν μ R c χy g τ y =
      streamCorr ν R χy (sepWre ν μ (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g)) τ y +
        sepComm ν μ R χy (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) τ y := by
  obtain ⟨-, -, hae⟩ := xa_oldReg hc hν hR hg
  have hresp : ∀ (m : ℂ) (z : Space) (t : ℝ),
      IIIa.sepW ν m (oldPhys R c g) z t =
        IIIa.sepW ν m (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) z t :=
    fun m z t => sepWCongrAE ν m _ _ hae z t
  have heq : transField ν μ R c χy g =
      sepTrans ν μ R χy (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) := by
    rw [transField_eq_sepTrans]
    exact sepTrans_congr hresp
  exact congrFun (congrFun heq τ) y

/-- Off the axis (`0 < ϱ y`), `sepComm` equals `tcComm` for any separated axisymmetric source. -/
theorem w113_sepComm_eq_tcComm {ν μ R P : ℝ} {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy)
    (hν : 0 < ν) (hR : 0 < R) (hμ : -(1 / 4) < μ) (hP : 0 < P)
    {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hT : IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T) (hM : SepMoment P T)
    (hA : IsAxiSource T) (τ : ℝ) {y : Space} (hy : 0 < ϱ y) :
    sepComm ν μ R χy T τ y = tcComm ν R χy (sepX0 ν μ T) τ y := by
  by_cases hmem : y ∈ streamAnn ν R
  · have hctx : TCCtxW μ μ ν μ R P T y :=
      ⟨hμ, hν, trivial, hR, hP, ⟨le_rfl, le_rfl⟩, hT, hM, hA, hmem⟩
    obtain ⟨r1, r2, r3, r4⟩ := tcRegW μ μ ν μ R P T τ y hctx
    obtain ⟨i1, i2, i3, i4⟩ := tcIntW μ μ ν μ R P T τ y hctx
    exact tcLeibniz ν μ R χy hχ hν hR (sepX0 ν μ T) τ y hy r1 r2 r3 r4 i1 i2 i3 i4
      (tcTimeW μ μ ν μ R P T τ y hctx)
      (tcGrad_of_partsW tcGradX0StructW tcGradX0DecayW μ μ ν μ R P T τ y hctx)
      (tcLapW μ μ ν μ R P T τ y hctx) (tcRadW μ μ ν μ R P T τ y hctx) (μ + 1)
  · have hout := (Sub8_1_1_2_3.tcOut_iff_not_mem hν hR hy).2 hmem
    rw [Sub8_1_1_2_3.sepComm_eq_tcComm_out hχ T τ hy hout,
      Sub8_1_1_2_3.tcComm_eq_zero_out hχ _ τ hy hout]

/-- `tcComm` of a separated axisymmetric source is differentiable off the axis. -/
theorem w113_tcComm_diffAt {ν μ R P : ℝ} {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy)
    (hν : 0 < ν) (hR : 0 < R) (hμ : -(1 / 4) < μ) (hP : 0 < P)
    {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hT : IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T) (hM : SepMoment P T)
    (hA : IsAxiSource T) (τ : ℝ) {y : Space} (hy : 0 < ϱ y) :
    DifferentiableAt ℝ (tcComm ν R χy (sepX0 ν μ T) τ) y := by
  by_cases hmem : y ∈ streamAnn ν R
  · have hctx : TCCtxW μ μ ν μ R P T y :=
      ⟨hμ, hν, trivial, hR, hP, ⟨le_rfl, le_rfl⟩, hT, hM, hA, hmem⟩
    obtain ⟨r1, _, r3, _⟩ := tcRegW μ μ ν μ R P T τ y hctx
    exact Sub8_1_1_2_3.tcComm_diffAt hχ (sepX0 ν μ T) τ hy r1 r3
  · have hout := (Sub8_1_1_2_3.tcOut_iff_not_mem hν hR hy).2 hmem
    have hz := Sub8_1_1_2_3.tcComm_eventually_zero hχ (sepX0 ν μ T) τ hy hout
    exact (differentiableAt_const (0 : Space)).congr_of_eventuallyEq hz

/-- `sepComm` of a separated axisymmetric source is differentiable off the axis. -/
theorem w113_sepComm_diffAt {ν μ R P : ℝ} {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy)
    (hν : 0 < ν) (hR : 0 < R) (hμ : -(1 / 4) < μ) (hP : 0 < P)
    {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hT : IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T) (hM : SepMoment P T)
    (hA : IsAxiSource T) (τ : ℝ) {y : Space} (hy : 0 < ϱ y) :
    DifferentiableAt ℝ (sepComm ν μ R χy T τ) y := by
  have hpos : ∀ᶠ y' in 𝓝 y, 0 < ϱ y' :=
    (continuous_ϱ.continuousAt).eventually (lt_mem_nhds hy)
  have heq : sepComm ν μ R χy T τ =ᶠ[𝓝 y] tcComm ν R χy (sepX0 ν μ T) τ := by
    filter_upwards [hpos] with y' hy'
    exact w113_sepComm_eq_tcComm hχ hν hR hμ hP hT hM hA τ hy'
  exact (w113_tcComm_diffAt hχ hν hR hμ hP hT hM hA τ hy).congr_of_eventuallyEq heq

/-- `wardYoungW` is differentiable off the axis (`0 < ϱ y`). -/
theorem w113_wardYoungW_diffAt {ν μ R c : ℝ} {χy : ℝ → ℝ} (hχy : IsYoungCutoff χy)
    (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4) < μ)
    {g : Chart → Ten3} (hg : IsOldL2 c ν g) (τ : ℝ) {y : Space} (hy : 0 < ϱ y) :
    DifferentiableAt ℝ (wardYoungW ν μ R c χy g τ) y := by
  obtain ⟨hS, hM, _⟩ := w10_ctx hν hR hc hg
  set T := oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g with hTdef
  have hW := w113_W_eq (μ := μ) hν hR hc hg
  have hfun : wardYoungW ν μ R c χy g τ = fun y' => χy (ν * age R y') • sepWre ν μ T τ y' := by
    funext y'
    simp only [wardYoungW, hW, hTdef]
  rw [hfun]
  by_cases hold : 1 < ν * age R y
  · have hcAt : ContinuousAt (fun y' : Space => ν * (R ^ 2 / ϱ y' ^ 2)) y :=
      (continuousAt_const.div ((continuous_ϱ.pow 2).continuousAt)
        (pow_ne_zero 2 hy.ne')).const_mul ν
    have hev : ∀ᶠ y' in 𝓝 y, 1 < ν * age R y' := continuousAt_const.eventually_lt hcAt hold
    have h0 : (fun y' : Space => χy (ν * age R y') • sepWre ν μ T τ y') =ᶠ[𝓝 y]
        fun _ => (0 : Space) := by
      filter_upwards [hev] with y' hy'
      simp [hχy.zero _ hy'.le]
    exact (differentiableAt_const (0 : Space)).congr_of_eventuallyEq h0
  · have hL : R * Real.sqrt ν ≤ ϱ y :=
      Sub8_1_1_2_3.le_of_age_le hν hR hy (not_lt.1 hold)
    have hlt : R * Real.sqrt (5 * ν / 6) < ϱ y := by
      have h1 : Real.sqrt (5 * ν / 6) < Real.sqrt ν :=
        Real.sqrt_lt_sqrt (by positivity) (by linarith)
      exact lt_of_lt_of_le (mul_lt_mul_of_pos_left h1 hR) hL
    have hr0 : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
    have hP : 0 < 2 * c / R := by positivity
    have hZd : DifferentiableAt ℝ (sepWre ν μ T τ) y :=
      w10_diffV hν hμ hr0 hP hS hM τ hlt
    have hcd : DifferentiableAt ℝ (fun y' : Space => χy (ν * age R y')) y :=
      (w3_cut_hasFDerivAt hχy (Sub8_1_1_2_3.not_axis_of_pos hy)).differentiableAt
    exact hcd.smul hZd

/-- `transField` is differentiable off the axis (`0 < ϱ y`). -/
theorem w113_transField_diffAt {ν μ R c : ℝ} {χy : ℝ → ℝ} (hχy : IsYoungCutoff χy)
    (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4) < μ)
    {g : Chart → Ten3} (hg : IsOldL2 c ν g) (τ : ℝ) {y : Space} (hy : 0 < ϱ y) :
    DifferentiableAt ℝ (transField ν μ R c χy g τ) y := by
  have hχ : IsStreamCutoff χy := ⟨hχy.smooth, hχy.one, hχy.zero, hχy.range⟩
  obtain ⟨hS, hM, hAx⟩ := w10_ctx hν hR hc hg
  set T := oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g with hTdef
  have hP : 0 < 2 * c / R := by positivity
  have hW := w113_W_eq (μ := μ) hν hR hc hg
  have hcut : DifferentiableAt ℝ (wardStreamCut ν R χy (sepWre ν μ T) τ) y :=
    Sub8_1_1_2_3.cutW_diffAt hχ hν hR hμ hP hS hM hAx τ hy
  have hYW : DifferentiableAt ℝ (fun y' => χy (ν * age R y') • sepWre ν μ T τ y') y := by
    have hfun : wardYoungW ν μ R c χy g τ = fun y' => χy (ν * age R y') • sepWre ν μ T τ y' := by
      funext y'; simp only [wardYoungW, hW, hTdef]
    rw [← hfun]
    exact w113_wardYoungW_diffAt hχy hν hR hc hμ hg τ hy
  have hcorr_eq : streamCorr ν R χy (sepWre ν μ T) τ =
      fun y' => wardStreamCut ν R χy (sepWre ν μ T) τ y' -
        χy (ν * age R y') • sepWre ν μ T τ y' := by
    funext y'
    rw [wardStreamCut_eq]
    abel
  have hcorr : DifferentiableAt ℝ (streamCorr ν R χy (sepWre ν μ T) τ) y := by
    rw [hcorr_eq]
    exact hcut.sub hYW
  have hcomm : DifferentiableAt ℝ (sepComm ν μ R χy T τ) y :=
    w113_sepComm_diffAt hχ hν hR hμ hP hS hM hAx τ hy
  have htf : transField ν μ R c χy g τ =
      fun y' => streamCorr ν R χy (sepWre ν μ T) τ y' + sepComm ν μ R χy T τ y' := by
    funext y'
    exact w113_transField_eq hν hR hc hg τ y'
  rw [htf]
  exact hcorr.add hcomm

/-- **`∂_j(χ_yW_μ)` on the young support**. -/
theorem w113_wardDYWYoungL2 (ν μ R c : ℝ) (χy : ℝ → ℝ) (hχy : IsYoungCutoff χy)
    (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4) < μ) :
    ∃ C : ℝ, ∀ g : Chart → Ten3, IsOldL2 c ν g → ∀ j : Fin 3,
      YoungL2Le c ν R C (fun τ => physPd (wardYoungW ν μ R c χy g τ) j) g := by
  classical
  obtain ⟨C0, hC0, h0⟩ := w10_single0 μ hμ ν R c hν hR hc
  obtain ⟨C1, hC1, h1⟩ := w10_single1 μ hμ ν R c hν hR hc
  obtain ⟨Kcut, hKcut, hcut_bd⟩ := w3_cut_deriv_bound R ν hχy hR hν
  refine ⟨C1 + Kcut * C0, fun g hg j => ?_⟩
  obtain ⟨hS, hM, _⟩ := w10_ctx hν hR hc hg
  set T := oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g with hTdef
  have hW := w113_W_eq (μ := μ) hν hR hc hg
  have hrr : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  have hr0 : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hP : 0 < 2 * c / R := by positivity
  set U : Set Space := youngOpen ν R
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_ϱ
  have hYW_meas : Measurable fun x : ℝ × Space => wardYoungW ν μ R c χy g x.1 x.2 := by
    have hWm : Measurable fun x : ℝ × Space => sepWre ν μ T x.1 x.2 :=
      sepWre_measurable ν μ hν T (fun a b => hS.measurable a b)
    have hχm : Measurable fun x : ℝ × Space => χy (ν * age R x.2) := by
      have hage : Measurable fun x : ℝ × Space => ν * age R x.2 := by
        unfold age
        exact measurable_const.mul
          (measurable_const.div ((continuous_ϱ.measurable.comp measurable_snd).pow_const 2))
      exact hχy.smooth.continuous.measurable.comp hage
    have hfun : (fun x : ℝ × Space => wardYoungW ν μ R c χy g x.1 x.2) =
        fun x => χy (ν * age R x.2) • sepWre ν μ T x.1 x.2 := by
      funext x; simp only [wardYoungW, hW, hTdef]
    rw [hfun]
    exact hχm.smul hWm
  have hdYW : ∀ τ y, y ∈ U → DifferentiableAt ℝ (wardYoungW ν μ R c χy g τ) y := by
    intro τ y hy
    have hy0 : 0 < ϱ y := lt_of_le_of_lt hr0 hy
    exact w113_wardYoungW_diffAt hχy hν hR hc hμ hg τ hy0
  have hPd := w10_meas_pd hYW_meas hUo.measurableSet hdYW j
  have hread : wardYoungRead ν R (fun τ => physPd (wardYoungW ν μ R c χy g τ) j) =
      wardYoungRead ν R (fun τ y =>
        if y ∈ U then physPd (wardYoungW ν μ R c χy g τ) j y else 0) := by
    refine w10_read_congr hν hR fun τ y hy => ?_
    have : y ∈ U := lt_of_lt_of_le hrr hy
    simp [this]
  have hFm : AEStronglyMeasurable
      (wardYoungRead ν R (fun τ => physPd (wardYoungW ν μ R c χy g τ) j))
      (ageμ c (-3 / 2)) := by
    rw [hread]
    exact (w10_read_meas hPd).aestronglyMeasurable
  have hA : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (wardYoungRead ν R (fun τ => physPd (sepWre ν μ T τ) j)) C1 :=
    h1 g hg j
  have h0T : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (wardYoungRead ν R (sepWre ν μ T)) C0 := h0 g hg
  have hB : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (wardYoungRead ν R (fun τ y => Kcut • sepWre ν μ T τ y)) (Kcut * C0) := by
    rw [w2_read_smul, abs_of_nonneg hKcut]
    have := h0T.const_mul Kcut
    rwa [abs_of_nonneg hKcut] at this
  refine w10_young_of_sum hFm hA hB hC1 (mul_nonneg hKcut hC0) le_rfl ?_
  refine w10_read_dom hν hR fun τ y hy => ?_
  have hyU : y ∈ U := lt_of_lt_of_le hrr hy
  have hy0 : 0 < ϱ y := lt_of_le_of_lt hr0 hyU
  have hcut_d : HasFDerivAt (fun y' : Space => χy (ν * age R y'))
      (deriv χy (ν * age R y) • (ν • ageD R y)) y :=
    w3_cut_hasFDerivAt hχy (Sub8_1_1_2_3.not_axis_of_pos hy0)
  have hW_d : DifferentiableAt ℝ (sepWre ν μ T τ) y :=
    w10_diffV hν hμ hr0 hP hS hM τ hyU
  have hfun : wardYoungW ν μ R c χy g τ = fun y' => χy (ν * age R y') • sepWre ν μ T τ y' := by
    funext y'; simp only [wardYoungW, hW, hTdef]
  have hpd_eq : physPd (wardYoungW ν μ R c χy g τ) j y =
      χy (ν * age R y) • physPd (sepWre ν μ T τ) j y +
        ((deriv χy (ν * age R y) • (ν • ageD R y)) (coordinateVector j)) • sepWre ν μ T τ y := by
    unfold physPd
    rw [hfun]
    exact congrArg (fun L : Space →L[ℝ] Space => L (coordinateVector j))
      (hcut_d.smul hW_d.hasFDerivAt).fderiv
  rw [hpd_eq]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, Real.norm_eq_abs]
    have hχr := hχy.range (ν * age R y)
    rw [abs_of_nonneg hχr.1]
    exact mul_le_of_le_one_left (norm_nonneg _) hχr.2
  · rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hKcut]
    exact mul_le_mul_of_nonneg_right (hcut_bd y j hy) (norm_nonneg _)

end UnforcedLeray.Short.PartIIIb.Concrete
end
