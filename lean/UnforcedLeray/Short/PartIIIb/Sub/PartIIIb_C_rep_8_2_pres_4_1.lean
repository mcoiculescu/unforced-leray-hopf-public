import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4

/-!
# Measurability of the coefficient-change density (task `PartIII-b:C/rep/8/2/pres/4/1`)

Source `the November 2 reference manuscript`
1217-1222 (`IsExactProfile` smoothness), 5287-5289.  The density is continuous on the open set
`{x.2 ∉ axis}` once `U` and `V` are jointly `C²` there; the ring chart maps `{p.1 > 0}`
continuously into it, and the ring measure lives on `{p.1 > 0}`.
-/

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The (open) set of `(τ, y)` off the axis. -/
def offAxis : Set (ℝ × Space) := {x | x.2 ∉ axis}

theorem isOpen_offAxis : IsOpen offAxis := by
  have h : IsClosed {x : ℝ × Space | x.2 ∈ axis} := by
    have : {x : ℝ × Space | x.2 ∈ axis} = {x | x.2 0 = 0} ∩ {x | x.2 1 = 0} := by
      ext x; simp [axis]
    rw [this]
    refine IsClosed.inter (isClosed_eq ?_ continuous_const) (isClosed_eq ?_ continuous_const)
    · exact (EuclideanSpace.proj (0 : Fin 3)).continuous.comp continuous_snd
    · exact (EuclideanSpace.proj (1 : Fin 3)).continuous.comp continuous_snd
  exact h.isOpen_compl

/-- Slice derivative of a `C¹` map on an open set. -/
private theorem fderiv_slice {O : Set (ℝ × Space)} (hO : IsOpen O) {H : ℝ × Space → Space}
    (hH : ContDiffOn ℝ 1 H O) {τ : ℝ} {y : Space} (hx : (τ, y) ∈ O) (v : Space) :
    fderiv ℝ (fun y' => H (τ, y')) y v = fderiv ℝ H (τ, y) (0, v) := by
  have hd : DifferentiableAt ℝ H (τ, y) :=
    (hH.differentiableOn (by norm_num)).differentiableAt (hO.mem_nhds hx)
  have hc : HasFDerivAt (fun y' : Space => ((τ, y') : ℝ × Space))
      (ContinuousLinearMap.inr ℝ ℝ Space) y :=
    (hasFDerivAt_const τ y).prodMk (hasFDerivAt_id y)
  have := (hd.hasFDerivAt.comp y hc).fderiv
  show fderiv ℝ (H ∘ fun y' : Space => ((τ, y') : ℝ × Space)) y v = _
  rw [this]; rfl

theorem contDiffOn_fderiv_apply {O : Set (ℝ × Space)} (hO : IsOpen O) {F : ℝ × Space → Space}
    (hF : ContDiffOn ℝ 2 F O) (v : Space) :
    ContDiffOn ℝ 1 (fun x => fderiv ℝ F x (0, v)) O := by
  have h1 : ContDiffOn ℝ 1 (fun x => fderiv ℝ F x) O :=
    hF.fderiv_of_isOpen hO (by norm_num)
  exact h1.clm_apply contDiffOn_const

theorem physPd_slice {O : Set (ℝ × Space)} (hO : IsOpen O) {F : ℝ × Space → Space}
    (hF : ContDiffOn ℝ 2 F O) (j : Fin 3) {τ : ℝ} {y : Space} (hx : (τ, y) ∈ O) :
    physPd (fun y' => F (τ, y')) j y = fderiv ℝ F (τ, y) (0, coordinateVector j) := by
  simp only [physPd]
  exact fderiv_slice hO (hF.of_le (by norm_num)) hx _

theorem physPd2_slice {O : Set (ℝ × Space)} (hO : IsOpen O) {F : ℝ × Space → Space}
    (hF : ContDiffOn ℝ 2 F O) (j l : Fin 3) {τ : ℝ} {y : Space} (hx : (τ, y) ∈ O) :
    physPd2 (fun y' => F (τ, y')) j l y =
      fderiv ℝ (fun x => fderiv ℝ F x (0, coordinateVector l)) (τ, y) (0, coordinateVector j) := by
  have hH := contDiffOn_fderiv_apply hO hF (coordinateVector l)
  have hev : (fun y' => physPd (fun y'' => F (τ, y'')) l y') =ᶠ[𝓝 y]
      fun y' => (fun x => fderiv ℝ F x (0, coordinateVector l)) (τ, y') := by
    have hn : {y' : Space | (τ, y') ∈ O} ∈ 𝓝 y :=
      (hO.preimage (continuous_const.prodMk continuous_id)).mem_nhds hx
    filter_upwards [hn] with y' hy'
    exact physPd_slice hO hF l hy'
  have e : physPd2 (fun y' => F (τ, y')) j l y =
      fderiv ℝ (fun y' => physPd (fun y'' => F (τ, y'')) l y') y (coordinateVector j) := rfl
  rw [e, hev.fderiv_eq]
  exact fderiv_slice hO hH hx _

/-- The `C²` jet of a jointly `C²` map is continuous (value, `∂_j`, `∂_j∂_l`). -/
theorem jet_continuousOn {O : Set (ℝ × Space)} (hO : IsOpen O) {F : ℝ × Space → Space}
    (hF : ContDiffOn ℝ 2 F O) :
    ContinuousOn (fun x : ℝ × Space => F x) O ∧
    (∀ j : Fin 3, ContinuousOn
      (fun x : ℝ × Space => physPd (fun y => F (x.1, y)) j x.2) O) ∧
    (∀ j l : Fin 3, ContinuousOn
      (fun x : ℝ × Space => physPd2 (fun y => F (x.1, y)) j l x.2) O) := by
  refine ⟨hF.continuousOn, fun j => ?_, fun j l => ?_⟩
  · exact (contDiffOn_fderiv_apply hO hF (coordinateVector j)).continuousOn.congr
      fun x hx => physPd_slice hO hF j hx
  · have hH := contDiffOn_fderiv_apply hO hF (coordinateVector l)
    have h1 : ContinuousOn (fun x => fderiv ℝ (fun x => fderiv ℝ F x (0, coordinateVector l)) x) O :=
      hH.continuousOn_fderiv_of_isOpen hO le_rfl
    exact (h1.clm_apply continuousOn_const).congr fun x hx => physPd2_slice hO hF j l hx

/-- The first derivative of the slices of a jointly `C¹` map is continuous on `O`. -/
theorem fderiv_slice_continuousOn {O : Set (ℝ × Space)} (hO : IsOpen O) {F : ℝ × Space → Space}
    (hF : ContDiffOn ℝ 2 F O) :
    ContinuousOn (fun x : ℝ × Space => fderiv ℝ (fun y => F (x.1, y)) x.2) O := by
  have h1 : ContinuousOn (fun x => fderiv ℝ F x) O :=
    (hF.fderiv_of_isOpen hO (m := 1) (by norm_num)).continuousOn
  have h2 : ContinuousOn (fun x : ℝ × Space =>
      (fderiv ℝ F x).comp (ContinuousLinearMap.inr ℝ ℝ Space)) O :=
    h1.clm_comp continuousOn_const
  refine h2.congr fun x hx => ?_
  refine ContinuousLinearMap.ext fun v => ?_
  have := fderiv_slice hO (hF.of_le (by norm_num)) (τ := x.1) (y := x.2) hx v
  simpa using this

/-- Continuity of the coefficient-change density on `O` for two jointly `C²` fields. -/
theorem coefChgDens_continuousOn' {O : Set (ℝ × Space)} (hO : IsOpen O) {F G : ℝ × Space → Space}
    (hF : ContDiffOn ℝ 2 F O) (hG : ContDiffOn ℝ 2 G O) :
    ContinuousOn (fun x : ℝ × Space =>
      coefChgDens (fun y => F (x.1, y)) (fun y => G (x.1, y)) x.2) O := by
  obtain ⟨f0, f1, f2⟩ := jet_continuousOn hO hF
  obtain ⟨g0, g1, g2⟩ := jet_continuousOn hO hG
  have e2 : ∀ x : ℝ × Space, secondJet (fun y => F (x.1, y)) x.2 - secondJet (fun y => G (x.1, y)) x.2 =
      jet2 (fun j l => physPd2 (fun y => F (x.1, y)) j l x.2 -
        physPd2 (fun y => G (x.1, y)) j l x.2) := fun x => jet2_sub _ _
  unfold coefChgDens
  refine ContinuousOn.add (ContinuousOn.add ?_ ?_) ?_
  · exact (f0.sub g0).norm
  · exact ((fderiv_slice_continuousOn hO hF).sub (fderiv_slice_continuousOn hO hG)).norm
  · simp only [e2]
    have hj := continuous_jet2.comp_continuousOn
      (continuousOn_pi.2 fun j => continuousOn_pi.2 fun l => (f2 j l).sub (g2 j l))
    exact (continuous_norm (E := Space →L[ℝ] Space →L[ℝ] Space)).comp_continuousOn hj

/-- The ring chart point lives on `{p.1 > 0}` (a.e.). -/
theorem ae_ringPhysμ_pos (R c : ℝ) (hc : 0 < c) : ∀ᵐ p ∂ringPhysμ R c, 0 < p.1 := by
  unfold ringPhysμ
  refine Measure.ae_smul_measure ?_ _
  filter_upwards [ae_ageμ_mem hc (-5 / 2)] with p hp using hp.1

theorem continuousOn_chartMap (R : ℝ) :
    ContinuousOn (fun p : Chart => (NearInst.chartTau R p, NearInst.chartY R p))
      {p : Chart | 0 < p.1} := by
  have hs : ∀ p ∈ {p : Chart | 0 < p.1}, Real.sqrt p.1 ≠ 0 := fun p hp =>
    (Real.sqrt_pos.2 hp).ne'
  refine ContinuousOn.prodMk ?_ ?_
  · unfold NearInst.chartTau
    refine ContinuousOn.add (by fun_prop) ?_
    exact (Real.continuousOn_log.comp continuousOn_fst (fun p hp => (hp.ne' : p.1 ≠ 0)))
  · unfold NearInst.chartY
    refine (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp_continuousOn ?_
    refine continuousOn_pi.2 fun i => ?_
    have hq : ContinuousOn (fun p : Chart => Real.sqrt p.1) {p : Chart | 0 < p.1} :=
      Real.continuous_sqrt.comp_continuousOn continuousOn_fst
    fin_cases i
    · exact continuousOn_const.div hq hs
    · exact continuousOn_const
    · exact (continuous_snd.comp continuous_snd).continuousOn.div hq hs

theorem chartMap_mem_offAxis (R : ℝ) (hR : R ≠ 0) {p : Chart} (hp : 0 < p.1) :
    (NearInst.chartTau R p, NearInst.chartY R p) ∈ offAxis := by
  intro h
  have h0 := h.1
  simp only [NearInst.chartY] at h0
  have : R / Real.sqrt p.1 = 0 := by simpa using h0
  rcases div_eq_zero_iff.1 this with h | h
  · exact hR h
  · exact (Real.sqrt_pos.2 hp).ne' h

/-- The ring read of a density continuous on `offAxis` is a.e. strongly measurable for the ring
measure. -/
theorem aestronglyMeasurable_ringRead {R c : ℝ} (hR : R ≠ 0) (hc : 0 < c) {g : ℝ × Space → ℝ}
    (hg : ContinuousOn g offAxis) :
    AEStronglyMeasurable (ringRead R fun τ y => g (τ, y)) (ringPhysμ R c) := by
  have hcont : ContinuousOn (ringRead R fun τ y => g (τ, y)) {p : Chart | 0 < p.1} :=
    hg.comp (continuousOn_chartMap R) fun p hp => chartMap_mem_offAxis R hR hp
  have hs : MeasurableSet {p : Chart | 0 < p.1} := measurableSet_lt measurable_const measurable_fst
  have h1 := hcont.aestronglyMeasurable (μ := ringPhysμ R c) hs
  have he : (ringPhysμ R c).restrict {p : Chart | 0 < p.1} = ringPhysμ R c :=
    Measure.restrict_eq_self_of_ae_mem (ae_ringPhysμ_pos R c hc)
  rwa [he] at h1

/-- `coefChgMeas`, from the joint `C²` smoothness of `V = U_raw + E_εα` off the axis (the only
missing analytic input, task `PartIII-b:C/rep/8/2/pres/4/1/4`: `rawU_contDiffOn_offAxis_of` and
`IIb.inletContDiff`; `U` is `C^∞` by `IsExactProfile.smoothU`). -/
theorem coefChgMeas_of (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (hV : ∀ᶠ n : ℕ in atTop,
      ContDiffOn ℝ 2 (fun x : ℝ × Space => (D.level n).V x.1 x.2) offAxis) :
    CoefChgMeas D := by
  filter_upwards [hst.actual, hV] with n hn hr
  have hU : ContDiffOn ℝ 2 (fun x : ℝ × Space => (D.level n).U x.1 x.2) offAxis :=
    (hn.profile.smoothU.of_le (by norm_num)).contDiffOn
  have hg := coefChgDens_continuousOn' isOpen_offAxis hU hr
  exact aestronglyMeasurable_ringRead (inv_ne_zero (D.level n).ε_pos.ne')
    (cOf_pos (D.level n).ν_pos) hg

end UnforcedLeray.Short.PartIIIb.Concrete
