import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F7
import UnforcedLeray.Short.PartIIb.Tasks.EarlyBound.LinearBodySource
import UnforcedLeray.Short.PartIIb.Tasks.GlobalEnergy.TailSourceSlice

/-!
# `BodySourceGlue`: Global linear `StronglyMeasurable` body-source upgrade and slice uniqueness

Source of record: `the November 2 reference manuscript` (SP), lines 2213–2239,
2269–2295 (`g = -P_0(v_c · ∇b_0 + b_0 · ∇v_c)`).

In `EarlyBound`, the linear body-source map `gOf_eb` is only controlled in `sLpNorm (13 / 8) p.H`
on `(0, p.H]`; adding a constant `q`-periodic harmonic mode `(1, 0)` supported on `(p.H + 1, ∞)`
would preserve `QPeriodic`, `HasWeakVec`, and `IsBodySource` on `(0, ∞)` while making `sliceH1Norm`
infinite on `(p.H + 1, ∞)`. Here we construct a canonical `ℝ`-linear `StronglyMeasurable`
`QPeriodic` body-source triple `(gOf, gqOf, gηOf)` with finite `sliceH1Norm` a.e. on all `(0, ∞)`
(via `TailSliceP0LiftAux.p0SliceLiftH1_of_loc` and Hamel-basis extension on `HpR p.c`), and prove
via cylinder Biot–Savart uniqueness (`Short.IIIa.CTE.T20_2.biot_re`) that for every `F : HpR p.c`:
1. `(gOf F, gqOf F, gηOf F)` agrees cell-a.e. (and `volume`-a.e. on `(0, p.H) × ℝ²` by periodicity)
   with `EarlyBound`'s `(gOf_eb F, gqOf_eb F, gηOf_eb F)`, transferring both `sLpNorm (13 / 8) p.H`
   and `IsMeridionalCorrectionOn p p.H`;
2. `(gOf F, gqOf F, gηOf F)` agrees cell-a.e. on `(1, ∞)` with `TailSource`'s witness, transferring
   both the `L¹((p.H, ∞); H¹)` and `tailLpNorm (-9 / 8) (max 1 (p.H - 1))` bounds.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIb.ContBodySourceAux

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace
open UnforcedLeray.Short.IIb UnforcedLeray.Short.IIb.LinearBodySourceHelp

/-! ## 1. Planar solenoidal test helpers and Borel `QPeriodic` upgrades -/

private def perpGradTest (φ : Coord → ℝ) : Coord → Fin 2 → ℝ :=
  fun x => ![cpd 2 φ x, -cpd 1 φ x]

private lemma isPlanarSolTest_perpGradTest {φ : Coord → ℝ} (hφ : IsCoordTest φ) :
    IsPlanarSolTest (perpGradTest φ) where
  smooth i := by
    fin_cases i
    · exact planarTest_isCoordTest_partial hφ (cdir 2)
    · exact planarTest_isCoordTest_neg (planarTest_isCoordTest_partial hφ (cdir 1))
  div_free x := planarTest_div_free hφ.smooth x

private lemma isCoordTest_mul_smooth_left {ψ φ : Coord → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hφ : IsCoordTest φ) :
    IsCoordTest (fun x => ψ x * φ x) :=
  ⟨hψ.mul hφ.smooth, hφ.compact.mul_left, tsupport_mul_subset_right.trans hφ.supp⟩

private lemma locInt_of_isBodySource {ν c : ℝ} {tr : B0140.TrainSol ν c}
    {b0 b0q b0η g : CProf} (hg : IsBodySource tr b0 b0q b0η g) (i : Fin 2) :
    LocallyIntegrableOn (fun x => g x i) DriftWeakSHelp.Upos volume := by
  intro x₀ hx₀
  have hx₀' : 0 < x₀.1 := DriftWeakSHelp.mem_Upos.1 hx₀
  let χ := DriftWeakSHelp.mkBump x₀ hx₀'
  have hχ : IsCoordTest χ := DriftWeakSHelp.mkBump_isTest x₀ hx₀'
  let r : ℝ := χ.rIn / 2
  have hr : 0 < r := half_pos χ.rIn_pos
  have hχ_one : ∀ y ∈ Metric.closedBall x₀ r, (χ : Coord → ℝ) =ᶠ[𝓝 y] fun _ => (1 : ℝ) := by
    intro y hy
    have hy_ball : y ∈ Metric.ball x₀ χ.rIn :=
      Metric.mem_ball.2 (lt_of_le_of_lt (Metric.mem_closedBall.1 hy) (half_lt_self χ.rIn_pos))
    filter_upwards [Metric.isOpen_ball.mem_nhds hy_ball] with z hz
    exact χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hz)
  fin_cases i
  · let φ₀ : Coord → ℝ := fun z => (z.2.2 - x₀.2.2) * χ z
    have hφ₀ : IsCoordTest φ₀ :=
      isCoordTest_mul_smooth_left ((contDiff_snd.comp contDiff_snd).sub contDiff_const) hχ
    have hint := (hg.equation (perpGradTest φ₀) (isPlanarSolTest_perpGradTest hφ₀)).1.integrableOn
      (s := Metric.closedBall x₀ r)
    refine ⟨Metric.closedBall x₀ r,
      mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds x₀ hr), ?_⟩
    refine hint.congr_fun (fun y hy => ?_) measurableSet_closedBall
    have hev : φ₀ =ᶠ[𝓝 y] fun z : Coord => z.2.2 - x₀.2.2 := by
      filter_upwards [hχ_one y hy] with z hz
      simp [φ₀, hz]
    have hfd : fderiv ℝ φ₀ y =
        (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) := by
      rw [hev.fderiv_eq]
      exact ((hasFDerivAt_snd.comp y hasFDerivAt_snd).sub_const x₀.2.2).fderiv
    have hc1 : cpd 1 φ₀ y = 0 := by simp [cpd, hfd, cdir]
    have hc2 : cpd 2 φ₀ y = 1 := by simp [cpd, hfd, cdir]
    simp [cdot, perpGradTest, Fin.sum_univ_two, hc1, hc2]
  · let φ₁ : Coord → ℝ := fun z => -(z.2.1 - x₀.2.1) * χ z
    have hφ₁ : IsCoordTest φ₁ :=
      isCoordTest_mul_smooth_left (((contDiff_fst.comp contDiff_snd).sub contDiff_const).neg) hχ
    have hint := (hg.equation (perpGradTest φ₁) (isPlanarSolTest_perpGradTest hφ₁)).1.integrableOn
      (s := Metric.closedBall x₀ r)
    refine ⟨Metric.closedBall x₀ r,
      mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds x₀ hr), ?_⟩
    refine hint.congr_fun (fun y hy => ?_) measurableSet_closedBall
    have hev : φ₁ =ᶠ[𝓝 y] fun z : Coord => -(z.2.1 - x₀.2.1) := by
      filter_upwards [hχ_one y hy] with z hz
      simp [φ₁, hz]
    have hfd : fderiv ℝ φ₁ y =
        -((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) := by
      rw [hev.fderiv_eq]
      exact (((hasFDerivAt_fst.comp y hasFDerivAt_snd).sub_const x₀.2.1).neg).fderiv
    have hc1 : cpd 1 φ₁ y = -1 := by simp [cpd, hfd, cdir]
    have hc2 : cpd 2 φ₁ y = 0 := by simp [cpd, hfd, cdir]
    simp [cdot, perpGradTest, Fin.sum_univ_two, hc1, hc2]

private lemma hasWeakFO_shift {c : ℝ} (w : Fin 3 → ℝ) {u g : Coord → ℂ}
    (h : HasWeakFO (fun _ => w) dZero u g) :
    HasWeakFO (fun _ => w) dZero (fun x => u (qShift c x)) (fun x => g (qShift c x)) := by
  let e : Coord := (0, (c, 0))
  have hqe : qShift c = fun x => x + e := by
    funext x; ext <;> simp [qShift, e]
  have hS : ∀ x : Coord, qShift c x + -e = x := by
    intro x; rw [hqe]; simp
  have hmp : MeasurePreserving (qShift c) (volume : Measure Coord) volume := by
    rw [hqe]; exact measurePreserving_add_right volume e
  have hem : MeasurableEmbedding (qShift c) := by
    rw [hqe]; exact (Homeomorph.addRight e).measurableEmbedding
  have htest : ∀ φ, IsCoordTest φ → IsCoordTest (fun y => φ (y + -e)) := by
    intro φ hφ
    refine ⟨hφ.smooth.comp (contDiff_id.add contDiff_const),
      hφ.compact.comp_homeomorph (Homeomorph.addRight (-e)), ?_⟩
    have hc : IsClosed ((fun y : Coord => y + -e) ⁻¹' tsupport φ) :=
      (isClosed_tsupport φ).preimage (continuous_id.add continuous_const)
    have hsub : tsupport (fun y => φ (y + -e)) ⊆ (fun y : Coord => y + -e) ⁻¹' tsupport φ :=
      closure_minimal (fun y hy => subset_tsupport φ (by simpa [Function.mem_support] using hy)) hc
    intro y hy
    have := hφ.supp (hsub hy)
    simpa [e] using this
  have hTr_const : ∀ (ψ : Coord → ℝ), Differentiable ℝ ψ → ∀ y : Coord,
      coordTranspose (fun _ => w) dZero ψ y = -(∑ j : Fin 3, w j * cpd j ψ y) := by
    intro ψ hψ y
    simp only [coordTranspose, dZero, zero_mul, add_zero]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [cpd]
    rw [fderiv_const_mul (hψ y)]
    simp
  have hTr : ∀ φ, IsCoordTest φ → ∀ y : Coord,
      coordTranspose (fun _ => w) dZero (fun z => φ (z + -e)) y =
        coordTranspose (fun _ => w) dZero φ (y + -e) := by
    intro φ hφ y
    have hd : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
    have hd' : Differentiable ℝ (fun z => φ (z + -e)) := hd.comp (differentiable_id.add_const _)
    rw [hTr_const _ hd', hTr_const _ hd]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [cpd]
    rw [fderiv_comp_add_right]
  refine ⟨fun φ hφ => ⟨?_, ?_⟩, fun φ hφ => ?_⟩
  · have hI : Integrable (fun y => u y * ((coordTranspose (fun _ => w) dZero φ (y + -e) : ℝ) : ℂ)) :=
      (h.1 _ (htest φ hφ)).1.congr (Eventually.of_forall fun y => by simp [hTr φ hφ y])
    exact ((hmp.integrable_comp_emb hem).2 hI).congr
      (Eventually.of_forall fun x => by simp [Function.comp, hS])
  · have hI := (h.1 _ (htest φ hφ)).2
    exact ((hmp.integrable_comp_emb hem).2 hI).congr
      (Eventually.of_forall fun x => by simp [Function.comp, hS])
  · have e1 : ∫ x, g (qShift c x) * (φ x : ℂ) = ∫ y, g y * (φ (y + -e) : ℂ) := by
      simpa [hS] using hmp.integral_comp hem (fun y => g y * (φ (y + -e) : ℂ))
    have e2 : ∫ x, u (qShift c x) * (coordTranspose (fun _ => w) dZero φ x : ℂ) =
        ∫ y, u y * ((coordTranspose (fun _ => w) dZero φ (y + -e) : ℝ) : ℂ) := by
      simpa [hS] using hmp.integral_comp hem
        (fun y => u y * ((coordTranspose (fun _ => w) dZero φ (y + -e) : ℝ) : ℂ))
    rw [e1, e2, h.2 _ (htest φ hφ)]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp [hTr φ hφ y]

lemma qPeriodic_of_hasWeakVec {c : ℝ} (w : Fin 3 → ℝ) {u g : CProf}
    (hu : QPeriodic c u) (hw : HasWeakVec (fun _ => w) dZero u g) :
    QPeriodic c g := by
  have hshift : HasWeakVec (fun _ => w) dZero (fun x => u (qShift c x))
      (fun x => g (qShift c x)) := fun i => hasWeakFO_shift w (hw i)
  have hu_ae : ∀ᵐ x : Coord, 0 < x.1 → u (qShift c x) = u x := QPerHalf.ae_imp hu
  have hw' : HasWeakVec (fun _ => w) dZero (fun x => u (qShift c x)) g :=
    hasWeakVec_congr hu_ae (Eventually.of_forall fun _ _ => rfl) hw
  exact QPerHalf.of_ae_imp (GradBoundHelp.hasWeakVec_unique hshift hw')

lemma isBodySource_congr_g {ν c : ℝ} {tr : B0140.TrainSol ν c}
    {b0 b0q b0η g g' : CProf}
    (hg : ∀ᵐ x : Coord, 0 < x.1 → g' x = g x)
    (h : IsBodySource tr b0 b0q b0η g) :
    IsBodySource tr b0 b0q b0η g' := by
  refine ⟨fun φ hφ => ?_, fun Ψ hΨ => ?_⟩
  · obtain ⟨hI, h0⟩ := h.solenoidal φ hφ
    have hae : (fun x => g' x 0 * (cpd 1 φ x : ℂ) + g' x 1 * (cpd 2 φ x : ℂ)) =ᵐ[volume]
        fun x => g x 0 * (cpd 1 φ x : ℂ) + g x 1 * (cpd 2 φ x : ℂ) := by
      filter_upwards [hg] with x hx
      by_cases hp : 0 < x.1
      · simp [hx hp]
      · have h1 := F10K0Help.isCoordTest_zero_of_nonpos
          (planarTest_isCoordTest_partial hφ (cdir 1)) hp
        have h2 := F10K0Help.isCoordTest_zero_of_nonpos
          (planarTest_isCoordTest_partial hφ (cdir 2)) hp
        change fderiv ℝ φ x (cdir 1) = 0 at h1
        change fderiv ℝ φ x (cdir 2) = 0 at h2
        simp [cpd, h1, h2]
    exact ⟨hI.congr hae.symm, (integral_congr_ae hae).trans h0⟩
  · obtain ⟨hG, hB, hEq⟩ := h.equation Ψ hΨ
    have hae : cdot g' Ψ =ᵐ[volume] cdot g Ψ := by
      filter_upwards [hg] with x hx
      by_cases hp : 0 < x.1
      · simp [cdot, hx hp]
      · have h0 : ∀ i : Fin 2, Ψ x i = 0 :=
          fun i => F10K0Help.isCoordTest_zero_of_nonpos (hΨ.smooth i) hp
        simp [cdot, h0]
    exact ⟨hG.congr hae.symm, hB, (integral_congr_ae hae).trans hEq⟩

private lemma exists_sm_rep_pos {c : ℝ} {u : CProf}
    (hper : QPeriodic c u)
    (hloc : ∀ i : Fin 2, LocallyIntegrableOn (fun x => u x i) DriftWeakSHelp.Upos volume) :
    ∃ u' : CProf, StronglyMeasurable u' ∧ QPeriodic c u' ∧
      (∀ᵐ x : Coord, 0 < x.1 → u' x = u x) := by
  have hmeas_U : MeasurableSet DriftWeakSHelp.Upos := measurableSet_Ioi.prod MeasurableSet.univ
  have haesm_comp : ∀ i : Fin 2,
      AEStronglyMeasurable (DriftWeakSHelp.Upos.indicator (fun x => u x i)) volume :=
    fun i => (aestronglyMeasurable_indicator_iff hmeas_U).2 (hloc i).aestronglyMeasurable
  set u₀ : CProf := fun x => if 0 < x.1 then u x else 0
  have hu₀_eq : u₀ = wbdVec (fun i => DriftWeakSHelp.Upos.indicator (fun x => u x i)) := by
    funext x; ext i
    by_cases hp : 0 < x.1 <;> simp [u₀, wbdVec, hp]
  have hu₀_aesm : AEStronglyMeasurable u₀ volume := by
    rw [hu₀_eq]; exact wbdVec_aesm haesm_comp
  have hu₀_per : QPeriodic c u₀ := by
    refine QPerHalf.of_ae_imp ?_
    filter_upwards [QPerHalf.ae_imp hper] with x hx hp
    simp [u₀, hp, hx hp]
  obtain ⟨u₁, hu₁_sm, hu₁_per, hu₁_ae⟩ := exists_sm_rep_vol hu₀_per hu₀_aesm
  refine ⟨u₁, hu₁_sm, hu₁_per, ?_⟩
  filter_upwards [hu₁_ae] with x hx hp
  simpa [u₀, hp] using hx

lemma upgrade_bodySource_complex {ν c : ℝ} {tr : B0140.TrainSol ν c}
    {b0 b0q b0η g gq gη : CProf}
    (hg_per : QPeriodic c g)
    (hgq : HasWeakVec vQ0 dZero g gq)
    (hgη : HasWeakVec vEta dZero g gη)
    (hg_src : IsBodySource tr b0 b0q b0η g) :
    ∃ g' gq' gη' : CProf,
      StronglyMeasurable g' ∧ StronglyMeasurable gq' ∧ StronglyMeasurable gη' ∧
      QPeriodic c g' ∧ QPeriodic c gq' ∧ QPeriodic c gη' ∧
      HasWeakVec vQ0 dZero g' gq' ∧
      HasWeakVec vEta dZero g' gη' ∧
      IsBodySource tr b0 b0q b0η g' ∧
      (∀ᵐ x : Coord, 0 < x.1 → g' x = g x ∧ gq' x = gq x ∧ gη' x = gη x) ∧
      (∀ᵐ s ∂volume, 0 < s → sliceH1Norm c g' gq' gη' s = sliceH1Norm c g gq gη s) := by
  have hgq_per : QPeriodic c gq := qPeriodic_of_hasWeakVec ![0, 1, 0] hg_per hgq
  have hgη_per : QPeriodic c gη := qPeriodic_of_hasWeakVec ![0, 0, 1] hg_per hgη
  have hg_loc := locInt_of_isBodySource hg_src
  have hgq_loc : ∀ i : Fin 2, LocallyIntegrableOn (fun x => gq x i) DriftWeakSHelp.Upos volume :=
    fun i => DriftWeakSHelp.locInt_of_tests _ (fun φ hφ => ((hgq i).1 φ hφ).2)
  have hgη_loc : ∀ i : Fin 2, LocallyIntegrableOn (fun x => gη x i) DriftWeakSHelp.Upos volume :=
    fun i => DriftWeakSHelp.locInt_of_tests _ (fun φ hφ => ((hgη i).1 φ hφ).2)
  obtain ⟨g', hg'_sm, hg'_per, hg'_ae⟩ := exists_sm_rep_pos hg_per hg_loc
  obtain ⟨gq', hgq'_sm, hgq'_per, hgq'_ae⟩ := exists_sm_rep_pos hgq_per hgq_loc
  obtain ⟨gη', hgη'_sm, hgη'_per, hgη'_ae⟩ := exists_sm_rep_pos hgη_per hgη_loc
  have hgq' : HasWeakVec vQ0 dZero g' gq' :=
    hasWeakVec_congr hg'_ae hgq'_ae hgq
  have hgη' : HasWeakVec vEta dZero g' gη' :=
    hasWeakVec_congr hg'_ae hgη'_ae hgη
  have hg'_src : IsBodySource tr b0 b0q b0η g' := isBodySource_congr_g hg'_ae hg_src
  have hae_all : ∀ᵐ x : Coord, 0 < x.1 → g' x = g x ∧ gq' x = gq x ∧ gη' x = gη x := by
    filter_upwards [hg'_ae, hgq'_ae, hgη'_ae] with x h1 h2 h3 hp
    exact ⟨h1 hp, h2 hp, h3 hp⟩
  have hprod : ∀ᵐ s ∂(volume : Measure ℝ), ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)),
      0 < (s, z).1 → g' (s, z) = g (s, z) ∧ gq' (s, z) = gq (s, z) ∧ gη' (s, z) = gη (s, z) :=
    Measure.ae_ae_of_ae_prod hae_all
  have hsl : ∀ᵐ s ∂volume, 0 < s → sliceH1Norm c g' gq' gη' s = sliceH1Norm c g gq gη s := by
    filter_upwards [hprod] with s hs hp
    exact sliceH1Norm_congr_ae_cell
      (ae_restrict_of_ae (hs.mono fun z hz => (hz hp).1))
      (ae_restrict_of_ae (hs.mono fun z hz => (hz hp).2.1))
      (ae_restrict_of_ae (hs.mono fun z hz => (hz hp).2.2))
  exact ⟨g', gq', gη', hg'_sm, hgq'_sm, hgη'_sm, hg'_per, hgq'_per, hgη'_per,
    hgq', hgη', hg'_src, hae_all, hsl⟩

/-! ## 2. Slice uniqueness of `IsBodySource` on all `s > 0` with finite `sliceH1Norm` -/

private lemma ae_zero_on_Upos_of_tests {f : Coord → ℂ}
    (hloc : LocallyIntegrableOn f DriftWeakSHelp.Upos volume)
    (htest : ∀ φ : Coord → ℝ, IsCoordTest φ → ∫ x, f x * (φ x : ℂ) = 0) :
    ∀ᵐ x : Coord, 0 < x.1 → f x = 0 := by
  have : (volume : Measure Coord).IsAddHaarMeasure := DriftWeakSHelp.instIsAddHaarVolCoord
  have hae := (isOpen_Ioi.prod isOpen_univ).ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc (by
    intro χ hχs hχc hχU
    have hχ := htest χ ⟨hχs, hχc, hχU⟩
    simp only [Complex.real_smul]
    convert hχ using 2
    funext x; ring)
  filter_upwards [hae] with x hx hp
  exact hx (DriftWeakSHelp.mem_Upos.2 hp)

/-- Any two `StronglyMeasurable` `QPeriodic` `IsBodySource` solutions for the same `(b0, b0q, b0η)`
agree cell-a.e. (together with their spatial derivatives) on a.e. slice `s > 0` where both have
finite `sliceH1Norm`. -/
lemma ae_cell_eq_of_isBodySource_pos
    {ν c : ℝ} {tr : B0140.TrainSol ν c} (hc : 0 < c)
    {b0 b0q b0η g₁ gq₁ gη₁ g₂ gq₂ gη₂ : CProf}
    (hg₁_sm : StronglyMeasurable g₁) (hgq₁_sm : StronglyMeasurable gq₁)
    (hgη₁_sm : StronglyMeasurable gη₁)
    (hg₂_sm : StronglyMeasurable g₂) (hgq₂_sm : StronglyMeasurable gq₂)
    (hgη₂_sm : StronglyMeasurable gη₂)
    (hg₁_per : QPeriodic c g₁) (hgq₁_per : QPeriodic c gq₁) (hgη₁_per : QPeriodic c gη₁)
    (hg₂_per : QPeriodic c g₂) (hgq₂_per : QPeriodic c gq₂) (hgη₂_per : QPeriodic c gη₂)
    (hgq₁ : HasWeakVec vQ0 dZero g₁ gq₁) (hgη₁ : HasWeakVec vEta dZero g₁ gη₁)
    (hgq₂ : HasWeakVec vQ0 dZero g₂ gq₂) (hgη₂ : HasWeakVec vEta dZero g₂ gη₂)
    (hsrc₁ : IsBodySource tr b0 b0q b0η g₁) (hsrc₂ : IsBodySource tr b0 b0q b0η g₂) :
    ∀ᵐ s ∂volume, 0 < s →
      sliceH1Norm c g₁ gq₁ gη₁ s < ⊤ →
      sliceH1Norm c g₂ gq₂ gη₂ s < ⊤ →
      (fun z => g₁ (s, z)) =ᵐ[volume.restrict (B0579.cell c)] (fun z => g₂ (s, z)) ∧
      (fun z => gq₁ (s, z)) =ᵐ[volume.restrict (B0579.cell c)] (fun z => gq₂ (s, z)) ∧
      (fun z => gη₁ (s, z)) =ᵐ[volume.restrict (B0579.cell c)] (fun z => gη₂ (s, z)) := by
  let w : CProf := g₁ - g₂
  let wq : CProf := gq₁ - gq₂
  let wη : CProf := gη₁ - gη₂
  have hw_sm : StronglyMeasurable w := hg₁_sm.sub hg₂_sm
  have hwq_sm : StronglyMeasurable wq := hgq₁_sm.sub hgq₂_sm
  have hwη_sm : StronglyMeasurable wη := hgη₁_sm.sub hgη₂_sm
  have hsub_eq : ∀ u₁ u₂ : CProf, u₁ - u₂ = u₁ + (-1 : ℝ) • u₂ := by
    intro u₁ u₂; funext x; ext i; simp [sub_eq_add_neg]
  have hw_per : QPeriodic c w := by
    change QPeriodic c (g₁ - g₂)
    rw [hsub_eq]; exact qPeriodic_add hg₁_per (qPeriodic_smul_real (-1) hg₂_per)
  have hwq_per : QPeriodic c wq := by
    change QPeriodic c (gq₁ - gq₂)
    rw [hsub_eq]; exact qPeriodic_add hgq₁_per (qPeriodic_smul_real (-1) hgq₂_per)
  have hwη_per : QPeriodic c wη := by
    change QPeriodic c (gη₁ - gη₂)
    rw [hsub_eq]; exact qPeriodic_add hgη₁_per (qPeriodic_smul_real (-1) hgη₂_per)
  have hwq : HasWeakVec vQ0 dZero w wq := by
    change HasWeakVec vQ0 dZero (g₁ - g₂) (gq₁ - gq₂)
    rw [hsub_eq g₁ g₂, hsub_eq gq₁ gq₂]
    exact F10Help.hasWeakVec_add' hgq₁ (hasWeakVec_smul_real (-1) hgq₂)
  have hwη : HasWeakVec vEta dZero w wη := by
    change HasWeakVec vEta dZero (g₁ - g₂) (gη₁ - gη₂)
    rw [hsub_eq g₁ g₂, hsub_eq gη₁ gη₂]
    exact F10Help.hasWeakVec_add' hgη₁ (hasWeakVec_smul_real (-1) hgη₂)
  have hdiv_ae : ∀ᵐ x : Coord, 0 < x.1 → wq x 0 + wη x 1 = 0 := by
    have hloc : LocallyIntegrableOn (fun x => wq x 0 + wη x 1) DriftWeakSHelp.Upos volume :=
      (DriftWeakSHelp.locInt_of_tests _ (fun φ hφ => ((hwq 0).1 φ hφ).2)).add
        (DriftWeakSHelp.locInt_of_tests _ (fun φ hφ => ((hwη 1).1 φ hφ).2))
    refine ae_zero_on_Upos_of_tests hloc fun φ hφ => ?_
    have hIq := ((hwq 0).1 φ hφ).2
    have hIη := ((hwη 1).1 φ hφ).2
    have hadd : ∫ x, (wq x 0 + wη x 1) * (φ x : ℂ) =
        (∫ x, wq x 0 * (φ x : ℂ)) + ∫ x, wη x 1 * (φ x : ℂ) := by
      rw [← integral_add hIq hIη]; congr 1; funext x; ring
    rw [hadd, (hwq 0).2 φ hφ, (hwη 1).2 φ hφ]
    have hctQ : (fun x => w x 0 * (coordTranspose vQ0 dZero φ x : ℂ)) =
        fun x => -(w x 0 * (cpd 1 φ x : ℂ)) := by
      funext x; rw [wb_ct_Q]; push_cast; ring
    have hctE : (fun x => w x 1 * (coordTranspose vEta dZero φ x : ℂ)) =
        fun x => -(w x 1 * (cpd 2 φ x : ℂ)) := by
      funext x; rw [wb_ct_E]; push_cast; ring
    rw [hctQ, hctE, integral_neg, integral_neg]
    obtain ⟨hIs1, h01⟩ := hsrc₁.solenoidal φ hφ
    obtain ⟨hIs2, h02⟩ := hsrc₂.solenoidal φ hφ
    have hsol_w : ∫ x, (w x 0 * (cpd 1 φ x : ℂ) + w x 1 * (cpd 2 φ x : ℂ)) = 0 := by
      have heq : (fun x => w x 0 * (cpd 1 φ x : ℂ) + w x 1 * (cpd 2 φ x : ℂ)) =
          fun x => (g₁ x 0 * (cpd 1 φ x : ℂ) + g₁ x 1 * (cpd 2 φ x : ℂ)) -
            (g₂ x 0 * (cpd 1 φ x : ℂ) + g₂ x 1 * (cpd 2 φ x : ℂ)) := by
        funext x; simp only [w, Pi.sub_apply, PiLp.sub_apply]; ring
      rw [heq, integral_sub hIs1 hIs2, h01, h02, sub_self]
    have hIq' : Integrable (fun x => w x 0 * (cpd 1 φ x : ℂ)) := by
      have := ((hwq 0).1 φ hφ).1; rw [hctQ] at this
      exact this.neg.congr (Eventually.of_forall fun x => neg_neg _)
    have hIη' : Integrable (fun x => w x 1 * (cpd 2 φ x : ℂ)) := by
      have := ((hwη 1).1 φ hφ).1; rw [hctE] at this
      exact this.neg.congr (Eventually.of_forall fun x => neg_neg _)
    rw [← neg_add, ← integral_add hIq' hIη', hsol_w, neg_zero]
  have hcurl_ae : ∀ᵐ x : Coord, 0 < x.1 → wq x 1 - wη x 0 = 0 := by
    have hloc : LocallyIntegrableOn (fun x => wq x 1 - wη x 0) DriftWeakSHelp.Upos volume :=
      (DriftWeakSHelp.locInt_of_tests _ (fun φ hφ => ((hwq 1).1 φ hφ).2)).sub
        (DriftWeakSHelp.locInt_of_tests _ (fun φ hφ => ((hwη 0).1 φ hφ).2))
    refine ae_zero_on_Upos_of_tests hloc fun φ hφ => ?_
    have hIq := ((hwq 1).1 φ hφ).2
    have hIη := ((hwη 0).1 φ hφ).2
    have hsub : ∫ x, (wq x 1 - wη x 0) * (φ x : ℂ) =
        (∫ x, wq x 1 * (φ x : ℂ)) - ∫ x, wη x 0 * (φ x : ℂ) := by
      rw [← integral_sub hIq hIη]; congr 1; funext x; ring
    rw [hsub, (hwq 1).2 φ hφ, (hwη 0).2 φ hφ]
    have hctQ : (fun x => w x 1 * (coordTranspose vQ0 dZero φ x : ℂ)) =
        fun x => -(w x 1 * (cpd 1 φ x : ℂ)) := by
      funext x; rw [wb_ct_Q]; push_cast; ring
    have hctE : (fun x => w x 0 * (coordTranspose vEta dZero φ x : ℂ)) =
        fun x => -(w x 0 * (cpd 2 φ x : ℂ)) := by
      funext x; rw [wb_ct_E]; push_cast; ring
    rw [hctQ, hctE, integral_neg, integral_neg]
    let Ψ := perpGradTest φ
    have hΨ := isPlanarSolTest_perpGradTest hφ
    obtain ⟨hIg1, _, heq1⟩ := hsrc₁.equation Ψ hΨ
    obtain ⟨hIg2, _, heq2⟩ := hsrc₂.equation Ψ hΨ
    have heq_w : ∫ x, cdot w Ψ x = 0 := by
      have hfun : cdot w Ψ = fun x => cdot g₁ Ψ x - cdot g₂ Ψ x := by
        funext x; simp only [cdot, w, Pi.sub_apply, PiLp.sub_apply, Fin.sum_univ_two]; ring
      rw [hfun, integral_sub hIg1 hIg2, heq1, heq2, sub_self]
    have hIq' : Integrable (fun x => w x 1 * (cpd 1 φ x : ℂ)) := by
      have := ((hwq 1).1 φ hφ).1; rw [hctQ] at this
      exact this.neg.congr (Eventually.of_forall fun x => neg_neg _)
    have hIη' : Integrable (fun x => w x 0 * (cpd 2 φ x : ℂ)) := by
      have := ((hwη 0).1 φ hφ).1; rw [hctE] at this
      exact this.neg.congr (Eventually.of_forall fun x => neg_neg _)
    have hcomb : -(∫ x, w x 1 * (cpd 1 φ x : ℂ)) - -(∫ x, w x 0 * (cpd 2 φ x : ℂ)) =
        ∫ x, (w x 0 * (cpd 2 φ x : ℂ) - w x 1 * (cpd 1 φ x : ℂ)) := by
      calc -(∫ x, w x 1 * (cpd 1 φ x : ℂ)) - -(∫ x, w x 0 * (cpd 2 φ x : ℂ))
          = (∫ x, w x 0 * (cpd 2 φ x : ℂ)) - ∫ x, w x 1 * (cpd 1 φ x : ℂ) := by ring
        _ = ∫ x, (w x 0 * (cpd 2 φ x : ℂ) - w x 1 * (cpd 1 φ x : ℂ)) :=
            (integral_sub hIη' hIq').symm
    rw [hcomb]
    convert heq_w using 2
    funext x
    simp only [cdot, Ψ, perpGradTest, Fin.sum_univ_two]
    push_cast
    ring
  have hjw0 := FlatBvSliceGoodAeNeeded.jointWeakToSlice_proof c hc 0 w wq
    hw_sm hwq_sm hw_per hwq_per (by simpa using hwq)
  have hjw1 := FlatBvSliceGoodAeNeeded.jointWeakToSlice_proof c hc 1 w wη
    hw_sm hwη_sm hw_per hwη_per (by simpa using hwη)
  have hdiv_sl : ∀ᵐ s ∂(volume : Measure ℝ), ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)),
      0 < (s, z).1 → wq (s, z) 0 + wη (s, z) 1 = 0 :=
    Measure.ae_ae_of_ae_prod hdiv_ae
  have hcurl_sl : ∀ᵐ s ∂(volume : Measure ℝ), ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)),
      0 < (s, z).1 → wq (s, z) 1 - wη (s, z) 0 = 0 :=
    Measure.ae_ae_of_ae_prod hcurl_ae
  have hmem_of_h1 : ∀ (u uq uη : CProf) (s : ℝ),
      StronglyMeasurable u → StronglyMeasurable uq → StronglyMeasurable uη →
      sliceH1Norm c u uq uη s < ⊤ →
      MemLp (fun z => u (s, z)) 2 (volume.restrict (B0579.cell c)) ∧
      MemLp (fun z => uq (s, z)) 2 (volume.restrict (B0579.cell c)) ∧
      MemLp (fun z => uη (s, z)) 2 (volume.restrict (B0579.cell c)) := by
    intro u uq uη s hu huq huη hfin
    unfold sliceH1Norm at hfin
    refine ⟨⟨(hu.comp_measurable measurable_prodMk_left).aestronglyMeasurable,
        lt_of_le_of_lt (le_self_add.trans le_self_add) hfin⟩,
      ⟨(huq.comp_measurable measurable_prodMk_left).aestronglyMeasurable,
        lt_of_le_of_lt (le_add_self.trans le_self_add) hfin⟩,
      ⟨(huη.comp_measurable measurable_prodMk_left).aestronglyMeasurable,
        lt_of_le_of_lt le_add_self hfin⟩⟩
  filter_upwards [hjw0, hjw1, hdiv_sl, hcurl_sl] with s hw0 hw1 hds hcs hs0 hf1 hf2
  obtain ⟨hmg1, hmgq1, hmgη1⟩ := hmem_of_h1 g₁ gq₁ gη₁ s hg₁_sm hgq₁_sm hgη₁_sm hf1
  obtain ⟨hmg2, hmgq2, hmgη2⟩ := hmem_of_h1 g₂ gq₂ gη₂ s hg₂_sm hgq₂_sm hgη₂_sm hf2
  have hmw : MemLp (fun z => w (s, z)) 2 (volume.restrict (B0579.cell c)) := hmg1.sub hmg2
  have hmwq : MemLp (fun z => wq (s, z)) 2 (volume.restrict (B0579.cell c)) := hmgq1.sub hmgq2
  have hmwη : MemLp (fun z => wη (s, z)) 2 (volume.restrict (B0579.cell c)) := hmgη1.sub hmgη2
  have hcd0 := hw0 hs0 hmw hmwq
  have hcd1 := hw1 hs0 hmw hmwη
  have hmw_comp : ∀ j : Fin 2, MemLp (fun z => w (s, z) j) 2 (UnforcedLeray.Cyl.cellμ c) := by
    intro j
    rw [Short.IIIa.CTE.T20_2.cellμ_eq_B0579]
    exact (EuclideanSpace.proj j : CMerid →L[ℂ] ℂ).comp_memLp' hmw
  have hdiv_test : ∀ ψ : ℝ × ℝ → ℝ, UnforcedLeray.Sob.IsCylTest c ψ →
      ∫ z in UnforcedLeray.Cyl.cell c,
        (w (s, z) 0 * (fderiv ℝ ψ z (1, 0) : ℂ) +
          w (s, z) 1 * (fderiv ℝ ψ z (0, 1) : ℂ)) = 0 := by
    intro ψ hψ
    have hψB := Short.IIIa.CTE.T20_2.B0579_of_sob hψ
    rw [← Short.IIIa.CTE.T20_2.cell_eq]
    simp only [← Short.IIIa.CTE.T20_2.pd0_eq, ← Short.IIIa.CTE.T20_2.pd1_eq]
    rw [integral_add ((hcd0 0).1 ψ hψB).1 ((hcd1 1).1 ψ hψB).1,
      (hcd0 0).2 ψ hψB, (hcd1 1).2 ψ hψB, ← neg_add,
      ← integral_add ((hcd0 0).1 ψ hψB).2 ((hcd1 1).1 ψ hψB).2]
    have h0 : ∫ z in B0579.cell c, (wq (s, z) 0 * (ψ z : ℂ) + wη (s, z) 1 * (ψ z : ℂ)) = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [ae_restrict_of_ae hds] with z hz
      calc wq (s, z) 0 * (ψ z : ℂ) + wη (s, z) 1 * (ψ z : ℂ)
          = (wq (s, z) 0 + wη (s, z) 1) * (ψ z : ℂ) := by ring
        _ = 0 := by rw [hz hs0, zero_mul]
    rw [h0, neg_zero]
  have hcurl_test : ∀ ψ : ℝ × ℝ → ℝ, UnforcedLeray.Sob.IsCylTest c ψ →
      ∫ z in UnforcedLeray.Cyl.cell c,
        (w (s, z) 0 * (fderiv ℝ ψ z (0, 1) : ℂ) -
          w (s, z) 1 * (fderiv ℝ ψ z (1, 0) : ℂ)) = 0 := by
    intro ψ hψ
    have hψB := Short.IIIa.CTE.T20_2.B0579_of_sob hψ
    rw [← Short.IIIa.CTE.T20_2.cell_eq]
    simp only [← Short.IIIa.CTE.T20_2.pd0_eq, ← Short.IIIa.CTE.T20_2.pd1_eq]
    rw [integral_sub ((hcd1 0).1 ψ hψB).1 ((hcd0 1).1 ψ hψB).1,
      (hcd1 0).2 ψ hψB, (hcd0 1).2 ψ hψB]
    have hcomb : -(∫ z in B0579.cell c, wη (s, z) 0 * (ψ z : ℂ)) -
        -(∫ z in B0579.cell c, wq (s, z) 1 * (ψ z : ℂ)) =
        ∫ z in B0579.cell c, (wq (s, z) 1 * (ψ z : ℂ) - wη (s, z) 0 * (ψ z : ℂ)) := by
      calc -(∫ z in B0579.cell c, wη (s, z) 0 * (ψ z : ℂ)) -
            -(∫ z in B0579.cell c, wq (s, z) 1 * (ψ z : ℂ))
          = (∫ z in B0579.cell c, wq (s, z) 1 * (ψ z : ℂ)) -
            ∫ z in B0579.cell c, wη (s, z) 0 * (ψ z : ℂ) := by ring
        _ = ∫ z in B0579.cell c, (wq (s, z) 1 * (ψ z : ℂ) - wη (s, z) 0 * (ψ z : ℂ)) :=
            (integral_sub ((hcd0 1).1 ψ hψB).2 ((hcd1 0).1 ψ hψB).2).symm
    rw [hcomb]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [ae_restrict_of_ae hcs] with z hz
    calc wq (s, z) 1 * (ψ z : ℂ) - wη (s, z) 0 * (ψ z : ℂ)
        = (wq (s, z) 1 - wη (s, z) 0) * (ψ z : ℂ) := by ring
      _ = 0 := by rw [hz hs0, zero_mul]
  have hw_zero := Short.IIIa.CTE.T20_2.biot_re hc (fun z j => w (s, z) j) hmw_comp
    hdiv_test hcurl_test
  rw [Short.IIIa.CTE.T20_2.cellμ_eq_B0579] at hw_zero
  have hw_comp_zero : ∀ j : Fin 2,
      (fun z => w (s, z) j) =ᵐ[volume.restrict (B0579.cell c)] 0 := by
    intro j
    filter_upwards [hw_zero] with z hz
    exact congrFun hz j
  have hwq_comp_zero : ∀ j : Fin 2,
      (fun z => wq (s, z) j) =ᵐ[volume.restrict (B0579.cell c)] 0 :=
    fun j => hasWeakCellDerivC_ae_zero_of_ae_zero hc (hw_comp_zero j)
      ((EuclideanSpace.proj j : CMerid →L[ℂ] ℂ).comp_memLp' hmwq) (hcd0 j)
  have hwη_comp_zero : ∀ j : Fin 2,
      (fun z => wη (s, z) j) =ᵐ[volume.restrict (B0579.cell c)] 0 :=
    fun j => hasWeakCellDerivC_ae_zero_of_ae_zero hc (hw_comp_zero j)
      ((EuclideanSpace.proj j : CMerid →L[ℂ] ℂ).comp_memLp' hmwη) (hcd1 j)
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hw_comp_zero 0, hw_comp_zero 1] with z h0 h1
    ext j; fin_cases j
    · exact sub_eq_zero.mp h0
    · exact sub_eq_zero.mp h1
  · filter_upwards [hwq_comp_zero 0, hwq_comp_zero 1] with z h0 h1
    ext j; fin_cases j
    · exact sub_eq_zero.mp h0
    · exact sub_eq_zero.mp h1
  · filter_upwards [hwη_comp_zero 0, hwη_comp_zero 1] with z h0 h1
    ext j; fin_cases j
    · exact sub_eq_zero.mp h0
    · exact sub_eq_zero.mp h1

/-! ## 3. Lifting cell-a.e. slice equality to `volume`-a.e. equality and `IsMeridionalCorrectionOn` -/

private lemma cell_eq_qCell (c : ℝ) : B0579.cell c = Axi.qCell c := by
  unfold B0579.cell Axi.qCell
  rw [neg_div]

/-- Two `StronglyMeasurable`, `QPeriodic c` profiles that agree cell-a.e. on a.e. slice
`s ∈ Ioo 0 T` agree `volume`-a.e. on `Ioo 0 T ×ˢ univ`. -/
lemma ae_vol_eq_of_ae_cell_periodic {c T : ℝ} (hc : 0 < c) {u₁ u₂ : CProf}
    (hsm₁ : StronglyMeasurable u₁) (hsm₂ : StronglyMeasurable u₂)
    (hper₁ : QPeriodic c u₁) (hper₂ : QPeriodic c u₂)
    (hcell : ∀ᵐ s ∂volume, s ∈ Ioo 0 T →
      (fun z => u₁ (s, z)) =ᵐ[volume.restrict (B0579.cell c)] (fun z => u₂ (s, z))) :
    ∀ᵐ x : Coord, x.1 ∈ Ioo 0 T → u₁ x = u₂ x := by
  let S : Set Coord := {x : Coord | x.1 ∈ Ioo 0 T ∧ u₁ x ≠ u₂ x}
  have hS_meas : MeasurableSet S :=
    (measurableSet_Ioo.preimage measurable_fst).inter (hsm₁.measurableSet_eq_fun hsm₂).compl
  have hcell_null : volume (S ∩ (Ioi (0 : ℝ) ×ˢ B0579.cell c)) = 0 := by
    have hM : MeasurableSet (S ∩ (Ioi (0 : ℝ) ×ˢ B0579.cell c)) :=
      hS_meas.inter (measurableSet_Ioi.prod (B0579.measurableSet_cell c))
    rw [← lintegral_indicator_one hM, Measure.volume_eq_prod, lintegral_prod]
    · refine lintegral_eq_zero_of_ae_eq_zero ?_
      filter_upwards [hcell] with s hs
      by_cases hsT : s ∈ Ioo 0 T
      · have h0 : ∀ᵐ z ∂volume,
            (S ∩ (Ioi (0 : ℝ) ×ˢ B0579.cell c)).indicator (1 : Coord → ℝ≥0∞) (s, z) = 0 := by
          have hc_ae := (ae_restrict_iff' (B0579.measurableSet_cell c)).1 (hs hsT)
          filter_upwards [hc_ae] with z hz
          by_cases hzc : z ∈ B0579.cell c
          · have hnot : (s, z) ∉ S ∩ (Ioi (0 : ℝ) ×ˢ B0579.cell c) := fun h => h.1.2 (hz hzc)
            simp [hnot]
          · have hnot : (s, z) ∉ S ∩ (Ioi (0 : ℝ) ×ˢ B0579.cell c) := fun h => hzc h.2.2
            simp [hnot]
        exact lintegral_eq_zero_of_ae_eq_zero h0
      · have h0 : ∀ z, (S ∩ (Ioi (0 : ℝ) ×ˢ B0579.cell c)).indicator (1 : Coord → ℝ≥0∞) (s, z) = 0 :=
          fun z => Set.indicator_of_notMem (fun h => hsT h.1.1) _
        simp [h0]
    · exact (measurable_one.indicator hM).aemeasurable
  rw [cell_eq_qCell] at hcell_null
  have hper : ∀ᵐ x : Coord, 0 < x.1 → ∀ k : ℤ,
      u₁ (CongrHelp.T c k x) = u₁ x ∧ u₂ (CongrHelp.T c k x) = u₂ x := by
    have := ae_all_iff.2 fun k : ℤ => (CongrHelp.ae_T hper₁ k).and (CongrHelp.ae_T hper₂ k)
    filter_upwards [this] with x hx hpos k using ⟨(hx k).1 hpos, (hx k).2 hpos⟩
  have hnull : ∀ k : ℤ,
      volume (CongrHelp.T c (-k) ⁻¹' (S ∩ (Ioi (0 : ℝ) ×ˢ Axi.qCell c))) = 0 :=
    fun k => (CongrHelp.mp_T c (-k)).quasiMeasurePreserving.preimage_null hcell_null
  have hbad := measure_eq_zero_iff_ae_notMem.1 (measure_iUnion_null hnull)
  filter_upwards [hper, hbad] with x hx hxb hxT
  replace hx := hx hxT.1
  by_contra hne
  set k : ℤ := ⌊(x.2.1 + c / 2) / c⌋
  apply hxb
  refine Set.mem_iUnion.2 ⟨k, ?_⟩
  have hk1' : (k : ℝ) * c ≤ x.2.1 + c / 2 :=
    (le_div_iff₀ hc).1 (Int.floor_le _)
  have hk2' : x.2.1 + c / 2 < ((k : ℝ) + 1) * c :=
    (div_lt_iff₀ hc).1 (Int.lt_floor_add_one _)
  obtain ⟨e1, e2⟩ := hx (-k)
  refine ⟨⟨?_, ?_⟩, ?_, ?_, trivial⟩
  · simpa [CongrHelp.T] using hxT
  · intro hy; apply hne; rw [← e1, ← e2]; exact hy
  · simpa [CongrHelp.T] using hxT.1
  · simp only [CongrHelp.T, Prod.fst_add, Prod.snd_add]
    constructor <;> push_cast <;> linarith

/-- `IsMeridionalCorrectionOn p T` transfers along `volume`-a.e. equality of `g` on `(0, T) × ℝ²`. -/
lemma isMeridionalCorrectionOn_congr_g {p : Params} {T : ℝ} {g g' z zq zη : CProf} {α : E2}
    (hgg' : ∀ᵐ x : Coord, x.1 ∈ Ioo 0 T → g' x = g x)
    (h : IsMeridionalCorrectionOn p T g z zq zη α) :
    IsMeridionalCorrectionOn p T g' z zq zη α where
  periodic := h.periodic
  weak_q := h.weak_q
  weak_eta := h.weak_eta
  solenoidal := h.solenoidal
  equation Ψ hΨ hsupp := by
    obtain ⟨hIz, hIB, hIg, hEq⟩ := h.equation Ψ hΨ hsupp
    have hae : cdot g' Ψ =ᵐ[volume] cdot g Ψ := by
      filter_upwards [hgg'] with x hx
      by_cases hxT : x.1 ∈ Ioo 0 T
      · simp [cdot, hx hxT]
      · have h0 : ∀ i : Fin 2, Ψ x i = 0 := fun i =>
          image_eq_zero_of_notMem_tsupport (f := fun y => Ψ y i) (fun hm => hxT (hsupp i hm).1)
        simp [cdot, h0]
    exact ⟨hIz, hIB, hIg.congr hae.symm, hEq.trans (integral_congr_ae hae.symm)⟩
  initial_curl := h.initial_curl

/-! ## 4. Local-to-global a.e. finiteness and `sLpNorm` / `tailLpNorm` congruence -/

private lemma ae_pos_lt_top_of_loc_Icc {f : ℝ → ℝ≥0∞} (hf : Measurable f)
    (hloc : ∀ a b : ℝ, 0 < a → ∫⁻ s in Icc a b, f s < ⊤) :
    ∀ᵐ s ∂volume, 0 < s → f s < ⊤ := by
  have hn : ∀ n : ℕ, ∀ᵐ s ∂volume, s ∈ Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) → f s < ⊤ := by
    intro n
    rw [← ae_restrict_iff' measurableSet_Icc]
    exact ae_lt_top hf (hloc _ _ (by positivity)).ne
  filter_upwards [ae_all_iff.2 hn] with s hs hpos
  let n : ℕ := Nat.ceil (max s⁻¹ s)
  have hmax : max s⁻¹ s ≤ (n : ℝ) + 1 :=
    (Nat.le_ceil _).trans (by linarith)
  have hs_le : s ≤ (n : ℝ) + 1 := (le_max_right _ _).trans hmax
  have hinv_le : s⁻¹ ≤ (n : ℝ) + 1 := (le_max_left _ _).trans hmax
  have hle_s : 1 / ((n : ℝ) + 1) ≤ s := by
    rw [one_div]
    exact (inv_le_comm₀ (by positivity) hpos).2 hinv_le
  exact hs n ⟨hle_s, hs_le⟩

private lemma sliceH1Norm_add_le (c : ℝ) {g₁ gq₁ gη₁ g₂ gq₂ gη₂ : CProf}
    (hg₁ : StronglyMeasurable g₁) (hgq₁ : StronglyMeasurable gq₁) (hgη₁ : StronglyMeasurable gη₁)
    (hg₂ : StronglyMeasurable g₂) (hgq₂ : StronglyMeasurable gq₂) (hgη₂ : StronglyMeasurable gη₂)
    (s : ℝ) :
    sliceH1Norm c (g₁ + g₂) (gq₁ + gq₂) (gη₁ + gη₂) s ≤
      sliceH1Norm c g₁ gq₁ gη₁ s + sliceH1Norm c g₂ gq₂ gη₂ s := by
  have hsm : Measurable (fun z : B0579.Plane => (s, z)) :=
    measurable_const.prodMk measurable_id
  have h0 := eLpNorm_add_le (μ := volume.restrict (B0579.cell c)) (p := 2)
    (hg₁.comp_measurable hsm).aestronglyMeasurable
    (hg₂.comp_measurable hsm).aestronglyMeasurable (by norm_num)
  have h1 := eLpNorm_add_le (μ := volume.restrict (B0579.cell c)) (p := 2)
    (hgq₁.comp_measurable hsm).aestronglyMeasurable
    (hgq₂.comp_measurable hsm).aestronglyMeasurable (by norm_num)
  have h2 := eLpNorm_add_le (μ := volume.restrict (B0579.cell c)) (p := 2)
    (hgη₁.comp_measurable hsm).aestronglyMeasurable
    (hgη₂.comp_measurable hsm).aestronglyMeasurable (by norm_num)
  unfold sliceH1Norm
  exact (add_le_add (add_le_add h0 h1) h2).trans_eq (by ac_rfl)

private lemma sliceH1Norm_smul_le (c : ℝ) (a : ℝ) (g gq gη : CProf) (s : ℝ) :
    sliceH1Norm c (a • g) (a • gq) (a • gη) s ≤
      ‖a‖ₑ * sliceH1Norm c g gq gη s := by
  unfold sliceH1Norm
  rw [mul_add, mul_add]
  gcongr <;> exact eLpNorm_const_smul_le

private lemma sLpNorm_congr_ae_Ioc {b T : ℝ} {f g : ℝ → ℝ≥0∞}
    (h : ∀ᵐ s ∂volume, s ∈ Ioc 0 T → f s = g s) :
    sLpNorm b T f = sLpNorm b T g := by
  have hac : sMeas b ≪ volume :=
    (withDensity_absolutelyContinuous _ _).trans
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  have hs : ∀ᵐ s ∂(sMeas b).restrict (Ioc 0 T), f s ^ bgp = g s ^ bgp := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hac.ae_le h] with s hs hm
    rw [hs hm]
  unfold sLpNorm
  rw [lintegral_congr_ae hs]

private lemma tailLpNorm_congr_ae_Ioi {b T : ℝ} {f g : ℝ → ℝ≥0∞}
    (h : ∀ᵐ s ∂volume, T < s → f s = g s) :
    tailLpNorm b T f = tailLpNorm b T g := by
  have hac : sMeas b ≪ volume :=
    (withDensity_absolutelyContinuous _ _).trans
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  have hs : ∀ᵐ s ∂(sMeas b).restrict (Ioi T), f s ^ bgp = g s ^ bgp := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards [hac.ae_le h] with s hs hm
    rw [hs hm]
  unfold tailLpNorm
  rw [lintegral_congr_ae hs]

/-! ## 5. Main theorem: global `ℝ`-linear `StronglyMeasurable` body-source upgrade -/

/-- Given `hTS : TailSource` and `dm > 0`, there are `C_ts > 0`, `k_ts : ℕ`, `ν_bs > 0` such that
at any `BgRegime` parameter point with `p.ν ≤ ν_bs`, `p.ν ≤ 1`, `p.ageCut = Sig` (`Sig > 0`), and
`1 ≤ p.H`, any `EarlyBound` witness `(αMap, b0Of, b0qOf, b0ηOf, gOf_eb, gqOf_eb, gηOf_eb, zOf_eb, zqOf_eb, zηOf_eb)`
can have `(gOf_eb, gqOf_eb, gηOf_eb)` replaced by `ℝ`-linear `StronglyMeasurable` `QPeriodic` maps
`(gOf, gqOf, gηOf)` that preserve `IsBodySource`, `IsMeridionalCorrectionOn p p.H`, and the early
`sLpNorm (13 / 8) p.H` bound, while simultaneously obeying the late `L¹((p.H, ∞); H¹)` and
`tailLpNorm (-9 / 8) (max 1 (p.H - 1))` bounds from `TailSource`. -/
theorem global_linear_bodySource_upgrade
    (hTS : TailSource)
    {dm dp : ℝ} (hdm : 0 < dm) :
    ∃ (C_ts : ℝ) (k_ts : ℕ) (ν_bs : ℝ), 0 < C_ts ∧ 0 < ν_bs ∧
      ∀ {Sig C_eb : ℝ} {k_eb : ℕ} (p : Params) (d : ℝ),
        0 < Sig → 0 < C_eb →
        BgRegime p d dm dp → p.ν ≤ ν_bs → p.ν ≤ 1 → p.ageCut = Sig → 1 ≤ p.H →
        ∀ (αMap : HpR p.c →L[ℝ] E2)
          (b0Of b0qOf b0ηOf gOf_eb gqOf_eb gηOf_eb zOf_eb zqOf_eb zηOf_eb : HpR p.c →ₗ[ℝ] CProf),
          (∀ F : HpR p.c,
            InFlatClass p.c bgp (b0Of F) ∧
            IsFlatResponse p.ν 0 (toProf p.c F) (b0Of F) ∧
            HasWeakVec vQ0 dZero (b0Of F) (b0qOf F) ∧
            HasWeakVec vEta dZero (b0Of F) (b0ηOf F) ∧
            QPeriodic p.c (gOf_eb F) ∧
            HasWeakVec vQ0 dZero (gOf_eb F) (gqOf_eb F) ∧
            HasWeakVec vEta dZero (gOf_eb F) (gηOf_eb F) ∧
            IsBodySource p.train (b0Of F) (b0qOf F) (b0ηOf F) (gOf_eb F) ∧
            IsMeridionalCorrectionOn p p.H (gOf_eb F)
              (zOf_eb F) (zqOf_eb F) (zηOf_eb F) (αMap F) ∧
            Measurable (sliceH1Norm p.c (gOf_eb F) (gqOf_eb F) (gηOf_eb F)) ∧
            sLpNorm (13 / 8) p.H (sliceH1Norm p.c (gOf_eb F) (gqOf_eb F) (gηOf_eb F)) ≤
              ENNReal.ofReal (C_eb * (p.ν ^ k_eb)⁻¹ * ‖F‖)) →
          ∃ (gOf gqOf gηOf : HpR p.c →ₗ[ℝ] CProf),
            ∀ F : HpR p.c,
              StronglyMeasurable (gOf F) ∧
              StronglyMeasurable (gqOf F) ∧
              StronglyMeasurable (gηOf F) ∧
              QPeriodic p.c (gOf F) ∧
              QPeriodic p.c (gqOf F) ∧
              QPeriodic p.c (gηOf F) ∧
              HasWeakVec vQ0 dZero (gOf F) (gqOf F) ∧
              HasWeakVec vEta dZero (gOf F) (gηOf F) ∧
              IsBodySource p.train (b0Of F) (b0qOf F) (b0ηOf F) (gOf F) ∧
              IsMeridionalCorrectionOn p p.H (gOf F)
                (zOf_eb F) (zqOf_eb F) (zηOf_eb F) (αMap F) ∧
              Measurable (sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F)) ∧
              sLpNorm (13 / 8) p.H (sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F)) ≤
                ENNReal.ofReal (C_eb * (p.ν ^ k_eb)⁻¹ * ‖F‖) ∧
              (∫⁻ s in Ioc 0 p.H, sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F) s) < ⊤ ∧
              (∫⁻ s in Ioi p.H, sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F) s) ≤
                ENNReal.ofReal (C_ts * (p.ν ^ k_ts)⁻¹ * ‖F‖) ∧
              tailLpNorm (-9 / 8) (max 1 (p.H - 1))
                  (sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F)) ≤
                ENNReal.ofReal (C_ts * (p.ν ^ k_ts)⁻¹ * ‖F‖) := by
  obtain ⟨_, _, hFG⟩ := flatGraphD2Slice_proof
  obtain ⟨ν_loc, hν_loc, hTr_loc⟩ :=
    trainWeightedLp22over3Loc_proof 9 (by norm_num : (8 : ℝ) < 9) dm dp hdm
  obtain ⟨C_ts, k_ts, ν_ts, hC_ts, hν_ts, hTS_p⟩ := hTS dm dp hdm
  refine ⟨C_ts, k_ts, min ν_loc ν_ts, hC_ts, lt_min hν_loc hν_ts, ?_⟩
  intro Sig C_eb k_eb p d hSig hC_eb hreg hν_bs hν1 hAge hH1
    αMap b0Of b0qOf b0ηOf gOf_eb gqOf_eb gηOf_eb zOf_eb zqOf_eb zηOf_eb hEB_F
  have hν_pos : 0 < p.ν := p.ν_pos
  have hc_pos : 0 < p.c := p.c_pos
  have hH_pos : 0 < p.H := zero_lt_one.trans_le hH1
  have hH_eq : p.H = Sig / p.ν := by rw [Params.H, hAge]
  have hν_loc_le : p.ν ≤ ν_loc := hν_bs.trans (min_le_left _ _)
  have hν_ts_le : p.ν ≤ ν_ts := hν_bs.trans (min_le_right _ _)
  -- Step 1: Pointwise canonical P_0 slice lift for every F : HpR p.c with finite sliceH1Norm a.e. on (0, ∞)
  have h_pt : ∀ F : HpR p.c, ∃ g gq gη : CProf,
      StronglyMeasurable g ∧ StronglyMeasurable gq ∧ StronglyMeasurable gη ∧
      QPeriodic p.c g ∧ QPeriodic p.c gq ∧ QPeriodic p.c gη ∧
      HasWeakVec vQ0 dZero g gq ∧ HasWeakVec vEta dZero g gη ∧
      IsBodySource p.train (b0Of F) (b0qOf F) (b0ηOf F) g ∧
      (∀ᵐ s ∂volume, 0 < s → sliceH1Norm p.c g gq gη s < ⊤) := by
    intro F
    obtain ⟨hb0_cls, hb0_resp, hb0q, hb0η, _⟩ := hEB_F F
    have hF_inHr : InHr p.c bgp (toProf p.c F) := inHr_toProf hc_pos F
    obtain ⟨b0', b0q₀, b0η₀, D2, hb0'_ae, hb0'_hr, hbq₀_hr, hbη₀_hr, hD2_hr,
        hsm_b0', hsm_bq₀, hsm_bη₀, hsm_D2, hw_q₀, hw_η₀, hw_00, hw_01, hw_10, hw_11, _⟩ :=
      hFG p.ν p.c p.H hν_pos hc_pos hH_pos (toProf p.c F) (b0Of F) hF_inHr hb0_cls hb0_resp
    obtain ⟨hwU_q, hwU_η⟩ :=
      flatBvWeakLeibniz_proof p.train hc_pos (b0Of F) b0' b0q₀ b0η₀ D2 hb0_cls hb0'_ae
        hb0'_hr hbq₀_hr hbη₀_hr hD2_hr hsm_b0' hsm_bq₀ hsm_bη₀ hsm_D2
        hw_q₀ hw_η₀ hw_00 hw_01 hw_10 hw_11
    have hLoc :=
      TailSliceAssemblyAux.loc_lintegral_sliceH1Norm_lt_top p.train hc_pos b0' b0q₀ b0η₀ D2
        hb0'_hr hbq₀_hr hbη₀_hr hD2_hr hsm_b0' hsm_bq₀ hsm_bη₀ hsm_D2
        (hTr_loc p d hreg hν_loc_le)
    obtain ⟨g, gq, gη, hsm_g, hsm_gq, hsm_gη, hg_per, hgwq, hgwη, hg_src', hH1_le⟩ :=
      TailSliceP0LiftAux.p0SliceLiftH1_of_loc p.train hc_pos b0' b0q₀ b0η₀ D2
        hb0'_hr hbq₀_hr hbη₀_hr hD2_hr hsm_b0' hsm_bq₀ hsm_bη₀ hsm_D2 hwU_q hwU_η hLoc
    have hgq_per : QPeriodic p.c gq := qPeriodic_of_hasWeakVec ![0, 1, 0] hg_per hgwq
    have hgη_per : QPeriodic p.c gη := qPeriodic_of_hasWeakVec ![0, 0, 1] hg_per hgwη
    have hg_src₀ : IsBodySource p.train (b0Of F) b0q₀ b0η₀ g :=
      isBodySource_congr_b0 hb0'_ae hg_src'
    have hg_src : IsBodySource p.train (b0Of F) (b0qOf F) (b0ηOf F) g :=
      isBodySource_congr_deriv
        (GradBoundHelp.hasWeakVec_unique hw_q₀ hb0q)
        (GradBoundHelp.hasWeakVec_unique hw_η₀ hb0η)
        hg_src₀
    have hm_g : Measurable (sliceH1Norm p.c g gq gη) :=
      CylProjectionSub.measurable_sliceH1Norm_cp p.c hsm_g hsm_gq hsm_gη
    have hLoc_g : ∀ a b : ℝ, 0 < a → ∫⁻ s in Icc a b, sliceH1Norm p.c g gq gη s < ⊤ := by
      intro a b ha
      have hmono : ∀ᵐ s ∂volume.restrict (Icc a b),
          sliceH1Norm p.c g gq gη s ≤
            ENNReal.ofReal 2 * sliceH1Norm p.c (flatBv p.train b0' b0q₀ b0η₀)
              (flatBvQ p.train b0' b0q₀ b0η₀ (D2 0 0) (D2 1 0))
              (flatBvEta p.train b0' b0q₀ b0η₀ (D2 0 1) (D2 1 1)) s := by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
        exact hH1_le s (ha.trans_le hs.1)
      refine lt_of_le_of_lt (lintegral_mono_ae hmono) ?_
      rw [lintegral_const_mul' (ENNReal.ofReal 2) _ ENNReal.ofReal_ne_top]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hLoc a b ha)
    exact ⟨g, gq, gη, hsm_g, hsm_gq, hsm_gη, hg_per, hgq_per, hgη_per,
      hgwq, hgwη, hg_src, ae_pos_lt_top_of_loc_Icc hm_g hLoc_g⟩
  -- Step 2: Hamel-basis ℝ-linear extension over HpR p.c
  let B := Module.Basis.ofVectorSpace ℝ (HpR p.c)
  choose g_bas gq_bas gη_bas h_bas using fun i => h_pt (B i)
  let gOf : HpR p.c →ₗ[ℝ] CProf := B.constr ℝ g_bas
  let gqOf : HpR p.c →ₗ[ℝ] CProf := B.constr ℝ gq_bas
  let gηOf : HpR p.c →ₗ[ℝ] CProf := B.constr ℝ gη_bas
  have h_lin : ∀ F : HpR p.c,
      StronglyMeasurable (gOf F) ∧ StronglyMeasurable (gqOf F) ∧ StronglyMeasurable (gηOf F) ∧
      QPeriodic p.c (gOf F) ∧ QPeriodic p.c (gqOf F) ∧ QPeriodic p.c (gηOf F) ∧
      HasWeakVec vQ0 dZero (gOf F) (gqOf F) ∧ HasWeakVec vEta dZero (gOf F) (gηOf F) ∧
      IsBodySource p.train (b0Of F) (b0qOf F) (b0ηOf F) (gOf F) ∧
      (∀ᵐ s ∂volume, 0 < s → sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F) s < ⊤) := by
    let S : Submodule ℝ (HpR p.c) :=
      { carrier := {F |
          StronglyMeasurable (gOf F) ∧ StronglyMeasurable (gqOf F) ∧ StronglyMeasurable (gηOf F) ∧
          QPeriodic p.c (gOf F) ∧ QPeriodic p.c (gqOf F) ∧ QPeriodic p.c (gηOf F) ∧
          HasWeakVec vQ0 dZero (gOf F) (gqOf F) ∧ HasWeakVec vEta dZero (gOf F) (gηOf F) ∧
          IsBodySource p.train (b0Of F) (b0qOf F) (b0ηOf F) (gOf F) ∧
          (∀ᵐ s ∂volume, 0 < s → sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F) s < ⊤)}
        zero_mem' := by
          change StronglyMeasurable (gOf 0) ∧ _
          simp only [map_zero]
          exact ⟨stronglyMeasurable_zero, stronglyMeasurable_zero, stronglyMeasurable_zero,
            qPeriodic_zero p.c, qPeriodic_zero p.c, qPeriodic_zero p.c,
            hasWeakVec_zero vQ0 dZero, hasWeakVec_zero vEta dZero,
            isBodySource_zero p.train,
            Eventually.of_forall fun s _ => by simp [sliceH1Norm]⟩
        add_mem' := by
          intro F₁ F₂ h₁ h₂
          change StronglyMeasurable (gOf (F₁ + F₂)) ∧ _
          simp only [map_add]
          rcases h₁ with ⟨sm1, smq1, smη1, pg1, pgq1, pgη1, wq1, wη1, bs1, fin1⟩
          rcases h₂ with ⟨sm2, smq2, smη2, pg2, pgq2, pgη2, wq2, wη2, bs2, fin2⟩
          refine ⟨sm1.add sm2, smq1.add smq2, smη1.add smη2,
            qPeriodic_add pg1 pg2, qPeriodic_add pgq1 pgq2, qPeriodic_add pgη1 pgη2,
            F10Help.hasWeakVec_add' wq1 wq2, F10Help.hasWeakVec_add' wη1 wη2,
            isBodySource_add bs1 bs2, ?_⟩
          filter_upwards [fin1, fin2] with s hs1 hs2 hs0
          exact lt_of_le_of_lt (sliceH1Norm_add_le p.c sm1 smq1 smη1 sm2 smq2 smη2 s)
            (ENNReal.add_lt_top.2 ⟨hs1 hs0, hs2 hs0⟩)
        smul_mem' := by
          intro a F hF
          change StronglyMeasurable (gOf (a • F)) ∧ _
          simp only [map_smul]
          rcases hF with ⟨sm1, smq1, smη1, pg1, pgq1, pgη1, wq1, wη1, bs1, fin1⟩
          refine ⟨sm1.const_smul a, smq1.const_smul a, smη1.const_smul a,
            qPeriodic_smul_real a pg1, qPeriodic_smul_real a pgq1, qPeriodic_smul_real a pgη1,
            hasWeakVec_smul_real a wq1, hasWeakVec_smul_real a wη1,
            isBodySource_smul_real a bs1, ?_⟩
          filter_upwards [fin1] with s hs1 hs0
          exact lt_of_le_of_lt (sliceH1Norm_smul_le p.c a _ _ _ s)
            (ENNReal.mul_lt_top enorm_lt_top (hs1 hs0)) }
    have h_range : Set.range B ⊆ (S : Set (HpR p.c)) := by
      rintro _ ⟨i, rfl⟩
      change StronglyMeasurable (gOf (B i)) ∧ _
      simp only [gOf, gqOf, gηOf, Module.Basis.constr_basis]
      exact h_bas i
    have h_top : S = ⊤ :=
      top_unique (by rw [← B.span_eq]; exact Submodule.span_le.2 h_range)
    intro F
    have hmem : F ∈ S := by rw [h_top]; exact Submodule.mem_top
    exact hmem
  -- Step 3: Slice uniqueness against EarlyBound on (0, p.H] and TailSource on (1, ∞)
  refine ⟨gOf, gqOf, gηOf, fun F => ?_⟩
  rcases h_lin F with ⟨hsm_g, hsm_gq, hsm_gη, hper_g, hper_gq, hper_gη,
    hwq_g, hwη_g, hsrc_g, hfin_g⟩
  obtain ⟨hb0_cls, hb0_resp, hb0q, hb0η, hper_eb, hwq_eb, hwη_eb, hsrc_eb,
    hmc_eb, hm_eb, hsLp_eb⟩ := hEB_F F
  have hm_g : Measurable (sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F)) :=
    CylProjectionSub.measurable_sliceH1Norm_cp p.c hsm_g hsm_gq hsm_gη
  -- 3a: Compare with upgraded (gOf_eb F, gqOf_eb F, gηOf_eb F) on Ioc 0 p.H
  obtain ⟨g_eb', gq_eb', gη_eb', hsm_eb_g, hsm_eb_gq, hsm_eb_gη,
      hper_eb_g, hper_eb_gq, hper_eb_gη, hwq_eb', hwη_eb', hsrc_eb', hae_eb_pos, hsl_eb⟩ :=
    upgrade_bodySource_complex hper_eb hwq_eb hwη_eb hsrc_eb
  have hm_eb' : Measurable (sliceH1Norm p.c g_eb' gq_eb' gη_eb') :=
    CylProjectionSub.measurable_sliceH1Norm_cp p.c hsm_eb_g hsm_eb_gq hsm_eb_gη
  have hsLp_eb' : sLpNorm (13 / 8) p.H (sliceH1Norm p.c g_eb' gq_eb' gη_eb') ≤
      ENNReal.ofReal (C_eb * (p.ν ^ k_eb)⁻¹ * ‖F‖) := by
    rw [sLpNorm_congr_ae_Ioc (hsl_eb.mono fun s hs hm => hs hm.1)]
    exact hsLp_eb
  have hL1_eb' : ∫⁻ s in Ioc 0 p.H, sliceH1Norm p.c g_eb' gq_eb' gη_eb' s < ⊤ := by
    have hlt : sLpNorm (13 / 8) p.H (sliceH1Norm p.c g_eb' gq_eb' gη_eb') < ⊤ :=
      lt_of_le_of_lt hsLp_eb' ENNReal.ofReal_lt_top
    rw [hH_eq] at hlt ⊢
    exact lt_of_le_of_lt (curl_L1_le_of_sLpNorm hSig hν_pos hν1 hm_eb')
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hlt)
  have hfin_eb' : ∀ᵐ s ∂volume, s ∈ Ioc 0 p.H → sliceH1Norm p.c g_eb' gq_eb' gη_eb' s < ⊤ := by
    rw [← ae_restrict_iff' measurableSet_Ioc]
    exact ae_lt_top hm_eb' hL1_eb'.ne
  have hae_uniq_eb := ae_cell_eq_of_isBodySource_pos hc_pos
    hsm_g hsm_gq hsm_gη hsm_eb_g hsm_eb_gq hsm_eb_gη
    hper_g hper_gq hper_gη hper_eb_g hper_eb_gq hper_eb_gη
    hwq_g hwη_g hwq_eb' hwη_eb' hsrc_g hsrc_eb'
  have hae_cell_Ioc : ∀ᵐ s ∂volume, s ∈ Ioc 0 p.H →
      (fun z => gOf F (s, z)) =ᵐ[volume.restrict (B0579.cell p.c)] (fun z => g_eb' (s, z)) ∧
      (fun z => gqOf F (s, z)) =ᵐ[volume.restrict (B0579.cell p.c)] (fun z => gq_eb' (s, z)) ∧
      (fun z => gηOf F (s, z)) =ᵐ[volume.restrict (B0579.cell p.c)] (fun z => gη_eb' (s, z)) := by
    filter_upwards [hae_uniq_eb, hfin_g, hfin_eb'] with s hu hf1 hf2 hs
    exact hu hs.1 (hf1 hs.1) (hf2 hs)
  have hsl_eq_Ioc : ∀ᵐ s ∂volume, s ∈ Ioc 0 p.H →
      sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F) s =
        sliceH1Norm p.c g_eb' gq_eb' gη_eb' s := by
    filter_upwards [hae_cell_Ioc] with s hs hm
    exact sliceH1Norm_congr_ae_cell (hs hm).1 (hs hm).2.1 (hs hm).2.2
  have hsLp_g : sLpNorm (13 / 8) p.H (sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F)) ≤
      ENNReal.ofReal (C_eb * (p.ν ^ k_eb)⁻¹ * ‖F‖) := by
    rw [sLpNorm_congr_ae_Ioc hsl_eq_Ioc]
    exact hsLp_eb'
  have hL1_Ioc_g : ∫⁻ s in Ioc 0 p.H, sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F) s < ⊤ := by
    rw [lintegral_congr_ae ((ae_restrict_iff' measurableSet_Ioc).2 hsl_eq_Ioc)]
    exact hL1_eb'
  have hae_vol_eb' : ∀ᵐ x : Coord, x.1 ∈ Ioo 0 p.H → gOf F x = g_eb' x :=
    ae_vol_eq_of_ae_cell_periodic hc_pos hsm_g hsm_eb_g hper_g hper_eb_g
      (hae_cell_Ioc.mono fun _ hs hm => (hs ⟨hm.1, hm.2.le⟩).1)
  have hae_vol_eb : ∀ᵐ x : Coord, x.1 ∈ Ioo 0 p.H → gOf F x = gOf_eb F x := by
    filter_upwards [hae_vol_eb', hae_eb_pos] with x h1 h2 hx
    exact (h1 hx).trans (h2 hx.1).1
  have hmc_g : IsMeridionalCorrectionOn p p.H (gOf F)
      (zOf_eb F) (zqOf_eb F) (zηOf_eb F) (αMap F) :=
    isMeridionalCorrectionOn_congr_g hae_vol_eb hmc_eb
  -- 3b: Compare with upgraded TailSource witness on Ioi 1
  have hF_inHr : InHr p.c bgp (toProf p.c F) := inHr_toProf hc_pos F
  have hF_norm : hNorm p.c bgp (toProf p.c F) = ENNReal.ofReal ‖F‖ := by
    rw [hNorm_toProf hc_pos F, ofReal_norm]
  obtain ⟨b0', b0q₀, b0η₀, D2, hb0'_ae, hb0'_hr, hbq₀_hr, hbη₀_hr, hD2_hr,
      hsm_b0', hsm_bq₀, hsm_bη₀, hsm_D2, hw_q₀, hw_η₀, hw_00, hw_01, hw_10, hw_11, _⟩ :=
    hFG p.ν p.c p.H hν_pos hc_pos hH_pos (toProf p.c F) (b0Of F) hF_inHr hb0_cls hb0_resp
  obtain ⟨g_ts, gq_ts, gη_ts, hg_ts_per, hg_ts_wq, hg_ts_wη, hg_ts_src₀,
      _hg_ts_meas, _hg_ts_sl, hg_ts_T⟩ :=
    hTS_p p d hreg hν_ts_le (toProf p.c F) (b0Of F) b0' b0q₀ b0η₀ D2
      hF_inHr hb0_cls hb0_resp hb0'_ae hb0'_hr hbq₀_hr hbη₀_hr hD2_hr
      hsm_b0' hsm_bq₀ hsm_bη₀ hsm_D2 hw_q₀ hw_η₀ hw_00 hw_01 hw_10 hw_11
  have hg_ts_src : IsBodySource p.train (b0Of F) (b0qOf F) (b0ηOf F) g_ts :=
    isBodySource_congr_deriv
      (GradBoundHelp.hasWeakVec_unique hw_q₀ hb0q)
      (GradBoundHelp.hasWeakVec_unique hw_η₀ hb0η)
      hg_ts_src₀
  obtain ⟨g_ts', gq_ts', gη_ts', hsm_ts_g, hsm_ts_gq, hsm_ts_gη,
      hper_ts_g, hper_ts_gq, hper_ts_gη, hwq_ts', hwη_ts', hsrc_ts', _, hsl_ts⟩ :=
    upgrade_bodySource_complex hg_ts_per hg_ts_wq hg_ts_wη hg_ts_src
  have hm_ts' : Measurable (sliceH1Norm p.c g_ts' gq_ts' gη_ts') :=
    CylProjectionSub.measurable_sliceH1Norm_cp p.c hsm_ts_g hsm_ts_gq hsm_ts_gη
  have hC_ts_nn : 0 ≤ C_ts * (p.ν ^ k_ts)⁻¹ := by positivity
  have hL1_ts1 : ∫⁻ s in Ioi (1 : ℝ), sliceH1Norm p.c g_ts' gq_ts' gη_ts' s < ⊤ := by
    have heq1 : ∀ᵐ s ∂volume.restrict (Ioi (1 : ℝ)),
        sliceH1Norm p.c g_ts' gq_ts' gη_ts' s = sliceH1Norm p.c g_ts gq_ts gη_ts s := by
      rw [ae_restrict_iff' measurableSet_Ioi]
      filter_upwards [hsl_ts] with s hs hs1
      exact hs (zero_lt_one.trans hs1)
    rw [lintegral_congr_ae heq1]
    have hT1 := hg_ts_T 1 le_rfl
    rw [hF_norm, ← ENNReal.ofReal_mul hC_ts_nn] at hT1
    exact lt_of_le_of_lt (le_self_add.trans hT1) ENNReal.ofReal_lt_top
  have hfin_ts' : ∀ᵐ s ∂volume, 1 < s → sliceH1Norm p.c g_ts' gq_ts' gη_ts' s < ⊤ := by
    change ∀ᵐ s ∂volume, s ∈ Ioi (1 : ℝ) → sliceH1Norm p.c g_ts' gq_ts' gη_ts' s < ⊤
    rw [← ae_restrict_iff' measurableSet_Ioi]
    exact ae_lt_top hm_ts' hL1_ts1.ne
  have hae_uniq_ts := ae_cell_eq_of_isBodySource_pos hc_pos
    hsm_g hsm_gq hsm_gη hsm_ts_g hsm_ts_gq hsm_ts_gη
    hper_g hper_gq hper_gη hper_ts_g hper_ts_gq hper_ts_gη
    hwq_g hwη_g hwq_ts' hwη_ts' hsrc_g hsrc_ts'
  have hsl_eq_Ioi1 : ∀ᵐ s ∂volume, 1 < s →
      sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F) s =
        sliceH1Norm p.c g_ts gq_ts gη_ts s := by
    filter_upwards [hae_uniq_ts, hfin_g, hfin_ts', hsl_ts] with s hu hf1 hf2 hts hs1
    have hs0 : 0 < s := zero_lt_one.trans hs1
    obtain ⟨e1, e2, e3⟩ := hu hs0 (hf1 hs0) (hf2 hs1)
    exact (sliceH1Norm_congr_ae_cell e1 e2 e3).trans (hts hs0)
  have hL1_IoiH : (∫⁻ s in Ioi p.H, sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F) s) ≤
      ENNReal.ofReal (C_ts * (p.ν ^ k_ts)⁻¹ * ‖F‖) := by
    have heqH : ∀ᵐ s ∂volume.restrict (Ioi p.H),
        sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F) s = sliceH1Norm p.c g_ts gq_ts gη_ts s := by
      rw [ae_restrict_iff' measurableSet_Ioi]
      filter_upwards [hsl_eq_Ioi1] with s hs hsH
      exact hs (hH1.trans_lt hsH)
    rw [lintegral_congr_ae heqH]
    have hTH := hg_ts_T p.H hH1
    rw [hF_norm, ← ENNReal.ofReal_mul hC_ts_nn] at hTH
    exact le_self_add.trans hTH
  have htailLp_g : tailLpNorm (-9 / 8) (max 1 (p.H - 1))
      (sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F)) ≤
        ENNReal.ofReal (C_ts * (p.ν ^ k_ts)⁻¹ * ‖F‖) := by
    have heqm : ∀ᵐ s ∂volume, max 1 (p.H - 1) < s →
        sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F) s = sliceH1Norm p.c g_ts gq_ts gη_ts s := by
      filter_upwards [hsl_eq_Ioi1] with s hs hsm
      exact hs ((le_max_left 1 (p.H - 1)).trans_lt hsm)
    rw [tailLpNorm_congr_ae_Ioi heqm]
    have hTm := hg_ts_T (max 1 (p.H - 1)) (le_max_left 1 (p.H - 1))
    rw [hF_norm, ← ENNReal.ofReal_mul hC_ts_nn] at hTm
    exact le_add_self.trans hTm
  exact ⟨hsm_g, hsm_gq, hsm_gη, hper_g, hper_gq, hper_gη, hwq_g, hwη_g, hsrc_g,
    hmc_g, hm_g, hsLp_g, hL1_Ioc_g, hL1_IoiH, htailLp_g⟩

end UnforcedLeray.Short.IIb.ContBodySourceAux

end
