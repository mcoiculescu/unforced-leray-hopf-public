import UnforcedLeray.Short.PartIIb.Tasks.GlobalEnergy.Continuation.HorizonGluing.MollOp
import UnforcedLeray.Short.PartIIb.Tasks.GlobalEnergy.Continuation.BodySourceGlue
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.DivFreeCutoffDensity

/-!
# `HorizonGluing.TestLift`: Stream-primitive test lift and mollified Bochner time derivative

Internal helper module for `MeridionalHorizonGluing` (`PartII-b:F7/2/2`).
Proves:
1. `cprofToLMH`: canonical `LMH c` slice path via `BochnerTime.toPathLq` with automatic strong
   measurability and `L¹` Bochner integrability;
2. `upgrade_early_correction` & `bCut`: Borel `StronglyMeasurable` + `QPeriodic` upgrade of an
   early meridional correction `(z_eb, zq_eb, zη_eb)` on `(0, T]` and slice `L²` control of the
   convective drift `flatBv p.train z₀ zq₀ zη₀`;
3. `EarlyGoodSlice`: full-measure good slices on `(0, T)` with cylinder weak derivatives and
   solenoidality (`LMWeakPd`, `LMWeakDivFree`);
4. Stream-primitive coordinate lift (`tested_real_flatSpatial` -> `tested_real_h1DivFree`) and
   `hasWeakDerivTime_opJ_Z0`: `HasWeakDerivTime 0 T` for `s ↦ opJ p.c hc J hJ k (Z0 s)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff RealInnerProductSpace

namespace UnforcedLeray.Short.IIb.HorizonGluingAux

open UnforcedLeray.Cons.C03.Concrete
open UnforcedLeray.Short.IIb
open UnforcedLeray.Short.IIIa

/-! ### 1. `LMH c` slice paths from `CProf` via `BochnerTime.toPathLq` -/

def cprofToLMH (c : ℝ) (W : CProf) : ℝ → LMH c :=
  BochnerTime.toPathLq 2 (volume.restrict (B0579.cell c)) (fun p => cmeridToLM (W p))

lemma stronglyMeasurable_cprofToLMH {c : ℝ} {W : CProf} (hW : StronglyMeasurable W) :
    StronglyMeasurable (cprofToLMH c W) :=
  BochnerTime.stronglyMeasurable_toPathLq (continuous_cmeridToLM.comp_stronglyMeasurable hW)

lemma memLp_cmeridToLM_of_memLp {c : ℝ} {u : B0579.Plane → CMerid}
    (hu : MemLp u 2 (volume.restrict (B0579.cell c))) :
    MemLp (fun y => cmeridToLM (u y)) 2 (volume.restrict (B0579.cell c)) := by
  refine ⟨continuous_cmeridToLM.comp_aestronglyMeasurable hu.1, ?_⟩
  have heq : eLpNorm (fun y => cmeridToLM (u y)) 2 (volume.restrict (B0579.cell c)) =
      eLpNorm u 2 (volume.restrict (B0579.cell c)) :=
    eLpNorm_congr_norm_ae (Eventually.of_forall fun y => norm_cmeridToLM (u y))
  rw [heq]
  exact hu.2

lemma cprofToLMH_ae_of_memLp {c : ℝ} {W : CProf} {s : ℝ}
    (hW : MemLp (fun y => W (s, y)) 2 (volume.restrict (B0579.cell c))) :
    (cprofToLMH c W s : ℝ × ℝ → EuclideanSpace ℝ (Fin 4)) =ᵐ[volume.restrict (B0579.cell c)]
      fun y => cmeridToLM (W (s, y)) := by
  have hm := memLp_cmeridToLM_of_memLp hW
  unfold cprofToLMH
  rw [BochnerTime.toPathLq_of_memLp hm]
  exact hm.coeFn_toLp

lemma lmLift_cprofToLMH_ae {c : ℝ} {W : CProf} {s : ℝ}
    (hW : MemLp (fun y => W (s, y)) 2 (volume.restrict (B0579.cell c))) :
    ∀ᵐ y ∂(volume.restrict (B0579.cell c)), ∀ i : Fin 2,
      lmLift (cprofToLMH c W s) y i = W (s, y) i := by
  filter_upwards [cprofToLMH_ae_of_memLp hW] with y hy i
  unfold lmLift
  rw [hy]
  fin_cases i <;> simp [cmeridToLM, lmReal, lmSp]

lemma ofReal_norm_cprofToLMH {c : ℝ} {W : CProf} {s : ℝ}
    (hW : MemLp (fun y => W (s, y)) 2 (volume.restrict (B0579.cell c))) :
    ENNReal.ofReal ‖cprofToLMH c W s‖ = cylSliceL2 c (fun y => W (s, y)) := by
  symm
  refine cylSliceL2_eq_ofReal_norm ?_
  filter_upwards [cprofToLMH_ae_of_memLp hW] with y hy
  rw [hy, lmToCMerid_cmeridToLM]

lemma enorm_cprofToLMH_le (c : ℝ) (W : CProf) (s : ℝ) :
    ‖cprofToLMH c W s‖ₑ ≤ cylSliceL2 c (fun y => W (s, y)) := by
  unfold cprofToLMH cylSliceL2
  by_cases hm : MemLp (fun y => cmeridToLM (W (s, y))) 2 (volume.restrict (B0579.cell c))
  · rw [BochnerTime.toPathLq_of_memLp hm, ← enorm_norm, Real.enorm_eq_ofReal (norm_nonneg _),
      Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_lt_top _).ne]
    exact le_of_eq ((eLpNorm_congr_ae hm.coeFn_toLp).trans
      (eLpNorm_congr_norm_ae (Eventually.of_forall fun y => norm_cmeridToLM (W (s, y)))))
  · rw [BochnerTime.toPathLq_of_not_memLp hm, enorm_zero]
    exact zero_le

lemma integrableOn_cprofToLMH {c : ℝ} {W : CProf} (hW : StronglyMeasurable W)
    {S : Set ℝ} (hS : MeasurableSet S)
    (hfin : (∫⁻ s in S, cylSliceL2 c (fun y => W (s, y))) < ⊤) :
    IntegrableOn (cprofToLMH c W) S volume := by
  have _ : MeasurableSet S := hS
  refine ⟨(stronglyMeasurable_cprofToLMH hW).aestronglyMeasurable.restrict, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  exact (lintegral_mono (enorm_cprofToLMH_le c W)).trans_lt hfin

/-! ### 2. Borelian `StronglyMeasurable` & `QPeriodic` upgrade of `(z_eb, zq_eb, zη_eb)` -/

private lemma isCoordTest_mul_smooth_left {ψ φ : Coord → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hφ : IsCoordTest φ) :
    IsCoordTest (fun x => ψ x * φ x) :=
  ⟨hψ.mul hφ.smooth, hφ.compact.mul_left, tsupport_mul_subset_right.trans hφ.supp⟩

private lemma locInt_of_hasWeakFO_vQ0 {u g : Coord → ℂ}
    (h : HasWeakFO vQ0 dZero u g) :
    LocallyIntegrableOn u DriftWeakSHelp.Upos volume ∧
      LocallyIntegrableOn g DriftWeakSHelp.Upos volume := by
  refine ⟨?_, DriftWeakSHelp.locInt_of_tests g (fun φ hφ => (h.1 φ hφ).2)⟩
  intro x₀ hx₀
  have hx₀' : 0 < x₀.1 := DriftWeakSHelp.mem_Upos.1 hx₀
  let χ := DriftWeakSHelp.mkBump x₀ hx₀'
  have hχ : IsCoordTest χ := DriftWeakSHelp.mkBump_isTest x₀ hx₀'
  let r : ℝ := χ.rIn / 2
  have hr : 0 < r := half_pos χ.rIn_pos
  let φ : Coord → ℝ := fun z => -(z.2.1 - x₀.2.1) * χ z
  have hφ : IsCoordTest φ :=
    isCoordTest_mul_smooth_left (((contDiff_fst.comp contDiff_snd).sub contDiff_const).neg) hχ
  have hint := (h.1 φ hφ).1.integrableOn (s := Metric.closedBall x₀ r)
  refine ⟨Metric.closedBall x₀ r,
    mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds x₀ hr), ?_⟩
  refine hint.congr_fun (fun y hy => ?_) measurableSet_closedBall
  have hy_ball : y ∈ Metric.ball x₀ χ.rIn :=
    Metric.mem_ball.2 (lt_of_le_of_lt (Metric.mem_closedBall.1 hy) (half_lt_self χ.rIn_pos))
  have hev : φ =ᶠ[𝓝 y] fun z : Coord => -(z.2.1 - x₀.2.1) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hy_ball] with z hz
    have h1 : (χ : Coord → ℝ) z = 1 := χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hz)
    simp [φ, h1]
  have hfd : fderiv ℝ φ y =
      -((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) := by
    rw [hev.fderiv_eq]
    exact (((hasFDerivAt_fst.comp y hasFDerivAt_snd).sub_const x₀.2.1).neg).fderiv
  have htr : coordTranspose vQ0 dZero φ y = 1 := by
    rw [show vQ0 = ![vQ0, vEta] 0 from rfl, TailPeriodizeAux.coordTranspose_vQ0_vEta 0 φ y]
    simp [cpd, hfd, cdir]
  simp [htr]

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

/-- Weak PDE properties of the Borel-upgraded early profile `(z₀, zq₀, zη₀)` on `(0, T)` (excluding
`initial_curl`, which is transferred directly to the continuous representative `z₁` later). -/
structure IsEarlyBorelRep (p : Params) (T : ℝ) (g z₀ zq₀ zη₀ : CProf) : Prop where
  sm_z : StronglyMeasurable z₀
  sm_zq : StronglyMeasurable zq₀
  sm_zη : StronglyMeasurable zη₀
  per_z : QPeriodic p.c z₀
  per_zq : QPeriodic p.c zq₀
  per_zη : QPeriodic p.c zη₀
  weak_q : HasWeakVec vQ0 dZero z₀ zq₀
  weak_eta : HasWeakVec vEta dZero z₀ zη₀
  solenoidal : ∀ φ, IsCoordTest φ → tsupport φ ⊆ Ioo 0 T ×ˢ univ →
    Integrable (fun x => z₀ x 0 * (cpd 1 φ x : ℂ) + z₀ x 1 * (cpd 2 φ x : ℂ)) ∧
      ∫ x, (z₀ x 0 * (cpd 1 φ x : ℂ) + z₀ x 1 * (cpd 2 φ x : ℂ)) = 0
  equation : ∀ Ψ, IsPlanarSolTest Ψ →
    (∀ i, tsupport (fun x => Ψ x i) ⊆ Ioo 0 T ×ˢ univ) →
    Integrable (fun x => ∑ i : Fin 2, z₀ x i * meridTranspose p.ν Ψ x i) ∧
      Integrable (cdot (flatBv p.train z₀ zq₀ zη₀) Ψ) ∧
      Integrable (cdot g Ψ) ∧
      ∫ x, (∑ i : Fin 2, z₀ x i * meridTranspose p.ν Ψ x i +
          cdot (flatBv p.train z₀ zq₀ zη₀) Ψ x) =
        ∫ x, cdot g Ψ x

private lemma hasWeakVec_congr_pos {j : Fin 2} {u₁ u₂ g₁ g₂ : CProf}
    (hu : ∀ᵐ x : Coord, 0 < x.1 → u₁ x = u₂ x)
    (hg : ∀ᵐ x : Coord, 0 < x.1 → g₁ x = g₂ x)
    (hw : HasWeakVec (![vQ0, vEta] j) dZero u₂ g₂) :
    HasWeakVec (![vQ0, vEta] j) dZero u₁ g₁ := by
  intro i
  have hpair : ∀ φ : Coord → ℝ, IsCoordTest φ →
      (Integrable (fun x => u₁ x i * (coordTranspose (![vQ0, vEta] j) dZero φ x : ℂ)) ∧
        Integrable (fun x => g₁ x i * (φ x : ℂ))) ∧
      ∫ x, g₁ x i * (φ x : ℂ) =
        ∫ x, u₁ x i * (coordTranspose (![vQ0, vEta] j) dZero φ x : ℂ) := by
    intro φ hφ
    have h1 := (hw i).1 φ hφ
    have h2 := (hw i).2 φ hφ
    have hae_u : (fun x => u₁ x i * (coordTranspose (![vQ0, vEta] j) dZero φ x : ℂ)) =ᵐ[volume]
        fun x => u₂ x i * (coordTranspose (![vQ0, vEta] j) dZero φ x : ℂ) := by
      filter_upwards [hu] with x hx
      by_cases hp : 0 < x.1
      · simp [hx hp]
      · have h0 := F10K0Help.isCoordTest_zero_of_nonpos
          (planarTest_isCoordTest_partial hφ (cdir j.succ)) hp
        change cpd j.succ φ x = 0 at h0
        rw [TailPeriodizeAux.coordTranspose_vQ0_vEta j φ x, h0]
        simp
    have hae_g : (fun x => g₁ x i * (φ x : ℂ)) =ᵐ[volume]
        fun x => g₂ x i * (φ x : ℂ) := by
      filter_upwards [hg] with x hx
      by_cases hp : 0 < x.1
      · simp [hx hp]
      · simp [F10K0Help.isCoordTest_zero_of_nonpos hφ hp]
    exact ⟨⟨h1.1.congr hae_u.symm, h1.2.congr hae_g.symm⟩,
      (integral_congr_ae hae_g).trans (h2.trans (integral_congr_ae hae_u.symm))⟩
  exact ⟨fun φ hφ => (hpair φ hφ).1, fun φ hφ => (hpair φ hφ).2⟩

lemma upgrade_early_correction {p : Params} {T M : ℝ} {α : E2}
    {g z_eb zq_eb zη_eb : CProf}
    (heb : IsMeridionalCorrectionOn p T g z_eb zq_eb zη_eb α)
    (hbdd : ∀ᵐ s ∂volume, s ∈ Ioc 0 T → sliceH1Norm p.c z_eb zq_eb zη_eb s ≤ ENNReal.ofReal M) :
    ∃ z₀ zq₀ zη₀ : CProf,
      IsEarlyBorelRep p T g z₀ zq₀ zη₀ ∧
      (∀ᵐ x : Coord, 0 < x.1 → z₀ x = z_eb x ∧ zq₀ x = zq_eb x ∧ zη₀ x = zη_eb x) ∧
      (∀ᵐ s ∂volume, s ∈ Ioc 0 T → sliceH1Norm p.c z₀ zq₀ zη₀ s ≤ ENNReal.ofReal M) := by
  have hzq_per : QPeriodic p.c zq_eb :=
    ContBodySourceAux.qPeriodic_of_hasWeakVec ![0, 1, 0] heb.periodic heb.weak_q
  have hzη_per : QPeriodic p.c zη_eb :=
    ContBodySourceAux.qPeriodic_of_hasWeakVec ![0, 0, 1] heb.periodic heb.weak_eta
  have hz_loc : ∀ i : Fin 2, LocallyIntegrableOn (fun x => z_eb x i) DriftWeakSHelp.Upos volume :=
    fun i => (locInt_of_hasWeakFO_vQ0 (heb.weak_q i)).1
  have hzq_loc : ∀ i : Fin 2, LocallyIntegrableOn (fun x => zq_eb x i) DriftWeakSHelp.Upos volume :=
    fun i => (locInt_of_hasWeakFO_vQ0 (heb.weak_q i)).2
  have hzη_loc : ∀ i : Fin 2, LocallyIntegrableOn (fun x => zη_eb x i) DriftWeakSHelp.Upos volume :=
    fun i => DriftWeakSHelp.locInt_of_tests _ (fun φ hφ => ((heb.weak_eta i).1 φ hφ).2)
  obtain ⟨z₀, hz₀_sm, hz₀_per, hz₀_ae⟩ := exists_sm_rep_pos heb.periodic hz_loc
  obtain ⟨zq₀, hzq₀_sm, hzq₀_per, hzq₀_ae⟩ := exists_sm_rep_pos hzq_per hzq_loc
  obtain ⟨zη₀, hzη₀_sm, hzη₀_per, hzη₀_ae⟩ := exists_sm_rep_pos hzη_per hzη_loc
  have hae : ∀ᵐ x : Coord, 0 < x.1 → z₀ x = z_eb x ∧ zq₀ x = zq_eb x ∧ zη₀ x = zη_eb x := by
    filter_upwards [hz₀_ae, hzq₀_ae, hzη₀_ae] with x h1 h2 h3 hp
    exact ⟨h1 hp, h2 hp, h3 hp⟩
  have hprod := Measure.ae_ae_of_ae_prod hae
  have hsl_eq : ∀ᵐ s ∂volume, 0 < s →
      sliceH1Norm p.c z₀ zq₀ zη₀ s = sliceH1Norm p.c z_eb zq_eb zη_eb s := by
    filter_upwards [hprod] with s hs hp
    have e1 : eLpNorm (fun y => z₀ (s, y)) 2 (volume.restrict (B0579.cell p.c)) =
        eLpNorm (fun y => z_eb (s, y)) 2 (volume.restrict (B0579.cell p.c)) :=
      eLpNorm_congr_ae (ae_restrict_of_ae (hs.mono fun y hy => (hy hp).1))
    have e2 : eLpNorm (fun y => zq₀ (s, y)) 2 (volume.restrict (B0579.cell p.c)) =
        eLpNorm (fun y => zq_eb (s, y)) 2 (volume.restrict (B0579.cell p.c)) :=
      eLpNorm_congr_ae (ae_restrict_of_ae (hs.mono fun y hy => (hy hp).2.1))
    have e3 : eLpNorm (fun y => zη₀ (s, y)) 2 (volume.restrict (B0579.cell p.c)) =
        eLpNorm (fun y => zη_eb (s, y)) 2 (volume.restrict (B0579.cell p.c)) :=
      eLpNorm_congr_ae (ae_restrict_of_ae (hs.mono fun y hy => (hy hp).2.2))
    unfold sliceH1Norm
    rw [e1, e2, e3]
  have hbdd₀ : ∀ᵐ s ∂volume, s ∈ Ioc 0 T →
      sliceH1Norm p.c z₀ zq₀ zη₀ s ≤ ENNReal.ofReal M := by
    filter_upwards [hbdd, hsl_eq] with s hb heq hs
    rw [heq hs.1]
    exact hb hs
  refine ⟨z₀, zq₀, zη₀, ⟨hz₀_sm, hzq₀_sm, hzη₀_sm, hz₀_per, hzq₀_per, hzη₀_per,
    hasWeakVec_congr_pos (j := 0) hz₀_ae hzq₀_ae heb.weak_q,
    hasWeakVec_congr_pos (j := 1) hz₀_ae hzη₀_ae heb.weak_eta, ?_, ?_⟩, hae, hbdd₀⟩
  · intro φ hφ hsupp
    obtain ⟨hI, h0⟩ := heb.solenoidal φ hφ hsupp
    have hae_sol : (fun x => z₀ x 0 * (cpd 1 φ x : ℂ) + z₀ x 1 * (cpd 2 φ x : ℂ)) =ᵐ[volume]
        fun x => z_eb x 0 * (cpd 1 φ x : ℂ) + z_eb x 1 * (cpd 2 φ x : ℂ) := by
      filter_upwards [hz₀_ae] with x hx
      by_cases hp : 0 < x.1
      · simp [hx hp]
      · have h1 := F10K0Help.isCoordTest_zero_of_nonpos
          (planarTest_isCoordTest_partial hφ (cdir 1)) hp
        have h2 := F10K0Help.isCoordTest_zero_of_nonpos
          (planarTest_isCoordTest_partial hφ (cdir 2)) hp
        change cpd 1 φ x = 0 at h1
        change cpd 2 φ x = 0 at h2
        simp [h1, h2]
    exact ⟨hI.congr hae_sol.symm, (integral_congr_ae hae_sol).trans h0⟩
  · intro Ψ hΨ hsupp
    obtain ⟨hI1, hI2, hI3, heq⟩ := heb.equation Ψ hΨ hsupp
    have hae1 : (fun x => ∑ i : Fin 2, z₀ x i * meridTranspose p.ν Ψ x i) =ᵐ[volume]
        fun x => ∑ i : Fin 2, z_eb x i * meridTranspose p.ν Ψ x i := by
      filter_upwards [hz₀_ae] with x hx
      by_cases hp : 0 < x.1
      · simp [hx hp]
      · have hm0 : ∀ i : Fin 2, meridTranspose p.ν Ψ x i = 0 := fun i => by
          have hs0 := F10K0Help.isCoordTest_zero_of_nonpos
            (planarTest_isCoordTest_partial (hΨ.smooth i) (cdir 0)) hp
          have hq2 := F10K0Help.isCoordTest_zero_of_nonpos
            (planarTest_isCoordTest_partial
              (planarTest_isCoordTest_partial (hΨ.smooth i) (cdir 1)) (cdir 1)) hp
          have hη2 := F10K0Help.isCoordTest_zero_of_nonpos
            (planarTest_isCoordTest_partial
              (planarTest_isCoordTest_partial (hΨ.smooth i) (cdir 2)) (cdir 2)) hp
          change cpd 0 (fun y => Ψ y i) x = 0 at hs0
          change cpd 1 (fun y => cpd 1 (fun z => Ψ z i) y) x = 0 at hq2
          change cpd 2 (fun y => cpd 2 (fun z => Ψ z i) y) x = 0 at hη2
          simp [meridTranspose, hs0, hq2, hη2]
        simp [hm0]
    have hae2 : cdot (flatBv p.train z₀ zq₀ zη₀) Ψ =ᵐ[volume]
        cdot (flatBv p.train z_eb zq_eb zη_eb) Ψ := by
      filter_upwards [hae] with x hx
      by_cases hp : 0 < x.1
      · obtain ⟨e1, e2, e3⟩ := hx hp
        simp [cdot, flatBv, e1, e2, e3]
      · have h0 : ∀ i : Fin 2, Ψ x i = 0 :=
          fun i => F10K0Help.isCoordTest_zero_of_nonpos (hΨ.smooth i) hp
        simp [cdot, h0]
    have hae12 : (fun x => ∑ i : Fin 2, z₀ x i * meridTranspose p.ν Ψ x i +
        cdot (flatBv p.train z₀ zq₀ zη₀) Ψ x) =ᵐ[volume]
        fun x => ∑ i : Fin 2, z_eb x i * meridTranspose p.ν Ψ x i +
          cdot (flatBv p.train z_eb zq_eb zη_eb) Ψ x := by
      filter_upwards [hae1, hae2] with x e1 e2; rw [e1, e2]
    refine ⟨hI1.congr hae1.symm, hI2.congr hae2.symm, hI3, ?_⟩
    rw [integral_congr_ae hae12]
    exact heq

/-! ### 3. Cut-off convective drift `bCut` on `Ioc 0 T` -/

def bCut (p : Params) (T : ℝ) (z₀ zq₀ zη₀ : CProf) : CProf :=
  fun x => if x.1 ∈ Ioc 0 T then flatBv p.train z₀ zq₀ zη₀ x else 0

private lemma contDiff_train_slice (p : Params) {s : ℝ} (hs : 0 ≤ s) :
    ContDiff ℝ ∞ (p.train.v s) := by
  have hfun : p.train.v s = (fun q : ℝ × B0579.Plane => p.train.v q.1 q.2) ∘ (fun z => (s, z)) :=
    rfl
  rw [hfun]
  exact p.train.isTrain.smooth_v.comp_contDiff (contDiff_const.prodMk contDiff_id)
    fun z => ⟨hs, trivial⟩

private lemma stronglyMeasurable_train_v_clamp (p : Params) (i : Fin 2) :
    StronglyMeasurable (fun x : Coord => p.train.v (max 0 x.1) x.2 i) := by
  refine Continuous.stronglyMeasurable ?_
  have hproj : Continuous (fun v : UnforcedLeray.Train.Vec => v i) := PiLp.continuous_apply 2 _ i
  have hv_on : ContinuousOn (fun q : Coord => p.train.v q.1 q.2 i) (Ici 0 ×ˢ univ) :=
    hproj.comp_continuousOn p.train.isTrain.smooth_v.continuousOn
  exact hv_on.comp_continuous ((continuous_const.max continuous_fst).prodMk continuous_snd)
    fun x => ⟨le_max_left 0 x.1, trivial⟩

private lemma stronglyMeasurable_train_fderiv_clamp (p : Params) (i : Fin 2) (d : B0579.Plane) :
    StronglyMeasurable
      (fun x : Coord => fderiv ℝ (fun w => p.train.v (max 0 x.1) w i) x.2 d) := by
  let V : Coord → ℝ := fun x => p.train.v (max 0 x.1) x.2 i
  have hV_cont : Continuous V := by
    have hproj : Continuous (fun v : UnforcedLeray.Train.Vec => v i) := PiLp.continuous_apply 2 _ i
    exact (hproj.comp_continuousOn p.train.isTrain.smooth_v.continuousOn).comp_continuous
      ((continuous_const.max continuous_fst).prodMk continuous_snd)
      fun x => ⟨le_max_left 0 x.1, trivial⟩
  let fn : ℕ → Coord → ℝ := fun n x =>
    ((n : ℝ) + 1) * (V (x.1, x.2 + ((n : ℝ) + 1)⁻¹ • d) - V x)
  have hfn_sm : ∀ n : ℕ, StronglyMeasurable (fn n) := fun n => by
    refine Continuous.stronglyMeasurable ?_
    exact continuous_const.mul ((hV_cont.comp
      (continuous_fst.prodMk (continuous_snd.add continuous_const))).sub hV_cont)
  refine stronglyMeasurable_of_tendsto atTop hfn_sm (tendsto_pi_nhds.2 fun x => ?_)
  set s := max 0 x.1
  have hs : 0 ≤ s := le_max_left 0 x.1
  have hsm_i : ContDiff ℝ ∞ (fun w => p.train.v s w i) :=
    (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp
      (contDiff_train_slice p hs)
  have hd_at0 : HasFDerivAt (fun w => p.train.v s w i)
      (fderiv ℝ (fun w => p.train.v s w i) x.2) (x.2 + (0 : ℝ) • d) := by
    simpa using (hsm_i.differentiable (by simp) x.2).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => x.2 + t • d) d 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add x.2
  have hderiv : HasDerivAt (fun t : ℝ => p.train.v s (x.2 + t • d) i)
      (fderiv ℝ (fun w => p.train.v s w i) x.2 d) 0 := by
    simpa [Function.comp_def] using hd_at0.comp_hasDerivAt 0 hline
  have hseq_0 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝[≠] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)) ?_
    exact Eventually.of_forall fun n => inv_ne_zero (by positivity)
  have hlim := hderiv.tendsto_slope_zero.comp hseq_0
  refine hlim.congr fun n => ?_
  dsimp [Function.comp_def, fn, V, s]
  rw [inv_inv, zero_add, zero_smul, add_zero]

lemma stronglyMeasurable_bCut (p : Params) (T : ℝ) {z₀ zq₀ zη₀ : CProf}
    (hz₀ : StronglyMeasurable z₀) (hzq₀ : StronglyMeasurable zq₀)
    (hzη₀ : StronglyMeasurable zη₀) :
    StronglyMeasurable (bCut p T z₀ zq₀ zη₀) := by
  let raw : CProf := fun x => WithLp.toLp 2 fun i : Fin 2 =>
    ((p.train.v (max 0 x.1) x.2 0 : ℝ) : ℂ) * zq₀ x i +
      ((p.train.v (max 0 x.1) x.2 1 : ℝ) : ℂ) * zη₀ x i +
      z₀ x 0 * ((fderiv ℝ (fun w => p.train.v (max 0 x.1) w i) x.2 (1, 0) : ℝ) : ℂ) +
      z₀ x 1 * ((fderiv ℝ (fun w => p.train.v (max 0 x.1) w i) x.2 (0, 1) : ℝ) : ℂ)
  have hraw_sm : StronglyMeasurable raw := by
    have hcomp : ∀ i : Fin 2, StronglyMeasurable (fun x : Coord => raw x i) := fun i => by
      have hv0 := Complex.continuous_ofReal.comp_stronglyMeasurable
        (stronglyMeasurable_train_v_clamp p 0)
      have hv1 := Complex.continuous_ofReal.comp_stronglyMeasurable
        (stronglyMeasurable_train_v_clamp p 1)
      have hdv0 := Complex.continuous_ofReal.comp_stronglyMeasurable
        (stronglyMeasurable_train_fderiv_clamp p i (1, 0))
      have hdv1 := Complex.continuous_ofReal.comp_stronglyMeasurable
        (stronglyMeasurable_train_fderiv_clamp p i (0, 1))
      have hz0 := (PiLp.continuous_apply 2 _ 0).comp_stronglyMeasurable hz₀
      have hz1 := (PiLp.continuous_apply 2 _ 1).comp_stronglyMeasurable hz₀
      have hzq := (PiLp.continuous_apply 2 _ i).comp_stronglyMeasurable hzq₀
      have hzη := (PiLp.continuous_apply 2 _ i).comp_stronglyMeasurable hzη₀
      exact (((hv0.mul hzq).add (hv1.mul hzη)).add (hz0.mul hdv0)).add (hz1.mul hdv1)
    let pair : Coord → ℂ × ℂ := fun x => (raw x 0, raw x 1)
    let pairToCMerid : ℂ × ℂ → CMerid := fun q => WithLp.toLp 2 ![q.1, q.2]
    have hpair_cont : Continuous pairToCMerid :=
      (PiLp.continuous_toLp 2 _).comp
        (continuous_pi fun i => by fin_cases i <;> [exact continuous_fst; exact continuous_snd])
    have hfun : raw = pairToCMerid ∘ pair := by
      funext x; ext i; fin_cases i <;> rfl
    rw [hfun]
    exact hpair_cont.comp_stronglyMeasurable ((hcomp 0).prodMk (hcomp 1))
  have heq : bCut p T z₀ zq₀ zη₀ = (Ioc 0 T ×ˢ (univ : Set B0579.Plane)).indicator raw := by
    funext x
    by_cases hx : x.1 ∈ Ioc 0 T
    · have hmax : max 0 x.1 = x.1 := max_eq_right hx.1.le
      have hmem : x ∈ Ioc 0 T ×ˢ (univ : Set B0579.Plane) := ⟨hx, trivial⟩
      simp [bCut, hx, hmem, raw, flatBv, hmax]
    · have hmem : x ∉ Ioc 0 T ×ˢ (univ : Set B0579.Plane) := fun h => hx h.1
      simp [bCut, hx, hmem]
  rw [heq]
  exact hraw_sm.indicator (measurableSet_Ioc.prod MeasurableSet.univ)

lemma qPeriodic_bCut (p : Params) (T : ℝ) {z₀ zq₀ zη₀ : CProf}
    (hz₀ : QPeriodic p.c z₀) (hzq₀ : QPeriodic p.c zq₀) (hzη₀ : QPeriodic p.c zη₀) :
    QPeriodic p.c (bCut p T z₀ zq₀ zη₀) := by
  refine QPerHalf.of_ae_imp ?_
  filter_upwards [QPerHalf.ae_imp hz₀, QPerHalf.ae_imp hzq₀, QPerHalf.ae_imp hzη₀]
    with x hx0 hxq hxη hp
  have hqs1 : (qShift p.c x).1 = x.1 := rfl
  have hqs2 : (qShift p.c x).2 = (x.2.1 + p.c, x.2.2) := rfl
  by_cases hs : x.1 ∈ Ioc 0 T
  · have hv_per : p.train.v x.1 (x.2.1 + p.c, x.2.2) = p.train.v x.1 x.2 :=
      p.train.isTrain.periodic_v x.1 hp.le x.2
    have hfd_per : ∀ i : Fin 2,
        fderiv ℝ (fun w => p.train.v x.1 w i) (x.2.1 + p.c, x.2.2) =
          fderiv ℝ (fun w => p.train.v x.1 w i) x.2 := fun i => by
      let gv : B0579.Plane → ℝ := fun w => p.train.v x.1 w i
      have hshift : (fun w : B0579.Plane => gv (w + (p.c, 0))) = gv := by
        funext w
        have hw : w + (p.c, (0 : ℝ)) = (w.1 + p.c, w.2) := by ext <;> simp
        dsimp [gv]
        rw [hw]
        exact congrArg (fun u => u i) (p.train.isTrain.periodic_v x.1 hp.le w)
      have h1 : fderiv ℝ (fun w : B0579.Plane => gv (w + (p.c, 0))) x.2 =
          fderiv ℝ gv (x.2 + (p.c, 0)) :=
        fderiv_comp_add_right (f := gv) (p.c, (0 : ℝ))
      have hx2 : x.2 + (p.c, (0 : ℝ)) = (x.2.1 + p.c, x.2.2) := by ext <;> simp
      rw [hshift, hx2] at h1
      exact h1.symm
    ext i
    simp only [bCut, hqs1, hs, ↓reduceIte]
    dsimp [flatBv]
    rw [hqs2, hx0 hp, hxq hp, hxη hp, hv_per, hfd_per i]
  · simp only [bCut, hqs1, hs, ↓reduceIte]

lemma exists_bCut_sliceL2_bound {p : Params} {d dm dp T : ℝ}
    (hbg : BgRegime p d dm dp) (hT : 0 < T) (z₀ zq₀ zη₀ : CProf)
    (hz₀_sm : StronglyMeasurable z₀) (hzq₀_sm : StronglyMeasurable zq₀)
    (hzη₀_sm : StronglyMeasurable zη₀) :
    ∃ C_tr : ℝ, 0 ≤ C_tr ∧ ∀ s ∈ Ioc 0 T,
      cylSliceL2 p.c (fun y => bCut p T z₀ zq₀ zη₀ (s, y)) ≤
        ENNReal.ofReal C_tr * sliceH1Norm p.c z₀ zq₀ zη₀ s := by
  obtain ⟨M₀, hM₀⟩ := hbg.train_buc.sup_bound hT.le
  obtain ⟨M₁, hM₁⟩ := hbg.train_buc.deriv_bound hT.le 1
  set C₀ : ℝ := max 0 M₀
  set C₁ : ℝ := max 0 M₁
  set K : ℝ := 2 * C₀ + 4 * C₁
  have hC₀_nn : 0 ≤ C₀ := le_max_left 0 M₀
  have hC₁_nn : 0 ≤ C₁ := le_max_left 0 M₁
  have hK_nn : 0 ≤ K := by positivity
  refine ⟨K, hK_nn, fun s hs => ?_⟩
  have hs_cc : s ∈ Icc 0 T := ⟨hs.1.le, hs.2⟩
  set μ := volume.restrict (B0579.cell p.c)
  have hpt : ∀ y : B0579.Plane,
      ‖bCut p T z₀ zq₀ zη₀ (s, y)‖ ≤
        K * (‖z₀ (s, y)‖ + ‖zq₀ (s, y)‖ + ‖zη₀ (s, y)‖) := by
    intro y
    have hv_le : ∀ j : Fin 2, |p.train.v s y j| ≤ C₀ := fun j =>
      (Real.norm_eq_abs _ ▸ PiLp.norm_apply_le (p.train.v s y) j).trans
        ((hM₀ s hs_cc y).trans (le_max_right 0 M₀))
    have hfd_le : ∀ (i : Fin 2) (e : B0579.Plane), ‖e‖ ≤ 1 →
        |fderiv ℝ (fun w => p.train.v s w i) y e| ≤ C₁ := fun i e he => by
      have hd_v : DifferentiableAt ℝ (p.train.v s) y :=
        (contDiff_train_slice p hs_cc.1).differentiable (by simp) y
      have hproj : fderiv ℝ (fun w => p.train.v s w i) y =
          (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).comp
            (fderiv ℝ (p.train.v s) y) :=
        ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).hasFDerivAt.comp y
          hd_v.hasFDerivAt).fderiv
      rw [hproj, ContinuousLinearMap.comp_apply, ← Real.norm_eq_abs]
      calc ‖(EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
              (fderiv ℝ (p.train.v s) y e)‖
          ≤ ‖fderiv ℝ (p.train.v s) y e‖ := PiLp.norm_apply_le _ i
        _ ≤ ‖fderiv ℝ (p.train.v s) y‖ * ‖e‖ := (fderiv ℝ (p.train.v s) y).le_opNorm e
        _ ≤ ‖fderiv ℝ (p.train.v s) y‖ * 1 :=
            mul_le_mul_of_nonneg_left he (norm_nonneg _)
        _ = ‖iteratedFDeriv ℝ 1 (p.train.v s) y‖ := by rw [mul_one, norm_iteratedFDeriv_one]
        _ ≤ C₁ := (hM₁ s hs_cc y).trans (le_max_right 0 M₁)
    have he10 : ‖((1 : ℝ), (0 : ℝ))‖ ≤ 1 := by simp [Prod.norm_mk]
    have he01 : ‖((0 : ℝ), (1 : ℝ))‖ ≤ 1 := by simp [Prod.norm_mk]
    have hcomp_le : ∀ i : Fin 2,
        ‖bCut p T z₀ zq₀ zη₀ (s, y) i‖ ≤
          C₀ * ‖zq₀ (s, y)‖ + C₀ * ‖zη₀ (s, y)‖ + 2 * C₁ * ‖z₀ (s, y)‖ := fun i => by
      simp only [bCut, hs, ↓reduceIte, flatBv, WithLp.ofLp_toLp]
      set t1 : ℂ := ((p.train.v s y 0 : ℝ) : ℂ) * zq₀ (s, y) i
      set t2 : ℂ := ((p.train.v s y 1 : ℝ) : ℂ) * zη₀ (s, y) i
      set t3 : ℂ := z₀ (s, y) 0 * ((fderiv ℝ (fun w => p.train.v s w i) y (1, 0) : ℝ) : ℂ)
      set t4 : ℂ := z₀ (s, y) 1 * ((fderiv ℝ (fun w => p.train.v s w i) y (0, 1) : ℝ) : ℂ)
      calc ‖t1 + t2 + t3 + t4‖
          ≤ ‖t1‖ + ‖t2‖ + ‖t3‖ + ‖t4‖ := by
            linarith [norm_add_le (t1 + t2 + t3) t4, norm_add_le (t1 + t2) t3, norm_add_le t1 t2]
        _ = |p.train.v s y 0| * ‖zq₀ (s, y) i‖ +
            |p.train.v s y 1| * ‖zη₀ (s, y) i‖ +
            ‖z₀ (s, y) 0‖ * |fderiv ℝ (fun w => p.train.v s w i) y (1, 0)| +
            ‖z₀ (s, y) 1‖ * |fderiv ℝ (fun w => p.train.v s w i) y (0, 1)| := by
            simp [t1, t2, t3, t4, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ C₀ * ‖zq₀ (s, y)‖ + C₀ * ‖zη₀ (s, y)‖ +
            ‖z₀ (s, y)‖ * C₁ + ‖z₀ (s, y)‖ * C₁ := by
            gcongr
            · exact hv_le 0
            · exact PiLp.norm_apply_le _ i
            · exact hv_le 1
            · exact PiLp.norm_apply_le _ i
            · exact PiLp.norm_apply_le _ 0
            · exact hfd_le i (1, 0) he10
            · exact PiLp.norm_apply_le _ 1
            · exact hfd_le i (0, 1) he01
        _ = C₀ * ‖zq₀ (s, y)‖ + C₀ * ‖zη₀ (s, y)‖ + 2 * C₁ * ‖z₀ (s, y)‖ := by ring
    have hnorm_sum : ‖bCut p T z₀ zq₀ zη₀ (s, y)‖ ≤
        ‖bCut p T z₀ zq₀ zη₀ (s, y) 0‖ + ‖bCut p T z₀ zq₀ zη₀ (s, y) 1‖ := by
      have hsq : ‖bCut p T z₀ zq₀ zη₀ (s, y)‖ ^ 2 ≤
          (‖bCut p T z₀ zq₀ zη₀ (s, y) 0‖ + ‖bCut p T z₀ zq₀ zη₀ (s, y) 1‖) ^ 2 := by
        rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
        nlinarith [norm_nonneg (bCut p T z₀ zq₀ zη₀ (s, y) 0),
          norm_nonneg (bCut p T z₀ zq₀ zη₀ (s, y) 1)]
      nlinarith [norm_nonneg (bCut p T z₀ zq₀ zη₀ (s, y)),
        norm_nonneg (bCut p T z₀ zq₀ zη₀ (s, y) 0),
        norm_nonneg (bCut p T z₀ zq₀ zη₀ (s, y) 1)]
    have h0 := hcomp_le 0
    have h1 := hcomp_le 1
    have hz_nn := norm_nonneg (z₀ (s, y))
    have hzq_nn := norm_nonneg (zq₀ (s, y))
    have hzη_nn := norm_nonneg (zη₀ (s, y))
    dsimp [K]
    nlinarith
  have hm0 : AEStronglyMeasurable (fun y => ‖z₀ (s, y)‖) μ :=
    (hz₀_sm.comp_measurable (measurable_const.prodMk measurable_id)).norm.aestronglyMeasurable
  have hmq : AEStronglyMeasurable (fun y => ‖zq₀ (s, y)‖) μ :=
    (hzq₀_sm.comp_measurable (measurable_const.prodMk measurable_id)).norm.aestronglyMeasurable
  have hmη : AEStronglyMeasurable (fun y => ‖zη₀ (s, y)‖) μ :=
    (hzη₀_sm.comp_measurable (measurable_const.prodMk measurable_id)).norm.aestronglyMeasurable
  unfold cylSliceL2 sliceH1Norm
  calc eLpNorm (fun y => bCut p T z₀ zq₀ zη₀ (s, y)) 2 μ
      ≤ eLpNorm (fun y => K * (‖z₀ (s, y)‖ + ‖zq₀ (s, y)‖ + ‖zη₀ (s, y)‖)) 2 μ :=
        eLpNorm_mono fun y => (hpt y).trans (le_abs_self _)
    _ = ‖K‖ₑ * eLpNorm (fun y => ‖z₀ (s, y)‖ + ‖zq₀ (s, y)‖ + ‖zη₀ (s, y)‖) 2 μ :=
        eLpNorm_const_smul (f := fun y => ‖z₀ (s, y)‖ + ‖zq₀ (s, y)‖ + ‖zη₀ (s, y)‖) K 2 μ
    _ ≤ ENNReal.ofReal K *
        (eLpNorm (fun y => ‖z₀ (s, y)‖ + ‖zq₀ (s, y)‖) 2 μ +
          eLpNorm (fun y => ‖zη₀ (s, y)‖) 2 μ) := by
        rw [Real.enorm_eq_ofReal hK_nn]
        gcongr
        exact eLpNorm_add_le (hm0.add hmq) hmη one_le_two
    _ ≤ ENNReal.ofReal K *
        (eLpNorm (fun y => ‖z₀ (s, y)‖) 2 μ + eLpNorm (fun y => ‖zq₀ (s, y)‖) 2 μ +
          eLpNorm (fun y => ‖zη₀ (s, y)‖) 2 μ) := by
        gcongr
        exact eLpNorm_add_le hm0 hmq one_le_two
    _ = ENNReal.ofReal K *
        (eLpNorm (fun y => z₀ (s, y)) 2 μ + eLpNorm (fun y => zq₀ (s, y)) 2 μ +
          eLpNorm (fun y => zη₀ (s, y)) 2 μ) := by
        simp only [eLpNorm_norm]

/-! ### 4. Full-measure good slices `EarlyGoodSlice` on `(0, T)` -/

private lemma ae_div_zero_on_Ioo {T : ℝ} {u uq uη : CProf}
    (huq : HasWeakVec vQ0 dZero u uq)
    (huη : HasWeakVec vEta dZero u uη)
    (hsol : ∀ φ, IsCoordTest φ → tsupport φ ⊆ Ioo 0 T ×ˢ univ →
      Integrable (fun x => u x 0 * (cpd 1 φ x : ℂ) + u x 1 * (cpd 2 φ x : ℂ)) ∧
        ∫ x, (u x 0 * (cpd 1 φ x : ℂ) + u x 1 * (cpd 2 φ x : ℂ)) = 0) :
    ∀ᵐ x : Coord, x.1 ∈ Ioo 0 T → uq x 0 + uη x 1 = 0 := by
  let W : Set Coord := Ioo 0 T ×ˢ univ
  have hW_open : IsOpen W := isOpen_Ioo.prod isOpen_univ
  have hW_sub : W ⊆ DriftWeakSHelp.Upos := prod_mono Ioo_subset_Ioi_self subset_rfl
  have hloc_q : LocallyIntegrableOn (fun x => uq x 0) W volume :=
    (DriftWeakSHelp.locInt_of_tests _ (fun φ hφ => ((huq 0).1 φ hφ).2)).mono_set hW_sub
  have hloc_η : LocallyIntegrableOn (fun x => uη x 1) W volume :=
    (DriftWeakSHelp.locInt_of_tests _ (fun φ hφ => ((huη 1).1 φ hφ).2)).mono_set hW_sub
  have : (volume : Measure Coord).IsAddHaarMeasure := DriftWeakSHelp.instIsAddHaarVolCoord
  have hae := hW_open.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hloc_q.add hloc_η) (by
    intro χ hχ_sm hχ_cp hχ_supp
    have hχ_test : IsCoordTest χ := ⟨hχ_sm, hχ_cp, hχ_supp.trans hW_sub⟩
    have iq := (huq 0).1 χ hχ_test
    have iη := (huη 1).1 χ hχ_test
    have eq_q := (huq 0).2 χ hχ_test
    have eq_η := (huη 1).2 χ hχ_test
    have htr_q : (fun x => u x 0 * (coordTranspose vQ0 dZero χ x : ℂ)) =
        fun x => -(u x 0 * (cpd 1 χ x : ℂ)) := by
      funext x
      rw [show vQ0 = ![vQ0, vEta] 0 from rfl, TailPeriodizeAux.coordTranspose_vQ0_vEta 0 χ x]
      push_cast; ring
    have htr_η : (fun x => u x 1 * (coordTranspose vEta dZero χ x : ℂ)) =
        fun x => -(u x 1 * (cpd 2 χ x : ℂ)) := by
      funext x
      rw [show vEta = ![vQ0, vEta] 1 from rfl, TailPeriodizeAux.coordTranspose_vQ0_vEta 1 χ x]
      push_cast; ring
    have hfun : (fun x : Coord => χ x • (uq x 0 + uη x 1)) =
        fun x => uq x 0 * (χ x : ℂ) + uη x 1 * (χ x : ℂ) := by
      funext x; simp [Complex.real_smul]; ring
    change ∫ x, χ x • (uq x 0 + uη x 1) = 0
    rw [hfun, integral_add iq.2 iη.2, eq_q, eq_η]
    have iq_neg : Integrable (fun x => u x 0 * (cpd 1 χ x : ℂ)) := by
      have h := iq.1; rw [htr_q] at h; simpa using h.neg
    have iη_neg : Integrable (fun x => u x 1 * (cpd 2 χ x : ℂ)) := by
      have h := iη.1; rw [htr_η] at h; simpa using h.neg
    rw [htr_q, htr_η, integral_neg, integral_neg, ← neg_add, ← integral_add iq_neg iη_neg,
      (hsol χ hχ_test hχ_supp).2, neg_zero])
  filter_upwards [hae] with x hx hmem
  exact hx ⟨hmem, trivial⟩

private lemma measurable_cylSliceL2 (c : ℝ) {W : CProf} (hW : StronglyMeasurable W) :
    Measurable (fun s : ℝ => cylSliceL2 c (fun y => W (s, y))) := by
  unfold cylSliceL2
  have hp0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hpt : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have htwo : (2 : ℝ≥0∞).toReal = 2 := rfl
  have heq : (fun s : ℝ => eLpNorm (fun y => W (s, y)) 2 (volume.restrict (B0579.cell c))) =
      fun s => (∫⁻ y in B0579.cell c, ‖W (s, y)‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    funext s
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt, htwo]
  rw [heq]
  exact ((hW.measurable.enorm.pow_const (2 : ℝ)).lintegral_prod_right').pow_const (1 / 2 : ℝ)

structure EarlyGoodSlice (p : Params) (g gq gη z₀ zq₀ zη₀ b_cut : CProf)
    (M C_tr : ℝ) (s : ℝ) : Prop where
  memL2_z : MemLp (fun y => z₀ (s, y)) 2 (volume.restrict (B0579.cell p.c))
  memL2_zq : MemLp (fun y => zq₀ (s, y)) 2 (volume.restrict (B0579.cell p.c))
  memL2_zη : MemLp (fun y => zη₀ (s, y)) 2 (volume.restrict (B0579.cell p.c))
  memL2_b : MemLp (fun y => b_cut (s, y)) 2 (volume.restrict (B0579.cell p.c))
  memL2_g : MemLp (fun y => g (s, y)) 2 (volume.restrict (B0579.cell p.c))
  memL2_gq : MemLp (fun y => gq (s, y)) 2 (volume.restrict (B0579.cell p.c))
  memL2_gη : MemLp (fun y => gη (s, y)) 2 (volume.restrict (B0579.cell p.c))
  weak_z_q : ∀ i : Fin 2, HasWeakCellDerivC p.c 0 (fun y => z₀ (s, y) i) (fun y => zq₀ (s, y) i)
  weak_z_eta : ∀ i : Fin 2, HasWeakCellDerivC p.c 1 (fun y => z₀ (s, y) i) (fun y => zη₀ (s, y) i)
  sol_z : IsCylSolenoidalSlice p.c (fun y => z₀ (s, y))
  weak_g_q : ∀ i : Fin 2, HasWeakCellDerivC p.c 0 (fun y => g (s, y) i) (fun y => gq (s, y) i)
  weak_g_eta : ∀ i : Fin 2, HasWeakCellDerivC p.c 1 (fun y => g (s, y) i) (fun y => gη (s, y) i)
  sol_g : IsCylSolenoidalSlice p.c (fun y => g (s, y))
  bound_z : sliceH1Norm p.c z₀ zq₀ zη₀ s ≤ ENNReal.ofReal M
  bound_b : cylSliceL2 p.c (fun y => b_cut (s, y)) ≤ ENNReal.ofReal (C_tr * M)

lemma ae_earlyGoodSlice {p : Params} {T M C_tr : ℝ} (hM : 0 ≤ M) (hC_tr : 0 ≤ C_tr)
    {g gq gη z₀ zq₀ zη₀ b_cut : CProf}
    (hg : IsCylSourceH1 p.c g gq gη)
    (hg_int : (∫⁻ s in Ioc 0 T, sliceH1Norm p.c g gq gη s) < ⊤)
    (hz : IsEarlyBorelRep p T g z₀ zq₀ zη₀)
    (hb_sm : StronglyMeasurable b_cut)
    (hb_le : ∀ s ∈ Ioc 0 T,
      cylSliceL2 p.c (fun y => b_cut (s, y)) ≤ ENNReal.ofReal C_tr * sliceH1Norm p.c z₀ zq₀ zη₀ s)
    (hbdd : ∀ᵐ s ∂volume, s ∈ Ioc 0 T → sliceH1Norm p.c z₀ zq₀ zη₀ s ≤ ENNReal.ofReal M) :
    ∀ᵐ s ∂volume, s ∈ Ioo 0 T → EarlyGoodSlice p g gq gη z₀ zq₀ zη₀ b_cut M C_tr s := by
  have hc : 0 < p.c := p.c_pos
  have hmeas_g : Measurable (sliceH1Norm p.c g gq gη) :=
    ((measurable_cylSliceL2 p.c hg.sm_g).add (measurable_cylSliceL2 p.c hg.sm_gq)).add
      (measurable_cylSliceL2 p.c hg.sm_gη)
  have hg_ae_fin : ∀ᵐ s ∂volume, s ∈ Ioc 0 T → sliceH1Norm p.c g gq gη s < ⊤ :=
    (ae_restrict_iff' measurableSet_Ioc).1 (ae_lt_top hmeas_g hg_int.ne)
  have hdiv_z := Measure.ae_ae_of_ae_prod
    (ae_div_zero_on_Ioo (T := T) hz.weak_q hz.weak_eta hz.solenoidal)
  have hdiv_g := Measure.ae_ae_of_ae_prod
    (ae_div_zero_on_Ioo (T := T) hg.weak_q hg.weak_eta (fun φ hφ _ => hg.solenoidal φ hφ))
  have hw_zq := FlatBvSliceGoodAeNeeded.jointWeakToSlice_proof p.c hc 0 z₀ zq₀
    hz.sm_z hz.sm_zq hz.per_z hz.per_zq hz.weak_q
  have hw_zη := FlatBvSliceGoodAeNeeded.jointWeakToSlice_proof p.c hc 1 z₀ zη₀
    hz.sm_z hz.sm_zη hz.per_z hz.per_zη hz.weak_eta
  have hw_gq := FlatBvSliceGoodAeNeeded.jointWeakToSlice_proof p.c hc 0 g gq
    hg.sm_g hg.sm_gq hg.periodic_g hg.periodic_gq hg.weak_q
  have hw_gη := FlatBvSliceGoodAeNeeded.jointWeakToSlice_proof p.c hc 1 g gη
    hg.sm_g hg.sm_gη hg.periodic_g hg.periodic_gη hg.weak_eta
  filter_upwards [hbdd, hg_ae_fin, hdiv_z, hdiv_g, hw_zq, hw_zη, hw_gq, hw_gη] with
    s hbz hgf hdz hdg wzq wzη wgq wgη hs
  have hs_oc : s ∈ Ioc 0 T := ⟨hs.1, hs.2.le⟩
  have hbz' := hbz hs_oc
  have hgf' := hgf hs_oc
  have hfin_z : sliceH1Norm p.c z₀ zq₀ zη₀ s < ⊤ := hbz'.trans_lt ENNReal.ofReal_lt_top
  have hm_z : MemLp (fun y => z₀ (s, y)) 2 (volume.restrict (B0579.cell p.c)) :=
    ⟨(hz.sm_z.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable,
      (le_add_of_nonneg_right zero_le).trans
        (le_add_of_nonneg_right zero_le) |>.trans_lt hfin_z⟩
  have hm_zq : MemLp (fun y => zq₀ (s, y)) 2 (volume.restrict (B0579.cell p.c)) :=
    ⟨(hz.sm_zq.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable,
      (le_add_of_nonneg_left zero_le).trans
        (le_add_of_nonneg_right zero_le) |>.trans_lt hfin_z⟩
  have hm_zη : MemLp (fun y => zη₀ (s, y)) 2 (volume.restrict (B0579.cell p.c)) :=
    ⟨(hz.sm_zη.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable,
      (le_add_of_nonneg_left zero_le).trans_lt hfin_z⟩
  have hbb : cylSliceL2 p.c (fun y => b_cut (s, y)) ≤ ENNReal.ofReal (C_tr * M) := by
    calc cylSliceL2 p.c (fun y => b_cut (s, y))
        ≤ ENNReal.ofReal C_tr * sliceH1Norm p.c z₀ zq₀ zη₀ s := hb_le s hs_oc
      _ ≤ ENNReal.ofReal C_tr * ENNReal.ofReal M := by gcongr
      _ = ENNReal.ofReal (C_tr * M) := (ENNReal.ofReal_mul hC_tr).symm
  have hm_b : MemLp (fun y => b_cut (s, y)) 2 (volume.restrict (B0579.cell p.c)) :=
    ⟨(hb_sm.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable,
      hbb.trans_lt ENNReal.ofReal_lt_top⟩
  have hm_g : MemLp (fun y => g (s, y)) 2 (volume.restrict (B0579.cell p.c)) :=
    ⟨(hg.sm_g.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable,
      (le_add_of_nonneg_right zero_le).trans
        (le_add_of_nonneg_right zero_le) |>.trans_lt hgf'⟩
  have hm_gq : MemLp (fun y => gq (s, y)) 2 (volume.restrict (B0579.cell p.c)) :=
    ⟨(hg.sm_gq.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable,
      (le_add_of_nonneg_left zero_le).trans
        (le_add_of_nonneg_right zero_le) |>.trans_lt hgf'⟩
  have hm_gη : MemLp (fun y => gη (s, y)) 2 (volume.restrict (B0579.cell p.c)) :=
    ⟨(hg.sm_gη.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable,
      (le_add_of_nonneg_left zero_le).trans_lt hgf'⟩
  have wzq' := wzq hs.1 hm_z hm_zq
  have wzη' := wzη hs.1 hm_z hm_zη
  have wgq' := wgq hs.1 hm_g hm_gq
  have wgη' := wgη hs.1 hm_g hm_gη
  have hsol_z : IsCylSolenoidalSlice p.c (fun y => z₀ (s, y)) := by
    intro ψ hψ
    have i0 := (wzq' 0).1 ψ hψ
    have i1 := (wzη' 1).1 ψ hψ
    refine ⟨i0.1.add i1.1, ?_⟩
    rw [integral_add i0.1 i1.1, (wzq' 0).2 ψ hψ, (wzη' 1).2 ψ hψ, ← neg_add,
      ← integral_add i0.2 i1.2, neg_eq_zero]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [ae_restrict_of_ae hdz] with y hy
    rw [← add_mul, hy hs, zero_mul, Pi.zero_apply]
  have hsol_g : IsCylSolenoidalSlice p.c (fun y => g (s, y)) := by
    intro ψ hψ
    have i0 := (wgq' 0).1 ψ hψ
    have i1 := (wgη' 1).1 ψ hψ
    refine ⟨i0.1.add i1.1, ?_⟩
    rw [integral_add i0.1 i1.1, (wgq' 0).2 ψ hψ, (wgη' 1).2 ψ hψ, ← neg_add,
      ← integral_add i0.2 i1.2, neg_eq_zero]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [ae_restrict_of_ae hdg] with y hy
    rw [← add_mul, hy hs, zero_mul, Pi.zero_apply]
  have _ : 0 ≤ M := hM
  exact ⟨hm_z, hm_zq, hm_zη, hm_b, hm_g, hm_gq, hm_gη, wzq', wzη', hsol_z,
    wgq', wgη', hsol_g, hbz', hbb⟩

lemma lmWeakPd_of_hasWeakCellDerivC {c : ℝ} {j : Fin 2} {U Ud : CProf} {s : ℝ}
    (hU : MemLp (fun y => U (s, y)) 2 (volume.restrict (B0579.cell c)))
    (hUd : MemLp (fun y => Ud (s, y)) 2 (volume.restrict (B0579.cell c)))
    (hw : ∀ i : Fin 2, HasWeakCellDerivC c j (fun y => U (s, y) i) (fun y => Ud (s, y) i)) :
    ∀ i : Fin 2, LMWeakPd c j
      (fun y => lmLift (cprofToLMH c U s) y i)
      (fun y => lmLift (cprofToLMH c Ud s) y i) := by
  intro i
  refine ⟨lmLift_cellL2 _ i, lmLift_cellL2 _ i, fun φ hsm hper hband => ?_⟩
  have hφ : B0579.IsCylTest c φ := ⟨hsm, hper, hband⟩
  have e1 : ∫ x in B0579.cell c, lmLift (cprofToLMH c U s) x i * (B0579.pd j φ x : ℂ) =
      ∫ x in B0579.cell c, U (s, x) i * (B0579.pd j φ x : ℂ) := by
    refine integral_congr_ae ?_
    filter_upwards [lmLift_cprofToLMH_ae hU] with x hx
    rw [hx i]
  have e2 : ∫ x in B0579.cell c, lmLift (cprofToLMH c Ud s) x i * (φ x : ℂ) =
      ∫ x in B0579.cell c, Ud (s, x) i * (φ x : ℂ) := by
    refine integral_congr_ae ?_
    filter_upwards [lmLift_cprofToLMH_ae hUd] with x hx
    rw [hx i]
  rw [e1, e2]
  exact (hw i).2 φ hφ

lemma lmWeakDivFree_of_solenoidalSlice {c : ℝ} {U : CProf} {s : ℝ}
    (hU : MemLp (fun y => U (s, y)) 2 (volume.restrict (B0579.cell c)))
    (hsol : IsCylSolenoidalSlice c (fun y => U (s, y))) :
    LMWeakDivFree c (lmLift (cprofToLMH c U s)) := by
  intro ψ hψ
  rw [← (hsol ψ hψ).2]
  refine integral_congr_ae ?_
  filter_upwards [lmLift_cprofToLMH_ae hU] with x hx
  rw [hx 0, hx 1]

namespace EarlyGoodSlice

variable {p : Params} {g gq gη z₀ zq₀ zη₀ b_cut : CProf} {M C_tr s : ℝ}

lemma lmWeakPd_Z (hs : EarlyGoodSlice p g gq gη z₀ zq₀ zη₀ b_cut M C_tr s) (j : Fin 2) :
    ∀ i : Fin 2, LMWeakPd p.c j
      (fun y => lmLift (cprofToLMH p.c z₀ s) y i)
      (fun y => lmLift (cprofToLMH p.c (![zq₀, zη₀] j) s) y i) := by
  fin_cases j
  · exact lmWeakPd_of_hasWeakCellDerivC hs.memL2_z hs.memL2_zq hs.weak_z_q
  · exact lmWeakPd_of_hasWeakCellDerivC hs.memL2_z hs.memL2_zη hs.weak_z_eta

lemma lmWeakPd_G (hs : EarlyGoodSlice p g gq gη z₀ zq₀ zη₀ b_cut M C_tr s) (j : Fin 2) :
    ∀ i : Fin 2, LMWeakPd p.c j
      (fun y => lmLift (cprofToLMH p.c g s) y i)
      (fun y => lmLift (cprofToLMH p.c (![gq, gη] j) s) y i) := by
  fin_cases j
  · exact lmWeakPd_of_hasWeakCellDerivC hs.memL2_g hs.memL2_gq hs.weak_g_q
  · exact lmWeakPd_of_hasWeakCellDerivC hs.memL2_g hs.memL2_gη hs.weak_g_eta

lemma lmWeakDivFree_Z (hs : EarlyGoodSlice p g gq gη z₀ zq₀ zη₀ b_cut M C_tr s) :
    LMWeakDivFree p.c (lmLift (cprofToLMH p.c z₀ s)) :=
  lmWeakDivFree_of_solenoidalSlice hs.memL2_z hs.sol_z

lemma lmWeakDivFree_G (hs : EarlyGoodSlice p g gq gη z₀ zq₀ zη₀ b_cut M C_tr s) :
    LMWeakDivFree p.c (lmLift (cprofToLMH p.c g s)) :=
  lmWeakDivFree_of_solenoidalSlice hs.memL2_g hs.sol_g

lemma norm_Z0_le (hs : EarlyGoodSlice p g gq gη z₀ zq₀ zη₀ b_cut M C_tr s) (hM : 0 ≤ M) :
    ‖cprofToLMH p.c z₀ s‖ ≤ M := by
  have h1 : ENNReal.ofReal ‖cprofToLMH p.c z₀ s‖ ≤ ENNReal.ofReal M := by
    rw [ofReal_norm_cprofToLMH hs.memL2_z]
    exact ((le_add_of_nonneg_right zero_le).trans (le_add_of_nonneg_right zero_le)).trans hs.bound_z
  exact (ENNReal.ofReal_le_ofReal_iff hM).1 h1

lemma norm_Zq0_le (hs : EarlyGoodSlice p g gq gη z₀ zq₀ zη₀ b_cut M C_tr s) (hM : 0 ≤ M) :
    ‖cprofToLMH p.c zq₀ s‖ ≤ M := by
  have h1 : ENNReal.ofReal ‖cprofToLMH p.c zq₀ s‖ ≤ ENNReal.ofReal M := by
    rw [ofReal_norm_cprofToLMH hs.memL2_zq]
    exact ((le_add_of_nonneg_left zero_le).trans (le_add_of_nonneg_right zero_le)).trans hs.bound_z
  exact (ENNReal.ofReal_le_ofReal_iff hM).1 h1

lemma norm_Zη0_le (hs : EarlyGoodSlice p g gq gη z₀ zq₀ zη₀ b_cut M C_tr s) (hM : 0 ≤ M) :
    ‖cprofToLMH p.c zη₀ s‖ ≤ M := by
  have h1 : ENNReal.ofReal ‖cprofToLMH p.c zη₀ s‖ ≤ ENNReal.ofReal M := by
    rw [ofReal_norm_cprofToLMH hs.memL2_zη]
    exact (le_add_of_nonneg_left zero_le).trans hs.bound_z
  exact (ENNReal.ofReal_le_ofReal_iff hM).1 h1

lemma norm_B_le (hs : EarlyGoodSlice p g gq gη z₀ zq₀ zη₀ b_cut M C_tr s)
    (hM : 0 ≤ M) (hC_tr : 0 ≤ C_tr) :
    ‖cprofToLMH p.c b_cut s‖ ≤ C_tr * M := by
  have h1 : ENNReal.ofReal ‖cprofToLMH p.c b_cut s‖ ≤ ENNReal.ofReal (C_tr * M) := by
    rw [ofReal_norm_cprofToLMH hs.memL2_b]
    exact hs.bound_b
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC_tr hM)).1 h1

end EarlyGoodSlice

/-! ### 5. Real/imaginary `LMH c` embeddings, Stream-Primitive Lift, and `HasWeakDerivTime` -/

def vecRe (φ : ℝ × ℝ → Fin 2 → ℝ) : LMSpField :=
  fun y i => (φ y i : ℂ)

def vecIm (φ : ℝ × ℝ → Fin 2 → ℝ) : LMSpField :=
  fun y i => Complex.I * (φ y i : ℂ)

lemma vecRe_cellL2 {c : ℝ} {φ : ℝ × ℝ → Fin 2 → ℝ}
    (hφ : ∀ i : Fin 2, MemLp (fun y => φ y i) 2 (volume.restrict (B0579.cell c))) :
    LMCellL2 c (vecRe φ) :=
  fun i => Complex.ofRealCLM.comp_memLp' (hφ i)

lemma vecIm_cellL2 {c : ℝ} {φ : ℝ × ℝ → Fin 2 → ℝ}
    (hφ : ∀ i : Fin 2, MemLp (fun y => φ y i) 2 (volume.restrict (B0579.cell c))) :
    LMCellL2 c (vecIm φ) :=
  fun i => (Complex.ofRealCLM.comp_memLp' (hφ i)).const_mul Complex.I

lemma re_cell_pair_eq_inner {c : ℝ} {W : CProf} {s : ℝ}
    (hW : MemLp (fun y => W (s, y)) 2 (volume.restrict (B0579.cell c)))
    {φ : ℝ × ℝ → Fin 2 → ℝ}
    (hφ : ∀ i : Fin 2, MemLp (fun y => φ y i) 2 (volume.restrict (B0579.cell c))) :
    (∑ i : Fin 2, ∫ y in B0579.cell c, W (s, y) i * (φ y i : ℂ)).re =
      ⟪toLMH (vecRe φ) (vecRe_cellL2 hφ), cprofToLMH c W s⟫ := by
  have h1 := lmLift_cprofToLMH_ae hW
  rw [inner_lmH_eq_re_lmIp, lmIp_congr_left (lmLift_toLMH_ae (vecRe_cellL2 hφ)),
    lmIp_congr_right h1]
  unfold LMIp
  have hw_l2 : LMCellL2 c (fun y i => W (s, y) i) := fun i =>
    (lmLift_cellL2 (cprofToLMH c W s) i).ae_eq (h1.mono fun y hy => hy i)
  rw [integral_finsetSum _ fun i _ => lmIp_integrable (vecRe_cellL2 hφ) hw_l2 i]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  dsimp [vecRe]
  rw [Complex.conj_ofReal, mul_comm]

lemma im_cell_pair_eq_inner {c : ℝ} {W : CProf} {s : ℝ}
    (hW : MemLp (fun y => W (s, y)) 2 (volume.restrict (B0579.cell c)))
    {φ : ℝ × ℝ → Fin 2 → ℝ}
    (hφ : ∀ i : Fin 2, MemLp (fun y => φ y i) 2 (volume.restrict (B0579.cell c))) :
    (∑ i : Fin 2, ∫ y in B0579.cell c, W (s, y) i * (φ y i : ℂ)).im =
      ⟪toLMH (vecIm φ) (vecIm_cellL2 hφ), cprofToLMH c W s⟫ := by
  have h1 := lmLift_cprofToLMH_ae hW
  rw [inner_lmH_eq_re_lmIp, lmIp_congr_left (lmLift_toLMH_ae (vecIm_cellL2 hφ)),
    lmIp_congr_right h1]
  unfold LMIp
  have hw_l2 : LMCellL2 c (fun y i => W (s, y) i) := fun i =>
    (lmLift_cellL2 (cprofToLMH c W s) i).ae_eq (h1.mono fun y hy => hy i)
  rw [integral_finsetSum _ fun i _ => lmIp_integrable (vecIm_cellL2 hφ) hw_l2 i,
    Complex.im_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have heq : (fun y => starRingEnd ℂ (vecIm φ y i) * W (s, y) i) =
      fun y => (-Complex.I) * (W (s, y) i * (φ y i : ℂ)) := by
    funext y
    dsimp [vecIm]
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [heq, integral_const_mul]
  simp

private lemma norm_toLMH_vecRe_sub_sq {c : ℝ} {φ₁ φ₂ : ℝ × ℝ → Fin 2 → ℝ}
    (h1 : ∀ i : Fin 2, MemLp (fun y => φ₁ y i) 2 (volume.restrict (B0579.cell c)))
    (h2 : ∀ i : Fin 2, MemLp (fun y => φ₂ y i) 2 (volume.restrict (B0579.cell c))) :
    ‖toLMH (vecRe φ₁) (vecRe_cellL2 h1) - toLMH (vecRe φ₂) (vecRe_cellL2 h2)‖ ^ 2 =
      ∫ y in B0579.cell c, ∑ i : Fin 2, (φ₁ y i - φ₂ y i) ^ 2 := by
  have hsub : ∀ i : Fin 2, MemLp (fun y => φ₁ y i - φ₂ y i) 2 (volume.restrict (B0579.cell c)) :=
    fun i => (h1 i).sub (h2 i)
  have heq : toLMH (vecRe φ₁) (vecRe_cellL2 h1) - toLMH (vecRe φ₂) (vecRe_cellL2 h2) =
      toLMH (vecRe fun y i => φ₁ y i - φ₂ y i) (vecRe_cellL2 hsub) := by
    apply Lp.ext_iff.2
    filter_upwards [Lp.coeFn_sub (toLMH (vecRe φ₁) (vecRe_cellL2 h1))
        (toLMH (vecRe φ₂) (vecRe_cellL2 h2)),
      toLMH_ae (vecRe_cellL2 h1), toLMH_ae (vecRe_cellL2 h2),
      toLMH_ae (vecRe_cellL2 hsub)] with y hys hy1 hy2 hy3
    rw [hys, Pi.sub_apply, hy1, hy2, hy3, ← lmReal_sub]
    congr 1; ext i; simp [vecRe]
  rw [heq, norm_toLMH_sq]
  refine integral_congr_ae (ae_of_all _ fun y => Finset.sum_congr rfl fun i _ => ?_)
  dsimp [vecRe]
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

private lemma norm_toLMH_vecIm_sub_sq {c : ℝ} {φ₁ φ₂ : ℝ × ℝ → Fin 2 → ℝ}
    (h1 : ∀ i : Fin 2, MemLp (fun y => φ₁ y i) 2 (volume.restrict (B0579.cell c)))
    (h2 : ∀ i : Fin 2, MemLp (fun y => φ₂ y i) 2 (volume.restrict (B0579.cell c))) :
    ‖toLMH (vecIm φ₁) (vecIm_cellL2 h1) - toLMH (vecIm φ₂) (vecIm_cellL2 h2)‖ ^ 2 =
      ∫ y in B0579.cell c, ∑ i : Fin 2, (φ₁ y i - φ₂ y i) ^ 2 := by
  have hsub : ∀ i : Fin 2, MemLp (fun y => φ₁ y i - φ₂ y i) 2 (volume.restrict (B0579.cell c)) :=
    fun i => (h1 i).sub (h2 i)
  have heq : toLMH (vecIm φ₁) (vecIm_cellL2 h1) - toLMH (vecIm φ₂) (vecIm_cellL2 h2) =
      toLMH (vecIm fun y i => φ₁ y i - φ₂ y i) (vecIm_cellL2 hsub) := by
    apply Lp.ext_iff.2
    filter_upwards [Lp.coeFn_sub (toLMH (vecIm φ₁) (vecIm_cellL2 h1))
        (toLMH (vecIm φ₂) (vecIm_cellL2 h2)),
      toLMH_ae (vecIm_cellL2 h1), toLMH_ae (vecIm_cellL2 h2),
      toLMH_ae (vecIm_cellL2 hsub)] with y hys hy1 hy2 hy3
    rw [hys, Pi.sub_apply, hy1, hy2, hy3, ← lmReal_sub]
    congr 1; ext i; dsimp [vecIm]; push_cast; ring
  rw [heq, norm_toLMH_sq]
  refine integral_congr_ae (ae_of_all _ fun y => Finset.sum_congr rfl fun i _ => ?_)
  dsimp [vecIm]
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]

private lemma tendsto_of_norm_sq_tendsto_zero {E : Type*} [NormedAddCommGroup E]
    {u : ℕ → E} {x : E} (h : Tendsto (fun n => ‖u n - x‖ ^ 2) atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 x) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq := (Real.continuous_sqrt.tendsto 0).comp h
  rw [Real.sqrt_zero] at hsq
  exact hsq.congr fun n => Real.sqrt_sq (norm_nonneg _)

/-! #### 5a. Smooth `c`-periodic partition of unity `qPart` on `ℝ` -/

private def qBump0 (c : ℝ) (hc : 0 < c) : ContDiffBump (0 : ℝ) :=
  ⟨c, 2 * c, hc, by linarith⟩

private def qBumpSum (c : ℝ) (hc : 0 < c) (q : ℝ) : ℝ :=
  ∑' k : ℤ, qBump0 c hc (q + (k : ℝ) * c)

private lemma qBump0_eq_zero_of_abs {c : ℝ} (hc : 0 < c) {q : ℝ} (hq : 2 * c ≤ |q|) :
    qBump0 c hc q = 0 := by
  apply (qBump0 c hc).zero_of_le_dist
  simpa [qBump0, Real.dist_eq] using hq

private lemma qBumpSum_eq_finset {c Q : ℝ} (hc : 0 < c) {N : ℕ}
    (hN : (Q + 2 * c) / c + 1 < (N : ℝ)) {q : ℝ} (hq : |q| ≤ Q) :
    qBumpSum c hc q =
      ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), qBump0 c hc (q + (k : ℝ) * c) := by
  refine tsum_eq_sum fun k hk => qBump0_eq_zero_of_abs hc (le_of_lt ?_)
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hk
  have hk_abs : (N : ℝ) + 1 ≤ |(k : ℝ)| := by
    have hk_int : (N : ℤ) + 1 ≤ |k| := by
      rcases hk with hk | hk
      · rw [abs_of_neg (by omega)]; omega
      · rw [abs_of_nonneg (by omega)]; omega
    have hk_r : ((N : ℤ) + 1 : ℝ) ≤ (|k| : ℝ) := by exact_mod_cast hk_int
    simpa [Int.cast_abs] using hk_r
  have h1 : Q + 2 * c + c < ((N : ℝ) + 1) * c := by
    have hm := mul_lt_mul_of_pos_right hN hc
    have hdiv : ((Q + 2 * c) / c + 1) * c = Q + 2 * c + c := by field_simp [hc.ne']
    linarith
  have h2 : ((N : ℝ) + 1) * c ≤ |(k : ℝ)| * c := mul_le_mul_of_nonneg_right hk_abs hc.le
  have h3 : |(k : ℝ)| * c - |q| ≤ |q + (k : ℝ) * c| := by
    have hsub := abs_sub_abs_le_abs_add ((k : ℝ) * c) q
    rw [add_comm, abs_mul, abs_of_pos hc] at hsub
    linarith
  linarith

private lemma contDiff_qBumpSum {c : ℝ} (hc : 0 < c) : ContDiff ℝ ∞ (qBumpSum c hc) := by
  rw [contDiff_iff_contDiffAt]
  intro q₀
  obtain ⟨N, hN⟩ := exists_nat_gt (((|q₀| + 1) + 2 * c) / c + 1)
  have hU : {q : ℝ | |q| < |q₀| + 1} ∈ 𝓝 q₀ :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds (lt_add_one |q₀|)
  have hev : qBumpSum c hc =ᶠ[𝓝 q₀]
      fun q : ℝ => ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), qBump0 c hc (q + (k : ℝ) * c) :=
    Filter.eventually_of_mem hU fun q hq => qBumpSum_eq_finset hc hN (le_of_lt hq)
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  refine (ContDiff.sum fun k _ => ?_).contDiffAt
  exact (qBump0 c hc).contDiff.comp (contDiff_id.add contDiff_const)

private lemma qBumpSum_periodic {c : ℝ} (hc : 0 < c) (q : ℝ) :
    qBumpSum c hc (q + c) = qBumpSum c hc q := by
  unfold qBumpSum
  have e : (fun k : ℤ => qBump0 c hc (q + c + (k : ℝ) * c)) =
      fun k : ℤ => qBump0 c hc (q + ((k + 1 : ℤ) : ℝ) * c) := by
    funext k; congr 1; push_cast; ring
  rw [e]
  exact (Equiv.addRight (1 : ℤ)).tsum_eq (fun k : ℤ => qBump0 c hc (q + (k : ℝ) * c))

private lemma qBumpSum_int_shift {c : ℝ} (hc : 0 < c) (q : ℝ) (k : ℤ) :
    qBumpSum c hc (q + (k : ℝ) * c) = qBumpSum c hc q := by
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih =>
    have heq : q + (((n : ℤ) + 1 : ℤ) : ℝ) * c = (q + ((n : ℤ) : ℝ) * c) + c := by push_cast; ring
    rw [heq, qBumpSum_periodic hc]
    exact ih
  | pred n ih =>
    have heq : (q + ((- (n : ℤ) - 1 : ℤ) : ℝ) * c) + c = q + ((-(n : ℤ) : ℤ) : ℝ) * c := by
      push_cast; ring
    rw [← qBumpSum_periodic hc (q + ((- (n : ℤ) - 1 : ℤ) : ℝ) * c), heq]
    exact ih

private lemma one_le_qBumpSum {c : ℝ} (hc : 0 < c) (q : ℝ) :
    1 ≤ qBumpSum c hc q := by
  let m : ℤ := -⌊(q + c / 2) / c⌋
  obtain ⟨N, hN⟩ := exists_nat_gt (max ((|q| + 2 * c) / c + 1) |(m : ℝ)|)
  have hN1 : (|q| + 2 * c) / c + 1 < (N : ℝ) := (le_max_left _ _).trans_lt hN
  have hN2 : |(m : ℝ)| < (N : ℝ) := (le_max_right _ _).trans_lt hN
  rw [qBumpSum_eq_finset hc hN1 (le_refl |q|)]
  have hm_mem : m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    rw [Finset.mem_Icc]
    have hlt : |m| < (N : ℤ) := by
      have : (|m| : ℝ) < (N : ℝ) := by simpa [Int.cast_abs] using hN2
      exact_mod_cast this
    exact ⟨(abs_lt.1 hlt).1.le, (abs_lt.1 hlt).2.le⟩
  have hm_ball : q + (m : ℝ) * c ∈ Metric.closedBall (0 : ℝ) (qBump0 c hc).rIn := by
    change dist (q + (m : ℝ) * c) 0 ≤ c
    rw [Real.dist_eq, sub_zero, abs_le]
    have hf1 : (⌊(q + c / 2) / c⌋ : ℝ) ≤ (q + c / 2) / c := Int.floor_le _
    have hf2 : (q + c / 2) / c < (⌊(q + c / 2) / c⌋ : ℝ) + 1 := Int.lt_floor_add_one _
    have hm1 := mul_le_mul_of_nonneg_right hf1 hc.le
    have hm2 := mul_lt_mul_of_pos_right hf2 hc
    have hdiv : (q + c / 2) / c * c = q + c / 2 := div_mul_cancel₀ _ hc.ne'
    have hmc : (m : ℝ) * c = -((⌊(q + c / 2) / c⌋ : ℝ) * c) := by dsimp [m]; push_cast; ring
    exact ⟨by linarith, by linarith⟩
  have h1 : qBump0 c hc (q + (m : ℝ) * c) = 1 := (qBump0 c hc).one_of_mem_closedBall hm_ball
  calc (1 : ℝ) = qBump0 c hc (q + (m : ℝ) * c) := h1.symm
    _ ≤ ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), qBump0 c hc (q + (k : ℝ) * c) :=
      Finset.single_le_sum (f := fun k : ℤ => qBump0 c hc (q + (k : ℝ) * c))
        (fun k _ => (qBump0 c hc).nonneg' _) hm_mem

private def qPart (c : ℝ) (hc : 0 < c) (q : ℝ) : ℝ :=
  qBump0 c hc q * (qBumpSum c hc q)⁻¹

private lemma contDiff_qPart {c : ℝ} (hc : 0 < c) : ContDiff ℝ ∞ (qPart c hc) :=
  (qBump0 c hc).contDiff.mul
    ((contDiff_qBumpSum hc).inv fun q => by linarith [one_le_qBumpSum hc q])

private lemma qPart_eq_zero_of_abs {c : ℝ} (hc : 0 < c) {q : ℝ} (hq : 2 * c ≤ |q|) :
    qPart c hc q = 0 := by
  simp [qPart, qBump0_eq_zero_of_abs hc hq]

private lemma tsum_qPart_shifts {c : ℝ} (hc : 0 < c) (q : ℝ) :
    (∑' k : ℤ, qPart c hc (q + (k : ℝ) * c)) = 1 := by
  have heq : (fun k : ℤ => qPart c hc (q + (k : ℝ) * c)) =
      fun k : ℤ => qBump0 c hc (q + (k : ℝ) * c) * (qBumpSum c hc q)⁻¹ := by
    funext k
    simp [qPart, qBumpSum_int_shift hc q k]
  rw [heq, tsum_mul_right]
  change qBumpSum c hc q * (qBumpSum c hc q)⁻¹ = 1
  exact mul_inv_cancel₀ (by linarith [one_le_qBumpSum hc q])

/-! #### 5b. Stream-primitive lift of `IsFlatSpatialTest` to `IsPlanarSolTest` -/

private lemma memLp_cell_of_band {c S : ℝ} {f : ℝ × ℝ → ℝ}
    (hf : Continuous f) (hband : ∀ y : ℝ × ℝ, S < |y.2| → f y = 0) :
    MemLp f 2 (volume.restrict (B0579.cell c)) := by
  rcases le_or_gt c 0 with hc0 | hc
  · have hemp : B0579.cell c = ∅ := by
      ext y; simp only [B0579.cell, mem_prod, mem_Ico, mem_univ, and_true, mem_empty_iff_false,
        iff_false, not_and, not_lt]
      intro hy; linarith
    simp [hemp]
  · set R := max 1 S
    have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_left 1 S)
    let Kbox : Set (ℝ × ℝ) := Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R
    obtain ⟨M0, hM0⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
      (s := Kbox) hf.continuousOn
    set M := max 0 M0
    let Box : Set (ℝ × ℝ) := Ico (-(c / 2)) (c / 2) ×ˢ Icc (-R) R
    have hBox_meas : MeasurableSet Box := measurableSet_Ico.prod measurableSet_Icc
    have hBox_sub : Box ⊆ B0579.cell c := prod_mono Subset.rfl (subset_univ _)
    have hBox_fin : volume Box < ⊤ := by
      dsimp [Box]
      rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, Real.volume_Icc]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    have hp0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
    have hpt : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
    have htwo : (2 : ℝ≥0∞).toReal = 2 := rfl
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt, htwo]
    refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ne_of_lt ?_)
    calc ∫⁻ y in B0579.cell c, ‖f y‖ₑ ^ (2 : ℝ)
        ≤ ∫⁻ y in B0579.cell c, Box.indicator (fun _ => ENNReal.ofReal (M ^ 2)) y := by
          refine setLIntegral_mono (Measurable.indicator measurable_const hBox_meas) fun y hyc => ?_
          by_cases hyB : y ∈ Box
          · rw [Set.indicator_of_mem hyB]
            have hyK : y ∈ Kbox := ⟨Ico_subset_Icc_self hyB.1, hyB.2⟩
            have hle : ‖f y‖ ≤ M := (hM0 y hyK).trans (le_max_right 0 M0)
            rw [← enorm_norm, ← Real.enorm_rpow_of_nonneg (norm_nonneg _) (by norm_num),
              Real.rpow_two, Real.enorm_eq_ofReal (sq_nonneg _)]
            exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) hle 2)
          · have hnot : y.2 ∉ Icc (-R) R := fun h2 => hyB ⟨hyc.1, h2⟩
            have hgt : S < |y.2| := by
              have hRgt : R < |y.2| := by
                by_contra hle; push Not at hle; exact hnot (abs_le.1 hle)
              exact (le_max_right 1 S).trans_lt hRgt
            simp [Set.indicator_of_notMem hyB, hband y hgt]
      _ ≤ ∫⁻ y, Box.indicator (fun _ => ENNReal.ofReal (M ^ 2)) y := setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (M ^ 2) * volume Box := by rw [lintegral_indicator hBox_meas]; simp
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hBox_fin

private lemma pd_eq_zero_of_band {S : ℝ} {f : ℝ × ℝ → ℝ}
    (hband : ∀ y : ℝ × ℝ, S < |y.2| → f y = 0) (j : Fin 2) {y : ℝ × ℝ}
    (hy : S + 1 < |y.2|) :
    B0579.pd j f y = 0 := by
  have hev : f =ᶠ[𝓝 y] 0 := by
    filter_upwards [Metric.ball_mem_nhds y one_pos] with z hz
    apply hband
    have hdist : |z.2 - y.2| < 1 := by
      have h1 : ‖z - y‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
      exact (Real.norm_eq_abs _ ▸ norm_snd_le (z - y)).trans_lt h1
    have hsub := abs_sub_abs_le_abs_sub y.2 z.2
    rw [abs_sub_comm] at hdist
    linarith
  unfold B0579.pd
  rw [hev.fderiv_eq]
  simp

private lemma isH1DivFreeTest_of_flatSpatial {c : ℝ} {φ : ℝ × ℝ → Fin 2 → ℝ}
    (hφ : IsFlatSpatialTest c φ) :
    IsH1DivFreeTest c φ := by
  obtain ⟨R, hR⟩ := hφ.bounded
  refine ⟨hφ.smooth, hφ.periodic, hφ.divFree,
    fun i => memLp_cell_of_band (hφ.smooth i).continuous (fun y hy => hR y i hy),
    fun i j => memLp_cell_of_band ?_ (fun y hy => pd_eq_zero_of_band (fun z hz => hR z i hz) j hy)⟩
  unfold B0579.pd
  exact (((contDiff_infty_iff_fderiv.1 (hφ.smooth i)).2).clm_apply contDiff_const).continuous

private lemma contDiff_prim_1d {m : ℝ → ℝ} (hm : ContDiff ℝ ∞ m) (a : ℝ) :
    ContDiff ℝ ∞ (fun u : ℝ => ∫ t in a..u, m t) ∧
      ∀ u : ℝ, HasDerivAt (fun w : ℝ => ∫ t in a..w, m t) (m u) u := by
  have hhd : ∀ u : ℝ, HasDerivAt (fun w : ℝ => ∫ t in a..w, m t) (m u) u := fun u =>
    intervalIntegral.integral_hasDerivAt_right (hm.continuous.intervalIntegrable a u)
      (hm.continuous.stronglyMeasurableAtFilter volume (𝓝 u)) hm.continuous.continuousAt
  refine ⟨contDiff_infty.2 fun n => ?_, hhd⟩
  induction n with
  | zero =>
    push_cast
    rw [contDiff_zero]
    exact (show Differentiable ℝ _ from fun u => (hhd u).differentiableAt).continuous
  | succ k _ =>
    push_cast
    rw [contDiff_succ_iff_deriv]
    refine ⟨fun u => (hhd u).differentiableAt, by simp, ?_⟩
    have hder : deriv (fun u : ℝ => ∫ t in a..u, m t) = m := funext fun u => (hhd u).deriv
    rw [hder]
    exact hm.of_le (by simp)

private def prodSG (α : ℝ → ℝ) (G : ℝ × ℝ → ℝ) (x : Coord) : ℝ :=
  α x.1 * G x.2

private lemma hasDerivAt_coord_cdir {F : Coord → ℝ} (hF : ContDiff ℝ ∞ F)
    (k : Fin 3) (x : Coord) :
    HasDerivAt (fun t : ℝ => F (x + t • cdir k)) (cpd k F x) 0 := by
  have h1 : HasFDerivAt F (fderiv ℝ F x) (x + (0 : ℝ) • cdir k) := by
    simpa using (hF.differentiable (by simp) x).hasFDerivAt
  have h2 : HasDerivAt (fun t : ℝ => x + t • cdir k) (cdir k) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (cdir k)).const_add x
  simpa [cpd, Function.comp_def] using h1.comp_hasDerivAt 0 h2

private lemma hasDerivAt_plane_dir {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ ∞ G)
    (j : Fin 2) (y : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => G (y + t • B0579.dir j)) (B0579.pd j G y) 0 := by
  have h1 : HasFDerivAt G (fderiv ℝ G y) (y + (0 : ℝ) • B0579.dir j) := by
    simpa using (hG.differentiable (by simp) y).hasFDerivAt
  have h2 : HasDerivAt (fun t : ℝ => y + t • B0579.dir j) (B0579.dir j) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (B0579.dir j)).const_add y
  simpa [B0579.pd, Function.comp_def] using h1.comp_hasDerivAt 0 h2

private lemma contDiff_prodSG {α : ℝ → ℝ} {G : ℝ × ℝ → ℝ}
    (hα : ContDiff ℝ ∞ α) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (prodSG α G) :=
  (hα.comp contDiff_fst).mul (hG.comp contDiff_snd)

private lemma cpd0_prodSG {α : ℝ → ℝ} {G : ℝ × ℝ → ℝ}
    (hα : ContDiff ℝ ∞ α) (hG : ContDiff ℝ ∞ G) (x : Coord) :
    cpd 0 (prodSG α G) x = deriv α x.1 * G x.2 := by
  have hd1 := hasDerivAt_coord_cdir (contDiff_prodSG hα hG) 0 x
  have hlin : HasDerivAt (fun t : ℝ => x.1 + t) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add x.1
  have ha : HasDerivAt α (deriv α x.1) (x.1 + 0) := by
    rw [add_zero]
    exact (hα.differentiable (by simp) _).hasDerivAt
  have hd2 : HasDerivAt (fun t : ℝ => prodSG α G (x + t • cdir 0)) (deriv α x.1 * G x.2) 0 := by
    have hfun : (fun t : ℝ => prodSG α G (x + t • cdir 0)) = fun t => α (x.1 + t) * G x.2 := by
      funext t
      have hx1 : (x + t • cdir 0).1 = x.1 + t := by simp [cdir]
      have hx2 : (x + t • cdir 0).2 = x.2 := by ext <;> simp [cdir]
      simp [prodSG, hx1, hx2]
    rw [hfun]
    have hcomp : HasDerivAt (fun t : ℝ => α (x.1 + t)) (deriv α x.1 * 1) 0 :=
      (ha.comp (0 : ℝ) hlin).congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)
    rw [mul_one] at hcomp
    exact hcomp.mul_const (G x.2)
  exact hd1.unique hd2

private lemma cpd_succ_prodSG {α : ℝ → ℝ} {G : ℝ × ℝ → ℝ}
    (hα : ContDiff ℝ ∞ α) (hG : ContDiff ℝ ∞ G) (j : Fin 2) (x : Coord) :
    cpd j.succ (prodSG α G) x = α x.1 * B0579.pd j G x.2 := by
  have hd1 := hasDerivAt_coord_cdir (contDiff_prodSG hα hG) j.succ x
  have hfun : (fun t : ℝ => prodSG α G (x + t • cdir j.succ)) =
      fun t : ℝ => α x.1 * G (x.2 + t • B0579.dir j) := by
    funext t
    fin_cases j <;> simp [prodSG, cdir, B0579.dir]
  have hd2 : HasDerivAt (fun t : ℝ => prodSG α G (x + t • cdir j.succ))
      (α x.1 * B0579.pd j G x.2) 0 := by
    rw [hfun]
    exact (hasDerivAt_plane_dir hG j x.2).const_mul (α x.1)
  exact hd1.unique hd2

private lemma isCoordTest_prodSG {T Q S : ℝ} {α : ℝ → ℝ} {G : ℝ × ℝ → ℝ}
    (hα_sm : ContDiff ℝ ∞ α) (hα_cs : HasCompactSupport α) (hα_ts : tsupport α ⊆ Ioo 0 T)
    (hG_sm : ContDiff ℝ ∞ G)
    (hG_supp : ∀ y : ℝ × ℝ, (Q < |y.1| ∨ S < |y.2|) → G y = 0) :
    IsCoordTest (prodSG α G) ∧ tsupport (prodSG α G) ⊆ Ioo 0 T ×ˢ univ := by
  let Q' := max 1 Q
  let S' := max 1 S
  let K : Set Coord := tsupport α ×ˢ (Icc (-Q') Q' ×ˢ Icc (-S') S')
  have hK_comp : IsCompact K := hα_cs.isCompact.prod (isCompact_Icc.prod isCompact_Icc)
  have hsupp_sub : Function.support (prodSG α G) ⊆ K := by
    intro x hx
    rw [Function.mem_support] at hx
    refine ⟨subset_tsupport α (Function.mem_support.2 fun ha0 => hx (by simp [prodSG, ha0])), ?_⟩
    by_contra hnot
    refine hx ?_
    have hG0 : G x.2 = 0 := by
      apply hG_supp
      by_contra hle
      push Not at hle
      apply hnot
      exact ⟨abs_le.1 (hle.1.trans (le_max_right 1 Q)),
        abs_le.1 (hle.2.trans (le_max_right 1 S))⟩
    simp [prodSG, hG0]
  have hts_sub : tsupport (prodSG α G) ⊆ K :=
    closure_minimal hsupp_sub hK_comp.isClosed
  have hK_Ioo : K ⊆ Ioo 0 T ×ˢ univ := prod_mono hα_ts (subset_univ _)
  have hts_Ioo : tsupport (prodSG α G) ⊆ Ioo 0 T ×ˢ univ := hts_sub.trans hK_Ioo
  refine ⟨⟨contDiff_prodSG hα_sm hG_sm, HasCompactSupport.of_support_subset_isCompact hK_comp hsupp_sub,
    hts_Ioo.trans (prod_mono Ioo_subset_Ioi_self subset_rfl)⟩, hts_Ioo⟩

private lemma pd0_snd {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (y : ℝ × ℝ) :
    B0579.pd 0 (fun w : ℝ × ℝ => f w.2) y = 0 := by
  have hd1 := hasDerivAt_plane_dir (hf.comp contDiff_snd) 0 y
  have hd2 : HasDerivAt (fun t : ℝ => f (y + t • B0579.dir 0).2) 0 0 := by
    have hfun : (fun t : ℝ => f (y + t • B0579.dir 0).2) = fun _ => f y.2 := by
      funext t; simp [B0579.dir]
    rw [hfun]; exact hasDerivAt_const 0 (f y.2)
  exact hd1.unique hd2

private lemma pd1_snd {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (y : ℝ × ℝ) :
    B0579.pd 1 (fun w : ℝ × ℝ => f w.2) y = deriv f y.2 := by
  have hd1 := hasDerivAt_plane_dir (hf.comp contDiff_snd) 1 y
  have hlin : HasDerivAt (fun t : ℝ => y.2 + t) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add y.2
  have hdf : HasDerivAt f (deriv f y.2) (y.2 + 0) := by
    rw [add_zero]
    exact (hf.differentiable (by simp) _).hasDerivAt
  have hd2 : HasDerivAt (fun t : ℝ => f (y + t • B0579.dir 1).2) (deriv f y.2) 0 := by
    have hfun : (fun t : ℝ => f (y + t • B0579.dir 1).2) = fun t => f (y.2 + t) := by
      funext t; simp [B0579.dir]
    rw [hfun]
    have hcomp : HasDerivAt (fun t : ℝ => f (y.2 + t)) (deriv f y.2 * 1) 0 :=
      (hdf.comp (0 : ℝ) hlin).congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)
    rwa [mul_one] at hcomp
  exact hd1.unique hd2

private lemma tendsto_scaled_eta_sq {c R : ℝ} (hc : 0 < c) (hR : 0 < R) {h : ℝ → ℝ}
    (hh : Continuous h) (hsupp : ∀ u : ℝ, R < |u| → h u = 0) :
    Tendsto (fun n : ℕ =>
      ∫ y in B0579.cell c, (((n : ℝ) + 1)⁻¹ * h (y.2 / ((n : ℝ) + 1))) ^ 2) atTop (𝓝 0) := by
  obtain ⟨K0, hK0⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (-R) R) hh.continuousOn
  set K := max 0 K0
  have hK_nn : 0 ≤ K := le_max_left 0 K0
  have hh_bdd : ∀ u : ℝ, |h u| ≤ K := fun u => by
    by_cases hu : |u| ≤ R
    · exact (Real.norm_eq_abs _ ▸ hK0 u (abs_le.1 hu)).trans (le_max_right 0 K0)
    · rw [hsupp u (not_le.1 hu), abs_zero]; exact hK_nn
  have hle : ∀ n : ℕ,
      ∫ y in B0579.cell c, (((n : ℝ) + 1)⁻¹ * h (y.2 / ((n : ℝ) + 1))) ^ 2 ≤
        (2 * c * R * K ^ 2) * ((n : ℝ) + 1)⁻¹ := fun n => by
    set sn : ℝ := (n : ℝ) + 1
    have hsn : 0 < sn := by dsimp [sn]; positivity
    let fn : ℝ × ℝ → ℝ := fun y => (sn⁻¹ * h (y.2 / sn)) ^ 2
    let Box : Set (ℝ × ℝ) := Ico (-(c / 2)) (c / 2) ×ˢ Icc (-(R * sn)) (R * sn)
    have hBox_meas : MeasurableSet Box := measurableSet_Ico.prod measurableSet_Icc
    have hBox_sub : Box ⊆ B0579.cell c := prod_mono Subset.rfl (subset_univ _)
    have hBox_vol : volume Box = ENNReal.ofReal c * ENNReal.ofReal (2 * R * sn) := by
      dsimp [Box]
      rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, Real.volume_Icc]
      congr 2 <;> ring
    have hBox_fin : volume Box < ⊤ := by
      rw [hBox_vol]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
    have hBox_real : volume.real Box = c * (2 * R * sn) := by
      rw [Measure.real, hBox_vol, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le,
        ENNReal.toReal_ofReal (by positivity)]
    have hzero : ∀ y ∈ B0579.cell c \ Box, fn y = 0 := by
      rintro y ⟨hyc, hyn⟩
      have hnot : y.2 ∉ Icc (-(R * sn)) (R * sn) := fun h2 => hyn ⟨hyc.1, h2⟩
      have hgt : R * sn < |y.2| := by
        by_contra hle'; push Not at hle'; exact hnot (abs_le.1 hle')
      have hdiv : R < |y.2 / sn| := by
        rw [abs_div, abs_of_pos hsn, lt_div_iff₀ hsn]; exact hgt
      simp [fn, hsupp _ hdiv]
    have hfn_cont : Continuous fn :=
      (continuous_const.mul (hh.comp (continuous_snd.div_const sn))).pow 2
    have hfn_bdd : ∀ y : ℝ × ℝ, fn y ≤ (sn⁻¹ * K) ^ 2 := fun y => by
      dsimp [fn]
      have h1 : |sn⁻¹ * h (y.2 / sn)| ≤ sn⁻¹ * K := by
        rw [abs_mul, abs_of_pos (inv_pos.2 hsn)]
        exact mul_le_mul_of_nonneg_left (hh_bdd _) (inv_pos.2 hsn).le
      calc (sn⁻¹ * h (y.2 / sn)) ^ 2 = |sn⁻¹ * h (y.2 / sn)| ^ 2 := (sq_abs _).symm
        _ ≤ (sn⁻¹ * K) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    have hint_fn : IntegrableOn fn (B0579.cell c) volume := by
      have hm_l2 : MemLp (fun y : ℝ × ℝ => sn⁻¹ * h (y.2 / sn)) 2
          (volume.restrict (B0579.cell c)) := by
        refine memLp_cell_of_band (S := R * sn)
          (continuous_const.mul (hh.comp (continuous_snd.div_const sn))) fun y hy => ?_
        have hdiv : R < |y.2 / sn| := by
          rw [abs_div, abs_of_pos hsn, lt_div_iff₀ hsn]; exact hy
        simp [hsupp _ hdiv]
      exact hm_l2.integrable_sq
    have hint_ind : Integrable (Box.indicator (fun _ => (sn⁻¹ * K) ^ 2)) volume :=
      (integrableOn_const hBox_fin.ne).integrable_indicator hBox_meas
    change ∫ y in B0579.cell c, fn y ≤ _
    calc ∫ y in B0579.cell c, fn y
        ≤ ∫ y in B0579.cell c, Box.indicator (fun _ => (sn⁻¹ * K) ^ 2) y := by
          refine setIntegral_mono_on hint_fn hint_ind.integrableOn
            (B0579.measurableSet_cell c) fun y hyc => ?_
          by_cases hyB : y ∈ Box
          · rw [Set.indicator_of_mem hyB]; exact hfn_bdd y
          · rw [Set.indicator_of_notMem hyB, hzero y ⟨hyc, hyB⟩]
      _ ≤ ∫ y, Box.indicator (fun _ => (sn⁻¹ * K) ^ 2) y :=
          setIntegral_le_integral hint_ind
            (ae_of_all _ fun y => Set.indicator_nonneg (fun _ _ => sq_nonneg _) y)
      _ = (sn⁻¹ * K) ^ 2 * (c * (2 * R * sn)) := by
          rw [integral_indicator hBox_meas, setIntegral_const, hBox_real, smul_eq_mul, mul_comm]
      _ = (2 * c * R * K ^ 2) * sn⁻¹ := by field_simp [hsn.ne']
  have hlim : Tendsto (fun n : ℕ => (2 * c * R * K ^ 2) * ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    have h0 := (tendsto_const_nhds (x := 2 * c * R * K ^ 2)).mul
      (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add
        (tendsto_const_nhds (x := (1 : ℝ)))))
    rwa [mul_zero] at h0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => integral_nonneg fun _ => sq_nonneg _) hle

/-! #### 5c. Stream-primitive approximation of `IsFlatSpatialTest` -/

private lemma exists_stream_lift_approx {c T : ℝ} (hc : 0 < c)
    {ψ : ℝ → ℝ} (_hψ_sm : ContDiff ℝ ∞ ψ) (_hψ_cs : HasCompactSupport ψ)
    (_hψ_ts : tsupport ψ ⊆ Ioo 0 T)
    {φ : ℝ × ℝ → Fin 2 → ℝ} (hφ : IsFlatSpatialTest c φ) :
    ∃ (G : ℕ → ℝ × ℝ → ℝ) (φn : ℕ → ℝ × ℝ → Fin 2 → ℝ) (S_bound : ℕ → ℝ),
      (∀ n, ContDiff ℝ ∞ (G n)) ∧
      (∀ n, 0 < S_bound n) ∧
      (∀ n y, (2 * c < |y.1| ∨ S_bound n < |y.2|) → G n y = 0) ∧
      (∀ n, IsFlatSpatialTest c (φn n)) ∧
      (∀ n (α : ℝ → ℝ), ContDiff ℝ ∞ α → HasCompactSupport α → tsupport α ⊆ Ioo 0 T →
        ∀ s y, B0579.pd 1 (TailPeriodizeAux.qPeriodize c (prodSG α (G n)) s) y =
            α s * φn n y 0 ∧
          -B0579.pd 0 (TailPeriodizeAux.qPeriodize c (prodSG α (G n)) s) y =
            α s * φn n y 1) ∧
      Tendsto (fun n => ∫ y in B0579.cell c, ∑ i : Fin 2, (φn n y i - φ y i) ^ 2)
        atTop (𝓝 0) ∧
      (∀ j : Fin 2, Tendsto (fun n => ∫ y in B0579.cell c, ∑ i : Fin 2,
          (B0579.pd j (fun w => φn n w i) y - B0579.pd j (fun w => φ w i) y) ^ 2)
        atTop (𝓝 0)) := by
  have hφ_h1 : IsH1DivFreeTest c φ := isH1DivFreeTest_of_flatSpatial hφ
  obtain ⟨R0, hR0⟩ := hφ.bounded
  set R : ℝ := max 1 R0
  have hR_pos : 0 < R := lt_of_lt_of_le one_pos (le_max_left 1 R0)
  have hφ_band : ∀ (y : ℝ × ℝ) (i : Fin 2), R < |y.2| → φ y i = 0 :=
    fun y i hy => hR0 y i ((le_max_right 1 R0).trans_lt hy)
  have hqmean : ∀ η : ℝ, dfcQInt c (fun y => φ y 1) η = 0 := dfcQMeanZero c hc φ hφ_h1
  obtain ⟨hθ_sm, hθ_per, hθ_pd0, hθ_pd1⟩ := dfcPotentialFormulas c hc φ hφ_h1 hqmean
  set θ := dfcPotential c φ
  let m : ℝ → ℝ := fun η => c⁻¹ * dfcQInt c (fun y => φ y 0) η
  have hm_sm : ContDiff ℝ ∞ m :=
    contDiff_const.mul (dfcQPrimSmooth c hc (fun y => φ y 0) (hφ.smooth 0)).2
  have hm_band : ∀ η : ℝ, R < |η| → m η = 0 := fun η hη => by
    have h0 : (fun t : ℝ => φ (t, η) 0) = fun _ => 0 :=
      funext fun t => hφ_band (t, η) 0 hη
    change c⁻¹ * (∫ t in (-(c / 2))..(c / 2), φ (t, η) 0) = 0
    rw [h0, intervalIntegral.integral_zero, mul_zero]
  have hdm_band : ∀ η : ℝ, R < |η| → deriv m η = 0 := fun η hη => by
    have hopen : IsOpen {u : ℝ | R < |u|} := isOpen_lt continuous_const continuous_abs
    have hev : m =ᶠ[𝓝 η] 0 := Filter.eventually_of_mem (hopen.mem_nhds hη) hm_band
    rw [hev.deriv_eq]; simp
  have hθ_band : ∀ y : ℝ × ℝ, R < |y.2| → θ y = 0 := fun y hy => by
    have hprim0 : ∀ q : ℝ, dfcQPrim c (fun z => φ z 1) (q, y.2) = 0 := fun q => by
      have h0 : (fun t : ℝ => φ (t, y.2) 1) = fun _ => 0 :=
        funext fun t => hφ_band (t, y.2) 1 hy
      change (∫ t in (-(c / 2))..q, φ (t, y.2) 1) = 0
      rw [h0, intervalIntegral.integral_zero]
    have hint0 : dfcQInt c (dfcQPrim c (fun z => φ z 1)) y.2 = 0 := by
      have h0 : (fun q : ℝ => dfcQPrim c (fun z => φ z 1) (q, y.2)) = fun _ => 0 :=
        funext hprim0
      change (∫ q in (-(c / 2))..(c / 2), dfcQPrim c (fun z => φ z 1) (q, y.2)) = 0
      rw [h0, intervalIntegral.integral_zero]
    change -(dfcQPrim c (fun z => φ z 1) (y.1, y.2)) +
        c⁻¹ * dfcQInt c (dfcQPrim c (fun z => φ z 1)) y.2 = 0
    rw [hprim0 y.1, hint0]
    ring
  obtain ⟨hP_sm, hhd_P⟩ := contDiff_prim_1d hm_sm (-(R + 1))
  set P : ℝ → ℝ := fun u => ∫ t in (-(R + 1))..u, m t
  have hP_neg : ∀ u : ℝ, u ≤ -(R + 1) → P u = 0 := fun u hu => by
    dsimp [P]
    rw [intervalIntegral.integral_of_ge hu, neg_eq_zero]
    refine setIntegral_eq_zero_of_forall_eq_zero fun t ht => hm_band t ?_
    rw [abs_of_neg (by linarith [ht.2])]; linarith [ht.2]
  have hP_pos : ∀ u : ℝ, R + 1 ≤ u → P u = P (R + 1) := fun u hu => by
    dsimp only [P]
    have h1 := intervalIntegral.integral_add_adjacent_intervals
      (hm_sm.continuous.intervalIntegrable (μ := volume) (-(R + 1)) (R + 1))
      (hm_sm.continuous.intervalIntegrable (μ := volume) (R + 1) u)
    have h2 : (∫ t in (R + 1)..u, m t) = 0 := by
      rw [intervalIntegral.integral_of_le hu]
      refine setIntegral_eq_zero_of_forall_eq_zero fun t ht => hm_band t ?_
      rw [abs_of_pos (by linarith [ht.1])]; linarith [ht.1]
    rw [h2, add_zero] at h1
    exact h1.symm
  let sn : ℕ → ℝ := fun n => (n : ℝ) + 1
  let Mn : ℕ → ℝ → ℝ := fun n η => P η - P (η / sn n)
  let Θn : ℕ → ℝ × ℝ → ℝ := fun n y => θ y + Mn n y.2
  let Gn : ℕ → ℝ × ℝ → ℝ := fun n y => qPart c hc y.1 * Θn n y
  let φn : ℕ → ℝ × ℝ → Fin 2 → ℝ := fun n y =>
    ![φ y 0 - (sn n)⁻¹ * m (y.2 / sn n), φ y 1]
  let Sb : ℕ → ℝ := fun n => (R + 1) * sn n
  have hsn_pos : ∀ n : ℕ, 0 < sn n := fun n => by dsimp [sn]; positivity
  have hsn_ge1 : ∀ n : ℕ, 1 ≤ sn n := fun n => by dsimp [sn]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hMn_sm : ∀ n, ContDiff ℝ ∞ (Mn n) := fun n =>
    hP_sm.sub (hP_sm.comp (contDiff_id.div_const (sn n)))
  have hMn_der : ∀ n η, deriv (Mn n) η = m η - (sn n)⁻¹ * m (η / sn n) := fun n η => by
    have hd_div : HasDerivAt (fun x : ℝ => P (x / sn n)) (m (η / sn n) * (1 / sn n)) η :=
      ((hhd_P (η / sn n)).comp η ((hasDerivAt_id η).div_const (sn n))).congr_of_eventuallyEq
        (Eventually.of_forall fun _ => rfl)
    have hd : HasDerivAt (Mn n) (m η - m (η / sn n) * (1 / sn n)) η :=
      (hhd_P η).sub hd_div
    rw [hd.deriv]; ring
  have hMn_band : ∀ n η, Sb n < |η| → Mn n η = 0 := fun n η hη => by
    have hsn := hsn_pos n
    have hge1 := hsn_ge1 n
    rcases lt_or_ge η 0 with hneg | hnn
    · rw [abs_of_neg hneg] at hη
      have hdiv : η / sn n ≤ -(R + 1) := by
        rw [div_le_iff₀ hsn]; linarith
      have hle : η ≤ -(R + 1) := by nlinarith
      simp [Mn, hP_neg η hle, hP_neg _ hdiv]
    · rw [abs_of_nonneg hnn] at hη
      have hdiv : R + 1 ≤ η / sn n := by
        rw [le_div_iff₀ hsn]; linarith
      have hge : R + 1 ≤ η := by nlinarith
      simp [Mn, hP_pos η hge, hP_pos _ hdiv]
  have hΘn_sm : ∀ n, ContDiff ℝ ∞ (Θn n) := fun n =>
    hθ_sm.add ((hMn_sm n).comp contDiff_snd)
  have hΘn_per : ∀ n y, Θn n (y.1 + c, y.2) = Θn n y := fun n y => by
    dsimp [Θn]; rw [hθ_per y]
  have hΘn_int_shift : ∀ n (y : ℝ × ℝ) (k : ℤ),
      Θn n (y.1 + (k : ℝ) * c, y.2) = Θn n y := fun n y k => by
    induction k using Int.induction_on with
    | zero => simp
    | succ k ih =>
      have heq : (y.1 + (((k : ℤ) + 1 : ℤ) : ℝ) * c, y.2) =
          ((y.1 + ((k : ℤ) : ℝ) * c) + c, y.2) := by ext <;> push_cast <;> ring
      rw [heq, hΘn_per n (y.1 + ((k : ℤ) : ℝ) * c, y.2)]
      exact ih
    | pred k ih =>
      have heq : ((y.1 + ((-(k : ℤ) - 1 : ℤ) : ℝ) * c) + c, y.2) =
          (y.1 + ((-(k : ℤ) : ℤ) : ℝ) * c, y.2) := by ext <;> push_cast <;> ring
      rw [← hΘn_per n (y.1 + ((-(k : ℤ) - 1 : ℤ) : ℝ) * c, y.2), heq]
      exact ih
  have hΘn_pd0 : ∀ n y, B0579.pd 0 (Θn n) y = -φn n y 1 := fun n y => by
    have hadd : B0579.pd 0 (Θn n) y =
        B0579.pd 0 θ y + B0579.pd 0 (fun w : ℝ × ℝ => Mn n w.2) y := by
      have hd := (hasDerivAt_plane_dir hθ_sm 0 y).add
        (hasDerivAt_plane_dir ((hMn_sm n).comp contDiff_snd) 0 y)
      exact (hasDerivAt_plane_dir (hΘn_sm n) 0 y).unique hd
    rw [hadd, hθ_pd0 y, pd0_snd (hMn_sm n) y, add_zero]
    simp [φn]
  have hΘn_pd1 : ∀ n y, B0579.pd 1 (Θn n) y = φn n y 0 := fun n y => by
    have hadd : B0579.pd 1 (Θn n) y =
        B0579.pd 1 θ y + B0579.pd 1 (fun w : ℝ × ℝ => Mn n w.2) y := by
      have hd := (hasDerivAt_plane_dir hθ_sm 1 y).add
        (hasDerivAt_plane_dir ((hMn_sm n).comp contDiff_snd) 1 y)
      exact (hasDerivAt_plane_dir (hΘn_sm n) 1 y).unique hd
    rw [hadd, hθ_pd1 y, pd1_snd (hMn_sm n) y, hMn_der n y.2]
    dsimp [φn, m]; ring
  have hGn_sm : ∀ n, ContDiff ℝ ∞ (Gn n) := fun n =>
    ((contDiff_qPart hc).comp contDiff_fst).mul (hΘn_sm n)
  have hGn_supp : ∀ n y, (2 * c < |y.1| ∨ Sb n < |y.2|) → Gn n y = 0 := fun n y hy => by
    rcases hy with hq | hη
    · simp [Gn, qPart_eq_zero_of_abs hc hq.le]
    · have hR_lt : R < |y.2| := by
        have hge1 := hsn_ge1 n
        dsimp [Sb] at hη
        nlinarith
      simp [Gn, Θn, hθ_band y hR_lt, hMn_band n y.2 hη]
  have hφn_flat : ∀ n, IsFlatSpatialTest c (φn n) := fun n => by
    refine ⟨fun i => ?_, fun y i => ?_, ⟨Sb n, fun y i hy => ?_⟩, fun y => ?_⟩
    · fin_cases i
      · exact (hφ.smooth 0).sub
          (contDiff_const.mul (hm_sm.comp (contDiff_snd.div_const (sn n))))
      · exact hφ.smooth 1
    · fin_cases i <;> simp [φn, hφ.periodic y]
    · have hsn := hsn_pos n
      have hge1 := hsn_ge1 n
      have hR_lt : R < |y.2| := by dsimp [Sb] at hy; nlinarith
      fin_cases i
      · have hdiv : R < |y.2 / sn n| := by
          rw [abs_div, abs_of_pos hsn, lt_div_iff₀ hsn]
          dsimp [Sb] at hy; nlinarith
        simp [φn, hφ_band y 0 hR_lt, hm_band _ hdiv]
      · simp [φn, hφ_band y 1 hR_lt]
    · have hp0 : B0579.pd 0 (fun w => φn n w 0) y = B0579.pd 0 (fun w => φ w 0) y := by
        have hg_sm : ContDiff ℝ ∞ (fun u : ℝ => (sn n)⁻¹ * m (u / sn n)) :=
          contDiff_const.mul (hm_sm.comp (contDiff_id.div_const (sn n)))
        have hd := (hasDerivAt_plane_dir (hφ.smooth 0) 0 y).sub
          (hasDerivAt_plane_dir (hg_sm.comp contDiff_snd) 0 y)
        have heq : B0579.pd 0 (fun w => φn n w 0) y =
            B0579.pd 0 (fun w => φ w 0) y -
              B0579.pd 0 (fun w : ℝ × ℝ => (sn n)⁻¹ * m (w.2 / sn n)) y :=
          (hasDerivAt_plane_dir ((hφ.smooth 0).sub (hg_sm.comp contDiff_snd)) 0 y).unique hd
        have h0 : B0579.pd 0 (fun w : ℝ × ℝ => (sn n)⁻¹ * m (w.2 / sn n)) y = 0 :=
          pd0_snd hg_sm y
        rw [heq, h0, sub_zero]
      have hp1 : B0579.pd 1 (fun w => φn n w 1) y = B0579.pd 1 (fun w => φ w 1) y := rfl
      rw [hp0, hp1]
      exact hφ.divFree y
  have hper_eq : ∀ n (α : ℝ → ℝ), ContDiff ℝ ∞ α → HasCompactSupport α → tsupport α ⊆ Ioo 0 T →
      ∀ s y, B0579.pd 1 (TailPeriodizeAux.qPeriodize c (prodSG α (Gn n)) s) y =
          α s * φn n y 0 ∧
        -B0579.pd 0 (TailPeriodizeAux.qPeriodize c (prodSG α (Gn n)) s) y =
          α s * φn n y 1 := by
    intro n α hα_sm _ _ s y
    have hqper : TailPeriodizeAux.qPeriodize c (prodSG α (Gn n)) s =
        fun w : ℝ × ℝ => α s * Θn n w := by
      funext w
      unfold TailPeriodizeAux.qPeriodize prodSG
      have heq : (fun k : ℤ => α s * Gn n (w.1 + (k : ℝ) * c, w.2)) =
          fun k : ℤ => qPart c hc (w.1 + (k : ℝ) * c) * (α s * Θn n w) := by
        funext k
        dsimp [Gn]
        rw [hΘn_int_shift n w k]
        ring
      rw [heq, tsum_mul_right, tsum_qPart_shifts hc w.1, one_mul]
    rw [hqper]
    have hd1 : B0579.pd 1 (fun w : ℝ × ℝ => α s * Θn n w) y = α s * B0579.pd 1 (Θn n) y := by
      exact (hasDerivAt_plane_dir (contDiff_const.mul (hΘn_sm n)) 1 y).unique
        ((hasDerivAt_plane_dir (hΘn_sm n) 1 y).const_mul (α s))
    have hd0 : B0579.pd 0 (fun w : ℝ × ℝ => α s * Θn n w) y = α s * B0579.pd 0 (Θn n) y := by
      exact (hasDerivAt_plane_dir (contDiff_const.mul (hΘn_sm n)) 0 y).unique
        ((hasDerivAt_plane_dir (hΘn_sm n) 0 y).const_mul (α s))
    rw [hd1, hd0, hΘn_pd1 n y, hΘn_pd0 n y]
    exact ⟨rfl, by ring⟩
  have hconv_0 : Tendsto (fun n => ∫ y in B0579.cell c, ∑ i : Fin 2, (φn n y i - φ y i) ^ 2)
      atTop (𝓝 0) := by
    have heq : (fun n : ℕ => ∫ y in B0579.cell c, ∑ i : Fin 2, (φn n y i - φ y i) ^ 2) =
        fun n : ℕ => ∫ y in B0579.cell c, (((n : ℝ) + 1)⁻¹ * m (y.2 / ((n : ℝ) + 1))) ^ 2 := by
      funext n
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      dsimp only
      rw [Fin.sum_univ_two]
      dsimp [φn, sn]
      ring
    rw [heq]
    exact tendsto_scaled_eta_sq hc hR_pos hm_sm.continuous hm_band
  have hconv_pd : ∀ j : Fin 2, Tendsto (fun n => ∫ y in B0579.cell c, ∑ i : Fin 2,
      (B0579.pd j (fun w => φn n w i) y - B0579.pd j (fun w => φ w i) y) ^ 2) atTop (𝓝 0) := by
    intro j
    have hj01 : j = 0 ∨ j = 1 := by fin_cases j <;> simp
    rcases hj01 with rfl | rfl
    · have heq : (fun n : ℕ => ∫ y in B0579.cell c, ∑ i : Fin 2,
          (B0579.pd 0 (fun w => φn n w i) y - B0579.pd 0 (fun w => φ w i) y) ^ 2) =
          fun _ : ℕ => 0 := by
        funext n
        have hpt0 : ∀ y : B0579.Plane,
            (∑ i : Fin 2, (B0579.pd 0 (fun w => φn n w i) y -
              B0579.pd 0 (fun w => φ w i) y) ^ 2) = 0 := fun y => by
          rw [Fin.sum_univ_two]
          have hg_sm : ContDiff ℝ ∞ (fun u : ℝ => (sn n)⁻¹ * m (u / sn n)) :=
            contDiff_const.mul (hm_sm.comp (contDiff_id.div_const (sn n)))
          have hd := (hasDerivAt_plane_dir (hφ.smooth 0) 0 y).sub
            (hasDerivAt_plane_dir (hg_sm.comp contDiff_snd) 0 y)
          have hp0 : B0579.pd 0 (fun w => φn n w 0) y =
              B0579.pd 0 (fun w => φ w 0) y -
                B0579.pd 0 (fun w : ℝ × ℝ => (sn n)⁻¹ * m (w.2 / sn n)) y :=
            (hasDerivAt_plane_dir ((hφ.smooth 0).sub (hg_sm.comp contDiff_snd)) 0 y).unique hd
          have h0 : B0579.pd 0 (fun w : ℝ × ℝ => (sn n)⁻¹ * m (w.2 / sn n)) y = 0 :=
            pd0_snd hg_sm y
          have hp1 : B0579.pd 0 (fun w => φn n w 1) y = B0579.pd 0 (fun w => φ w 1) y := rfl
          rw [hp0, h0, sub_zero, sub_self, hp1, sub_self]
          norm_num
        simp_rw [hpt0]
        simp
      rw [heq]; exact tendsto_const_nhds
    · have hdm_cont : Continuous (deriv m) := (hm_sm.continuous_deriv (by simp))
      have hlim1 := tendsto_scaled_eta_sq hc hR_pos hdm_cont hdm_band
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim1
        (fun n => integral_nonneg fun y => Finset.sum_nonneg fun i _ => sq_nonneg _) (fun n => ?_)
      have hsn := hsn_pos n
      have hge1 := hsn_ge1 n
      have hpt : ∀ y : ℝ × ℝ,
          (∑ i : Fin 2, (B0579.pd 1 (fun w => φn n w i) y - B0579.pd 1 (fun w => φ w i) y) ^ 2) ≤
            (((n : ℝ) + 1)⁻¹ * deriv m (y.2 / ((n : ℝ) + 1))) ^ 2 := fun y => by
        rw [Fin.sum_univ_two]
        have hg_sm : ContDiff ℝ ∞ (fun u : ℝ => (sn n)⁻¹ * m (u / sn n)) :=
          contDiff_const.mul (hm_sm.comp (contDiff_id.div_const (sn n)))
        have hd := (hasDerivAt_plane_dir (hφ.smooth 0) 1 y).sub
          (hasDerivAt_plane_dir (hg_sm.comp contDiff_snd) 1 y)
        have hp0 : B0579.pd 1 (fun w => φn n w 0) y =
            B0579.pd 1 (fun w => φ w 0) y -
              B0579.pd 1 (fun w : ℝ × ℝ => (sn n)⁻¹ * m (w.2 / sn n)) y :=
          (hasDerivAt_plane_dir ((hφ.smooth 0).sub (hg_sm.comp contDiff_snd)) 1 y).unique hd
        have hg_der : deriv (fun u : ℝ => (sn n)⁻¹ * m (u / sn n)) y.2 =
            (sn n)⁻¹ * (deriv m (y.2 / sn n) * (1 / sn n)) := by
          have h1 : HasDerivAt (fun u : ℝ => (sn n)⁻¹ * m (u / sn n))
              ((sn n)⁻¹ * (deriv m (y.2 / sn n) * (1 / sn n))) y.2 :=
            ((((hm_sm.differentiable (by simp) _).hasDerivAt).comp y.2
              ((hasDerivAt_id y.2).div_const (sn n))).congr_of_eventuallyEq
                (Eventually.of_forall fun _ => rfl)).const_mul (sn n)⁻¹
          exact h1.deriv
        have h1 : B0579.pd 1 (fun w : ℝ × ℝ => (sn n)⁻¹ * m (w.2 / sn n)) y =
            deriv (fun u : ℝ => (sn n)⁻¹ * m (u / sn n)) y.2 := pd1_snd hg_sm y
        have hp1 : B0579.pd 1 (fun w => φn n w 1) y = B0579.pd 1 (fun w => φ w 1) y := rfl
        rw [hp0, h1, hg_der, hp1, sub_self]
        have hrew : (B0579.pd 1 (fun w => φ w 0) y -
            (sn n)⁻¹ * (deriv m (y.2 / sn n) * (1 / sn n)) -
            B0579.pd 1 (fun w => φ w 0) y) ^ 2 + 0 ^ 2 =
            ((sn n)⁻¹) ^ 2 * ((sn n)⁻¹ * deriv m (y.2 / sn n)) ^ 2 := by ring
        rw [hrew]
        have hsq1 : ((sn n)⁻¹) ^ 2 ≤ 1 :=
          pow_le_one₀ (inv_pos.2 hsn).le (inv_le_one_of_one_le₀ hge1)
        dsimp [sn] at hsq1 ⊢
        nlinarith [sq_nonneg (((n : ℝ) + 1)⁻¹ * deriv m (y.2 / ((n : ℝ) + 1)))]
      have hint_lhs : Integrable (fun y => ∑ i : Fin 2,
          (B0579.pd 1 (fun w => φn n w i) y - B0579.pd 1 (fun w => φ w i) y) ^ 2)
          (volume.restrict (B0579.cell c)) := by
        have hh1 := isH1DivFreeTest_of_flatSpatial (hφn_flat n)
        exact integrable_finsetSum _ fun i _ =>
          ((hh1.l2grad i 1).sub (hφ_h1.l2grad i 1)).integrable_sq
      have hint_rhs : Integrable (fun y =>
          (((n : ℝ) + 1)⁻¹ * deriv m (y.2 / ((n : ℝ) + 1))) ^ 2)
          (volume.restrict (B0579.cell c)) := by
        have hm_l2 : MemLp (fun y : ℝ × ℝ => ((n : ℝ) + 1)⁻¹ * deriv m (y.2 / ((n : ℝ) + 1)))
            2 (volume.restrict (B0579.cell c)) := by
          refine memLp_cell_of_band (S := R * sn n)
            (continuous_const.mul (hdm_cont.comp (continuous_snd.div_const ((n : ℝ) + 1))))
            fun y hy => ?_
          have hdiv : R < |y.2 / sn n| := by
            rw [abs_div, abs_of_pos hsn, lt_div_iff₀ hsn]; exact hy
          change (sn n)⁻¹ * deriv m (y.2 / sn n) = 0
          simp [hdm_band _ hdiv]
        exact hm_l2.integrable_sq
      exact integral_mono hint_lhs hint_rhs hpt
  exact ⟨Gn, φn, Sb, hGn_sm, fun n => mul_pos (by linarith) (hsn_pos n),
    hGn_supp, hφn_flat, hper_eq, hconv_0, hconv_pd⟩

/-! #### 5d. Tested inner-product equation and `HasWeakDerivTime` for `opJ k (Z0 s)` -/

private lemma integrableOn_early_paths {p : Params} {T M C_tr : ℝ}
    (hT : 0 < T) (hM : 0 ≤ M) (hC_tr : 0 ≤ C_tr)
    {g gq gη z₀ zq₀ zη₀ b_cut : CProf}
    (hg : IsCylSourceH1 p.c g gq gη)
    (hg_int : (∫⁻ s in Ioc 0 T, sliceH1Norm p.c g gq gη s) < ⊤)
    (hz : IsEarlyBorelRep p T g z₀ zq₀ zη₀)
    (hb_sm : StronglyMeasurable b_cut)
    (hb_le : ∀ s ∈ Ioc 0 T,
      cylSliceL2 p.c (fun y => b_cut (s, y)) ≤ ENNReal.ofReal C_tr * sliceH1Norm p.c z₀ zq₀ zη₀ s)
    (hbdd : ∀ᵐ s ∂volume, s ∈ Ioc 0 T → sliceH1Norm p.c z₀ zq₀ zη₀ s ≤ ENNReal.ofReal M) :
    IntegrableOn (cprofToLMH p.c z₀) (Ioo 0 T) volume ∧
      IntegrableOn (cprofToLMH p.c zq₀) (Ioo 0 T) volume ∧
      IntegrableOn (cprofToLMH p.c zη₀) (Ioo 0 T) volume ∧
      IntegrableOn (cprofToLMH p.c b_cut) (Ioo 0 T) volume ∧
      IntegrableOn (cprofToLMH p.c g) (Ioo 0 T) volume := by
  have _ : 0 ≤ M := hM
  have hvol_fin : volume (Ioo 0 T) < ⊤ := by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
  have hgood := ae_earlyGoodSlice hM hC_tr hg hg_int hz hb_sm hb_le hbdd
  have hfin_of_le : ∀ (W : CProf) (K : ℝ),
      (∀ᵐ s ∂volume, s ∈ Ioo 0 T → cylSliceL2 p.c (fun y => W (s, y)) ≤ ENNReal.ofReal K) →
      (∫⁻ s in Ioo 0 T, cylSliceL2 p.c (fun y => W (s, y))) < ⊤ := by
    intro W K hK
    calc ∫⁻ s in Ioo 0 T, cylSliceL2 p.c (fun y => W (s, y))
        ≤ ∫⁻ _s in Ioo 0 T, ENNReal.ofReal K :=
          lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioo).2 hK)
      _ = ENNReal.ofReal K * volume (Ioo 0 T) := by simp
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hvol_fin
  have _ : 0 < T := hT
  refine ⟨integrableOn_cprofToLMH hz.sm_z measurableSet_Ioo (hfin_of_le z₀ M ?_),
    integrableOn_cprofToLMH hz.sm_zq measurableSet_Ioo (hfin_of_le zq₀ M ?_),
    integrableOn_cprofToLMH hz.sm_zη measurableSet_Ioo (hfin_of_le zη₀ M ?_),
    integrableOn_cprofToLMH hb_sm measurableSet_Ioo (hfin_of_le b_cut (C_tr * M) ?_),
    integrableOn_cprofToLMH hg.sm_g measurableSet_Ioo ?_⟩
  · filter_upwards [hgood] with s hs hmem
    exact ((le_add_of_nonneg_right zero_le).trans (le_add_of_nonneg_right zero_le)).trans
      (hs hmem).bound_z
  · filter_upwards [hgood] with s hs hmem
    exact ((le_add_of_nonneg_left zero_le).trans (le_add_of_nonneg_right zero_le)).trans
      (hs hmem).bound_z
  · filter_upwards [hgood] with s hs hmem
    exact (le_add_of_nonneg_left zero_le).trans (hs hmem).bound_z
  · filter_upwards [hgood] with s hs hmem
    exact (hs hmem).bound_b
  · calc ∫⁻ s in Ioo 0 T, cylSliceL2 p.c (fun y => g (s, y))
        ≤ ∫⁻ s in Ioc 0 T, cylSliceL2 p.c (fun y => g (s, y)) :=
          lintegral_mono_set Ioo_subset_Ioc_self
      _ ≤ ∫⁻ s in Ioc 0 T, sliceH1Norm p.c g gq gη s :=
          lintegral_mono fun s =>
            (le_add_of_nonneg_right zero_le).trans (le_add_of_nonneg_right zero_le)
      _ < ⊤ := hg_int

private lemma integral_mul_inner_eq {c a b : ℝ} {w : ℝ → ℝ} {U : ℝ → LMH c}
    (hw_cont : Continuous w) (hw_cs : HasCompactSupport w)
    (hw_supp : ∀ s : ℝ, s ∉ Icc a b → w s = 0)
    (hU : IntegrableOn U (Icc a b) volume) (Y : LMH c) :
    (∫ s in Icc a b, w s * ⟪Y, U s⟫) = ⟪Y, ∫ s, w s • U s⟫ := by
  have hint_all : Integrable (fun s => w s • U s) volume := by
    have hIcc : IntegrableOn (fun s => w s • U s) (Icc a b) volume := by
      obtain ⟨M, hM⟩ := hw_cs.isCompact.exists_bound_of_continuousOn hw_cont.continuousOn
      have hM' : ∀ s : ℝ, ‖w s‖ ≤ max 0 M := fun s => by
        by_cases hs : s ∈ tsupport w
        · exact (hM s hs).trans (le_max_right 0 M)
        · rw [image_eq_zero_of_notMem_tsupport hs, norm_zero]; exact le_max_left 0 M
      exact (hU.norm.const_mul (max 0 M)).mono'
        (hw_cont.aestronglyMeasurable.restrict.smul hU.aestronglyMeasurable)
        (ae_of_all _ fun s => by
          rw [norm_smul]; exact mul_le_mul_of_nonneg_right (hM' s) (norm_nonneg _))
    have hpw : (Icc a b).piecewise (fun s => w s • U s) 0 = fun s => w s • U s := by
      funext s
      by_cases hs : s ∈ Icc a b
      · exact Set.piecewise_eq_of_mem _ _ _ hs
      · simp [Set.piecewise_eq_of_notMem _ _ _ hs, hw_supp s hs]
    rw [← hpw]
    exact Integrable.piecewise measurableSet_Icc hIcc integrableOn_zero
  have h1 : (∫ s, ⟪Y, w s • U s⟫) = ⟪Y, ∫ s, w s • U s⟫ :=
    (innerSL ℝ Y).integral_comp_comm hint_all
  rw [← h1]
  simp_rw [← real_inner_smul_right (x := Y)]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs => by
    rw [hw_supp s hs, zero_smul, inner_zero_right]

private lemma plane_zero_outside_box {Q S : ℝ} {G : ℝ × ℝ → ℝ}
    (hG_supp : ∀ y : ℝ × ℝ, (Q < |y.1| ∨ S < |y.2|) → G y = 0) :
    ∀ y : ℝ × ℝ, (max Q S + 1 < |y.1| ∨ max Q S + 1 < |y.2|) →
      G =ᶠ[𝓝 y] 0 := by
  intro y hy
  filter_upwards [Metric.ball_mem_nhds y one_pos] with w hw
  have hnorm : ‖w - y‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hw
  have h1 : |w.1 - y.1| < 1 := (Real.norm_eq_abs _ ▸ norm_fst_le (w - y)).trans_lt hnorm
  have h2 : |w.2 - y.2| < 1 := (Real.norm_eq_abs _ ▸ norm_snd_le (w - y)).trans_lt hnorm
  apply hG_supp
  rcases hy with hy1 | hy2
  · left
    have hsub := abs_sub_abs_le_abs_sub y.1 w.1
    rw [abs_sub_comm] at h1
    linarith [le_max_left Q S]
  · right
    have hsub := abs_sub_abs_le_abs_sub y.2 w.2
    rw [abs_sub_comm] at h2
    linarith [le_max_right Q S]

private lemma pd_eq_zero_of_eventuallyEq_zero {F : ℝ × ℝ → ℝ} {y : ℝ × ℝ}
    (hev : F =ᶠ[𝓝 y] 0) (j : Fin 2) :
    B0579.pd j F y = 0 := by
  unfold B0579.pd; rw [hev.fderiv_eq]; simp

private lemma tested_pair_of_prodSG {p : Params} {T M C_tr : ℝ}
    (hT : 0 < T) (hM : 0 ≤ M) (hC_tr : 0 ≤ C_tr)
    {g gq gη z₀ zq₀ zη₀ : CProf}
    (hg : IsCylSourceH1 p.c g gq gη)
    (hg_int : (∫⁻ s in Ioc 0 T, sliceH1Norm p.c g gq gη s) < ⊤)
    (hz : IsEarlyBorelRep p T g z₀ zq₀ zη₀)
    (hb_le : ∀ s ∈ Ioc 0 T,
      cylSliceL2 p.c (fun y => bCut p T z₀ zq₀ zη₀ (s, y)) ≤
        ENNReal.ofReal C_tr * sliceH1Norm p.c z₀ zq₀ zη₀ s)
    (hbdd : ∀ᵐ s ∂volume, s ∈ Ioc 0 T → sliceH1Norm p.c z₀ zq₀ zη₀ s ≤ ENNReal.ofReal M)
    {ψ : ℝ → ℝ} (hψ_sm : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_ts : tsupport ψ ⊆ Ioo 0 T)
    {Q S : ℝ} (hQ : 0 < Q) (_hS : 0 < S)
    {G : ℝ × ℝ → ℝ} (hG_sm : ContDiff ℝ ∞ G)
    (hG_supp : ∀ y : ℝ × ℝ, (Q < |y.1| ∨ S < |y.2|) → G y = 0)
    {φ : ℝ × ℝ → Fin 2 → ℝ} (hφ : IsFlatSpatialTest p.c φ)
    (hper_eq : ∀ (α : ℝ → ℝ), ContDiff ℝ ∞ α → HasCompactSupport α → tsupport α ⊆ Ioo 0 T →
      ∀ s y, B0579.pd 1 (TailPeriodizeAux.qPeriodize p.c (prodSG α G) s) y =
          α s * φ y 0 ∧
        -B0579.pd 0 (TailPeriodizeAux.qPeriodize p.c (prodSG α G) s) y =
          α s * φ y 1) :
    let hφ_h1 := isH1DivFreeTest_of_flatSpatial hφ
    let Z0 := cprofToLMH p.c z₀
    let Zq0 := cprofToLMH p.c zq₀
    let Zη0 := cprofToLMH p.c zη₀
    let B_path := cprofToLMH p.c (bCut p T z₀ zq₀ zη₀)
    let G_path := cprofToLMH p.c g
    (⟪toLMH (vecRe φ) (vecRe_cellL2 hφ_h1.l2), ∫ s, deriv ψ s • Z0 s⟫ =
      p.ν * (⟪toLMH (vecRe fun y i => B0579.pd 0 (fun w => φ w i) y)
                (vecRe_cellL2 fun i => hφ_h1.l2grad i 0), ∫ s, ψ s • Zq0 s⟫ +
             ⟪toLMH (vecRe fun y i => B0579.pd 1 (fun w => φ w i) y)
                (vecRe_cellL2 fun i => hφ_h1.l2grad i 1), ∫ s, ψ s • Zη0 s⟫) +
        ⟪toLMH (vecRe φ) (vecRe_cellL2 hφ_h1.l2), ∫ s, ψ s • B_path s⟫ -
        ⟪toLMH (vecRe φ) (vecRe_cellL2 hφ_h1.l2), ∫ s, ψ s • G_path s⟫) ∧
    (⟪toLMH (vecIm φ) (vecIm_cellL2 hφ_h1.l2), ∫ s, deriv ψ s • Z0 s⟫ =
      p.ν * (⟪toLMH (vecIm fun y i => B0579.pd 0 (fun w => φ w i) y)
                (vecIm_cellL2 fun i => hφ_h1.l2grad i 0), ∫ s, ψ s • Zq0 s⟫ +
             ⟪toLMH (vecIm fun y i => B0579.pd 1 (fun w => φ w i) y)
                (vecIm_cellL2 fun i => hφ_h1.l2grad i 1), ∫ s, ψ s • Zη0 s⟫) +
        ⟪toLMH (vecIm φ) (vecIm_cellL2 hφ_h1.l2), ∫ s, ψ s • B_path s⟫ -
        ⟪toLMH (vecIm φ) (vecIm_cellL2 hφ_h1.l2), ∫ s, ψ s • G_path s⟫) := by
  intro hφ_h1 Z0 Zq0 Zη0 B_path G_path
  have hc : 0 < p.c := p.c_pos
  set b_cut := bCut p T z₀ zq₀ zη₀
  have hb_sm : StronglyMeasurable b_cut := stronglyMeasurable_bCut p T hz.sm_z hz.sm_zq hz.sm_zη
  have hb_per : QPeriodic p.c b_cut := qPeriodic_bCut p T hz.per_z hz.per_zq hz.per_zη
  by_cases hne : (tsupport ψ).Nonempty
  · let a : ℝ := sInf (tsupport ψ)
    let b : ℝ := sSup (tsupport ψ)
    have ha_mem : a ∈ tsupport ψ := hψ_cs.isCompact.sInf_mem hne
    have hb_mem : b ∈ tsupport ψ := hψ_cs.isCompact.sSup_mem hne
    have ha_Ioo : a ∈ Ioo 0 T := hψ_ts ha_mem
    have hb_Ioo : b ∈ Ioo 0 T := hψ_ts hb_mem
    have ha_pos : 0 < a := ha_Ioo.1
    have hab : a ≤ b := csInf_le hψ_cs.isCompact.bddBelow hb_mem
    have hb_ltT : b < T := hb_Ioo.2
    have hIcc_sub : Icc a b ⊆ Ioo 0 T := fun s hs => ⟨lt_of_lt_of_le ha_pos hs.1, hs.2.trans_lt hb_ltT⟩
    have hψ_out : ∀ s : ℝ, s ∉ Icc a b → ψ s = 0 := fun s hs =>
      image_eq_zero_of_notMem_tsupport fun hmem =>
        hs ⟨csInf_le hψ_cs.isCompact.bddBelow hmem, le_csSup hψ_cs.isCompact.bddAbove hmem⟩
    have hdψ_ts : tsupport (deriv ψ) ⊆ tsupport ψ := tsupport_deriv_subset
    have hdψ_out : ∀ s : ℝ, s ∉ Icc a b → deriv ψ s = 0 := fun s hs =>
      image_eq_zero_of_notMem_tsupport fun hmem =>
        hs ⟨csInf_le hψ_cs.isCompact.bddBelow (hdψ_ts hmem),
          le_csSup hψ_cs.isCompact.bddAbove (hdψ_ts hmem)⟩
    -- Build `Φ = prodSG ψ G` and `Ψ = ![cpd 2 Φ, -cpd 1 Φ]`
    have hdψ_sm : ContDiff ℝ ∞ (deriv ψ) := (contDiff_infty_iff_deriv.1 hψ_sm).2
    have hnegψ_sm : ContDiff ℝ ∞ (-ψ) := hψ_sm.neg
    obtain ⟨hΦ_test, hΦ_ts⟩ := isCoordTest_prodSG hψ_sm hψ_cs hψ_ts hG_sm hG_supp
    obtain ⟨hΦ'_test, _⟩ := isCoordTest_prodSG hdψ_sm
      hψ_cs.deriv (hdψ_ts.trans hψ_ts) hG_sm hG_supp
    set Φ := prodSG ψ G
    set Φ' := prodSG (deriv ψ) G
    let Ψ : Coord → Fin 2 → ℝ := fun x => ![cpd 2 Φ x, -cpd 1 Φ x]
    have hΨ_test : IsPlanarSolTest Ψ :=
      ⟨fun i => by
        fin_cases i
        · exact planarTest_isCoordTest_partial hΦ_test (cdir 2)
        · exact planarTest_isCoordTest_neg (planarTest_isCoordTest_partial hΦ_test (cdir 1)),
        fun x => planarTest_div_free hΦ_test.smooth x⟩
    have hcpd_ts : ∀ k : Fin 3, tsupport (cpd k Φ) ⊆ tsupport Φ := fun k => by
      refine closure_minimal (fun x hx => ?_) isClosed_closure
      by_contra hnot
      rw [notMem_tsupport_iff_eventuallyEq] at hnot
      apply Function.mem_support.1 hx
      unfold cpd
      rw [hnot.fderiv_eq]
      simp
    have hΨ_supp : ∀ i : Fin 2, tsupport (fun x => Ψ x i) ⊆ Ioo 0 T ×ˢ univ := fun i => by
      fin_cases i <;> dsimp only [Ψ]
      · exact (hcpd_ts 2).trans hΦ_ts
      · change tsupport (-cpd 1 Φ) ⊆ _
        rw [tsupport_neg]
        exact (hcpd_ts 1).trans hΦ_ts
    have hΨ_eq : ∀ x : Coord,
        Ψ x 0 = prodSG ψ (B0579.pd 1 G) x ∧ Ψ x 1 = prodSG (-ψ) (B0579.pd 0 G) x := fun x => by
      refine ⟨cpd_succ_prodSG hψ_sm hG_sm 1 x, ?_⟩
      change -cpd (0 : Fin 2).succ (prodSG ψ G) x = (-ψ x.1) * B0579.pd 0 G x.2
      rw [cpd_succ_prodSG hψ_sm hG_sm 0 x]; ring
    have hpdG_sm : ∀ j : Fin 2, ContDiff ℝ ∞ (B0579.pd j G) := fun j =>
      ((contDiff_infty_iff_fderiv.1 hG_sm).2).clm_apply contDiff_const
    have hcpd0_Ψ0 : cpd 0 (fun x => Ψ x 0) = cpd 2 Φ' := by
      funext x
      have hf : (fun y => Ψ y 0) = prodSG ψ (B0579.pd 1 G) := funext fun y => (hΨ_eq y).1
      change cpd 0 (fun y => Ψ y 0) x = cpd (1 : Fin 2).succ (prodSG (deriv ψ) G) x
      rw [hf, cpd0_prodSG hψ_sm (hpdG_sm 1) x, cpd_succ_prodSG hdψ_sm hG_sm 1 x]
    have hcpd0_Ψ1 : cpd 0 (fun x => Ψ x 1) = fun x => -cpd 1 Φ' x := by
      funext x
      have hf : (fun y => Ψ y 1) = prodSG (-ψ) (B0579.pd 0 G) := funext fun y => (hΨ_eq y).2
      have hder_neg : deriv (-ψ) x.1 = -deriv ψ x.1 := deriv.neg
      change cpd 0 (fun y => Ψ y 1) x = -cpd (0 : Fin 2).succ (prodSG (deriv ψ) G) x
      rw [hf, cpd0_prodSG hnegψ_sm (hpdG_sm 0) x, hder_neg,
        cpd_succ_prodSG hdψ_sm hG_sm 0 x]
      ring
    -- Box vanishing on `Icc a b × [-R_box, R_box] × [-R_box, R_box]`
    set R_box : ℝ := max Q S + 1
    have hR_box_pos : 0 < R_box := by dsimp [R_box]; positivity
    have hev0_G := plane_zero_outside_box hG_supp
    have hbox_Ψ : ∀ (i : Fin 2) (x : Coord),
        (x.1 ∉ Icc a b ∨ R_box < |x.2.1| ∨ R_box < |x.2.2|) →
          Ψ x i = 0 ∧ cpd 0 (fun y => Ψ y i) x = 0 ∧
            cpd 1 (fun y => cpd 1 (fun z => Ψ z i) y) x = 0 ∧
            cpd 2 (fun y => cpd 2 (fun z => Ψ z i) y) x = 0 := by
      intro i x hx
      have hi01 : i = 0 ∨ i = 1 := by fin_cases i <;> simp
      have hΨ_i_sm : ContDiff ℝ ∞ (fun y => Ψ y i) := (hΨ_test.smooth i).smooth
      have hpd2_eq : ∀ j : Fin 2, cpd j.succ (fun y => cpd j.succ (fun z => Ψ z i) y) x =
          (if i = 0 then ψ x.1 * B0579.pd j (B0579.pd j (B0579.pd 1 G)) x.2
            else -ψ x.1 * B0579.pd j (B0579.pd j (B0579.pd 0 G)) x.2) := fun j => by
        rcases hi01 with rfl | rfl
        · have hf1 : (fun z => Ψ z 0) = prodSG ψ (B0579.pd 1 G) := funext fun z => (hΨ_eq z).1
          have hf2 : (fun y => cpd j.succ (prodSG ψ (B0579.pd 1 G)) y) =
              prodSG ψ (B0579.pd j (B0579.pd 1 G)) :=
            funext fun y => cpd_succ_prodSG hψ_sm (hpdG_sm 1) j y
          have hpdj1 : ContDiff ℝ ∞ (B0579.pd j (B0579.pd 1 G)) :=
            ((contDiff_infty_iff_fderiv.1 (hpdG_sm 1)).2).clm_apply contDiff_const
          rw [hf1, hf2, cpd_succ_prodSG hψ_sm hpdj1 j x]
          simp
        · have hf1 : (fun z => Ψ z 1) = prodSG (-ψ) (B0579.pd 0 G) := funext fun z => (hΨ_eq z).2
          have hf2 : (fun y => cpd j.succ (prodSG (-ψ) (B0579.pd 0 G)) y) =
              prodSG (-ψ) (B0579.pd j (B0579.pd 0 G)) :=
            funext fun y => cpd_succ_prodSG hnegψ_sm (hpdG_sm 0) j y
          have hpdj0 : ContDiff ℝ ∞ (B0579.pd j (B0579.pd 0 G)) :=
            ((contDiff_infty_iff_fderiv.1 (hpdG_sm 0)).2).clm_apply contDiff_const
          rw [hf1, hf2, cpd_succ_prodSG hnegψ_sm hpdj0 j x]
          simp
      rcases hx with hs_out | hxy_out
      · have hψ0 := hψ_out x.1 hs_out
        have hdψ0 := hdψ_out x.1 hs_out
        refine ⟨?_, ?_, ?_, ?_⟩
        · rcases hi01 with rfl | rfl
          · rw [(hΨ_eq x).1]; simp [prodSG, hψ0]
          · rw [(hΨ_eq x).2]; simp [prodSG, hψ0]
        · rcases hi01 with rfl | rfl
          · rw [hcpd0_Ψ0]
            change cpd (1 : Fin 2).succ (prodSG (deriv ψ) G) x = 0
            rw [cpd_succ_prodSG hdψ_sm hG_sm 1 x, hdψ0, zero_mul]
          · rw [hcpd0_Ψ1]
            change -cpd (0 : Fin 2).succ (prodSG (deriv ψ) G) x = 0
            rw [cpd_succ_prodSG hdψ_sm hG_sm 0 x, hdψ0, zero_mul, neg_zero]
        · exact (hpd2_eq 0).trans (by rcases hi01 with rfl | rfl <;> simp [hψ0])
        · exact (hpd2_eq 1).trans (by rcases hi01 with rfl | rfl <;> simp [hψ0])
      · have hev : G =ᶠ[𝓝 x.2] 0 := hev0_G x.2 hxy_out
        have hev_pd : ∀ k : Fin 2, B0579.pd k G =ᶠ[𝓝 x.2] 0 := fun k => by
          obtain ⟨U, hU0, hU_open, hxyU⟩ := eventually_nhds_iff.1 hev
          exact Filter.eventually_of_mem (hU_open.mem_nhds hxyU) fun w hw =>
            pd_eq_zero_of_eventuallyEq_zero
              (Filter.eventually_of_mem (hU_open.mem_nhds hw) hU0) k
        have hev_pd2 : ∀ j k : Fin 2, B0579.pd j (B0579.pd k G) =ᶠ[𝓝 x.2] 0 := fun j k => by
          obtain ⟨U, hU0, hU_open, hxyU⟩ := eventually_nhds_iff.1 (hev_pd k)
          exact Filter.eventually_of_mem (hU_open.mem_nhds hxyU) fun w hw =>
            pd_eq_zero_of_eventuallyEq_zero
              (Filter.eventually_of_mem (hU_open.mem_nhds hw) hU0) j
        refine ⟨?_, ?_, ?_, ?_⟩
        · rcases hi01 with rfl | rfl
          · rw [(hΨ_eq x).1]; simp [prodSG, pd_eq_zero_of_eventuallyEq_zero hev 1]
          · rw [(hΨ_eq x).2]; simp [prodSG, pd_eq_zero_of_eventuallyEq_zero hev 0]
        · rcases hi01 with rfl | rfl
          · rw [hcpd0_Ψ0]
            change cpd (1 : Fin 2).succ (prodSG (deriv ψ) G) x = 0
            rw [cpd_succ_prodSG hdψ_sm hG_sm 1 x,
              pd_eq_zero_of_eventuallyEq_zero hev 1, mul_zero]
          · rw [hcpd0_Ψ1]
            change -cpd (0 : Fin 2).succ (prodSG (deriv ψ) G) x = 0
            rw [cpd_succ_prodSG hdψ_sm hG_sm 0 x,
              pd_eq_zero_of_eventuallyEq_zero hev 0, mul_zero, neg_zero]
        · exact (hpd2_eq 0).trans (by
            rcases hi01 with rfl | rfl <;> simp [pd_eq_zero_of_eventuallyEq_zero (hev_pd2 0 _) 0])
        · exact (hpd2_eq 1).trans (by
            rcases hi01 with rfl | rfl <;> simp [pd_eq_zero_of_eventuallyEq_zero (hev_pd2 1 _) 1])
    -- Compute `qPeriodize` of `Ψ`, `cpd 0 Ψ`, and `cpd j.succ (cpd j.succ Ψ)`
    have hq_Ψ : ∀ s y i, TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y =
        ψ s * φ y i := by
      intro s y i
      have hp := hper_eq ψ hψ_sm hψ_cs hψ_ts s y
      have hi01 : i = 0 ∨ i = 1 := by fin_cases i <;> simp
      rcases hi01 with rfl | rfl
      · change TailPeriodizeAux.qPeriodize p.c (cpd (1 : Fin 2).succ Φ) s y = ψ s * φ y 0
        rw [← TailPeriodizeAux.pd_qPeriodize hc hΦ_test s 1 y]
        exact hp.1
      · have hneg : TailPeriodizeAux.qPeriodize p.c (fun x => -cpd (0 : Fin 2).succ Φ x) s y =
            -TailPeriodizeAux.qPeriodize p.c (cpd (0 : Fin 2).succ Φ) s y := by
          unfold TailPeriodizeAux.qPeriodize; exact tsum_neg
        change TailPeriodizeAux.qPeriodize p.c (fun x => -cpd (0 : Fin 2).succ Φ x) s y = ψ s * φ y 1
        rw [hneg, ← TailPeriodizeAux.pd_qPeriodize hc hΦ_test s 0 y]
        exact hp.2
    have hq_cpd0 : ∀ s y i, TailPeriodizeAux.qPeriodize p.c (cpd 0 (fun x => Ψ x i)) s y =
        deriv ψ s * φ y i := by
      intro s y i
      have hp := hper_eq (deriv ψ) hdψ_sm hψ_cs.deriv (hdψ_ts.trans hψ_ts) s y
      have hi01 : i = 0 ∨ i = 1 := by fin_cases i <;> simp
      rcases hi01 with rfl | rfl
      · rw [hcpd0_Ψ0]
        change TailPeriodizeAux.qPeriodize p.c (cpd (1 : Fin 2).succ Φ') s y = deriv ψ s * φ y 0
        rw [← TailPeriodizeAux.pd_qPeriodize hc hΦ'_test s 1 y]
        exact hp.1
      · rw [hcpd0_Ψ1]
        have hneg : TailPeriodizeAux.qPeriodize p.c (fun x => -cpd (0 : Fin 2).succ Φ' x) s y =
            -TailPeriodizeAux.qPeriodize p.c (cpd (0 : Fin 2).succ Φ') s y := by
          unfold TailPeriodizeAux.qPeriodize; exact tsum_neg
        change TailPeriodizeAux.qPeriodize p.c (fun x => -cpd (0 : Fin 2).succ Φ' x) s y = deriv ψ s * φ y 1
        rw [hneg, ← TailPeriodizeAux.pd_qPeriodize hc hΦ'_test s 0 y]
        exact hp.2
    have hq_lap : ∀ (j : Fin 2) s y i,
        TailPeriodizeAux.qPeriodize p.c
          (cpd j.succ (fun w => cpd j.succ (fun z => Ψ z i) w)) s y =
          ψ s * B0579.pd j (B0579.pd j (fun w => φ w i)) y := by
      intro j s y i
      have ht1 : IsCoordTest (fun z => Ψ z i) := hΨ_test.smooth i
      have ht2 : IsCoordTest (cpd j.succ (fun z => Ψ z i)) :=
        planarTest_isCoordTest_partial ht1 (cdir j.succ)
      rw [← TailPeriodizeAux.pd_qPeriodize hc ht2 s j y]
      have hfn : TailPeriodizeAux.qPeriodize p.c (cpd j.succ (fun z => Ψ z i)) s =
          B0579.pd j (TailPeriodizeAux.qPeriodize p.c (fun z => Ψ z i) s) :=
        funext fun w => (TailPeriodizeAux.pd_qPeriodize hc ht1 s j w).symm
      have hfn0 : TailPeriodizeAux.qPeriodize p.c (fun z => Ψ z i) s =
          fun w => ψ s * φ w i := funext fun w => hq_Ψ s w i
      rw [hfn, hfn0]
      have hsm1 : ContDiff ℝ ∞ (fun w => φ w i) := hφ.smooth i
      have hsm2 : ContDiff ℝ ∞ (B0579.pd j (fun w => φ w i)) :=
        ((contDiff_infty_iff_fderiv.1 hsm1).2).clm_apply contDiff_const
      have hmul1 : B0579.pd j (fun w => ψ s * φ w i) =
          fun w => ψ s * B0579.pd j (fun u => φ u i) w :=
        funext fun w => (hasDerivAt_plane_dir (contDiff_const.mul hsm1) j w).unique
          ((hasDerivAt_plane_dir hsm1 j w).const_mul (ψ s))
      rw [hmul1]
      exact (hasDerivAt_plane_dir (contDiff_const.mul hsm2) j y).unique
        ((hasDerivAt_plane_dir hsm2 j y).const_mul (ψ s))
    -- Apply `hz.equation` and unfold to `Icc a b`
    obtain ⟨hInt_z_mt, hInt_bv, hInt_g, heq_pde⟩ := hz.equation Ψ hΨ_test hΨ_supp
    have hb_ae_eq : cdot (flatBv p.train z₀ zq₀ zη₀) Ψ = cdot b_cut Ψ := by
      funext x
      by_cases hs : x.1 ∈ Icc a b
      · have hs_oc : x.1 ∈ Ioc 0 T := Ioo_subset_Ioc_self (hIcc_sub hs)
        simp [cdot, b_cut, bCut, hs_oc]
      · have h0 := (hbox_Ψ 0 x (Or.inl hs)).1
        have h1 := (hbox_Ψ 1 x (Or.inl hs)).1
        simp [cdot, Fin.sum_univ_two, h0, h1]
    rw [hb_ae_eq] at hInt_bv heq_pde
    obtain ⟨hZ0_int, hZq0_int, hZη0_int, hB_int, hG_int⟩ :=
      integrableOn_early_paths hT hM hC_tr hg hg_int hz hb_sm hb_le hbdd
    have hgood := ae_earlyGoodSlice hM hC_tr hg hg_int hz hb_sm hb_le hbdd
    -- Local `L¹(Icc a b; L²(cell))` finiteness for `z₀`, `b_cut`, `g`
    have hloc_of : ∀ {W : CProf} (hW_sm : StronglyMeasurable W)
        (hW_int : IntegrableOn (cprofToLMH p.c W) (Ioo 0 T) volume)
        (hW_l2 : ∀ᵐ s ∂volume, s ∈ Ioo 0 T →
          MemLp (fun y => W (s, y)) 2 (volume.restrict (B0579.cell p.c))) (i : Fin 2),
        (∫⁻ s in Icc a b,
          eLpNorm (fun y => W (s, y) i) 2 (volume.restrict (B0579.cell p.c))) < ⊤ := by
      intro W _ hW_int hW_l2 i
      have hIcc_int : IntegrableOn (cprofToLMH p.c W) (Icc a b) volume :=
        hW_int.mono_set hIcc_sub
      calc ∫⁻ s in Icc a b, eLpNorm (fun y => W (s, y) i) 2 (volume.restrict (B0579.cell p.c))
          ≤ ∫⁻ s in Icc a b, cylSliceL2 p.c (fun y => W (s, y)) := by
            refine lintegral_mono fun s => eLpNorm_mono_enorm fun y => ?_
            rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
            exact_mod_cast PiLp.norm_apply_le (W (s, y)) i
        _ = ∫⁻ s in Icc a b, ‖cprofToLMH p.c W s‖ₑ := by
            refine setLIntegral_congr_fun_ae measurableSet_Icc ?_
            filter_upwards [hW_l2] with s hs hmem
            rw [← ofReal_norm_cprofToLMH (hs (hIcc_sub hmem)),
              ← Real.enorm_eq_ofReal (norm_nonneg _), enorm_norm]
        _ < ⊤ := hIcc_int.2
    have hmem_z : ∀ᵐ s ∂volume, s ∈ Ioo 0 T →
        MemLp (fun y => z₀ (s, y)) 2 (volume.restrict (B0579.cell p.c)) := by
      filter_upwards [hgood] with s hs hmem; exact (hs hmem).memL2_z
    have hmem_b : ∀ᵐ s ∂volume, s ∈ Ioo 0 T →
        MemLp (fun y => b_cut (s, y)) 2 (volume.restrict (B0579.cell p.c)) := by
      filter_upwards [hgood] with s hs hmem; exact (hs hmem).memL2_b
    have hmem_g : ∀ᵐ s ∂volume, s ∈ Ioo 0 T →
        MemLp (fun y => g (s, y)) 2 (volume.restrict (B0579.cell p.c)) := by
      filter_upwards [hgood] with s hs hmem; exact (hs hmem).memL2_g
    -- Unfold each component integral via `integrable_and_integral_coord_eq_cell_qPeriodize`
    have hunfold : ∀ (W : CProf) (hW_sm : StronglyMeasurable W) (hW_per : QPeriodic p.c W)
        (hW_loc : ∀ i : Fin 2, (∫⁻ s in Icc a b,
          eLpNorm (fun y => W (s, y) i) 2 (volume.restrict (B0579.cell p.c))) < ⊤)
        (A : Fin 2 → Coord → ℝ) (hA_cont : ∀ i, Continuous (A i))
        (hA_supp : ∀ i x, (x.1 ∉ Icc a b ∨ R_box < |x.2.1| ∨ R_box < |x.2.2|) → A i x = 0),
        (∀ i, Integrable (fun x : Coord => W x i * (A i x : ℂ)) volume) ∧
        (∫ x : Coord, ∑ i : Fin 2, W x i * (A i x : ℂ)) =
          ∫ s in Icc a b, ∑ i : Fin 2,
            ∫ y in B0579.cell p.c, W (s, y) i *
              (TailPeriodizeAux.qPeriodize p.c (A i) s y : ℂ) := by
      intro W hW_sm hW_per hW_loc A hA_cont hA_supp
      have hcomp : ∀ i : Fin 2,
          Integrable (fun x : Coord => W x i * (A i x : ℂ)) volume ∧
          IntegrableOn (fun x : Coord =>
              W x i * (TailPeriodizeAux.qPeriodize p.c (A i) x.1 x.2 : ℂ))
            (Icc a b ×ˢ B0579.cell p.c) volume ∧
          (∫ x : Coord, W x i * (A i x : ℂ)) =
            ∫ s in Icc a b, ∫ y in B0579.cell p.c, W (s, y) i *
              (TailPeriodizeAux.qPeriodize p.c (A i) s y : ℂ) := fun i =>
        TailPeriodizeAux.integrable_and_integral_coord_eq_cell_qPeriodize hc ha_pos hab hR_box_pos
          (((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable
            hW_sm).aestronglyMeasurable)
          (hW_per.mono fun _ hx => congrArg (fun v : CMerid => v i) hx)
          (hW_loc i) (hA_cont i) (hA_supp i)
      have hs_int : ∀ i : Fin 2, IntegrableOn
          (fun s : ℝ => ∫ y in B0579.cell p.c, W (s, y) i *
            (TailPeriodizeAux.qPeriodize p.c (A i) s y : ℂ)) (Icc a b) volume := fun i => by
        have hc_i := (hcomp i).2.1
        have hp : Integrable (fun x : Coord =>
            W x i * (TailPeriodizeAux.qPeriodize p.c (A i) x.1 x.2 : ℂ))
            ((volume.restrict (Icc a b)).prod (volume.restrict (B0579.cell p.c))) := by
          rwa [Measure.prod_restrict, ← Measure.volume_eq_prod]
        exact hp.integral_prod_left
      refine ⟨fun i => (hcomp i).1, ?_⟩
      rw [integral_finsetSum _ fun i _ => (hcomp i).1,
        integral_finsetSum _ fun i _ => hs_int i]
      exact Finset.sum_congr rfl fun i _ => (hcomp i).2.2
    -- Apply `hunfold` to `b_cut`, `g`, and the three parts of `meridTranspose`
    have hu_b := hunfold b_cut hb_sm hb_per
      (hloc_of hb_sm hB_int hmem_b) (fun i x => Ψ x i)
      (fun i => (hΨ_test.smooth i).smooth.continuous)
      (fun i x hx => (hbox_Ψ i x hx).1)
    have hu_g := hunfold g hg.sm_g hg.periodic_g
      (hloc_of hg.sm_g hG_int hmem_g) (fun i x => Ψ x i)
      (fun i => (hΨ_test.smooth i).smooth.continuous)
      (fun i x hx => (hbox_Ψ i x hx).1)
    have hu_z0 := hunfold z₀ hz.sm_z hz.per_z
      (hloc_of hz.sm_z hZ0_int hmem_z) (fun i x => -cpd 0 (fun y => Ψ y i) x)
      (fun i => (planarTest_isCoordTest_partial (hΨ_test.smooth i) (cdir 0)).smooth.continuous.neg)
      (fun i x hx => by simp [(hbox_Ψ i x hx).2.1])
    have hu_zq2 := hunfold z₀ hz.sm_z hz.per_z
      (hloc_of hz.sm_z hZ0_int hmem_z)
      (fun i x => -p.ν * cpd 1 (fun y => cpd 1 (fun z => Ψ z i) y) x)
      (fun i => continuous_const.mul
        (planarTest_isCoordTest_partial
          (planarTest_isCoordTest_partial (hΨ_test.smooth i) (cdir 1)) (cdir 1)).smooth.continuous)
      (fun i x hx => by simp [(hbox_Ψ i x hx).2.2.1])
    have hu_zη2 := hunfold z₀ hz.sm_z hz.per_z
      (hloc_of hz.sm_z hZ0_int hmem_z)
      (fun i x => -p.ν * cpd 2 (fun y => cpd 2 (fun z => Ψ z i) y) x)
      (fun i => continuous_const.mul
        (planarTest_isCoordTest_partial
          (planarTest_isCoordTest_partial (hΨ_test.smooth i) (cdir 2)) (cdir 2)).smooth.continuous)
      (fun i x hx => by simp [(hbox_Ψ i x hx).2.2.2])
    -- Split `meridTranspose` integral into its 3 summands
    have hmt_split : (∫ x : Coord, ∑ i : Fin 2, z₀ x i * meridTranspose p.ν Ψ x i) =
        (∫ x : Coord, ∑ i : Fin 2, z₀ x i * ((-cpd 0 (fun y => Ψ y i) x : ℝ) : ℂ)) +
        (∫ x : Coord, ∑ i : Fin 2,
          z₀ x i * ((-p.ν * cpd 1 (fun y => cpd 1 (fun z => Ψ z i) y) x : ℝ) : ℂ)) +
        (∫ x : Coord, ∑ i : Fin 2,
          z₀ x i * ((-p.ν * cpd 2 (fun y => cpd 2 (fun z => Ψ z i) y) x : ℝ) : ℂ)) := by
      have i0 : Integrable (fun x : Coord =>
          ∑ i : Fin 2, z₀ x i * ((-cpd 0 (fun y => Ψ y i) x : ℝ) : ℂ)) :=
        integrable_finsetSum _ fun i _ => hu_z0.1 i
      have i1 : Integrable (fun x : Coord => ∑ i : Fin 2,
          z₀ x i * ((-p.ν * cpd 1 (fun y => cpd 1 (fun z => Ψ z i) y) x : ℝ) : ℂ)) :=
        integrable_finsetSum _ fun i _ => hu_zq2.1 i
      have i2 : Integrable (fun x : Coord => ∑ i : Fin 2,
          z₀ x i * ((-p.ν * cpd 2 (fun y => cpd 2 (fun z => Ψ z i) y) x : ℝ) : ℂ)) :=
        integrable_finsetSum _ fun i _ => hu_zη2.1 i
      have i01 : Integrable (fun x : Coord =>
          (∑ i : Fin 2, z₀ x i * ((-cpd 0 (fun y => Ψ y i) x : ℝ) : ℂ)) +
          (∑ i : Fin 2, z₀ x i *
            ((-p.ν * cpd 1 (fun y => cpd 1 (fun z => Ψ z i) y) x : ℝ) : ℂ))) :=
        i0.add i1
      rw [← integral_add i0 i1, ← integral_add i01 i2]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      dsimp only
      simp only [meridTranspose, Fin.sum_univ_two]
      push_cast; ring
    rw [integral_add hInt_z_mt hInt_bv, hmt_split, hu_z0.2, hu_zq2.2, hu_zη2.2,
      show (∫ x, cdot b_cut Ψ x) = ∫ x, ∑ i : Fin 2, b_cut x i * (Ψ x i : ℂ) from rfl, hu_b.2,
      show (∫ x, cdot g Ψ x) = ∫ x, ∑ i : Fin 2, g x i * (Ψ x i : ℂ) from rfl, hu_g.2] at heq_pde
    -- Simplify `qPeriodize` on each slice and IBP the two spatial Laplacian pieces on good slices
    obtain ⟨Rφ, hRφ⟩ := hφ.bounded
    have hcyl_φ : ∀ i : Fin 2, B0579.IsCylTest p.c (fun y => φ y i) := fun i =>
      ⟨hφ.smooth i, fun y => hφ.periodic y i, Rφ, fun y hy => hRφ y i hy⟩
    have hq_neg_cpd0 : ∀ s y i,
        TailPeriodizeAux.qPeriodize p.c (fun x => -cpd 0 (fun w => Ψ w i) x) s y =
          -deriv ψ s * φ y i := fun s y i => by
      have hneg : TailPeriodizeAux.qPeriodize p.c (fun x => -cpd 0 (fun w => Ψ w i) x) s y =
          -TailPeriodizeAux.qPeriodize p.c (cpd 0 (fun w => Ψ w i)) s y := by
        unfold TailPeriodizeAux.qPeriodize; exact tsum_neg
      rw [hneg, hq_cpd0 s y i]; ring
    have hq_lap0 : ∀ s y i,
        TailPeriodizeAux.qPeriodize p.c
          (fun x => -p.ν * cpd 1 (fun w => cpd 1 (fun z => Ψ z i) w) x) s y =
          -p.ν * ψ s * B0579.pd 0 (B0579.pd 0 (fun w => φ w i)) y := fun s y i => by
      have hmul : TailPeriodizeAux.qPeriodize p.c
          (fun x => -p.ν * cpd 1 (fun w => cpd 1 (fun z => Ψ z i) w) x) s y =
          (-p.ν) * TailPeriodizeAux.qPeriodize p.c
            (cpd 1 (fun w => cpd 1 (fun z => Ψ z i) w)) s y := by
        unfold TailPeriodizeAux.qPeriodize; exact tsum_mul_left
      have hlap0 : TailPeriodizeAux.qPeriodize p.c
          (cpd 1 (fun w => cpd 1 (fun z => Ψ z i) w)) s y =
          ψ s * B0579.pd 0 (B0579.pd 0 (fun w => φ w i)) y := hq_lap 0 s y i
      rw [hmul, hlap0]; ring
    have hq_lap1 : ∀ s y i,
        TailPeriodizeAux.qPeriodize p.c
          (fun x => -p.ν * cpd 2 (fun w => cpd 2 (fun z => Ψ z i) w) x) s y =
          -p.ν * ψ s * B0579.pd 1 (B0579.pd 1 (fun w => φ w i)) y := fun s y i => by
      have hmul : TailPeriodizeAux.qPeriodize p.c
          (fun x => -p.ν * cpd 2 (fun w => cpd 2 (fun z => Ψ z i) w) x) s y =
          (-p.ν) * TailPeriodizeAux.qPeriodize p.c
            (cpd 2 (fun w => cpd 2 (fun z => Ψ z i) w)) s y := by
        unfold TailPeriodizeAux.qPeriodize; exact tsum_mul_left
      have hlap1 : TailPeriodizeAux.qPeriodize p.c
          (cpd 2 (fun w => cpd 2 (fun z => Ψ z i) w)) s y =
          ψ s * B0579.pd 1 (B0579.pd 1 (fun w => φ w i)) y := hq_lap 1 s y i
      rw [hmul, hlap1]; ring
    -- Prove both `.re` and `.im` identities uniformly via a helper on `(vecRe, re)` and `(vecIm, im)`
    let Y_re := toLMH (vecRe φ) (vecRe_cellL2 hφ_h1.l2)
    let Y0_re := toLMH (vecRe fun y i => B0579.pd 0 (fun w => φ w i) y)
      (vecRe_cellL2 fun i => hφ_h1.l2grad i 0)
    let Y1_re := toLMH (vecRe fun y i => B0579.pd 1 (fun w => φ w i) y)
      (vecRe_cellL2 fun i => hφ_h1.l2grad i 1)
    let Y_im := toLMH (vecIm φ) (vecIm_cellL2 hφ_h1.l2)
    let Y0_im := toLMH (vecIm fun y i => B0579.pd 0 (fun w => φ w i) y)
      (vecIm_cellL2 fun i => hφ_h1.l2grad i 0)
    let Y1_im := toLMH (vecIm fun y i => B0579.pd 1 (fun w => φ w i) y)
      (vecIm_cellL2 fun i => hφ_h1.l2grad i 1)
    have hslice_eq : ∀ (proj : ℂ →L[ℝ] ℝ) (Y Y0 Y1 : LMH p.c),
        (∀ {W : CProf} {s : ℝ},
          MemLp (fun y => W (s, y)) 2 (volume.restrict (B0579.cell p.c)) →
          proj (∑ i : Fin 2, ∫ y in B0579.cell p.c, W (s, y) i * (φ y i : ℂ)) =
            ⟪Y, cprofToLMH p.c W s⟫) →
        (∀ {W : CProf} {s : ℝ},
          MemLp (fun y => W (s, y)) 2 (volume.restrict (B0579.cell p.c)) →
          proj (∑ i : Fin 2, ∫ y in B0579.cell p.c,
            W (s, y) i * (B0579.pd 0 (fun w => φ w i) y : ℂ)) =
            ⟪Y0, cprofToLMH p.c W s⟫) →
        (∀ {W : CProf} {s : ℝ},
          MemLp (fun y => W (s, y)) 2 (volume.restrict (B0579.cell p.c)) →
          proj (∑ i : Fin 2, ∫ y in B0579.cell p.c,
            W (s, y) i * (B0579.pd 1 (fun w => φ w i) y : ℂ)) =
            ⟪Y1, cprofToLMH p.c W s⟫) →
        ⟪Y, ∫ s, deriv ψ s • Z0 s⟫ =
          p.ν * (⟪Y0, ∫ s, ψ s • Zq0 s⟫ + ⟪Y1, ∫ s, ψ s • Zη0 s⟫) +
            ⟪Y, ∫ s, ψ s • B_path s⟫ - ⟪Y, ∫ s, ψ s • G_path s⟫ := by
      intro proj Y Y0 Y1 hp0 hp_d0 hp_d1
      have happ := congrArg proj heq_pde
      simp only [map_add] at happ
      -- Commute `proj` with each `∫ s in Icc a b` using integrability of the `ℂ`-valued slice sums
      have hint_slice : ∀ (W : CProf) (hW_sm : StronglyMeasurable W) (hW_per : QPeriodic p.c W)
          (hW_loc : ∀ i : Fin 2, (∫⁻ s in Icc a b,
            eLpNorm (fun y => W (s, y) i) 2 (volume.restrict (B0579.cell p.c))) < ⊤)
          (A : Fin 2 → Coord → ℝ) (hA_cont : ∀ i, Continuous (A i))
          (hA_supp : ∀ i x, (x.1 ∉ Icc a b ∨ R_box < |x.2.1| ∨ R_box < |x.2.2|) → A i x = 0),
          IntegrableOn (fun s : ℝ => ∑ i : Fin 2,
            ∫ y in B0579.cell p.c, W (s, y) i *
              (TailPeriodizeAux.qPeriodize p.c (A i) s y : ℂ)) (Icc a b) volume := by
        intro W hW_sm hW_per hW_loc A hA_cont hA_supp
        refine integrable_finsetSum _ fun i _ => ?_
        have hc_i :=
          (TailPeriodizeAux.integrable_and_integral_coord_eq_cell_qPeriodize hc ha_pos hab
            hR_box_pos
            (((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable
              hW_sm).aestronglyMeasurable)
            (hW_per.mono fun _ hx => congrArg (fun v : CMerid => v i) hx)
            (hW_loc i) (hA_cont i) (hA_supp i)).2.1
        have hp : Integrable (fun x : Coord =>
            W x i * (TailPeriodizeAux.qPeriodize p.c (A i) x.1 x.2 : ℂ))
            ((volume.restrict (Icc a b)).prod (volume.restrict (B0579.cell p.c))) := by
          rwa [Measure.prod_restrict, ← Measure.volume_eq_prod]
        exact hp.integral_prod_left
      have hi_z0 := hint_slice z₀ hz.sm_z hz.per_z (hloc_of hz.sm_z hZ0_int hmem_z)
        (fun i x => -cpd 0 (fun y => Ψ y i) x)
        (fun i => (planarTest_isCoordTest_partial (hΨ_test.smooth i) (cdir 0)).smooth.continuous.neg)
        (fun i x hx => by simp [(hbox_Ψ i x hx).2.1])
      have hi_zq2 := hint_slice z₀ hz.sm_z hz.per_z (hloc_of hz.sm_z hZ0_int hmem_z)
        (fun i x => -p.ν * cpd 1 (fun y => cpd 1 (fun z => Ψ z i) y) x)
        (fun i => continuous_const.mul
          (planarTest_isCoordTest_partial
            (planarTest_isCoordTest_partial (hΨ_test.smooth i) (cdir 1)) (cdir 1)).smooth.continuous)
        (fun i x hx => by simp [(hbox_Ψ i x hx).2.2.1])
      have hi_zη2 := hint_slice z₀ hz.sm_z hz.per_z (hloc_of hz.sm_z hZ0_int hmem_z)
        (fun i x => -p.ν * cpd 2 (fun y => cpd 2 (fun z => Ψ z i) y) x)
        (fun i => continuous_const.mul
          (planarTest_isCoordTest_partial
            (planarTest_isCoordTest_partial (hΨ_test.smooth i) (cdir 2)) (cdir 2)).smooth.continuous)
        (fun i x hx => by simp [(hbox_Ψ i x hx).2.2.2])
      have hi_b := hint_slice b_cut hb_sm hb_per (hloc_of hb_sm hB_int hmem_b)
        (fun i x => Ψ x i) (fun i => (hΨ_test.smooth i).smooth.continuous)
        (fun i x hx => (hbox_Ψ i x hx).1)
      have hi_g := hint_slice g hg.sm_g hg.periodic_g (hloc_of hg.sm_g hG_int hmem_g)
        (fun i x => Ψ x i) (fun i => (hΨ_test.smooth i).smooth.continuous)
        (fun i x hx => (hbox_Ψ i x hx).1)
      rw [← proj.integral_comp_comm hi_z0, ← proj.integral_comp_comm hi_zq2,
        ← proj.integral_comp_comm hi_zη2, ← proj.integral_comp_comm hi_b,
        ← proj.integral_comp_comm hi_g] at happ
      -- Evaluate each of the 5 slice integrals on good slices `s ∈ Icc a b`
      have e_z0 : (∫ s in Icc a b, proj (∑ i : Fin 2, ∫ y in B0579.cell p.c, z₀ (s, y) i *
            (TailPeriodizeAux.qPeriodize p.c (fun x => -cpd 0 (fun w => Ψ w i) x) s y : ℂ))) =
          -⟪Y, ∫ s, deriv ψ s • Z0 s⟫ := by
        have hcongr : (∫ s in Icc a b, proj (∑ i : Fin 2, ∫ y in B0579.cell p.c, z₀ (s, y) i *
              (TailPeriodizeAux.qPeriodize p.c (fun x => -cpd 0 (fun w => Ψ w i) x) s y : ℂ))) =
            ∫ s in Icc a b, -(deriv ψ s * ⟪Y, Z0 s⟫) := by
          refine setIntegral_congr_ae measurableSet_Icc ?_
          filter_upwards [hgood] with s hs hs_ab
          have hgs := hs (hIcc_sub hs_ab)
          have h1 : (∑ i : Fin 2, ∫ y in B0579.cell p.c, z₀ (s, y) i *
                (TailPeriodizeAux.qPeriodize p.c (fun x => -cpd 0 (fun w => Ψ w i) x) s y : ℂ)) =
              ((-deriv ψ s : ℝ) : ℂ) * ∑ i : Fin 2, ∫ y in B0579.cell p.c, z₀ (s, y) i * (φ y i : ℂ) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← integral_const_mul]
            refine integral_congr_ae (ae_of_all _ fun y => ?_)
            dsimp only
            rw [hq_neg_cpd0 s y i]; push_cast; ring
          rw [h1, ← Complex.real_smul,
            proj.map_smul, hp0 hgs.memL2_z, smul_eq_mul, neg_mul]
        rw [hcongr, integral_neg, integral_mul_inner_eq hdψ_sm.continuous
          hψ_cs.deriv hdψ_out (hZ0_int.mono_set hIcc_sub) Y]
      have e_zq2 : (∫ s in Icc a b, proj (∑ i : Fin 2, ∫ y in B0579.cell p.c, z₀ (s, y) i *
            (TailPeriodizeAux.qPeriodize p.c
              (fun x => -p.ν * cpd 1 (fun w => cpd 1 (fun z => Ψ z i) w) x) s y : ℂ))) =
          p.ν * ⟪Y0, ∫ s, ψ s • Zq0 s⟫ := by
        have hcongr : (∫ s in Icc a b, proj (∑ i : Fin 2, ∫ y in B0579.cell p.c, z₀ (s, y) i *
              (TailPeriodizeAux.qPeriodize p.c
                (fun x => -p.ν * cpd 1 (fun w => cpd 1 (fun z => Ψ z i) w) x) s y : ℂ))) =
            ∫ s in Icc a b, p.ν * (ψ s * ⟪Y0, Zq0 s⟫) := by
          refine setIntegral_congr_ae measurableSet_Icc ?_
          filter_upwards [hgood] with s hs hs_ab
          have hgs := hs (hIcc_sub hs_ab)
          have h1 : (∑ i : Fin 2, ∫ y in B0579.cell p.c, z₀ (s, y) i *
                (TailPeriodizeAux.qPeriodize p.c
                  (fun x => -p.ν * cpd 1 (fun w => cpd 1 (fun z => Ψ z i) w) x) s y : ℂ)) =
              ((p.ν * ψ s : ℝ) : ℂ) * ∑ i : Fin 2, ∫ y in B0579.cell p.c,
                zq₀ (s, y) i * (B0579.pd 0 (fun w => φ w i) y : ℂ) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            have heq_y : (∫ y in B0579.cell p.c, z₀ (s, y) i *
                  (TailPeriodizeAux.qPeriodize p.c
                    (fun x => -p.ν * cpd 1 (fun w => cpd 1 (fun z => Ψ z i) w) x) s y : ℂ)) =
                ((-p.ν * ψ s : ℝ) : ℂ) * ∫ y in B0579.cell p.c, z₀ (s, y) i *
                  (B0579.pd 0 (B0579.pd 0 (fun w => φ w i)) y : ℂ) := by
              rw [← integral_const_mul]
              refine integral_congr_ae (ae_of_all _ fun y => ?_)
              dsimp only
              rw [hq_lap0 s y i]; push_cast; ring
            rw [heq_y, (hgs.weak_z_q i).2 _ ((hcyl_φ i).pd 0)]
            push_cast; ring
          rw [h1, ← Complex.real_smul,
            proj.map_smul, hp_d0 hgs.memL2_zq, smul_eq_mul, mul_assoc]
        rw [hcongr, integral_const_mul,
          integral_mul_inner_eq hψ_sm.continuous hψ_cs hψ_out (hZq0_int.mono_set hIcc_sub) Y0]
      have e_zη2 : (∫ s in Icc a b, proj (∑ i : Fin 2, ∫ y in B0579.cell p.c, z₀ (s, y) i *
            (TailPeriodizeAux.qPeriodize p.c
              (fun x => -p.ν * cpd 2 (fun w => cpd 2 (fun z => Ψ z i) w) x) s y : ℂ))) =
          p.ν * ⟪Y1, ∫ s, ψ s • Zη0 s⟫ := by
        have hcongr : (∫ s in Icc a b, proj (∑ i : Fin 2, ∫ y in B0579.cell p.c, z₀ (s, y) i *
              (TailPeriodizeAux.qPeriodize p.c
                (fun x => -p.ν * cpd 2 (fun w => cpd 2 (fun z => Ψ z i) w) x) s y : ℂ))) =
            ∫ s in Icc a b, p.ν * (ψ s * ⟪Y1, Zη0 s⟫) := by
          refine setIntegral_congr_ae measurableSet_Icc ?_
          filter_upwards [hgood] with s hs hs_ab
          have hgs := hs (hIcc_sub hs_ab)
          have h1 : (∑ i : Fin 2, ∫ y in B0579.cell p.c, z₀ (s, y) i *
                (TailPeriodizeAux.qPeriodize p.c
                  (fun x => -p.ν * cpd 2 (fun w => cpd 2 (fun z => Ψ z i) w) x) s y : ℂ)) =
              ((p.ν * ψ s : ℝ) : ℂ) * ∑ i : Fin 2, ∫ y in B0579.cell p.c,
                zη₀ (s, y) i * (B0579.pd 1 (fun w => φ w i) y : ℂ) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            have heq_y : (∫ y in B0579.cell p.c, z₀ (s, y) i *
                  (TailPeriodizeAux.qPeriodize p.c
                    (fun x => -p.ν * cpd 2 (fun w => cpd 2 (fun z => Ψ z i) w) x) s y : ℂ)) =
                ((-p.ν * ψ s : ℝ) : ℂ) * ∫ y in B0579.cell p.c, z₀ (s, y) i *
                  (B0579.pd 1 (B0579.pd 1 (fun w => φ w i)) y : ℂ) := by
              rw [← integral_const_mul]
              refine integral_congr_ae (ae_of_all _ fun y => ?_)
              dsimp only
              rw [hq_lap1 s y i]; push_cast; ring
            rw [heq_y, (hgs.weak_z_eta i).2 _ ((hcyl_φ i).pd 1)]
            push_cast; ring
          rw [h1, ← Complex.real_smul,
            proj.map_smul, hp_d1 hgs.memL2_zη, smul_eq_mul, mul_assoc]
        rw [hcongr, integral_const_mul,
          integral_mul_inner_eq hψ_sm.continuous hψ_cs hψ_out (hZη0_int.mono_set hIcc_sub) Y1]
      have e_b : (∫ s in Icc a b, proj (∑ i : Fin 2, ∫ y in B0579.cell p.c, b_cut (s, y) i *
            (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y : ℂ))) =
          ⟪Y, ∫ s, ψ s • B_path s⟫ := by
        have hcongr : (∫ s in Icc a b, proj (∑ i : Fin 2, ∫ y in B0579.cell p.c, b_cut (s, y) i *
              (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y : ℂ))) =
            ∫ s in Icc a b, ψ s * ⟪Y, B_path s⟫ := by
          refine setIntegral_congr_ae measurableSet_Icc ?_
          filter_upwards [hgood] with s hs hs_ab
          have hgs := hs (hIcc_sub hs_ab)
          have h1 : (∑ i : Fin 2, ∫ y in B0579.cell p.c, b_cut (s, y) i *
                (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y : ℂ)) =
              ((ψ s : ℝ) : ℂ) * ∑ i : Fin 2, ∫ y in B0579.cell p.c, b_cut (s, y) i * (φ y i : ℂ) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← integral_const_mul]
            refine integral_congr_ae (ae_of_all _ fun y => ?_)
            dsimp only
            rw [hq_Ψ s y i]; push_cast; ring
          rw [h1, ← Complex.real_smul,
            proj.map_smul, hp0 hgs.memL2_b, smul_eq_mul]
        rw [hcongr, integral_mul_inner_eq hψ_sm.continuous hψ_cs hψ_out
          (hB_int.mono_set hIcc_sub) Y]
      have e_g : (∫ s in Icc a b, proj (∑ i : Fin 2, ∫ y in B0579.cell p.c, g (s, y) i *
            (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y : ℂ))) =
          ⟪Y, ∫ s, ψ s • G_path s⟫ := by
        have hcongr : (∫ s in Icc a b, proj (∑ i : Fin 2, ∫ y in B0579.cell p.c, g (s, y) i *
              (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y : ℂ))) =
            ∫ s in Icc a b, ψ s * ⟪Y, G_path s⟫ := by
          refine setIntegral_congr_ae measurableSet_Icc ?_
          filter_upwards [hgood] with s hs hs_ab
          have hgs := hs (hIcc_sub hs_ab)
          have h1 : (∑ i : Fin 2, ∫ y in B0579.cell p.c, g (s, y) i *
                (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y : ℂ)) =
              ((ψ s : ℝ) : ℂ) * ∑ i : Fin 2, ∫ y in B0579.cell p.c, g (s, y) i * (φ y i : ℂ) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← integral_const_mul]
            refine integral_congr_ae (ae_of_all _ fun y => ?_)
            dsimp only
            rw [hq_Ψ s y i]; push_cast; ring
          rw [h1, ← Complex.real_smul,
            proj.map_smul, hp0 hgs.memL2_g, smul_eq_mul]
        rw [hcongr, integral_mul_inner_eq hψ_sm.continuous hψ_cs hψ_out
          (hG_int.mono_set hIcc_sub) Y]
      change (∫ s in Icc a b, proj _) + (∫ s in Icc a b, proj _) + (∫ s in Icc a b, proj _) +
          (∫ s in Icc a b, proj _) = ∫ s in Icc a b, proj _ at happ
      rw [e_z0, e_zq2, e_zη2, e_b, e_g] at happ
      linarith
    exact ⟨hslice_eq Complex.reCLM Y_re Y0_re Y1_re
        (fun hW => re_cell_pair_eq_inner hW hφ_h1.l2)
        (fun hW => re_cell_pair_eq_inner hW fun i => hφ_h1.l2grad i 0)
        (fun hW => re_cell_pair_eq_inner hW fun i => hφ_h1.l2grad i 1),
      hslice_eq Complex.imCLM Y_im Y0_im Y1_im
        (fun hW => im_cell_pair_eq_inner hW hφ_h1.l2)
        (fun hW => im_cell_pair_eq_inner hW fun i => hφ_h1.l2grad i 0)
        (fun hW => im_cell_pair_eq_inner hW fun i => hφ_h1.l2grad i 1)⟩
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    have hψ0 : ψ = 0 := funext fun s => image_eq_zero_of_notMem_tsupport (by rw [hne]; simp)
    simp [hψ0]

private lemma inner_balance_of_tendsto {c ν : ℝ}
    {Yn Y0n Y1n : ℕ → LMH c} {Y Y0 Y1 I_dZ I_Zq I_Zη I_B I_G : LMH c}
    (ht : Tendsto Yn atTop (𝓝 Y))
    (ht0 : Tendsto Y0n atTop (𝓝 Y0))
    (ht1 : Tendsto Y1n atTop (𝓝 Y1))
    (heq : ∀ n : ℕ, ⟪Yn n, I_dZ⟫ =
      ν * (⟪Y0n n, I_Zq⟫ + ⟪Y1n n, I_Zη⟫) + ⟪Yn n, I_B⟫ - ⟪Yn n, I_G⟫) :
    ⟪Y, I_dZ⟫ = ν * (⟪Y0, I_Zq⟫ + ⟪Y1, I_Zη⟫) + ⟪Y, I_B⟫ - ⟪Y, I_G⟫ := by
  have tin : ∀ {f : ℕ → LMH c} {a : LMH c}, Tendsto f atTop (𝓝 a) → ∀ b : LMH c,
      Tendsto (fun n => ⟪f n, b⟫) atTop (𝓝 ⟪a, b⟫) := fun {f a} hf b => by
    have hsub : Tendsto (fun n => ‖f n - a‖ * ‖b‖) atTop (𝓝 0) := by
      simpa using (tendsto_iff_norm_sub_tendsto_zero.1 hf).mul_const ‖b‖
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hsub
    rw [← inner_sub_left, Real.norm_eq_abs]
    exact abs_real_inner_le_norm (f n - a) b
  have hlhs : Tendsto (fun n => ⟪Yn n, I_dZ⟫) atTop (𝓝 ⟪Y, I_dZ⟫) := tin ht I_dZ
  have hrhs : Tendsto
      (fun n => ν * (⟪Y0n n, I_Zq⟫ + ⟪Y1n n, I_Zη⟫) + ⟪Yn n, I_B⟫ - ⟪Yn n, I_G⟫)
      atTop (𝓝 (ν * (⟪Y0, I_Zq⟫ + ⟪Y1, I_Zη⟫) + ⟪Y, I_B⟫ - ⟪Y, I_G⟫)) :=
    (((tendsto_const_nhds (x := ν)).mul ((tin ht0 I_Zq).add (tin ht1 I_Zη))).add
      (tin ht I_B)).sub (tin ht I_G)
  exact tendsto_nhds_unique hlhs (hrhs.congr fun n => (heq n).symm)

private lemma tested_pair_of_flatSpatial {p : Params} {T M C_tr : ℝ}
    (hT : 0 < T) (hM : 0 ≤ M) (hC_tr : 0 ≤ C_tr)
    {g gq gη z₀ zq₀ zη₀ : CProf}
    (hg : IsCylSourceH1 p.c g gq gη)
    (hg_int : (∫⁻ s in Ioc 0 T, sliceH1Norm p.c g gq gη s) < ⊤)
    (hz : IsEarlyBorelRep p T g z₀ zq₀ zη₀)
    (hb_le : ∀ s ∈ Ioc 0 T,
      cylSliceL2 p.c (fun y => bCut p T z₀ zq₀ zη₀ (s, y)) ≤
        ENNReal.ofReal C_tr * sliceH1Norm p.c z₀ zq₀ zη₀ s)
    (hbdd : ∀ᵐ s ∂volume, s ∈ Ioc 0 T → sliceH1Norm p.c z₀ zq₀ zη₀ s ≤ ENNReal.ofReal M)
    {ψ : ℝ → ℝ} (hψ_sm : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_ts : tsupport ψ ⊆ Ioo 0 T)
    {φ : ℝ × ℝ → Fin 2 → ℝ} (hφ : IsFlatSpatialTest p.c φ) :
    let hφ_h1 := isH1DivFreeTest_of_flatSpatial hφ
    let Z0 := cprofToLMH p.c z₀
    let Zq0 := cprofToLMH p.c zq₀
    let Zη0 := cprofToLMH p.c zη₀
    let B_path := cprofToLMH p.c (bCut p T z₀ zq₀ zη₀)
    let G_path := cprofToLMH p.c g
    (⟪toLMH (vecRe φ) (vecRe_cellL2 hφ_h1.l2), ∫ s, deriv ψ s • Z0 s⟫ =
      p.ν * (⟪toLMH (vecRe fun y i => B0579.pd 0 (fun w => φ w i) y)
                (vecRe_cellL2 fun i => hφ_h1.l2grad i 0), ∫ s, ψ s • Zq0 s⟫ +
             ⟪toLMH (vecRe fun y i => B0579.pd 1 (fun w => φ w i) y)
                (vecRe_cellL2 fun i => hφ_h1.l2grad i 1), ∫ s, ψ s • Zη0 s⟫) +
        ⟪toLMH (vecRe φ) (vecRe_cellL2 hφ_h1.l2), ∫ s, ψ s • B_path s⟫ -
        ⟪toLMH (vecRe φ) (vecRe_cellL2 hφ_h1.l2), ∫ s, ψ s • G_path s⟫) ∧
    (⟪toLMH (vecIm φ) (vecIm_cellL2 hφ_h1.l2), ∫ s, deriv ψ s • Z0 s⟫ =
      p.ν * (⟪toLMH (vecIm fun y i => B0579.pd 0 (fun w => φ w i) y)
                (vecIm_cellL2 fun i => hφ_h1.l2grad i 0), ∫ s, ψ s • Zq0 s⟫ +
             ⟪toLMH (vecIm fun y i => B0579.pd 1 (fun w => φ w i) y)
                (vecIm_cellL2 fun i => hφ_h1.l2grad i 1), ∫ s, ψ s • Zη0 s⟫) +
        ⟪toLMH (vecIm φ) (vecIm_cellL2 hφ_h1.l2), ∫ s, ψ s • B_path s⟫ -
        ⟪toLMH (vecIm φ) (vecIm_cellL2 hφ_h1.l2), ∫ s, ψ s • G_path s⟫) := by
  intro hφ_h1 Z0 Zq0 Zη0 B_path G_path
  have hc : 0 < p.c := p.c_pos
  obtain ⟨Gn, φn, Sb, hGn_sm, hSb_pos, hGn_supp, hφn_flat, hper_eq, hconv_0, hconv_pd⟩ :=
    exists_stream_lift_approx hc hψ_sm hψ_cs hψ_ts hφ
  have hφn_h1 : ∀ n, IsH1DivFreeTest p.c (φn n) := fun n =>
    isH1DivFreeTest_of_flatSpatial (hφn_flat n)
  have ht_re : Tendsto (fun n => toLMH (vecRe (φn n)) (vecRe_cellL2 (hφn_h1 n).l2))
      atTop (𝓝 (toLMH (vecRe φ) (vecRe_cellL2 hφ_h1.l2))) :=
    tendsto_of_norm_sq_tendsto_zero
      (hconv_0.congr fun n => (norm_toLMH_vecRe_sub_sq (hφn_h1 n).l2 hφ_h1.l2).symm)
  have ht_re_d : ∀ j : Fin 2, Tendsto
      (fun n => toLMH (vecRe fun y i => B0579.pd j (fun w => φn n w i) y)
        (vecRe_cellL2 fun i => (hφn_h1 n).l2grad i j))
      atTop (𝓝 (toLMH (vecRe fun y i => B0579.pd j (fun w => φ w i) y)
        (vecRe_cellL2 fun i => hφ_h1.l2grad i j))) := fun j =>
    tendsto_of_norm_sq_tendsto_zero
      ((hconv_pd j).congr fun n =>
        (norm_toLMH_vecRe_sub_sq (fun i => (hφn_h1 n).l2grad i j)
          (fun i => hφ_h1.l2grad i j)).symm)
  have ht_im : Tendsto (fun n => toLMH (vecIm (φn n)) (vecIm_cellL2 (hφn_h1 n).l2))
      atTop (𝓝 (toLMH (vecIm φ) (vecIm_cellL2 hφ_h1.l2))) :=
    tendsto_of_norm_sq_tendsto_zero
      (hconv_0.congr fun n => (norm_toLMH_vecIm_sub_sq (hφn_h1 n).l2 hφ_h1.l2).symm)
  have ht_im_d : ∀ j : Fin 2, Tendsto
      (fun n => toLMH (vecIm fun y i => B0579.pd j (fun w => φn n w i) y)
        (vecIm_cellL2 fun i => (hφn_h1 n).l2grad i j))
      atTop (𝓝 (toLMH (vecIm fun y i => B0579.pd j (fun w => φ w i) y)
        (vecIm_cellL2 fun i => hφ_h1.l2grad i j))) := fun j =>
    tendsto_of_norm_sq_tendsto_zero
      ((hconv_pd j).congr fun n =>
        (norm_toLMH_vecIm_sub_sq (fun i => (hφn_h1 n).l2grad i j)
          (fun i => hφ_h1.l2grad i j)).symm)
  refine ⟨inner_balance_of_tendsto ht_re (ht_re_d 0) (ht_re_d 1) fun n =>
      (tested_pair_of_prodSG hT hM hC_tr hg hg_int hz hb_le hbdd hψ_sm hψ_cs hψ_ts
        (mul_pos two_pos hc) (hSb_pos n) (hGn_sm n) (hGn_supp n) (hφn_flat n) (hper_eq n)).1,
    inner_balance_of_tendsto ht_im (ht_im_d 0) (ht_im_d 1) fun n =>
      (tested_pair_of_prodSG hT hM hC_tr hg hg_int hz hb_le hbdd hψ_sm hψ_cs hψ_ts
        (mul_pos two_pos hc) (hSb_pos n) (hGn_sm n) (hGn_supp n) (hφn_flat n) (hper_eq n)).2⟩

private lemma tested_pair_of_h1DivFree {p : Params} {T M C_tr : ℝ}
    (hT : 0 < T) (hM : 0 ≤ M) (hC_tr : 0 ≤ C_tr)
    {g gq gη z₀ zq₀ zη₀ : CProf}
    (hg : IsCylSourceH1 p.c g gq gη)
    (hg_int : (∫⁻ s in Ioc 0 T, sliceH1Norm p.c g gq gη s) < ⊤)
    (hz : IsEarlyBorelRep p T g z₀ zq₀ zη₀)
    (hb_le : ∀ s ∈ Ioc 0 T,
      cylSliceL2 p.c (fun y => bCut p T z₀ zq₀ zη₀ (s, y)) ≤
        ENNReal.ofReal C_tr * sliceH1Norm p.c z₀ zq₀ zη₀ s)
    (hbdd : ∀ᵐ s ∂volume, s ∈ Ioc 0 T → sliceH1Norm p.c z₀ zq₀ zη₀ s ≤ ENNReal.ofReal M)
    {ψ : ℝ → ℝ} (hψ_sm : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_ts : tsupport ψ ⊆ Ioo 0 T)
    {φ : ℝ × ℝ → Fin 2 → ℝ} (hφ : IsH1DivFreeTest p.c φ) :
    let Z0 := cprofToLMH p.c z₀
    let Zq0 := cprofToLMH p.c zq₀
    let Zη0 := cprofToLMH p.c zη₀
    let B_path := cprofToLMH p.c (bCut p T z₀ zq₀ zη₀)
    let G_path := cprofToLMH p.c g
    (⟪toLMH (vecRe φ) (vecRe_cellL2 hφ.l2), ∫ s, deriv ψ s • Z0 s⟫ =
      p.ν * (⟪toLMH (vecRe fun y i => B0579.pd 0 (fun w => φ w i) y)
                (vecRe_cellL2 fun i => hφ.l2grad i 0), ∫ s, ψ s • Zq0 s⟫ +
             ⟪toLMH (vecRe fun y i => B0579.pd 1 (fun w => φ w i) y)
                (vecRe_cellL2 fun i => hφ.l2grad i 1), ∫ s, ψ s • Zη0 s⟫) +
        ⟪toLMH (vecRe φ) (vecRe_cellL2 hφ.l2), ∫ s, ψ s • B_path s⟫ -
        ⟪toLMH (vecRe φ) (vecRe_cellL2 hφ.l2), ∫ s, ψ s • G_path s⟫) ∧
    (⟪toLMH (vecIm φ) (vecIm_cellL2 hφ.l2), ∫ s, deriv ψ s • Z0 s⟫ =
      p.ν * (⟪toLMH (vecIm fun y i => B0579.pd 0 (fun w => φ w i) y)
                (vecIm_cellL2 fun i => hφ.l2grad i 0), ∫ s, ψ s • Zq0 s⟫ +
             ⟪toLMH (vecIm fun y i => B0579.pd 1 (fun w => φ w i) y)
                (vecIm_cellL2 fun i => hφ.l2grad i 1), ∫ s, ψ s • Zη0 s⟫) +
        ⟪toLMH (vecIm φ) (vecIm_cellL2 hφ.l2), ∫ s, ψ s • B_path s⟫ -
        ⟪toLMH (vecIm φ) (vecIm_cellL2 hφ.l2), ∫ s, ψ s • G_path s⟫) := by
  intro Z0 Zq0 Zη0 B_path G_path
  have hc : 0 < p.c := p.c_pos
  obtain ⟨φk, hφk_flat, hφk_tend⟩ := divFreeCutoffDensity p.c hc φ hφ
  have hφk_h1 : ∀ k, IsH1DivFreeTest p.c (φk k) := fun k =>
    isH1DivFreeTest_of_flatSpatial (hφk_flat k)
  -- Extract real-valued `L²` convergence of `φk k - φ` and `pd j (φk k) - pd j φ` from `hφk_tend`
  let tot : ℕ → ℝ × ℝ → ℝ := fun k y => ∑ i : Fin 2,
    ((φk k y i - φ y i) ^ 2 +
      ∑ j : Fin 2, (B0579.pd j (fun w => φk k w i) y - B0579.pd j (fun w => φ w i) y) ^ 2)
  have hconv_part : ∀ (f : ℕ → ℝ × ℝ → ℝ),
      (∀ k, Integrable (f k) (volume.restrict (B0579.cell p.c))) →
      (∀ k y, 0 ≤ f k y) →
      (∀ k y, f k y ≤ tot k y) →
      Tendsto (fun k => ∫ y in B0579.cell p.c, f k y) atTop (𝓝 0) := by
    intro f hf_int hf_nn hf_le
    have hof : Tendsto (fun k => ENNReal.ofReal (∫ y in B0579.cell p.c, f k y)) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hφk_tend
        (fun _ => zero_le) fun k => ?_
      rw [ofReal_integral_eq_lintegral_ofReal (hf_int k) (ae_of_all _ (hf_nn k))]
      exact lintegral_mono fun y => ENNReal.ofReal_le_ofReal (hf_le k y)
    have hto := (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hof
    rw [ENNReal.toReal_zero] at hto
    exact hto.congr fun k =>
      ENNReal.toReal_ofReal (integral_nonneg (hf_nn k))
  have hconv_0 : Tendsto (fun k => ∫ y in B0579.cell p.c, ∑ i : Fin 2, (φk k y i - φ y i) ^ 2)
      atTop (𝓝 0) := by
    refine hconv_part _ (fun k => integrable_finsetSum _ fun i _ =>
      (((hφk_h1 k).l2 i).sub (hφ.l2 i)).integrable_sq)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) fun k y => ?_
    refine Finset.sum_le_sum fun i _ => le_add_of_nonneg_right
      (Finset.sum_nonneg fun j _ => sq_nonneg _)
  have hconv_pd : ∀ j : Fin 2, Tendsto (fun k => ∫ y in B0579.cell p.c, ∑ i : Fin 2,
      (B0579.pd j (fun w => φk k w i) y - B0579.pd j (fun w => φ w i) y) ^ 2) atTop (𝓝 0) := by
    intro j
    refine hconv_part _ (fun k => integrable_finsetSum _ fun i _ =>
      (((hφk_h1 k).l2grad i j).sub (hφ.l2grad i j)).integrable_sq)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) fun k y => ?_
    refine Finset.sum_le_sum fun i _ => ?_
    have hj_le : (B0579.pd j (fun w => φk k w i) y - B0579.pd j (fun w => φ w i) y) ^ 2 ≤
        ∑ l : Fin 2, (B0579.pd l (fun w => φk k w i) y - B0579.pd l (fun w => φ w i) y) ^ 2 :=
      Finset.single_le_sum
        (f := fun l : Fin 2 => (B0579.pd l (fun w => φk k w i) y - B0579.pd l (fun w => φ w i) y) ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
    exact hj_le.trans (le_add_of_nonneg_left (sq_nonneg _))
  have ht_re : Tendsto (fun k => toLMH (vecRe (φk k)) (vecRe_cellL2 (hφk_h1 k).l2))
      atTop (𝓝 (toLMH (vecRe φ) (vecRe_cellL2 hφ.l2))) :=
    tendsto_of_norm_sq_tendsto_zero
      (hconv_0.congr fun k => (norm_toLMH_vecRe_sub_sq (hφk_h1 k).l2 hφ.l2).symm)
  have ht_re_d : ∀ j : Fin 2, Tendsto
      (fun k => toLMH (vecRe fun y i => B0579.pd j (fun w => φk k w i) y)
        (vecRe_cellL2 fun i => (hφk_h1 k).l2grad i j))
      atTop (𝓝 (toLMH (vecRe fun y i => B0579.pd j (fun w => φ w i) y)
        (vecRe_cellL2 fun i => hφ.l2grad i j))) := fun j =>
    tendsto_of_norm_sq_tendsto_zero
      ((hconv_pd j).congr fun k =>
        (norm_toLMH_vecRe_sub_sq (fun i => (hφk_h1 k).l2grad i j)
          (fun i => hφ.l2grad i j)).symm)
  have ht_im : Tendsto (fun k => toLMH (vecIm (φk k)) (vecIm_cellL2 (hφk_h1 k).l2))
      atTop (𝓝 (toLMH (vecIm φ) (vecIm_cellL2 hφ.l2))) :=
    tendsto_of_norm_sq_tendsto_zero
      (hconv_0.congr fun k => (norm_toLMH_vecIm_sub_sq (hφk_h1 k).l2 hφ.l2).symm)
  have ht_im_d : ∀ j : Fin 2, Tendsto
      (fun k => toLMH (vecIm fun y i => B0579.pd j (fun w => φk k w i) y)
        (vecIm_cellL2 fun i => (hφk_h1 k).l2grad i j))
      atTop (𝓝 (toLMH (vecIm fun y i => B0579.pd j (fun w => φ w i) y)
        (vecIm_cellL2 fun i => hφ.l2grad i j))) := fun j =>
    tendsto_of_norm_sq_tendsto_zero
      ((hconv_pd j).congr fun k =>
        (norm_toLMH_vecIm_sub_sq (fun i => (hφk_h1 k).l2grad i j)
          (fun i => hφ.l2grad i j)).symm)
  refine ⟨inner_balance_of_tendsto ht_re (ht_re_d 0) (ht_re_d 1) fun k =>
      (tested_pair_of_flatSpatial hT hM hC_tr hg hg_int hz hb_le hbdd hψ_sm hψ_cs hψ_ts
        (hφk_flat k)).1,
    inner_balance_of_tendsto ht_im (ht_im_d 0) (ht_im_d 1) fun k =>
      (tested_pair_of_flatSpatial hT hM hC_tr hg hg_int hz hb_le hbdd hψ_sm hψ_cs hψ_ts
        (hφk_flat k)).2⟩

/-- Weak Bochner time derivative of `s ↦ opJ p.c hc J hJ k (cprofToLMH p.c z₀ s)` on `(0, T)`. -/
def mollTimeDeriv (p : Params) (hc : 0 < p.c)
    (J : ℕ → LMSpField → LMSpField) (hJ : IsLMMollifier p.c J) (k : ℕ)
    (zq₀ zη₀ b_cut g : CProf) (s : ℝ) : LMH p.c :=
  p.ν • (opDJ p.c hc J hJ k 0 (cprofToLMH p.c zq₀ s) +
      opDJ p.c hc J hJ k 1 (cprofToLMH p.c zη₀ s)) -
    opJ p.c hc J hJ k (opP0 p.c hc (cprofToLMH p.c b_cut s)) +
    opJ p.c hc J hJ k (cprofToLMH p.c g s)

theorem hasWeakDerivTime_opJ_Z0 {p : Params} {T M C_tr : ℝ}
    (hT : 0 < T) (hM : 0 ≤ M) (hC_tr : 0 ≤ C_tr)
    (hc : 0 < p.c) (J : ℕ → LMSpField → LMSpField) (hJ : IsLMMollifier p.c J) (k : ℕ)
    {g gq gη z₀ zq₀ zη₀ : CProf}
    (hg : IsCylSourceH1 p.c g gq gη)
    (hg_int : (∫⁻ s in Ioc 0 T, sliceH1Norm p.c g gq gη s) < ⊤)
    (hz : IsEarlyBorelRep p T g z₀ zq₀ zη₀)
    (hb_le : ∀ s ∈ Ioc 0 T,
      cylSliceL2 p.c (fun y => bCut p T z₀ zq₀ zη₀ (s, y)) ≤
        ENNReal.ofReal C_tr * sliceH1Norm p.c z₀ zq₀ zη₀ s)
    (hbdd : ∀ᵐ s ∂volume, s ∈ Ioc 0 T → sliceH1Norm p.c z₀ zq₀ zη₀ s ≤ ENNReal.ofReal M) :
    BochnerTime.HasWeakDerivTime 0 T
      (fun s => opJ p.c hc J hJ k (cprofToLMH p.c z₀ s))
      (mollTimeDeriv p hc J hJ k zq₀ zη₀ (bCut p T z₀ zq₀ zη₀) g) := by
  set b_cut := bCut p T z₀ zq₀ zη₀
  set Z0 := cprofToLMH p.c z₀
  set Zq0 := cprofToLMH p.c zq₀
  set Zη0 := cprofToLMH p.c zη₀
  set B_path := cprofToLMH p.c b_cut
  set G_path := cprofToLMH p.c g
  set Uk' := mollTimeDeriv p hc J hJ k zq₀ zη₀ b_cut g
  have hb_sm : StronglyMeasurable b_cut := stronglyMeasurable_bCut p T hz.sm_z hz.sm_zq hz.sm_zη
  obtain ⟨hZ0_int, hZq0_int, hZη0_int, hB_int, hG_int⟩ :=
    integrableOn_early_paths hT hM hC_tr hg hg_int hz hb_sm hb_le hbdd
  have hUk_int : IntegrableOn (fun s => opJ p.c hc J hJ k (Z0 s)) (Ioo 0 T) volume :=
    (opJ p.c hc J hJ k).integrable_comp hZ0_int
  have hUk'_int : IntegrableOn Uk' (Ioo 0 T) volume := by
    have h1 := ((opDJ p.c hc J hJ k 0).integrable_comp hZq0_int).add
      ((opDJ p.c hc J hJ k 1).integrable_comp hZη0_int)
    have h2 := (opJ p.c hc J hJ k).integrable_comp ((opP0 p.c hc).integrable_comp hB_int)
    have h3 := (opJ p.c hc J hJ k).integrable_comp hG_int
    exact ((h1.smul p.ν).sub h2).add h3
  refine ⟨hUk_int, hUk'_int, fun ψ hψ_sm hψ_cs hψ_ts => ?_⟩
  have hgood := ae_earlyGoodSlice hM hC_tr hg hg_int hz hb_sm hb_le hbdd
  refine ext_inner_left ℝ fun χ => ?_
  set X := opP0 p.c hc χ
  let w : LMSpField := J k (lmLift X)
  obtain ⟨hw_re, hw_im⟩ := lmH1Test p.c hc J hJ ⟨hJ.gradL2, hJ.divFreeWeak⟩ k
    (lmLift X) (lmLift_cellL2 X) (opP0_weakDivFree hc χ)
  have hre_id := (tested_pair_of_h1DivFree hT hM hC_tr hg hg_int hz hb_le hbdd
    hψ_sm hψ_cs hψ_ts hw_re).1
  have him_id := (tested_pair_of_h1DivFree hT hM hC_tr hg hg_int hz hb_le hbdd
    hψ_sm hψ_cs hψ_ts hw_im).2
  -- Identify `toLMH (vecRe (Re w)) + toLMH (vecIm (Im w)) = opJ k X`
  have hw_sum : toLMH (vecRe fun y i => (w y i).re) (vecRe_cellL2 hw_re.l2) +
      toLMH (vecIm fun y i => (w y i).im) (vecIm_cellL2 hw_im.l2) =
      opJ p.c hc J hJ k X := by
    apply Lp.ext_iff.2
    filter_upwards [Lp.coeFn_add (toLMH (vecRe fun y i => (w y i).re) (vecRe_cellL2 hw_re.l2))
        (toLMH (vecIm fun y i => (w y i).im) (vecIm_cellL2 hw_im.l2)),
      toLMH_ae (vecRe_cellL2 hw_re.l2), toLMH_ae (vecIm_cellL2 hw_im.l2),
      opJ_ae hc hJ k X] with y hya hy1 hy2 hyj
    rw [hya, Pi.add_apply, hy1, hy2, hyj, ← lmReal_add]
    congr 1; ext i
    dsimp [vecRe, vecIm, w]
    rw [mul_comm Complex.I _, Complex.re_add_im]
  have hwd_sum : ∀ j : Fin 2,
      toLMH (vecRe fun y i => B0579.pd j (fun z => (w z i).re) y)
        (vecRe_cellL2 fun i => hw_re.l2grad i j) +
      toLMH (vecIm fun y i => B0579.pd j (fun z => (w z i).im) y)
        (vecIm_cellL2 fun i => hw_im.l2grad i j) =
      opDJ p.c hc J hJ k j X := fun j => by
    apply Lp.ext_iff.2
    filter_upwards [Lp.coeFn_add
        (toLMH (vecRe fun y i => B0579.pd j (fun z => (w z i).re) y)
          (vecRe_cellL2 fun i => hw_re.l2grad i j))
        (toLMH (vecIm fun y i => B0579.pd j (fun z => (w z i).im) y)
          (vecIm_cellL2 fun i => hw_im.l2grad i j)),
      toLMH_ae (vecRe_cellL2 fun i => hw_re.l2grad i j),
      toLMH_ae (vecIm_cellL2 fun i => hw_im.l2grad i j),
      opDJ_ae hc hJ k j X] with y hya hy1 hy2 hyd
    rw [hya, Pi.add_apply, hy1, hy2, hyd, ← lmReal_add]
    refine congrArg lmReal (funext fun i => ?_)
    dsimp [vecRe, vecIm, w]
    rw [lmPd_re, lmPd_im, mul_comm Complex.I _, Complex.re_add_im]
  have hcomb : ⟪opJ p.c hc J hJ k X, ∫ s, deriv ψ s • Z0 s⟫ =
      p.ν * (⟪opDJ p.c hc J hJ k 0 X, ∫ s, ψ s • Zq0 s⟫ +
             ⟪opDJ p.c hc J hJ k 1 X, ∫ s, ψ s • Zη0 s⟫) +
        ⟪opJ p.c hc J hJ k X, ∫ s, ψ s • B_path s⟫ -
        ⟪opJ p.c hc J hJ k X, ∫ s, ψ s • G_path s⟫ := by
    rw [← hw_sum, ← hwd_sum 0, ← hwd_sum 1]
    simp only [inner_add_left]
    linarith
  -- Rewrite LHS and RHS as `∫ s, ⟪χ, ...⟫` using self-adjointness / anti-symmetry on good slices
  have hint_dZ0 : Integrable (fun s => deriv ψ s • Z0 s) volume :=
    BochnerTime.integrable_deriv_smul hψ_sm hψ_cs hψ_ts hZ0_int
  have hint_dUk : Integrable (fun s => deriv ψ s • opJ p.c hc J hJ k (Z0 s)) volume :=
    BochnerTime.integrable_deriv_smul hψ_sm hψ_cs hψ_ts hUk_int
  have hint_Zq : Integrable (fun s => ψ s • Zq0 s) volume :=
    BochnerTime.integrable_smul hψ_sm hψ_cs hψ_ts hZq0_int
  have hint_Zη : Integrable (fun s => ψ s • Zη0 s) volume :=
    BochnerTime.integrable_smul hψ_sm hψ_cs hψ_ts hZη0_int
  have hint_B : Integrable (fun s => ψ s • B_path s) volume :=
    BochnerTime.integrable_smul hψ_sm hψ_cs hψ_ts hB_int
  have hint_G : Integrable (fun s => ψ s • G_path s) volume :=
    BochnerTime.integrable_smul hψ_sm hψ_cs hψ_ts hG_int
  have hint_Uk' : Integrable (fun s => ψ s • Uk' s) volume :=
    BochnerTime.integrable_smul hψ_sm hψ_cs hψ_ts hUk'_int
  have inner_int : ∀ (A : LMH p.c) (F : ℝ → LMH p.c), Integrable F volume →
      ⟪A, ∫ s, F s⟫ = ∫ s, ⟪A, F s⟫ :=
    fun A F hF => ((innerSL ℝ A).integral_comp_comm hF).symm
  rw [inner_int _ _ hint_dZ0, inner_int _ _ hint_Zq, inner_int _ _ hint_Zη,
    inner_int _ _ hint_B, inner_int _ _ hint_G] at hcomb
  have hlhs_eq : (∫ s, ⟪opJ p.c hc J hJ k X, deriv ψ s • Z0 s⟫) =
      ⟪χ, ∫ s, deriv ψ s • opJ p.c hc J hJ k (Z0 s)⟫ := by
    rw [inner_int _ _ hint_dUk]
    refine integral_congr_ae ?_
    filter_upwards [hgood] with s hs
    by_cases hmem : s ∈ Ioo 0 T
    · have hgs := hs hmem
      have hp0_Z : opP0 p.c hc (Z0 s) = Z0 s :=
        opP0_eq_self_of_weakDivFree hc hgs.lmWeakDivFree_Z
      change ⟪opJ p.c hc J hJ k (opP0 p.c hc χ), deriv ψ s • Z0 s⟫ =
        ⟪χ, deriv ψ s • opJ p.c hc J hJ k (Z0 s)⟫
      rw [real_inner_smul_right, real_inner_smul_right, inner_opJ_selfAdj,
        inner_opP0_selfAdj, opP0_comm_opJ, hp0_Z]
    · have hd0 : deriv ψ s = 0 :=
        BochnerTime.eq_zero_of_tsupport_subset (BochnerTime.tsupport_deriv_subset_Ioo hψ_ts) hmem
      change ⟪_, deriv ψ s • _⟫ = ⟪_, deriv ψ s • _⟫
      simp [hd0]
  have hrhs_eq : p.ν * ((∫ s, ⟪opDJ p.c hc J hJ k 0 X, ψ s • Zq0 s⟫) +
        (∫ s, ⟪opDJ p.c hc J hJ k 1 X, ψ s • Zη0 s⟫)) +
      (∫ s, ⟪opJ p.c hc J hJ k X, ψ s • B_path s⟫) -
      (∫ s, ⟪opJ p.c hc J hJ k X, ψ s • G_path s⟫) =
      ⟪χ, -∫ s, ψ s • Uk' s⟫ := by
    have i0 : Integrable (fun s => ⟪opDJ p.c hc J hJ k 0 X, ψ s • Zq0 s⟫) volume :=
      (innerSL ℝ (opDJ p.c hc J hJ k 0 X)).integrable_comp hint_Zq
    have i1 : Integrable (fun s => ⟪opDJ p.c hc J hJ k 1 X, ψ s • Zη0 s⟫) volume :=
      (innerSL ℝ (opDJ p.c hc J hJ k 1 X)).integrable_comp hint_Zη
    have ib : Integrable (fun s => ⟪opJ p.c hc J hJ k X, ψ s • B_path s⟫) volume :=
      (innerSL ℝ (opJ p.c hc J hJ k X)).integrable_comp hint_B
    have ig : Integrable (fun s => ⟪opJ p.c hc J hJ k X, ψ s • G_path s⟫) volume :=
      (innerSL ℝ (opJ p.c hc J hJ k X)).integrable_comp hint_G
    have i01 : Integrable (fun s =>
        ⟪opDJ p.c hc J hJ k 0 X, ψ s • Zq0 s⟫ + ⟪opDJ p.c hc J hJ k 1 X, ψ s • Zη0 s⟫) volume :=
      i0.add i1
    have i01ν : Integrable (fun s =>
        p.ν * (⟪opDJ p.c hc J hJ k 0 X, ψ s • Zq0 s⟫ +
          ⟪opDJ p.c hc J hJ k 1 X, ψ s • Zη0 s⟫)) volume :=
      i01.const_mul p.ν
    have i01νb : Integrable (fun s =>
        p.ν * (⟪opDJ p.c hc J hJ k 0 X, ψ s • Zq0 s⟫ +
          ⟪opDJ p.c hc J hJ k 1 X, ψ s • Zη0 s⟫) +
          ⟪opJ p.c hc J hJ k X, ψ s • B_path s⟫) volume :=
      i01ν.add ib
    rw [← integral_add i0 i1, ← integral_const_mul, ← integral_add i01ν ib,
      ← integral_sub i01νb ig,
      inner_neg_right, inner_int χ _ hint_Uk', ← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [hgood] with s hs
    by_cases hmem : s ∈ Ioo 0 T
    · have hgs := hs hmem
      have hdiv_Zq : LMWeakDivFree p.c (lmLift (Zq0 s)) :=
        weakDivFree_of_weakPd 0 hgs.lmWeakDivFree_Z (hgs.lmWeakPd_Z 0)
      have hdiv_Zη : LMWeakDivFree p.c (lmLift (Zη0 s)) :=
        weakDivFree_of_weakPd 1 hgs.lmWeakDivFree_Z (hgs.lmWeakPd_Z 1)
      have hp0_dj0 : opP0 p.c hc (opDJ p.c hc J hJ k 0 (Zq0 s)) = opDJ p.c hc J hJ k 0 (Zq0 s) :=
        opP0_eq_self_of_weakDivFree hc (opDJ_weakDivFree hc hJ k 0 hdiv_Zq)
      have hp0_dj1 : opP0 p.c hc (opDJ p.c hc J hJ k 1 (Zη0 s)) = opDJ p.c hc J hJ k 1 (Zη0 s) :=
        opP0_eq_self_of_weakDivFree hc (opDJ_weakDivFree hc hJ k 1 hdiv_Zη)
      have hp0_G : opP0 p.c hc (G_path s) = G_path s :=
        opP0_eq_self_of_weakDivFree hc hgs.lmWeakDivFree_G
      change p.ν * (⟪opDJ p.c hc J hJ k 0 (opP0 p.c hc χ), ψ s • Zq0 s⟫ +
            ⟪opDJ p.c hc J hJ k 1 (opP0 p.c hc χ), ψ s • Zη0 s⟫) +
          ⟪opJ p.c hc J hJ k (opP0 p.c hc χ), ψ s • B_path s⟫ -
          ⟪opJ p.c hc J hJ k (opP0 p.c hc χ), ψ s • G_path s⟫ =
        -⟪χ, ψ s • Uk' s⟫
      simp only [Uk', mollTimeDeriv, real_inner_smul_right, inner_add_right, inner_sub_right]
      rw [inner_opDJ_antiSymm, inner_opP0_selfAdj, hp0_dj0,
        inner_opDJ_antiSymm, inner_opP0_selfAdj, hp0_dj1,
        inner_opJ_selfAdj, inner_opP0_selfAdj, opP0_comm_opJ,
        inner_opJ_selfAdj, inner_opP0_selfAdj, opP0_comm_opJ, hp0_G]
      ring
    · have h0 : ψ s = 0 := BochnerTime.eq_zero_of_tsupport_subset hψ_ts hmem
      change p.ν * (⟪_, ψ s • _⟫ + ⟪_, ψ s • _⟫) + ⟪_, ψ s • _⟫ - ⟪_, ψ s • _⟫ =
        -⟪χ, ψ s • _⟫
      simp [h0]
  linarith [hcomb, hlhs_eq, hrhs_eq]

end UnforcedLeray.Short.IIb.HorizonGluingAux
