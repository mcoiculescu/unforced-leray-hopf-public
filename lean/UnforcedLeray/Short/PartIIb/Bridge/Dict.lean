import UnforcedLeray.Short.PartIIb.Bridge.Rep

/-!
# Bridge Part II-a / Part II-b: the dictionary `toYq` / `fromYq`

Source of record: `the November 2 reference manuscript`, lines 1339-1349, 1409-1412,
1478-1480.

* `exists_hasRepY` (Rep.lean): `IsInYr P r f → ∃ F, HasRepY F f ∧ ‖F‖ = (phaseLpNorm P r f).toReal`;
* `toYq` : the chosen such `F` (the a.e.-class of `f`), with `toYq_eq_of_hasRepY` (uniqueness);
* `exists_isInYr_hasRepY` : the converse representative of `F ∈ Y_r`, `r ∈ (0,∞)`;
* `hasPtwOp_iff_hasPhaseOp` : `HasPtwOp P Lt w a ↔ HasPhaseOp Lt F A` for representatives, for any
  `Lt` mapping phase tests to phase tests (`nuLapT ν`, `driftT`, `L0T ν`, `-dy j`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.Cons.C03.Concrete

/-- Two elements of `Y_q` with a common representative are equal. -/
theorem hasRepY_unique {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)] {F G : Yq P q}
    {W : ℝ × Space → CVec3} (hF : HasRepY F W) (hG : HasRepY G W) : F = G :=
  eq_of_forall_phasePair fun _ hΦ => by
    rw [phasePair_eq_pairF_of_hasRepY F W hF hΦ, phasePair_eq_pairF_of_hasRepY G W hG hΦ]

/-- Representatives with a common element agree on pairings with phase tests (so do a.e.-equal
fields). -/
theorem pairF_eq_of_hasRepY {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)] {F : Yq P q}
    {W W' : ℝ × Space → CVec3} (hW : HasRepY F W) (hW' : HasRepY F W') {Φ : ℝ × Space → CVec3}
    (hΦ : IsPhaseTest P Φ) : pairF P Φ W = pairF P Φ W' := by
  rw [← phasePair_eq_pairF_of_hasRepY F W hW hΦ, ← phasePair_eq_pairF_of_hasRepY F W' hW' hΦ]

/-- The element of `Y_r` represented by `f ∈ Y_r` (junk-free: needs the membership proof). -/
def toYq (P : ℝ) [Fact (0 < P)] (r : ℝ) (hr : 0 < r) [Fact (1 ≤ ENNReal.ofReal r)]
    (f : ℝ × Space → CVec3) (hf : IsInYr P r f) : Yq P (ENNReal.ofReal r) :=
  Classical.choose (exists_hasRepY P r hr f hf)

theorem toYq_hasRepY (P : ℝ) [Fact (0 < P)] (r : ℝ) (hr : 0 < r) [Fact (1 ≤ ENNReal.ofReal r)]
    (f : ℝ × Space → CVec3) (hf : IsInYr P r f) : HasRepY (toYq P r hr f hf) f :=
  (Classical.choose_spec (exists_hasRepY P r hr f hf)).1

/-- **(a)** `‖toYq f‖ = ‖f‖_{Y_r}`. -/
theorem norm_toYq (P : ℝ) [Fact (0 < P)] (r : ℝ) (hr : 0 < r) [Fact (1 ≤ ENNReal.ofReal r)]
    (f : ℝ × Space → CVec3) (hf : IsInYr P r f) :
    ‖toYq P r hr f hf‖ = (phaseLpNorm P r f).toReal :=
  (Classical.choose_spec (exists_hasRepY P r hr f hf)).2

theorem toYq_eq_of_hasRepY (P : ℝ) [Fact (0 < P)] (r : ℝ) (hr : 0 < r)
    [Fact (1 ≤ ENNReal.ofReal r)] (f : ℝ × Space → CVec3) (hf : IsInYr P r f)
    {F : Yq P (ENNReal.ofReal r)} (hF : HasRepY F f) : toYq P r hr f hf = F :=
  hasRepY_unique (toYq_hasRepY P r hr f hf) hF

/-- **Converse representative**: every `F ∈ Y_q` (`q.toReal = r > 0`) is represented by a field in
`IsInYr` (the Fubini identification, `exists_isRep`), with `phaseLpNorm = ‖F‖`. -/
theorem exists_isInYr_hasRepY_q (P : ℝ) [Fact (0 < P)] (r : ℝ) (hr : 0 < r) {q : ℝ≥0∞}
    [Fact (1 ≤ q)] (hq : q ≠ ⊤) (hp : q.toReal = r) (F : Yq P q) :
    ∃ W : ℝ × Space → CVec3, IsInYr P r W ∧ HasRepY F W ∧
      (phaseLpNorm P r W).toReal = ‖F‖ := by
  obtain ⟨W, hW⟩ := UnforcedLeray.Short.PartIIa.Rep.exists_isRep hq F
  have hrep : HasRepY F W := ⟨hW.meas.aestronglyMeasurable, hW.slice⟩
  have hnorm := phaseLpNorm_eq_enorm_q r hr hq hp W F hW
  have hper : ∀ᵐ x : ℝ × Space, W (x.1 + P, x.2) = W x := by
    have hm : MeasurableSet {x : ℝ × Space | W (x.1 + P, x.2) = W x} :=
      measurableSet_eq_fun
        (hW.meas.measurable.comp (measurable_fst.add_const P |>.prodMk measurable_snd))
        hW.meas.measurable
    rw [Measure.volume_eq_prod]
    refine (Measure.ae_prod_iff_ae_ae hm).2 ?_
    have hs := (measurePreserving_add_right (volume : Measure ℝ) P).quasiMeasurePreserving.ae
      hW.slice
    filter_upwards [hW.slice, hs] with τ h1 h2
    filter_upwards [h1, h2] with y e1 e2
    have : ((τ + P : ℝ) : AddCircle P) = (τ : AddCircle P) := AddCircle.coe_add_period P τ
    rw [this] at e2
    exact e2.trans e1.symm
  refine ⟨W, ⟨hper, hW.meas.aestronglyMeasurable, ?_⟩, hrep, ?_⟩
  · rw [hnorm]; exact (enorm_lt_top)
  · rw [hnorm, toReal_enorm]

theorem exists_isInYr_hasRepY (P : ℝ) [Fact (0 < P)] (r : ℝ) (hr : 0 < r)
    [Fact (1 ≤ ENNReal.ofReal r)] (F : Yq P (ENNReal.ofReal r)) :
    ∃ W : ℝ × Space → CVec3, IsInYr P r W ∧ HasRepY F W ∧
      (phaseLpNorm P r W).toReal = ‖F‖ :=
  exists_isInYr_hasRepY_q P r hr ENNReal.ofReal_ne_top (ENNReal.toReal_ofReal hr.le) F

/-- **(b)** Distributional operators: for `Lt` preserving phase tests, `HasPtwOp` for fields is
`HasPhaseOp` for the represented elements. -/
theorem hasPtwOp_iff_hasPhaseOp {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)]
    {Lt : (ℝ × Space → CVec3) → ℝ × Space → CVec3}
    (hLt : ∀ Φ, IsPhaseTest P Φ → IsPhaseTest P (Lt Φ)) {F A : Yq P q}
    {w a : ℝ × Space → CVec3} (hw : HasRepY F w) (ha : HasRepY A a) :
    HasPtwOp P Lt w a ↔ HasPhaseOp Lt F A := by
  unfold HasPtwOp HasPhaseOp
  refine forall_congr' fun Φ => forall_congr' fun hΦ => ?_
  rw [phasePair_eq_pairF_of_hasRepY F w hw (hLt Φ hΦ), phasePair_eq_pairF_of_hasRepY A a ha hΦ]

end UnforcedLeray.Short.IIb
