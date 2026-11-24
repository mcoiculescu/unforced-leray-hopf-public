import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T18
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphFlat
import UnforcedLeray.Short.PartIIb.Tasks.LpBound23over8
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradBound
import UnforcedLeray.Short.PartIIb.Bridge.Tasks.SolSeparation
import UnforcedLeray.Short.PartIIb.Tasks.RieszThorinApplication.HrOperatorFamily.PhysUniqueCross
import UnforcedLeray.Short.PartIIb.Tasks.RieszThorinApplication.HrOperatorFamily.FlatUniqueCross
import UnforcedLeray.Short.PartIIb.Tasks.RieszThorinApplication.HrOperatorFamily.Linearity

/-!
# Part II-b, task `PartII-b:T18/1` (`HrOperatorFamily`): consistent `H_r` comparison operator family

Source of record: `the November 2 reference manuscript`, lines 1912-1938, 1992-2004.

Constructs a single profile-level operator `K_op : CProf → CProf` representing `B(T_ε - T_0)` across
`r ∈ {2, bgr, bgp}` and proves `hrComparisonOperatorFamily_proof : HrComparisonOperatorFamily`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.HrOpHelp

/-- `hMeas c r` is absolutely continuous with respect to `volume.restrict DriftWeakSHelp.Upos`. -/
theorem hMeas_ac_restrict (c r : ℝ) :
    hMeas c r ≪ (volume : Measure Coord).restrict DriftWeakSHelp.Upos := by
  unfold hMeas DriftWeakSHelp.Upos
  rw [Axi.ageμ, Measure.volume_eq_prod, ← Measure.prod_restrict]
  refine Measure.AbsolutelyContinuous.prod ?_ ?_
  · exact withDensity_absolutelyContinuous _ _
  · unfold UnforcedLeray.Cyl.avgμ
    rw [Measure.restrict_univ]
    exact (Measure.smul_absolutelyContinuous).trans
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)

/-- Every profile weak derivative `g` satisfying `HasWeakVec v d b g` is `AEStronglyMeasurable`
with respect to `hMeas c r`. -/
theorem HasWeakVec.aestronglyMeasurable_hMeas {c r : ℝ}
    {v : Coord → Fin 3 → ℝ} {d : Coord → ℝ} {b g : CProf}
    (hw : HasWeakVec v d b g) :
    AEStronglyMeasurable g (hMeas c r) := by
  have h0 : AEStronglyMeasurable (fun x : Coord => g x 0) (hMeas c r) :=
    (DriftWeakSHelp.locInt_of_tests (fun x => g x 0)
      (fun φ hφ => ((hw 0).1 φ hφ).2)).aestronglyMeasurable.mono_ac (hMeas_ac_restrict c r)
  have h1 : AEStronglyMeasurable (fun x : Coord => g x 1) (hMeas c r) :=
    (DriftWeakSHelp.locInt_of_tests (fun x => g x 1)
      (fun φ hφ => ((hw 1).1 φ hφ).2)).aestronglyMeasurable.mono_ac (hMeas_ac_restrict c r)
  have heq : g = fun x : Coord =>
      g x 0 • EuclideanSpace.single 0 (1 : ℂ) +
        g x 1 • EuclideanSpace.single 1 (1 : ℂ) := by
    ext x i
    fin_cases i <;> simp
  rw [heq]
  exact (h0.smul aestronglyMeasurable_const).add (h1.smul aestronglyMeasurable_const)

/-- For any `ObsOp`, `B.apply b gq gη` is `AEStronglyMeasurable` whenever `b, gq, gη` are. -/
theorem ObsOp.aestronglyMeasurable_apply {σ H₁ L₁ Γ : ℝ} {μ : Measure Coord}
    (B : ObsOp σ H₁ L₁ Γ) {b gq gη : CProf}
    (hb : AEStronglyMeasurable b μ) (hgq : AEStronglyMeasurable gq μ)
    (hgη : AEStronglyMeasurable gη μ) :
    AEStronglyMeasurable (B.apply b gq gη) μ := by
  have heval : Continuous (fun p : (CMerid →L[ℂ] CMerid) × CMerid => p.1 p.2) :=
    isBoundedBilinearMap_apply.continuous
  have hAq : AEStronglyMeasurable (fun x => B.Aq x (gq x)) μ :=
    heval.comp_aestronglyMeasurable (B.smooth.1.continuous.aestronglyMeasurable.prodMk hgq)
  have hAeta : AEStronglyMeasurable (fun x => B.Aeta x (gη x)) μ :=
    heval.comp_aestronglyMeasurable (B.smooth.2.1.continuous.aestronglyMeasurable.prodMk hgη)
  have hA0 : AEStronglyMeasurable (fun x => B.A0 x (b x)) μ :=
    heval.comp_aestronglyMeasurable (B.smooth.2.2.continuous.aestronglyMeasurable.prodMk hb)
  exact (hAq.add hAeta).add hA0

/-- `coordTranspose v d φ x = 0` for `x.1 ≤ 0` when `IsCoordTest φ`. -/
theorem coordTranspose_eq_zero_of_nonpos {v : Coord → Fin 3 → ℝ} {d φ : Coord → ℝ}
    (hφ : IsCoordTest φ) {x : Coord} (hx : ¬ 0 < x.1) :
    coordTranspose v d φ x = 0 := by
  have hnot : x ∉ tsupport φ := fun h => hx (hφ.supp h).1
  have hopen : IsOpen (tsupport φ)ᶜ := isClosed_tsupport φ |>.isOpen_compl
  have hev : φ =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [hopen.mem_nhds hnot] with y hy
    exact Function.notMem_support.1 (fun hs => hy (subset_tsupport φ hs))
  have h0 : φ x = 0 := hev.eq_of_nhds
  have hfd : ∀ j : Fin 3, fderiv ℝ (fun y => v y j * φ y) x = 0 := by
    intro j
    have hevj : (fun y => v y j * φ y) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) :=
      hev.mono fun y hy => by simp [hy]
    rw [hevj.fderiv_eq]; simp
  simp [coordTranspose, cpd, h0, hfd]

/-- `HasWeakVec` respects a.e. equality of the base profile on `{s > 0}`. -/
theorem hasWeakVec_congr_base {v : Coord → Fin 3 → ℝ} {d : Coord → ℝ} {b₁ b₂ g : CProf}
    (hb : ∀ᵐ x : Coord, 0 < x.1 → b₁ x = b₂ x) (hw : HasWeakVec v d b₁ g) :
    HasWeakVec v d b₂ g := by
  intro i
  obtain ⟨hint, heq⟩ := hw i
  refine ⟨fun φ hφ => ⟨?_, (hint φ hφ).2⟩, fun φ hφ => ?_⟩
  · refine (hint φ hφ).1.congr ?_
    filter_upwards [hb] with x hx
    by_cases hpos : 0 < x.1
    · rw [hx hpos]
    · rw [coordTranspose_eq_zero_of_nonpos hφ hpos]; simp
  · rw [heq φ hφ]
    refine integral_congr_ae ?_
    filter_upwards [hb] with x hx
    by_cases hpos : 0 < x.1
    · rw [hx hpos]
    · rw [coordTranspose_eq_zero_of_nonpos hφ hpos]; simp

/-- Combined physical and flat response and weak-derivative witness tuple at exponent `r`. -/
def IsRespTuple (ν c ε : ℝ) (μ : ℂ) (r : ℝ)
    (F bε Sbε Qbε Ebε b0 Sb0 Qb0 Eb0 : CProf) : Prop :=
  InHr c r bε ∧ IsResponse ν c ε μ r F bε ∧
  HasWeakVec vS dZero bε Sbε ∧ HasWeakVec (vQ ε) (dQ ε) bε Qbε ∧ HasWeakVec vEta dZero bε Ebε ∧
  InFlatClass c r b0 ∧ IsFlatResponse ν μ F b0 ∧
  HasWeakVec vS dZero b0 Sb0 ∧ HasWeakVec vQ0 dZero b0 Qb0 ∧ HasWeakVec vEta dZero b0 Eb0

/-- Exponent and spectral gap bounds for `r ∈ {2, bgr, bgp}`. -/
theorem r_mem_bounds {r Γ : ℝ} {μ : ℂ} (hr : r ∈ ({2, bgr, bgp} : Set ℝ))
    (hΓ1 : 1 ≤ Γ) (hgap : Γ⁻¹ ≤ μ.re + 1 / 46) :
    1 < r ∧ r < 3 ∧ Γ⁻¹ ≤ μ.re + (3 / r - 1) / 2 ∧ 0 < μ.re + (3 / r - 1) / 2 := by
  have hΓ0 : 0 < Γ := lt_of_lt_of_le one_pos hΓ1
  have h146 : (1 / 46 : ℝ) ≤ (3 / r - 1) / 2 := by
    rcases hr with rfl | rfl | rfl <;> norm_num [bgr, bgp]
  have hr1 : 1 < r := by
    rcases hr with rfl | rfl | rfl <;> norm_num [bgr, bgp]
  have hr3 : r < 3 := by
    rcases hr with rfl | rfl | rfl <;> norm_num [bgr, bgp]
  refine ⟨hr1, hr3, by linarith, lt_of_lt_of_le (inv_pos.2 hΓ0) (by linarith)⟩

/-- Existence of an `IsRespTuple` for any `F ∈ H_r` with `r ∈ {2, bgr, bgp}`. -/
theorem exists_isRespTuple {Γ ν c ε r : ℝ} {μ : ℂ}
    (hr : r ∈ ({2, bgr, bgp} : Set ℝ)) (hΓ1 : 1 ≤ Γ) (hμΓ : ‖μ‖ ≤ Γ)
    (hgap : Γ⁻¹ ≤ μ.re + 1 / 46) (hν : 0 < ν) (hc : 0 < c)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hP : 2 * ε * c ≤ 1)
    {F : CProf} (hF : InHr c r F) :
    ∃ bε Sbε Qbε Ebε b0 Sb0 Qb0 Eb0 : CProf,
      IsRespTuple ν c ε μ r F bε Sbε Qbε Ebε b0 Sb0 Qb0 Eb0 := by
  obtain ⟨hr1, hr3, hgap_r, hμ_pos⟩ := r_mem_bounds hr hΓ1 hgap
  obtain ⟨_, -, hphys_ex⟩ := profileGraphPhys_proof r hr1 hr3 μ hμ_pos
  obtain ⟨⟨bε, hbε_in, hbε_resp⟩, -⟩ := hphys_ex ν c ε hν hc hε0 hε1 hP F hF
  obtain ⟨_, _, hphys_poly⟩ := phys_graph_poly r hr1 hr3
  obtain ⟨Sbε, Qbε, Ebε, hSε, hQε, hEε, -⟩ :=
    hphys_poly Γ ν c ε μ hΓ1 hμΓ hgap_r hν hc hε0 hε1 hP F bε hF hbε_resp
  obtain ⟨_, -, hflat_ex⟩ := profileGraphFlat_proof r hr1 hr3 μ hμ_pos
  obtain ⟨b0, hb0_class, hb0_resp, -⟩ := hflat_ex ν c hν hc F hF
  obtain ⟨Sb0, Qb0, Eb0, hS0, hQ0, hE0, -⟩ := hb0_class.deriv
  exact ⟨bε, Sbε, Qbε, Ebε, b0, Sb0, Qb0, Eb0,
    hbε_in, hbε_resp, hSε, hQε, hEε, hb0_class, hb0_resp, hS0, hQ0, hE0⟩

/-- Cross-exponent uniqueness of `IsRespTuple` components on `{s > 0}`. -/
theorem isRespTuple_unique_pos {Γ ν c ε r₁ r₂ : ℝ} {μ : ℂ}
    (hr₁ : r₁ ∈ ({2, bgr, bgp} : Set ℝ)) (hr₂ : r₂ ∈ ({2, bgr, bgp} : Set ℝ))
    (hΓ1 : 1 ≤ Γ) (hgap : Γ⁻¹ ≤ μ.re + 1 / 46) (hν : 0 < ν) (hc : 0 < c) (hε0 : 0 < ε)
    {F₁ F₂ bε₁ Sbε₁ Qbε₁ Ebε₁ b0₁ Sb0₁ Qb0₁ Eb0₁
     bε₂ Sbε₂ Qbε₂ Ebε₂ b0₂ Sb0₂ Qb0₂ Eb0₂ : CProf}
    (hF₁ : InHr c r₁ F₁) (hF₂ : InHr c r₂ F₂) (hFF : F₁ =ᵐ[dm c] F₂)
    (ht₁ : IsRespTuple ν c ε μ r₁ F₁ bε₁ Sbε₁ Qbε₁ Ebε₁ b0₁ Sb0₁ Qb0₁ Eb0₁)
    (ht₂ : IsRespTuple ν c ε μ r₂ F₂ bε₂ Sbε₂ Qbε₂ Ebε₂ b0₂ Sb0₂ Qb0₂ Eb0₂) :
    ∀ᵐ x : Coord, 0 < x.1 →
      bε₁ x = bε₂ x ∧ Sbε₁ x = Sbε₂ x ∧ Qbε₁ x = Qbε₂ x ∧ Ebε₁ x = Ebε₂ x ∧
      b0₁ x = b0₂ x ∧ Sb0₁ x = Sb0₂ x ∧ Qb0₁ x = Qb0₂ x ∧ Eb0₁ x = Eb0₂ x := by
  obtain ⟨hr₁1, hr₁3, _, hμ₁⟩ := r_mem_bounds hr₁ hΓ1 hgap
  obtain ⟨hr₂1, hr₂3, _, hμ₂⟩ := r_mem_bounds hr₂ hΓ1 hgap
  obtain ⟨hbε₁, hresp₁, hSε₁, hQε₁, hEε₁, hbc₁, hb0₁, hS0₁, hQ0₁, hE0₁⟩ := ht₁
  obtain ⟨hbε₂, hresp₂, hSε₂, hQε₂, hEε₂, hbc₂, hb0₂, hS0₂, hQ0₂, hE0₂⟩ := ht₂
  have ebε : ∀ᵐ x : Coord, 0 < x.1 → bε₁ x = bε₂ x :=
    physResponse_unique_cross hc hε0 hν hr₁1 hr₁3 hr₂1 hr₂3 hμ₁ hμ₂
      hF₁ hF₂ hFF hbε₁ hresp₁ hbε₂ hresp₂
  have eSε : ∀ᵐ x : Coord, 0 < x.1 → Sbε₁ x = Sbε₂ x :=
    GradBoundHelp.hasWeakVec_unique (hasWeakVec_congr_base ebε hSε₁) hSε₂
  have eQε : ∀ᵐ x : Coord, 0 < x.1 → Qbε₁ x = Qbε₂ x :=
    GradBoundHelp.hasWeakVec_unique (hasWeakVec_congr_base ebε hQε₁) hQε₂
  have eEε : ∀ᵐ x : Coord, 0 < x.1 → Ebε₁ x = Ebε₂ x :=
    GradBoundHelp.hasWeakVec_unique (hasWeakVec_congr_base ebε hEε₁) hEε₂
  have eb0 : ∀ᵐ x : Coord, 0 < x.1 → b0₁ x = b0₂ x :=
    flatResponse_unique_cross hc hν hr₁1 hr₁3 hr₂1 hr₂3 hμ₁ hμ₂
      hF₁ hF₂ hFF hbc₁ hb0₁ hbc₂ hb0₂
  have eS0 : ∀ᵐ x : Coord, 0 < x.1 → Sb0₁ x = Sb0₂ x :=
    GradBoundHelp.hasWeakVec_unique (hasWeakVec_congr_base eb0 hS0₁) hS0₂
  have eQ0 : ∀ᵐ x : Coord, 0 < x.1 → Qb0₁ x = Qb0₂ x :=
    GradBoundHelp.hasWeakVec_unique (hasWeakVec_congr_base eb0 hQ0₁) hQ0₂
  have eE0 : ∀ᵐ x : Coord, 0 < x.1 → Eb0₁ x = Eb0₂ x :=
    GradBoundHelp.hasWeakVec_unique (hasWeakVec_congr_base eb0 hE0₁) hE0₂
  filter_upwards [ebε, eSε, eQε, eEε, eb0, eS0, eQ0, eE0] with x h1 h2 h3 h4 h5 h6 h7 h8 hpos
  exact ⟨h1 hpos, h2 hpos, h3 hpos, h4 hpos, h5 hpos, h6 hpos, h7 hpos, h8 hpos⟩

/-- Bundled response and weak-derivative tuple `(r, bε, Sbε, Qbε, Ebε, b0, Sb0, Qb0, Eb0)`. -/
structure RespData where
  r : ℝ
  bε : CProf
  Sbε : CProf
  Qbε : CProf
  Ebε : CProf
  b0 : CProf
  Sb0 : CProf
  Qb0 : CProf
  Eb0 : CProf

/-- Predicate that `d : RespData` is a valid response tuple for `F` at `d.r ∈ {2, bgr, bgp}`. -/
def ValidRespData (ν c ε : ℝ) (μ : ℂ) (F : CProf) (d : RespData) : Prop :=
  d.r ∈ ({2, bgr, bgp} : Set ℝ) ∧ InHr c d.r F ∧
    IsRespTuple ν c ε μ d.r F d.bε d.Sbε d.Qbε d.Ebε d.b0 d.Sb0 d.Qb0 d.Eb0

/-- Profile-level comparison operator `K_op F = B(b_ε - b_0)`. -/
def kOp (ν c σ H₁ L₁ Γ ε : ℝ) (μ : ℂ) (B : ObsOp σ H₁ L₁ Γ) (F : CProf) : CProf :=
  letI := Classical.propDecidable
  if h : ∃ d : RespData, ValidRespData ν c ε μ F d then
    let d := h.choose
    B.apply (d.bε - d.b0) (dqOf ε d.bε d.Sbε d.Qbε d.Ebε - d.Qb0) (d.Ebε - d.Eb0)
  else 0

/-- For any `r ∈ {2, bgr, bgp}`, `F ∈ H_r`, and any `IsRespTuple` for `F` at `r`, `kOp` agrees
with `B.apply (bε - b0) (dqOf ε bε Sbε Qbε Ebε - Qb0) (Ebε - Eb0)` Lebesgue-a.e. on `{s > 0}`. -/
theorem kOp_ae_pos_of_isRespTuple {Γ ν c σ H₁ L₁ ε r : ℝ} {μ : ℂ}
    (B : ObsOp σ H₁ L₁ Γ) (hr : r ∈ ({2, bgr, bgp} : Set ℝ))
    (hΓ1 : 1 ≤ Γ) (hgap : Γ⁻¹ ≤ μ.re + 1 / 46) (hν : 0 < ν) (hc : 0 < c) (hε0 : 0 < ε)
    {F bε Sbε Qbε Ebε b0 Sb0 Qb0 Eb0 : CProf} (hF : InHr c r F)
    (ht : IsRespTuple ν c ε μ r F bε Sbε Qbε Ebε b0 Sb0 Qb0 Eb0) :
    ∀ᵐ x : Coord, 0 < x.1 →
      kOp ν c σ H₁ L₁ Γ ε μ B F x =
        B.apply (bε - b0) (dqOf ε bε Sbε Qbε Ebε - Qb0) (Ebε - Eb0) x := by
  have h : ∃ d : RespData, ValidRespData ν c ε μ F d :=
    ⟨⟨r, bε, Sbε, Qbε, Ebε, b0, Sb0, Qb0, Eb0⟩, hr, hF, ht⟩
  obtain ⟨hr', hF', ht'⟩ := h.choose_spec
  have hk : kOp ν c σ H₁ L₁ Γ ε μ B F =
      B.apply (h.choose.bε - h.choose.b0)
        (dqOf ε h.choose.bε h.choose.Sbε h.choose.Qbε h.choose.Ebε - h.choose.Qb0)
        (h.choose.Ebε - h.choose.Eb0) := by
    unfold kOp
    exact dite_eq_left_of_eq_true (eq_true h)
  have huniq := isRespTuple_unique_pos hr' hr hΓ1 hgap hν hc hε0 hF' hF (EventuallyEq.refl _ _) ht' ht
  filter_upwards [huniq] with x hx hpos
  obtain ⟨e1, e2, e3, e4, e5, -, e7, e8⟩ := hx hpos
  rw [hk]
  have ed : (h.choose.bε - h.choose.b0) x = (bε - b0) x := by simp [e1, e5]
  have edq : (dqOf ε h.choose.bε h.choose.Sbε h.choose.Qbε h.choose.Ebε - h.choose.Qb0) x =
      (dqOf ε bε Sbε Qbε Ebε - Qb0) x := by
    rw [Pi.sub_apply, Pi.sub_apply, dqOf_eq_add, dqOf_eq_add, e1, e2, e3, e4, e7]
  have egη : (h.choose.Ebε - h.choose.Eb0) x = (Ebε - Eb0) x := by simp [e4, e8]
  simp only [ObsOp.apply, ed, edq, egη]

/-- Sum of two `IsRespTuple`s at exponent `r`. -/
theorem isRespTuple_add {ν c ε r : ℝ} {μ : ℂ} (hc : 0 < c) (hε0 : 0 < ε) (hr1 : 1 < r)
    {F₁ bε₁ Sbε₁ Qbε₁ Ebε₁ b0₁ Sb0₁ Qb0₁ Eb0₁
     F₂ bε₂ Sbε₂ Qbε₂ Ebε₂ b0₂ Sb0₂ Qb0₂ Eb0₂ : CProf}
    (hF₁ : InHr c r F₁) (hF₂ : InHr c r F₂)
    (ht₁ : IsRespTuple ν c ε μ r F₁ bε₁ Sbε₁ Qbε₁ Ebε₁ b0₁ Sb0₁ Qb0₁ Eb0₁)
    (ht₂ : IsRespTuple ν c ε μ r F₂ bε₂ Sbε₂ Qbε₂ Ebε₂ b0₂ Sb0₂ Qb0₂ Eb0₂) :
    IsRespTuple ν c ε μ r (F₁ + F₂) (bε₁ + bε₂) (Sbε₁ + Sbε₂) (Qbε₁ + Qbε₂) (Ebε₁ + Ebε₂)
      (b0₁ + b0₂) (Sb0₁ + Sb0₂) (Qb0₁ + Qb0₂) (Eb0₁ + Eb0₂) := by
  obtain ⟨hbε₁, hresp₁, hSε₁, hQε₁, hEε₁, hbc₁, hb0₁, hS0₁, hQ0₁, hE0₁⟩ := ht₁
  obtain ⟨hbε₂, hresp₂, hSε₂, hQε₂, hEε₂, hbc₂, hb0₂, hS0₂, hQ0₂, hE0₂⟩ := ht₂
  exact ⟨inHr_add hbε₁ hbε₂, isResponse_add hc hε0 hr1 hF₁ hF₂ hbε₁ hbε₂ hresp₁ hresp₂,
    hasWeakVec_add hSε₁ hSε₂, hasWeakVec_add hQε₁ hQε₂, hasWeakVec_add hEε₁ hEε₂,
    inFlatClass_add hbc₁ hbc₂, isFlatResponse_add hb0₁ hb0₂,
    hasWeakVec_add hS0₁ hS0₂, hasWeakVec_add hQ0₁ hQ0₂, hasWeakVec_add hE0₁ hE0₂⟩

/-- Scalar multiple of an `IsRespTuple` at exponent `r`. -/
theorem isRespTuple_smul {ν c ε r : ℝ} {μ : ℂ} (a : ℂ) (hc : 0 < c) (hε0 : 0 < ε) (hr1 : 1 < r)
    {F bε Sbε Qbε Ebε b0 Sb0 Qb0 Eb0 : CProf}
    (hF : InHr c r F) (ht : IsRespTuple ν c ε μ r F bε Sbε Qbε Ebε b0 Sb0 Qb0 Eb0) :
    IsRespTuple ν c ε μ r (a • F) (a • bε) (a • Sbε) (a • Qbε) (a • Ebε)
      (a • b0) (a • Sb0) (a • Qb0) (a • Eb0) := by
  obtain ⟨hbε, hresp, hSε, hQε, hEε, hbc, hb0, hS0, hQ0, hE0⟩ := ht
  exact ⟨inHr_smul a hbε, isResponse_smul a hc hε0 hr1 hF hbε hresp,
    hasWeakVec_smul a hSε, hasWeakVec_smul a hQε, hasWeakVec_smul a hEε,
    inFlatClass_smul a hbc, isFlatResponse_smul a hb0,
    hasWeakVec_smul a hS0, hasWeakVec_smul a hQ0, hasWeakVec_smul a hE0⟩

end UnforcedLeray.Short.IIb.HrOpHelp

namespace UnforcedLeray.Short.IIb

open HrOpHelp

/-- **`PartII-b:T18/1` (`hrComparisonOperatorFamily_proof`)** (SP 1912-1938, 1992-2004):
there is a consistent `ℂ`-linear operator family `K_op : CProf → CProf` across `r ∈ {2, bgr, bgp}`
representing `B(T_ε - T_0)` such that `CompBoundAt` at exponent `r` is equivalent to the `H_r`
norm bound `hNorm c r (K_op F) ≤ ENNReal.ofReal M * hNorm c r F`. -/
theorem hrComparisonOperatorFamily_proof : UnforcedLeray.Short.IIb.HrComparisonOperatorFamily := by
  intro Γ ν c σ H₁ L₁ μ hΓ1 hνΓ1 hνΓ hcΓ hcinvΓ hσΓ hH₁ hL₁ hμΓ hgap hν hc hσ B ε hε0 hε1 hP
  refine ⟨kOp ν c σ H₁ L₁ Γ ε μ B, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · -- meas
    intro r hr F hF
    obtain ⟨bε, Sbε, Qbε, Ebε, b0, Sb0, Qb0, Eb0, ht⟩ :=
      exists_isRespTuple hr hΓ1 hμΓ hgap hν hc hε0 hε1 hP hF
    have hpos := kOp_ae_pos_of_isRespTuple B hr hΓ1 hgap hν hc hε0 hF ht
    have hae : kOp ν c σ H₁ L₁ Γ ε μ B F =ᵐ[hMeas c r]
        B.apply (bε - b0) (dqOf ε bε Sbε Qbε Ebε - Qb0) (Ebε - Eb0) :=
      ae_hMeas_of_ae_pos hc hpos
    obtain ⟨hbε, -, hSε, hQε, hEε, hbc, -, -, hQ0, hE0⟩ := ht
    have hDq : HasWeakVec vQ0 dZero bε (dqOf ε bε Sbε Qbε Ebε) :=
      hasWeakVec_dqOf ε hSε hQε hEε
    have hm_b : AEStronglyMeasurable (bε - b0) (hMeas c r) :=
      hbε.meas.sub hbc.inHr.meas
    have hm_gq : AEStronglyMeasurable (dqOf ε bε Sbε Qbε Ebε - Qb0) (hMeas c r) :=
      HasWeakVec.aestronglyMeasurable_hMeas (flatCls_hasWeakVec_sub hDq hQ0)
    have hm_gη : AEStronglyMeasurable (Ebε - Eb0) (hMeas c r) :=
      HasWeakVec.aestronglyMeasurable_hMeas (flatCls_hasWeakVec_sub hEε hE0)
    exact (ObsOp.aestronglyMeasurable_apply B hm_b hm_gq hm_gη).congr hae.symm
  · -- congr_ae
    intro r hr F₁ F₂ hF₁ hF₂ hFF
    obtain ⟨bε₁, Sbε₁, Qbε₁, Ebε₁, b0₁, Sb0₁, Qb0₁, Eb0₁, ht₁⟩ :=
      exists_isRespTuple hr hΓ1 hμΓ hgap hν hc hε0 hε1 hP hF₁
    obtain ⟨bε₂, Sbε₂, Qbε₂, Ebε₂, b0₂, Sb0₂, Qb0₂, Eb0₂, ht₂⟩ :=
      exists_isRespTuple hr hΓ1 hμΓ hgap hν hc hε0 hε1 hP hF₂
    have hk₁ := kOp_ae_pos_of_isRespTuple B hr hΓ1 hgap hν hc hε0 hF₁ ht₁
    have hk₂ := kOp_ae_pos_of_isRespTuple B hr hΓ1 hgap hν hc hε0 hF₂ ht₂
    have huniq := isRespTuple_unique_pos hr hr hΓ1 hgap hν hc hε0 hF₁ hF₂ hFF ht₁ ht₂
    have hpos : ∀ᵐ x : Coord, 0 < x.1 →
        kOp ν c σ H₁ L₁ Γ ε μ B F₁ x = kOp ν c σ H₁ L₁ Γ ε μ B F₂ x := by
      filter_upwards [hk₁, hk₂, huniq] with x e1 e2 hu hpos
      obtain ⟨u1, u2, u3, u4, u5, -, u7, u8⟩ := hu hpos
      rw [e1 hpos, e2 hpos]
      have ed : (bε₁ - b0₁) x = (bε₂ - b0₂) x := by simp [u1, u5]
      have edq : (dqOf ε bε₁ Sbε₁ Qbε₁ Ebε₁ - Qb0₁) x =
          (dqOf ε bε₂ Sbε₂ Qbε₂ Ebε₂ - Qb0₂) x := by
        rw [Pi.sub_apply, Pi.sub_apply, dqOf_eq_add, dqOf_eq_add, u1, u2, u3, u4, u7]
      have egη : (Ebε₁ - Eb0₁) x = (Ebε₂ - Eb0₂) x := by simp [u4, u8]
      simp only [ObsOp.apply, ed, edq, egη]
    have hdm : dm c = hMeas c 0 := by
      unfold dm hMeas
      congr 1; norm_num
    rw [hdm]
    exact ae_hMeas_of_ae_pos hc hpos
  · -- map_add_ae
    intro r hr F₁ F₂ hF₁ hF₂
    obtain ⟨hr1, -⟩ := r_mem_bounds hr hΓ1 hgap
    obtain ⟨bε₁, Sbε₁, Qbε₁, Ebε₁, b0₁, Sb0₁, Qb0₁, Eb0₁, ht₁⟩ :=
      exists_isRespTuple hr hΓ1 hμΓ hgap hν hc hε0 hε1 hP hF₁
    obtain ⟨bε₂, Sbε₂, Qbε₂, Ebε₂, b0₂, Sb0₂, Qb0₂, Eb0₂, ht₂⟩ :=
      exists_isRespTuple hr hΓ1 hμΓ hgap hν hc hε0 hε1 hP hF₂
    have ht₁₂ := isRespTuple_add hc hε0 hr1 hF₁ hF₂ ht₁ ht₂
    have hk₁ := kOp_ae_pos_of_isRespTuple B hr hΓ1 hgap hν hc hε0 hF₁ ht₁
    have hk₂ := kOp_ae_pos_of_isRespTuple B hr hΓ1 hgap hν hc hε0 hF₂ ht₂
    have hk₁₂ := kOp_ae_pos_of_isRespTuple B hr hΓ1 hgap hν hc hε0 (inHr_add hF₁ hF₂) ht₁₂
    have hpos : ∀ᵐ x : Coord, 0 < x.1 →
        kOp ν c σ H₁ L₁ Γ ε μ B (F₁ + F₂) x =
          (kOp ν c σ H₁ L₁ Γ ε μ B F₁ + kOp ν c σ H₁ L₁ Γ ε μ B F₂) x := by
      filter_upwards [hk₁, hk₂, hk₁₂] with x e1 e2 e12 hpos
      simp only [Pi.add_apply, e1 hpos, e2 hpos, e12 hpos]
      have hd : (bε₁ + bε₂) - (b0₁ + b0₂) = (bε₁ - b0₁) + (bε₂ - b0₂) := by abel
      have hdq : dqOf ε (bε₁ + bε₂) (Sbε₁ + Sbε₂) (Qbε₁ + Qbε₂) (Ebε₁ + Ebε₂) - (Qb0₁ + Qb0₂) =
          (dqOf ε bε₁ Sbε₁ Qbε₁ Ebε₁ - Qb0₁) + (dqOf ε bε₂ Sbε₂ Qbε₂ Ebε₂ - Qb0₂) := by
        rw [dqOf_add]; abel
      have hgη : (Ebε₁ + Ebε₂) - (Eb0₁ + Eb0₂) = (Ebε₁ - Eb0₁) + (Ebε₂ - Eb0₂) := by abel
      rw [hd, hdq, hgη, obsOp_apply_add, Pi.add_apply]
    have hdm : dm c = hMeas c 0 := by
      unfold dm hMeas
      congr 1; norm_num
    rw [hdm]
    exact ae_hMeas_of_ae_pos hc hpos
  · -- map_smul_ae
    intro r hr a F hF
    obtain ⟨hr1, -⟩ := r_mem_bounds hr hΓ1 hgap
    obtain ⟨bε, Sbε, Qbε, Ebε, b0, Sb0, Qb0, Eb0, ht⟩ :=
      exists_isRespTuple hr hΓ1 hμΓ hgap hν hc hε0 hε1 hP hF
    have hta := isRespTuple_smul a hc hε0 hr1 hF ht
    have hk := kOp_ae_pos_of_isRespTuple B hr hΓ1 hgap hν hc hε0 hF ht
    have hka := kOp_ae_pos_of_isRespTuple B hr hΓ1 hgap hν hc hε0 (inHr_smul a hF) hta
    have hpos : ∀ᵐ x : Coord, 0 < x.1 →
        kOp ν c σ H₁ L₁ Γ ε μ B (a • F) x = (a • kOp ν c σ H₁ L₁ Γ ε μ B F) x := by
      filter_upwards [hk, hka] with x e1 ea hpos
      simp only [Pi.smul_apply, e1 hpos, ea hpos]
      have hd : a • bε - a • b0 = a • (bε - b0) := (smul_sub a bε b0).symm
      have hdq : dqOf ε (a • bε) (a • Sbε) (a • Qbε) (a • Ebε) - a • Qb0 =
          a • (dqOf ε bε Sbε Qbε Ebε - Qb0) := by
        rw [dqOf_smul, smul_sub]
      have hgη : a • Ebε - a • Eb0 = a • (Ebε - Eb0) := (smul_sub a Ebε Eb0).symm
      rw [hd, hdq, hgη, obsOp_apply_smul, Pi.smul_apply]
    have hdm : dm c = hMeas c 0 := by
      unfold dm hMeas
      congr 1; norm_num
    rw [hdm]
    exact ae_hMeas_of_ae_pos hc hpos
  · -- CompBoundAt ↔ norm bound
    intro r hr M hM
    obtain ⟨hr1, hr3, hgap_r, _⟩ := r_mem_bounds hr hΓ1 hgap
    constructor
    · intro hCB F hF
      obtain ⟨bε, Sbε, Qbε, Ebε, b0, Sb0, Qb0, Eb0, ht⟩ :=
        exists_isRespTuple hr hΓ1 hμΓ hgap hν hc hε0 hε1 hP hF
      have hk := kOp_ae_pos_of_isRespTuple B hr hΓ1 hgap hν hc hε0 hF ht
      obtain ⟨hbε, hrespε, hSε, hQε, hEε, hbc0, hresp0, -, hQ0, hE0⟩ := ht
      obtain ⟨gq, gη, hgq, hgη, hbnd⟩ := hCB F bε b0 hF hbε hrespε hresp0 hbc0
      have hDq : HasWeakVec vQ0 dZero (bε - b0) (dqOf ε bε Sbε Qbε Ebε - Qb0) :=
        flatCls_hasWeakVec_sub (hasWeakVec_dqOf ε hSε hQε hEε) hQ0
      have hDη : HasWeakVec vEta dZero (bε - b0) (Ebε - Eb0) :=
        flatCls_hasWeakVec_sub hEε hE0
      have egq := GradBoundHelp.hasWeakVec_unique hDq hgq
      have egη := GradBoundHelp.hasWeakVec_unique hDη hgη
      have hpos : ∀ᵐ x : Coord, 0 < x.1 →
          kOp ν c σ H₁ L₁ Γ ε μ B F x = B.apply (bε - b0) gq gη x := by
        filter_upwards [hk, egq, egη] with x ek uq uη hpos
        rw [ek hpos]
        simp only [ObsOp.apply, uq hpos, uη hpos]
      have hae : kOp ν c σ H₁ L₁ Γ ε μ B F =ᵐ[hMeas c r] B.apply (bε - b0) gq gη :=
        ae_hMeas_of_ae_pos hc hpos
      unfold hNorm at hbnd ⊢
      rwa [eLpNorm_congr_ae hae]
    · intro hK F bε b0 hF hbε hrespε hresp0 hbc0
      obtain ⟨_, _, hphys_poly⟩ := phys_graph_poly r hr1 hr3
      obtain ⟨Sbε, Qbε, Ebε, hSε, hQε, hEε, -⟩ :=
        hphys_poly Γ ν c ε μ hΓ1 hμΓ hgap_r hν hc hε0 hε1 hP F bε hF hrespε
      obtain ⟨Sb0, Qb0, Eb0, hS0, hQ0, hE0, -⟩ := hbc0.deriv
      have ht : IsRespTuple ν c ε μ r F bε Sbε Qbε Ebε b0 Sb0 Qb0 Eb0 :=
        ⟨hbε, hrespε, hSε, hQε, hEε, hbc0, hresp0, hS0, hQ0, hE0⟩
      have hk := kOp_ae_pos_of_isRespTuple B hr hΓ1 hgap hν hc hε0 hF ht
      have hae : B.apply (bε - b0) (dqOf ε bε Sbε Qbε Ebε - Qb0) (Ebε - Eb0) =ᵐ[hMeas c r]
          kOp ν c σ H₁ L₁ Γ ε μ B F :=
        (ae_hMeas_of_ae_pos hc hk).symm
      refine ⟨dqOf ε bε Sbε Qbε Ebε - Qb0, Ebε - Eb0,
        flatCls_hasWeakVec_sub (hasWeakVec_dqOf ε hSε hQε hEε) hQ0,
        flatCls_hasWeakVec_sub hEε hE0, ?_⟩
      unfold hNorm
      rw [eLpNorm_congr_ae hae]
      exact hK F hF

end UnforcedLeray.Short.IIb

end
