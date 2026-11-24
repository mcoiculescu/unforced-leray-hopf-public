import UnforcedLeray.Short.PartIIb.Tasks.BodySource.SliceHolder.CylProjection.P0SliceLiftH1.Needed
import UnforcedLeray.Short.PartIIb.Tasks.GlobalEnergy.TailSourceSlice.SliceP0Lift

/-!
# `PartII-b:F5/2/2/3` (`P0SliceLiftH1Loc`): jointly measurable slice cylinder Leray projection of `-flatBv` in `H¹`

Source of record: `the November 2 reference manuscript` (SP), lines 2213–2239 and
2269–2282 (`g = -P_0(v_c · ∇b_0 + b_0 · ∇v_c)`, slice `H¹` projection and curl preservation).

Proves `p0SliceLiftH1Loc_proof : UnforcedLeray.Short.IIb.P0SliceLiftH1Needed.P0SliceLiftH1Loc`:
1. Applies `TailSliceP0LiftAux.p0SliceLiftH1_of_loc` to obtain `(g₀, gq₀, gη₀)` with joint
   `StronglyMeasurable`, `QPeriodic c g₀`, `HasWeakVec`, `IsBodySource`, and the `sliceH1Norm`
   bound with constant `2`;
2. Tests `hg₀_src.equation` against perpendicular gradients `∇^⊥ φ = (∂_η φ, -∂_q φ)` of coordinate
   tests `IsCoordTest φ` and integrates by parts via `HasWeakVec` on `(g₀, gq₀, gη₀)` and
   `(U, Uq, Uη)` to identify `profCurl gq₀ gη₀ = -profCurl Uq Uη` a.e. on `{s > 0}` (via
   `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`), hence on `B0579.cell c` for a.e. `s > 0`
   by Fubini;
3. Modifies `(gq₀, gη₀)` to `0` on `N_meas ×ˢ univ` for a measurable null superset `N_meas` of the
   bad slices so the curl dichotomy holds for every `s > 0` while preserving `StronglyMeasurable`,
   `HasWeakVec`, and the `sliceH1Norm` bound.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete

/-! ### 1. Perpendicular-gradient planar solenoidal tests and weak curl pairing on `Coord` -/

private theorem hasFDerivAt_partial_coord {φ : Coord → ℝ} (hφ : ContDiff ℝ ∞ φ) (v x : Coord) :
    HasFDerivAt (fun y => fderiv ℝ φ y v) ((fderiv ℝ (fderiv ℝ φ) x).flip v) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    ((ContDiff.fderiv_right (m := ∞) hφ (by simp)).differentiable (by simp)) x
  simpa using hd.hasFDerivAt.clm_apply (hasFDerivAt_const v x)

private theorem isCoordTest_partial_coord {φ : Coord → ℝ} (hφ : IsCoordTest φ) (v : Coord) :
    IsCoordTest (fun x => fderiv ℝ φ x v) :=
  ⟨(ContDiff.fderiv_right (m := ∞) hφ.smooth (by simp)).clm_apply contDiff_const,
    hφ.compact.fderiv_apply (𝕜 := ℝ) v,
    (tsupport_fderiv_apply_subset (𝕜 := ℝ) v).trans hφ.supp⟩

private theorem isCoordTest_neg_coord {f : Coord → ℝ} (hf : IsCoordTest f) :
    IsCoordTest (fun x => -f x) := by
  have hsub : Function.support (fun x => -f x) ⊆ Function.support f := by
    intro x hx h0
    exact (Function.mem_support.1 hx) (by simp [h0])
  exact ⟨hf.smooth.neg, hf.compact.neg,
    (closure_minimal (hsub.trans (subset_tsupport f)) (isClosed_tsupport f)).trans hf.supp⟩

private def perpGradCoord (φ : Coord → ℝ) : Coord → Fin 2 → ℝ :=
  fun x => ![cpd 2 φ x, -cpd 1 φ x]

private theorem isPlanarSolTest_perpGradCoord {φ : Coord → ℝ} (hφ : IsCoordTest φ) :
    IsPlanarSolTest (perpGradCoord φ) where
  smooth i := by
    fin_cases i
    · exact isCoordTest_partial_coord hφ (cdir 2)
    · exact isCoordTest_neg_coord (isCoordTest_partial_coord hφ (cdir 1))
  div_free x := by
    change fderiv ℝ (fun y => fderiv ℝ φ y (cdir 2)) x (cdir 1) +
        fderiv ℝ (fun y => -(fderiv ℝ φ y (cdir 1))) x (cdir 2) = 0
    have hsymm : IsSymmSndFDerivAt ℝ φ x := hφ.smooth.contDiffAt.isSymmSndFDerivAt (by simp)
    have hA : fderiv ℝ (fun y => fderiv ℝ φ y (cdir 2)) x (cdir 1) =
        fderiv ℝ (fderiv ℝ φ) x (cdir 1) (cdir 2) := by
      rw [(hasFDerivAt_partial_coord hφ.smooth (cdir 2) x).fderiv]; rfl
    have hB : fderiv ℝ (fun y => -(fderiv ℝ φ y (cdir 1))) x (cdir 2) =
        -(fderiv ℝ (fderiv ℝ φ) x (cdir 2) (cdir 1)) := by
      rw [(hasFDerivAt_partial_coord hφ.smooth (cdir 1) x).fun_neg.fderiv]; rfl
    rw [hA, hB, hsymm (cdir 1) (cdir 2)]
    ring

private theorem coordTranspose_vQ0_dZero (φ : Coord → ℝ) (x : Coord) :
    coordTranspose vQ0 dZero φ x = -cpd 1 φ x := by
  unfold coordTranspose vQ0 dZero
  rw [Fin.sum_univ_three]
  simp [cpd]

private theorem coordTranspose_vEta_dZero (φ : Coord → ℝ) (x : Coord) :
    coordTranspose vEta dZero φ x = -cpd 2 φ x := by
  unfold coordTranspose vEta dZero
  rw [Fin.sum_univ_three]
  simp [cpd]

private theorem integral_profCurl_mul_test {b bq bη : CProf}
    (hwq : HasWeakVec vQ0 dZero b bq) (hwη : HasWeakVec vEta dZero b bη)
    {φ : Coord → ℝ} (hφ : IsCoordTest φ) :
    Integrable (fun x => profCurl bq bη x * (φ x : ℂ)) ∧
      ∫ x, profCurl bq bη x * (φ x : ℂ) = ∫ x, cdot b (perpGradCoord φ) x := by
  have hq1 := (hwq 1).1 φ hφ
  have hη0 := (hwη 0).1 φ hφ
  have hfun : (fun x => profCurl bq bη x * (φ x : ℂ)) =
      fun x => bq x 1 * (φ x : ℂ) - bη x 0 * (φ x : ℂ) := by
    funext x; unfold profCurl; ring
  refine ⟨hfun ▸ hq1.2.sub hη0.2, ?_⟩
  rw [hfun, integral_sub hq1.2 hη0.2, (hwq 1).2 φ hφ, (hwη 0).2 φ hφ, ← integral_sub hq1.1 hη0.1]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only [Pi.sub_apply]
  rw [coordTranspose_vQ0_dZero, coordTranspose_vEta_dZero]
  simp only [cdot, perpGradCoord, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.ofReal_neg]
  ring

/-! ### 2. Fundamental lemma on `{s > 0}` and slice curl identification -/

private def mkPosBump (x : Coord) (hx : 0 < x.1) : ContDiffBump x where
  rIn := x.1 / 4
  rOut := x.1 / 2
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

private theorem isCoordTest_mkPosBump (x : Coord) (hx : 0 < x.1) :
    IsCoordTest ((mkPosBump x hx : ContDiffBump x) : Coord → ℝ) := by
  refine ⟨(mkPosBump x hx).contDiff, (mkPosBump x hx).hasCompactSupport, ?_⟩
  rw [(mkPosBump x hx).tsupport_eq]
  intro y hy
  have hy' : dist y x ≤ x.1 / 2 := by simpa [mkPosBump] using hy
  have h1 : dist y.1 x.1 ≤ dist y x := by
    rw [Prod.dist_eq]
    exact le_max_left _ _
  rw [Real.dist_eq] at h1
  have hd : |y.1 - x.1| ≤ x.1 / 2 := h1.trans hy'
  refine ⟨?_, trivial⟩
  show 0 < y.1
  linarith [(abs_le.mp hd).1]

private theorem ae_pos_eq_zero_of_coordTests {W : Coord → ℂ}
    (hInt : ∀ φ : Coord → ℝ, IsCoordTest φ → Integrable (fun x => W x * (φ x : ℂ)))
    (hZero : ∀ φ : Coord → ℝ, IsCoordTest φ → ∫ x, W x * (φ x : ℂ) = 0) :
    ∀ᵐ x : Coord, 0 < x.1 → W x = 0 := by
  have : Measure.IsAddHaarMeasure (volume : Measure Coord) := Measure.prod.instIsAddHaarMeasure _ _
  let Upos : Set Coord := Ioi (0 : ℝ) ×ˢ univ
  have hloc : LocallyIntegrableOn W Upos volume := by
    intro x hx
    have hx' : 0 < x.1 := hx.1
    let χ := mkPosBump x hx'
    have hT := isCoordTest_mkPosBump x hx'
    have hint := (hInt χ hT).integrableOn (s := Metric.closedBall x χ.rIn)
    refine ⟨Metric.closedBall x χ.rIn,
      mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds x χ.rIn_pos), ?_⟩
    refine hint.congr_fun (fun y hy => ?_) measurableSet_closedBall
    have h1 : (χ : Coord → ℝ) y = 1 := χ.one_of_mem_closedBall hy
    simp [h1]
  have hae := (isOpen_Ioi.prod isOpen_univ).ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc (by
    intro χ hχs hχc hχU
    have hχ := hZero χ ⟨hχs, hχc, hχU⟩
    simp only [Complex.real_smul]
    convert hχ using 2
    funext x
    ring)
  filter_upwards [hae] with x hx hpos
  exact hx ⟨hpos, trivial⟩

private theorem ae_slice_curl_eq_neg {ν c : ℝ} {tr : B0140.TrainSol ν c}
    {b0' b0q b0η g₀ gq₀ gη₀ Uq Uη : CProf}
    (hg₀_src : IsBodySource tr b0' b0q b0η g₀)
    (hgwq₀ : HasWeakVec vQ0 dZero g₀ gq₀) (hgwη₀ : HasWeakVec vEta dZero g₀ gη₀)
    (hwU_q : HasWeakVec vQ0 dZero (flatBv tr b0' b0q b0η) Uq)
    (hwU_η : HasWeakVec vEta dZero (flatBv tr b0' b0q b0η) Uη) :
    ∀ᵐ s ∂volume, 0 < s →
      ∀ᵐ z ∂(volume.restrict (B0579.cell c)),
        profCurl gq₀ gη₀ (s, z) = -profCurl Uq Uη (s, z) := by
  have hae_coord : ∀ᵐ x : Coord, 0 < x.1 →
      profCurl gq₀ gη₀ x + profCurl Uq Uη x = 0 := by
    refine ae_pos_eq_zero_of_coordTests (fun φ hφ => ?_) (fun φ hφ => ?_)
    · have h1 := (integral_profCurl_mul_test hgwq₀ hgwη₀ hφ).1
      have h2 := (integral_profCurl_mul_test hwU_q hwU_η hφ).1
      exact (h1.add h2).congr (Eventually.of_forall fun x => by simp only [Pi.add_apply]; ring)
    · obtain ⟨hI_g, hEq_g⟩ := integral_profCurl_mul_test hgwq₀ hgwη₀ hφ
      obtain ⟨hI_U, hEq_U⟩ := integral_profCurl_mul_test hwU_q hwU_η hφ
      have hsrc := (hg₀_src.equation (perpGradCoord φ) (isPlanarSolTest_perpGradCoord hφ)).2.2
      have hadd : (fun x => (profCurl gq₀ gη₀ x + profCurl Uq Uη x) * (φ x : ℂ)) =
          fun x => profCurl gq₀ gη₀ x * (φ x : ℂ) + profCurl Uq Uη x * (φ x : ℂ) := by
        funext x; ring
      rw [hadd, integral_add hI_g hI_U, hEq_g, hEq_U, hsrc, neg_add_cancel]
  have hprod : ∀ᵐ s ∂(volume : Measure ℝ), ∀ᵐ z ∂(volume : Measure B0579.Plane),
      0 < (s, z).1 → profCurl gq₀ gη₀ (s, z) = -profCurl Uq Uη (s, z) :=
    Measure.ae_ae_of_ae_prod (hae_coord.mono fun x hx hpos => eq_neg_of_add_eq_zero_left (hx hpos))
  filter_upwards [hprod] with s hs hpos
  exact ae_restrict_of_ae (hs.mono fun _ hz => hz hpos)

/-! ### 3. Main theorem `p0SliceLiftH1Loc_proof` -/

/-- **Target of `PartII-b:F5/2/2/3`**: jointly measurable slice cylinder Leray projection of
`-flatBv` in `H¹(C_c)` with curl preservation and null-slice dichotomy. -/
theorem p0SliceLiftH1Loc_proof : UnforcedLeray.Short.IIb.P0SliceLiftH1Needed.P0SliceLiftH1Loc := by
  intro m _hm ν c tr hc b0 b0' b0q b0η D2 _hb0 _hae0 hb0'_hr hbq_hr hbη_hr hD2_hr
    hsm0 hsmq hsmη hsmD2 _hwq _hwη _hw00 _hw01 _hw10 _hw11 U Uq Uη hwU_q hwU_η hLoc _hgood_ae
  obtain ⟨g₀, gq₀, gη₀, hg₀_sm, hgq₀_sm, hgη₀_sm, hg₀_per, hgwq₀, hgwη₀, hg₀_src, hH1_le₀⟩ :=
    TailSliceP0LiftAux.p0SliceLiftH1_of_loc tr hc b0' b0q b0η D2
      hb0'_hr hbq_hr hbη_hr hD2_hr hsm0 hsmq hsmη hsmD2 hwU_q hwU_η hLoc
  have hcurl_ae₀ := ae_slice_curl_eq_neg (c := c) hg₀_src hgwq₀ hgwη₀ hwU_q hwU_η
  let Bad : Set ℝ := {s : ℝ | 0 < s ∧ ¬ (∀ᵐ z ∂(volume.restrict (B0579.cell c)),
      profCurl gq₀ gη₀ (s, z) = -profCurl Uq Uη (s, z))}
  have hBad_null : volume Bad = 0 := by
    rw [← compl_mem_ae_iff]
    filter_upwards [hcurl_ae₀] with s hs hBad
    exact hBad.2 (hs hBad.1)
  let N_meas : Set ℝ := toMeasurable volume Bad
  have hN_meas : MeasurableSet N_meas := measurableSet_toMeasurable volume Bad
  have hBad_sub : Bad ⊆ N_meas := subset_toMeasurable volume Bad
  have hN_null : volume N_meas = 0 := by rw [measure_toMeasurable]; exact hBad_null
  let S_good : Set Coord := (N_meas ×ˢ (univ : Set B0579.Plane))ᶜ
  have hS_good_meas : MeasurableSet S_good := (hN_meas.prod MeasurableSet.univ).compl
  have hProd_null : (volume : Measure Coord) (N_meas ×ˢ (univ : Set B0579.Plane)) = 0 := by
    change (volume.prod volume) (N_meas ×ˢ (univ : Set B0579.Plane)) = 0
    rw [Measure.prod_prod, hN_null, zero_mul]
  have hae_good_coord : ∀ᵐ x : Coord, x ∈ S_good := compl_mem_ae_iff.2 hProd_null
  let gq : CProf := S_good.indicator gq₀
  let gη : CProf := S_good.indicator gη₀
  have hgq_sm : StronglyMeasurable gq := hgq₀_sm.indicator hS_good_meas
  have hgη_sm : StronglyMeasurable gη := hgη₀_sm.indicator hS_good_meas
  have hgwq : HasWeakVec vQ0 dZero g₀ gq := fun i =>
    FlatBvWL.hasWeakFO_congr_ae (hgwq₀ i) (Eventually.of_forall fun _ _ => rfl)
      (hae_good_coord.mono fun x hx _ =>
        congrArg (fun v : CMerid => v i) (Set.indicator_of_mem hx gq₀))
  have hgwη : HasWeakVec vEta dZero g₀ gη := fun i =>
    FlatBvWL.hasWeakFO_congr_ae (hgwη₀ i) (Eventually.of_forall fun _ _ => rfl)
      (hae_good_coord.mono fun x hx _ =>
        congrArg (fun v : CMerid => v i) (Set.indicator_of_mem hx gη₀))
  have hnotMem_S : ∀ {s : ℝ}, s ∈ N_meas → ∀ z : B0579.Plane, ((s, z) : Coord) ∉ S_good :=
    fun hsN _ h => h ⟨hsN, trivial⟩
  have hmem_S : ∀ {s : ℝ}, s ∉ N_meas → ∀ z : B0579.Plane, ((s, z) : Coord) ∈ S_good :=
    fun hsN _ h => hsN h.1
  have hH1_le : ∀ s : ℝ, 0 < s →
      sliceH1Norm c g₀ gq gη s ≤ ENNReal.ofReal 2 * sliceH1Norm c U Uq Uη s := by
    intro s hs
    refine (?_ : sliceH1Norm c g₀ gq gη s ≤ sliceH1Norm c g₀ gq₀ gη₀ s).trans (hH1_le₀ s hs)
    by_cases hsN : s ∈ N_meas
    · have eq0_q : (fun z : B0579.Plane => gq (s, z)) = 0 :=
        funext fun z => Set.indicator_of_notMem (hnotMem_S hsN z) gq₀
      have eq0_η : (fun z : B0579.Plane => gη (s, z)) = 0 :=
        funext fun z => Set.indicator_of_notMem (hnotMem_S hsN z) gη₀
      unfold sliceH1Norm
      rw [eq0_q, eq0_η, eLpNorm_zero, add_zero, add_zero]
      exact le_self_add.trans le_self_add
    · have eq_q : (fun z : B0579.Plane => gq (s, z)) = fun z => gq₀ (s, z) :=
        funext fun z => Set.indicator_of_mem (hmem_S hsN z) gq₀
      have eq_η : (fun z : B0579.Plane => gη (s, z)) = fun z => gη₀ (s, z) :=
        funext fun z => Set.indicator_of_mem (hmem_S hsN z) gη₀
      unfold sliceH1Norm
      rw [eq_q, eq_η]
  have hcurl_good : ∀ {s : ℝ}, 0 < s → s ∉ N_meas →
      ∀ᵐ z ∂(volume.restrict (B0579.cell c)),
        profCurl gq gη (s, z) = -profCurl Uq Uη (s, z) := by
    intro s hs hsN
    have hsBad : s ∉ Bad := fun h => hsN (hBad_sub h)
    have hae0 : ∀ᵐ z ∂(volume.restrict (B0579.cell c)),
        profCurl gq₀ gη₀ (s, z) = -profCurl Uq Uη (s, z) :=
      not_not.1 fun hnot => hsBad ⟨hs, hnot⟩
    refine hae0.mono fun z hz => ?_
    have hq_eq : gq (s, z) = gq₀ (s, z) := Set.indicator_of_mem (hmem_S hsN z) gq₀
    have hη_eq : gη (s, z) = gη₀ (s, z) := Set.indicator_of_mem (hmem_S hsN z) gη₀
    unfold profCurl at hz ⊢
    rw [hq_eq, hη_eq]
    exact hz
  refine ⟨g₀, gq, gη, hg₀_sm, hgq_sm, hgη_sm, hg₀_per, hgwq, hgwη, hg₀_src, hH1_le, ?_, ?_⟩
  · intro s hs
    by_cases hsN : s ∈ N_meas
    · exact Or.inl fun z =>
        ⟨Set.indicator_of_notMem (hnotMem_S hsN z) gq₀,
          Set.indicator_of_notMem (hnotMem_S hsN z) gη₀⟩
    · exact Or.inr (hcurl_good hs hsN)
  · filter_upwards [compl_mem_ae_iff.2 hN_null] with s hsN hs
    exact hcurl_good hs hsN

end UnforcedLeray.Short.IIb

end
