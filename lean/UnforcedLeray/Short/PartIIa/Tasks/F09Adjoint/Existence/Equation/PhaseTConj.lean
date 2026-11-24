import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F09_1_3_1_3

/-!
# Part II-a, task `PartII-a:F09/1/3/1/3/1`: `PhaseTConj`

Source `the November 2 reference manuscript` lines 1403-1413, 1426-1428.
`S_ν(s)` is real, so it commutes with complex conjugation, and so does `𝒯(s) = phaseT`.

Proof outline.
1. `freeC_conj`: for `F` in `L^p` and `G` in `L^q` with `F = conj G` a.e., `S_ν(s) F = conj (S_ν(s) G)`
   a.e. The real and imaginary parts of `F` and `G` are `Re G`, `-Im G`, and `S_ν(s)` is linear and
   respects a.e. equality (`freeEvolution_congr_ae`, `freeEvolution_smul`).
2. `hkey`: slices of `conjF Φ` are pointwise conjugates of slices of `Φ`, using `MemLp.coeFn_toLp`.
3. `hK`: on the phase circle, `testElem (conjF Φ)` is a.e. the conjugate of `testElem Φ`.
4. Shift by `s` (measure-preserving) and `coeFn_phaseT` for both exponents, then `freeC_conj`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

namespace PhaseTConjAux

/-- `reV` of a componentwise conjugate is `reV`. -/
theorem reV_conj_vec (z : CVec3) :
    reV (WithLp.toLp 2 fun k => star (z k) : CVec3) = reV z := by
  ext i
  simp [reV_apply]

/-- `imV` of a componentwise conjugate is `-imV`. -/
theorem imV_conj_vec (z : CVec3) :
    imV (WithLp.toLp 2 fun k => star (z k) : CVec3) = -imV z := by
  ext i
  simp [imV_apply]

/-- Pointwise: the conjugate of `ofReV a + ofImV b` is `ofReV a + ofImV (-b)`. -/
theorem conj_pt (a b : Space) :
    ofReV a + ofImV (-b) =
      (WithLp.toLp 2 fun k => star ((ofReV a + ofImV b : CVec3) k) : CVec3) := by
  ext k
  simp [ofReV_apply, ofImV_apply]

/-- **`S_ν(s)` commutes with conjugation a.e.**: if `F = conj G` a.e., then
`S_ν(s) F = conj (S_ν(s) G)` a.e. -/
theorem freeC_conj {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (ν s : ℝ) (F : Lp CVec3 p (volume : Measure Space))
    (G : Lp CVec3 q (volume : Measure Space))
    (h : ⇑F =ᵐ[volume] fun y => (WithLp.toLp 2 fun k => star (G y k) : CVec3)) :
    ⇑(UnforcedLeray.B0421.freeC hp ν s F) =ᵐ[volume] fun y =>
      (WithLp.toLp 2 fun k =>
        star ((UnforcedLeray.B0421.freeC hq ν s G : Space → CVec3) y k) : CVec3) := by
  have hRe : (reV.compLpL p volume F : SpatialField) =ᵐ[volume]
      (reV.compLpL q volume G : SpatialField) := by
    filter_upwards [reV.coeFn_compLpL (μ := volume) (p := p) F,
      reV.coeFn_compLpL (μ := volume) (p := q) G, h] with y h1 h2 h3
    simp only [h1, h2, h3, reV_conj_vec]
  have hIm : (imV.compLpL p volume F : SpatialField) =ᵐ[volume]
      fun y => -((imV.compLpL q volume G : SpatialField) y) := by
    filter_upwards [imV.coeFn_compLpL (μ := volume) (p := p) F,
      imV.coeFn_compLpL (μ := volume) (p := q) G, h] with y h1 h2 h3
    simp only [h1, h2, h3, imV_conj_vec]
  have hRe' : UnforcedLeray.AncientLocalization.freeEvolution ν s
      (reV.compLpL p volume F : SpatialField) =ᵐ[volume]
      UnforcedLeray.AncientLocalization.freeEvolution ν s
        (reV.compLpL q volume G : SpatialField) :=
    UnforcedLeray.B0418.freeEvolution_congr_ae hRe ν s
  have hIm' : UnforcedLeray.AncientLocalization.freeEvolution ν s
      (imV.compLpL p volume F : SpatialField) =ᵐ[volume] fun y =>
        -(UnforcedLeray.AncientLocalization.freeEvolution ν s
          (imV.compLpL q volume G : SpatialField) y) := by
    have h1 := UnforcedLeray.B0418.freeEvolution_congr_ae hIm ν s
    have h2 : (fun y => -((imV.compLpL q volume G : SpatialField) y)) =
        (-1 : ℝ) • (imV.compLpL q volume G : SpatialField) := by
      funext y
      simp
    rw [h2, UnforcedLeray.B0418.freeEvolution_smul] at h1
    filter_upwards [h1] with y hy
    rw [hy]
    simp
  filter_upwards [UnforcedLeray.B0421.coeFn_freeC hp ν s F,
    UnforcedLeray.B0421.coeFn_freeC hq ν s G, hRe', hIm'] with y h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  exact conj_pt _ _

end PhaseTConjAux

set_option maxHeartbeats 1600000 in
open PhaseTConjAux in
/-- **Task `PartII-a:F09/1/3/1/3/1`**: `𝒯(s)` commutes with conjugation on phase tests. -/
theorem phaseTConj : PhaseTConj := by
  intro P _ ν s Φ hΦ
  have hΨ : IsPhaseTest P (conjF Φ) := conjF_isPhaseTest hΦ
  have hq2 : conjExp 2 ≠ ⊤ := conjExp_ne_top (by norm_num)
  have hs2 : IsSliceTest P 2 (conjF Φ) := hΨ.isSliceTest 2
  have hsΦ : IsSliceTest P (conjExp 2) Φ := hΦ.isSliceTest (conjExp 2)
  -- the slices of `conj Φ` are pointwise conjugates of the slices of `Φ`
  have hkey : ∀ τ : AddCircle P,
      ⇑(circleSlice hs2 τ) =ᵐ[volume] fun y =>
        (WithLp.toLp 2 fun k => star ((circleSlice hsΦ τ) y k) : CVec3) := by
    intro τ
    induction τ using QuotientAddGroup.induction_on with
    | H t =>
      simp only [circleSlice_coe, sliceMap]
      filter_upwards [MemLp.coeFn_toLp (hs2.2.memLp t), MemLp.coeFn_toLp (hsΦ.2.memLp t)]
        with y h1 h2
      rw [h1, h2]
      rfl
  -- `Y_2`-elements agree haar-a.e. with their continuous slice maps
  have hae1 : ⇑(testElem P 2 (conjF Φ)) =ᵐ[AddCircle.haarAddCircle (T := P)]
      ⇑(circleSlice hs2) := by
    rw [testElem_of hs2]
    exact ContinuousMap.coeFn_toLp (E := Lp CVec3 2 (volume : Measure Space)) (p := 2)
      (𝕜 := ℂ) AddCircle.haarAddCircle (circleSlice hs2)
  have hae2 : ⇑(testElem P (conjExp 2) Φ) =ᵐ[AddCircle.haarAddCircle (T := P)]
      ⇑(circleSlice hsΦ) := by
    rw [testElem_of hsΦ]
    exact ContinuousMap.coeFn_toLp (E := Lp CVec3 (conjExp 2) (volume : Measure Space))
      (p := conjExp 2) (𝕜 := ℂ) AddCircle.haarAddCircle (circleSlice hsΦ)
  have hK : ∀ᵐ τ ∂(AddCircle.haarAddCircle : Measure (AddCircle P)),
      ⇑((testElem P 2 (conjF Φ)) τ) =ᵐ[volume] fun y =>
        (WithLp.toLp 2 fun k => star (((testElem P (conjExp 2) Φ) τ) y k) : CVec3) := by
    filter_upwards [hae1, hae2] with τ h1 h2
    rw [h1, h2]
    exact hkey τ
  have hKs : ∀ᵐ τ ∂(AddCircle.haarAddCircle : Measure (AddCircle P)),
      ⇑((testElem P 2 (conjF Φ)) (τ - (s : AddCircle P))) =ᵐ[volume] fun y =>
        (WithLp.toLp 2 fun k =>
          star (((testElem P (conjExp 2) Φ) (τ - (s : AddCircle P))) y k) : CVec3) := by
    have hqm : Measure.QuasiMeasurePreserving (fun τ : AddCircle P => τ - (s : AddCircle P))
        (AddCircle.haarAddCircle : Measure (AddCircle P))
        (AddCircle.haarAddCircle : Measure (AddCircle P)) :=
      (measurePreserving_sub_right (AddCircle.haarAddCircle : Measure (AddCircle P))
        (s : AddCircle P)).quasiMeasurePreserving
    exact hqm.ae (p := fun τ : AddCircle P =>
      ⇑((testElem P 2 (conjF Φ)) τ) =ᵐ[volume] fun y =>
        (WithLp.toLp 2 fun k => star (((testElem P (conjExp 2) Φ) τ) y k) : CVec3)) hK
  filter_upwards [hKs,
    UnforcedLeray.B0421.coeFn_phaseT (P := P) (q := 2) ENNReal.ofNat_ne_top ν s
      (testElem P 2 (conjF Φ)),
    UnforcedLeray.B0421.coeFn_phaseT (P := P) (q := conjExp 2) hq2 ν s
      (testElem P (conjExp 2) Φ)] with τ hτ hτ1 hτ2
  rw [hτ1, hτ2]
  exact freeC_conj ENNReal.ofNat_ne_top hq2 ν s _ _ hτ

end UnforcedLeray.Short.PartIIa
