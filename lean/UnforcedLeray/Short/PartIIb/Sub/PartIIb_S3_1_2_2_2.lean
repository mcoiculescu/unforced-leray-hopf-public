import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S3_1_2_2
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S3_1_1_2
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S3_1_2_1

/-!
# `PartII-b:S3/1/2/2/2` decomposition (`Sub/PartII-b_S3_1_2_2_2.lean`, SP 2519-2523, 2559-2562)

Source of record: `the November 2 reference manuscript`
(SP), lines 2519-2523 and 2559-2562:
"The projected equation is $A_0 U + \mathbb{P}(U \cdot \nabla U) = 0$ with zero residual. ...
On positive physical-time compact intervals the resulting $C_\tau W^{k,4}$ regularity and the
projected equation give all time derivatives, so $U$ is jointly smooth through the axis."

## Proved here (zero `sorry`)

1. **Exact commutators of `spatialRadialDrift` with `spatialPartial`, `spatialLaplacian`,
   `spatialDiffReact`, and `spatialConvect`**:
   - `spatialPartial_spatialRadialDrift` and `spatialRadialDrift_spatialPartial`:
     `spatialRadialDrift (spatialPartial i F) = spatialPartial i (spatialRadialDrift F) - spatialPartial i F`;
   - `spatialLaplacian_spatialRadialDrift` and `spatialRadialDrift_spatialLaplacian`:
     `spatialRadialDrift (spatialLaplacian F) = spatialLaplacian (spatialRadialDrift F) - (2 : ℝ) • spatialLaplacian F`;
   - `spatialRadialDrift_spatialDiffReact`:
     `spatialRadialDrift (spatialDiffReact ν F) = spatialDiffReact ν (spatialRadialDrift F) - (2 * ν) • spatialLaplacian F`;
   - `spatialRadialDrift_spatialConvect`:
     `spatialRadialDrift (spatialConvect V W) = spatialConvect (spatialRadialDrift V) W + spatialConvect V (spatialRadialDrift W) - spatialConvect V W`.
2. **Iterated radial drift `spatialRadialDrift^[r]` and `IsIteratedRadialDriftSliceFamily`**:
   - Linearity (`iterate_spatialRadialDrift_zero`, `iterate_spatialRadialDrift_add`,
     `iterate_spatialRadialDrift_smul`, `iterate_spatialRadialDrift_sub`,
     `iterate_spatialRadialDrift_sum`), slice smoothness
     (`contDiff_infty_iterate_spatialRadialDrift`), and Morrey `L⁴` upgrade
     (`sliceFamily_iterate_spatialRadialDrift_of_l4`,
     `isIteratedRadialDriftSliceFamily_of_succ_succ_l4`);
   - Closure of `IsIteratedRadialDriftSliceFamily` under `0`, `+`, `-`, `•`, `Finset.sum`,
     `spatialRadialDrift`, `spatialLaplacian`, `spatialDiffReact`, `spatialProjectedLin`,
     `spatialConvect`, `smoothLeraySlice` (given `SmoothLerayRadialDriftComm`),
     `smoothConvectiveLeray`, and `leibnizBilinearSum`.
3. **All-order induction along `bgPhaseDerivTower`**:
   - `iteratedRadialDrift_bgPhaseDerivTower` and
     `sliceFamily_spatialRadialDrift_bgPhaseDerivTower`: if `U₀` satisfies
     `IsIteratedRadialDriftSliceFamily U₀` and `SmoothLerayRadialDriftComm` holds, then every stage
     `bgPhaseDerivTower ν U₀ m` satisfies `IsIteratedRadialDriftSliceFamily`, and in particular
     `fun τ => spatialRadialDrift (bgPhaseDerivTower ν U₀ m τ)` lies in
     `IsUniformSmoothL4SliceFamily` for every `m : ℕ`;
   - `bgHigherOrderRadialDriftSlice_of` (and alias `bgHigherOrderRadialDriftSlice_of_parts`):
     conditional assembly of `BgHigherOrderRadialDriftSlice` (`PartII-b:S3/1/2/2/2`) from
     `SmoothLerayRadialDriftComm` (`PartII-b:S3/1/2/2/2/1`) and
     `BgBaseIteratedRadialDriftSlice` (`PartII-b:S3/1/2/2/2/2`).
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff BigOperators

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412 UnforcedLeray.Blueprint

namespace RadialDriftTowerSub

/-! ## 1. Smoothness helpers and commutators of `spatialRadialDrift` -/

theorem contDiff_infty_spatialPartial {F : SpatialField} (hF : ContDiff ℝ ∞ F) (i : Fin 3) :
    ContDiff ℝ ∞ (spatialPartial i F) :=
  JointSmoothSub.contDiff_infty_dirSpatialJet hF [EuclideanSpace.single i 1]

theorem contDiff_infty_spatialLaplacian {F : SpatialField} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (spatialLaplacian F) :=
  ContDiff.sum fun i _ =>
    JointSmoothSub.contDiff_infty_dirSpatialJet hF
      [EuclideanSpace.single i 1, EuclideanSpace.single i 1]

/-- Commutator of `spatialPartial i` and `spatialRadialDrift`:
`spatialPartial i (spatialRadialDrift F) = spatialRadialDrift (spatialPartial i F) + spatialPartial i F`. -/
theorem spatialPartial_spatialRadialDrift {F : SpatialField}
    (hF : ContDiff ℝ ∞ F) (i : Fin 3) :
    spatialPartial i (spatialRadialDrift F) =
      spatialRadialDrift (spatialPartial i F) + spatialPartial i F :=
  PhaseDerivStepSub.dirSpatialJet_spatialRadialDrift_singleton hF (EuclideanSpace.single i 1)

/-- Reordered commutator of `spatialRadialDrift` and `spatialPartial i`:
`spatialRadialDrift (spatialPartial i F) = spatialPartial i (spatialRadialDrift F) - spatialPartial i F`. -/
theorem spatialRadialDrift_spatialPartial {F : SpatialField}
    (hF : ContDiff ℝ ∞ F) (i : Fin 3) :
    spatialRadialDrift (spatialPartial i F) =
      spatialPartial i (spatialRadialDrift F) - spatialPartial i F :=
  eq_sub_of_add_eq (spatialPartial_spatialRadialDrift hF i).symm

/-- Commutator of `spatialLaplacian` and `spatialRadialDrift`:
`spatialLaplacian (spatialRadialDrift F) = spatialRadialDrift (spatialLaplacian F) + (2 : ℝ) • spatialLaplacian F`. -/
theorem spatialLaplacian_spatialRadialDrift {F : SpatialField}
    (hF : ContDiff ℝ ∞ F) :
    spatialLaplacian (spatialRadialDrift F) =
      spatialRadialDrift (spatialLaplacian F) + (2 : ℝ) • spatialLaplacian F := by
  have hjet (i : Fin 3) :
      dirSpatialJet (spatialRadialDrift F)
          [EuclideanSpace.single i 1, EuclideanSpace.single i 1] =
        spatialRadialDrift (dirSpatialJet F
          [EuclideanSpace.single i 1, EuclideanSpace.single i 1]) +
          (2 : ℝ) • dirSpatialJet F
            [EuclideanSpace.single i 1, EuclideanSpace.single i 1] := by
    simpa using
      PhaseDerivStepSub.dirSpatialJet_spatialRadialDrift hF
        [EuclideanSpace.single i 1, EuclideanSpace.single i 1]
  have hrad_sum :
      spatialRadialDrift (spatialLaplacian F) =
        fun y => ∑ i : Fin 3,
          spatialRadialDrift (dirSpatialJet F
            [EuclideanSpace.single i 1, EuclideanSpace.single i 1]) y :=
    ProjectedEvolutionSub.spatialRadialDrift_sum (Finset.univ : Finset (Fin 3))
      (F := fun i => dirSpatialJet F [EuclideanSpace.single i 1, EuclideanSpace.single i 1])
      (fun i _ => JointSmoothSub.contDiff_infty_dirSpatialJet hF
        [EuclideanSpace.single i 1, EuclideanSpace.single i 1])
  funext y
  change ∑ i : Fin 3,
      dirSpatialJet (spatialRadialDrift F)
        [EuclideanSpace.single i 1, EuclideanSpace.single i 1] y =
    spatialRadialDrift (spatialLaplacian F) y + (2 : ℝ) • (∑ i : Fin 3,
      dirSpatialJet F [EuclideanSpace.single i 1, EuclideanSpace.single i 1] y)
  rw [hrad_sum]
  simp only [hjet, Pi.add_apply, Pi.smul_apply, Finset.sum_add_distrib, ← Finset.smul_sum]

/-- Reordered commutator of `spatialRadialDrift` and `spatialLaplacian`:
`spatialRadialDrift (spatialLaplacian F) = spatialLaplacian (spatialRadialDrift F) - (2 : ℝ) • spatialLaplacian F`. -/
theorem spatialRadialDrift_spatialLaplacian {F : SpatialField}
    (hF : ContDiff ℝ ∞ F) :
    spatialRadialDrift (spatialLaplacian F) =
      spatialLaplacian (spatialRadialDrift F) - (2 : ℝ) • spatialLaplacian F :=
  eq_sub_of_add_eq (spatialLaplacian_spatialRadialDrift hF).symm

/-- Commutator of `spatialRadialDrift` and `spatialDiffReact ν`:
`spatialRadialDrift (spatialDiffReact ν F) = spatialDiffReact ν (spatialRadialDrift F) - (2 * ν) • spatialLaplacian F`. -/
theorem spatialRadialDrift_spatialDiffReact (ν : ℝ) {F : SpatialField}
    (hF : ContDiff ℝ ∞ F) :
    spatialRadialDrift (spatialDiffReact ν F) =
      spatialDiffReact ν (spatialRadialDrift F) - (2 * ν) • spatialLaplacian F := by
  have hLap : ContDiff ℝ ∞ (spatialLaplacian F) := contDiff_infty_spatialLaplacian hF
  have hνLap : ContDiff ℝ ∞ (ν • spatialLaplacian F) := hLap.const_smul ν
  have hHalfF : ContDiff ℝ ∞ ((1 / 2 : ℝ) • F) := hF.const_smul (1 / 2 : ℝ)
  unfold spatialDiffReact
  rw [ProjectedEvolutionSub.spatialRadialDrift_add hνLap hHalfF,
    ProjectedEvolutionSub.spatialRadialDrift_smul ν hLap,
    ProjectedEvolutionSub.spatialRadialDrift_smul (1 / 2 : ℝ) hF,
    spatialRadialDrift_spatialLaplacian hF]
  funext y
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_sub, smul_smul, mul_comm (2 : ℝ) ν]
  abel

/-- Commutator / Leibniz identity for `spatialRadialDrift` on `spatialConvect V W`:
`spatialRadialDrift (spatialConvect V W) = spatialConvect (spatialRadialDrift V) W + spatialConvect V (spatialRadialDrift W) - spatialConvect V W`. -/
theorem spatialRadialDrift_spatialConvect {V W : SpatialField}
    (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W) :
    spatialRadialDrift (spatialConvect V W) =
      spatialConvect (spatialRadialDrift V) W +
        spatialConvect V (spatialRadialDrift W) -
        spatialConvect V W := by
  funext y
  have hdV : HasFDerivAt V (fderiv ℝ V y) y :=
    ((hV.differentiable (by simp)) y).hasFDerivAt
  have hdW : Differentiable ℝ (fderiv ℝ W) :=
    (hW.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have hconv : HasFDerivAt (spatialConvect V W)
      ((fderiv ℝ W y).comp (fderiv ℝ V y) + (fderiv ℝ (fderiv ℝ W) y).flip (V y)) y :=
    (hdW y).hasFDerivAt.clm_apply hdV
  have h1 : spatialRadialDrift (spatialConvect V W) y =
      fderiv ℝ W y (fderiv ℝ V y y) + fderiv ℝ (fderiv ℝ W) y y (V y) := by
    change fderiv ℝ (spatialConvect V W) y y = _
    rw [hconv.fderiv]
    rfl
  have hradW : HasFDerivAt (spatialRadialDrift W)
      ((fderiv ℝ W y).comp (ContinuousLinearMap.id ℝ Space) +
        (fderiv ℝ (fderiv ℝ W) y).flip y) y :=
    (hdW y).hasFDerivAt.clm_apply (hasFDerivAt_id y)
  have h2 : spatialConvect V (spatialRadialDrift W) y =
      fderiv ℝ W y (V y) + fderiv ℝ (fderiv ℝ W) y (V y) y := by
    change fderiv ℝ (spatialRadialDrift W) y (V y) = _
    rw [hradW.fderiv]
    rfl
  have hsymm : fderiv ℝ (fderiv ℝ W) y (V y) y = fderiv ℝ (fderiv ℝ W) y y (V y) :=
    (hW.contDiffAt.isSymmSndFDerivAt (n := ∞) (by simp)).eq (V y) y
  change spatialRadialDrift (spatialConvect V W) y =
    spatialConvect (spatialRadialDrift V) W y +
      spatialConvect V (spatialRadialDrift W) y -
      spatialConvect V W y
  rw [h1, h2, hsymm]
  change fderiv ℝ W y (fderiv ℝ V y y) + fderiv ℝ (fderiv ℝ W) y y (V y) =
    fderiv ℝ W y (fderiv ℝ V y y) +
      (fderiv ℝ W y (V y) + fderiv ℝ (fderiv ℝ W) y y (V y)) -
      fderiv ℝ W y (V y)
  abel

/-! ## 2. Iterated radial drift `spatialRadialDrift^[r]` and linearity -/

/-- `r`-fold iterated radial drift preserves `ContDiff ℝ ∞`. -/
theorem contDiff_infty_iterate_spatialRadialDrift (r : ℕ) {F : SpatialField}
    (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ ((spatialRadialDrift^[r]) F) := by
  induction r generalizing F with
  | zero => exact hF
  | succ r ih =>
      rw [Function.iterate_succ_apply]
      exact ih (HigherPhaseSub.contDiff_infty_spatialRadialDrift hF)

@[simp]
theorem iterate_spatialRadialDrift_zero (r : ℕ) :
    (spatialRadialDrift^[r]) (0 : SpatialField) = 0 := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [Function.iterate_succ_apply', ih, ProjectedEvolutionSub.spatialRadialDrift_zero]

theorem iterate_spatialRadialDrift_add (r : ℕ) {F G : SpatialField}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    (spatialRadialDrift^[r]) (F + G) =
      (spatialRadialDrift^[r]) F + (spatialRadialDrift^[r]) G := by
  induction r generalizing F G with
  | zero => rfl
  | succ r ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
        ProjectedEvolutionSub.spatialRadialDrift_add hF hG,
        ih (HigherPhaseSub.contDiff_infty_spatialRadialDrift hF)
          (HigherPhaseSub.contDiff_infty_spatialRadialDrift hG)]

theorem iterate_spatialRadialDrift_smul (r : ℕ) (c : ℝ) {F : SpatialField}
    (hF : ContDiff ℝ ∞ F) :
    (spatialRadialDrift^[r]) (c • F) = c • (spatialRadialDrift^[r]) F := by
  induction r generalizing F with
  | zero => rfl
  | succ r ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        ProjectedEvolutionSub.spatialRadialDrift_smul c hF,
        ih (HigherPhaseSub.contDiff_infty_spatialRadialDrift hF)]

theorem iterate_spatialRadialDrift_neg (r : ℕ) {F : SpatialField}
    (hF : ContDiff ℝ ∞ F) :
    (spatialRadialDrift^[r]) (-F) = -(spatialRadialDrift^[r]) F := by
  have h := iterate_spatialRadialDrift_smul r (-1 : ℝ) hF
  simpa [neg_one_smul] using h

theorem iterate_spatialRadialDrift_sub (r : ℕ) {F G : SpatialField}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    (spatialRadialDrift^[r]) (F - G) =
      (spatialRadialDrift^[r]) F - (spatialRadialDrift^[r]) G := by
  have hnegG : ContDiff ℝ ∞ (-G) := hG.neg
  rw [sub_eq_add_neg, iterate_spatialRadialDrift_add r hF hnegG,
    iterate_spatialRadialDrift_neg r hG, ← sub_eq_add_neg]

theorem iterate_spatialRadialDrift_sum (r : ℕ) {ι : Type*} (s : Finset ι)
    {F : ι → SpatialField} (hF : ∀ i ∈ s, ContDiff ℝ ∞ (F i)) :
    (spatialRadialDrift^[r]) (fun y => ∑ i ∈ s, F i y) =
      fun y => ∑ i ∈ s, (spatialRadialDrift^[r]) (F i) y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have h0 : (fun y : Space => ∑ i ∈ (∅ : Finset ι), F i y) = 0 := by
        funext y
        simp
      rw [h0, iterate_spatialRadialDrift_zero]
      funext y
      simp
  | @insert a s ha ih =>
      have ha_cd : ContDiff ℝ ∞ (F a) := hF a (Finset.mem_insert_self a s)
      have hs_cd : ContDiff ℝ ∞ (fun y => ∑ i ∈ s, F i y) :=
        ContDiff.sum fun i hi => hF i (Finset.mem_insert_of_mem hi)
      have hfun : (fun y : Space => ∑ i ∈ insert a s, F i y) =
          F a + (fun y => ∑ i ∈ s, F i y) := by
        funext y
        exact Finset.sum_insert ha
      rw [hfun, iterate_spatialRadialDrift_add r ha_cd hs_cd,
        ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))]
      funext y
      exact (Finset.sum_insert (f := fun i => (spatialRadialDrift^[r]) (F i) y) ha).symm

/-- Morrey `L⁴` upgrade for the `r`-th iterated radial drift of a smooth-slice family `U₀`. -/
theorem sliceFamily_iterate_spatialRadialDrift_of_l4 (r : ℕ) {U₀ : ℝ → SpatialField}
    (hU₀ : IsUniformSmoothL4SliceFamily U₀)
    (hL4 : ∀ k : ℕ, ∃ M : ℝ, ∀ τ : ℝ,
      eLpNorm (fun y => iteratedFDeriv ℝ k ((spatialRadialDrift^[r]) (U₀ τ)) y) 4 volume ≤
        ENNReal.ofReal M) :
    IsUniformSmoothL4SliceFamily (fun τ => (spatialRadialDrift^[r]) (U₀ τ)) :=
  PhaseDerivStepSub.sliceFamily_of_contDiff_and_l4
    (fun k τ =>
      (contDiff_infty_iterate_spatialRadialDrift r
        (HigherPhaseSub.sliceFamily_contDiff_infty hU₀ τ)).of_le (by exact_mod_cast le_top))
    hL4

/-! ## 3. `IsIteratedRadialDriftSliceFamily` and closure properties -/

/-- A slice family `V : ℝ → SpatialField` whose `r`-fold iterated radial drift
`fun τ => (spatialRadialDrift^[r]) (V τ)` lies in `IsUniformSmoothL4SliceFamily` for every
`r : ℕ`. -/
def IsIteratedRadialDriftSliceFamily (V : ℝ → SpatialField) : Prop :=
  ∀ r : ℕ, IsUniformSmoothL4SliceFamily (fun τ => (spatialRadialDrift^[r]) (V τ))

theorem IsIteratedRadialDriftSliceFamily.sliceFamily {V : ℝ → SpatialField}
    (hV : IsIteratedRadialDriftSliceFamily V) :
    IsUniformSmoothL4SliceFamily V :=
  hV 0

theorem IsIteratedRadialDriftSliceFamily.spatialRadialDrift_sliceFamily {V : ℝ → SpatialField}
    (hV : IsIteratedRadialDriftSliceFamily V) :
    IsUniformSmoothL4SliceFamily (fun τ => spatialRadialDrift (V τ)) :=
  hV 1

theorem IsIteratedRadialDriftSliceFamily.contDiff_infty {V : ℝ → SpatialField}
    (hV : IsIteratedRadialDriftSliceFamily V) (τ : ℝ) :
    ContDiff ℝ ∞ (V τ) :=
  HigherPhaseSub.sliceFamily_contDiff_infty hV.sliceFamily τ

/-- Since `r = 0` is given by `hU₀` and `r = 1` is given by
`ProjectedEvolutionSub.sliceFamily_spatialRadialDrift_bgPhaseDerivTower_zero`, establishing
`IsIteratedRadialDriftSliceFamily U₀` reduces to `L⁴(ℝ³)` bounds on
`iteratedFDeriv ℝ k ((spatialRadialDrift^[r + 2]) (U₀ τ))` for `r, k : ℕ`. -/
theorem isIteratedRadialDriftSliceFamily_of_succ_succ_l4
    (hLeray : SmoothLeraySliceRegularity)
    (ν : ℝ) {U₀ U₁ : ℝ → SpatialField}
    (hU₀ : IsUniformSmoothL4SliceFamily U₀)
    (hU₁ : IsUniformSmoothL4SliceFamily U₁)
    (hEq : U₁ = bgPhaseDerivTower ν U₀ 1)
    (hL4 : ∀ (r k : ℕ), ∃ M : ℝ, ∀ τ : ℝ,
      eLpNorm (fun y => iteratedFDeriv ℝ k ((spatialRadialDrift^[r + 2]) (U₀ τ)) y) 4 volume ≤
        ENNReal.ofReal M) :
    IsIteratedRadialDriftSliceFamily U₀
  | 0 => hU₀
  | 1 => ProjectedEvolutionSub.sliceFamily_spatialRadialDrift_bgPhaseDerivTower_zero
      hLeray ν hU₀ hU₁ hEq
  | r + 2 => sliceFamily_iterate_spatialRadialDrift_of_l4 (r + 2) hU₀ (hL4 r)

theorem iteratedRadialDrift_zero :
    IsIteratedRadialDriftSliceFamily (0 : ℝ → SpatialField) := by
  intro r
  have h0 : (fun τ : ℝ => (spatialRadialDrift^[r]) ((0 : ℝ → SpatialField) τ)) = 0 := by
    funext τ
    exact iterate_spatialRadialDrift_zero r
  rw [h0]
  exact HigherPhaseSub.sliceFamily_zero

theorem iteratedRadialDrift_add {V W : ℝ → SpatialField}
    (hV : IsIteratedRadialDriftSliceFamily V) (hW : IsIteratedRadialDriftSliceFamily W) :
    IsIteratedRadialDriftSliceFamily (V + W) := by
  intro r
  have heq : (fun τ : ℝ => (spatialRadialDrift^[r]) ((V + W) τ)) =
      (fun τ => (spatialRadialDrift^[r]) (V τ)) +
        (fun τ => (spatialRadialDrift^[r]) (W τ)) := by
    funext τ
    exact iterate_spatialRadialDrift_add r (hV.contDiff_infty τ) (hW.contDiff_infty τ)
  rw [heq]
  exact HigherPhaseSub.sliceFamily_add (hV r) (hW r)

theorem iteratedRadialDrift_smul (c : ℝ) {V : ℝ → SpatialField}
    (hV : IsIteratedRadialDriftSliceFamily V) :
    IsIteratedRadialDriftSliceFamily (c • V) := by
  intro r
  have heq : (fun τ : ℝ => (spatialRadialDrift^[r]) ((c • V) τ)) =
      c • (fun τ => (spatialRadialDrift^[r]) (V τ)) := by
    funext τ
    exact iterate_spatialRadialDrift_smul r c (hV.contDiff_infty τ)
  rw [heq]
  exact HigherPhaseSub.sliceFamily_smul c (hV r)

theorem iteratedRadialDrift_sub {V W : ℝ → SpatialField}
    (hV : IsIteratedRadialDriftSliceFamily V) (hW : IsIteratedRadialDriftSliceFamily W) :
    IsIteratedRadialDriftSliceFamily (V - W) := by
  intro r
  have heq : (fun τ : ℝ => (spatialRadialDrift^[r]) ((V - W) τ)) =
      (fun τ => (spatialRadialDrift^[r]) (V τ)) -
        (fun τ => (spatialRadialDrift^[r]) (W τ)) := by
    funext τ
    exact iterate_spatialRadialDrift_sub r (hV.contDiff_infty τ) (hW.contDiff_infty τ)
  rw [heq]
  exact HigherPhaseSub.sliceFamily_sub (hV r) (hW r)

theorem iteratedRadialDrift_sum {ι : Type*} (s : Finset ι)
    {V : ι → ℝ → SpatialField}
    (hV : ∀ i ∈ s, IsIteratedRadialDriftSliceFamily (V i)) :
    IsIteratedRadialDriftSliceFamily (fun τ y => ∑ i ∈ s, V i τ y) := by
  intro r
  have heq : (fun τ : ℝ => (spatialRadialDrift^[r]) (fun y => ∑ i ∈ s, V i τ y)) =
      fun τ y => ∑ i ∈ s, (spatialRadialDrift^[r]) (V i τ) y := by
    funext τ
    exact iterate_spatialRadialDrift_sum r s (fun i hi => (hV i hi).contDiff_infty τ)
  rw [heq]
  exact HigherPhaseSub.sliceFamily_sum s (fun i hi => hV i hi r)

/-- `IsIteratedRadialDriftSliceFamily` is closed under `spatialRadialDrift`. -/
theorem iteratedRadialDrift_spatialRadialDrift {V : ℝ → SpatialField}
    (hV : IsIteratedRadialDriftSliceFamily V) :
    IsIteratedRadialDriftSliceFamily (fun τ => spatialRadialDrift (V τ)) := by
  intro r
  have heq : (fun τ : ℝ => (spatialRadialDrift^[r]) (spatialRadialDrift (V τ))) =
      fun τ => (spatialRadialDrift^[r + 1]) (V τ) := by
    funext τ
    exact (Function.iterate_succ_apply _ r (V τ)).symm
  rw [heq]
  exact hV (r + 1)

/-- `IsIteratedRadialDriftSliceFamily` is closed under `spatialLaplacian`. -/
theorem iteratedRadialDrift_spatialLaplacian {V : ℝ → SpatialField}
    (hV : IsIteratedRadialDriftSliceFamily V) :
    IsIteratedRadialDriftSliceFamily (fun τ => spatialLaplacian (V τ)) := by
  intro r
  induction r generalizing V with
  | zero =>
      exact HigherPhaseSub.sliceFamily_spatialLaplacian hV.sliceFamily
  | succ r ih =>
      have heq :
          (fun τ : ℝ => (spatialRadialDrift^[r + 1]) (spatialLaplacian (V τ))) =
            (fun τ => (spatialRadialDrift^[r]) (spatialLaplacian (spatialRadialDrift (V τ)))) -
              (2 : ℝ) • (fun τ => (spatialRadialDrift^[r]) (spatialLaplacian (V τ))) := by
        funext τ
        have hVτ : ContDiff ℝ ∞ (V τ) := hV.contDiff_infty τ
        have hLapRad : ContDiff ℝ ∞ (spatialLaplacian (spatialRadialDrift (V τ))) :=
          contDiff_infty_spatialLaplacian
            (HigherPhaseSub.contDiff_infty_spatialRadialDrift hVτ)
        have hLap : ContDiff ℝ ∞ (spatialLaplacian (V τ)) :=
          contDiff_infty_spatialLaplacian hVτ
        have h2Lap : ContDiff ℝ ∞ ((2 : ℝ) • spatialLaplacian (V τ)) :=
          hLap.const_smul (2 : ℝ)
        rw [Function.iterate_succ_apply, spatialRadialDrift_spatialLaplacian hVτ,
          iterate_spatialRadialDrift_sub r hLapRad h2Lap,
          iterate_spatialRadialDrift_smul r (2 : ℝ) hLap]
        rfl
      rw [heq]
      exact HigherPhaseSub.sliceFamily_sub
        (ih (iteratedRadialDrift_spatialRadialDrift hV))
        (HigherPhaseSub.sliceFamily_smul (2 : ℝ) (ih hV))

/-- `IsIteratedRadialDriftSliceFamily` is closed under `spatialDiffReact ν`. -/
theorem iteratedRadialDrift_spatialDiffReact (ν : ℝ) {V : ℝ → SpatialField}
    (hV : IsIteratedRadialDriftSliceFamily V) :
    IsIteratedRadialDriftSliceFamily (fun τ => spatialDiffReact ν (V τ)) :=
  iteratedRadialDrift_add
    (iteratedRadialDrift_smul ν (iteratedRadialDrift_spatialLaplacian hV))
    (iteratedRadialDrift_smul (1 / 2 : ℝ) hV)

/-- `IsIteratedRadialDriftSliceFamily` is closed under `spatialProjectedLin ν`. -/
theorem iteratedRadialDrift_spatialProjectedLin (ν : ℝ) {V : ℝ → SpatialField}
    (hV : IsIteratedRadialDriftSliceFamily V) :
    IsIteratedRadialDriftSliceFamily (fun τ => spatialProjectedLin ν (V τ)) :=
  iteratedRadialDrift_add
    (iteratedRadialDrift_smul (1 / 2 : ℝ) (iteratedRadialDrift_spatialRadialDrift hV))
    (iteratedRadialDrift_spatialDiffReact ν hV)

/-- `IsIteratedRadialDriftSliceFamily` is closed under `spatialConvect`. -/
theorem iteratedRadialDrift_spatialConvect {V W : ℝ → SpatialField}
    (hV : IsIteratedRadialDriftSliceFamily V) (hW : IsIteratedRadialDriftSliceFamily W) :
    IsIteratedRadialDriftSliceFamily (fun τ => spatialConvect (V τ) (W τ)) := by
  intro r
  induction r generalizing V W with
  | zero =>
      exact HigherPhaseSub.sliceFamily_spatialConvect hV.sliceFamily hW.sliceFamily
  | succ r ih =>
      have heq :
          (fun τ : ℝ => (spatialRadialDrift^[r + 1]) (spatialConvect (V τ) (W τ))) =
            ((fun τ => (spatialRadialDrift^[r])
                (spatialConvect (spatialRadialDrift (V τ)) (W τ))) +
              (fun τ => (spatialRadialDrift^[r])
                (spatialConvect (V τ) (spatialRadialDrift (W τ))))) -
              (fun τ => (spatialRadialDrift^[r]) (spatialConvect (V τ) (W τ))) := by
        funext τ
        have hVτ : ContDiff ℝ ∞ (V τ) := hV.contDiff_infty τ
        have hWτ : ContDiff ℝ ∞ (W τ) := hW.contDiff_infty τ
        have h1 : ContDiff ℝ ∞ (spatialConvect (spatialRadialDrift (V τ)) (W τ)) :=
          HigherPhaseSub.contDiff_infty_spatialConvect
            (HigherPhaseSub.contDiff_infty_spatialRadialDrift hVτ) hWτ
        have h2 : ContDiff ℝ ∞ (spatialConvect (V τ) (spatialRadialDrift (W τ))) :=
          HigherPhaseSub.contDiff_infty_spatialConvect hVτ
            (HigherPhaseSub.contDiff_infty_spatialRadialDrift hWτ)
        have h3 : ContDiff ℝ ∞ (spatialConvect (V τ) (W τ)) :=
          HigherPhaseSub.contDiff_infty_spatialConvect hVτ hWτ
        have h12 : ContDiff ℝ ∞
            (spatialConvect (spatialRadialDrift (V τ)) (W τ) +
              spatialConvect (V τ) (spatialRadialDrift (W τ))) :=
          h1.add h2
        rw [Function.iterate_succ_apply, spatialRadialDrift_spatialConvect hVτ hWτ,
          iterate_spatialRadialDrift_sub r h12 h3,
          iterate_spatialRadialDrift_add r h1 h2]
        rfl
      rw [heq]
      exact HigherPhaseSub.sliceFamily_sub
        (HigherPhaseSub.sliceFamily_add
          (ih (iteratedRadialDrift_spatialRadialDrift hV) hW)
          (ih hV (iteratedRadialDrift_spatialRadialDrift hW)))
        (ih hV hW)

end RadialDriftTowerSub

/-! ## 4. Atomic leaves and all-order induction along `bgPhaseDerivTower` -/

/-- **Leaf 1 (`PartII-b:S3/1/2/2/2/1`, `SmoothLerayRadialDriftComm`)**
(`the November 2 reference manuscript`,
lines 2519-2523 and 2552: "The projected equation is $A_0 U + \mathbb{P}(U \cdot \nabla U) = 0$
with zero residual. ... These estimates are uniform in phase; the bounded Cartesian Leray map
preserves them in $W^{k,p}$"): because the 3D `L⁴` Leray projection `RieszLp.lerayLp 4` commutes
with isotropic spatial dilations `y ↦ b • y` (`b > 0`, `RieszLp.lerayLp_dilate` in
`Lib/LerayC/Dilate.lean`), `smoothLeraySlice` commutes with their infinitesimal generator
`spatialRadialDrift = y · ∇` on every slice family `G` with `G` and `spatialRadialDrift G` in
`IsUniformSmoothL4SliceFamily`.
Composed by task `PartII-b:S3/1/2/2/2` via `bgHigherOrderRadialDriftSlice_of`. -/
def SmoothLerayRadialDriftComm : Prop :=
  ∀ G : ℝ → SpatialField,
    IsUniformSmoothL4SliceFamily G →
    IsUniformSmoothL4SliceFamily (fun τ => spatialRadialDrift (G τ)) →
    ∀ τ : ℝ,
      spatialRadialDrift (smoothLeraySlice G τ) =
        smoothLeraySlice (fun τ' => spatialRadialDrift (G τ')) τ

/-- **Leaf 2 (`PartII-b:S3/1/2/2/2/2`, `BgBaseIteratedRadialDriftSlice`)**
(`the November 2 reference manuscript`,
lines 2519-2523 and 2559-2562: "On positive physical-time compact intervals the resulting
$C_\tau W^{k,4}$ regularity and the projected equation give all time derivatives, so $U$ is
jointly smooth through the axis"): under `SmoothLeraySliceRegularity` and the regime and all-order
spatial regularity hypotheses of `BgHigherOrderRadialDriftSlice`, all `r`-fold iterated radial
drifts `fun τ => (spatialRadialDrift^[r]) (bgField p z τ)` (`r : ℕ`) of the base background field
`bgField p z` lie in `IsUniformSmoothL4SliceFamily` (where `r = 0` and `r = 1` are already supplied
by `isIteratedRadialDriftSliceFamily_of_succ_succ_l4`).
Composed by task `PartII-b:S3/1/2/2/2` via `bgHigherOrderRadialDriftSlice_of`. -/
def BgBaseIteratedRadialDriftSlice : Prop :=
  SmoothLeraySliceRegularity →
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ m : ℝ, 0 < m → ∀ dm dp : ℝ, 0 < dm → 2 * m < 3 * dm / 11 →
  ∀ (C₁ : ℝ) (k₁ : ℕ), 0 < C₁ →
    ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ContDiff ℝ ∞ (fun x : ℝ × Space => p.raw x.1 x.2) →
      (∀ i : Fin 2, ContDiff ℝ ∞ (fun x : ℝ × Space => p.inlet i x.1 x.2)) →
      ∀ z : p.Z, ProjectedEquation p z →
      ‖z‖ ≤ C₁ * (p.ν ^ k₁)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) →
      (∀ k : ℕ, ∃ g : (Fin k → Fin 3) → B0411.D p.period p.ν q0E,
        IsIteratedPhaseGrad p.period q0E k (p.wOf z) (fun α => (g α : Yq p.period q0E))) →
      (∀ k : ℕ, ∃ M : ℝ, ∀ τ : ℝ,
        ContDiff ℝ k (bgField p z τ) ∧
        (∀ y : Space, ‖iteratedFDeriv ℝ k (p.corr z τ) y‖ ≤ M) ∧
        eLpNorm (fun y => iteratedFDeriv ℝ k (bgField p z τ) y) 4 volume ≤ ENNReal.ofReal M) →
      (Blueprint.IsBoundedBackground p.raw ∧ ∀ τ, IsSolenoidal (p.raw τ)) →
      (∀ i : Fin 2, Blueprint.IsBoundedBackground (p.inlet i) ∧
        ∀ τ, IsSolenoidal (p.inlet i τ)) →
      IsUniformSmoothL4SliceFamily (bgField p z) →
      ∀ U₁ : ℝ → SpatialField,
        IsUniformSmoothL4SliceFamily U₁ →
        HasPhaseJetDeriv (bgField p z) U₁ →
        U₁ = bgPhaseDerivTower p.ν (bgField p z) 1 →
        RadialDriftTowerSub.IsIteratedRadialDriftSliceFamily (bgField p z)

namespace RadialDriftTowerSub

/-- Under `SmoothLerayRadialDriftComm`, `IsIteratedRadialDriftSliceFamily` is closed under
`smoothLeraySlice`. -/
theorem iteratedRadialDrift_smoothLeraySlice
    (hComm : SmoothLerayRadialDriftComm) {G : ℝ → SpatialField}
    (hG : IsIteratedRadialDriftSliceFamily G) :
    IsIteratedRadialDriftSliceFamily (smoothLeraySlice G) := by
  intro r
  induction r generalizing G with
  | zero =>
      exact (SmoothLeraySliceSub.sliceFamily_smoothLeraySlice_of_repExists
        smoothLerayRepExists_proof G hG.sliceFamily).2
  | succ r ih =>
      have heq :
          (fun τ : ℝ => (spatialRadialDrift^[r + 1]) (smoothLeraySlice G τ)) =
            fun τ =>
              (spatialRadialDrift^[r])
                (smoothLeraySlice (fun τ' => spatialRadialDrift (G τ')) τ) := by
        funext τ
        rw [Function.iterate_succ_apply,
          hComm G hG.sliceFamily hG.spatialRadialDrift_sliceFamily τ]
      rw [heq]
      exact ih (iteratedRadialDrift_spatialRadialDrift hG)

/-- Under `SmoothLerayRadialDriftComm`, `IsIteratedRadialDriftSliceFamily` is closed under
`smoothConvectiveLeray`. -/
theorem iteratedRadialDrift_smoothConvectiveLeray
    (hComm : SmoothLerayRadialDriftComm) {V W : ℝ → SpatialField}
    (hV : IsIteratedRadialDriftSliceFamily V) (hW : IsIteratedRadialDriftSliceFamily W) :
    IsIteratedRadialDriftSliceFamily (smoothConvectiveLeray V W) :=
  iteratedRadialDrift_smoothLeraySlice hComm (iteratedRadialDrift_spatialConvect hV hW)

/-- If `U 0, ..., U m` satisfy `IsIteratedRadialDriftSliceFamily`, then so does the binomial
Leibniz sum `leibnizBilinearSum smoothConvectiveLeray U m`. -/
theorem iteratedRadialDrift_leibnizBilinearSum
    (hComm : SmoothLerayRadialDriftComm)
    {U : ℕ → ℝ → SpatialField} {m : ℕ}
    (hU : ∀ j ≤ m, IsIteratedRadialDriftSliceFamily (U j)) :
    IsIteratedRadialDriftSliceFamily (leibnizBilinearSum smoothConvectiveLeray U m) := by
  unfold leibnizBilinearSum
  refine iteratedRadialDrift_sum (Finset.range (m + 1)) fun j hj => ?_
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hsub : m - j ≤ m := Nat.sub_le m j
  exact iteratedRadialDrift_smul (Nat.choose m j : ℝ)
    (iteratedRadialDrift_smoothConvectiveLeray hComm (hU j hjm) (hU (m - j) hsub))

/-- By strong induction on `m : ℕ`, if `U₀` satisfies `IsIteratedRadialDriftSliceFamily U₀` and
`SmoothLerayRadialDriftComm` holds, then every stage `bgPhaseDerivTower ν U₀ m` satisfies
`IsIteratedRadialDriftSliceFamily`. -/
theorem iteratedRadialDrift_bgPhaseDerivTower
    (hComm : SmoothLerayRadialDriftComm) (ν : ℝ) {U₀ : ℝ → SpatialField}
    (hU₀ : IsIteratedRadialDriftSliceFamily U₀) :
    ∀ m : ℕ, IsIteratedRadialDriftSliceFamily (bgPhaseDerivTower ν U₀ m) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      rcases m with _ | m
      · rw [HigherPhaseSub.bgPhaseDerivTower_zero]
        exact hU₀
      · rw [HigherPhaseSub.bgPhaseDerivTower_succ]
        have hm : IsIteratedRadialDriftSliceFamily (bgPhaseDerivTower ν U₀ m) :=
          ih m (Nat.lt_succ_self m)
        have hLin : IsIteratedRadialDriftSliceFamily
            (fun τ => spatialProjectedLin ν (bgPhaseDerivTower ν U₀ m τ)) :=
          iteratedRadialDrift_spatialProjectedLin ν hm
        have hConv : IsIteratedRadialDriftSliceFamily
            (leibnizBilinearSum smoothConvectiveLeray (bgPhaseDerivTower ν U₀) m) :=
          iteratedRadialDrift_leibnizBilinearSum hComm
            (fun j hj => ih j (Nat.lt_succ_of_le hj))
        exact iteratedRadialDrift_sub hLin hConv

/-- Corollary at `r = 1`: for every `m : ℕ`,
`fun τ => spatialRadialDrift (bgPhaseDerivTower ν U₀ m τ)` lies in `IsUniformSmoothL4SliceFamily`. -/
theorem sliceFamily_spatialRadialDrift_bgPhaseDerivTower
    (hComm : SmoothLerayRadialDriftComm) (ν : ℝ) {U₀ : ℝ → SpatialField}
    (hU₀ : IsIteratedRadialDriftSliceFamily U₀) (m : ℕ) :
    IsUniformSmoothL4SliceFamily
      (fun τ => spatialRadialDrift (bgPhaseDerivTower ν U₀ m τ)) :=
  (iteratedRadialDrift_bgPhaseDerivTower hComm ν hU₀ m).spatialRadialDrift_sliceFamily

end RadialDriftTowerSub

/-- Conditional assembly of `BgHigherOrderRadialDriftSlice` (`PartII-b:S3/1/2/2/2`, SP 2519-2523,
2559-2562) from `SmoothLerayRadialDriftComm` (`PartII-b:S3/1/2/2/2/1`) and
`BgBaseIteratedRadialDriftSlice` (`PartII-b:S3/1/2/2/2/2`). -/
theorem bgHigherOrderRadialDriftSlice_of
    (hComm : SmoothLerayRadialDriftComm)
    (hBase : BgBaseIteratedRadialDriftSlice) :
    BgHigherOrderRadialDriftSlice := by
  intro hLeray Sig lam q hSig hlam m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₀, hν₀, hB⟩ := hBase hLeray Sig lam q hSig hlam m hm dm dp hdm h2m C₁ k₁ hC₁
  refine ⟨ν₀, hν₀, ?_⟩
  intro p d hReg hν hAge hMode hRawCD hInCD z hProj hz hGraph hSlice hRaw hInlet
    hBg U₁ hU₁Smooth hU₁Deriv hU₁Eq m_ord
  have hIter : RadialDriftTowerSub.IsIteratedRadialDriftSliceFamily (bgField p z) :=
    hB p d hReg hν hAge hMode hRawCD hInCD z hProj hz hGraph hSlice hRaw hInlet
      hBg U₁ hU₁Smooth hU₁Deriv hU₁Eq
  exact RadialDriftTowerSub.sliceFamily_spatialRadialDrift_bgPhaseDerivTower
    hComm p.ν hIter (m_ord + 1)

/-- Alias of `bgHigherOrderRadialDriftSlice_of` for backwards compatibility. -/
theorem bgHigherOrderRadialDriftSlice_of_parts
    (hComm : SmoothLerayRadialDriftComm)
    (hBase : BgBaseIteratedRadialDriftSlice) :
    BgHigherOrderRadialDriftSlice :=
  bgHigherOrderRadialDriftSlice_of hComm hBase

end UnforcedLeray.Short.IIb

end
