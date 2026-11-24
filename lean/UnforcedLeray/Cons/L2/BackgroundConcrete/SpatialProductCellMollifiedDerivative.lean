import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellHolder

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ContDiff ENNReal

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint
open UnforcedLeray.PhaseSpace
open UnforcedLeray.Sob

/-- Restricting a smooth spacetime scalar to a fixed phase differentiates in the spatial
component of the spacetime direction. This scalar-valued form is used for the mollified product. -/
theorem fderiv_scalarSlice_eq_spatial {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : SpaceTime → F} (hf : Differentiable ℝ f)
    (τ : ℝ) (y v : Space) :
    fderiv ℝ (fun x : Space => f (τ, x)) y v = fderiv ℝ f (τ, y) (0, v) := by
  have hmap : HasFDerivAt (fun x : Space => (τ, x))
      ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space)) y :=
    (hasFDerivAt_const τ y).prodMk (hasFDerivAt_id y)
  have hcomp := (hf (τ, y)).hasFDerivAt.comp y hmap
  have h := congrArg (fun A : Space →L[ℝ] F => A v) hcomp.fderiv
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
    zero_apply] using h

/-- The spatial derivative of the physical mollification is the physical representative of the
actual mollified weak derivative supplied by the frozen Hilbert-space identity. -/
theorem spatialDerivative_mollifiedPhaseCutoffScalarProduct {P : ℝ} [Fact (0 < P)]
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {U : ℝ → SpatialField} (hU : IsBoundedBackground U)
    (n k : ℕ) (j : Fin 3) (τ : ℝ) (y : Space) :
    fderiv ℝ (fun x : Space => mollifiedPhaseCutoffScalarProduct P n k Φ U (τ, x)) y
        (EuclideanSpace.single j (1 : ℝ)) =
      (moll (spacetimeShrinkBump k) volume
        ((fun z : SpaceTime => phaseCutoffSpaceTime (phaseInteriorCutoff P n) z •
          fderiv ℝ (fun x : Space => scalarTestBackground Φ U (z.1, x)) z.2
            (EuclideanSpace.single j (1 : ℝ))) ∘ spacetimeHilbertEquiv.symm))
        (spacetimeHilbertEquiv (τ, y)) := by
  let χ : ℝ → ℝ := phaseInteriorCutoff P n
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  have hcell := scalarTestBackground_memLp_cell (p := 2) hΦ hU (by norm_num)
  have hcut : MemLp (fun z : SpaceTime => phaseCutoffSpaceTime χ z •
      scalarTestBackground Φ U z) 2 volume := by
    simpa [χ, phaseCutoffSpaceTime] using
      (memLp_phaseInteriorCutoff_of_cell_memLp (P := P) hcell n)
  have hiter := iterDD_cutoff_scalarTestBackground_mollification_of_cellLp
    (P := P) (hΦ := hΦ) (hU := hU) (hχ := contDiff_phaseInteriorCutoff P n)
    (p := 2) (j := j) (n := k) hcut
  have hFmemST : MemLp
      (phaseCutoffScalarProduct P n Φ U ∘ spacetimeHilbertEquiv.symm) 2 volume :=
    memLp_spacetimeHilbertPullback hcut
  have hHilbcd : ContDiff ℝ ∞
      (moll (spacetimeShrinkBump k) volume
        (phaseCutoffScalarProduct P n Φ U ∘ spacetimeHilbertEquiv.symm)) :=
    contDiff_spacetimeMollification hFmemST k
  have hMcd : ContDiff ℝ ∞ (mollifiedPhaseCutoffScalarProduct P n k Φ U) := by
    exact hHilbcd.comp spacetimeHilbertEquiv.contDiff
  let e : Space := EuclideanSpace.single j (1 : ℝ)
  have hchain : fderiv ℝ (mollifiedPhaseCutoffScalarProduct P n k Φ U) (τ, y)
        (scalarTestSpaceTimeDir j) =
      fderiv ℝ (moll (spacetimeShrinkBump k) volume
        ((phaseCutoffScalarProduct P n Φ U) ∘ spacetimeHilbertEquiv.symm))
        (spacetimeHilbertEquiv (τ, y))
        (spacetimeHilbertEquiv (scalarTestSpaceTimeDir j)) := by
    have hcomp := ((hHilbcd.differentiable (by simp)
      (spacetimeHilbertEquiv (τ, y))).hasFDerivAt.comp
        (τ, y) spacetimeHilbertEquiv.hasFDerivAt)
    change fderiv ℝ
      ((moll (spacetimeShrinkBump k) volume
        (phaseCutoffScalarProduct P n Φ U ∘ spacetimeHilbertEquiv.symm)) ∘
          spacetimeHilbertEquiv) (τ, y) (scalarTestSpaceTimeDir j) = _
    have h := congrArg
      (fun A : SpaceTime →L[ℝ] ℂ => A (scalarTestSpaceTimeDir j)) hcomp.fderiv
    convert h using 1 <;> rfl
  have hchain' : fderiv ℝ (mollifiedPhaseCutoffScalarProduct P n k Φ U)
      (τ, y) (0, e) =
      fderiv ℝ (moll (spacetimeShrinkBump k) volume
        (phaseCutoffScalarProduct P n Φ U ∘ spacetimeHilbertEquiv.symm))
        (spacetimeHilbertEquiv (τ, y))
        (spacetimeHilbertEquiv (0, e)) := by
    simpa [scalarTestSpaceTimeDir, e] using hchain
  have hslice := fderiv_scalarSlice_eq_spatial (hMcd.differentiable (by simp)) τ y e
  have hiterAt := congrFun hiter (spacetimeHilbertEquiv (τ, y))
  have hiterAt' :
      fderiv ℝ (moll (spacetimeShrinkBump k) volume
        ((fun z : SpaceTime => phaseCutoffSpaceTime (phaseInteriorCutoff P n) z •
          scalarTestBackground Φ U z) ∘ spacetimeHilbertEquiv.symm))
        (spacetimeHilbertEquiv (τ, y))
        (spacetimeHilbertEquiv (0, e)) =
      (moll (spacetimeShrinkBump k) volume
        ((fun z : SpaceTime => phaseCutoffSpaceTime (phaseInteriorCutoff P n) z •
          fderiv ℝ (fun x : Space => scalarTestBackground Φ U (z.1, x)) z.2 e) ∘
          spacetimeHilbertEquiv.symm)) (spacetimeHilbertEquiv (τ, y)) := by
    simpa [iterDD, phaseCutoffScalarProduct, scalarTestSpaceTimeDir, e] using hiterAt
  change fderiv ℝ (fun x : Space => mollifiedPhaseCutoffScalarProduct P n k Φ U (τ, x)) y e = _
  calc
    _ = fderiv ℝ (mollifiedPhaseCutoffScalarProduct P n k Φ U) (τ, y) (0, e) := hslice
    _ = fderiv ℝ (moll (spacetimeShrinkBump k) volume
        (phaseCutoffScalarProduct P n Φ U ∘ spacetimeHilbertEquiv.symm))
        (spacetimeHilbertEquiv (τ, y)) (spacetimeHilbertEquiv (0, e)) := hchain'
    _ = _ := by
      change fderiv ℝ (moll (spacetimeShrinkBump k) volume
        ((fun z : SpaceTime => phaseCutoffSpaceTime (phaseInteriorCutoff P n) z •
          scalarTestBackground Φ U z) ∘ spacetimeHilbertEquiv.symm))
        (spacetimeHilbertEquiv (τ, y)) (spacetimeHilbertEquiv (0, e)) = _
      exact hiterAt'

#print axioms fderiv_scalarSlice_eq_spatial
#print axioms spatialDerivative_mollifiedPhaseCutoffScalarProduct

end UnforcedLeray.Cons.C03.Concrete
