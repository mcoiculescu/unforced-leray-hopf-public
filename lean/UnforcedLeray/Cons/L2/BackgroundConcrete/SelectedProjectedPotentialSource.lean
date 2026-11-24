import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedPotential

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0412
open UnforcedLeray.RieszLp

/-- The real-coordinate map on complex three-vectors. -/
def projectedPotentialReCoordCLM (i : Fin 3) : CVec3 →L[ℝ] ℝ :=
  Complex.reCLM.comp
    ((EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin 3) i).restrictScalars ℝ)

/-- The imaginary-coordinate map on complex three-vectors. -/
def projectedPotentialImCoordCLM (i : Fin 3) : CVec3 →L[ℝ] ℝ :=
  Complex.imCLM.comp
    ((EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin 3) i).restrictScalars ℝ)

def projectedPotentialReCoord (Φ : ℝ × Space → CVec3) (i : Fin 3) : ℝ × Space → ℝ :=
  fun p => projectedPotentialReCoordCLM i (Φ p)

def projectedPotentialImCoord (Φ : ℝ × Space → CVec3) (i : Fin 3) : ℝ × Space → ℝ :=
  fun p => projectedPotentialImCoordCLM i (Φ p)

/-- The real and imaginary divergence source families whose slice Newton potentials appear in
`lerayProjectedPhaseTest_eq_newtonPotentialGrad_ae`. -/
def projectedPotentialReDiv (Φ : ℝ × Space → CVec3) (p : ℝ × Space) : ℝ :=
  ∑ i : Fin 3, fderiv ℝ (projectedPotentialReCoord Φ i) p (0, coordinateVector i)

def projectedPotentialImDiv (Φ : ℝ × Space → CVec3) (p : ℝ × Space) : ℝ :=
  ∑ i : Fin 3, fderiv ℝ (projectedPotentialImCoord Φ i) p (0, coordinateVector i)

theorem isPhaseTest_projectedPotentialReDiv {P : ℝ} {Φ : ℝ × Space → CVec3}
    (hΦ : IsPhaseTest P Φ) : IsPhaseTest P (projectedPotentialReDiv Φ) := by
  unfold projectedPotentialReDiv
  change IsPhaseTest P (∑ i : Fin 3, fun p =>
    fderiv ℝ (projectedPotentialReCoord Φ i) p (0, coordinateVector i))
  apply IsPhaseTest.sum Finset.univ
  intro i hi
  exact (hΦ.clm_comp (projectedPotentialReCoordCLM i)).fderiv_apply
    (0, coordinateVector i)

theorem isPhaseTest_projectedPotentialImDiv {P : ℝ} {Φ : ℝ × Space → CVec3}
    (hΦ : IsPhaseTest P Φ) : IsPhaseTest P (projectedPotentialImDiv Φ) := by
  unfold projectedPotentialImDiv
  change IsPhaseTest P (∑ i : Fin 3, fun p =>
    fderiv ℝ (projectedPotentialImCoord Φ i) p (0, coordinateVector i))
  apply IsPhaseTest.sum Finset.univ
  intro i hi
  exact (hΦ.clm_comp (projectedPotentialImCoordCLM i)).fderiv_apply
    (0, coordinateVector i)

/-- On each phase slice the compact phase-test divergence source is exactly the spatial `divTest`
used by the concrete Newton potential. -/
theorem projectedPotentialReDiv_slice {P : ℝ} (Φ : ℝ × Space → CVec3)
    (hΦ : IsPhaseTest P Φ) (τ : ℝ) (y : Space) :
    projectedPotentialReDiv Φ (τ, y) =
      divTest (projectedPotentialReTest Φ τ) y := by
  unfold projectedPotentialReDiv UnforcedLeray.RieszLp.divTest
  refine Finset.sum_congr rfl ?_
  intro i hi
  let g : ℝ × Space → ℝ := projectedPotentialReCoord Φ i
  let inc : Space → ℝ × Space := fun x => (τ, x)
  have hg : ContDiff ℝ ∞ g := (hΦ.clm_comp (projectedPotentialReCoordCLM i)).smooth
  have hgD : Differentiable ℝ g := hg.differentiable (by simp)
  have hincC : ContDiff ℝ ∞ inc :=
    (contDiff_const : ContDiff ℝ ∞ (fun _ : Space => τ)).prodMk contDiff_id
  have hincD : Differentiable ℝ inc := hincC.differentiable (by simp)
  have hincF : HasFDerivAt inc
      (ContinuousLinearMap.prod 0 (ContinuousLinearMap.id ℝ Space)) y := by
    simpa [inc] using (hasFDerivAt_const τ y).prodMk (hasFDerivAt_id y)
  have hcomp := (hgD (τ, y)).hasFDerivAt.comp y (hincD y).hasFDerivAt
  have hincv : fderiv ℝ inc y (coordinateVector i) = (0, coordinateVector i) := by
    rw [hincF.fderiv]
    simp
  change fderiv ℝ g (τ, y) (0, coordinateVector i) =
    fderiv ℝ (fun x : Space => (Φ (τ, x) i).re) y (coordinateVector i)
  have hslice : (fun x : Space => (Φ (τ, x) i).re) = g ∘ inc := by
    funext x
    rfl
  rw [hslice, hcomp.fderiv]
  rw [ContinuousLinearMap.comp_apply, hincv]

/-- Actual real Newton-potential component of the selected projected-test correction. -/
def projectedPotentialRePath (Φ : ℝ × Space → CVec3) (p : ℝ × Space) : ℝ :=
  lerayPotential (projectedPotentialReTest Φ p.1) p.2

/-- Actual imaginary Newton-potential component of the selected projected-test correction. -/
def projectedPotentialImPath (Φ : ℝ × Space → CVec3) (p : ℝ × Space) : ℝ :=
  lerayPotential (projectedPotentialImTest Φ p.1) p.2

theorem isSpatialTest_projectedPotentialReTest {P : ℝ} {Φ : ℝ × Space → CVec3}
    (hΦ : IsPhaseTest P Φ) (τ : ℝ) :
    ∀ i, IsSpatialTest (projectedPotentialReTest Φ τ i) := by
  have hsmooth : ContDiff ℝ ∞ (fun y : Space => Φ (τ, y)) :=
    hΦ.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hcompact : HasCompactSupport (fun y : Space => Φ (τ, y)) := hΦ.hasCompactSupport_slice τ
  intro i
  refine ⟨(projectedPotentialReCoordCLM i).contDiff.comp hsmooth, ?_⟩
  exact hcompact.comp_left (g := fun x : CVec3 => projectedPotentialReCoordCLM i x) (by simp)

theorem isSpatialTest_projectedPotentialImTest {P : ℝ} {Φ : ℝ × Space → CVec3}
    (hΦ : IsPhaseTest P Φ) (τ : ℝ) :
    ∀ i, IsSpatialTest (projectedPotentialImTest Φ τ i) := by
  have hsmooth : ContDiff ℝ ∞ (fun y : Space => Φ (τ, y)) :=
    hΦ.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hcompact : HasCompactSupport (fun y : Space => Φ (τ, y)) := hΦ.hasCompactSupport_slice τ
  intro i
  refine ⟨(projectedPotentialImCoordCLM i).contDiff.comp hsmooth, ?_⟩
  exact hcompact.comp_left (g := fun x : CVec3 => projectedPotentialImCoordCLM i x) (by simp)

theorem projectedPotentialRePath_contDiff_slice {P : ℝ} {Φ : ℝ × Space → CVec3}
    (hΦ : IsPhaseTest P Φ) (τ : ℝ) :
    ContDiff ℝ ∞ (fun y => projectedPotentialRePath Φ (τ, y)) := by
  exact lerayPotential_contDiff (isSpatialTest_projectedPotentialReTest hΦ τ)

theorem projectedPotentialImPath_contDiff_slice {P : ℝ} {Φ : ℝ × Space → CVec3}
    (hΦ : IsPhaseTest P Φ) (τ : ℝ) :
    ContDiff ℝ ∞ (fun y => projectedPotentialImPath Φ (τ, y)) := by
  exact lerayPotential_contDiff (isSpatialTest_projectedPotentialImTest hΦ τ)

/-- The same slice identification for the imaginary source. -/
theorem projectedPotentialImDiv_slice {P : ℝ} (Φ : ℝ × Space → CVec3)
    (hΦ : IsPhaseTest P Φ) (τ : ℝ) (y : Space) :
    projectedPotentialImDiv Φ (τ, y) =
      divTest (projectedPotentialImTest Φ τ) y := by
  unfold projectedPotentialImDiv UnforcedLeray.RieszLp.divTest
  refine Finset.sum_congr rfl ?_
  intro i hi
  let g : ℝ × Space → ℝ := projectedPotentialImCoord Φ i
  let inc : Space → ℝ × Space := fun x => (τ, x)
  have hg : ContDiff ℝ ∞ g := (hΦ.clm_comp (projectedPotentialImCoordCLM i)).smooth
  have hgD : Differentiable ℝ g := hg.differentiable (by simp)
  have hincC : ContDiff ℝ ∞ inc :=
    (contDiff_const : ContDiff ℝ ∞ (fun _ : Space => τ)).prodMk contDiff_id
  have hincD : Differentiable ℝ inc := hincC.differentiable (by simp)
  have hincF : HasFDerivAt inc
      (ContinuousLinearMap.prod 0 (ContinuousLinearMap.id ℝ Space)) y := by
    simpa [inc] using (hasFDerivAt_const τ y).prodMk (hasFDerivAt_id y)
  have hcomp := (hgD (τ, y)).hasFDerivAt.comp y (hincD y).hasFDerivAt
  have hincv : fderiv ℝ inc y (coordinateVector i) = (0, coordinateVector i) := by
    rw [hincF.fderiv]
    simp
  change fderiv ℝ g (τ, y) (0, coordinateVector i) =
    fderiv ℝ (fun x : Space => (Φ (τ, x) i).im) y (coordinateVector i)
  have hslice : (fun x : Space => (Φ (τ, x) i).im) = g ∘ inc := by
    funext x
    rfl
  rw [hslice, hcomp.fderiv]
  rw [ContinuousLinearMap.comp_apply, hincv]

theorem projectedPotentialRePath_periodic {P : ℝ} {Φ : ℝ × Space → CVec3}
    (hΦ : IsPhaseTest P Φ) :
    ∀ τ y, projectedPotentialRePath Φ (τ + P, y) = projectedPotentialRePath Φ (τ, y) := by
  intro τ y
  have hsrc : divTest (projectedPotentialReTest Φ (τ + P)) =
      divTest (projectedPotentialReTest Φ τ) := by
    funext x
    rw [← projectedPotentialReDiv_slice Φ hΦ (τ + P) x,
      ← projectedPotentialReDiv_slice Φ hΦ τ x]
    exact (isPhaseTest_projectedPotentialReDiv hΦ).periodic τ x
  change lerayPotential (projectedPotentialReTest Φ (τ + P)) y =
    lerayPotential (projectedPotentialReTest Φ τ) y
  simp [lerayPotential, hsrc]

theorem projectedPotentialImPath_periodic {P : ℝ} {Φ : ℝ × Space → CVec3}
    (hΦ : IsPhaseTest P Φ) :
    ∀ τ y, projectedPotentialImPath Φ (τ + P, y) = projectedPotentialImPath Φ (τ, y) := by
  intro τ y
  have hsrc : divTest (projectedPotentialImTest Φ (τ + P)) =
      divTest (projectedPotentialImTest Φ τ) := by
    funext x
    rw [← projectedPotentialImDiv_slice Φ hΦ (τ + P) x,
      ← projectedPotentialImDiv_slice Φ hΦ τ x]
    exact (isPhaseTest_projectedPotentialImDiv hΦ).periodic τ x
  change lerayPotential (projectedPotentialImTest Φ (τ + P)) y =
    lerayPotential (projectedPotentialImTest Φ τ) y
  simp [lerayPotential, hsrc]

#print axioms isPhaseTest_projectedPotentialReDiv
#print axioms isPhaseTest_projectedPotentialImDiv
#print axioms projectedPotentialReDiv_slice
#print axioms projectedPotentialImDiv_slice
#print axioms projectedPotentialRePath_periodic
#print axioms projectedPotentialImPath_periodic

end UnforcedLeray.Cons.C03.Concrete

end
