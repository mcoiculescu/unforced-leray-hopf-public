import UnforcedLeray.Cons.L2.BackgroundConcrete.ProjectedTest
import UnforcedLeray.Lib.CZL2.TestProjection
import UnforcedLeray.Lib.LerayLp.Leray

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0412
open UnforcedLeray.RieszLp
open scoped ContDiff

/-- Real component tests for the scalar Newton potential in the slice-wise Leray decomposition. -/
def projectedPotentialReTest (Φ : ℝ × Space → CVec3) (τ : ℝ) : Fin 3 → Space → ℝ :=
  fun i y => (Φ (τ, y) i).re

/-- Imaginary component tests for the scalar Newton potential in the slice-wise Leray decomposition. -/
def projectedPotentialImTest (Φ : ℝ × Space → CVec3) (τ : ℝ) : Fin 3 → Space → ℝ :=
  fun i y => (Φ (τ, y) i).im

/-- The actual phasewise Newton-potential decomposition of the complex Leray projection of a
compact smooth phase test. No compactness of the projected vector field is asserted. -/
theorem lerayProjectedPhaseTest_eq_newtonPotentialGrad_ae
    {P : ℝ} {r : ℝ≥0∞} [Fact (1 ≤ r)] [Fact (0 < P)]
    (hr1 : 1 < r) (hrtop : r ≠ ⊤) {Φ : ℝ × Space → CVec3}
    (hΦ : IsPhaseTest P Φ) (τ : ℝ) :
    (fun y => lerayProjectedPhaseTest hr1 hrtop (hΦ.isSliceTest r) (τ, y)) =ᵐ[volume]
      fun y => Φ (τ, y) +
        ofReV (gradField (lerayPotential (projectedPotentialReTest Φ τ)) y) +
        ofImV (gradField (lerayPotential (projectedPotentialImTest Φ τ)) y) := by
  let fR : Fin 3 → Space → ℝ := projectedPotentialReTest Φ τ
  let fI : Fin 3 → Space → ℝ := projectedPotentialImTest Φ τ
  have hsmooth : ContDiff ℝ ∞ (fun y : Space => Φ (τ, y)) :=
    hΦ.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hcompact : HasCompactSupport (fun y : Space => Φ (τ, y)) := hΦ.hasCompactSupport_slice τ
  have hR (i : Fin 3) : IsSpatialTest (fR i) := by
    let coordCLM : CVec3 →L[ℝ] ℂ :=
      (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin 3) i).restrictScalars ℝ
    refine ⟨?_, ?_⟩
    · change ContDiff ℝ ∞ (fun y => Complex.reCLM ((Φ (τ, y)).ofLp i))
      exact Complex.reCLM.contDiff.comp (coordCLM.contDiff.comp hsmooth)
    · exact hcompact.comp_left (g := fun x : CVec3 => Complex.reCLM (coordCLM x)) (by simp)
  have hI (i : Fin 3) : IsSpatialTest (fI i) := by
    let coordCLM : CVec3 →L[ℝ] ℂ :=
      (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin 3) i).restrictScalars ℝ
    refine ⟨?_, ?_⟩
    · change ContDiff ℝ ∞ (fun y => Complex.imCLM ((Φ (τ, y)).ofLp i))
      exact Complex.imCLM.contDiff.comp (coordCLM.contDiff.comp hsmooth)
    · exact hcompact.comp_left (g := fun x : CVec3 => Complex.imCLM (coordCLM x)) (by simp)
  let FR : SpatialField := vecField fR
  let FI : SpatialField := vecField fI
  have hFRr : MemLp FR r volume := memLp_vecField hR r
  have hFIr : MemLp FI r volume := memLp_vecField hI r
  have hFR2 : MemLp FR 2 volume := memLp_vecField hR 2
  have hFI2 : MemLp FI 2 volume := memLp_vecField hI 2
  let s : Lp CVec3 r (volume : Measure Space) := sliceMap (hΦ.isSliceTest r).2 τ
  have hRclass : reV.compLpL r volume s = hFRr.toLp FR := by
    apply Lp.ext
    filter_upwards [reV.coeFn_compLpL (μ := volume) (p := r) s,
      (hΦ.isSliceTest r).2.memLp τ |>.coeFn_toLp,
      hFRr.coeFn_toLp] with y h1 h2 h3
    rw [h1]
    dsimp [s, sliceMap] at h2 ⊢
    rw [h2]
    rw [h3]
    ext i
    simp [FR, vecField_apply, fR, projectedPotentialReTest, reV_apply]
  have hIclass : imV.compLpL r volume s = hFIr.toLp FI := by
    apply Lp.ext
    filter_upwards [imV.coeFn_compLpL (μ := volume) (p := r) s,
      (hΦ.isSliceTest r).2.memLp τ |>.coeFn_toLp,
      hFIr.coeFn_toLp] with y h1 h2 h3
    rw [h1]
    dsimp [s, sliceMap] at h2 ⊢
    rw [h2]
    rw [h3]
    ext i
    simp [FI, vecField_apply, fI, projectedPotentialImTest, imV_apply]
  have hRproj := lerayLp_toLp_ae_eq_projection hr1 hrtop hFRr hFR2
  have hIproj := lerayLp_toLp_ae_eq_projection hr1 hrtop hFIr hFI2
  have hRval : (lerayLp r hr1 hrtop (reV.compLpL r volume s) : SpatialField) =ᵐ[volume]
      FR + gradField (lerayPotential fR) := by
    have hinput : reV.compLpL r volume s = hFRr.toLp FR := hRclass
    have h := hRproj
    rw [← hinput] at h
    rw [projection_toL2_vecField hR] at h
    have hsum := coeFn_toL2 (hFR2.add (memLp_gradField_lerayPotential hR))
    filter_upwards [h, hsum] with y hy hs
    rw [hy, hs]
  have hIval : (lerayLp r hr1 hrtop (imV.compLpL r volume s) : SpatialField) =ᵐ[volume]
      FI + gradField (lerayPotential fI) := by
    have hinput : imV.compLpL r volume s = hFIr.toLp FI := hIclass
    have h := hIproj
    rw [← hinput] at h
    rw [projection_toL2_vecField hI] at h
    have hsum := coeFn_toL2 (hFI2.add (memLp_gradField_lerayPotential hI))
    filter_upwards [h, hsum] with y hy hs
    rw [hy, hs]
  filter_upwards [coeFn_lerayC hr1 hrtop s, hRval, hIval] with y hproj hrv hiv
  change ((lerayC r hr1 hrtop s : Lp CVec3 r volume) : Space → CVec3) y = _
  rw [hproj, hrv, hiv]
  have hRparts : FR y = reV (Φ (τ, y)) := by
    ext i
    simp [FR, vecField, sum_smul_coordinateVector_apply, fR,
      projectedPotentialReTest, reV_apply]
  have hIparts : FI y = imV (Φ (τ, y)) := by
    ext i
    simp [FI, vecField, sum_smul_coordinateVector_apply, fI,
      projectedPotentialImTest, imV_apply]
  simp only [Pi.add_apply, map_add, hRparts, hIparts, fR, fI]
  calc
    ofReV (reV (Φ (τ, y))) +
        ofReV (gradField (lerayPotential (projectedPotentialReTest Φ τ)) y) +
        (ofImV (imV (Φ (τ, y))) +
          ofImV (gradField (lerayPotential (projectedPotentialImTest Φ τ)) y)) =
        (ofReV (reV (Φ (τ, y))) + ofImV (imV (Φ (τ, y)))) +
          (ofReV (gradField (lerayPotential (projectedPotentialReTest Φ τ)) y) +
            ofImV (gradField (lerayPotential (projectedPotentialImTest Φ τ)) y)) := by abel
    _ = Φ (τ, y) + ofReV (gradField (lerayPotential (projectedPotentialReTest Φ τ)) y) +
        ofImV (gradField (lerayPotential (projectedPotentialImTest Φ τ)) y) := by
      rw [ofReV_reV_add_ofImV_imV]
      simp only [add_assoc]

#print axioms lerayProjectedPhaseTest_eq_newtonPotentialGrad_ae

end UnforcedLeray.Cons.C03.Concrete

end
