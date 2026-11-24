import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedPotentialPathSmooth
import UnforcedLeray.Cons.L2.BackgroundConcrete.RepresentativeLp
import UnforcedLeray.Lib.FreeStressCouplings.ProdLp

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

open MeasureTheory
open Set
open scoped ENNReal

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0412
open UnforcedLeray.RieszLp

local instance dual_q0_ge_one_cell : Fact (1 ≤ conjExp q0E) := ⟨by
  norm_num [PhaseSpace.conjExp, q0E, B0281.q0]⟩

local instance q0_ne_top_cell : Fact (q0E ≠ ⊤) := ⟨q0E_ne_top⟩

private def projectedNewtonCorrection (Φ : SpaceTime → CVec3) (z : SpaceTime) : CVec3 :=
  ofReV (gradField (fun y => projectedPotentialRePath Φ (z.1, y)) z.2) +
    ofImV (gradField (fun y => projectedPotentialImPath Φ (z.1, y)) z.2)

private theorem continuous_projectedNewtonCorrection {P : ℝ} {Φ : SpaceTime → CVec3}
    (hΦ : IsPhaseTest P Φ) : Continuous (projectedNewtonCorrection Φ) := by
  have hR := contDiff_projectedPotentialRePath hΦ
  have hI := contDiff_projectedPotentialImPath hΦ
  have hRfd : Continuous (fderiv ℝ (projectedPotentialRePath Φ)) :=
    hR.continuous_fderiv (by simp)
  have hIfd : Continuous (fderiv ℝ (projectedPotentialImPath Φ)) :=
    hI.continuous_fderiv (by simp)
  have hRcoord (i : Fin 3) : Continuous (fun z : SpaceTime =>
      fderiv ℝ (projectedPotentialRePath Φ) z (0, coordinateVector i)) :=
    hRfd.clm_apply continuous_const
  have hIcoord (i : Fin 3) : Continuous (fun z : SpaceTime =>
      fderiv ℝ (projectedPotentialImPath Φ) z (0, coordinateVector i)) :=
    hIfd.clm_apply continuous_const
  have hRgrad : Continuous (fun z : SpaceTime =>
      gradField (fun y => projectedPotentialRePath Φ (z.1, y)) z.2) := by
    unfold gradField
    refine continuous_finsetSum Finset.univ ?_
    intro i hi
    have hslice (z : SpaceTime) : spatialTestDerivative i
        (fun y => projectedPotentialRePath Φ (z.1, y)) z.2 =
        fderiv ℝ (projectedPotentialRePath Φ) z (0, coordinateVector i) := by
      unfold spatialTestDerivative
      let inc : Space → SpaceTime := fun y => (z.1, y)
      have hinc : HasFDerivAt inc (ContinuousLinearMap.prod 0 (ContinuousLinearMap.id ℝ Space)) z.2 := by
        simpa [inc] using (hasFDerivAt_const z.1 z.2).prodMk (hasFDerivAt_id z.2)
      have hcomp := (hR.differentiable (by simp) z).hasFDerivAt.comp z.2 hinc
      change fderiv ℝ (projectedPotentialRePath Φ ∘ inc) z.2 (coordinateVector i) = _
      rw [hcomp.fderiv]
      simp [inc, ContinuousLinearMap.comp_apply]
    have hcoord := hRcoord i
    have heq : (fun z : SpaceTime => spatialTestDerivative i
        (fun y => projectedPotentialRePath Φ (z.1, y)) z.2) =
        fun z => fderiv ℝ (projectedPotentialRePath Φ) z (0, coordinateVector i) := by
      funext z
      exact hslice z
    have hfun : (fun z : SpaceTime => spatialTestDerivative i
        (fun y => projectedPotentialRePath Φ (z.1, y)) z.2 • coordinateVector i) =
        fun z => (fderiv ℝ (projectedPotentialRePath Φ) z (0, coordinateVector i)) •
          coordinateVector i := by
      funext z
      rw [hslice z]
    rw [hfun]
    exact hcoord.smul continuous_const
  have hIgrad : Continuous (fun z : SpaceTime =>
      gradField (fun y => projectedPotentialImPath Φ (z.1, y)) z.2) := by
    unfold gradField
    refine continuous_finsetSum Finset.univ ?_
    intro i hi
    have hslice (z : SpaceTime) : spatialTestDerivative i
        (fun y => projectedPotentialImPath Φ (z.1, y)) z.2 =
        fderiv ℝ (projectedPotentialImPath Φ) z (0, coordinateVector i) := by
      unfold spatialTestDerivative
      let inc : Space → SpaceTime := fun y => (z.1, y)
      have hinc : HasFDerivAt inc (ContinuousLinearMap.prod 0 (ContinuousLinearMap.id ℝ Space)) z.2 := by
        simpa [inc] using (hasFDerivAt_const z.1 z.2).prodMk (hasFDerivAt_id z.2)
      have hcomp := (hI.differentiable (by simp) z).hasFDerivAt.comp z.2 hinc
      change fderiv ℝ (projectedPotentialImPath Φ ∘ inc) z.2 (coordinateVector i) = _
      rw [hcomp.fderiv]
      simp [inc, ContinuousLinearMap.comp_apply]
    have hcoord := hIcoord i
    have heq : (fun z : SpaceTime => spatialTestDerivative i
        (fun y => projectedPotentialImPath Φ (z.1, y)) z.2) =
        fun z => fderiv ℝ (projectedPotentialImPath Φ) z (0, coordinateVector i) := by
      funext z
      exact hslice z
    have hfun : (fun z : SpaceTime => spatialTestDerivative i
        (fun y => projectedPotentialImPath Φ (z.1, y)) z.2 • coordinateVector i) =
        fun z => (fderiv ℝ (projectedPotentialImPath Φ) z (0, coordinateVector i)) •
          coordinateVector i := by
      funext z
      rw [hslice z]
    rw [hfun]
    exact hcoord.smul continuous_const
  unfold projectedNewtonCorrection
  exact (ofReV.continuous.comp hRgrad).add (ofImV.continuous.comp hIgrad)

/-- The actual Newton-gradient correction in the Leray projection belongs to the dual exponent
on a whole period cell. This is obtained from the genuine phase-space Leray projection and its
Newton representation, with joint smoothness supplying a measurable representative. -/
theorem memLp_projectedNewtonCorrection_cell {P : ℝ} [Fact (0 < P)]
    {Φ : SpaceTime → CVec3} (hΦ : IsPhaseTest P Φ) :
    MemLp (projectedNewtonCorrection Φ) (conjExp q0E)
      (volume.restrict (Ioc (0 : ℝ) P ×ˢ (univ : Set Space))) := by
  have hr1 : 1 < conjExp q0E := by
    exact one_lt_of_holderConjugate q0E_ne_top
  have hrtop : conjExp q0E ≠ ⊤ := conjExp_ne_top one_lt_q0E
  let hs : IsSliceTest P (conjExp q0E) Φ := hΦ.isSliceTest (conjExp q0E)
  let hproj : IsSliceTest P (conjExp q0E)
      (lerayProjectedPhaseTest hr1 hrtop hs) :=
    isSliceTest_lerayProjectedPhaseTest hr1 hrtop hs
  let wproj : Yq P (conjExp q0E) := testElem P (conjExp q0E)
    (lerayProjectedPhaseTest hr1 hrtop hs)
  let wbase : Yq P (conjExp q0E) := testElem P (conjExp q0E) Φ
  let S : Set SpaceTime := Ioc (0 : ℝ) P ×ˢ (univ : Set Space)
  let μ : Measure SpaceTime := volume.restrict S
  have hrep : MemLp (fun z : SpaceTime => rep wproj z.1 z.2) (conjExp q0E) μ := by
    simpa [wproj, μ, S] using
      memLp_rep_periodCell (q := conjExp q0E) (conjExp_ne_top one_lt_q0E) wproj
  have hbase : MemLp (fun z : SpaceTime => rep wbase z.1 z.2) (conjExp q0E) μ := by
    simpa [wbase, μ, S] using
      memLp_rep_periodCell (q := conjExp q0E) (conjExp_ne_top one_lt_q0E) wbase
  have hbaseCircle : (fun θ : AddCircle P => wbase θ) =ᵐ[AddCircle.haarAddCircle]
      fun θ => circleSlice hs θ := by
    change (fun θ : AddCircle P => testElem P (conjExp q0E) Φ θ) =ᵐ[AddCircle.haarAddCircle]
      fun θ => circleSlice hs θ
    rw [testElem_of hs]
    exact ContinuousMap.coeFn_toLp (E := Lp CVec3 (conjExp q0E) volume)
      (p := conjExp q0E) (𝕜 := ℂ) AddCircle.haarAddCircle (circleSlice hs)
  have hbaseTime := UnforcedLeray.PhaseTrace.ae_comp_mk hbaseCircle
  have hbaseSlice : ∀ᵐ τ : ℝ ∂volume, (fun y : Space => rep wbase τ y) =ᵐ[volume]
      fun y => Φ (τ, y) := by
    filter_upwards [hbaseTime] with τ hτ
    have hr := rep_slice wbase τ
    have ht := MemLp.coeFn_toLp (hs.2.memLp τ)
    have hte : (wbase (τ : AddCircle P) : Lp CVec3 (conjExp q0E) volume) =
        circleSlice hs (τ : AddCircle P) := hτ
    filter_upwards [hr, ht] with y hrepY htestY
    have hcoerce : ((wbase (τ : AddCircle P) : Lp CVec3 (conjExp q0E) volume) :
        Space → CVec3) y = (circleSlice hs (τ : AddCircle P) : Space → CVec3) y :=
      congrArg (fun f : Lp CVec3 (conjExp q0E) volume => (f : Space → CVec3) y) hte
    rw [hrepY, hcoerce, circleSlice_coe hs τ]
    exact (by simpa only [sliceMap] using htestY)
  have hPhiEq : (fun z : SpaceTime => rep wbase z.1 z.2) =ᵐ[μ] Φ := by
    have hglobal := (UnforcedLeray.FreeStress.ae_eq_prod_iff
      (stronglyMeasurable_rep wbase).aestronglyMeasurable
      hΦ.smooth.continuous.aestronglyMeasurable).2 hbaseSlice
    have hprod : (fun z : SpaceTime => rep wbase z.1 z.2) =ᵐ[volume] Φ := by
      simpa only [Measure.volume_eq_prod] using hglobal
    exact ae_restrict_of_ae hprod
  have hPhiMem : MemLp Φ (conjExp q0E) μ := hbase.ae_eq hPhiEq
  let G : SpaceTime → CVec3 := fun z => Φ z + projectedNewtonCorrection Φ z
  have hGcont : Continuous G := hΦ.smooth.continuous.add (continuous_projectedNewtonCorrection hΦ)
  have hprojCircle : (fun θ : AddCircle P => wproj θ) =ᵐ[AddCircle.haarAddCircle]
      fun θ => circleSlice hproj θ := by
    change (fun θ : AddCircle P => testElem P (conjExp q0E)
      (lerayProjectedPhaseTest hr1 hrtop hs) θ) =ᵐ[AddCircle.haarAddCircle]
      fun θ => circleSlice hproj θ
    rw [testElem_of hproj]
    exact ContinuousMap.coeFn_toLp (E := Lp CVec3 (conjExp q0E) volume)
      (p := conjExp q0E) (𝕜 := ℂ) AddCircle.haarAddCircle (circleSlice hproj)
  have hprojTime := UnforcedLeray.PhaseTrace.ae_comp_mk hprojCircle
  have hslice : ∀ᵐ τ : ℝ ∂volume, (fun y : Space => rep wproj τ y) =ᵐ[volume]
      fun y => lerayProjectedPhaseTest
      hr1 hrtop hs (τ, y) := by
    filter_upwards [hprojTime] with τ hτ
    have hr := rep_slice wproj τ
    have ht := MemLp.coeFn_toLp (hproj.2.memLp τ)
    have hte : (wproj (τ : AddCircle P) : Lp CVec3 (conjExp q0E) volume) =
        circleSlice hproj (τ : AddCircle P) := hτ
    filter_upwards [hr, ht] with y hyR hyT
    have hcoerce : ((wproj (τ : AddCircle P) : Lp CVec3 (conjExp q0E) volume) :
        Space → CVec3) y = (circleSlice hproj (τ : AddCircle P) : Space → CVec3) y :=
      congrArg (fun f : Lp CVec3 (conjExp q0E) volume => (f : Space → CVec3) y) hte
    rw [hyR, hcoerce, circleSlice_coe hproj τ]
    exact (by simpa only [sliceMap] using hyT)
  have hdecomp : ∀ᵐ τ : ℝ ∂volume, (fun y : Space => rep wproj τ y) =ᵐ[volume]
      fun y => G (τ, y) := by
    filter_upwards [hslice] with τ hsliceτ
    have hprojτ := lerayProjectedPhaseTest_eq_newtonPotentialGrad_ae hr1 hrtop hΦ τ
    filter_upwards [hsliceτ, hprojτ] with y hy1 hy2
    rw [hy1, hy2]
    simp only [G, projectedNewtonCorrection, projectedPotentialRePath,
      projectedPotentialImPath]
    abel
  have haeEq : (fun z : SpaceTime => rep wproj z.1 z.2) =ᵐ[μ] G := by
    have hglobal := (UnforcedLeray.FreeStress.ae_eq_prod_iff
      (stronglyMeasurable_rep wproj).aestronglyMeasurable
      hGcont.aestronglyMeasurable).2 hdecomp
    have hprod : (fun z : SpaceTime => rep wproj z.1 z.2) =ᵐ[volume] G := by
      simpa only [Measure.volume_eq_prod] using hglobal
    exact ae_restrict_of_ae hprod
  have hGmem : MemLp G (conjExp q0E) μ := hrep.ae_eq haeEq
  have hdiff : MemLp (fun z : SpaceTime => G z - Φ z) (conjExp q0E) μ := hGmem.sub hPhiMem
  have hdiffEq : (fun z : SpaceTime => G z - Φ z) = projectedNewtonCorrection Φ := by
    funext z
    simp [G]
  exact hdiff.ae_eq (ae_of_all _ (fun z => congrFun hdiffEq z))

#print axioms memLp_projectedNewtonCorrection_cell

end UnforcedLeray.Cons.C03.Concrete

end
