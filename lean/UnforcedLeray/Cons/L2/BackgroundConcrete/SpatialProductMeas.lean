import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProduct

/-! Joint measurability of the actual test/background scalar product. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter
open scoped ContDiff

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint
open UnforcedLeray.PhaseSpace
open UnforcedLeray.B0411
open UnforcedLeray.B0412

private theorem contDiff_realC_local : ContDiff ℝ ∞ (fun x : Space => realC x) := by
  apply (contDiff_piLp 2).2
  intro i
  have hcoord : (fun x : Space => (realC x).ofLp i) =
      fun x : Space => ((x i : ℝ) : ℂ) := by
    funext x
    exact realC_apply x i
  rw [hcoord]
  exact Complex.ofRealCLM.contDiff.comp
    (contDiff_piLp_apply (p := 2) (i := i))

/-- The actual scalar product of a smooth phase test with a jointly measurable background is
jointly a.e. strongly measurable. -/
theorem aesm_scalarTestBackground {P : ℝ} {Φ : ℝ × Space → CVec3}
    (hΦ : IsPhaseTest P Φ) {U : ℝ → SpatialField} (hU : IsBoundedBackground U) :
    AEStronglyMeasurable (fun z : SpaceTime => scalarTestBackground Φ U z) volume := by
  have hΦc : Continuous Φ := hΦ.smooth.continuous
  have hRealC : Continuous (fun x : Space => realC x) :=
    contDiff_realC_local.continuous
  have hA : Continuous (fun w : SpaceTime × Space => dotLR (Φ w.1)) := by
    exact dotLR.continuous.comp (hΦc.comp continuous_fst)
  have hG : Continuous (fun w : SpaceTime × Space => dotLR (Φ w.1) (realC w.2)) :=
    hA.clm_apply (hRealC.comp continuous_snd)
  have hmap : AEStronglyMeasurable
      (fun z : SpaceTime => (z, U z.1 z.2)) volume :=
    aestronglyMeasurable_id.prodMk hU.measurable
  have hcomp := hG.comp_aestronglyMeasurable hmap
  have heq : (fun z : SpaceTime => dotLR (Φ z) (realC (U z.1 z.2))) =
      (fun z => scalarTestBackground Φ U z) := by
    funext z
    simp [scalarTestBackground, dotLR_apply]
  exact hcomp.congr (Eventually.of_forall fun z => congrFun heq z)

#print axioms aesm_scalarTestBackground

end UnforcedLeray.Cons.C03.Concrete
