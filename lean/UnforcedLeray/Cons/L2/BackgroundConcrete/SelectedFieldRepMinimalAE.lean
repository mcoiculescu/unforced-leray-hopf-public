import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedFieldAE
import UnforcedLeray.Lib.PhaseTrace.Trace

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.PhaseSpace
open UnforcedLeray.PhaseTrace
open UnforcedLeray.RieszLp

variable {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- A real element of the nested phase space has a real selected joint representative almost
 everywhere in phase-space product measure. No evolution or continuous-representative premise is
 needed for this product-a.e. conclusion. -/
theorem rep_real_ae_of_realSub (w : Yq P q)
    (hw : w ∈ realSub P q) :
    (fun z : ℝ × Space => rep w z.1 z.2) =ᵐ[(volume : Measure ℝ).prod (volume : Measure Space)]
      fun z => ofReV (reV (rep w z.1 z.2)) := by
  have hfix := realPhaseProjection_eq_of_realSub w hw
  have houter : (fun τ : AddCircle P => w τ) =ᵐ[AddCircle.haarAddCircle]
      fun τ => realPhaseProjection w τ := by
    exact Filter.Eventually.of_forall fun τ => congrArg (fun f : Yq P q => f τ) hfix
  have hphase : (fun τ : AddCircle P => realSliceProjection (w τ)) =ᵐ[AddCircle.haarAddCircle]
      fun τ => w τ := (realPhaseProjection_coe_ae w).symm.trans houter.symm
  have hline := PhaseTrace.ae_comp_mk hphase
  have hslice : ∀ᵐ τ : ℝ ∂volume,
      (fun y => rep w τ y) =ᵐ[volume]
        fun y => ofReV (reV (rep w τ y)) := by
    filter_upwards [hline] with τ hτ
    have hfixFn : (realSliceProjection (w (τ : AddCircle P)) : Space → CVec3) =ᵐ[volume]
        (w (τ : AddCircle P) : Space → CVec3) := Lp.ext_iff.mp hτ
    filter_upwards [hfixFn, realSliceProjection_coe_ae (w (τ : AddCircle P)), rep_slice w τ]
      with y hfixy hproj hrep
    calc
      rep w τ y = (w (τ : AddCircle P) : Space → CVec3) y := hrep
      _ = (realSliceProjection (w (τ : AddCircle P)) : Space → CVec3) y :=
        hfixy.symm
      _ = ofReV (reV (w (τ : AddCircle P) y)) := hproj
      _ = ofReV (reV (rep w τ y)) := by rw [hrep]
  let F : ℝ × Space → CVec3 := fun z => rep w z.1 z.2
  let G : ℝ × Space → CVec3 := fun z => ofReV (reV (rep w z.1 z.2))
  have hF : StronglyMeasurable F := by
    change StronglyMeasurable (fun z : ℝ × Space => rep w z.1 z.2)
    exact stronglyMeasurable_rep w
  have hG : StronglyMeasurable G := by
    change StronglyMeasurable (fun z : ℝ × Space => (ofReV.comp reV) (rep w z.1 z.2))
    exact (ofReV.comp reV).continuous.comp_stronglyMeasurable hF
  have hset : MeasurableSet {z : ℝ × Space | F z = G z} :=
    measurableSet_eq_fun hF.measurable hG.measurable
  exact (Measure.ae_prod_iff_ae_ae hset).2 hslice

#print axioms rep_real_ae_of_realSub

end UnforcedLeray.Cons.C03.Concrete
