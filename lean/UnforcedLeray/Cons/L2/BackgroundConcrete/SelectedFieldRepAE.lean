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

/-- The actual jointly measurable representative of a real graph element is real almost
 everywhere in phase and space. The drift trace supplies continuous representatives at every
 phase; the conclusion itself is only the product-a.e. identity needed by the selected field. -/
theorem rep_real_ae_of_realSub_and_drift
    (w b : Yq P q) (hqtop : q ≠ ⊤)
    (hTime : HasPhaseOp driftT w b)
    (hw : w ∈ realSub P q) :
    (fun z : ℝ × Space => rep w z.1 z.2) =ᵐ[(volume : Measure ℝ).prod (volume : Measure Space)]
      fun z => ofReV (reV (rep w z.1 z.2)) := by
  have hfix := realPhaseProjection_eq_of_realSub w hw
  have houter : (fun τ : AddCircle P => w τ) =ᵐ[AddCircle.haarAddCircle]
      fun τ => realPhaseProjection w τ := by
    exact Filter.Eventually.of_forall fun τ => congrArg (fun f : Yq P q => f τ) hfix
  have hphase : (fun τ : AddCircle P => realSliceProjection (w τ)) =ᵐ[AddCircle.haarAddCircle]
      fun τ => w τ := by
    exact (realPhaseProjection_coe_ae w).symm.trans houter.symm
  let tr := phaseRepC (q := q) hqtop hTime
  have htrace : (w : AddCircle P → Lp CVec3 q volume) =ᵐ[AddCircle.haarAddCircle] tr :=
    phaseRepC_ae hqtop hTime
  have hrealTrace : (fun τ : AddCircle P => realSliceProjection (tr τ)) =ᵐ[
      AddCircle.haarAddCircle] fun τ => tr τ := by
    filter_upwards [hphase, htrace] with τ hτ hτtr
    calc
      realSliceProjection (tr τ) = realSliceProjection (w τ) := by rw [hτtr]
      _ = w τ := hτ
      _ = tr τ := hτtr
  have hcontLeft : Continuous (fun τ : AddCircle P => realSliceProjection (tr τ)) :=
    (realSliceProjection (q := q)).continuous.comp tr.continuous
  have hrealTraceAll : ∀ τ : AddCircle P, realSliceProjection (tr τ) = tr τ := by
    have heq := (hcontLeft.ae_eq_iff_eq (μ := AddCircle.haarAddCircle)
      tr.continuous).mp hrealTrace
    intro τ
    exact congrFun heq τ
  have hrealTraceSlice (τ : AddCircle P) :
      (fun y => ofReV (reV ((tr τ : Space → CVec3) y))) =ᵐ[volume]
        (tr τ : Space → CVec3) := by
    have hfixFn : (realSliceProjection (tr τ) : Space → CVec3) =
        (tr τ : Space → CVec3) :=
      congrArg (fun f : Lp CVec3 q volume => (f : Space → CVec3)) (hrealTraceAll τ)
    filter_upwards [realSliceProjection_coe_ae (tr τ)] with y hproj
    exact hproj.symm.trans (congrFun hfixFn y)
  have hline := phaseRep_ae_line hqtop hTime
  have hslice : ∀ᵐ τ : ℝ ∂volume,
      (fun y => rep w τ y) =ᵐ[volume] fun y => ofReV (reV (rep w τ y)) := by
    filter_upwards [hline] with τ hτ
    have hrepTrace : (fun y => rep w τ y) =ᵐ[volume]
        fun y => tr (τ : AddCircle P) y := by
      have hrep := rep_slice w τ
      have hlineFun : (fun y => (phaseRep hqtop hTime τ : Space → CVec3) y) =ᵐ[volume]
          fun y => (w (τ : AddCircle P) : Space → CVec3) y := Lp.ext_iff.mp hτ
      have htrFun : (fun y => (tr (τ : AddCircle P) : Space → CVec3) y) =ᵐ[volume]
          fun y => (phaseRep hqtop hTime τ : Space → CVec3) y := by
        exact Lp.ext_iff.mp (phaseRepC_coe hqtop hTime τ).symm
      exact hrep.trans (hlineFun.symm.trans htrFun)
    filter_upwards [hrepTrace, hrealTraceSlice (τ : AddCircle P)] with y hrep hreal
    calc
      rep w τ y = tr (τ : AddCircle P) y := hrep
      _ = ofReV (reV (tr (τ : AddCircle P) y)) := hreal.symm
      _ = ofReV (reV (rep w τ y)) := by rw [hrep.symm]
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
  have hprod : ∀ᵐ z ∂(volume : Measure ℝ).prod (volume : Measure Space), F z = G z :=
    (Measure.ae_prod_iff_ae_ae hset).2 hslice
  exact hprod

#print axioms rep_real_ae_of_realSub_and_drift

end UnforcedLeray.Cons.C03.Concrete
