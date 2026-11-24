import UnforcedLeray.Cons.L2.BackgroundConcrete.RepresentativeLp
import UnforcedLeray.Cons.L2.BackgroundConcrete.ProjectedTest

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0412

/-- A jointly measurable actual field that agrees phasewise almost everywhere with a genuine
`IsSliceTest` belongs to that test's exponent on one period cell. The proof uses the selected
joint representative of `testElem`, not independently chosen spatial representatives. -/
theorem memLp_of_ae_sliceTest_on_periodCell
    {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)] (hqtop : q ≠ ⊤)
    {F G : SpaceTime → CVec3} (hF : StronglyMeasurable F)
    (hG : IsSliceTest P q G)
    (hFG : ∀ᵐ τ : ℝ ∂volume, (fun y : Space => F (τ, y)) =ᵐ[volume]
      fun y => G (τ, y)) :
    MemLp F q (volume.restrict (Ioc (0 : ℝ) P ×ˢ (univ : Set Space))) := by
  let w : Yq P q := testElem P q G
  have hrep : MemLp (fun z : SpaceTime => rep w z.1 z.2) q
      (volume.restrict (Ioc (0 : ℝ) P ×ˢ (univ : Set Space))) :=
    memLp_rep_periodCell hqtop w
  have hcircle : (fun θ : AddCircle P => w θ) =ᵐ[AddCircle.haarAddCircle]
      fun θ => circleSlice hG θ := by
    change (fun θ : AddCircle P => testElem P q G θ) =ᵐ[AddCircle.haarAddCircle]
      fun θ => circleSlice hG θ
    rw [testElem_of hG]
    exact ContinuousMap.coeFn_toLp (E := Lp CVec3 q volume) (p := q) (𝕜 := ℂ)
      (AddCircle.haarAddCircle (T := P)) (circleSlice hG)
  have htime := UnforcedLeray.PhaseTrace.ae_comp_mk hcircle
  have hrepSlice : ∀ᵐ τ : ℝ ∂volume,
      (fun y : Space => rep w τ y) =ᵐ[volume] fun y => G (τ, y) := by
    filter_upwards [htime] with τ hτ
    have hr := rep_slice w τ
    have ht := MemLp.coeFn_toLp (hG.2.memLp τ)
    have hte : (w (τ : AddCircle P) : Lp CVec3 q volume) =
        circleSlice hG (τ : AddCircle P) := hτ
    filter_upwards [hr, ht] with y hrepY htestY
    have hcoerce : ((w (τ : AddCircle P) : Lp CVec3 q volume) : Space → CVec3) y =
        (circleSlice hG (τ : AddCircle P) : Space → CVec3) y :=
      congrArg (fun f : Lp CVec3 q volume => (f : Space → CVec3) y) hte
    rw [hrepY, hcoerce, circleSlice_coe hG τ]
    exact (by simpa only [sliceMap] using htestY)
  have hrepF : ∀ᵐ τ : ℝ ∂volume,
      (fun y : Space => rep w τ y) =ᵐ[volume] fun y => F (τ, y) := by
    filter_upwards [hrepSlice, hFG] with τ h1 h2
    exact h1.trans h2.symm
  have hset : MeasurableSet {z : SpaceTime |
      rep w z.1 z.2 = F z} :=
    measurableSet_eq_fun (stronglyMeasurable_rep w).measurable hF.measurable
  have hglobal : (fun z : SpaceTime => rep w z.1 z.2) =ᵐ[
      (volume : Measure ℝ).prod (volume : Measure Space)] F := by
    exact (Measure.ae_prod_iff_ae_ae hset).2 hrepF
  have hprod : (fun z : SpaceTime => rep w z.1 z.2) =ᵐ[volume] F := by
    simpa only [Measure.volume_eq_prod] using hglobal
  exact hrep.ae_eq (ae_restrict_of_ae hprod)

#print axioms memLp_of_ae_sliceTest_on_periodCell

end UnforcedLeray.Cons.C03.Concrete

end
