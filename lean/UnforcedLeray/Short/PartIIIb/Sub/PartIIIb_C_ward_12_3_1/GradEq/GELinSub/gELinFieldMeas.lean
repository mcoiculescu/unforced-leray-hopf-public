import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.Props
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.gELinConvTPhaseTest
import UnforcedLeray.Cons.L2.BackgroundConcrete.Operators

/-!
# `GELinFieldMeas`: strong measurability of the linear-term field (source 2525-2533)

Task `PartIII-b:C/ward/12/3/1/2/6/8`.  Each component of `GELinField` is a finite sum of products of
continuous complex functions (`rawD`, `rawDD`, `raw`, obtained from the joint smoothness of `raw`
by `gELinConvT_partial`) and of the jointly strongly measurable representatives `rep`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set
open scoped ContDiff
open UnforcedLeray.Cons.C03.Concrete (rep stronglyMeasurable_rep)

theorem gELinFieldMeas : GELinFieldMeas := by
  intro p z g h j hp
  have hC : ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => p.raw x.1 x.2) := hp.1
  have hrD : ∀ k : Fin 3, ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => rawD p k x) :=
    fun k => gELinConvT_partial hC k
  have hrDD : ∀ a b : Fin 3, ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => rawDD p a b x) :=
    fun a b => gELinConvT_partial (hrD b) a
  have hcomp : ∀ {F : ℝ × UnforcedLeray.Space → UnforcedLeray.Space}, ContDiff ℝ ∞ F →
      ∀ i : Fin 3, Measurable (fun x : ℝ × UnforcedLeray.Space => ((F x i : ℝ) : ℂ)) := by
    intro F hF i
    exact (Complex.continuous_ofReal.comp ((contDiff_piLp 2).1 hF i).continuous).measurable
  have hrep : ∀ (w : Yq p.period UnforcedLeray.B0412.q0E) (k : Fin 3),
      Measurable (fun x : ℝ × UnforcedLeray.Space => rep w x.1 x.2 k) := by
    intro w k
    exact ((EuclideanSpace.proj k : UnforcedLeray.PhaseSpace.CVec3 →L[ℂ] ℂ).continuous.comp_stronglyMeasurable
      (stronglyMeasurable_rep w)).measurable
  have htl : Measurable (WithLp.toLp 2 : (Fin 3 → ℂ) → UnforcedLeray.PhaseSpace.CVec3) :=
    (MeasurableEquiv.toLp 2 (Fin 3 → ℂ)).measurable
  apply stronglyMeasurable_iff_measurable.2
  unfold GELinField
  apply htl.comp
  apply measurable_pi_iff.2
  intro i
  apply Measurable.neg
  apply Measurable.add
  · apply Measurable.add
    · exact Finset.measurable_sum _ (fun k _ => (hcomp (hrD k) i).mul (hrep (g j) k))
    · exact Finset.measurable_sum _ (fun m _ =>
        ((hcomp (hrD m) m).mul (hrep (g j) i)).add ((hcomp hC m).mul (hrep (h j m) i)))
  · apply Measurable.add
    · exact Finset.measurable_sum _ (fun k _ => (hcomp (hrDD k j) i).mul (hrep (p.wOf z) k))
    · exact Finset.measurable_sum _ (fun m _ =>
        ((hcomp (hrDD m j) m).mul (hrep (p.wOf z) i)).add ((hcomp (hrD j) m).mul (hrep (g m) i)))

end UnforcedLeray.Short.PartIIIb.Concrete
