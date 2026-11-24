import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1_3_2
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg

/-!
# `cYrSub`: `Y_2` is closed under differences (source 1334-1337)

Periodicity and measurability are immediate; finiteness is Minkowski (`phaseLpNorm_add_le`)
applied to `f + (-g)`, with `phaseLpNorm (-g) = phaseLpNorm g` (`enorm_neg`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem cyR_neg (P : ℝ) (g : ℝ × Space → CVec3) :
    UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => -g x)
      = UnforcedLeray.Short.IIb.phaseLpNorm P 2 g := by
  unfold UnforcedLeray.Short.IIb.phaseLpNorm
  simp only [enorm_neg]

theorem cYrSub : CYrSub := by
  intro P hP f g hf hg
  refine ⟨?_, hf.meas.sub hg.meas, ?_⟩
  · filter_upwards [hf.periodic, hg.periodic] with x h1 h2
    simp only [h1, h2]
  · have e : (fun x => f x - g x) = fun x => f x + -g x :=
      funext fun x => sub_eq_add_neg _ _
    have h := phaseLpNorm_add_le P hP f (fun x => -g x) hf.meas hg.meas.neg
    rw [← e, cyR_neg] at h
    exact lt_of_le_of_lt h (ENNReal.add_lt_top.2 ⟨hf.finite, hg.finite⟩)

end UnforcedLeray.Short.PartIIIb.Concrete
