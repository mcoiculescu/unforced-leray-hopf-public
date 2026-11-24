import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_2_KerPDE.E

/-!
# `kdGapSmooth` (`PartIII-b:C/rep/2/6/3/3/4`, source 3603-3626, 3800-3807, 4171-4200, 5223)

For `h > 0`, `y ↦ kerF (Kd) (h,z) y` is `C²`: `Kd = Gker μ - Gker (μ+1)` and each `Gker` is `C²`
in `y` (`gker_contDiff`), with the constant `T`-factors.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **(L4)** smoothness of `y ↦ kerF (Kd) (h,z) y` for `h > 0`. -/
theorem kdGapSmooth : KdGapSmooth := by
  intro ν μ hν T τ i p hp
  have hk : kerF T τ i (Kd ν μ) p = fun y => ∑ j : Fin 3, ∑ k : Fin 3,
      Kd ν μ p.1 y p.2 i j k * ((T (τ - p.1) p.2 j k : ℝ) : ℂ) := rfl
  have hK : ∀ j k : Fin 3, ContDiff ℝ 2 (fun y => Kd ν μ p.1 y p.2 i j k) := fun j k =>
    (gker_contDiff ν (μ : ℂ) hν p.1 hp p.2 i j k).sub
      (gker_contDiff ν ((μ : ℂ) + 1) hν p.1 hp p.2 i j k)
  rw [hk]
  exact ContDiff.sum fun j _ => ContDiff.sum fun k _ => (hK j k).mul contDiff_const

end UnforcedLeray.Short.PartIIIb.Concrete
