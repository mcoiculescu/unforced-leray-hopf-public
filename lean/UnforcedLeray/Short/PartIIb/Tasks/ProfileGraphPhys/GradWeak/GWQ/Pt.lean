import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.GWQ.Calc5

/-!
# `PartII-b:T10/7/1/2/4` (`GWQ`) helper: pointwise form of the right-hand pairing
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.GWQ

open UnforcedLeray UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

theorem tst_eq (c ε a : ℝ) (φ : Coord → ℝ) (i : Fin 2) (j : Fin 3) (x : ℝ × Space) :
    tst c ε a φ i j x = (((Axi.eR x.2 j * ctLift c ε a φ x : ℝ) : ℂ)) • frameC i x.2 := by
  simp only [tst, frameC_eq]
  rw [Complex.coe_smul]

theorem rhs_pt (c ε a : ℝ) (φ : Coord → ℝ) (i : Fin 2) (g : Fin 3 → ℝ × Space → CVec3)
    (x : ℝ × Space) :
    ∑ j : Fin 3, dotL (tst c ε a φ i j x) (g j x) =
      dotL ((((ctLift c ε a φ x : ℝ)) : ℂ) • frameC i x.2)
        ((((x.2 0 / Real.sqrt (x.2 0 ^ 2 + x.2 1 ^ 2) : ℝ) : ℂ)) • g 0 x +
          (((x.2 1 / Real.sqrt (x.2 0 ^ 2 + x.2 1 ^ 2) : ℝ) : ℂ)) • g 1 x) := by
  simp only [Fin.sum_univ_three, tst_eq, Axi.eR_apply_zero, Axi.eR_apply_one, Axi.eR_apply_two]
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  have : Axi.ϱ x.2 = Real.sqrt (x.2 0 ^ 2 + x.2 1 ^ 2) := rfl
  rw [this]
  push_cast
  ring

end UnforcedLeray.Short.IIb.GWQ
