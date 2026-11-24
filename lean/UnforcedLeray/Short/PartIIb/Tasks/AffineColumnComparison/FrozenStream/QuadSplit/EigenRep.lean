import UnforcedLeray.Short.PartIIb.Sub.G4_2_2_1

/-!
# Part II-b, task `PartII-b:G4/2/2/1/3`: `EigenRep`

Source of record: `the November 2 reference manuscript`, lines 2349-2352.

Route: `generatorL0 q r = λ q r` unfolds to `(λ + 2iΩ) q r = 2ik R q r`; the denominator has real
part `Re λ > 0`, hence is nonzero, and `q r = aCoef λ r * R q r`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Blueprint

theorem eigenRep : UnforcedLeray.Short.IIb.EigenRep := by
  intro lam q hq r hr
  have hE := hq.eigen r hr
  unfold Planar.generatorL0 at hE
  have hden : lam + 2 * Complex.I * (Planar.vortexOmega r : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith [hq.re_pos]
  unfold aCoef
  rw [div_mul_eq_mul_div, eq_div_iff hden]
  linear_combination (-1 : ℂ) * hE

end UnforcedLeray.Short.IIb
