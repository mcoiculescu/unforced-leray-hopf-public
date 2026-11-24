import UnforcedLeray.Short.PartIIa.Tasks.R01.EarlyCalculus.Products
import UnforcedLeray.Short.PartIIa.Tasks.R01.EarlyCalculus.Mul

/-!


Target: `earlyCalculus : EarlyCalculus` (`Short/PartII-a/Sub/R01.lean`, the structure with 13
closure fields). Source of record: `the November 2 reference manuscript`, lines
1294-1297 (the zero-age bounds behind the early table).

Status of this file. The twelve fields other than `mul`, and the derived fields `scaling` and
`shift`, are proved in `Tasks/R01/EarlyCalculus/Framework.lean`, `Closure.lean`, `Products.lean`.
The product field `mul` is proved in `Tasks/R01/EarlyCalculus/Mul.lean` (`earlyBdd_mul :
EarlyMulClosure`, by induction on the total order of the jets). `earlyCalculus` combines them.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0187 UnforcedLeray.B0188
  UnforcedLeray.B0190
open UnforcedLeray.Short.PartIIa.EarlyCalc

theorem earlyBdd_scaling {ρ : ℝ} {X : ProfFam} (h : EarlyBdd ρ X) :
    EarlyBdd ρ (fun ν ψ p => ageOperator (X ν ψ p)) := by
  refine earlyBdd_congr (fun ν ψ p x => ?_)
    (earlyBdd_add (earlyBdd_etaMul (earlyBdd_dEta h))
      (earlyBdd_constMul 2 (earlyBdd_ageMul (earlyBdd_dAge h))))
  simp only [Pi.add_apply, ageOperator]
  ring

theorem earlyBdd_shift {ρ a : ℝ} {X : ProfFam} (h : EarlyBdd ρ X) :
    EarlyBdd ρ (fun ν ψ p => ageShift a (X ν ψ p)) := by
  refine earlyBdd_congr (fun ν ψ p x => ?_)
    (earlyBdd_add (earlyBdd_scaling h) (earlyBdd_constMul a h))
  simp only [Pi.add_apply, ageShift]

/-- The structure `EarlyCalculus` holds once the product field is supplied. -/
theorem earlyCalculus_of_mul (hmul : EarlyMulClosure) : EarlyCalculus where
  add ρ X Y _ hX hY := earlyBdd_add hX hY
  sub ρ X Y _ hX hY := earlyBdd_sub hX hY
  neg ρ X _ hX := earlyBdd_neg hX
  mul ρ X Y h hX hY := hmul ρ X Y h hX hY
  constMul ρ r X _ hX := earlyBdd_constMul r hX
  nuMul ρ X _ hX := earlyBdd_nuMul hX
  etaMul ρ X _ hX := earlyBdd_etaMul hX
  ageMul ρ X _ hX := earlyBdd_ageMul hX
  dEta ρ X _ hX := earlyBdd_dEta hX
  dQ ρ X _ hX := earlyBdd_dQ hX
  dAge ρ X _ hX := earlyBdd_dAge hX
  scaling ρ X _ hX := earlyBdd_scaling hX
  shift ρ a X _ hX := earlyBdd_shift hX

/-- **Target `earlyCalculus`.** The structure `EarlyCalculus` of `Sub/R01.lean`, with the product
field supplied by `earlyBdd_mul` (`Tasks/R01/EarlyCalculus/Mul.lean`). -/
theorem earlyCalculus : EarlyCalculus := earlyCalculus_of_mul earlyBdd_mul

end UnforcedLeray.Short.PartIIa
