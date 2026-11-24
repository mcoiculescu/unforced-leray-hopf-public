import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_4_4_1_org_1_1_3
import UnforcedLeray.Short.PartIIIa.T16_SepYoung

/-!
# `PartIII-b:C/rep/4/4/1/org/1/1/3`: `sepWreYoungL2` (wrapper)

Source `the November 2 reference manuscript`
3631-3646 (`sep:young`), 3648-3668 (`sep:repair-energy`, `j = 0`), 4163-4166.
The analytic content is `sepWreYoungL2_of` (Sub file); its only hypothesis `IIIa.SepYoung`
is supplied by `IIIa.sepYoung` (task `PartIII-a:T16`, `Short/PartIII-a/T16_SepYoung.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem sepWreYoungL2 (a b : ℝ) (ha : -(1/4) < a) : ∃ C : ℝ, 0 ≤ C ∧ ∀ ν R P : ℝ, 0 < ν → 0 < R → 0 < P → ∀ μ ∈ Icc a b,
    ∀ T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ,
    IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T →
    IIIa.ltauLq P 2 (fun τ y => if R * Real.sqrt ν ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) then ‖sepWre ν μ T τ y‖ₑ else 0) ≤ ENNReal.ofReal (C * (R * Real.sqrt ν) ^ (-(23 / 11 : ℝ))) * IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T) :=
  sepWreYoungL2_of UnforcedLeray.Short.IIIa.sepYoung a b ha

end UnforcedLeray.Short.PartIIIb.Concrete
end
