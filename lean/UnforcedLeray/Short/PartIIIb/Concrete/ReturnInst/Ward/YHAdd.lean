import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.YHAdd.Calc

/-!
# Additivity of `Y` and `h` on old `L²` data (source 4171-4174)

Pure calculus on the open set `axisᶜ`: `WardXAdd` gives the pointwise sum of the displacements off
the axis, `WardXDiff` gives the `C³` regularity and the time differentiability that the calculus
of `Ward/YHAdd/Calc.lean` needs.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- **`Y` and `h` are additive** (`WardYHAdd`, source 4171-4174) from the displacement additivity
and regularity leaves. -/
theorem wardYHAdd_of (h1 : WardXAdd) (h2 : WardXDiff) : WardYHAdd := by
  unfold WardYHAdd
  intro ν μ R c χy U hχy hν hR hc hμ g g' hg hg' τ y hy
  have hs : IsOpen axisᶜ := Axi.isOpen_compl_axis
  have hyS : y ∈ axisᶜ := hy
  have hX : ∀ t, ∀ y' ∈ axisᶜ, wardX ν μ R c χy (g + g') t y' =
      wardX ν μ R c χy g t y' + wardX ν μ R c χy g' t y' :=
    fun t y' hy' => h1 ν μ R c χy hχy hν hR hc hμ g g' hg hg' t y' hy'
  have hA := (h2 ν μ R c χy hχy hν hR hc hμ g hg τ).1
  have hB := (h2 ν μ R c χy hχy hν hR hc hμ g' hg' τ).1
  have ht1 := (h2 ν μ R c χy hχy hν hR hc hμ g hg τ).2.1 y hy
  have ht2 := (h2 ν μ R c χy hχy hν hR hc hμ g' hg' τ).2.1 y hy
  unfold wardY wardH
  constructor
  · exact WardCalc.physDmu_sum_pt hs hA hB (fun t y' hy' => hX t y' hy') hyS ht1 ht2
  · rw [WardCalc.fderiv_sum_pt hs hA hB (hX τ) hyS, hX τ y hy]
    simp only [add_apply, map_add]
    abel

end UnforcedLeray.Short.PartIIIb.Concrete
