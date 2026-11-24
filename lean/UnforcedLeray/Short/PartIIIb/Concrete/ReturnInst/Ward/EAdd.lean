import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.YHAdd.Calc

/-!
# Additivity of the residual `Ẽ_μ` on old `L²` data (source 4271-4280)

`Ẽ_μ = 2U·∇Y - 2νC_diff + (U⊗U):D²X - (DX + DXᵀ)∇p` is a sum of four pointwise terms.  The
displacement and `Y` are additive off the axis (`WardXAdd`, `WardXDiff`, `WardYHAdd`), so `fderiv`
of `Y` and the three other terms add at `y` (`Ward/YHAdd/Calc.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- **The residual `Ẽ_μ` is additive** (`WardEAdd`, source 4271-4280) from the leaves
`WardXAdd`, `WardXDiff` and `WardYHAdd`. -/
theorem wardEAdd_of (h1 : WardXAdd) (h2 : WardXDiff) (h3 : WardYHAdd) : WardEAdd := by
  unfold WardEAdd
  intro ν μ R c χy U p hχy hν hR hc hμ g g' hg hg' τ y hy
  have hs : IsOpen axisᶜ := Axi.isOpen_compl_axis
  have hyS : y ∈ axisᶜ := hy
  have hX : ∀ t, ∀ y' ∈ axisᶜ, wardX ν μ R c χy (g + g') t y' =
      wardX ν μ R c χy g t y' + wardX ν μ R c χy g' t y' :=
    fun t y' hy' => h1 ν μ R c χy hχy hν hR hc hμ g g' hg hg' t y' hy'
  have hA := (h2 ν μ R c χy hχy hν hR hc hμ g hg τ).1
  have hB := (h2 ν μ R c χy hχy hν hR hc hμ g' hg' τ).1
  have hder1 := (h2 ν μ R c χy hχy hν hR hc hμ g hg τ).2.2
  have hder2 := (h2 ν μ R c χy hχy hν hR hc hμ g' hg' τ).2.2
  have hWA : DifferentiableAt ℝ (fun y' => wardY ν μ R c χy g τ y') y :=
    WardCalc.physDmu_differentiableAt hs hA hder1 hyS
  have hWB : DifferentiableAt ℝ (fun y' => wardY ν μ R c χy g' τ y') y :=
    WardCalc.physDmu_differentiableAt hs hB hder2 hyS
  have hW : fderiv ℝ (wardY ν μ R c χy (g + g') τ) y =
      fderiv ℝ (wardY ν μ R c χy g τ) y + fderiv ℝ (wardY ν μ R c χy g' τ) y := by
    apply WardCalc.fderiv_sum_of_eventuallyEq hWA hWB
    filter_upwards [hs.mem_nhds hyS] with y' hy'
    exact (h3 ν μ R c χy U hχy hν hR hc hμ g g' hg hg' τ y' hy').1
  unfold wardE
  rw [hW, WardCalc.physCdiff_sum_pt (U τ) hs hA hB (hX τ) hyS,
    WardCalc.physUUD2_sum_pt (U τ) hs hA hB (hX τ) hyS,
    WardCalc.physDXp_sum_pt (p τ) hs hA hB (hX τ) hyS]
  simp only [add_apply, smul_add]
  abel

end UnforcedLeray.Short.PartIIIb.Concrete
