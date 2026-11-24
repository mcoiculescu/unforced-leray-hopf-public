import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.TransTable.Props
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.MultStep.PointMass
import UnforcedLeray.Short.PartIIIa.Tasks16.DomPointwise
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_1.SepDomFacts
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Core lemmas for `transMajPointL2` (source 3647, 4181-4192, 5337-5341)
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace PL2

/-- Minkowski in a parameter over a measurable set, for the normalised phase norm. -/
theorem ltauAt_lintegral_set_le (P : ℝ) (hP : 0 < P) (S : Set ℝ) (F : ℝ → ℝ → ℝ≥0∞)
    (hF : Measurable (Function.uncurry F)) :
    IIIa.ltauAt P (fun τ => ∫⁻ l in S, F l τ) ≤ ∫⁻ l in S, IIIa.ltauAt P (F l) := by
  have hc : ((ENNReal.ofReal P)⁻¹) ^ (1 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hP).ne')
  have hF' : AEMeasurable (Function.uncurry fun (τ l : ℝ) => F l τ)
      ((volume.restrict (Ioc 0 P)).prod (volume.restrict S)) := by
    refine Measurable.aemeasurable ?_
    exact hF.comp measurable_swap
  have hM := UnforcedLeray.PlanarBS.Conv.lintegral_lintegral_rpow_le
    (μ := volume.restrict (Ioc 0 P)) (ν := volume.restrict S) hF' (p := 2) (by norm_num)
  unfold IIIa.ltauAt
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  calc ((ENNReal.ofReal P)⁻¹) ^ (1 / 2 : ℝ) *
        (∫⁻ τ in Ioc 0 P, (∫⁻ l in S, F l τ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
      ≤ ((ENNReal.ofReal P)⁻¹) ^ (1 / 2 : ℝ) *
        ∫⁻ l in S, (∫⁻ τ in Ioc 0 P, F l τ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        gcongr
    _ = _ := by
        rw [← lintegral_const_mul' _ _ hc]
        refine lintegral_congr fun l => ?_
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]

theorem lintegral_Ioi_rpow (r : ℝ) (hr : 0 < r) :
    ∫⁻ ρ in Ioi r, ENNReal.ofReal (ρ ^ (-(57 / 22) : ℝ)) =
      ENNReal.ofReal (22 / 35 * r ^ (-(35 / 22) : ℝ)) := by
  have hi : IntegrableOn (fun x : ℝ => x ^ (-(57 / 22) : ℝ)) (Ioi r) volume :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hr
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx =>
      Real.rpow_nonneg (hr.le.trans (le_of_lt hx)) _)]
  rw [integral_Ioi_rpow_of_lt (by norm_num) hr]
  congr 1
  have : (-(57 / 22) : ℝ) + 1 = -(35 / 22) := by norm_num
  rw [this]
  ring

/-- Measurability of the half-line embedding. -/
theorem measurable_halfline (z : ℝ) : Measurable (fun ρ : ℝ => (!₂[ρ, 0, z] : Space)) := by
  have : Continuous (fun ρ : ℝ => (!₂[ρ, 0, z] : Space)) := by
    refine (PiLp.continuous_toLp 2 _).comp ?_
    refine continuous_pi fun i => ?_
    fin_cases i <;> simp <;> fun_prop
  exact this.measurable

end PL2

end UnforcedLeray.Short.PartIIIb.Concrete

end
