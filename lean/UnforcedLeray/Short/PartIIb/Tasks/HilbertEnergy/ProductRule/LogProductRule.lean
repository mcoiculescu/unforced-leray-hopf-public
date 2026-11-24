import UnforcedLeray.Short.PartIIb.Sub.T15_2
import UnforcedLeray.Short.PartIIb.Tasks.HilbertEnergy.ProductRule.LogProductRuleScalar
import UnforcedLeray.Short.PartIIb.Tasks.HilbertEnergy.ProductRule.LogTestBounds
import UnforcedLeray.Short.PartIIb.Tasks.HilbertEnergy.ProductRule.LogCrossLimit

/-!
# Part II-b, task `PartII-b:T15/2/14`: the vector weak product rule in the logarithmic chart

Source of record: `the November 2 reference manuscript`, lines 1975-1979. The target
is the Prop `LogProductRule` (`Sub/T15_2.lean`, leaf `PartII-b:T15/2/14`), proved unchanged.

Proof outline. Apply `logProductRuleScalar` to each component `i : Fin 2`, and add.
The integrands `g_i \overline{ψ u_i}`, `ψ ‖u_i‖²` and `∂_tψ ‖u_i‖²` are integrable
(`logCL_holder` for the first, `Integrable.bdd_mul` for the others), so `integral_finset_sum`
and `Complex.re_sum` apply.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- **Task `PartII-b:T15/2/14`**: the vector weak product rule in the logarithmic chart. -/
theorem logProductRule : UnforcedLeray.Short.IIb.LogProductRule := by
  intro c u g hc hu hg hweak ψ hψ
  obtain ⟨C, hC⟩ := (logTestBounds c ψ hc hψ).1
  obtain ⟨D, hD⟩ := (logTestBounds c ψ hc hψ).2.1
  have hψc : Continuous ψ := hψ.smooth.continuous
  have hψm : AEStronglyMeasurable ψ (logMeas c) := hψc.aestronglyMeasurable
  have hDm : AEStronglyMeasurable (cpd 0 ψ) (logMeas c) :=
    (logTestBounds_cpd_continuous hψ.smooth).aestronglyMeasurable
  have hsq : ∀ i : Fin 2, Integrable (fun x : Coord => ‖u x i‖ ^ 2) (logMeas c) :=
    fun i => (memLp_two_iff_integrable_sq_norm (hu i).1).mp (hu i)
  have hψsq : ∀ i : Fin 2, Integrable (fun x : Coord => ψ x * ‖u x i‖ ^ 2) (logMeas c) :=
    fun i => (hsq i).bdd_mul hψm (ae_of_all _ fun x => by
      show ‖ψ x‖ ≤ C
      rw [Real.norm_eq_abs]
      exact hC x)
  have hDsq : ∀ i : Fin 2, Integrable (fun x : Coord => cpd 0 ψ x * ‖u x i‖ ^ 2) (logMeas c) :=
    fun i => (hsq i).bdd_mul hDm (ae_of_all _ fun x => by
      show ‖cpd 0 ψ x‖ ≤ D
      rw [Real.norm_eq_abs]
      exact hD x)
  have hcross : ∀ i : Fin 2, Integrable
      (fun x : Coord => g x i * (starRingEnd ℂ) ((ψ x : ℂ) * u x i)) (logMeas c) := by
    intro i
    refine (logCL_holder (logMeas c) (fun x : Coord => g x i)
      (fun x : Coord => (starRingEnd ℂ) (u x i)) ψ C (hg i) (hu i).star hψc hC).1.congr
      (ae_of_all _ fun x => ?_)
    show g x i * (starRingEnd ℂ) (u x i) * (ψ x : ℂ) =
      g x i * (starRingEnd ℂ) ((ψ x : ℂ) * u x i)
    rw [map_mul, Complex.conj_ofReal]
    ring
  have hL : ∫ x, ∑ i : Fin 2, g x i * (starRingEnd ℂ) ((ψ x : ℂ) * u x i) ∂(logMeas c) =
      ∑ i : Fin 2, ∫ x, g x i * (starRingEnd ℂ) ((ψ x : ℂ) * u x i) ∂(logMeas c) :=
    integral_finset_sum _ (fun i _ => hcross i)
  have hR : ∫ x, ψ x * ∑ i : Fin 2, ‖u x i‖ ^ 2 ∂(logMeas c) =
      ∑ i : Fin 2, ∫ x, ψ x * ‖u x i‖ ^ 2 ∂(logMeas c) := by
    simp_rw [Finset.mul_sum]
    exact integral_finset_sum _ (fun i _ => hψsq i)
  have hT : ∫ x, cpd 0 ψ x * ∑ i : Fin 2, ‖u x i‖ ^ 2 ∂(logMeas c) =
      ∑ i : Fin 2, ∫ x, cpd 0 ψ x * ‖u x i‖ ^ 2 ∂(logMeas c) := by
    simp_rw [Finset.mul_sum]
    exact integral_finset_sum _ (fun i _ => hDsq i)
  rw [hL, hR, hT, Complex.re_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact logProductRuleScalar c (fun x => u x i) (fun x => g x i) hc (hu i) (hg i) (hweak i) ψ hψ

end UnforcedLeray.Short.IIb
