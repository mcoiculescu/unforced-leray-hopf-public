import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2.L2.Defs
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2.L2.Deriv
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2.L2.PhiDeriv

/-!
# `sepWDivDerivFormula` (`PartIII-b:IIIb-D2/3/1/2/2`)

Source `the November 2 reference manuscript` 3600-3621.
The divergence of `sepW` in the gap is the iterated integral of the contracted second derivatives
of `K`: differentiate under `∫ dρ` (`sepW_hasFDerivAt`), pull the sum over `i` inside, and pass
from the product measure to the iterated integral (`integral_prod`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem sepWDivDerivFormula : SepWDivDerivFormula := by
  intro ν μ rOut P T hν hμ hr hP hS hM τ y hy
  have key := fun i : Fin 3 => sepW_hasFDerivAt ν μ rOut P T hν hμ hr hP hS hM τ i y hy
  have happ : ∀ i : Fin 3, Integrable (fun p => fderiv ℝ (sepPhi ν μ T τ i p) y
      (coordinateVector i)) sepRho := fun i =>
    ((ContinuousLinearMap.apply ℝ ℂ (coordinateVector i)).integrable_comp (key i).2)
  have h1 : ∑ i : Fin 3, fderiv ℝ (fun y' => IIIa.sepW ν μ T y' τ i) y (coordinateVector i) =
      ∫ p, ∑ i : Fin 3, fderiv ℝ (sepPhi ν μ T τ i p) y (coordinateVector i) ∂sepRho := by
    rw [integral_finset_sum _ (fun i _ => happ i)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(key i).1.fderiv, ContinuousLinearMap.integral_apply (key i).2]
  rw [h1]
  have hF : Integrable (fun p => ∑ i : Fin 3, fderiv ℝ (sepPhi ν μ T τ i p) y
      (coordinateVector i)) sepRho := integrable_finset_sum _ (fun i _ => happ i)
  unfold sepRho at hF ⊢
  rw [integral_prod _ hF, ← integral_const_mul (-2 : ℂ)]
  refine setIntegral_congr_fun measurableSet_Ioo (fun l hl => ?_)
  have hpt : ∀ z : Space, ∑ i : Fin 3, fderiv ℝ (sepPhi ν μ T τ i (l, z)) y (coordinateVector i) =
      -2 * ((l : ℂ) ^ (2 * μ + 2) * ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        ((fderiv ℝ (fun x => fderiv ℝ (fun x' => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x') x
          (coordinateVector k)) (y - l • z) (coordinateVector i) : ℝ) : ℂ) *
          ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ)) := by
    intro z
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sepPhi_fderiv_apply ν μ T τ i l z y hν hl]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul, integral_const_mul]

end UnforcedLeray.Short.PartIIIb.Concrete
