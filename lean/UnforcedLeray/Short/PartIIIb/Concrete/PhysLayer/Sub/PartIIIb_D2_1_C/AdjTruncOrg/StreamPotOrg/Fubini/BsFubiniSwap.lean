import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.BsPairIntegrable
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.BsFubiniSwap.Helpers
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Biot-Savart Fubini swap (BSFubiniSwap)

Source `the November 2 reference manuscript` lines 1351-1362.

For continuous compactly supported `A` and `f ∈ L²`:
`∫ A · bsSlice f = ∫ f · (∫ K(y-z) × A(y) dy)`.

Proof outline.  Joint integrability of the pairing is `BSPairIntegrable`.  For a.e. `y` the
`z`-section `z ↦ f(z) × K(y-z)` is integrable: componentwise, the bump `φ_n e_i` (equal to `1`
on `‖y‖ ≤ n+1`) gives integrable sections by `Integrable.prod_right_ae`, and countably many `n`
cover all `y`.  For such `y` the dot product commutes with the `z`-integral.  Then
`integral_integral_swap` gives the swap, and the scalar triple product identity
`a · (f × K) = f · (K × a)` (`bsTriple`) turns the integrand into the right-hand side.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace

/-- **Fubini swap for the Biot-Savart pairing.** -/
theorem bsFubiniSwap : BSFubiniSwap := by
  intro A hA hAc f hf
  obtain ⟨C, hC⟩ := bsWeightConv A hA hAc
  have hAint : ∀ z : Space, Integrable (fun y : Space => ‖A y‖ * ‖bsKernel (y - z)‖) volume :=
    fun z => (hC z).1
  have hJ : Integrable
      (fun p : Space × Space => dotL (A p.1) (crossC (f p.2) (bsKernel (p.1 - p.2))))
      ((volume : Measure Space).prod volume) :=
    bsPairIntegrable A hA hAc f hf
  -- componentwise a.e. integrability of the z-sections
  have hcomp : ∀ (n : ℕ) (i : Fin 3), ∀ᵐ y : Space, ‖y‖ ≤ (n : ℝ) + 1 →
      Integrable (fun z : Space => crossC (f z) (bsKernel (y - z)) i) volume := by
    intro n i
    have hprod : Integrable
        (fun p : Space × Space =>
          dotL (bsBasisBump n i p.1) (crossC (f p.2) (bsKernel (p.1 - p.2))))
        ((volume : Measure Space).prod volume) :=
      bsPairIntegrable (bsBasisBump n i) (bsBasisBump_continuous n i)
        (bsBasisBump_hasCompactSupport n i) f hf
    filter_upwards [hprod.prod_right_ae] with y hy hball
    refine hy.congr (Filter.Eventually.of_forall (fun z => ?_))
    simp only [bsBasisBump, bsDotL_smul_single, bsBumpN_one n hball, Complex.ofReal_one, one_mul]
  -- a.e. y: the whole z-section is integrable
  have hsec : ∀ᵐ y : Space, Integrable (fun z : Space => crossC (f z) (bsKernel (y - z))) volume := by
    have hall : ∀ᵐ y : Space, ∀ n : ℕ, ∀ i : Fin 3, ‖y‖ ≤ (n : ℝ) + 1 →
        Integrable (fun z : Space => crossC (f z) (bsKernel (y - z)) i) volume :=
      ae_all_iff.2 (fun n => ae_all_iff.2 (fun i => hcomp n i))
    filter_upwards [hall] with y hy
    obtain ⟨n, hn⟩ := exists_nat_ge ‖y‖
    have hcomp_y : ∀ i : Fin 3,
        Integrable (fun z : Space => crossC (f z) (bsKernel (y - z)) i) volume :=
      fun i => hy n i (by linarith)
    have hKz : AEStronglyMeasurable (fun z : Space => bsKernel (y - z)) volume :=
      (bsKernel_measurable.comp (measurable_id.const_sub y)).aestronglyMeasurable
    have hmeasz : AEStronglyMeasurable (fun z : Space => crossC (f z) (bsKernel (y - z))) volume :=
      crossC_continuous'.comp_aestronglyMeasurable₂ (g := fun a b : CVec3 => crossC a b)
        hf.aestronglyMeasurable hKz
    exact bsIntegrable_of_comp hmeasz hcomp_y
  -- for a.e. y, the pairing with A(y) commutes with the z-integral
  have hstep1 : ∀ᵐ y : Space,
      dotL (A y) (bsSlice f y) = ∫ z : Space, dotL (A y) (crossC (f z) (bsKernel (y - z))) := by
    filter_upwards [hsec] with y hy
    rw [bsSlice]
    exact (ContinuousLinearMap.integral_comp_comm (dotL (A y)) hy).symm
  have hswap : ∫ y : Space, ∫ z : Space, dotL (A y) (crossC (f z) (bsKernel (y - z)))
      = ∫ z : Space, ∫ y : Space, dotL (A y) (crossC (f z) (bsKernel (y - z))) :=
    integral_integral_swap hJ
  rw [integral_congr_ae hstep1, hswap]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  have h2 : ∀ y : Space, dotL (A y) (crossC (f z) (bsKernel (y - z)))
      = dotL (f z) (crossC (bsKernel (y - z)) (A y)) := fun y => bsTriple _ _ _
  simp only [h2]
  exact (ContinuousLinearMap.integral_comp_comm (dotL (f z))
    (bsKernelCross_integrable A hA hAint z))

end UnforcedLeray.Short.PartIIIb.Concrete
