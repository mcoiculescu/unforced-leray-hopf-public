import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2

/-!
# `SepWDivDerivFormula` (`PartIII-b:IIIb-D2/3/1/2/2`)

Source `the November 2 reference manuscript` 3600-3621.
The statement is isolated here so that the proof file and `../L2.lean` can both import it.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Shared derivative-under-integral formula for `∑_i ∂_{y_i} sepW_i` (D2/3/1/1/2): for
`rOut < ϱ y`, the divergence of `sepW` is the integral of the contracted second derivatives of
`K`, with the component sum taken inside the integrals. -/
def SepWDivDerivFormula : Prop :=
  ∀ (ν : ℝ) (μ : ℂ) (rOut P : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ),
    0 < ν → -(1 / 4) < μ.re → 0 ≤ rOut → 0 < P → IIIa.IsSepSource P rOut T → SepMoment P T →
    ∀ (τ : ℝ) (y : Space), rOut < ϱ y →
      ∑ i : Fin 3, fderiv ℝ (fun y' => IIIa.sepW ν μ T y' τ i) y (coordinateVector i) =
        -2 * ∫ l in Ioo (0 : ℝ) 1, (l : ℂ) ^ (2 * μ + 2) *
          ∫ z : Space, ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
            ((fderiv ℝ (fun x => fderiv ℝ (fun x' => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x') x
                (coordinateVector k)) (y - l • z) (coordinateVector i) : ℝ) : ℂ) *
              ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ)

end UnforcedLeray.Short.PartIIIb.Concrete
