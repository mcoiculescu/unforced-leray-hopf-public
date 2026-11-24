import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T17

/-!
# The far-field oscillation leaf (helper for `GeomX.PhasePrimitive`)

Source `the November 2 reference manuscript`
lines 5400-5427 (separated kernels; "the gradient Newton kernel has degree `-5`, and the ratio of
the old source radius to the young receiver radius is at most `1/√1.2 < 1`"; one phase primitive
in the dilation variable with its dilation-one boundary term retained), SP 3768-3790 (`IIIa`
`sep:mean-comparison`, oscillatory part).

## Why a far-field form is needed

`PhasePrimitiveAt` asks for `P_ν ε⁴ s^{5/2} N` at **every** young chart point `0 < s ≤ 1/ν`,
i.e. at receivers `|x_obs'| = s^{-1/2} ∈ [√ν, ∞)`.  The factor `s^{5/2} = |x_obs'|^{-5}` is the
degree `-5` of the gradient kernel `D∇K`.  The `IIIa` leaves `SepOscPart` / `SepMeanPart` give the
constant `C(1 + ν⁻¹ + c + ρ_i + ρ_o + (ρ_i - ρ_o)⁻¹)^k ε⁴ N₁`, which does **not** decay as the
receiver goes out (it is non-decreasing in `ρ_i`), and the dilation `x ↦ λx` that moves the
receiver to unit distance replaces `ν` by `ν/λ² = νs`, so `(νs)^{-k}` destroys the gain.  Hence
the leaf below is the decay form of `SepSplit` + `SepOscPart`: the same oscillation estimate with
the factor `|x_obs'|^{-5}`, the polynomial now in `ν⁻¹, c, ρ_i⁻¹` and the gap ratio
`ρ_i/(ρ_i - ρ_o)` (scale invariant).  The majorant is asked to be periodic (it is, being built
from the periodic source), so it controls every phase window.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short.IIIa

/-- **Far-field oscillation estimate** (source 5400-5427; SP 3768-3790 with the degree `-5` of
`D∇K` kept): for a measurable, `c`-periodic thin source `F(x',Y,q)` supported in `|x'| ≤ ρ_o`, with
finite first transverse moment, at every receiver `|x_obs'| ≥ ρ_i > ρ_o`, the oscillating part
`∇_yW_μ(F) - ∇_yW_μ(F̄)` (`F̄` the phase mean) at `y = ε⁻¹x_obs` has a measurable periodic phase
majorant `B` with
`‖B‖_{L²_τ} ≤ C(1 + ν⁻¹ + c + ρ_i⁻¹ + ρ_i/(ρ_i - ρ_o))^k ε⁴ |x_obs'|^{-5} N₁(F)`. -/
def SepOscFar : Prop :=
  ∀ K : Set ℂ, IsCompact K → (∀ μ ∈ K, -(1 / 4) < μ.re) → ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧
    ∀ ν c ε ρo ρi : ℝ, 0 < ν → ν ≤ 1 → 0 < c → 0 < ε → ε ≤ 1 → 0 ≤ ρo → ρo < ρi → ∀ μ ∈ K,
      ∀ F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ,
        (∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ × ℝ => F w.1 w.2.1 w.2.2 i j) →
        (∀ x' Y q, F x' Y (q + c) = F x' Y q) →
        (∀ x' Y q, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → F x' Y q = 0) →
        thinMoment c F ≠ ⊤ →
        ∀ xo : Space, ρi ≤ Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) →
          ∃ B : ℝ → ℝ≥0∞, Measurable B ∧ Function.Periodic B (2 * ε * c) ∧
            (∀ᵐ τ ∂(volume : Measure ℝ),
              ‖fderiv ℝ (fun y => sepW ν μ (thinSource ε F) y τ) (ε⁻¹ • xo) -
                fderiv ℝ (fun y => sepW ν μ (thinSource ε (meanLift (phaseMean c F))) y τ)
                  (ε⁻¹ • xo)‖ₑ ≤ B τ) ∧
            ltauAt (2 * ε * c) B ≤
              ENNReal.ofReal (C * (1 + ν⁻¹ + c + ρi⁻¹ + ρi * (ρi - ρo)⁻¹) ^ k * ε ^ 4 *
                Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) ^ (-5 : ℝ)) * thinMoment c F

end UnforcedLeray.Short.PartIIIb.Concrete
