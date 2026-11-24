import UnforcedLeray.Short.Spine.Params
import UnforcedLeray.Short.Spine.PartII
import UnforcedLeray.Short.Interface.Statements

/-!
# Part III output: the energy-class Floquet mode on the exact background

Source: `the November 2 reference manuscript`, Part III (lines 2647-5988),
in particular `closure:mixed-return` (lines 5717-5775), the parameter budget (lines 5835-5920)
and the phase selection and scalar crossing (lines 5922-5985).

`PartIIIOutput`: for every reference choice `R = (planar data, σ₀)` there is a threshold `m₀`
(`m_0` of line 5870: `m_0 < min{ϑ d₀/16, γ/1000}`, with `d₀ = γ/3`; it does not depend on the
background) such that for every loss exponent `m ≤ m₀`, every slow age `Σ > 0` of the fixed inlet
and every polynomial `P_ν = Cν^{-N}` (the internal choices of the background construction, fixed
after `m₀`: "The background construction realizes this `m₀`; all its internal choices are then
fixed", lines 5856-5857), and for every sequence of backgrounds, one per level ("Construct the
background once at these parameters", lines 5951-5952), that are exact backgrounds of Part II
(`IsShortBackground`, `Short/Spine/Background.lean`) at the parameters
`(ν_n, ε_n, c_n = ν_n^{-2}, P_n = 2ε_nc_n)` for all large `n`, the background of every large level
carries a real `P_n`-periodic solenoidal energy mode `b_* ∈ 𝒴_{2,div}`, `∇b_* ∈ 𝒴₂`, nonzero,
axisymmetric without swirl, solving `loc:eq:mode` in `𝒟'(ℝ³ × ℝ/𝒯ℤ)` with some `σ ∈ (0,1/4)`
(line 5977: "`σ_n = μ_n(z_n) ∈ (0,1/4)`"; lines 5979-5987). The conclusion is the Interface area's
`Short.Interface.IsEnergyMode` (`Short/Interface/Statements.lean`: `0 < σ < 1/4`, `IsH1Periodic`,
nonzero, the equation against periodic tests, symmetry) on the background core
`(h, 𝒯, u_dss, U_*, r_heat) = (ν_n, P_n, a, U, Q)`, so that the composed claim is the Interface
area's `ConstructionClaimShort`. (`Spine/Objects.lean` also contains an earlier, non-periodic-test
version `Spine.IsEnergyMode`; it is not used by the composition.)
The background and geometry are held fixed while `σ` varies (lines 5953-5954), so the background
of a level is given before the choice of `σ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace UnforcedLeray.Short.Spine

open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Blueprint.Planar
open UnforcedLeray.Cons.Data

/-- **Part III output**, for sequences of backgrounds, one per level (lines 5835-5987). -/
def PartIIIOutput : Prop :=
  ∀ R : Reference, R.IsReferenceChoice →
    ∃ m₀ : ℝ, 0 < m₀ ∧ ∀ m : ℝ, 0 < m → m ≤ m₀ → ∀ (Sig C : ℝ) (N : ℕ), 0 < Sig →
      ∀ B : ℕ → ShortBackground,
        (∀ᶠ n : ℕ in atTop,
          IsShortBackground R.planar (nuSeq R n) (epsSeq R n) m C N Sig (B n)) →
        ∀ᶠ n : ℕ in atTop, ∃ M : Interface.EnergyModeCore,
          Interface.IsEnergyMode
            ⟨nuSeq R n, shortPeriod (nuSeq R n) (epsSeq R n), (B n).a, (B n).U, (B n).Q⟩ M

end UnforcedLeray.Short.Spine
