import UnforcedLeray.Short.PartIIIa.Sub.T20_4
import UnforcedLeray.Short.PartIIIa.T20_4_VelocityIsBiotSavart.TestModeFourier
import UnforcedLeray.Short.PartIIIa.T20_4_VelocityIsBiotSavart.ModeDiv
import UnforcedLeray.Short.PartIIIa.T20_4_VelocityIsBiotSavart.ModeCurl
import UnforcedLeray.Short.PartIIIa.T20_4_VelocityIsBiotSavart.SynthEmbed0
import UnforcedLeray.Short.PartIIIa.T20_4_VelocityIsBiotSavart.MeanPartOfX

/-!
# Part III-a, task `PartIII-a:T20/4`: the library velocity solves Biot-Savart

Proves `CTE.VelocityIsBiotSavart` (statement in `Sub/T20.lean`, unchanged): for `m > 1` and
`ω ∈ X_{m,c}` with zero circulation, `B0583.velocity c ω` is an `L²` field with `div = 0` and
`curl = ω` weakly against all cylinder tests (`IsBiotSavart`).
Source of record: `the November 2 reference manuscript`, lines 3236-3240
(`u = K_c ω`, `K_c = ∇^⊥Δ⁻¹`; the library velocity is `B0581`/`B0583`).

Proof. `velocityIsBiotSavart_of` (`Sub/T20_4.lean`) assembles `IsBiotSavart` from the weak
gradients `B0583.hasWeakVelDeriv_velocity_q`, `hasWeakVelDeriv_velocity_eta` and four facts, proved
in `T20_4_VelocityIsBiotSavart/`: `modeDiv` (modewise `iκ bsSym₀ + iζ bsSym₁ = 0`), `modeCurl`
(modewise `iκ bsSym₁ - iζ bsSym₀ = 1`, with `testModeFourier` the Fourier shape of the modes of a
test field), `synthEmbed0` (synthesis commutes with `z ↦ z e₀`) and `meanPartOfX` (the horizontal
mean is `ω̄`). Completeness of the scalar modes is `Cons.L2.SolAudit.b0581_synth_modes`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

namespace CTE

/-- **The library velocity solves Biot-Savart** (`PartIII-a:T20/4`). -/
theorem velocityIsBiotSavart : VelocityIsBiotSavart :=
  velocityIsBiotSavart_of modeDiv modeCurl synthEmbed0 meanPartOfX

end CTE

end UnforcedLeray.Short.IIIa
