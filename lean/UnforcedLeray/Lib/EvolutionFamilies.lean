import UnforcedLeray.Lib.EvolutionFamilies.Basic
import UnforcedLeray.Lib.EvolutionFamilies.Integral
import UnforcedLeray.Lib.EvolutionFamilies.Dyson
import UnforcedLeray.Lib.EvolutionFamilies.Fubini
import UnforcedLeray.Lib.EvolutionFamilies.DysonRight
import UnforcedLeray.Lib.EvolutionFamilies.Adjoint
import UnforcedLeray.Lib.EvolutionFamilies.Mild
import UnforcedLeray.Lib.EvolutionFamilies.WeakGenerator
import UnforcedLeray.Lib.EvolutionFamilies.Bridge
import UnforcedLeray.Lib.EvolutionFamilies.ExternalInputs

/-!
# Block 1G part 3: evolution families (INF08) and the localisation spectral package (E5–E9)


targets of `scoping/INF07-INF08-INF09-Evolution.md` §5 (Layer 3: T8.1–T8.3, T8.7, T8.8) and
`scoping/ExternalInputs.md` §5.2 (E5–E9, reconciled with the drafted `Infra/` modules under
decision D11). Frozen interfaces of D17: `EvolutionFamily`, `BoundedPert`, `dyson`.

INF08 (`namespace UnforcedLeray.Evolution`; tex 1586-1621, 1655-1676, 1698-1710, 1768-1840,
6224-6233; blueprint B0104, B0106, B0108, B0110, B0111, B0116, B0119, B0322, B0657):
* T8.1 `Basic`: `EvolutionFamily`, `BoundedPert` (strong measurability, as in the manuscript),
  `EvolutionFamily.norm_le_of_blocks` (block composition, B0322); `Bridge`:
  `EvolutionFamily.ofForwardEvolution`, `EvolutionFamily.ofVolterra` (the drafted Volterra
  evolution as an evolution family).
* T8.2 `Dyson`, `DysonRight`, `Mild`, `Bridge`: `dysonTerm`, `dyson`, `dyson_left`,
  `dyson_right`, `hasSum_dyson`, `dyson_unique`, `norm_dyson_le`, `norm_dyson_le_integral`,
  `norm_dyson_sub_dyson_le`, `dyson_commute`, `dyson_compat`; auxiliary `Integral` (strong
  measurability of `L(a) g(a)`, continuity of triangle integrals) and `Fubini` (exchange of the
  iterated integrals on the time triangle).
* T8.3 `Adjoint`: `EvolutionFamily.adjointRefl`, `BoundedPert.adjointRefl`, `adjoint_dyson_eq`,
  `continuousOn_adjoint_dyson`, `adjoint_dyson`, `adjoint_dyson_left`.
* T8.7 `WeakGenerator`: `EvolutionFamily.HasWeakGenerator`, `EvolutionFamily.integral_form`,
  `dyson_hasWeakGenerator`, `EvolutionFamily.proj_evolution_of_left_eig`,
  `EvolutionFamily.deriv_moving_functional`.
* T8.8 `Mild`: `dyson_inhom` (variation of constants), `mild_unique`, `mild_transfer`.

External inputs (`namespace UnforcedLeray.ExternalInputs`), `ExternalInputs`:
E5 `isCompactOperator_of_forall_weaklyNull`, `tendsto_norm_of_isCompactOperator_of_weaklyNull`,
E6 `isCompactOperator_of_integral_compact`, E7 `spectralRadius_le_of_norm_pow_le`,
E8 `finite_spectrum_outside_of_compact_perturbation`, `exists_weight_circle`,
E9 `monodromy_dichotomy`, `CommutesWith.rieszProj_monodromy`
(B0714(d), B0716, B1014; tex 331-370).

Not built: T8.8 "strong solutions are mild" (backward derivative of `U` on a core) and the
causal weighted integrals `s^{-ζ}∫_0^s t^{ζ+3/2} U(s,t) H_t dt`.
-/
