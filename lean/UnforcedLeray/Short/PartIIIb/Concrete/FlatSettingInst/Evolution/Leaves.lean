import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Evolution.Defs

/-!
# The leaves of `TrainEvolutionExists` (source 2819-2836, 4349-4352, 287-288, 2934-2935, 3100-3101)

Source of record: `the November 2 reference manuscript` (73 pages).

`TrainEvolutionExists` (`FlatSettingInst/Leaves.lean`) asks, for `m > 8`, small `ν`, `c = ν⁻²` and
every BUC train, for the pinned operator family `TrainEvolution m tr` on `X_{m,c}` (source 4349-4352:
"The weighted vorticity space is the centrally even, zero-circulation subspace `X_{m,c}` ... Let
`𝒰(s,t)` be the actual train evolution").  The evolution is the Volterra evolution of the source
(2819-2836) around the actual train, built on the real zero-circulation state space by
`Exist.horizonEvolution` (`Short/PartIII-a/Sub/T21_3_Horizon.lean`; the free part is the rescaled
physical heat family `ScaleAux.scaleHeat`, the perturbation `B(r)ω = vω + E K_cω`).  Zero
circulation is built into that state space (source 2934-2935, 3100-3101: "Restriction to zero
circulation is preserved by the actual equation", "Zero mass is preserved by the conservative
physical equation").  `Evolution/Assembly.lean` turns it into a `TrainEvolution` by the
complexification `cx` (`Evolution/Defs.lean`); what remains are the Props below.

* Central evenness is preserved because the actual train is odd (source 287-288: "Uniqueness gives
  `v(-q,-η,s) = -v(q,η,s)`"): every ingredient of the Volterra equation commutes with the
  reflection `x ↦ -x` (`HeatS0Refl`, `HeatResponseRefl`, `FluxBOnRefl`, from `PeriodicRepRefl`,
  `BiotSavartReflect`, `StripVelRefl`, `ec_even`), and the Volterra evolution is the unique solution
  of its strip equations (`VolterraReflect`).
* The joint strong continuity of `𝒰(s,t)` on `0 ≤ t ≤ s` (`TrainEvolution.jointCont`, the
  "jointly strongly continuous evolution" of the Volterra construction) is `VolterraDiagCont` +
  `VolterraJointCont`.
* The flows of `TrainEvolution.flow` are the strip flows of the Volterra evolution, glued
  (`FlowOfRealFamily`).

Status (all compiled): `volterraReflect`, `volterraDiagCont`, `volterraJointCont_of`
(`Evolution/Volterra.lean`); `flowOfRealFamily_of` (`Evolution/Flow.lean`); `biotSavartReflect`,
`stripVelRefl_of` (`Evolution/BiotSavart.lean`); `fluxBOnRefl_of` (`Evolution/FluxRefl.lean`);
`periodicRepRefl`, `heatS0Refl_of`, `heatResponseRefl_of` (`Evolution/Heat.lean`, with
`heat_refl`, `heatDiv_refl` of `Evolution/HeatConv.lean`).  Open: `ReflHeatSupplierExists`

-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Evol

open UnforcedLeray.Infra.VolterraEvolution (VolterraData)
open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution (ActualVorticity ActualFlux
  ActualTrainFluxPathOn actualTrainFluxBOn actualPhysicalWeightedHeatStripSupplier
  xColumnPeriodicRep)
open UnforcedLeray.Short.IIIa.Exist (vortFn fluxFn cplx stripVel IsLinFlowOn)

/-! ## The abstract Volterra evolution -/

/-- **The Volterra evolution commutes with a symmetry of its data** (source 2819-2836: the
evolution is the unique strongly continuous solution of its strip Volterra equations).  If `R_X` is
an involution of `X`, `R_Y` an operator on `Y` and `S₀(t)R_X = R_X S₀(t)`, `S(t)R_Y = R_X S(t)`,
`B(t)R_X = R_Y B(t)` for all `t`, then `E(τ,s)R_X = R_X E(τ,s)` for `s ≤ τ`.
Route: `E'(τ,s) = R_X ∘ E(τ,s) ∘ R_X` (as a CLM) is strongly continuous on strips
(`VolterraData.continuousOn_evolution` + continuity of `R_X`), satisfies the strip Volterra equation
(`VolterraData.evolution_volterra`; `R_X` passes through the interval integral by
`ContinuousLinearMap.intervalIntegral_comp_comm` with `VolterraData.intervalIntegrable_integrand`
and `continuousOn_evolution`, then the three intertwining laws) and the evolution law
(`VolterraData.evolution_comp`, `R_X ∘ R_X = id`); `VolterraData.eq_evolution_of_volterra` gives
`E' = E`; apply to `R_X x` and use `R_X (R_X x) = x`. -/
def VolterraReflect : Prop :=
  ∀ (X Y : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (D : VolterraData ℝ X Y), D.Compatible →
    ∀ (RX : X →L[ℝ] X) (RY : Y →L[ℝ] Y), (∀ x, RX (RX x) = x) →
      (∀ t x, D.S₀ t (RX x) = RX (D.S₀ t x)) → (∀ t y, D.S t (RY y) = RX (D.S t y)) →
      (∀ t x, D.B t (RX x) = RY (D.B t x)) →
      ∀ s τ : ℝ, s ≤ τ → ∀ x, D.evolution τ s (RX x) = RX (D.evolution τ s x)

/-- **Uniform continuity at the diagonal** (source 2819-2836: the Volterra evolution is strongly
continuous, `E(s,s) = I`): if `S₀(0) = I`, then `‖E(τ,s)x - x‖ → 0` as `τ - s → 0⁺`, uniformly
in `s`.  Route: for `s ≤ τ ≤ s + 1`, `VolterraData.evolution_eq_stripEvolution` and
`VolterraData.norm_stripEvolution_sub_apply_le` give
`‖E(τ,s)x - S₀(τ-s)x‖ ≤ 2C₀β(2M₀e^λ)(τ-s)^{1/2}‖x‖`; and `‖S₀(τ-s)x - x‖ = ‖S₀(τ-s)x - S₀(0)x‖`
is small for `τ - s` small by `D.continuousOn_S₀ x` at `0` (within `Icc 0 1`, `Metric.continuousWithinAt_iff`);
take `δ ≤ 1` making both terms `≤ ε/2` (`Real.rpow_le_rpow`, `(ε/2/K)²`). -/
def VolterraDiagCont : Prop :=
  ∀ (X Y : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (D : VolterraData ℝ X Y), D.Compatible →
    D.S₀ 0 = ContinuousLinearMap.id ℝ X →
    ∀ (x : X) (ε : ℝ), 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s τ : ℝ, s ≤ τ → τ ≤ s + δ →
      ‖D.evolution τ s x - x‖ ≤ ε

/-- **Joint strong continuity of the Volterra evolution** on `{s ≤ τ}` (source 2819-2836, the
"jointly strongly continuous evolution" of the Volterra iteration).  Route (with
`VolterraDiagCont`): fix `(τ₀, s₀)`, `s₀ ≤ τ₀`, `ε > 0`; `M` bounds `‖E(τ,s)‖` for
`0 ≤ τ - s ≤ τ₀ - s₀ + 2` (`VolterraData.norm_evolution_le`); for `(τ,s)` near with `s ≤ τ`:
if `s ≤ s₀ ≤ τ`: `E(τ,s)x - E(τ,s₀)x = E(τ,s₀)(E(s₀,s)x - x)` (`evolution_apply_comp`); if
`s₀ ≤ s ≤ τ`: `E(τ,s₀)x - E(τ,s)x = E(τ,s)(E(s,s₀)x - x)`; in both cases `E(τ,s₀)x → E(τ₀,s₀)x`
by `VolterraData.continuousOn_evolution` (on `Ici s₀`); if `s ≤ τ < s₀` (only near the diagonal,
`τ₀ - s₀ < |τ - τ₀|`), compare both `E(τ,s)x` and `E(τ₀,s₀)x` with `x` by `VolterraDiagCont`. -/
def VolterraJointCont : Prop :=
  ∀ (X Y : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (D : VolterraData ℝ X Y), D.Compatible →
    D.S₀ 0 = ContinuousLinearMap.id ℝ X →
    ∀ x : X, ContinuousOn (fun p : ℝ × ℝ => D.evolution p.1 p.2 x) {p : ℝ × ℝ | p.2 ≤ p.1}

/-! ## Reflection of the ingredients (the actual train is odd, source 287-288) -/

/-- **Biot-Savart velocities of reflected vorticities** (source 3236-3240, `K_c = ∇^⊥Δ⁻¹`
commutes with `x ↦ -x` up to the sign of a vector field): if `u` is a Biot-Savart velocity of `ω`
on the cylinder, then `x ↦ -u(-x)` is one of `x ↦ ω(-x)`.  Route: `ψ ↦ ψ ∘ neg` maps cylinder tests
to cylinder tests (`B0579.IsCylTest`: smooth, `c`-periodic by periodicity at `(-q-c, -η)`,
band); `B0579.pd j (ψ ∘ neg) x = -(B0579.pd j ψ (-x))` (chain rule for `fderiv`); integrals over the
cell are invariant under `x ↦ -x` (`integral_cell_comp_neg`, `Evolution/Defs.lean`); `MemLp` by
`MemLp.comp_measurePreserving` with `mp_neg_cell` (`Space.lean`), then `.neg`. -/
def BiotSavartReflect : Prop :=
  ∀ (c : ℝ) (ω : ℝ × ℝ → ℂ) (u : ℝ × ℝ → Fin 2 → ℂ), IIIa.IsBiotSavart c ω u →
    IIIa.IsBiotSavart c (fun x => ω (-x)) (fun x j => -u (-x) j)

/-- **The real Biot-Savart velocity of the reflected vorticity** (`K_c(Rω) = -(K_cω)(-·)`): for `w`
in the actual state space, `stripVel (reflV w) = -stripVel w (-·)` a.e. on the cell.  Route:
`Exist.biotSavartFieldAll` for `w` and `reflV w`; `BiotSavartReflect` for `w`; the vorticities
agree a.e. (`vortFn_reflV`, `Evolution/Defs.lean`; `IIIa.IsBiotSavart` sees the vorticity only
through `∫_cell ω ψ`, so it is invariant under a.e. changes of `ω`); uniqueness
`IIIa.CTE.isBiotSavart_unique` (`Short/PartIII-a/T20_2_BiotSavartUnique.lean`). -/
def StripVelRefl : Prop :=
  ∀ (c m : ℝ) [Fact (0 < c)] (hm : 1 ≤ m) (w : ActualVorticity (c := c) (m := m) hm),
    ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ∀ j, stripVel hm (reflV hm w) x j = -stripVel hm w (-x) j

/-- **The train flux intertwines the reflections** (source 287-288, 2819-2836: `B(r)ω = vω + E K_cω`
with `v` odd, `E = curl v` even): `B(r)(Rω) = R_F(B(r)ω)` for the clamped horizon flux.  Route:
`actualTrainFluxBOn hm P r` is `physicalFluxKernelCLM` of `Vc tr s`, `Ec tr s` at the clamped age
`s = (actualTrainAgeClamp T hT r).1 ≥ 0` (unfold `actualTrainFluxBOn`, `actualTrainFluxAtNonneg`);
compare components a.e. on the cell (`Subtype`/`Lp.ext`, `ae_cellMeasure_of_ae_cell`) with
`Exist.L4Aux.fluxFn_ae`: `fluxFn (B w) i x = w(x) v_i(x) + E(x)(K_c w)_i(x)`; for `reflV w` use
`vortFn_reflV` and `StripVelRefl` (real parts); for `reflF (B w)` use `fluxFn_reflF` and
`fluxFn_ae` at `-x` (transport through `(mp_neg_cell c).quasiMeasurePreserving.ae`); then
`tr.isTrain.odd s hs` (`v(-x) = -v(x)`) and `ec_even` (`Evolution/Defs.lean`). -/
def FluxBOnRefl : Prop :=
  ∀ (ν c m : ℝ) [Fact (0 < c)] (hm : 1 ≤ m) (tr : UnforcedLeray.B0140.TrainSol ν c) (T : ℝ)
    (hT : 0 ≤ T) (P : ActualTrainFluxPathOn (c := c) (m := m) (ν := ν) hm tr hT) (r : ℝ)
    (w : ActualVorticity (c := c) (m := m) hm),
    actualTrainFluxBOn hm P r (reflV hm w) = reflF (actualTrainFluxBOn hm P r w)

/-- **The periodic representative commutes with the reflection** (the heat family acts on the
periodic lift of the cell datum, source 2819-2836): on the whole plane,
`rep(f(-·)) = rep(f)(-·)` and `rep(-f) = -rep(f)` almost everywhere, `rep = xColumnPeriodicRep`.
Route: `xColumnPeriodicRep hc f = HeatCylinder.centeredPerLift hc (mk f)`
(`Cons/.../MixedEvolution/FluxHeatCLM.lean`, `Lib/HeatCylinder/PeriodicLift.lean`);
`centeredPerLift_congr_ae` (cell-a.e. equal data give a.e. equal lifts), `xColumnPeriodicRep_ae_eq`,
`coeFn_reflR`, `Lp.coeFn_neg`; and for any `g`,
`centeredPerLift hc (g ∘ neg) z = centeredPerLift hc g (-z)` unless the wrapped coordinate
`toIcoMod hc (-(c/2)) z.1` is `-(c/2)` (`Sob.perExt`; `toIcoMod_neg`), a set `(-(c/2) + cℤ) × ℝ` of
measure zero. -/
def PeriodicRepRefl : Prop :=
  ∀ (c m : ℝ) (hc : 0 < c) (f : B0579.X c m),
    (xColumnPeriodicRep hc (reflR c m f) =ᵐ[volume] fun z => xColumnPeriodicRep hc f (-z)) ∧
      (xColumnPeriodicRep hc (-f) =ᵐ[volume] fun z => -xColumnPeriodicRep hc f z)

/-- **The physical heat family commutes with the reflection** (source 2819-2836, the free part of
the Volterra iteration; the planar heat kernel is even).  Route: `S₀ t` is
`actualWeightedHeatS0Totalized hc1 hm t`: `0` off `[0,1]`, the identity at `t = 0`
(`actualWeightedHeatS0_zero`), and for `0 < t ≤ 1` the class of
`z ↦ (B0284.heat t (xColumnHeatLift hc f) z).1 = ∫ w, heatKernel2 t w * rep f (z - w)`
(`actualWeightedHeatS0_apply_of_pos`, `coeFn_xColumnHeatS0Positive`, `B0284.heat_apply_of_pos`);
by `PeriodicRepRefl` (a.e. on the plane, transported by `w ↦ z - w`) and the substitution
`w ↦ -w` (`integral_neg_eq_self`), with `heatKernel2 t (-w) = heatKernel2 t w`, the heat of
`rep(f(-·))` at `z` is the heat of `rep f` at `-z`; conclude with `coeFn_reflR` and `Lp.ext`. -/
def HeatS0Refl : Prop :=
  ∀ (c m : ℝ) [Fact (0 < c)] (hc1 : 1 ≤ c) (hm : 1 ≤ m) (t : ℝ)
    (w : ActualVorticity (c := c) (m := m) hm),
    (actualPhysicalWeightedHeatStripSupplier hc1 hm).S₀ t (reflV hm w) =
      reflV hm ((actualPhysicalWeightedHeatStripSupplier hc1 hm).S₀ t w)

/-- **The heat-divergence response intertwines the reflections** (source 2819-2836, the response
`S(t) = -e^{tΔ}div` of the Volterra iteration; the gradient of the heat kernel is odd).  Route: `S t`
is `actualWeightedHeatResponse t`: `0` unless `0 < t ≤ 1`, then the class of the first component of
`negativeHeatDiv t (xFluxPeriodicTensor hc F) = -B0296.heatDiv t (scalarFluxTensor (rep F₀) (rep F₁))`
(`actualWeightedHeatResponse_value`), i.e.
`-∫ w, ((gradHeatKernel2 t w).1 * rep F₀ (z - w) + (gradHeatKernel2 t w).2 * rep F₁ (z - w))`;
for `reflF F` the components are `-(R F_i)`, so by both parts of `PeriodicRepRefl`,
`w ↦ -w` and `gradHeatKernel2 t (-w) = -gradHeatKernel2 t w` the response of `reflF F` at `z` is the
response of `F` at `-z`. -/
def HeatResponseRefl : Prop :=
  ∀ (c m : ℝ) [Fact (0 < c)] (hc1 : 1 ≤ c) (hm : 1 ≤ m) (t : ℝ) (F : ActualFlux (c := c) (m := m)),
    (actualPhysicalWeightedHeatStripSupplier hc1 hm).S t (reflF F) =
      reflV hm ((actualPhysicalWeightedHeatStripSupplier hc1 hm).S t F)

/-- **A rescaled heat family with the reflection laws** (source 2819-2836: the free part of the
Volterra iteration is the heat semigroup `e^{νtΔ}` and its divergence response; source 287-288 for
the symmetry): for `0 < ν ≤ 1` there is a heat supplier with the weak heat properties of diffusivity
`ν` whose `S₀(t)` commutes with the reflection and whose `S(t)` intertwines `reflF` and `reflV`.
Route: `H = Exist.ScaleAux.scaleHeat hm H0 ν hν0 hν1` with
`H0 = actualPhysicalWeightedHeatStripSupplier hc1 hm` (`Clock/Existence/ScaleSupplier.lean`);
`Exist.ScaleAux.scaledHeatWeak_scale` with `Exist.unitHeatWeakActual` (task `PartIII-a:T21/3/2`);
`H.S₀ t = H0.S₀ (ν * t)`, `H.S t = H0.S (ν * t)` (`scaleHeat_S₀`, `scaleHeat_S`, by `rfl`) with
`HeatS0Refl`, `HeatResponseRefl`. -/
def ReflHeatSupplierExists : Prop :=
  ∀ (ν c m : ℝ) [Fact (0 < c)] (hc1 : 1 ≤ c) (hm : 1 ≤ m), 0 < ν → ν ≤ 1 →
    ∃ H : UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.WeightedHeatStripSupplier
        (c := c) (m := m) hm,
      UnforcedLeray.Short.IIIa.Exist.ScaledHeatWeak hm ν H ∧
      (∀ t w, H.S₀ t (reflV hm w) = reflV hm (H.S₀ t w)) ∧
      (∀ t F, H.S t (reflF F) = reflV hm (H.S t F))

/-! ## The flows -/

/-- **Complex flows from the real Volterra family** (source 2819-2836; the Volterra evolution acts on
real data and complex data are split into real and imaginary parts): if `E` is a cocycle of
operators on the actual state space whose orbits are weak linearised flows on every unit strip
`[a, a+1]`, `a ≥ 0`, then for `t ≥ 0` and `a, b` in the state space, any `f`, `ω` a.e. equal to
`a + i b` and `E(s,t)a + i E(s,t)b` (`s ≥ t`) form a weak linearised flow on `[t, ∞)` with velocity
`K_c E(s,t)a + i K_c E(s,t)b`.  Route: as `Exist.fullFlowExists_of_family` (`Sub/T21_3.lean`):
`Exist.flowGlobal`; induction on the windows `[t, t + N + 1]` with `Exist.flowAppend`; each unit
strip `[a', a'+1]`, `a' = t + N` (base: `a' = t`), from `Exist.linFlowComb` of the strip flows of
`E(a',t)a`, `E(a',t)b`, transported by `Exist.flowCongrAE` (the cocycle law
`E(s,a')E(a',t) = E(s,t)` rewrites vorticity and velocity; the datum `ω a'` is a.e.
`E(a',t)a + i E(a',t)b`). -/
def FlowOfRealFamily : Prop :=
  ∀ (ν c m : ℝ) [Fact (0 < c)] (hm : 1 ≤ m) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (E : ℝ → ℝ → ActualVorticity (c := c) (m := m) hm →L[ℝ] ActualVorticity (c := c) (m := m) hm),
    (∀ s r τ : ℝ, 0 ≤ s → s ≤ r → r ≤ τ → ∀ w, E τ r (E r s w) = E τ s w) →
    (∀ a : ℝ, 0 ≤ a → ∀ w, IsLinFlowOn ν c m tr a (a + 1) (cplx (vortFn hm w))
      (fun r => cplx (vortFn hm (E r a w))) (fun r => stripVel hm (E r a w))) →
    ∀ t : ℝ, 0 ≤ t → ∀ (a b : ActualVorticity (c := c) (m := m) hm) (f : ℝ × ℝ → ℂ)
      (ω : ℝ → ℝ × ℝ → ℂ),
      f =ᵐ[volume.restrict (B0579.cell c)]
        (fun x => cplx (vortFn hm a) x + Complex.I * cplx (vortFn hm b) x) →
      (∀ s, t ≤ s → ω s =ᵐ[volume.restrict (B0579.cell c)]
        fun x => cplx (vortFn hm (E s t a)) x + Complex.I * cplx (vortFn hm (E s t b)) x) →
      IIIa.IsLinearisedFlow ν c m tr t f ω
        (fun s x j => stripVel hm (E s t a) x j + Complex.I * stripVel hm (E s t b) x j)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Evol
