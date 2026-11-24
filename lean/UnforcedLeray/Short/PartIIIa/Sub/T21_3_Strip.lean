import UnforcedLeray.Short.PartIIIa.Sub.T21_3

/-!
# Part III-a, `PartIII-a:T21/3`: the Volterra side (statements and conditional assembly)

Source of record: `the November 2 reference manuscript`, lines 2819-2836 (existence
of `U(s,t)`: Volterra iteration around the actual train).  The vorticity equation around the
actual train `(v, E)` is
`ω_s = νΔω - ∇·(vω + E K_cω)` on the cylinder, i.e. `ω_s + v·∇ω + (K_cω)·∇E = νΔω`
(`div v = div K_cω = 0`).  The bounded perturbation is `B(r)ω = vω + E K_cω`
(`actualTrainFluxB`, built from B0238 `Vc`, `Ec` and the real Biot-Savart velocity
`realBiotSavart`), the free part is the weighted heat semigroup `S₀` and its heat-divergence
response `S` (`WeightedHeatStripSupplier`), and the unit-strip mild equation is
`D.evolution t s w = S₀(t-s) w + ∫_s^t S(t-r) B(r) D.evolution r s w dr`
(`actualTrainEvolution_mild`).

All statements below are Props, quantified over `(ν, c, m)` in the regime `Regime`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.Short.IIIa
open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

/-- The regime of the full-clock estimate: `0 < ν ≤ 1`, `c = ν⁻²` (so `c ≥ 1`), `m > 8`. -/
def Regime (ν c m : ℝ) : Prop := 0 < ν ∧ ν ≤ 1 ∧ c = ν ^ (-2 : ℝ) ∧ 8 < m

theorem Regime.one_le_c {ν c m : ℝ} (h : Regime ν c m) : 1 ≤ c := by
  obtain ⟨h0, h1, hc, -⟩ := h
  rw [hc]
  exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos h0 h1 (by norm_num)

theorem Regime.pos_c {ν c m : ℝ} (h : Regime ν c m) : 0 < c :=
  lt_of_lt_of_le one_pos h.one_le_c

theorem Regime.one_le_m {ν c m : ℝ} (h : Regime ν c m) : 1 ≤ m := by
  have := h.2.2.2; linarith

section Defs

variable {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)

/-- The (real) function represented by an element of the physical state space. -/
def vortFn (w : ActualVorticity (c := c) (m := m) hm) : ℝ × ℝ → ℝ :=
  fun x => (w.1 : UnforcedLeray.B0579.X c m) x

/-- The function represented by the `i`-th component of a weighted flux. -/
def fluxFn (F : ActualFlux (c := c) (m := m)) (i : Fin 2) : ℝ × ℝ → ℝ :=
  fun x => (F i : UnforcedLeray.B0579.X c m) x

/-- Complex coercion of a real function. -/
def cplx (g : ℝ × ℝ → ℝ) : ℝ × ℝ → ℂ := fun x => (g x : ℂ)

/-- The real Biot-Savart velocity `K_c w` (B0583 + real part), as a complex-coerced field. -/
def stripVel (w : ActualVorticity (c := c) (m := m) hm) : ℝ × ℝ → Fin 2 → ℂ :=
  fun x j => ((realBiotSavart hm w.1
    ((mem_zeroCirculationSubmodule_iff (by linarith : 1 / 2 < m) w.1).1 w.2) x :
      UnforcedLeray.Train.Vec) j : ℂ)

/-- **Weak form of the free heat family with diffusivity `ν`** (SP 2819-2836; the supplier's heat
runs on `[0,1]`).  (a) `t ↦ S₀(t) w` is the weak solution of `∂_t ω = νΔω` from `w`;
(b) for every continuous flux path `F` on `[a,b] ⊂ [a, a+1]`, the Duhamel term
`Y(t) = ∫_a^t S(t-r) F(r) dr` is the weak solution of `∂_t Y = νΔY - ∇·F` from `0`, i.e.
`∫ Y(t) φ = ν ∫_a^t ∫ Y(r) Δφ dr + ∫_a^t ∫ F(r)·∇φ dr`. -/
def ScaledHeatWeak (ν : ℝ) (H : WeightedHeatStripSupplier (c := c) (m := m) hm) : Prop :=
  haveI := actualVorticityCompleteSpace (c := c) (m := m) hm
  (∀ (w : ActualVorticity (c := c) (m := m) hm) (φ : ℝ × ℝ → ℝ), UnforcedLeray.B0579.IsCylTest c φ →
    ∀ t ∈ Icc (0 : ℝ) 1,
      ∫ x in UnforcedLeray.B0579.cell c, vortFn hm (H.S₀ t w) x * φ x =
        (∫ x in UnforcedLeray.B0579.cell c, vortFn hm w x * φ x) +
          ν * ∫ r in (0 : ℝ)..t, ∫ x in UnforcedLeray.B0579.cell c,
            vortFn hm (H.S₀ r w) x * lapP φ x) ∧
  (∀ (F : ℝ → ActualFlux (c := c) (m := m)) (a b : ℝ), a ≤ b → b ≤ a + 1 →
    ContinuousOn F (Icc a b) → ∀ φ : ℝ × ℝ → ℝ, UnforcedLeray.B0579.IsCylTest c φ →
      ∀ t ∈ Icc a b,
        ∫ x in UnforcedLeray.B0579.cell c, vortFn hm (∫ r in a..t, H.S (t - r) (F r)) x * φ x =
          (ν * ∫ r in a..t, ∫ x in UnforcedLeray.B0579.cell c,
              vortFn hm (∫ s in a..r, H.S (r - s) (F s)) x * lapP φ x) +
            ∫ r in a..t, ∫ x in UnforcedLeray.B0579.cell c,
              (fluxFn (F r) 0 x * UnforcedLeray.B0579.pd 0 φ x +
                fluxFn (F r) 1 x * UnforcedLeray.B0579.pd 1 φ x))

variable {ν : ℝ}

/-- The Volterra evolution of the actual train flux path `P` with heat family `H` is, on every
unit strip `[a, a+1]`, `a ≥ 0`, a weak linearised flow from any `w` in the physical state space,
with velocity the real Biot-Savart velocity of the current vorticity. -/
def StripWeakLp (tr : UnforcedLeray.B0140.TrainSol ν c)
    (P : ActualTrainFluxPath (c := c) (m := m) hm (ν := ν) tr)
    (H : WeightedHeatStripSupplier (c := c) (m := m) hm) : Prop :=
  ∀ a : ℝ, 0 ≤ a → ∀ w : ActualVorticity (c := c) (m := m) hm,
    IsLinFlowOn ν c m tr a (a + 1) (cplx (vortFn hm w))
      (fun r => cplx (vortFn hm ((actualTrainVolterraData hm P H).evolution r a w)))
      (fun r => stripVel hm ((actualTrainVolterraData hm P H).evolution r a w))

/-- The real Biot-Savart velocity of `w ∈ X_{m,c}` of zero circulation is a (complex-coerced)
`IsBiotSavart` velocity: `L²`, divergence free, `curl u = ∂_q u_η - ∂_η u_q = ω` in the weak
sense on the cylinder.  (Check the orientation convention of `realBiotSavart` against
`IsBiotSavart` in `Defs.lean`; B0583 `velocity`, `hasWeakVelDeriv_*`, `Cons/.../RealBiotSavart.lean`
`realBiotSavart_hasWeakDerivs`.) -/
def BiotSavartField : Prop :=
  ∀ w : ActualVorticity (c := c) (m := m) hm,
    IsBiotSavart c (cplx (vortFn hm w)) (stripVel hm w)

/-- **Flux identity.**  At every age `r ≥ 0`, for `w` in the state space and every cylinder test
`φ`, the tested right-hand side of the linearised equation is integrable on the cell and equals
`ν ∫ w Δφ + ∫ (B(r) w)·∇φ` with `B(r) w = v ω + E K_cω` (`actualTrainFluxB`): the integration by
parts `-(u·∇E)φ ↦ ∫ E u·∇φ` uses `div K_cw = 0` (cf. `flowIntegrand` in `Defs.lean`). -/
def FluxIdentity (tr : UnforcedLeray.B0140.TrainSol ν c)
    (P : ActualTrainFluxPath (c := c) (m := m) hm (ν := ν) tr) : Prop :=
  ∀ r : ℝ, 0 ≤ r → ∀ w : ActualVorticity (c := c) (m := m) hm, ∀ φ : ℝ × ℝ → ℝ,
    UnforcedLeray.B0579.IsCylTest c φ →
      IntegrableOn (flowIntegrand tr (cplx (vortFn hm w)) (stripVel hm w) r φ)
          (UnforcedLeray.B0579.cell c) ∧
        ∫ x in UnforcedLeray.B0579.cell c, flowIntegrand tr (cplx (vortFn hm w)) (stripVel hm w) r φ x
          = (((ν * (∫ x in UnforcedLeray.B0579.cell c, vortFn hm w x * lapP φ x) +
              ∫ x in UnforcedLeray.B0579.cell c,
                (fluxFn (actualTrainFluxB hm P r w) 0 x * UnforcedLeray.B0579.pd 0 φ x +
                  fluxFn (actualTrainFluxB hm P r w) 1 x * UnforcedLeray.B0579.pd 1 φ x)
              : ℝ)) : ℂ)

/-- **Mild solution is weak, integrated form.**  If the heat family satisfies `ScaledHeatWeak ν H`,
the unit-strip Volterra path `ω(s) = D.evolution s a w` satisfies for `s ∈ [a, a+1]`
`∫ ω(s) φ = ∫ w φ + ∫_a^s (ν ∫ ω(r) Δφ + ∫ (B(r) ω(r))·∇φ) dr`
(Duhamel with `S₀` weak (a) and the response weak (b) applied to `F(r) = B(r) ω(r)`, which is
continuous on `[a, a+1]` by `continuous_actualTrainFluxB_apply` + `continuousOn_evolution`; the
mild equation is `actualTrainEvolution_mild`). -/
def MildIntegrated (tr : UnforcedLeray.B0140.TrainSol ν c)
    (P : ActualTrainFluxPath (c := c) (m := m) hm (ν := ν) tr)
    (H : WeightedHeatStripSupplier (c := c) (m := m) hm) : Prop :=
  ScaledHeatWeak hm ν H →
  ∀ a : ℝ, 0 ≤ a → ∀ w : ActualVorticity (c := c) (m := m) hm, ∀ φ : ℝ × ℝ → ℝ,
    UnforcedLeray.B0579.IsCylTest c φ → ∀ s ∈ Icc a (a + 1),
      ∫ x in UnforcedLeray.B0579.cell c,
          vortFn hm ((actualTrainVolterraData hm P H).evolution s a w) x * φ x =
        (∫ x in UnforcedLeray.B0579.cell c, vortFn hm w x * φ x) +
          ∫ r in a..s,
            (ν * (∫ x in UnforcedLeray.B0579.cell c,
                vortFn hm ((actualTrainVolterraData hm P H).evolution r a w) x * lapP φ x) +
              ∫ x in UnforcedLeray.B0579.cell c,
                (fluxFn (actualTrainFluxB hm P r ((actualTrainVolterraData hm P H).evolution r a w)) 0 x *
                    UnforcedLeray.B0579.pd 0 φ x +
                  fluxFn (actualTrainFluxB hm P r ((actualTrainVolterraData hm P H).evolution r a w)) 1 x *
                    UnforcedLeray.B0579.pd 1 φ x))

/-- **Continuity fields.**  The unit-strip path is strongly continuous in `X_{m,c}` (complex
norm), and its tested right-hand side `r ↦ ∫_cell flowIntegrand` is interval integrable (continuous
in `r`: continuity of `evolution`, of `B`, of the train, and the bounds of `FluxIdentity`). -/
def StripContinuity (tr : UnforcedLeray.B0140.TrainSol ν c)
    (P : ActualTrainFluxPath (c := c) (m := m) hm (ν := ν) tr)
    (H : WeightedHeatStripSupplier (c := c) (m := m) hm) : Prop :=
  ∀ a : ℝ, 0 ≤ a → ∀ w : ActualVorticity (c := c) (m := m) hm,
    (∀ s ∈ Icc a (a + 1),
      Tendsto (fun s' => xNorm c m
          (cplx (vortFn hm ((actualTrainVolterraData hm P H).evolution s' a w)) -
            cplx (vortFn hm ((actualTrainVolterraData hm P H).evolution s a w))))
        (𝓝[Icc a (a + 1)] s) (𝓝 0)) ∧
    (∀ φ : ℝ × ℝ → ℝ, UnforcedLeray.B0579.IsCylTest c φ → ∀ s ∈ Icc a (a + 1),
      IntervalIntegrable (fun r => ∫ x in UnforcedLeray.B0579.cell c,
        flowIntegrand tr (cplx (vortFn hm ((actualTrainVolterraData hm P H).evolution r a w)))
          (stripVel hm ((actualTrainVolterraData hm P H).evolution r a w)) r φ x) volume a s)

end Defs

/-! ## Universal forms (one per leaf) -/

/-- `T21/3/1` (restated by `PartIII-a:T21/3/1/org`): a train with finite-horizon coefficient bounds
gives, for every age horizon `T ≥ 0`, a horizon flux path `ActualTrainFluxPathOn` (SP 2819-2836:
`B(t)ω = vω + E K_cω` bounded and strongly continuous on bounded age strips; the bounds on `[0, T]`
are `FiniteHorizonTrainBounds`, `Sub/T21_3_TrainBounds.lean`).  The age-uniform path
`ActualTrainFluxPath` is not used: the weighted curl bound of the actual train grows with the age
(see the docstring of `Sub/T21_3_TrainBounds.lean`). -/
def FluxPathExistsAll : Prop :=
  ∀ (ν c m : ℝ) [Fact (0 < c)] (hm : 1 ≤ m) (tr : UnforcedLeray.B0140.TrainSol ν c),
    Regime ν c m → FiniteHorizonTrainBounds tr m → ∀ (T : ℝ) (hT : 0 ≤ T),
      Nonempty (ActualTrainFluxPathOn (c := c) (m := m) (ν := ν) hm tr hT)

/-- `FluxPathExistsAll` from the strong continuity of the clamped flux (`FluxContinuityOn`). -/
theorem fluxPathExistsAll_of (h : FluxContinuityOn) : FluxPathExistsAll := by
  intro ν c m _ hm tr _ hB T hT
  exact nonempty_actualTrainFluxPathOn h hm tr hB hT

/-- `T21/3/2`: the constructed physical heat family has the weak properties with diffusivity `1`. -/
def UnitHeatWeakActual : Prop :=
  ∀ (c m : ℝ) [Fact (0 < c)] (hc1 : 1 ≤ c) (hm : 1 ≤ m),
    ScaledHeatWeak hm 1 (actualPhysicalWeightedHeatStripSupplier (c := c) (m := m) hc1 hm)

/-- `T21/3/3`: time rescaling `S₀^ν(t) = S₀(νt)`, `S^ν(t) = S(νt)` (`0 < ν ≤ 1`, so `νt ∈ [0,1]`
for `t ∈ [0,1]`) gives a `WeightedHeatStripSupplier` with `ScaledHeatWeak ν`. -/
def ScaleSupplier : Prop :=
  ∀ (ν c m : ℝ) [Fact (0 < c)] (hc1 : 1 ≤ c) (hm : 1 ≤ m), 0 < ν → ν ≤ 1 →
    ScaledHeatWeak hm 1 (actualPhysicalWeightedHeatStripSupplier (c := c) (m := m) hc1 hm) →
    ∃ H : WeightedHeatStripSupplier (c := c) (m := m) hm, ScaledHeatWeak hm ν H

/-- `T21/3/4`. -/
def BiotSavartFieldAll : Prop :=
  ∀ (c m : ℝ) [Fact (0 < c)] (hm : 1 ≤ m), BiotSavartField (c := c) (m := m) hm

/-- `T21/3/5`. -/
def FluxIdentityAll : Prop :=
  ∀ (ν c m : ℝ) [Fact (0 < c)] (hm : 1 ≤ m) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (P : ActualTrainFluxPath (c := c) (m := m) hm (ν := ν) tr), Regime ν c m →
    FluxIdentity hm tr P

/-- `T21/3/6`. -/
def MildIntegratedAll : Prop :=
  ∀ (ν c m : ℝ) [Fact (0 < c)] (hm : 1 ≤ m) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (P : ActualTrainFluxPath (c := c) (m := m) hm (ν := ν) tr)
    (H : WeightedHeatStripSupplier (c := c) (m := m) hm), Regime ν c m →
    MildIntegrated hm tr P H

/-- `T21/3/7`. -/
def StripContinuityAll : Prop :=
  ∀ (ν c m : ℝ) [Fact (0 < c)] (hm : 1 ≤ m) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (P : ActualTrainFluxPath (c := c) (m := m) hm (ν := ν) tr)
    (H : WeightedHeatStripSupplier (c := c) (m := m) hm), Regime ν c m →
    StripContinuity hm tr P H

/-- `T21/3/8`: the unit-strip Volterra path is a weak linearised flow, from the four parts and the
weak heat property (the fields of `IsLinFlowOn`: `initial` from `actualTrainEvolution_initial`,
`memX` from `Lp`, `strongCont`/`timeIntegrable` from `StripContinuity`, `biotSavart` from
`BiotSavartField`, `integrable` from `FluxIdentity`, `weak` from `MildIntegrated` and
`FluxIdentity`, in `ℂ`). -/
def StripWeakAssemblyFromParts : Prop :=
  BiotSavartFieldAll → FluxIdentityAll → MildIntegratedAll → StripContinuityAll →
  ∀ (ν c m : ℝ) [Fact (0 < c)] (hm : 1 ≤ m) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (P : ActualTrainFluxPath (c := c) (m := m) hm (ν := ν) tr)
    (H : WeightedHeatStripSupplier (c := c) (m := m) hm), Regime ν c m →
    ScaledHeatWeak hm ν H → StripWeakLp hm tr P H

/-- `T21/3/9`: from the strip flows of the Volterra evolution to the cocycle of complex-data flows
(`W r a f = cplx(D.evolution r a f_re) + I * cplx(D.evolution r a f_im)` for admissible
`f = f_re + I f_im`, `0` otherwise; the cocycle law is `evolution_comp`; linearity of the equation in
`(ω, u)`; real and imaginary parts of an admissible datum are admissible). -/
def StripBookkeeping : Prop :=
  ∀ (ν c m : ℝ) [Fact (0 < c)] (hm : 1 ≤ m) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (P : ActualTrainFluxPath (c := c) (m := m) hm (ν := ν) tr)
    (H : WeightedHeatStripSupplier (c := c) (m := m) hm), Regime ν c m →
    StripWeakLp hm tr P H → ComplexStripFamily ν c m tr

/-! The conditional assembly of `FullFlowExistsSmall` is `fullFlowExistsSmall_of` in
`Sub/T21_3_Horizon.lean` (horizon data); the forms above over an age-uniform path
`ActualTrainFluxPath` (`StripWeakLp`, `FluxIdentity`, `MildIntegrated`, `StripContinuity`,
`StripBookkeeping` and their universal forms) are kept for the files that already use them, and are
not part of the main chain. -/

end UnforcedLeray.Short.IIIa.Exist
