import UnforcedLeray.Short.PartIIIa.Sub.T21_3_Strip
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_5.L4
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_9

/-!
# Part III-a, `PartIII-a:T21/3`: the Volterra evolution from horizon data

Source of record: `the November 2 reference manuscript`, SP 2819-2836 (the full
evolution `U(s,t)` around the actual train `(v, E)`: free part the weighted heat family, bounded
perturbation `B(r)ω = vω + E K_cω`), SP 2072-2095 (the evolution is built on bounded age intervals,
where the train bounds hold), SP 270-288 and 460-467 (train bounds on `[0, S_*]`).

The actual train has velocity and weighted curl bounds only on finite age horizons
(`Sub/T21_3_TrainBounds.lean`).  So for every horizon `T` the Volterra data `horizonData hm P H`
uses the horizon flux path `P : ActualTrainFluxPathOn hm tr hT` (coefficient `B` the actual flux on
`[0, T]`, clamped outside) and the heat family `H`.  On a unit strip `[a, a + 1] ⊆ [0, T]` its
evolution is a weak linearised flow (`StripWeakLpOn`, assembled here from `FluxIdentityOn`,
`MildIntegratedOn`, `StripContinuityOn`, `BiotSavartField`).  Two horizon evolutions agree on
common ages (`HorizonLocality`: uniqueness of the strip Volterra equation), so the evolutions with
horizons `⌈τ⌉₊` form one family `horizonEvolution` with the cocycle law; real and imaginary parts
then give `ComplexStripFamily` (`stripBookkeepingOn_of`), and `fullFlowExists_of_family` glues.

## Contents

* `horizonData`, `horizonData_compatible`, `horizonData_mild`, `horizonData_initial`;
* `actualTrainFluxBOn_congr`: the clamped fluxes of two horizons agree on common ages;
* leaf Props: `FluxIdentityOn` (+ `fluxIdentityOn_of`, proved from the accepted lemmas of
  `PartIII-a:T21/3/5/1-3`), `MildIntegratedOn`, `StripContinuityOn`, `HorizonLocality`;
* `StripWeakLpOn`, `stripWeakAssemblyOnFromParts` (proved);
* `horizonEvolution`, `StripBookkeepingOn`, `stripBookkeepingOn_of` (proved from the accepted
  lemmas of `PartIII-a:T21/3/9/1-4`, `FlowCongrAE` and `HorizonLocality`);
* `fullFlowExistsSmall_of`: the conditional assembly of `FullFlowExistsSmall`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.Short.IIIa
open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

section Horizon

variable {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)

/-- **The Volterra data on the age horizon `[0, T]`**: free family `H.S₀`, response `H.S`,
coefficient the clamped actual train flux `actualTrainFluxBOn hm P` (equal to `B(r) = vω + E K_cω`
for `r ∈ [0, T]`, `actualTrainFluxBOn_eq_actual`). -/
def horizonData {ν : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c} {T : ℝ} {hT : 0 ≤ T}
    (P : ActualTrainFluxPathOn hm tr hT) (H : WeightedHeatStripSupplier (c := c) (m := m) hm) :
    UnforcedLeray.Infra.VolterraEvolution.VolterraData ℝ
      (ActualVorticity (c := c) (m := m) hm) (ActualFlux (c := c) (m := m)) where
  S₀ := H.S₀
  S := H.S
  B := actualTrainFluxBOn hm P
  M₀ := H.M₀
  C₀ := H.C₀
  β := P.Cv + P.CE * (c / (2 * Real.pi) + 2)
  norm_S₀_le := H.norm_S₀_le
  norm_S_le := H.norm_S_le
  norm_B_le := norm_actualTrainFluxBOn_le hm P
  continuousOn_S₀ := H.continuousOn_S₀
  continuousOn_S := H.continuousOn_S
  continuous_B := continuous_actualTrainFluxBOn_apply hm P

theorem horizonData_compatible {ν : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c} {T : ℝ}
    {hT : 0 ≤ T} (P : ActualTrainFluxPathOn hm tr hT)
    (H : WeightedHeatStripSupplier (c := c) (m := m) hm) :
    (horizonData hm P H).Compatible where
  S₀_comp_S₀ := H.S₀_comp_S₀
  S₀_comp_S := H.S₀_comp_S

/-- The unit-strip mild equation of the horizon evolution. -/
theorem horizonData_mild {ν : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c} {T : ℝ}
    {hT : 0 ≤ T} (P : ActualTrainFluxPathOn hm tr hT)
    (H : WeightedHeatStripSupplier (c := c) (m := m) hm) {s t : ℝ} (hst : s ≤ t)
    (ht : t ≤ s + 1) (w : ActualVorticity (c := c) (m := m) hm) :
    (horizonData hm P H).evolution t s w =
      H.S₀ (t - s) w + ∫ r in s..t,
        H.S (t - r) (actualTrainFluxBOn hm P r ((horizonData hm P H).evolution r s w)) :=
  (horizonData hm P H).evolution_volterra (horizonData_compatible hm P H) ⟨hst, ht⟩ w

theorem horizonData_initial {ν : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c} {T : ℝ}
    {hT : 0 ≤ T} (P : ActualTrainFluxPathOn hm tr hT)
    (H : WeightedHeatStripSupplier (c := c) (m := m) hm) (s : ℝ)
    (w : ActualVorticity (c := c) (m := m) hm) :
    (horizonData hm P H).evolution s s w = w := by
  have h := horizonData_mild hm P H (s := s) (t := s) le_rfl (by linarith) w
  simpa [H.S₀_zero] using h

/-- The clamped fluxes of two horizon paths agree on their common physical ages (both are the
actual flux of `Vc tr r`, `Ec tr r`; the bound constants do not enter its values). -/
theorem actualTrainFluxBOn_congr {ν : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c} {T T' : ℝ}
    {hT : 0 ≤ T} {hT' : 0 ≤ T'} (P : ActualTrainFluxPathOn hm tr hT)
    (P' : ActualTrainFluxPathOn hm tr hT') {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ T) (h2 : r ≤ T') :
    actualTrainFluxBOn hm P r = actualTrainFluxBOn hm P' r := by
  rw [actualTrainFluxBOn_eq_actual hm P ⟨h0, h1⟩, actualTrainFluxBOn_eq_actual hm P' ⟨h0, h2⟩]
  ext w i : 2
  simp only [actualTrainFluxAtNonneg, physicalFluxKernelCLM, ContinuousLinearMap.pi_apply,
    physicalFluxComponentCLM_apply]
  all_goals rfl

/-! ## Leaf statements on a horizon -/

/-- **Flux identity on the horizon** (SP 2819-2836; as `FluxIdentity`, with the horizon flux): at
every age `r ∈ [0, T]`, for `w` in the state space and every cylinder test `φ`, the tested
right-hand side of the linearised equation is integrable on the cell and equals
`ν ∫ w Δφ + ∫ (B(r) w)·∇φ`. -/
def FluxIdentityOn {ν : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {T : ℝ} {hT : 0 ≤ T}
    (P : ActualTrainFluxPathOn hm tr hT) : Prop :=
  ∀ r ∈ Icc (0 : ℝ) T, ∀ w : ActualVorticity (c := c) (m := m) hm, ∀ φ : ℝ × ℝ → ℝ,
    UnforcedLeray.B0579.IsCylTest c φ →
      IntegrableOn (flowIntegrand tr (cplx (vortFn hm w)) (stripVel hm w) r φ)
          (UnforcedLeray.B0579.cell c) ∧
        ∫ x in UnforcedLeray.B0579.cell c, flowIntegrand tr (cplx (vortFn hm w)) (stripVel hm w) r φ x
          = (((ν * (∫ x in UnforcedLeray.B0579.cell c, vortFn hm w x * lapP φ x) +
              ∫ x in UnforcedLeray.B0579.cell c,
                (fluxFn (actualTrainFluxBOn hm P r w) 0 x * UnforcedLeray.B0579.pd 0 φ x +
                  fluxFn (actualTrainFluxBOn hm P r w) 1 x * UnforcedLeray.B0579.pd 1 φ x)
              : ℝ)) : ℂ)

/-- **Mild solution is weak, integrated form, horizon data** (as `MildIntegrated`): if the heat
family satisfies `ScaledHeatWeak ν H`, then for every `a ≥ 0` the path `ω(s) = D.evolution s a w`
(`D = horizonData hm P H`) satisfies for `s ∈ [a, a+1]`
`∫ ω(s) φ = ∫ w φ + ∫_a^s (ν ∫ ω(r) Δφ + ∫ (B(r) ω(r))·∇φ) dr` with `B = actualTrainFluxBOn hm P`. -/
def MildIntegratedOn {ν : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {T : ℝ} {hT : 0 ≤ T}
    (P : ActualTrainFluxPathOn hm tr hT) (H : WeightedHeatStripSupplier (c := c) (m := m) hm) :
    Prop :=
  ScaledHeatWeak hm ν H →
  ∀ a : ℝ, 0 ≤ a → ∀ w : ActualVorticity (c := c) (m := m) hm, ∀ φ : ℝ × ℝ → ℝ,
    UnforcedLeray.B0579.IsCylTest c φ → ∀ s ∈ Icc a (a + 1),
      ∫ x in UnforcedLeray.B0579.cell c,
          vortFn hm ((horizonData hm P H).evolution s a w) x * φ x =
        (∫ x in UnforcedLeray.B0579.cell c, vortFn hm w x * φ x) +
          ∫ r in a..s,
            (ν * (∫ x in UnforcedLeray.B0579.cell c,
                vortFn hm ((horizonData hm P H).evolution r a w) x * lapP φ x) +
              ∫ x in UnforcedLeray.B0579.cell c,
                (fluxFn (actualTrainFluxBOn hm P r ((horizonData hm P H).evolution r a w)) 0 x *
                    UnforcedLeray.B0579.pd 0 φ x +
                  fluxFn (actualTrainFluxBOn hm P r ((horizonData hm P H).evolution r a w)) 1 x *
                    UnforcedLeray.B0579.pd 1 φ x))

/-- **Continuity fields, horizon data** (as `StripContinuity`): on a unit strip `[a, a+1] ⊆ [0, T]`
the path is strongly continuous in `X_{m,c}` (complex norm), and its tested right-hand side is
interval integrable. -/
def StripContinuityOn {ν : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {T : ℝ} {hT : 0 ≤ T}
    (P : ActualTrainFluxPathOn hm tr hT) (H : WeightedHeatStripSupplier (c := c) (m := m) hm) :
    Prop :=
  ∀ a : ℝ, 0 ≤ a → a + 1 ≤ T → ∀ w : ActualVorticity (c := c) (m := m) hm,
    (∀ s ∈ Icc a (a + 1),
      Tendsto (fun s' => xNorm c m
          (cplx (vortFn hm ((horizonData hm P H).evolution s' a w)) -
            cplx (vortFn hm ((horizonData hm P H).evolution s a w))))
        (𝓝[Icc a (a + 1)] s) (𝓝 0)) ∧
    (∀ φ : ℝ × ℝ → ℝ, UnforcedLeray.B0579.IsCylTest c φ → ∀ s ∈ Icc a (a + 1),
      IntervalIntegrable (fun r => ∫ x in UnforcedLeray.B0579.cell c,
        flowIntegrand tr (cplx (vortFn hm ((horizonData hm P H).evolution r a w)))
          (stripVel hm ((horizonData hm P H).evolution r a w)) r φ x) volume a s)

/-- The horizon evolution on every unit strip `[a, a+1] ⊆ [0, T]` is a weak linearised flow. -/
def StripWeakLpOn {ν : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {T : ℝ} {hT : 0 ≤ T}
    (P : ActualTrainFluxPathOn hm tr hT) (H : WeightedHeatStripSupplier (c := c) (m := m) hm) :
    Prop :=
  ∀ a : ℝ, 0 ≤ a → a + 1 ≤ T → ∀ w : ActualVorticity (c := c) (m := m) hm,
    IsLinFlowOn ν c m tr a (a + 1) (cplx (vortFn hm w))
      (fun r => cplx (vortFn hm ((horizonData hm P H).evolution r a w)))
      (fun r => stripVel hm ((horizonData hm P H).evolution r a w))

end Horizon

/-! ## Universal forms -/

/-- `T21/3/5` (horizon form). -/
def FluxIdentityOnAll : Prop :=
  ∀ (ν c m : ℝ) [Fact (0 < c)] (hm : 1 ≤ m) (tr : UnforcedLeray.B0140.TrainSol ν c) (T : ℝ)
    (hT : 0 ≤ T) (P : ActualTrainFluxPathOn (c := c) (m := m) (ν := ν) hm tr hT),
    Regime ν c m → FluxIdentityOn hm tr P

/-- `T21/3/6` (horizon form). -/
def MildIntegratedOnAll : Prop :=
  ∀ (ν c m : ℝ) [Fact (0 < c)] (hm : 1 ≤ m) (tr : UnforcedLeray.B0140.TrainSol ν c) (T : ℝ)
    (hT : 0 ≤ T) (P : ActualTrainFluxPathOn (c := c) (m := m) (ν := ν) hm tr hT)
    (H : WeightedHeatStripSupplier (c := c) (m := m) hm), Regime ν c m →
    MildIntegratedOn hm tr P H

/-- `T21/3/7` (horizon form). -/
def StripContinuityOnAll : Prop :=
  ∀ (ν c m : ℝ) [Fact (0 < c)] (hm : 1 ≤ m) (tr : UnforcedLeray.B0140.TrainSol ν c) (T : ℝ)
    (hT : 0 ≤ T) (P : ActualTrainFluxPathOn (c := c) (m := m) (ν := ν) hm tr hT)
    (H : WeightedHeatStripSupplier (c := c) (m := m) hm), Regime ν c m →
    StripContinuityOn hm tr P H

/-- **Locality of the horizon evolutions** (`T21/3/9/5`; SP 2819-2836, the evolution is unique):
two horizon evolutions with the same heat family agree at all ages `0 ≤ s ≤ τ` inside both
horizons (their coefficients agree there, `actualTrainFluxBOn_congr`, and the strip Volterra
equation has unique continuous solutions, `VolterraData.eqOn_stripEvolution`). -/
def HorizonLocality : Prop :=
  ∀ (ν c m : ℝ) [Fact (0 < c)] (hm : 1 ≤ m) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (H : WeightedHeatStripSupplier (c := c) (m := m) hm) (T T' : ℝ) (hT : 0 ≤ T) (hT' : 0 ≤ T')
    (P : ActualTrainFluxPathOn (c := c) (m := m) (ν := ν) hm tr hT)
    (P' : ActualTrainFluxPathOn (c := c) (m := m) (ν := ν) hm tr hT') (s τ : ℝ),
    0 ≤ s → s ≤ τ → τ ≤ T → τ ≤ T' →
      (horizonData hm P H).evolution τ s = (horizonData hm P' H).evolution τ s

/-! ## The flux identity from the accepted lemmas of `T21/3/5` -/

section FluxId

variable {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)

/-- The flux identity at one age `r ≥ 0` for any flux operator `F` with the physical formula
(the proof of `fluxIdentity_of`, with `F` in place of `actualTrainFluxB hm P r`). -/
theorem fluxIdentityAt_of {ν : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {r : ℝ} (hr : 0 ≤ r)
    (F : ActualVorticity (c := c) (m := m) hm →L[ℝ] ActualFlux (c := c) (m := m))
    (h1 : EcSmoothPeriodic (c := c) tr) (h2 : FluxIntOmega (m := m) hm tr)
    (h3 : FluxIntVel (m := m) hm tr) (hBS : BiotSavartField (c := c) (m := m) hm)
    (h4 : ∀ (w : ActualVorticity (c := c) (m := m) hm) (φ : ℝ × ℝ → ℝ),
      UnforcedLeray.B0579.IsCylTest c φ →
      (fun x => ((fluxFn (F w) 0 x * UnforcedLeray.B0579.pd 0 φ x +
          fluxFn (F w) 1 x * UnforcedLeray.B0579.pd 1 φ x : ℝ) : ℂ)) =ᵐ[volume.restrict
          (UnforcedLeray.B0579.cell c)]
        fun x => cplx (vortFn hm w) x *
            ((tr.v r x 0 * UnforcedLeray.B0579.pd 0 φ x + tr.v r x 1 * UnforcedLeray.B0579.pd 1 φ x : ℝ) : ℂ) +
          (UnforcedLeray.B0238.Ec tr r x : ℂ) *
            (stripVel hm w x 0 * (UnforcedLeray.B0579.pd 0 φ x : ℂ) +
              stripVel hm w x 1 * (UnforcedLeray.B0579.pd 1 φ x : ℂ)))
    (w : ActualVorticity (c := c) (m := m) hm) (φ : ℝ × ℝ → ℝ)
    (hφ : UnforcedLeray.B0579.IsCylTest c φ) :
    IntegrableOn (flowIntegrand tr (cplx (vortFn hm w)) (stripVel hm w) r φ)
        (UnforcedLeray.B0579.cell c) ∧
      ∫ x in UnforcedLeray.B0579.cell c, flowIntegrand tr (cplx (vortFn hm w)) (stripVel hm w) r φ x
        = (((ν * (∫ x in UnforcedLeray.B0579.cell c, vortFn hm w x * lapP φ x) +
            ∫ x in UnforcedLeray.B0579.cell c,
              (fluxFn (F w) 0 x * UnforcedLeray.B0579.pd 0 φ x +
                fluxFn (F w) 1 x * UnforcedLeray.B0579.pd 1 φ x)
            : ℝ)) : ℂ) := by
  obtain ⟨hE, hEp⟩ := h1 r hr
  have hψ := isCylTest_mul_of hE hEp hφ
  have hdiv := (hBS w).2.1 _ hψ
  have hEd : Differentiable ℝ (UnforcedLeray.B0238.Ec tr r) := hE.differentiable (by simp)
  have hφd : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
  obtain ⟨hA1, hA2⟩ := h2 r hr w φ hφ
  obtain ⟨hB1, hB2⟩ := h3 hBS r hr w φ hφ
  have hdiv' : ∫ x in UnforcedLeray.B0579.cell c,
      ((stripVel hm w x 0 * (UnforcedLeray.B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x : ℂ) +
          stripVel hm w x 1 * (UnforcedLeray.B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℂ)) * (φ x : ℂ)
        + (UnforcedLeray.B0238.Ec tr r x : ℂ) *
          (stripVel hm w x 0 * (UnforcedLeray.B0579.pd 0 φ x : ℂ) +
            stripVel hm w x 1 * (UnforcedLeray.B0579.pd 1 φ x : ℂ))) = 0 := by
    rw [← hdiv]
    apply integral_congr_ae
    refine Filter.Eventually.of_forall (fun x => ?_)
    show _ = stripVel hm w x 0 * ((UnforcedLeray.B0579.pd 0 (fun y => UnforcedLeray.B0238.Ec tr r y * φ y) x : ℝ) : ℂ) + _
    rw [pd_mul_of_diff 0 hEd hφd, pd_mul_of_diff 1 hEd hφd]
    push_cast
    ring
  rw [integral_add hB1 hB2] at hdiv'
  have hfi : flowIntegrand tr (cplx (vortFn hm w)) (stripVel hm w) r φ = fun x =>
      ((ν : ℂ) * (cplx (vortFn hm w) x * (lapP φ x : ℂ)) +
        cplx (vortFn hm w) x *
          ((tr.v r x 0 * UnforcedLeray.B0579.pd 0 φ x + tr.v r x 1 * UnforcedLeray.B0579.pd 1 φ x : ℝ) : ℂ)) -
      (stripVel hm w x 0 * (UnforcedLeray.B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x : ℂ) +
          stripVel hm w x 1 * (UnforcedLeray.B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℂ)) * (φ x : ℂ) := by
    funext x
    unfold flowIntegrand
    push_cast
    ring
  have hAA : IntegrableOn (fun x => (ν : ℂ) * (cplx (vortFn hm w) x * (lapP φ x : ℂ)) +
        cplx (vortFn hm w) x *
          ((tr.v r x 0 * UnforcedLeray.B0579.pd 0 φ x + tr.v r x 1 * UnforcedLeray.B0579.pd 1 φ x : ℝ) : ℂ))
      (UnforcedLeray.B0579.cell c) := (hA1.const_mul (ν : ℂ)).add hA2
  constructor
  · rw [hfi]
    exact hAA.sub hB1
  · rw [hfi, integral_sub hAA hB1,
      integral_add (hA1.const_mul (ν : ℂ)) hA2, integral_const_mul]
    have hB : ∫ x in UnforcedLeray.B0579.cell c,
        (stripVel hm w x 0 * (UnforcedLeray.B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x : ℂ) +
          stripVel hm w x 1 * (UnforcedLeray.B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℂ)) * (φ x : ℂ)
        = -∫ x in UnforcedLeray.B0579.cell c, (UnforcedLeray.B0238.Ec tr r x : ℂ) *
          (stripVel hm w x 0 * (UnforcedLeray.B0579.pd 0 φ x : ℂ) +
            stripVel hm w x 1 * (UnforcedLeray.B0579.pd 1 φ x : ℂ)) :=
      eq_neg_of_add_eq_zero_left hdiv'
    rw [hB]
    have e1 : ∫ x in UnforcedLeray.B0579.cell c, cplx (vortFn hm w) x * (lapP φ x : ℂ) =
        ((∫ x in UnforcedLeray.B0579.cell c, vortFn hm w x * lapP φ x : ℝ) : ℂ) := by
      have h : ∀ x, cplx (vortFn hm w) x * (lapP φ x : ℂ) = ((vortFn hm w x * lapP φ x : ℝ) : ℂ) :=
        fun x => by simp [cplx]
      simp only [h]
      exact integral_complex_ofReal
    have e2 : ∫ x in UnforcedLeray.B0579.cell c,
        ((fluxFn (F w) 0 x * UnforcedLeray.B0579.pd 0 φ x +
          fluxFn (F w) 1 x * UnforcedLeray.B0579.pd 1 φ x : ℝ) : ℂ) =
        ((∫ x in UnforcedLeray.B0579.cell c,
          (fluxFn (F w) 0 x * UnforcedLeray.B0579.pd 0 φ x +
          fluxFn (F w) 1 x * UnforcedLeray.B0579.pd 1 φ x) : ℝ) : ℂ) :=
      integral_complex_ofReal
    rw [Complex.ofReal_add, Complex.ofReal_mul, ← e1, ← e2,
      integral_congr_ae (h4 w φ hφ), integral_add hA2 hB2]
    ring

/-- The physical formula for the horizon flux at an age `r ∈ [0, T]` (the proof of
`fluxFnAe_all`, through `actualTrainFluxBOn_eq_actual`). -/
theorem fluxFnAeOn {ν : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {T : ℝ} {hT : 0 ≤ T}
    (P : ActualTrainFluxPathOn hm tr hT) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) T)
    (w : ActualVorticity (c := c) (m := m) hm) (φ : ℝ × ℝ → ℝ) :
    (fun x => ((fluxFn (actualTrainFluxBOn hm P r w) 0 x * UnforcedLeray.B0579.pd 0 φ x +
        fluxFn (actualTrainFluxBOn hm P r w) 1 x * UnforcedLeray.B0579.pd 1 φ x : ℝ) : ℂ))
      =ᵐ[volume.restrict (UnforcedLeray.B0579.cell c)]
      fun x => cplx (vortFn hm w) x *
          ((tr.v r x 0 * UnforcedLeray.B0579.pd 0 φ x + tr.v r x 1 * UnforcedLeray.B0579.pd 1 φ x : ℝ) : ℂ) +
        (UnforcedLeray.B0238.Ec tr r x : ℂ) *
          (stripVel hm w x 0 * (UnforcedLeray.B0579.pd 0 φ x : ℂ) +
            stripVel hm w x 1 * (UnforcedLeray.B0579.pd 1 φ x : ℂ)) := by
  rw [actualTrainFluxBOn_eq_actual hm P hr]
  have h0 := L4Aux.fluxFn_ae hm (UnforcedLeray.B0238.Vc tr r) (UnforcedLeray.B0238.Ec tr r)
    (continuous_actualTrainVelocity_slice tr hr.1) (continuous_actualTrainCurl_slice tr hr.1)
    P.hCv P.hCE (P.velocity_bound ⟨r, hr⟩) (P.weighted_curl_bound ⟨r, hr⟩) w 0
  have h1 := L4Aux.fluxFn_ae hm (UnforcedLeray.B0238.Vc tr r) (UnforcedLeray.B0238.Ec tr r)
    (continuous_actualTrainVelocity_slice tr hr.1) (continuous_actualTrainCurl_slice tr hr.1)
    P.hCv P.hCE (P.velocity_bound ⟨r, hr⟩) (P.weighted_curl_bound ⟨r, hr⟩) w 1
  filter_upwards [h0, h1] with x hx0 hx1
  simp only [actualTrainFluxAtNonneg]
  rw [hx0, hx1]
  unfold stripVel cplx vortFn
  simp only [UnforcedLeray.B0238.Vc]
  push_cast
  ring

end FluxId

/-- **`FluxIdentityOnAll` from the accepted lemmas** `EcSmoothPeriodic` (`T21/3/5/1`),
`FluxIntOmega` (`/5/2`), `FluxIntVel` (`/5/3`) and `BiotSavartFieldAll` (`T21/3/4`). -/
theorem fluxIdentityOn_of
    (h1 : ∀ (ν c : ℝ) [Fact (0 < c)] (tr : UnforcedLeray.B0140.TrainSol ν c),
      EcSmoothPeriodic (c := c) tr)
    (h2 : ∀ (ν c m : ℝ) [Fact (0 < c)] (hm : 1 ≤ m) (tr : UnforcedLeray.B0140.TrainSol ν c),
      FluxIntOmega (c := c) (m := m) hm tr)
    (h3 : ∀ (ν c m : ℝ) [Fact (0 < c)] (hm : 1 ≤ m) (tr : UnforcedLeray.B0140.TrainSol ν c),
      FluxIntVel (c := c) (m := m) hm tr)
    (h4 : BiotSavartFieldAll) : FluxIdentityOnAll := by
  intro ν c m _ hm tr T hT P _ r hr w φ hφ
  exact fluxIdentityAt_of hm tr hr.1 (actualTrainFluxBOn hm P r) (h1 ν c tr) (h2 ν c m hm tr)
    (h3 ν c m hm tr) (h4 c m hm) (fun w' φ' _ => fluxFnAeOn hm tr P hr w' φ') w φ hφ

/-! ## The strip flows of the horizon data -/

/-- **The horizon strip flows from the four parts** (the proof of `stripWeakAssemblyFromParts`,
`Clock/Existence/StripWeakAssembly.lean`, on the horizon data). -/
def StripWeakAssemblyOnFromParts : Prop :=
  BiotSavartFieldAll → FluxIdentityOnAll → MildIntegratedOnAll → StripContinuityOnAll →
  ∀ (ν c m : ℝ) [Fact (0 < c)] (hm : 1 ≤ m) (tr : UnforcedLeray.B0140.TrainSol ν c) (T : ℝ)
    (hT : 0 ≤ T) (P : ActualTrainFluxPathOn (c := c) (m := m) (ν := ν) hm tr hT)
    (H : WeightedHeatStripSupplier (c := c) (m := m) hm), Regime ν c m →
    ScaledHeatWeak hm ν H → StripWeakLpOn hm tr P H

theorem stripWeakAssemblyOnFromParts : StripWeakAssemblyOnFromParts := by
  intro hB hF hM hC ν c m inst hm tr T hT P H hR hH
  refine fun a ha haT w => ?_
  have hMild := hM ν c m hm tr T hT P H hR hH
  have hStrip := hC ν c m hm tr T hT P H hR
  have hBS := hB c m hm
  have e1 : ∀ (g : ℝ × ℝ → ℝ) (φ : ℝ × ℝ → ℝ),
      ∫ x in UnforcedLeray.B0579.cell c, cplx g x * (φ x : ℂ) =
        ((∫ x in UnforcedLeray.B0579.cell c, g x * φ x : ℝ) : ℂ) := by
    intro g φ
    have h : ∀ x, cplx g x * (φ x : ℂ) = ((g x * φ x : ℝ) : ℂ) := fun x => by simp [cplx]
    simp only [h]
    exact integral_complex_ofReal
  constructor
  · show cplx (vortFn hm ((horizonData hm P H).evolution a a w)) =ᵐ[volume.restrict
      (UnforcedLeray.B0579.cell c)] cplx (vortFn hm w)
    rw [horizonData_initial]
  · intro s _
    exact MeasureTheory.MemLp.ofReal (Lp.memLp ((horizonData hm P H).evolution s a w).1)
  · intro s hs
    exact (hStrip a ha haT w).1 s hs
  · intro s _
    exact hBS _
  · intro φ hφ r hr
    exact (hF ν c m hm tr T hT P hR r ⟨le_trans ha hr.1, le_trans hr.2 haT⟩ _ φ hφ).1
  · intro φ hφ s hs
    exact (hStrip a ha haT w).2 φ hφ s hs
  · intro φ hφ s hs
    have hsa : a ≤ s := hs.1
    have hreal := hMild a ha w φ hφ s hs
    have hint : ∫ r in a..s, (∫ x in UnforcedLeray.B0579.cell c,
        flowIntegrand tr (cplx (vortFn hm ((horizonData hm P H).evolution r a w)))
          (stripVel hm ((horizonData hm P H).evolution r a w)) r φ x)
        = ((∫ r in a..s,
            (ν * (∫ x in UnforcedLeray.B0579.cell c,
                vortFn hm ((horizonData hm P H).evolution r a w) x * lapP φ x) +
              ∫ x in UnforcedLeray.B0579.cell c,
                (fluxFn (actualTrainFluxBOn hm P r ((horizonData hm P H).evolution r a w)) 0 x *
                    UnforcedLeray.B0579.pd 0 φ x +
                  fluxFn (actualTrainFluxBOn hm P r ((horizonData hm P H).evolution r a w)) 1 x *
                    UnforcedLeray.B0579.pd 1 φ x)) : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]
      apply intervalIntegral.integral_congr
      intro r hr
      rw [Set.uIcc_of_le hsa] at hr
      exact (hF ν c m hm tr T hT P hR r
        ⟨le_trans ha hr.1, le_trans (le_trans hr.2 hs.2) haT⟩ _ φ hφ).2
    show ∫ x in UnforcedLeray.B0579.cell c,
        cplx (vortFn hm ((horizonData hm P H).evolution s a w)) x * (φ x : ℂ) =
        (∫ x in UnforcedLeray.B0579.cell c, cplx (vortFn hm w) x * (φ x : ℂ)) +
          ∫ r in a..s, (∫ x in UnforcedLeray.B0579.cell c,
            flowIntegrand tr (cplx (vortFn hm ((horizonData hm P H).evolution r a w)))
              (stripVel hm ((horizonData hm P H).evolution r a w)) r φ x)
    rw [hint, e1, e1, hreal, Complex.ofReal_add]

/-! ## One evolution family from the horizons -/

section Family

variable {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)

/-- The evolution family of the actual train: at final age `τ` use the horizon `⌈τ⌉₊`. -/
def horizonEvolution {ν : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c}
    (Pn : ∀ n : ℕ, ActualTrainFluxPathOn (c := c) (m := m) (ν := ν) hm tr (Nat.cast_nonneg n))
    (H : WeightedHeatStripSupplier (c := c) (m := m) hm) (τ s : ℝ) :
    ActualVorticity (c := c) (m := m) hm →L[ℝ] ActualVorticity (c := c) (m := m) hm :=
  (horizonData hm (Pn ⌈τ⌉₊) H).evolution τ s

theorem horizonEvolution_eq (hLoc : HorizonLocality) {ν : ℝ}
    {tr : UnforcedLeray.B0140.TrainSol ν c}
    (Pn : ∀ n : ℕ, ActualTrainFluxPathOn (c := c) (m := m) (ν := ν) hm tr (Nat.cast_nonneg n))
    (H : WeightedHeatStripSupplier (c := c) (m := m) hm) {n : ℕ} {s τ : ℝ} (hs : 0 ≤ s)
    (hsτ : s ≤ τ) (hτn : τ ≤ n) :
    horizonEvolution hm Pn H τ s = (horizonData hm (Pn n) H).evolution τ s :=
  hLoc ν c m hm tr H _ _ _ _ (Pn ⌈τ⌉₊) (Pn n) s τ hs hsτ (Nat.le_ceil τ) hτn

theorem horizonEvolution_comp (hLoc : HorizonLocality) {ν : ℝ}
    {tr : UnforcedLeray.B0140.TrainSol ν c}
    (Pn : ∀ n : ℕ, ActualTrainFluxPathOn (c := c) (m := m) (ν := ν) hm tr (Nat.cast_nonneg n))
    (H : WeightedHeatStripSupplier (c := c) (m := m) hm) {s r τ : ℝ} (hs : 0 ≤ s)
    (hsr : s ≤ r) (hrτ : r ≤ τ) (w : ActualVorticity (c := c) (m := m) hm) :
    horizonEvolution hm Pn H τ r (horizonEvolution hm Pn H r s w) =
      horizonEvolution hm Pn H τ s w := by
  have hτ : τ ≤ (⌈τ⌉₊ : ℝ) := Nat.le_ceil τ
  rw [horizonEvolution_eq hm hLoc Pn H (n := ⌈τ⌉₊) (hs.trans hsr) hrτ hτ,
    horizonEvolution_eq hm hLoc Pn H (n := ⌈τ⌉₊) hs hsr (hrτ.trans hτ),
    horizonEvolution_eq hm hLoc Pn H (n := ⌈τ⌉₊) hs (hsr.trans hrτ) hτ]
  exact (horizonData hm (Pn ⌈τ⌉₊) H).evolution_apply_comp
    (horizonData_compatible hm (Pn ⌈τ⌉₊) H) hsr hrτ w

end Family

/-- `T21/3/9` (horizon form): from the horizon strip flows (one horizon path for each integer
horizon) to the cocycle of complex-data flows (`ComplexStripFamily`). -/
def StripBookkeepingOn : Prop :=
  ∀ (ν c m : ℝ) [Fact (0 < c)] (hm : 1 ≤ m) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (H : WeightedHeatStripSupplier (c := c) (m := m) hm)
    (Pn : ∀ n : ℕ, ActualTrainFluxPathOn (c := c) (m := m) (ν := ν) hm tr (Nat.cast_nonneg n)),
    Regime ν c m → (∀ n : ℕ, StripWeakLpOn hm tr (Pn n) H) → ComplexStripFamily ν c m tr

/-- **Bookkeeping on horizons** (the proof of `stripBookkeeping_of`, with the evolution family
`horizonEvolution`; its strip values are those of the horizon `⌈a + 1⌉₊` and its cocycle law
comes from `HorizonLocality`). -/
theorem stripBookkeepingOn_of (hL : LinFlowComb) (hR : ActualRepresentation) (hG : GoodCStable)
    (hInj : VortFnInj) (hCongr : FlowCongrAE) (hLoc : HorizonLocality) : StripBookkeepingOn := by
  intro ν c m _ hm tr H Pn hReg hstrip
  classical
  have hrep : ∀ f, GoodC c m f → ∃ wr wi : ActualVorticity (c := c) (m := m) hm,
      f =ᵐ[volume.restrict (B0579.cell c)]
        fun x => cplx (vortFn hm wr) x + Complex.I * cplx (vortFn hm wi) x :=
    fun f hf => hR c m hm f hf
  choose! wr wi hrepw using hrep
  obtain ⟨E, hE⟩ : ∃ E : ℝ → ℝ → ActualVorticity (c := c) (m := m) hm →
      ActualVorticity (c := c) (m := m) hm,
      ∀ r a w, E r a w = horizonEvolution hm Pn H r a w :=
    ⟨fun r a w => horizonEvolution hm Pn H r a w, fun _ _ _ => rfl⟩
  have hW : ∀ r a f, GoodC c m f → stripW hm E wr wi r a f =
      fun x => cplx (vortFn hm (E r a (wr f))) x + Complex.I * cplx (vortFn hm (E r a (wi f))) x := by
    intro r a f hf
    unfold stripW
    simp [hf]
  have hU : ∀ r a f, GoodC c m f → stripU hm E wr wi r a f =
      fun x j => stripVel hm (E r a (wr f)) x j + Complex.I * stripVel hm (E r a (wi f)) x j := by
    intro r a f hf
    unfold stripU
    simp [hf]
  have hgood : ∀ a r : ℝ, ∀ f, GoodC c m f → GoodC c m (stripW hm E wr wi r a f) := by
    intro a r f hf
    rw [hW r a f hf]
    exact hG.2 c m (cplx (vortFn hm (E r a (wr f)))) (cplx (vortFn hm (E r a (wi f))))
      (hG.1 c m hm _) (hG.1 c m hm _)
  refine ⟨stripW hm E wr wi, stripU hm E wr wi, ?_, fun a r _ _ f hf => hgood a r f hf, ?_⟩
  · intro a ha f hf
    have hn : a + 1 ≤ ((⌈a + 1⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have hEq : ∀ s ∈ Icc a (a + 1), ∀ w, E s a w =
        (horizonData hm (Pn ⌈a + 1⌉₊) H).evolution s a w := by
      intro s hs w
      rw [hE]
      exact congrArg (fun L => L w)
        (horizonEvolution_eq hm hLoc Pn H ha hs.1 (hs.2.trans hn))
    have h1 := hL ν c m tr a (a + 1) _ _ _ _ _ _ (hstrip ⌈a + 1⌉₊ a ha hn (wr f))
      (hstrip ⌈a + 1⌉₊ a ha hn (wi f))
    refine hCongr ν c m tr a (a + 1) _ f _ _ _ _ (by linarith) h1 (hrepw f hf).symm ?_ ?_
    · intro s hs
      refine Filter.EventuallyEq.of_eq ?_
      rw [hW s a f hf, hEq s hs, hEq s hs]
    · intro s hs
      refine Filter.EventuallyEq.of_eq ?_
      rw [hU s a f hf, hEq s hs, hEq s hs]
  · intro a r T ha har hrT f hf
    have hg := hgood a r f hf
    set g := stripW hm E wr wi r a f with hg_def
    have hgeq : g = fun x => cplx (vortFn hm (E r a (wr f))) x +
        Complex.I * cplx (vortFn hm (E r a (wi f))) x := hW r a f hf
    have hae1 := (hrepw g hg).symm
    have hae : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
        cplx (vortFn hm (wr g)) x + Complex.I * cplx (vortFn hm (wi g)) x =
          cplx (vortFn hm (E r a (wr f))) x + Complex.I * cplx (vortFn hm (E r a (wi f))) x := by
      filter_upwards [hae1] with x hx
      exact hx.trans (congrFun hgeq x)
    have hre : vortFn hm (wr g) =ᵐ[volume.restrict (B0579.cell c)]
        vortFn hm (E r a (wr f)) := by
      filter_upwards [hae] with x hx
      have := congrArg Complex.re hx
      simpa [cplx] using this
    have him : vortFn hm (wi g) =ᵐ[volume.restrict (B0579.cell c)]
        vortFn hm (E r a (wi f)) := by
      filter_upwards [hae] with x hx
      have := congrArg Complex.im hx
      simpa [cplx] using this
    have hwr : wr g = E r a (wr f) := hInj c m hm _ _ hre
    have hwi : wi g = E r a (wi f) := hInj c m hm _ _ him
    have c1 : ∀ w, E T r (E r a w) = E T a w := by
      intro w
      rw [hE, hE, hE]
      exact horizonEvolution_comp hm hLoc Pn H ha har hrT w
    refine ⟨?_, ?_⟩
    · rw [hW T a f hf, hW T r g hg, hwr, hwi, c1, c1]
    · rw [hU T a f hf, hU T r g hg, hwr, hwi, c1, c1]

/-! ## Conditional assembly of `FullFlowExistsSmall` -/

/-- **Conditional assembly of the target `FullFlowExistsSmall`** (`PartIII-a:T21/3`): finite-horizon
train bounds give one horizon path per integer horizon (`FluxPathExistsAll`), the rescaled heat
family (`UnitHeatWeakActual`, `ScaleSupplier`), the horizon strip flows
(`stripWeakAssemblyOnFromParts`), the complex family (`StripBookkeepingOn`) and the gluing
(`fullFlowExists_of_family`). -/
theorem fullFlowExistsSmall_of
    (h1 : FluxPathExistsAll) (h2 : UnitHeatWeakActual) (h3 : ScaleSupplier)
    (h4 : BiotSavartFieldAll) (h5 : FluxIdentityOnAll) (h6 : MildIntegratedOnAll)
    (h7 : StripContinuityOnAll) (h9 : StripBookkeepingOn)
    (hApp : FlowAppend) (hCongr : FlowCongrAE) (hGlob : FlowGlobal) :
    FullFlowExistsSmall := by
  intro m hm8 ν hν hν1 tr hB
  have hR : Regime ν (ν ^ (-2 : ℝ)) m := ⟨hν, hν1, rfl, hm8⟩
  have : Fact (0 < ν ^ (-2 : ℝ)) := ⟨hR.pos_c⟩
  have hm1 : 1 ≤ m := hR.one_le_m
  have hP : ∀ n : ℕ, Nonempty (ActualTrainFluxPathOn (c := ν ^ (-2 : ℝ)) (m := m) (ν := ν) hm1 tr
      (Nat.cast_nonneg n)) :=
    fun n => h1 ν (ν ^ (-2 : ℝ)) m hm1 tr hR hB n (Nat.cast_nonneg n)
  let Pn : ∀ n : ℕ, ActualTrainFluxPathOn (c := ν ^ (-2 : ℝ)) (m := m) (ν := ν) hm1 tr
      (Nat.cast_nonneg n) := fun n => Classical.choice (hP n)
  obtain ⟨H, hH⟩ := h3 ν (ν ^ (-2 : ℝ)) m hR.one_le_c hm1 hν hν1
    (h2 (ν ^ (-2 : ℝ)) m hR.one_le_c hm1)
  have hS : ∀ n : ℕ, StripWeakLpOn hm1 tr (Pn n) H := fun n =>
    stripWeakAssemblyOnFromParts h4 h5 h6 h7 ν (ν ^ (-2 : ℝ)) m hm1 tr n (Nat.cast_nonneg n)
      (Pn n) H hR hH
  exact fullFlowExists_of_family hApp hCongr hGlob tr (h9 ν (ν ^ (-2 : ℝ)) m hm1 tr H Pn hR hS)

end UnforcedLeray.Short.IIIa.Exist
