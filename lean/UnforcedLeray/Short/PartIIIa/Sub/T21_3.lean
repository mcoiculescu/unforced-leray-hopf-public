import UnforcedLeray.Short.PartIIIa.Clock.Moving
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.PhysicalTrainVolterra
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.RealBiotSavart
import UnforcedLeray.Short.PartIIIa.Sub.T21_3_TrainBounds

/-!
# Part III-a, `PartIII-a:T21/3`: existence of the full evolution (conditional decomposition)

Source of record: `the November 2 reference manuscript`, lines 2819-2836
("The full forward train estimate", existence of `U(s,t)`: Volterra iteration around the actual
train, the heat semigroup and its divergence response as free part, `B(t)ω = vω + E K_cω` as the
bounded perturbation).

## Target

`FullFlowExistsSmall`: for every `m > 8`, every `0 < ν ≤ 1`, every actual train `tr` on the
cylinder of length `c = ν⁻²` with finite-horizon coefficient bounds
(`FiniteHorizonTrainBounds tr m`, `Sub/T21_3_TrainBounds.lean`), every age `t ≥ 0` and every
zero-circulation datum `f ∈ X_{m,c}` (complex valued) there is a weak linearised flow
`IsLinearisedFlow ν c m tr t f ω u`.
(`FullFlowExistsAll` of `Clock/Moving.lean` also asks for `ν > 1`; that range is never used since
`FullClockLongForward` only concerns small `ν`; the adapter `fullClockLongForward_of_small` below
turns `FullFlowExistsSmall` + `TrainBoundsSmall` + `LongForwardEstimate` into
`FullClockLongForward`.)

The coefficient bounds are on finite age horizons only: the weighted curl bound of the actual train
is not uniform in the age (`Sub/T21_3_TrainBounds.lean`, `PartIII-a:T21/3/1/org`), so the Volterra
evolution is built from horizon data and glued by locality (`Sub/T21_3_Horizon.lean`).

## Plan (each item is a Prop with a docstring; `fullFlowExistsSmall_of` in `Sub/T21_3_Horizon.lean`
assembles them)

1. `FluxPathExistsAll` (`T21/3/1`): finite-horizon train bounds give, for every horizon `T`, an
   `ActualTrainFluxPathOn` (bounds on `[0, T]`, strong continuity of the clamped `B`).
2. `UnitHeatWeakActual` (`T21/3/2`): the constructed physical heat family
   `actualPhysicalWeightedHeatStripSupplier` solves the weak heat / heat-divergence equations
   (diffusivity `1`).  `ScaleSupplier` (`T21/3/3`): time rescaling `t ↦ νt` gives the diffusivity-`ν`
   supplier `ScaledHeatWeak ν H`.
3. `stripWeakAssemblyOnFromParts` (proved in `Sub/T21_3_Horizon.lean`) from `BiotSavartField`
   (`/4`), `FluxIdentityOn` (`/5`), `MildIntegratedOn` (`/6`), `StripContinuityOn` (`/7`): the
   horizon Volterra evolution on a unit strip inside the horizon is a weak linearised flow.
4. `StripBookkeepingOn` (`T21/3/9`): the horizon evolutions agree on common ages
   (`HorizonLocality`), so they define one evolution family with the cocycle law; with real and
   imaginary parts this gives `ComplexStripFamily`.
5. `FlowAppend`, `FlowCongrAE`, `FlowGlobal` (`T21/3/10-12`): concatenation of flows on
   consecutive windows, a.e. invariance, passage to `[t, ∞)`.  With the cocycle law,
   `fullFlowExists_of_family` (proved here) glues the unit strips.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.Short.IIIa

/-! ## Linearised flows on a bounded window -/

/-- `ω` (with velocities `u`) is a weak linearised flow on the window `[t, T]` with datum `f`
at age `t`: the fields of `IsLinearisedFlow` (`Defs.lean`) restricted to `s ∈ [t, T]`. -/
structure IsLinFlowOn (ν c m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t T : ℝ)
    (f : ℝ × ℝ → ℂ) (ω : ℝ → ℝ × ℝ → ℂ) (u : ℝ → ℝ × ℝ → Fin 2 → ℂ) : Prop where
  initial : ω t =ᵐ[volume.restrict (B0579.cell c)] f
  memX : ∀ s ∈ Icc t T, MemLp (ω s) 2 (B0579.cellMeasure c m)
  strongCont : ∀ s ∈ Icc t T,
    Tendsto (fun s' => xNorm c m (ω s' - ω s)) (𝓝[Icc t T] s) (𝓝 0)
  biotSavart : ∀ s ∈ Icc t T, IsBiotSavart c (ω s) (u s)
  integrable : ∀ φ, B0579.IsCylTest c φ → ∀ r ∈ Icc t T,
    IntegrableOn (flowIntegrand tr (ω r) (u r) r φ) (B0579.cell c)
  timeIntegrable : ∀ φ, B0579.IsCylTest c φ → ∀ s ∈ Icc t T,
    IntervalIntegrable (fun r => ∫ x in B0579.cell c, flowIntegrand tr (ω r) (u r) r φ x)
      volume t s
  weak : ∀ φ, B0579.IsCylTest c φ → ∀ s ∈ Icc t T,
    ∫ x in B0579.cell c, ω s x * (φ x : ℂ) =
      (∫ x in B0579.cell c, f x * (φ x : ℂ)) +
        ∫ r in t..s, (∫ x in B0579.cell c, flowIntegrand tr (ω r) (u r) r φ x)

/-- Admissible data: `X_{m,c}` and zero circulation. -/
def GoodC (c m : ℝ) (f : ℝ × ℝ → ℂ) : Prop :=
  MemLp f 2 (B0579.cellMeasure c m) ∧ HasZeroCirculation c f

/-- **Concatenation of windows** (`T21/3/10`). If `ω` is a flow on `[t, T]` from `f` and on
`[T, T']` from its own value `ω T`, it is a flow on `[t, T']` from `f` (continuity at the junction
from the two one-sided limits; the time integral splits at `T`). -/
def FlowAppend : Prop :=
  ∀ (ν c m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t T T' : ℝ) (f : ℝ × ℝ → ℂ)
    (ω : ℝ → ℝ × ℝ → ℂ) (u : ℝ → ℝ × ℝ → Fin 2 → ℂ), t ≤ T → T ≤ T' →
    IsLinFlowOn ν c m tr t T f ω u → IsLinFlowOn ν c m tr T T' (ω T) ω u →
    IsLinFlowOn ν c m tr t T' f ω u

/-- **A.e. invariance** (`T21/3/11`). A flow stays a flow when, at every age of the window, the
vorticity and the velocity are changed on a null set of the cell (all fields only see
`∫_cell` of the fields, `cellMeasure ≪ volume.restrict cell`), and the datum on a null set. -/
def FlowCongrAE : Prop :=
  ∀ (ν c m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t T : ℝ) (f f' : ℝ × ℝ → ℂ)
    (ω ω' : ℝ → ℝ × ℝ → ℂ) (u u' : ℝ → ℝ × ℝ → Fin 2 → ℂ), t ≤ T →
    IsLinFlowOn ν c m tr t T f ω u → f =ᵐ[volume.restrict (B0579.cell c)] f' →
    (∀ s ∈ Icc t T, ω s =ᵐ[volume.restrict (B0579.cell c)] ω' s) →
    (∀ s ∈ Icc t T, u s =ᵐ[volume.restrict (B0579.cell c)] u' s) →
    IsLinFlowOn ν c m tr t T f' ω' u'

/-- **Passage to `[t, ∞)`** (`T21/3/12`). A flow on every window `[t, t + N + 1]` is a flow in the
sense of `IsLinearisedFlow` (each `s` has a window with `s < t + N + 1`, where the one-sided
neighbourhoods `𝓝[Icc]` and `𝓝[Ici]` agree). -/
def FlowGlobal : Prop :=
  ∀ (ν c m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t : ℝ) (f : ℝ × ℝ → ℂ)
    (ω : ℝ → ℝ × ℝ → ℂ) (u : ℝ → ℝ × ℝ → Fin 2 → ℂ),
    (∀ N : ℕ, IsLinFlowOn ν c m tr t (t + ((N + 1 : ℕ) : ℝ)) f ω u) →
    IsLinearisedFlow ν c m tr t f ω u

/-! ## The family of strip flows on complex data -/

/-- A cocycle of flows on unit windows (`T21/3/9` produces it from the Volterra evolution): for
every base age `a ≥ 0` and admissible datum `f`, `r ↦ W r a f` (velocity `U r a f`) is a flow on
`[a, a + 1]`; admissibility is preserved; and `W T a f = W T r (W r a f)` a.e. (same for `U`)
for `a ≤ r ≤ T`. -/
def ComplexStripFamily (ν c m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) : Prop :=
  ∃ (W : ℝ → ℝ → (ℝ × ℝ → ℂ) → (ℝ × ℝ → ℂ))
    (U : ℝ → ℝ → (ℝ × ℝ → ℂ) → (ℝ × ℝ → Fin 2 → ℂ)),
    (∀ a : ℝ, 0 ≤ a → ∀ f, GoodC c m f →
      IsLinFlowOn ν c m tr a (a + 1) f (fun r => W r a f) (fun r => U r a f)) ∧
    (∀ a r : ℝ, 0 ≤ a → a ≤ r → ∀ f, GoodC c m f → GoodC c m (W r a f)) ∧
    (∀ a r T : ℝ, 0 ≤ a → a ≤ r → r ≤ T → ∀ f, GoodC c m f →
      W T a f =ᵐ[volume.restrict (B0579.cell c)] W T r (W r a f) ∧
      U T a f =ᵐ[volume.restrict (B0579.cell c)] U T r (W r a f))

/-- **Gluing of unit strips** (proved from the three flow lemmas). -/
theorem fullFlowExists_of_family (hApp : FlowAppend) (hCongr : FlowCongrAE)
    (hGlob : FlowGlobal) {ν c m : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    (hF : ComplexStripFamily ν c m tr) : FullFlowExists ν c m tr := by
  obtain ⟨W, U, hstrip, hgood, hcoc⟩ := hF
  intro t ht f hf hz
  have hfg : GoodC c m f := ⟨hf, hz⟩
  refine ⟨fun r => W r t f, fun r => U r t f, hGlob ν c m tr t f _ _ ?_⟩
  intro N
  induction N with
  | zero => simpa using hstrip t ht f hfg
  | succ N ih =>
    have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    set a : ℝ := t + ((N + 1 : ℕ) : ℝ) with ha
    have ha0 : 0 ≤ a := by rw [ha]; push_cast; linarith
    have hta : t ≤ a := by rw [ha]; push_cast; linarith
    have hg := hgood t a ht hta f hfg
    have hs := hstrip a ha0 (W a t f) hg
    have hs' : IsLinFlowOn ν c m tr a (a + 1) (W a t f) (fun r => W r t f) (fun r => U r t f) := by
      refine hCongr ν c m tr a (a + 1) (W a t f) (W a t f) _ _ _ _ (by linarith) hs
        Filter.EventuallyEq.rfl ?_ ?_
      · intro s hs1
        exact (hcoc t a s ht hta hs1.1 f hfg).1.symm
      · intro s hs1
        exact (hcoc t a s ht hta hs1.1 f hfg).2.symm
    have hjoin : t + (((N + 1 + 1 : ℕ)) : ℝ) = a + 1 := by rw [ha]; push_cast; ring
    rw [hjoin]
    exact hApp ν c m tr t a (a + 1) f _ _ hta (by linarith) ih hs'

/-! ## Adapter to `FullClockLongForward` -/

/-- Existence of the full evolution in the range `0 < ν ≤ 1` (the only one used), for every train
with finite-horizon coefficient bounds (SP 2819-2836; `Sub/T21_3_TrainBounds.lean`). -/
def FullFlowExistsSmall : Prop :=
  ∀ m : ℝ, 8 < m → ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    FiniteHorizonTrainBounds tr m → FullFlowExists ν (ν ^ (-2 : ℝ)) m tr

/-- `FullClockLongForward` = small-`ν` existence + finite-horizon bounds of the BUC trains + the
long estimate.  `TrainBoundsSmall` (`Sub/T21_3_TrainBounds.lean`) is supplied by
`trainBoundsSmall_of` (task `PartIII-a:T21/3/1/2`, from the transverse tails SP 460-467). -/
theorem fullClockLongForward_of_small (hEx : FullFlowExistsSmall) (hTB : TrainBoundsSmall)
    (hL : LongForwardEstimate) : FullClockLongForward := by
  intro P hP m hm
  obtain ⟨b₀, hb₀⟩ := hL P hP m hm
  obtain ⟨ν₁, hν₁, hB⟩ := hTB m hm
  refine ⟨b₀, fun b hb => ?_⟩
  obtain ⟨C, ν₀, hν₀, h⟩ := hb₀ b hb
  refine ⟨C, min ν₀ (min ν₁ 1), lt_min hν₀ (lt_min hν₁ one_pos), fun ν hν tr htr =>
    ⟨hEx m hm ν hν.1 (hν.2.trans ((min_le_right _ _).trans (min_le_right _ _))) tr
      (hB ν hν.1 (hν.2.trans ((min_le_right _ _).trans (min_le_left _ _))) tr htr), ?_⟩⟩
  intro t s ht hts hb' f hf hz w u hw
  exact h ν ⟨hν.1, hν.2.trans (min_le_left _ _)⟩ tr htr t s ht hts hb' f hf hz w u hw

end UnforcedLeray.Short.IIIa.Exist
