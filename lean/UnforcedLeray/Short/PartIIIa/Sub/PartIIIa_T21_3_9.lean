import UnforcedLeray.Short.PartIIIa.Sub.T21_3_Strip

/-!
# Part III-a, `PartIII-a:T21/3/9`: bookkeeping from real strip flows to the complex family

Source of record: `the November 2 reference manuscript`, lines 2819-2836
(existence of `U(s,t)`; the Volterra evolution acts on real state-space elements and the
complex data are split into real and imaginary parts).

Decomposition of `StripBookkeeping` into five elementary facts (Props below, one task each) and the
assembly `stripBookkeeping_of`.  With `f = w_re + I w_im` (a.e.), `W r a f` is
`cplx(vortFn(E r a w_re)) + I cplx(vortFn(E r a w_im))` for `f` admissible and `0` otherwise,
`U` likewise with `stripVel`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.Short.IIIa
open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

/-- **Linearity of linearised flows** (SP 2819-2836): `IsLinFlowOn` is stable under
`(f, ω, u) ↦ (f₁ + I f₂, ω₁ + I ω₂, u₁ + I u₂)` (all the fields of `IsLinFlowOn` are linear:
`memX` by `MemLp.add`/`const_mul`, `strongCont` by the triangle inequality for `xNorm`,
`flowIntegrand` is `ℂ`-linear in `(ω, u)`, integrals are linear, and `IsBiotSavart` is linear
given `L²` integrability of the velocities against the test derivatives). -/
def LinFlowComb : Prop :=
  ∀ (ν c m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t T : ℝ)
    (f₁ f₂ : ℝ × ℝ → ℂ) (ω₁ ω₂ : ℝ → ℝ × ℝ → ℂ) (u₁ u₂ : ℝ → ℝ × ℝ → Fin 2 → ℂ),
    IsLinFlowOn ν c m tr t T f₁ ω₁ u₁ → IsLinFlowOn ν c m tr t T f₂ ω₂ u₂ →
    IsLinFlowOn ν c m tr t T (fun x => f₁ x + Complex.I * f₂ x)
      (fun s x => ω₁ s x + Complex.I * ω₂ s x) (fun s x j => u₁ s x j + Complex.I * u₂ s x j)

/-- **Real and imaginary parts of an admissible datum** (SP 2819-2836): an admissible `f`
(`GoodC`: `L²(cellMeasure)` with zero circulation) is a.e. `w_re + I w_im` with `w_re, w_im` in the
physical state space (`toLp` of `Re f`, `Im f`, using `integral_re`, `integral_im` for the zero
circulation and `mem_zeroCirculationSubmodule_iff`). -/
def ActualRepresentation : Prop :=
  ∀ (c m : ℝ) [Fact (0 < c)] (hm : 1 ≤ m) (f : ℝ × ℝ → ℂ), GoodC c m f →
    ∃ wr wi : ActualVorticity (c := c) (m := m) hm,
      f =ᵐ[volume.restrict (B0579.cell c)]
        fun x => cplx (vortFn hm wr) x + Complex.I * cplx (vortFn hm wi) x

/-- **Admissibility is stable** (SP 2819-2836): every element of the physical state space is
admissible (`MemLp` from the `X_{m,c}` norm, zero circulation from the submodule), and admissible
data are stable under `f₁ + I f₂` (`MemLp.add`, `MemLp.const_mul`, `integral_add`). -/
def GoodCStable : Prop :=
  (∀ (c m : ℝ) [Fact (0 < c)] (hm : 1 ≤ m) (w : ActualVorticity (c := c) (m := m) hm),
      GoodC c m (cplx (vortFn hm w))) ∧
  (∀ (c m : ℝ) (f₁ f₂ : ℝ × ℝ → ℂ), GoodC c m f₁ → GoodC c m f₂ →
      GoodC c m (fun x => f₁ x + Complex.I * f₂ x))

/-- **The state space injects into functions a.e.** (SP 2819-2836): two elements of the physical
state space with a.e. equal representatives on the cell are equal (`cellMeasure ≪ volume.restrict
cell`, `Lp.ext`/`Subtype.ext`). -/
def VortFnInj : Prop :=
  ∀ (c m : ℝ) [Fact (0 < c)] (hm : 1 ≤ m) (w w' : ActualVorticity (c := c) (m := m) hm),
    vortFn hm w =ᵐ[volume.restrict (B0579.cell c)] vortFn hm w' → w = w'

/-- The classically-defined bookkeeping functions. -/
def stripW {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)
    (E : ℝ → ℝ → ActualVorticity (c := c) (m := m) hm → ActualVorticity (c := c) (m := m) hm)
    (wr wi : (ℝ × ℝ → ℂ) → ActualVorticity (c := c) (m := m) hm) :
    ℝ → ℝ → (ℝ × ℝ → ℂ) → (ℝ × ℝ → ℂ) := by
  classical
  exact fun r a f =>
    if GoodC c m f then
      fun x => cplx (vortFn hm (E r a (wr f))) x + Complex.I * cplx (vortFn hm (E r a (wi f))) x
    else 0

def stripU {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)
    (E : ℝ → ℝ → ActualVorticity (c := c) (m := m) hm → ActualVorticity (c := c) (m := m) hm)
    (wr wi : (ℝ × ℝ → ℂ) → ActualVorticity (c := c) (m := m) hm) :
    ℝ → ℝ → (ℝ × ℝ → ℂ) → (ℝ × ℝ → Fin 2 → ℂ) := by
  classical
  exact fun r a f =>
    if GoodC c m f then
      fun x j => stripVel hm (E r a (wr f)) x j + Complex.I * stripVel hm (E r a (wi f)) x j
    else 0

theorem stripBookkeeping_of (hL : LinFlowComb) (hR : ActualRepresentation) (hG : GoodCStable)
    (hInj : VortFnInj) (hCongr : FlowCongrAE) : StripBookkeeping := by
  intro ν c m _ hm tr P H hReg hstrip
  classical
  have hrep : ∀ f, GoodC c m f → ∃ wr wi : ActualVorticity (c := c) (m := m) hm,
      f =ᵐ[volume.restrict (B0579.cell c)]
        fun x => cplx (vortFn hm wr) x + Complex.I * cplx (vortFn hm wi) x :=
    fun f hf => hR c m hm f hf
  choose! wr wi hrepw using hrep
  have hcomp := actualTrainVolterra_compatible hm P H
  obtain ⟨E, hE⟩ : ∃ E : ℝ → ℝ → ActualVorticity (c := c) (m := m) hm →
      ActualVorticity (c := c) (m := m) hm,
      ∀ r a w, E r a w = (actualTrainVolterraData hm P H).evolution r a w :=
    ⟨fun r a w => (actualTrainVolterraData hm P H).evolution r a w, fun _ _ _ => rfl⟩
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
    have h1 := hL ν c m tr a (a + 1) _ _ _ _ _ _ (hstrip a ha (wr f)) (hstrip a ha (wi f))
    have hWf : (fun r => stripW hm E wr wi r a f) = fun r x =>
        cplx (vortFn hm ((actualTrainVolterraData hm P H).evolution r a (wr f))) x +
          Complex.I * cplx (vortFn hm ((actualTrainVolterraData hm P H).evolution r a (wi f))) x := by
      funext r
      rw [hW r a f hf, hE, hE]
    have hUf : (fun r => stripU hm E wr wi r a f) = fun r x j =>
        stripVel hm ((actualTrainVolterraData hm P H).evolution r a (wr f)) x j +
          Complex.I * stripVel hm ((actualTrainVolterraData hm P H).evolution r a (wi f)) x j := by
      funext r
      rw [hU r a f hf, hE, hE]
    rw [hWf, hUf]
    exact hCongr ν c m tr a (a + 1) _ f _ _ _ _ (by linarith) h1 (hrepw f hf).symm
      (fun s _ => Filter.EventuallyEq.rfl) (fun s _ => Filter.EventuallyEq.rfl)
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
      exact (actualTrainVolterraData hm P H).evolution_apply_comp hcomp har hrT w
    refine ⟨?_, ?_⟩
    · rw [hW T a f hf, hW T r g hg, hwr, hwi, c1, c1]
    · rw [hU T a f hf, hU T r g hg, hwr, hwi, c1, c1]

end UnforcedLeray.Short.IIIa.Exist
