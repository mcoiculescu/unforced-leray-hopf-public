import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.Analysis.Fourier.AddCircle

/-!
# Strong continuity of translation in `L^p` of time (INF14 target T9, translation part)


target T9 and §3.1 ("Translation continuity in Lp for locally compact groups
`Lp.instContinuousSMulDomMulAct` … covers ℝⁿ, ℝ and AddCircle, so translation continuity in
`Y_q` needs no new theory"). The resolvent `R_μ f(τ) = ∫_0^∞ e^{-μr} S_ν(r) P_σ f(τ - r) dr` of
tex 7427–7445 (blueprint unit B0421) is a `Y_q`-valued Bochner integral because translation
`τ ↦ f(· - τ)` is strongly continuous on `Y_q = L^q(ℝ/Pℤ; X)` (decision D2).

The translate of `f ∈ L^p(G; E)` by `t ∈ G` is `DomAddAct.mk t +ᵥ f`, which is a.e. equal to
`x ↦ f (t + x)` (`vadd_Lp_ae_eq`).

## Main results

* `continuous_translate_real`: `t ↦ f(t + ·)` is continuous `ℝ → L^p(ℝ; E)`;
* `continuous_translate_addCircle`: the same on `AddCircle P` with its normalized Haar measure
  `haarAddCircle` (the phase measure of decision D2), for any normed group `E` (in particular
  `E = L^q(ℝ³; ℂ³)`);
* `translate_ae_eq`: the translate is `x ↦ f (t + x)` almost everywhere.
-/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.BochnerTime

variable {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (p ≠ ∞)]

/-- **Translation continuity on the line** (T9). For `f ∈ L^p(ℝ; E)`, `1 ≤ p < ∞`, the map
`t ↦ f(t + ·)` is continuous into `L^p(ℝ; E)`. -/
theorem continuous_translate_real (f : Lp E p (volume : Measure ℝ)) :
    Continuous fun t : ℝ => DomAddAct.mk t +ᵥ f :=
  DomAddAct.continuous_mk.vadd continuous_const

/-- **Translation continuity in the phase** (T9; decision D2). For `f ∈ L^p(ℝ/Pℤ; E)` with the
normalized Haar measure, `1 ≤ p < ∞`, the map `t ↦ f(t + ·)` is continuous into the same space. -/
theorem continuous_translate_addCircle {P : ℝ} [Fact (0 < P)]
    (f : Lp E p (AddCircle.haarAddCircle (T := P))) :
    Continuous fun t : AddCircle P => DomAddAct.mk t +ᵥ f :=
  DomAddAct.continuous_mk.vadd continuous_const

/-- The translate `DomAddAct.mk t +ᵥ f` is `x ↦ f (t + x)` almost everywhere. -/
theorem translate_ae_eq {G : Type*} [AddGroup G] [MeasurableSpace G] [MeasurableAdd G]
    {μ : Measure G} [μ.IsAddLeftInvariant] (t : G) (f : Lp E p μ) :
    (DomAddAct.mk t +ᵥ f : Lp E p μ) =ᵐ[μ] fun x => f (t + x) :=
  DomAddAct.vadd_Lp_ae_eq _ f

end UnforcedLeray.BochnerTime
