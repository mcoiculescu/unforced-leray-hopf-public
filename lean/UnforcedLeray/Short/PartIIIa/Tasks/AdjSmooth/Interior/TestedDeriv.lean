import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.RhsCont
import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.Defs

/-!
# `PartIII-a:T21/2/7/2/1/1/4`: the differentiated weak equation (`adjTestedDerivOf`)

Source: `the November 2 reference manuscript` line 3060.
The weak identity `IsAdjointWeak.weak` gives `∫ φ(r) ψ = ∫ g ψ + ∫_r^s I`, with
`I(r) = ∫ adjIntegrand tr (φ r) r ψ uψ`, and `I` is continuous on `[t, s]` by `adjTestedRhsCont`.
The fundamental theorem of calculus then gives the derivative `-I(r)` within `[t, s]`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa

theorem adjTestedDerivOf (m : ℝ) : AdjTestedDerivOf m := by
  unfold AdjTestedDerivOf
  intro ν hν hν1 tr hbd t s ht hts g φ hφ
  unfold AdjTestedDeriv
  intro ψ uψ hψ huψ
  have hcont : ContinuousOn
      (fun r => ∫ x in B0579.cell (ν ^ (-2 : ℝ)), adjIntegrand tr (φ r) r ψ uψ x) (Icc t s) :=
    adjTestedRhsCont m ν hν hν1 tr hbd t s ht hts g φ hφ ψ uψ hψ huψ
  refine ⟨hcont, fun r hr => ?_⟩
  set I : ℝ → ℂ := fun r' => ∫ x in B0579.cell (ν ^ (-2 : ℝ)), adjIntegrand tr (φ r') r' ψ uψ x
    with hI
  set G0 : ℂ := ∫ x in B0579.cell (ν ^ (-2 : ℝ)), g x * (ψ x : ℂ) with hG0
  have hIt : ∀ u ∈ Icc t s, IntervalIntegrable I volume t u := fun u hu =>
    (hcont.mono (Icc_subset_Icc le_rfl hu.2)).intervalIntegrable_of_Icc hu.1
  have hF : ∀ u ∈ Icc t s,
      (fun r' => ∫ x in B0579.cell (ν ^ (-2 : ℝ)), φ r' x * (ψ x : ℂ)) u =
        G0 + ((∫ x in t..s, I x) - ∫ x in t..u, I x) := by
    intro u hu
    have h := hφ.weak ψ uψ hψ huψ u hu
    rw [intervalIntegral.integral_interval_sub_left (hIt s ⟨hts.le, le_rfl⟩) (hIt u hu)]
    exact h
  have h1 : HasDerivWithinAt (fun u => ∫ x in t..u, I x) (I r) (Icc t s) r := by
    haveI : Fact (r ∈ Icc t s) := ⟨hr⟩
    exact intervalIntegral.integral_hasDerivWithinAt_right (hIt r hr)
      (hcont.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc r)
      (hcont.continuousWithinAt hr)
  have hderiv : HasDerivWithinAt (fun u => G0 + ((∫ x in t..s, I x) - ∫ x in t..u, I x))
      (-I r) (Icc t s) r :=
    (h1.const_sub (∫ x in t..s, I x)).const_add G0
  exact hderiv.congr (fun u hu => hF u hu) (hF r hr)

end UnforcedLeray.Short.IIIa
