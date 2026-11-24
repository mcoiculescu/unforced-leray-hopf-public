import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_1_15
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.CRDeriv.Diff.Common
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.HeatMoments

/-!
# `PartII-b:T22/1/15/4` (`ConvLinear`): linearity of the Duhamel convolution

Source: SP 2074-2093.  Pointwise linearity of `heatSG` on bounded continuous functions, and
interval integrability of `r ↦ heatSG (ν (τ - r)) (F r) x` from `dParamCont` and `heatWBounds`
(as in `dDiff`), then `intervalIntegral.integral_sub`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

namespace CylPDE

namespace ConvLin

lemma heatSG_sub {f g : Pl → ℝ} {B : ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfB : ∀ y, |f y| ≤ B) (hgB : ∀ y, |g y| ≤ B) (a : ℝ) (x : Pl) :
    heatSG a (fun y => f y - g y) x = heatSG a f x - heatSG a g x := by
  unfold heatSG
  split_ifs with h
  · rfl
  · have ha : 0 < a := not_le.1 h
    obtain ⟨-, hI, -, -⟩ := heatKernelMoments a ha
    have hK : Integrable (fun y : Pl => heatK a (x - y)) := hI.comp_sub_left x
    have hKc : Continuous (fun y : Pl => heatK a (x - y)) := by
      unfold heatK; fun_prop
    have hmb : ∀ {h : Pl → ℝ}, Continuous h → (∀ y, |h y| ≤ B) →
        Integrable (fun y : Pl => heatK a (x - y) * h y) := by
      intro h hc hb
      refine Integrable.mono' (hK.norm.mul_const B)
        (hKc.aestronglyMeasurable.mul hc.aestronglyMeasurable) (ae_of_all _ fun z => ?_)
      simp only [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hb z) (abs_nonneg _)
    simp_rw [mul_sub]
    exact integral_sub (hmb hf hfB) (hmb hg hgB)

end ConvLin

open ConvLin in
/-- **Leaf 4 (`/15/4`).** Linearity of the Duhamel convolution for regular integrands bounded in
the `cosh` weight. -/
theorem convLinear_proof : UnforcedLeray.Short.IIb.CylPDE.ConvLinear := by
  intro ν s T hν hsT F G hF hG B hB τ hτ x
  have hτs : s ≤ τ := hτ.1
  have hτT : τ ≤ T := hτ.2
  have hB0 : 0 ≤ B := by
    have h := (hB s ⟨le_rfl, hsT⟩).1 0
    have h0 : 0 ≤ |F s 0| * Real.cosh (0 : Pl).2 := by positivity
    exact h0.trans h
  have hHyp : ∀ (g : ℝ → Pl → ℝ), FReg s T g → (∀ r ∈ Icc s T, WB B (g r)) →
      DHyp s T g (fun _ => B) := fun g hg hgB =>
    ⟨hg.contF, continuousOn_const, fun _ _ => hB0, hgB⟩
  have hint : ∀ (g : ℝ → Pl → ℝ), DHyp s T g (fun _ => B) →
      IntervalIntegrable (fun t => heatSG (ν * (τ - t)) (g t) x) volume s τ := by
    intro g hH
    obtain ⟨hDc, -⟩ := dParamCont ν s T hν hsT g (fun _ => B) hH τ hτ
    obtain ⟨-, -, hb0, hgb⟩ := hH
    refine DiffC.intInt_of_bdd (F := fun t => heatSG (ν * (τ - t)) (g t) x)
      (K := 2 * Real.exp (ν * (T - s)) * B) hτs
      (DiffC.aesm_slice (fun t y => heatSG (ν * (τ - t)) (g t) y) hDc x) ?_
    intro t ht
    have hts : t ∈ Icc s T := ⟨ht.1.le, ht.2.trans hτT⟩
    exact DiffC.heatSG_bound_aux hν hτT ht.1.le ht.2 le_rfl hB0 (hgb t hts) x
  have hFi := hint F (hHyp F hF (fun r hr => (hB r hr).1))
  have hGi := hint G (hHyp G hG (fun r hr => (hB r hr).2))
  unfold duhamelConv
  rw [← intervalIntegral.integral_sub hFi hGi]
  refine intervalIntegral.integral_congr (fun r hr => ?_)
  rw [uIcc_of_le hτs] at hr
  have hrm : r ∈ Icc s T := ⟨hr.1, hr.2.trans hτT⟩
  have hFc : Continuous (F r) := DiffC.cont_slice hF.contF hrm
  have hGc : Continuous (G r) := DiffC.cont_slice hG.contF hrm
  exact heatSG_sub hFc hGc (fun y => HC.gbound ((hB r hrm).1) y)
    (fun y => HC.gbound ((hB r hrm).2) y) _ x

end CylPDE

end UnforcedLeray.Short.IIb
