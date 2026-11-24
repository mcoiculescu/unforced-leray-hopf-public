import UnforcedLeray.Short.PartIIb.Sub.T15_2
import UnforcedLeray.Short.PartIIb.Tasks.HilbertEnergy.ProductRule.ExpChartIntegral
import UnforcedLeray.Short.PartIIb.Tasks.HilbertEnergy.ProductRule.OrigTestOfLog

/-!


Source of record: `the November 2 reference manuscript`, lines 1975-1979 (weak
product rule in the `H_2` measure; logarithmic chart `s = e^t`).

The statement `LogWeakTransfer` is `Sub/T15_2.lean`, lines 139-141. Proof: given a `LogTest Φ`,
take the original test `φ` from `origTestOfLog`, apply the periodic weak identity at `φ`, and
transport both sides to the logarithmic chart with the complex Bochner part of `expChartIntegral`
(`a = -3/2`, density `e^{-t/2}`). The remaining identities are pointwise algebra with `Real.exp_add`.
No integrability is needed.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.IIb

/-- **Leaf `PartII-b:T15/2/5`** (weak identity in the logarithmic chart). If
`PeriodicWeakS c (-3/2) w Sw` then, for each component `i`, `u = logU w i` and `g = logU Sw i`
satisfy `LogWeak`. -/
theorem logWeakTransfer : UnforcedLeray.Short.IIb.LogWeakTransfer := by
  unfold LogWeakTransfer
  intro c w Sw hc hPW i
  unfold LogWeak
  intro Φ hΦ
  obtain ⟨φ, hφc, hφp, hφs, hφe, hφd⟩ := UnforcedLeray.Short.IIb.origTestOfLog c Φ hΦ
  -- periodic weak identity at the transported test `φ`
  have hW : ∫ x, Sw x i * (φ x : ℂ) ∂(Axi.ageμ c (-3 / 2)) =
      -∫ x, w x i * (((1 + (-3 / 2)) * φ x + x.1 * cpd 0 φ x : ℝ) : ℂ) ∂(Axi.ageμ c (-3 / 2)) :=
    hPW φ hφc hφp hφs i
  -- change of variable `s = e^t` (complex Bochner part of `ExpChartIntegral`)
  have hL : ∫ x, Sw x i * (φ x : ℂ) ∂(Axi.ageμ c (-3 / 2)) =
      ∫ x, ((Real.exp ((-3 / 2 + 1) * x.1) : ℝ) : ℂ) *
        (Sw (Real.exp x.1, x.2) i * (φ (Real.exp x.1, x.2) : ℂ)) ∂(logMeas c) :=
    (UnforcedLeray.Short.IIb.expChartIntegral c (-3 / 2) hc).2.2 (fun x => Sw x i * (φ x : ℂ))
  have hR : ∫ x, w x i * (((1 + (-3 / 2)) * φ x + x.1 * cpd 0 φ x : ℝ) : ℂ)
        ∂(Axi.ageμ c (-3 / 2)) =
      ∫ x, ((Real.exp ((-3 / 2 + 1) * x.1) : ℝ) : ℂ) *
        (w (Real.exp x.1, x.2) i *
          (((1 + (-3 / 2)) * φ (Real.exp x.1, x.2) + Real.exp x.1 * cpd 0 φ (Real.exp x.1, x.2) :
            ℝ) : ℂ)) ∂(logMeas c) :=
    (UnforcedLeray.Short.IIb.expChartIntegral c (-3 / 2) hc).2.2
      (fun x => w x i * (((1 + (-3 / 2)) * φ x + x.1 * cpd 0 φ x : ℝ) : ℂ))
  -- pointwise identity on the logarithmic side, left-hand side
  have hLHS : ∫ x, logU Sw i x * (Φ x : ℂ) ∂(logMeas c) =
      ∫ x, ((Real.exp ((-3 / 2 + 1) * x.1) : ℝ) : ℂ) *
        (Sw (Real.exp x.1, x.2) i * (φ (Real.exp x.1, x.2) : ℂ)) ∂(logMeas c) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    rw [hφe x]
    unfold logU
    rw [show Real.exp (-x.1 / 4) = Real.exp ((-3 / 2 + 1) * x.1) * Real.exp (x.1 / 4) by
      rw [← Real.exp_add]; congr 1; ring]
    push_cast
    ring
  -- pointwise identity on the logarithmic side, right-hand side
  have hRHS : -∫ x, w x i * (((1 + (-3 / 2)) * φ x + x.1 * cpd 0 φ x : ℝ) : ℂ)
        ∂(Axi.ageμ c (-3 / 2)) =
      ∫ x, logU w i x * ((Φ x / 4 - cpd 0 Φ x : ℝ) : ℂ) ∂(logMeas c) := by
    rw [hR, ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    rw [hφe x, hφd x]
    unfold logU
    rw [show Real.exp (-x.1 / 4) = Real.exp ((-3 / 2 + 1) * x.1) * Real.exp (x.1 / 4) by
      rw [← Real.exp_add]; congr 1; ring]
    push_cast
    ring
  exact hLHS.trans (hL.symm.trans (hW.trans hRHS))

end UnforcedLeray.Short.IIb
