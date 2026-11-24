import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.TimeJets.Defs
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TimeJets.KerVelPairDeriv
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.NearFar
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.AdjFubini
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.VelFarFieldParts.Bdd
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.VelFarFieldParts.Meas

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **(16) Derivatives commute with the kernel adjoint** (SP 3052-3058): the weak derivative of
`F` (tested against cylinder tests) passes through `K_d^T` to the weak derivative of `K_d^T F`.
Proof: the duality identity `KerAdjFubini` for `∂_jψ` and for `ψ`, the kernel velocity
`K_d∂_jψ` is bounded and measurable (`KerVelBdd`, `KerVelMeas`), so the sum over components
splits into scalar pairings, each given by `KerVelPairDeriv`. -/
theorem kerAdjWeakDeriv : KerAdjWeakDeriv := by
  intro d hd j F G hFG
  have hF : ∀ l, IntegrableOn (F l) (B0579.cell d) := fun l => (hFG l).1
  have hG : ∀ l, IntegrableOn (G l) (B0579.cell d) := fun l => (hFG l).2.1
  have hW : ∀ l, HasWeakCellDerivC d j (F l) (G l) := fun l => (hFG l).2.2
  -- integrability of `H · K_dφ_l` for an integrable `H` and a cylinder test `φ`
  have hint : ∀ (H : ℝ × ℝ → ℂ), IntegrableOn H (B0579.cell d) →
      ∀ (φ : ℝ × ℝ → ℝ), B0579.IsCylTest d φ → ∀ l : Fin 2,
      IntegrableOn (fun x => H x * ((kerVel d φ x l : ℝ) : ℂ)) (B0579.cell d) := by
    intro H hH φ hφ l
    obtain ⟨B, hB⟩ := kerVelBdd d hd φ hφ
    unfold IntegrableOn at hH ⊢
    refine Integrable.mul_bdd (c := B) hH ?_ ?_
    · exact Complex.continuous_ofReal.comp_aestronglyMeasurable (kerVelMeas d hd φ hφ l)
    · refine Filter.Eventually.of_forall fun x => ?_
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hB x l
  have hFub := kerAdjFubini_of kerNearFar
  unfold HasWeakCellDerivC
  refine ⟨fun ψ hψ => ⟨(hFub d hd F hF (B0579.pd j ψ) (hψ.pd j)).1,
    (hFub d hd G hG ψ hψ).1⟩, fun ψ hψ => ?_⟩
  rw [(hFub d hd F hF (B0579.pd j ψ) (hψ.pd j)).2, (hFub d hd G hG ψ hψ).2]
  have h1 : ∫ x in B0579.cell d, ∑ l, F l x * ((kerVel d (B0579.pd j ψ) x l : ℝ) : ℂ)
      = ∑ l, ∫ x in B0579.cell d, F l x * ((kerVel d (B0579.pd j ψ) x l : ℝ) : ℂ) :=
    integral_finsetSum _ fun l _ => hint (F l) (hF l) _ (hψ.pd j) l
  have h2 : ∫ x in B0579.cell d, ∑ l, G l x * ((kerVel d ψ x l : ℝ) : ℂ)
      = ∑ l, ∫ x in B0579.cell d, G l x * ((kerVel d ψ x l : ℝ) : ℂ) :=
    integral_finsetSum _ fun l _ => hint (G l) (hG l) ψ hψ l
  rw [h1, h2, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun l _ =>
    kerVelPairDeriv d hd j (F l) (G l) (hF l) (hG l) (hW l) ψ hψ l

end UnforcedLeray.Short.IIIa
