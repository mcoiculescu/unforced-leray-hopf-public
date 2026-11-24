import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollCommLemmas.FriedrichsBound.KapNormedScale

/-!
# `kapScale`: dilation covariance of the Friedrichs kernel

Source `the November 2 reference manuscript` lines 1556-1583.
From `kapNormedScale`: `ρ.normed = c · g(s ·)` with `g = kapUnit.normed`, and the chain rule.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem kapScale : KapScale := by
  intro ρ hρ z
  have hgd : Differentiable ℝ (kapUnit.normed volume) :=
    (kapUnit.contDiff_normed (n := 1)).differentiable one_ne_zero
  have hder : HasFDerivAt (fun w : ℝ × Space => (ρ.rIn ^ 4)⁻¹ * kapUnit.normed volume (ρ.rIn⁻¹ • w))
      ((ρ.rIn ^ 4)⁻¹ • (fderiv ℝ (kapUnit.normed volume) (ρ.rIn⁻¹ • z)).comp
        (ρ.rIn⁻¹ • ContinuousLinearMap.id ℝ (ℝ × Space))) z := by
    have h1 : HasFDerivAt (fun w : ℝ × Space => ρ.rIn⁻¹ • w)
        (ρ.rIn⁻¹ • ContinuousLinearMap.id ℝ (ℝ × Space)) z :=
      ((hasFDerivAt_id z).const_smul (ρ.rIn⁻¹ : ℝ) : _)
    have h2 := (hgd (ρ.rIn⁻¹ • z)).hasFDerivAt.comp z h1
    exact h2.const_mul _
  have hfn : fderiv ℝ (ρ.normed volume) z =
      (ρ.rIn ^ 4)⁻¹ • (fderiv ℝ (kapUnit.normed volume) (ρ.rIn⁻¹ • z)).comp
        (ρ.rIn⁻¹ • ContinuousLinearMap.id ℝ (ℝ × Space)) := by
    have hn : ρ.normed volume = fun w => (ρ.rIn ^ 4)⁻¹ * kapUnit.normed volume (ρ.rIn⁻¹ • w) :=
      funext (kapNormedScale ρ hρ)
    rw [hn]
    exact hder.fderiv
  have hv : ∀ v : ℝ × Space, fderiv ℝ (ρ.normed volume) z v =
      (ρ.rIn ^ 4)⁻¹ * (ρ.rIn⁻¹ * fderiv ℝ (kapUnit.normed volume) (ρ.rIn⁻¹ • z) v) := by
    intro v
    rw [hfn]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
  have hz : ((0 : ℝ), (ρ.rIn⁻¹ • z).2) = ρ.rIn⁻¹ • ((0 : ℝ), z.2) := by
    ext <;> simp
  unfold kap kerDv
  rw [hv, kapNormedScale ρ hρ z, hz, map_smul, smul_eq_mul]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
