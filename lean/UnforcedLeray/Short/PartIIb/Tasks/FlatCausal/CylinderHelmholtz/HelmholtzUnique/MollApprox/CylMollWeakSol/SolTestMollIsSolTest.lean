import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T12_1_3_1_6
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.HelmholtzUnique.MollApprox.CylMollWeakDiv.TestMollIsTest
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.HelmholtzUnique.MollApprox.CylMollWeakDiv.TestMollDeriv

/-!
# Leaf `T12/1/3/1/6/1`: the componentwise reflected mollification of a `CylSolTest` is a `CylSolTest`

Proves `solTestMollIsSolTest : SolTestMollIsSolTest` (source
`the November 2 reference manuscript`, lines 1670, 1923-1926).
Components are cylinder tests by `testMollIsTest`. For the divergence, `testMollDeriv` gives
`∂_i (testMoll ρ Ψ_i) (z) v = ∫ ρ(y) ∂Ψ_i(z + y) v`, so the sum of the two divergence terms is
`∫ ρ(y) (div Ψ)(z + y) dy = 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Complex
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem solTestMollIsSolTest : UnforcedLeray.Short.IIb.SolTestMollIsSolTest := by
  intro c ρ Ψ hΨ
  have h0 : CylTest c (fun z => Ψ z 0) := hΨ.comp 0
  have h1 : CylTest c (fun z => Ψ z 1) := hΨ.comp 1
  refine ⟨fun i => testMollIsTest c ρ (fun z => Ψ z i) (hΨ.comp i), ?_⟩
  intro z
  show fderiv ℝ (testMoll ρ (fun w => Ψ w 0)) z (1, 0) +
      fderiv ℝ (testMoll ρ (fun w => Ψ w 1)) z (0, 1) = 0
  rw [testMollDeriv c ρ (fun w => Ψ w 0) h0 z (1, 0),
    testMollDeriv c ρ (fun w => Ψ w 1) h1 z (0, 1)]
  have hc0 : Continuous (fun y : ℝ × ℝ => fderiv ℝ (fun w => Ψ w 0) (z + y) (1, 0)) := by
    have hd : Continuous (fderiv ℝ (fun w => Ψ w 0)) := h0.smooth.continuous_fderiv (by simp)
    exact (hd.comp (continuous_const.add continuous_id)).clm_apply continuous_const
  have hc1 : Continuous (fun y : ℝ × ℝ => fderiv ℝ (fun w => Ψ w 1) (z + y) (0, 1)) := by
    have hd : Continuous (fderiv ℝ (fun w => Ψ w 1)) := h1.smooth.continuous_fderiv (by simp)
    exact (hd.comp (continuous_const.add continuous_id)).clm_apply continuous_const
  have hsmρ : ContDiff ℝ ∞ (ρ.normed volume) := ρ.contDiff_normed
  have hcρ : Continuous (ρ.normed volume) := hsmρ.continuous
  have hi0 : Integrable
      (fun y : ℝ × ℝ => ρ.normed volume y * fderiv ℝ (fun w => Ψ w 0) (z + y) (1, 0)) volume :=
    (hcρ.mul hc0).integrable_of_hasCompactSupport ρ.hasCompactSupport_normed.mul_right
  have hi1 : Integrable
      (fun y : ℝ × ℝ => ρ.normed volume y * fderiv ℝ (fun w => Ψ w 1) (z + y) (0, 1)) volume :=
    (hcρ.mul hc1).integrable_of_hasCompactSupport ρ.hasCompactSupport_normed.mul_right
  rw [← integral_add hi0 hi1]
  have hzero : ∀ y : ℝ × ℝ,
      ρ.normed volume y * fderiv ℝ (fun w => Ψ w 0) (z + y) (1, 0) +
        ρ.normed volume y * fderiv ℝ (fun w => Ψ w 1) (z + y) (0, 1) = 0 := by
    intro y
    rw [← mul_add, hΨ.div_free (z + y), mul_zero]
  simp only [hzero, integral_zero]

end UnforcedLeray.Short.IIb
