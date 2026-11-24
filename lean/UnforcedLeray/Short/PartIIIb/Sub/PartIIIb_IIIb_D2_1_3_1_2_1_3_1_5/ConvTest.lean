import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1_5

/-!
# Convolution in `y` preserves phase tests

Source `the November 2 reference manuscript`
lines 1351-1362, 1470-1480.  For a smooth compactly supported kernel `κ` and a phase test `Θ`,
`convY κ Θ` is smooth, `P`-periodic in the phase and vanishes for large `‖y‖`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem convTest_smooth (P : ℝ) (κ : Space → ℝ) (Θ : ℝ × Space → CVec3) (hκ : KerOK κ)
    (hΘ : UnforcedLeray.PhaseSpace.IsPhaseTest P Θ) :
    ContDiff ℝ ∞ (convY κ Θ) := by
  obtain ⟨R, hR⟩ := hΘ.bounded_support
  have hf : LocallyIntegrable κ volume := hκ.1.continuous.locallyIntegrable
  have hgs : ∀ p : ℝ, ∀ x : Space, p ∈ (univ : Set ℝ) → x ∉ Metric.closedBall (0 : Space) R →
      (fun (τ : ℝ) (z : Space) => Θ (τ, z)) p x = 0 := by
    intro p x _ hx
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
    exact hR p x hx
  have hg : ContDiffOn ℝ ∞ (Function.uncurry fun (τ : ℝ) (z : Space) => Θ (τ, z))
      (univ ×ˢ univ) := by
    exact hΘ.smooth.contDiffOn
  have key := MeasureTheory.contDiffOn_convolution_right_with_param
    (μ := volume) (f := κ)
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] CVec3 →L[ℝ] CVec3)
    (s := univ) (k := Metric.closedBall (0 : Space) R)
    isOpen_univ (isCompact_closedBall _ _) hgs hf hg
  have heq : convY κ Θ = fun q : ℝ × Space =>
      (convolution κ ((fun (τ : ℝ) (z : Space) => Θ (τ, z)) q.1)
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] CVec3 →L[ℝ] CVec3) volume) q.2 := by
    funext x
    simp only [convY, convolution, ContinuousLinearMap.lsmul_apply, Complex.coe_smul]
  rw [heq]
  rw [Set.univ_prod_univ] at key
  exact contDiffOn_univ.mp key

theorem convTest_bounded (κ : Space → ℝ) (Θ : ℝ × Space → CVec3) (hκ : KerOK κ)
    (P : ℝ) (hΘ : UnforcedLeray.PhaseSpace.IsPhaseTest P Θ) :
    ∃ R, ∀ τ y, R < ‖y‖ → convY κ Θ (τ, y) = 0 := by
  obtain ⟨R, hR⟩ := hΘ.bounded_support
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hκ.2.isCompact.isBounded
  refine ⟨R + C, fun τ y hy => ?_⟩
  unfold convY
  have hz : ∀ z : Space, (κ z : ℂ) • Θ (τ, y - z) = 0 := by
    intro z
    by_cases hzC : C < ‖z‖
    · have : κ z = 0 := image_eq_zero_of_notMem_tsupport (fun h => by
        have := hC z h
        linarith)
      simp [this]
    · have hzC' : ‖z‖ ≤ C := not_lt.mp hzC
      have h1 : ‖y‖ ≤ ‖y - z‖ + ‖z‖ := by
        have := norm_add_le (y - z) z
        rwa [sub_add_cancel] at this
      have : R < ‖y - z‖ := by linarith
      simp [hR τ (y - z) this]
  simp [hz]

theorem convTest : UnforcedLeray.Short.PartIIIb.Concrete.ConvTest := by
  intro P κ Θ hκ hΘ
  refine ⟨convTest_smooth P κ Θ hκ hΘ, ?_, convTest_bounded κ Θ hκ P hΘ⟩
  intro τ y
  unfold convY
  congr 1
  funext z
  rw [hΘ.periodic]

end UnforcedLeray.Short.PartIIIb.Concrete
