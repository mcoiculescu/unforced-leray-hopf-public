import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.YoungW2.Corr.ContRepWeakSlice.SlabInt

/-!
# Product phase tests `χ(τ) ψ(y) e_k` (helper of `bgContRepWeakSlice`)
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace

/-- The product test `(τ, y) ↦ χ(τ) ψ(y) e_k`. -/
def prodTestReal (χ : ℝ → ℝ) (ψ : Space → ℝ) (k : Fin 3) : ℝ × Space → CVec3 :=
  fun p => ((χ p.1 * ψ p.2 : ℝ) : ℂ) • EuclideanSpace.single k (1 : ℂ)

theorem prodTest_apply (χ : ℝ → ℝ) (ψ : Space → ℝ) (k : Fin 3) (p : ℝ × Space) :
    prodTestReal χ ψ k p = ((χ p.1 * ψ p.2 : ℝ) : ℂ) • EuclideanSpace.single k (1 : ℂ) := rfl

theorem isSpatialTest_derivative {φ : Space → ℝ} (hφ : UnforcedLeray.IsSpatialTest φ)
    (j : Fin 3) : UnforcedLeray.IsSpatialTest (UnforcedLeray.spatialTestDerivative j φ) :=
  ⟨(hφ.smooth.fderiv_right (by simp)).clm_apply contDiff_const,
    hφ.compact.fderiv_apply (𝕜 := ℝ) (UnforcedLeray.coordinateVector j)⟩

theorem isSpatialTest_neg {φ : Space → ℝ} (hφ : UnforcedLeray.IsSpatialTest φ) :
    UnforcedLeray.IsSpatialTest (fun y => -φ y) :=
  ⟨hφ.smooth.neg, hφ.compact.neg⟩

theorem prodTest_isPhaseTest {P : ℝ} {χ : ℝ → ℝ} {ψ : Space → ℝ} (k : Fin 3)
    (hχ : ContDiff ℝ ∞ χ) (hχp : ∀ t, χ (t + P) = χ t) (hψ : UnforcedLeray.IsSpatialTest ψ) :
    IsPhaseTest P (prodTestReal χ ψ k) where
  smooth := by
    unfold prodTestReal
    exact (Complex.ofRealCLM.contDiff.comp
      ((hχ.comp contDiff_fst).mul (hψ.smooth.comp contDiff_snd))).smul contDiff_const
  periodic := fun τ y => by simp [prodTestReal, hχp]
  bounded_support := by
    obtain ⟨R, hR⟩ := hψ.compact.isCompact.isBounded.subset_closedBall (0 : Space)
    refine ⟨R, fun τ y hy => ?_⟩
    have : ψ y = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      have := hR hmem
      simp [Metric.mem_closedBall, dist_zero_right] at this
      linarith
    simp [prodTestReal, this]

theorem dy_prodTest {χ : ℝ → ℝ} {ψ : Space → ℝ} (k j : Fin 3) (hχ : ContDiff ℝ ∞ χ)
    (hψ : UnforcedLeray.IsSpatialTest ψ) :
    dy j (prodTestReal χ ψ k) = prodTestReal χ (UnforcedLeray.spatialTestDerivative j ψ) k := by
  funext p
  have hχd : HasFDerivAt (fun p : ℝ × Space => χ p.1)
      ((fderiv ℝ χ p.1).comp (ContinuousLinearMap.fst ℝ ℝ Space)) p :=
    ((hχ.differentiable (by simp)) p.1).hasFDerivAt.comp p (hasFDerivAt_fst)
  have hψd : HasFDerivAt (fun p : ℝ × Space => ψ p.2)
      ((fderiv ℝ ψ p.2).comp (ContinuousLinearMap.snd ℝ ℝ Space)) p :=
    ((hψ.smooth.differentiable (by simp)) p.2).hasFDerivAt.comp p (hasFDerivAt_snd)
  have hm := (hχd.mul hψd)
  have hc := (Complex.ofRealCLM.hasFDerivAt.comp p hm).smul_const
    (EuclideanSpace.single k (1 : ℂ))
  have h2 : HasFDerivAt (prodTestReal χ ψ k) _ p := hc
  unfold dy
  rw [h2.fderiv]
  simp [prodTestReal, UnforcedLeray.spatialTestDerivative]

end UnforcedLeray.Short.PartIIIb.Concrete
