import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_3

/-!
# `PartII-a:N01/3/1` (phase gradients are slice tests)

Source `the November 2 reference manuscript`,
line 1669 and lines 1639-1643 (chart `y = R x`, `R = ε⁻¹`).

`physGradPhase ε φ (τ, y) = cplx3 (∇ₓφ(ε y, τ))` is a phase test for a physical test `φ`:
smooth, `P`-periodic in `τ`, and vanishing for `‖y‖` beyond `R/ε`. Phase tests are slice tests
(`IsPhaseTest.isSliceTest`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.PhaseSpace
open UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization (cplx3 toX)

/-- Smoothness of `(τ, y) ↦ ∇ₓφ(εy, τ)` composed with `cplx3`. -/
theorem contDiff_physGradPhase {ε : ℝ} {φ : UnforcedLeray.Space × ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (physGradPhase ε φ) := by
  have hD : ContDiff ℝ ∞ (fun y : UnforcedLeray.Space × ℝ =>
      (fderiv ℝ φ y).comp (ContinuousLinearMap.inl ℝ UnforcedLeray.Space ℝ)) :=
    (hφ.fderiv_right (m := ∞) (by simp)).clm_comp contDiff_const
  have hL : ContDiff ℝ ∞ (InnerProductSpace.toDual ℝ UnforcedLeray.Space).symm := by
    let L : (StrongDual ℝ UnforcedLeray.Space) →L[ℝ] UnforcedLeray.Space :=
      (InnerProductSpace.toDual ℝ UnforcedLeray.Space).symm.toContinuousLinearEquiv.toContinuousLinearMap
    exact L.contDiff
  have hG : ContDiff ℝ ∞ (fun y : UnforcedLeray.Space × ℝ => UnforcedLeray.B0226.gradX φ y) :=
    hL.comp hD
  have hC : ContDiff ℝ ∞ (fun p : ℝ × UnforcedLeray.Space => ((ε • p.2, p.1) : UnforcedLeray.Space × ℝ)) :=
    (contDiff_snd.const_smul ε).prodMk contDiff_fst
  exact (cplx3.contDiff).comp (hG.comp hC)

/-- The fderiv of a `P`-periodic function is `P`-periodic in the time variable. -/
theorem fderiv_periodic_time {P : ℝ} {φ : UnforcedLeray.Space × ℝ → ℝ}
    (hper : ∀ (x : UnforcedLeray.Space) (τ : ℝ), φ (x, τ + P) = φ (x, τ))
    (x : UnforcedLeray.Space) (τ : ℝ) :
    fderiv ℝ φ (x, τ + P) = fderiv ℝ φ (x, τ) := by
  have hfun : (fun w : UnforcedLeray.Space × ℝ => φ (w + ((0 : UnforcedLeray.Space), P))) = φ := by
    funext w
    have hw : w + ((0 : UnforcedLeray.Space), P) = (w.1, w.2 + P) := by
      ext <;> simp
    rw [hw]
    exact hper w.1 w.2
  have h : fderiv ℝ (fun w : UnforcedLeray.Space × ℝ => φ (w + ((0 : UnforcedLeray.Space), P))) (x, τ)
      = fderiv ℝ φ ((x, τ) + ((0 : UnforcedLeray.Space), P)) := by
    rw [fderiv_comp_add_right]
  rw [hfun] at h
  rw [show (x, τ) + ((0 : UnforcedLeray.Space), P) = (x, τ + P) from by ext <;> simp] at h
  exact h.symm

/-- `∇ₓφ` is `P`-periodic in `τ`. -/
theorem gradX_periodic_time {P : ℝ} {φ : UnforcedLeray.Space × ℝ → ℝ}
    (hper : ∀ (x : UnforcedLeray.Space) (τ : ℝ), φ (x, τ + P) = φ (x, τ))
    (x : UnforcedLeray.Space) (τ : ℝ) :
    UnforcedLeray.B0226.gradX φ (x, τ + P) = UnforcedLeray.B0226.gradX φ (x, τ) := by
  unfold UnforcedLeray.B0226.gradX
  rw [fderiv_periodic_time hper x τ]

/-- `physGradPhase ε φ` is a phase test when `φ` is a physical test. -/
theorem physGradPhase_isPhaseTest {ε P : ℝ} (hε : 0 < ε) {φ : UnforcedLeray.Space × ℝ → ℝ}
    (hφ : UnforcedLeray.B0226.IsPhysTest P φ) : IsPhaseTest P (physGradPhase ε φ) := by
  refine ⟨contDiff_physGradPhase hφ.smooth, ?_, ?_⟩
  · intro τ y
    simp only [physGradPhase]
    rw [gradX_periodic_time hφ.periodic]
  · obtain ⟨R, hR⟩ := hφ.bounded
    refine ⟨R / ε, fun τ y hy => ?_⟩
    have hzero : UnforcedLeray.B0226.gradX φ (ε • y, τ) = 0 := by
      apply UnforcedLeray.B0226.gradX_eq_zero_of_notMem
      intro hmem
      have h1 := UnforcedLeray.B0226.tsupport_subset_of_bound hR hmem
      simp only [Set.mem_setOf_eq] at h1
      rw [norm_smul, Real.norm_of_nonneg hε.le] at h1
      have h2 := (div_lt_iff₀ hε).1 hy
      nlinarith
    simp only [physGradPhase]
    rw [hzero, map_zero]

/-- **Sub-lemma 1 (`PartII-a:N01/3/1`).** -/
theorem physGradPhaseSliceTest : UnforcedLeray.Short.PartIIa.N01.PhysGradPhaseSliceTest := by
  intro ε P _ hε φ hφ
  exact (physGradPhase_isPhaseTest hε hφ).isSliceTest 2

end UnforcedLeray.Short.PartIIa.N01
