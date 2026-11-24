import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_5_1
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# `PartIII-b:C/grad/3/5/1` task T1: `TsumContDiffOnBounds`

Generic lattice-sum smoothness on an open convex set: a `tsum` of `C^n` functions whose
iterated derivatives up to order `n` have summable uniform bounds on `U` is `C^n` on `U`.
Mathlib's `contDiff_tsum` needs global bounds, so the proof localizes to `U` by induction on `n`,
following `perDeriv_contDiffOn_aux`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Iterated within-derivatives of a derivative family are iterated derivatives one order up,
on an open set. -/
lemma tsumCDO_iteratedWithin_fderiv {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (U : Set E) (hU : IsOpen U) (g : E → F)
    (k : ℕ) (x : E) (hx : x ∈ U) :
    ‖iteratedFDerivWithin ℝ k (fun y => fderiv ℝ g y) U x‖ =
      ‖iteratedFDerivWithin ℝ (k + 1) g U x‖ := by
  rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) k hU hx,
    iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (k + 1) hU hx, norm_iteratedFDeriv_fderiv]

/-- Induction core: finite-order smoothness of a termwise-bounded series on an open convex set. -/
theorem tsumCDO_aux (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (U : Set E)
    (hU : IsOpen U) (hUc : Convex ℝ U) (n : ℕ) :
    ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      (f : ℤ → E → F) (v : ℕ → ℤ → ℝ), (∀ i, ContDiffOn ℝ n (f i) U) →
      (∀ k ≤ n, Summable (v k)) →
      (∀ k ≤ n, ∀ i (x : E), x ∈ U → ‖iteratedFDerivWithin ℝ k (f i) U x‖ ≤ v k i) →
      ContDiffOn ℝ n (fun y => ∑' i, f i y) U := by
  induction n with
  | zero =>
    intro F _ _ _ f v hf hv hb
    refine contDiffOn_zero.2 (continuousOn_tsum (fun i => (hf i).continuousOn) (hv 0 le_rfl) ?_)
    intro i y hy
    have h := hb 0 le_rfl i y hy
    rwa [norm_iteratedFDerivWithin_zero] at h
  | succ n ih =>
    intro F _ _ _ f v hf hv hb
    have hf1 : ∀ i, ContDiffOn ℝ ((n : WithTop ℕ∞) + 1) (f i) U := by
      intro i
      have h := hf i
      rw [Nat.cast_succ] at h
      exact h
    have hdiff : ∀ i, DifferentiableOn ℝ (f i) U := fun i =>
      ((contDiffOn_succ_iff_fderiv_of_isOpen hU).1 (hf1 i)).1
    have hfd : ∀ i, ContDiffOn ℝ n (fderiv ℝ (f i)) U := fun i =>
      ((contDiffOn_succ_iff_fderiv_of_isOpen hU).1 (hf1 i)).2.2
    have hb0 : ∀ i (y : E), y ∈ U → ‖f i y‖ ≤ v 0 i := by
      intro i y hy
      have h := hb 0 (Nat.zero_le _) i y hy
      rwa [norm_iteratedFDerivWithin_zero] at h
    have hbd1 : ∀ i (y : E), y ∈ U → ‖fderiv ℝ (f i) y‖ ≤ v 1 i := by
      intro i y hy
      have h := tsumCDO_iteratedWithin_fderiv U hU (f i) 0 y hy
      rw [norm_iteratedFDerivWithin_zero] at h
      rw [h]
      exact hb 1 (by omega) i y hy
    have hdiffS : ∀ y ∈ U, HasFDerivAt (fun z => ∑' i, f i z) (∑' i, fderiv ℝ (f i) y) y := by
      intro y hy
      refine hasFDerivAt_tsum_of_isPreconnected (f := f) (f' := fun i z => fderiv ℝ (f i) z)
        (hv 1 (by omega)) hU hUc.isPreconnected
        (fun i z hz => ((hdiff i).differentiableAt (hU.mem_nhds hz)).hasFDerivAt)
        (fun i z hz => hbd1 i z hz) hy (Summable.of_norm_bounded (hv 0 (by omega))
          (fun i => hb0 i y hy)) hy
    have htsum : ∀ y ∈ U, fderiv ℝ (fun z => ∑' i, f i z) y = ∑' i, fderiv ℝ (f i) y :=
      fun y hy => (hdiffS y hy).fderiv
    have hbk : ∀ k ≤ n, ∀ i (x : E), x ∈ U →
        ‖iteratedFDerivWithin ℝ k (fun y => fderiv ℝ (f i) y) U x‖ ≤ v (k + 1) i := by
      intro k hk i x hx
      rw [tsumCDO_iteratedWithin_fderiv U hU (f i) k x hx]
      exact hb (k + 1) (by omega) i x hx
    have hv' : ∀ k ≤ n, Summable (v (k + 1)) := fun k hk => hv (k + 1) (by omega)
    have hcong := ih (E →L[ℝ] F) (fun i => fderiv ℝ (f i)) (fun k => v (k + 1)) hfd hv' hbk
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun y hy => (hdiffS y hy).differentiableAt.differentiableWithinAt,
      fun h => absurd h (by simp), ?_⟩
    exact hcong.congr (fun y hy => htsum y hy)

/-- Smoothness of lattice sums with summable termwise derivative bounds on open convex sets. -/
theorem tsumContDiffOnBounds : TsumContDiffOnBounds := by
  intro E F _ _ _ _ _ U hU hUc n f v hf hv hb
  exact tsumCDO_aux E U hU hUc n F f v hf hv hb

end UnforcedLeray.Short.PartIIIb.Concrete
