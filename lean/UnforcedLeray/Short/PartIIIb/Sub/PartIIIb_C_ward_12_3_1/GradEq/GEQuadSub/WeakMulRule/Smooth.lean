import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Defs
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Weak product rule for functions smooth in `y` (Lemma C of `WeakMulRule`)

Source `the November 2 reference manuscript`
2562-2564; phase tests have compact `y`-support (2525-2531).

Because the spatial mollifications `a_ε` of a `τ`-measurable function are smooth only in `y`,
the classical `y`-derivative is the slice derivative `dyS` (it coincides with
`PhaseSpace.dy` for jointly differentiable `a`, `dy_eq_dyS`).  The smoothness hypothesis is
`ContDiff ℝ 1` of every `y`-slice; no measurability in `τ` is needed, because the identity holds
for each fixed `τ` and `phaseInt` is an iterated integral.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set
open scoped ContDiff
open UnforcedLeray.Cons.C03.Concrete (phaseInt)

/-- The classical `y_j`-derivative of the `y`-slice of `a` (source 2562-2564). -/
def dyS (j : Fin 3) (a : ℝ × UnforcedLeray.Space → ℂ) (x : ℝ × UnforcedLeray.Space) : ℂ :=
  fderiv ℝ (fun y => a (x.1, y)) x.2 (coordinateVector j)

theorem dy_eq_dyS (j : Fin 3) {φ : ℝ × UnforcedLeray.Space → ℂ}
    (h : Differentiable ℝ φ) : dy j φ = dyS j φ := by
  funext x
  obtain ⟨τ, y⟩ := x
  have h1 : HasFDerivAt (fun y : UnforcedLeray.Space => (τ, y))
      (ContinuousLinearMap.inr ℝ ℝ UnforcedLeray.Space) y := hasFDerivAt_prodMk_right τ y
  have h2 : HasFDerivAt (fun y : UnforcedLeray.Space => φ (τ, y))
      ((fderiv ℝ φ (τ, y)).comp (ContinuousLinearMap.inr ℝ ℝ UnforcedLeray.Space)) y :=
    (h (τ, y)).hasFDerivAt.comp y h1
  simp only [dy, dyS]
  rw [h2.fderiv]
  simp

/-- **Lemma C.** Product rule in the weak `y_j`-sense for functions that are `C¹` in `y`. -/
theorem weakDyS_mul_smooth (P : ℝ) [Fact (0 < P)] (j : Fin 3)
    (a b : ℝ × UnforcedLeray.Space → ℂ)
    (ha : ∀ τ, ContDiff ℝ 1 (fun y => a (τ, y)))
    (hb : ∀ τ, ContDiff ℝ 1 (fun y => b (τ, y))) :
    WeakDyS P j (fun x => a x * b x) (fun x => dyS j a x * b x + a x * dyS j b x) := by
  intro φ hφ
  obtain ⟨R, hR⟩ := hφ.bounded_support
  unfold phaseInt
  rw [← smul_neg]
  congr 1
  rw [← integral_neg]
  refine setIntegral_congr_fun measurableSet_Ioc fun τ _ => ?_
  simp only
  set ψ : UnforcedLeray.Space → ℂ := fun y => φ (τ, y) with hψ
  set F : UnforcedLeray.Space → ℂ := fun y => a (τ, y) * b (τ, y) with hF
  have hψs : ContDiff ℝ ∞ ψ := hφ.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hψc : HasCompactSupport ψ :=
    HasCompactSupport.intro (isCompact_closedBall (0 : UnforcedLeray.Space) R) fun y hy => by
      apply hR
      simpa [not_le] using hy
  have hFs : ContDiff ℝ 1 F := (ha τ).mul (hb τ)
  have hψ1 : Continuous (fun y => fderiv ℝ ψ y (coordinateVector j)) :=
    ((hψs.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hF1 : Continuous (fun y => fderiv ℝ F y (coordinateVector j)) :=
    ((hFs.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hψ1c : HasCompactSupport (fun y => fderiv ℝ ψ y (coordinateVector j)) :=
    hψc.fderiv_apply (𝕜 := ℝ) (coordinateVector j)
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure UnforcedLeray.Space)) (f := ψ) (g := F)
    (v := coordinateVector j)
    ((hψ1.mul hFs.continuous).integrable_of_hasCompactSupport hψ1c.mul_right)
    ((hψs.continuous.mul hF1).integrable_of_hasCompactSupport hψc.mul_right)
    ((hψs.continuous.mul hFs.continuous).integrable_of_hasCompactSupport hψc.mul_right)
    (fun x _ => (hψs.differentiable (by simp)) x)
    (fun x _ => (hFs.differentiable (by simp)) x)
  have hdy : ∀ y, dy j φ (τ, y) = fderiv ℝ ψ y (coordinateVector j) := by
    intro y
    have := congrFun (dy_eq_dyS j (hφ.smooth.differentiable (by simp))) (τ, y)
    simpa [dyS] using this
  have hprod : ∀ y, fderiv ℝ F y (coordinateVector j) =
      dyS j a (τ, y) * b (τ, y) + a (τ, y) * dyS j b (τ, y) := by
    intro y
    have h1 := ((ha τ).differentiable (by simp)) y
    have h2 := ((hb τ).differentiable (by simp)) y
    rw [hF, fderiv_fun_mul h1 h2]
    simp [dyS]
    ring
  simp only [hdy, hprod] at key ⊢
  rw [key, neg_neg]
