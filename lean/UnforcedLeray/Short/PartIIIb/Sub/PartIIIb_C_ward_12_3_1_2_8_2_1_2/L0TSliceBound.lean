import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_2.Statements

/-!
# `l0TSliceBound`: pointwise control of `L₀ᵗ` by slice derivatives

Proves `L0TSliceBound` (`Statements.lean`), source lines 1446-1455.
`L₀ᵗF = -∂_τF + ½ y·∇F + F - ν ΔF`; each spatial derivative of the phase test is bounded by the
operator norm of the slice derivative (`iteratedFDeriv`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.SolApprox

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.B0412 UnforcedLeray.RieszLp
open UnforcedLeray.Cons.C03.Concrete
open NavierStokesR3.ComparisonCutoffs

private theorem l0t_fderiv_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : ℝ × Space → E} (hH : ContDiff ℝ ∞ H) (τ : ℝ) (y v : Space) :
    fderiv ℝ (fun x : Space => H (τ, x)) y v = fderiv ℝ H (τ, y) (0, v) := by
  have hAt := hH.differentiable (by simp) (τ, y)
  have hcomp := hAt.hasFDerivAt.comp y (hasFDerivAt_prodMk_right τ y)
  have heq := hcomp.fderiv
  change fderiv ℝ (fun x : Space => H (τ, x)) y = _ at heq
  rw [heq]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]

private theorem l0t_dy_slice {H : ℝ × Space → CVec3} (hH : ContDiff ℝ ∞ H) (τ : ℝ) (y : Space)
    (j : Fin 3) :
    dy j H (τ, y) = fderiv ℝ (fun x : Space => H (τ, x)) y (coordinateVector j) := by
  simp only [dy]
  rw [l0t_fderiv_slice hH]

private theorem l0t_dy_dy_slice {H : ℝ × Space → CVec3} (hH : ContDiff ℝ ∞ H) (τ : ℝ) (y : Space)
    (j : Fin 3) :
    dy j (dy j H) (τ, y) =
      iteratedFDeriv ℝ 2 (fun x : Space => H (τ, x)) y ![coordinateVector j, coordinateVector j] := by
  have hG : ContDiff ℝ ∞ (dy j H) := by
    unfold dy
    exact (hH.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have h1 : dy j (dy j H) (τ, y) =
      fderiv ℝ (fun x : Space => dy j H (τ, x)) y (coordinateVector j) :=
    l0t_dy_slice hG τ y j
  rw [h1]
  have h2 : (fun x : Space => dy j H (τ, x)) =
      fun x : Space => fderiv ℝ (fun z : Space => H (τ, z)) x (coordinateVector j) := by
    funext x
    exact l0t_dy_slice hH τ x j
  rw [h2]
  have hS : ContDiff ℝ ∞ (fun z : Space => H (τ, z)) := hH.comp (contDiff_const.prodMk contDiff_id)
  have hc : DifferentiableAt ℝ (fun x : Space => fderiv ℝ (fun z : Space => H (τ, z)) x) y :=
    (hS.fderiv_right (m := ∞) (by simp)).differentiable (by simp) y
  have hu : DifferentiableAt ℝ (fun _ : Space => coordinateVector j) y := differentiableAt_const _
  rw [fderiv_clm_apply hc hu]
  simp

private theorem l0t_norm_dy_le {H : ℝ × Space → CVec3} (hH : ContDiff ℝ ∞ H) (τ : ℝ) (y : Space)
    (j : Fin 3) :
    ‖dy j H (τ, y)‖ ≤ ‖iteratedFDeriv ℝ 1 (fun x : Space => H (τ, x)) y‖ := by
  rw [l0t_dy_slice hH, norm_iteratedFDeriv_one]
  have h := (fderiv ℝ (fun x : Space => H (τ, x)) y).le_opNorm (coordinateVector j)
  simpa [UnforcedLeray.PhaseSpace.norm_coordinateVector] using h

private theorem l0t_norm_dy_dy_le {H : ℝ × Space → CVec3} (hH : ContDiff ℝ ∞ H) (τ : ℝ) (y : Space)
    (j : Fin 3) :
    ‖dy j (dy j H) (τ, y)‖ ≤ ‖iteratedFDeriv ℝ 2 (fun x : Space => H (τ, x)) y‖ := by
  rw [l0t_dy_dy_slice hH]
  have h := (iteratedFDeriv ℝ 2 (fun x : Space => H (τ, x)) y).le_opNorm
    ![coordinateVector j, coordinateVector j]
  refine h.trans ?_
  simp [Fin.prod_univ_two, UnforcedLeray.PhaseSpace.norm_coordinateVector]

private theorem l0t_norm_lapT_le {H : ℝ × Space → CVec3} (hH : ContDiff ℝ ∞ H) (τ : ℝ) (y : Space) :
    ‖lapT H (τ, y)‖ ≤ 3 * ‖iteratedFDeriv ℝ 2 (fun x : Space => H (τ, x)) y‖ := by
  rw [show lapT H (τ, y) = ∑ j : Fin 3, dy j (dy j H) (τ, y) from rfl]
  refine (norm_sum_le _ _).trans ?_
  simp only [Fin.sum_univ_three]
  have h0 := l0t_norm_dy_dy_le hH τ y 0
  have h1 := l0t_norm_dy_dy_le hH τ y 1
  have h2 := l0t_norm_dy_dy_le hH τ y 2
  linarith

private theorem l0t_norm_radialT_le {H : ℝ × Space → CVec3} (hH : ContDiff ℝ ∞ H) (τ : ℝ)
    (y : Space) :
    ‖radialT H (τ, y)‖ ≤ 3 * ‖y‖ * ‖iteratedFDeriv ℝ 1 (fun x : Space => H (τ, x)) y‖ := by
  rw [show radialT H (τ, y) = ∑ j : Fin 3, (y j) • dy j H (τ, y) from rfl]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ j : Fin 3, ‖(y j) • dy j H (τ, y)‖ ≤
      ‖y‖ * ‖iteratedFDeriv ℝ 1 (fun x : Space => H (τ, x)) y‖ := by
    intro j
    rw [norm_smul, Real.norm_eq_abs]
    apply mul_le_mul _ (l0t_norm_dy_le hH τ y j) (norm_nonneg _) (norm_nonneg _)
    have := PiLp.norm_apply_le y j
    simpa [Real.norm_eq_abs] using this
  simp only [Fin.sum_univ_three]
  have h0 := hterm 0
  have h1 := hterm 1
  have h2 := hterm 2
  linarith

theorem l0TSliceBound : UnforcedLeray.Short.PartIIIb.Concrete.SolApprox.L0TSliceBound := by
  intro F hF ν hν τ y
  have hL : L0T ν F (τ, y) = -dτ F (τ, y) + (1 / 2 : ℝ) • radialT F (τ, y) + F (τ, y)
      - ν • lapT F (τ, y) := by
    simp only [L0T, driftT, nuLapT, Pi.sub_apply, Pi.smul_apply]
    module
  rw [hL]
  have hrad := l0t_norm_radialT_le hF τ y
  have hlap := l0t_norm_lapT_le hF τ y
  have hn1 := norm_sub_le (-dτ F (τ, y) + (1 / 2 : ℝ) • radialT F (τ, y) + F (τ, y))
    (ν • lapT F (τ, y))
  have ht := norm_add₃_le (a := -dτ F (τ, y)) (b := (1 / 2 : ℝ) • radialT F (τ, y))
    (c := F (τ, y))
  have e1 : ‖-dτ F (τ, y)‖ = ‖dτ F (τ, y)‖ := norm_neg _
  have e2 : ‖(1 / 2 : ℝ) • radialT F (τ, y)‖ = (1 / 2) * ‖radialT F (τ, y)‖ := by
    rw [norm_smul]; norm_num
  have e3 : ‖ν • lapT F (τ, y)‖ = ν * ‖lapT F (τ, y)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hν]
  have hlap' := mul_le_mul_of_nonneg_left hlap hν
  have hy : 0 ≤ ‖y‖ * ‖iteratedFDeriv ℝ 1 (fun x : Space => F (τ, x)) y‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  linarith [norm_nonneg (F (τ, y))]
