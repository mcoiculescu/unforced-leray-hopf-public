import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Lap.Psi

/-!
# Radial calculus for `y ↦ g(ϱ y)` off the axis (`TCLeibniz` leaves)

Source `the November 2 reference manuscript` 3700-3712, 4176-4214:
`∇(g∘ϱ) = g'(ϱ) e_r`, `y·∇(g∘ϱ) = ϱ g'(ϱ)`, `Δ(g∘ϱ) = g''(ϱ) + g'(ϱ)/ϱ`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The scalar Laplacian `Σ_j ∂_j ∂_j φ`. -/
def tcleLapS (φ : Space → ℝ) (y : Space) : ℝ :=
  ∑ j : Fin 3, fderiv ℝ (fun y' => fderiv ℝ φ y' (coordinateVector j)) y (coordinateVector j)

theorem tcle_notaxis {y : Space} (h : 0 < ϱ y) : y ∉ axis := fun hh => by
  have := (mem_axis_iff y).1 hh
  linarith

theorem tcle_hasFDeriv_comp {g : ℝ → ℝ} {y : Space} (h : 0 < ϱ y)
    (hg : DifferentiableAt ℝ g (ϱ y)) :
    HasFDerivAt (fun y' => g (ϱ y')) (deriv g (ϱ y) • ϱD y) y :=
  hg.hasDerivAt.comp_hasFDerivAt y (hasFDerivAt_ϱ (tcle_notaxis h))

theorem tcle_fderiv_comp {g : ℝ → ℝ} {y : Space} (h : 0 < ϱ y)
    (hg : DifferentiableAt ℝ g (ϱ y)) (v : Space) :
    fderiv ℝ (fun y' => g (ϱ y')) y v = deriv g (ϱ y) * ((y 0 * v 0 + y 1 * v 1) / ϱ y) := by
  rw [(tcle_hasFDeriv_comp h hg).fderiv]
  simp [ϱD_apply]

theorem tcle_dy_comp {g : ℝ → ℝ} {y : Space} (h : 0 < ϱ y)
    (hg : DifferentiableAt ℝ g (ϱ y)) :
    fderiv ℝ (fun y' => g (ϱ y')) y y = ϱ y * deriv g (ϱ y) := by
  rw [tcle_fderiv_comp h hg, tcl_sqsum h]
  field_simp

theorem tcle_lapS_comp {g : ℝ → ℝ} {y : Space} (h : 0 < ϱ y) (hg : ContDiffAt ℝ 2 g (ϱ y)) :
    tcleLapS (fun y' => g (ϱ y')) y = deriv (deriv g) (ϱ y) + deriv g (ϱ y) / ϱ y := by
  have hdg : DifferentiableAt ℝ (deriv g) (ϱ y) := by
    have h1 : DifferentiableAt ℝ (fderiv ℝ g) (ϱ y) :=
      (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have : deriv g = fun r => fderiv ℝ g r 1 := rfl
    rw [this]
    exact h1.clm_apply (differentiableAt_const _)
  set κ : ℝ → ℝ := fun r => deriv g r / r with hκ
  have hκd : HasDerivAt κ (deriv (deriv g) (ϱ y) / ϱ y - deriv g (ϱ y) / ϱ y ^ 2) (ϱ y) := by
    have := hdg.hasDerivAt.div (hasDerivAt_id (ϱ y)) h.ne'
    have e : (deriv (deriv g) (ϱ y) * id (ϱ y) - deriv g (ϱ y) * 1) / id (ϱ y) ^ 2 =
        deriv (deriv g) (ϱ y) / ϱ y - deriv g (ϱ y) / ϱ y ^ 2 := by
      simp only [id]
      field_simp
    rw [e] at this
    exact this
  have hev : ∀ᶠ y' in nhds y, 0 < ϱ y' ∧ DifferentiableAt ℝ g (ϱ y') := by
    have e1 : ∀ᶠ y' in nhds y, 0 < ϱ y' := continuous_ϱ.continuousAt.eventually (lt_mem_nhds h)
    have e2 : ∀ᶠ y' in nhds y, DifferentiableAt ℝ g (ϱ y') := by
      have : ∀ᶠ r in nhds (ϱ y), DifferentiableAt ℝ g r :=
        (hg.eventually (by simp)).mono fun r hr => hr.differentiableAt (by norm_num)
      exact continuous_ϱ.continuousAt.eventually this
    exact e1.and e2
  have hk : DifferentiableAt ℝ (fun y' => κ (ϱ y')) y := (tcle_hasFDeriv_comp (g := κ) h
    hκd.differentiableAt).differentiableAt
  unfold tcleLapS
  have hj : ∀ j : Fin 3, (fun y' => fderiv ℝ (fun y' => g (ϱ y')) y' (coordinateVector j)) =ᶠ[nhds y]
      fun y' => if j = 0 then y' 0 * κ (ϱ y') else if j = 1 then y' 1 * κ (ϱ y') else 0 := by
    intro j
    filter_upwards [hev] with y' ⟨hy', hgy'⟩
    rw [tcle_fderiv_comp hy' hgy']
    fin_cases j
    · simp [coordinateVector, hκ]; field_simp
    · simp [coordinateVector, hκ]; field_simp
    · simp [coordinateVector]
  have hκ' := (tcle_hasFDeriv_comp (g := κ) h hκd.differentiableAt)
  rw [Fin.sum_univ_three]
  rw [(hj 0).fderiv_eq, (hj 1).fderiv_eq, (hj 2).fderiv_eq]
  simp only [Fin.isValue, if_true, show ¬ ((1 : Fin 3) = 0) from by decide, if_false,
    show ¬ ((2 : Fin 3) = 0) from by decide, show ¬ ((2 : Fin 3) = 1) from by decide,
    if_true]
  have f0 := tcl_fd_mul 0 hk (coordinateVector 0)
  have f1 := tcl_fd_mul 1 hk (coordinateVector 1)
  have hd := hκd.deriv
  have g0 := tcle_fderiv_comp (g := κ) h hκd.differentiableAt (coordinateVector 0)
  have g1 := tcle_fderiv_comp (g := κ) h hκd.differentiableAt (coordinateVector 1)
  rw [hd] at g0 g1
  rw [f0, f1, g0, g1]
  have hsq := tcl_sqsum h
  simp only [coordinateVector, EuclideanSpace.single_apply] at *
  simp
  have hρ := h.ne'
  simp only [hκ]
  field_simp
  linear_combination (deriv (deriv g) (ϱ y) * ϱ y - deriv g (ϱ y)) * hsq

end UnforcedLeray.Short.PartIIIb.Concrete
