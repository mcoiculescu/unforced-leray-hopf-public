import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_2.Shell.Defs

/-!
# Smoothness and axial invariance of the ring-chart pieces off the axis

Source `the November 2 reference manuscript`
lines 1206-1222 (the chart `s = R²/ϱ²`, `η = R z/ϱ`, the phase, the lift).  Off the axis the
age, phase, transverse coordinate, chart and frame factor are `C^∞`; the age, the frame factor
and `log s` are invariant under `y ↦ y + t e₃`; the jets of `∂_ξ b` are jets of `b` one order up.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.Shell

open UnforcedLeray.Axi

theorem ϱ_add_e3 (x : UnforcedLeray.Space) (t : ℝ) : ϱ (x + t • e3) = ϱ x := by
  simp [ϱ, e3_apply]

theorem hor_add_e3 (x : UnforcedLeray.Space) (t : ℝ) : hor (x + t • e3) = hor x := by
  ext i
  fin_cases i <;> simp [hor, e3_apply]

theorem eR_add_e3 (x : UnforcedLeray.Space) (t : ℝ) : eR (x + t • e3) = eR x := by
  unfold eR
  rw [ϱ_add_e3, hor_add_e3]

theorem age_add_e3 (R : ℝ) (x : UnforcedLeray.Space) (t : ℝ) : age R (x + t • e3) = age R x := by
  unfold age
  rw [ϱ_add_e3]

theorem frameL_add_e3 (x : UnforcedLeray.Space) (t : ℝ) : frameL (x + t • e3) = frameL x := by
  unfold frameL
  rw [eR_add_e3]

theorem frameFac_add_e3 (R : ℝ) (x : UnforcedLeray.Space) (t : ℝ) :
    frameFac R (x + t • e3) = frameFac R x := by
  unfold frameFac
  rw [age_add_e3, frameL_add_e3]

theorem notMem_axis_of_le {ρ0 : ℝ} (hρ0 : 0 < ρ0) {y : UnforcedLeray.Space} (hy : ρ0 ≤ ϱ y) :
    y ∉ axis := by
  rw [mem_axis_iff]
  exact (lt_of_lt_of_le hρ0 hy).ne'

theorem contDiffOn_age (R : ℝ) : ContDiffOn ℝ ∞ (age R) axisᶜ := by
  unfold age
  exact contDiffOn_const.div (contDiffOn_ϱ.pow 2) fun _ hx => pow_ne_zero 2 (ϱ_ne_zero hx)

theorem contDiffOn_log_age {R : ℝ} (hR : R ≠ 0) :
    ContDiffOn ℝ ∞ (fun y => Real.log (age R y)) axisᶜ :=
  (contDiffOn_age R).log fun _ hx => (age_pos hR hx).ne'

theorem contDiffOn_phase {R : ℝ} (hR : R ≠ 0) (τ : ℝ) : ContDiffOn ℝ ∞ (phase R τ) axisᶜ := by
  unfold phase
  exact contDiffOn_const.sub (contDiffOn_const.mul (contDiffOn_log_age hR))

theorem contDiffOn_inv_ϱ : ContDiffOn ℝ ∞ (fun y => (ϱ y)⁻¹) axisᶜ :=
  contDiffOn_ϱ.inv fun _ hx => ϱ_ne_zero hx

theorem contDiffOn_trans (R : ℝ) : ContDiffOn ℝ ∞ (Axi.trans R) axisᶜ := by
  unfold Axi.trans
  have h2 : ContDiff ℝ ∞ (fun x : UnforcedLeray.Space => x 2) := by fun_prop
  exact ((contDiff_const.mul h2).contDiffOn).div contDiffOn_ϱ fun _ hx => ϱ_ne_zero hx

theorem contDiffOn_chart {R : ℝ} (hR : R ≠ 0) (τ : ℝ) : ContDiffOn ℝ ∞ (chart R τ) axisᶜ :=
  (contDiffOn_age R).prodMk ((contDiffOn_phase hR τ).prodMk (contDiffOn_trans R))

theorem contDiffOn_frameL : ContDiffOn ℝ ∞ frameL axisᶜ := by
  unfold frameL
  exact (contDiffOn_const.smulRight contDiffOn_eR).add contDiffOn_const

theorem contDiffOn_frameFac {R : ℝ} (hR : R ≠ 0) : ContDiffOn ℝ ∞ (frameFac R) axisᶜ := by
  unfold frameFac
  exact ((contDiffOn_age R).sqrt fun _ hx => (age_pos hR hx).ne').smul contDiffOn_frameL

theorem contDiffOn_Nv {R : ℝ} (hR : R ≠ 0) {b : ℝ × (ℝ × ℝ) → Merid} (hb : ContDiff ℝ ∞ b)
    (τ : ℝ) : ContDiffOn ℝ ∞ (Nv R b τ) axisᶜ := by
  have hbc : ContDiffOn ℝ ∞ (fun y => b (chart R τ y)) axisᶜ :=
    hb.comp_contDiffOn (contDiffOn_chart hR τ)
  exact (contDiffOn_frameFac hR).clm_apply hbc

/-- `∂_ξ b` is smooth. -/
theorem contDiff_dQ {b : ℝ × (ℝ × ℝ) → Merid} (hb : ContDiff ℝ ∞ b) : ContDiff ℝ ∞ (dQ b) := by
  have h : ContDiff ℝ ∞ (fun m => fderiv ℝ b m) := hb.fderiv_right (m := ∞) le_rfl
  exact h.clm_apply contDiff_const

/-- The jets of `∂_ξ b` are jets of `b` one order up. -/
theorem norm_iteratedFDeriv_dQ_le {b : ℝ × (ℝ × ℝ) → Merid} (hb : ContDiff ℝ ∞ b) (l : ℕ)
    (m : ℝ × (ℝ × ℝ)) : ‖iteratedFDeriv ℝ l (dQ b) m‖ ≤ ‖iteratedFDeriv ℝ (l + 1) b m‖ := by
  have h : ContDiff ℝ ∞ (fun m => fderiv ℝ b m) := hb.fderiv_right (m := ∞) le_rfl
  have h1 := norm_iteratedFDeriv_clm_apply_const (c := ((0 : ℝ), ((1 : ℝ), (0 : ℝ))))
    (h.contDiffAt (x := m)) (n := l) (by exact_mod_cast le_top)
  have hn : ‖((0 : ℝ), ((1 : ℝ), (0 : ℝ)))‖ = 1 := by simp [Prod.norm_def]
  rw [hn, one_mul, norm_iteratedFDeriv_fderiv] at h1
  exact h1

end UnforcedLeray.Short.PartIIIb.Concrete.Shell
