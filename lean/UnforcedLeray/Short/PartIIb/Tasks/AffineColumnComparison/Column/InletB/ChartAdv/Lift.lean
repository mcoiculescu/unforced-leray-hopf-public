import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.InletB.ChartAdv.Chain

/-!
# Part II-b, task `PartII-b:G4/3/4/1/D` (`chartAdv_lift`)

Source of record: `the November 2 reference manuscript`, SP 1919-1921, 2007-2012.
Both ring lifts are meridional lifts of the scaled profiles `U = √(R²/ρ²) b(merChart ·)` and
`V = √(R²/ρ²) d(merChart ·)` (`Axi.Nv_eq_liftMer`). The advection identity
`Axi.advection_liftMer` gives the sum `merAdv U V + merAdv V U` at `mer y`, and the chain rule
`chartAdv_dRho_dz` (task C) turns the profile derivatives into `Q_ε` and `∂_η` terms, with the
factor `m.1 = R²/ρ²` of the target profile.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- The scaled ring profile `ρ ↦ √(R²/ρ²) φ(merChart R τ ρ)` is differentiable at a meridional
point off the axis, where `φ` is differentiable at the chart point. -/
theorem chartAdv_sqrtProf_diffAt {R τ : ℝ} (hR : R ≠ 0) {p : ℝ × ℝ} (hp : p.1 ≠ 0)
    {φ : Coord → Axi.Merid} (hφ : DifferentiableAt ℝ φ (Axi.merChart R τ p)) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ => √(R ^ 2 / q.1 ^ 2) • φ (Axi.merChart R τ q)) p := by
  have hs : DifferentiableAt ℝ (fun q : ℝ × ℝ => R ^ 2 / q.1 ^ 2) p := by
    simp only [div_eq_mul_inv]
    exact (differentiableAt_const (R ^ 2)).fun_mul
      ((differentiableAt_fst.pow 2).fun_inv (pow_ne_zero 2 hp))
  have hne : R ^ 2 / p.1 ^ 2 ≠ 0 := div_ne_zero (pow_ne_zero 2 hR) (pow_ne_zero 2 hp)
  exact (hs.sqrt hne).smul (hφ.comp p (Axi.differentiableAt_merChart hR τ hp))

/-- Two meridional profiles whose values at `mer y` add to the value of a third lift to the same
lift: pointwise identity at the meridional point suffices. -/
theorem chartAdv_liftMer_add (F H G : ℝ × ℝ → Axi.Merid) (y : Space)
    (h : F (Axi.mer y) + H (Axi.mer y) = G (Axi.mer y)) :
    Axi.liftMer F y + Axi.liftMer H y = Axi.liftMer G y := by
  unfold Axi.liftMer
  rw [← h]
  simp only [PiLp.add_apply, add_smul]
  abel

/-- **`PartII-b:G4/3/4/1/D`**: the advection test of the ring lift is the lift of the profile
advection sum with the factor `m.1`. -/
theorem chartAdv_lift (R : ℝ) (hR : 0 < R) (b d : Coord → Axi.Merid) (τ : ℝ) (y : Space)
    (hy : y ∉ Axi.axis) (hb : DifferentiableAt ℝ b (Axi.chart R τ y))
    (hd : DifferentiableAt ℝ d (Axi.chart R τ y)) :
    Axi.advection (Axi.Nv R b τ) (Axi.Nv R d τ) y + Axi.advection (Axi.Nv R d τ) (Axi.Nv R b τ) y =
      Axi.Nv R (fun m => m.1 • (b m 0 • qEps R⁻¹ d m + b m 1 • Axi.dEta d m +
        (d m 0 • qEps R⁻¹ b m + d m 1 • Axi.dEta b m))) τ y := by
  have hR0 : R ≠ 0 := hR.ne'
  have hpne : (Axi.mer y).1 ≠ 0 := fun h => hy ((Axi.mem_axis_iff y).2 h)
  have hpos : 0 < (Axi.mer y).1 := lt_of_le_of_ne (Axi.ϱ_nonneg y) (Ne.symm hpne)
  have hbm : DifferentiableAt ℝ b (Axi.merChart R τ (Axi.mer y)) := by
    rw [← Axi.chart_eq_merChart]; exact hb
  have hdm : DifferentiableAt ℝ d (Axi.merChart R τ (Axi.mer y)) := by
    rw [← Axi.chart_eq_merChart]; exact hd
  have hUb := chartAdv_sqrtProf_diffAt hR0 hpne hbm
  have hUd := chartAdv_sqrtProf_diffAt hR0 hpne hdm
  obtain ⟨hρU, hzU⟩ := chartAdv_dRho_dz R hR b τ (Axi.mer y) hpos hbm
  obtain ⟨hρV, hzV⟩ := chartAdv_dRho_dz R hR d τ (Axi.mer y) hpos hdm
  unfold Axi.dRho at hρU hρV
  rw [Axi.Nv_eq_liftMer R b τ, Axi.Nv_eq_liftMer R d τ,
    Axi.advection_liftMer _ hy hUd, Axi.advection_liftMer _ hy hUb,
    Axi.Nv_eq_liftMer R (fun m => m.1 • (b m 0 • qEps R⁻¹ d m + b m 1 • Axi.dEta d m +
      (d m 0 • qEps R⁻¹ b m + d m 1 • Axi.dEta b m))) τ]
  refine chartAdv_liftMer_add _ _ _ y ?_
  have e1 : (Axi.merChart R τ (Axi.mer y)).1 = R ^ 2 / (Axi.mer y).1 ^ 2 := rfl
  simp only [Axi.merAdv, PiLp.smul_apply, smul_eq_mul, e1]
  rw [hρU, hzU, hρV, hzV]
  module

end UnforcedLeray.Short.IIb
