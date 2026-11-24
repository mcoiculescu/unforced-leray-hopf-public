import UnforcedLeray.Lib.Axisymmetric.RingChart
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Smoothness of the ring chart off the axis (task `PartIII-b:C/rep/8/2/pres/6/2/1`)

Source `the November 2 reference manuscript`,
lines 1205-1225 (the lift is smooth off the axis for positive time).
The chart is `chart R τ y = (age R y, (phase R τ y, trans R y))`
(`Lib/Axisymmetric/RingChart.lean`), with `age = R²/ϱ²`, `phase = Rτ/2 - (R/2) log age`,
`trans = R y₂/ϱ`.  Off the axis `ϱ > 0`, so every component is `C^∞`.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff

namespace UnforcedLeray.Axi

/-- The age `R²/ϱ²` is `C^∞` off the axis. -/
theorem offAxis_age_contDiffOn (R : ℝ) : ContDiffOn ℝ ∞ (age R) axisᶜ := by
  unfold age
  exact contDiffOn_const.div (contDiffOn_ϱ.pow 2) fun z hz => pow_ne_zero 2 (ϱ_ne_zero hz)

/-- The transverse coordinate `R y₂/ϱ` is `C^∞` off the axis. -/
theorem offAxis_trans_contDiffOn (R : ℝ) : ContDiffOn ℝ ∞ (trans R) axisᶜ := by
  unfold trans
  have h2 : ContDiff ℝ ∞ (fun z : Space => z 2) := by fun_prop
  exact (contDiffOn_const.mul h2.contDiffOn).div contDiffOn_ϱ fun z hz => ϱ_ne_zero hz

/-- The first coordinate of the chart is positive off the axis. -/
theorem chart_fst_pos {R : ℝ} (hR : R ≠ 0) (τ : ℝ) {y : Space} (hy : y ∉ axis) :
    0 < (chart R τ y).1 :=
  age_pos hR hy

/-- **Smoothness of the ring chart off the axis** (source 1205-1225): the map
`(τ, y) ↦ chart R τ y` is `C^∞` on `{(τ, y) | y ∉ axis}`. -/
theorem chart_contDiffOn_offAxis (R : ℝ) (hR : R ≠ 0) :
    ContDiffOn ℝ ∞ (fun x : ℝ × Space => UnforcedLeray.Axi.chart R x.1 x.2)
      {x : ℝ × Space | x.2 ∉ UnforcedLeray.Axi.axis} := by
  have hmap : MapsTo (fun x : ℝ × Space => x.2) {x : ℝ × Space | x.2 ∉ axis} axisᶜ :=
    fun _ hx => hx
  have hsnd : ContDiffOn ℝ ∞ (fun x : ℝ × Space => x.2) {x : ℝ × Space | x.2 ∉ axis} :=
    contDiff_snd.contDiffOn
  have hage : ContDiffOn ℝ ∞ (fun x : ℝ × Space => age R x.2)
      {x : ℝ × Space | x.2 ∉ axis} :=
    (offAxis_age_contDiffOn R).comp hsnd hmap
  have htrans : ContDiffOn ℝ ∞ (fun x : ℝ × Space => trans R x.2)
      {x : ℝ × Space | x.2 ∉ axis} :=
    (offAxis_trans_contDiffOn R).comp hsnd hmap
  have hlog : ContDiffOn ℝ ∞ (fun x : ℝ × Space => Real.log (age R x.2))
      {x : ℝ × Space | x.2 ∉ axis} :=
    hage.log fun x hx => (age_pos hR hx).ne'
  have hτ : ContDiff ℝ ∞ (fun x : ℝ × Space => R * x.1 / 2) := by fun_prop
  have hphase : ContDiffOn ℝ ∞ (fun x : ℝ × Space => phase R x.1 x.2)
      {x : ℝ × Space | x.2 ∉ axis} := by
    unfold phase
    exact hτ.contDiffOn.sub (contDiffOn_const.mul hlog)
  exact hage.prodMk (hphase.prodMk htrans)

end UnforcedLeray.Axi
