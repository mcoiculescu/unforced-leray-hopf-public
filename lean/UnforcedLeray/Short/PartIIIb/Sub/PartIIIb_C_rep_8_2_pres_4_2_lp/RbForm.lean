import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_lp.ChartFormOf
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_lp.RbY
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Defs
import UnforcedLeray.Cons.L2.BackgroundConcrete.GraphStateSymmetry
import UnforcedLeray.Cons.L2.BackgroundConcrete.Operators
import UnforcedLeray.Cons.L2.BackgroundConcrete.Fields
import UnforcedLeray.Short.PartIIIa.Compose

/-!
# `RbChartForm` from the repair standing hypotheses (task `PartIII-b:C/rep/8/2/pres/4/2/lp/2`)

Source `the November 2 reference manuscript` 2664-2674 (exact split `U = V + r_b`,
chart), 2681-2688 (normalized phase/space integral in the chart), 121-124 (axisymmetry without
swirl), 5287-5289.

Proof outline.  For a level with `r_b τ = corr z τ`, the family `τ ↦ r_b τ` is jointly continuous,
`C²` off the axis, axisymmetric without swirl, and `2c/R`-periodic in `τ` with `R = ε⁻¹` and
`c = cOf ν` (the period identity `Params.period_eq`).  The criterion
`LpChartForm.axiChartForm_coefChgDens` (ChartFormOf.lean) then gives the chart reading of the
change density of `r_b`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem rbChartForm (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : RbChartForm D := by
  have hlim : Tendsto (retNu D.Pl D.σ₀) atTop (nhds 0) := retNu_tendsto D.σ₀ hst.omega_ne
  have hsmall : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n < dm ^ 3 / 12 :=
    hlim.eventually (gt_mem_nhds (by have := hst.dm_pos; positivity))
  have hnu : ∀ᶠ n : ℕ in atTop, (D.level n).ν ≤ 1 ∧ 0 ≤ rhoRep D.K (D.level n) :=
    nuLeOneRhoNonneg D hst
  unfold RbChartForm
  filter_upwards [hst.actual, hnu, hsmall] with n hact hN hS
  have hR : 0 < (D.level n).ε⁻¹ := inv_pos.2 (D.level n).ε_pos
  obtain ⟨z, -, hV, hrb, -⟩ := hact.split.state
  have hrbf : ∀ τ, D.rb n τ = ((D.level n).params D.Pl).corr z τ := fun τ => congrFun hrb τ
  have hP1 : ((D.level n).params D.Pl).period ≤ 1 :=
    bgCorr_period_le_one hact.regime (le_of_lt hS)
  have hcont : Continuous fun x : ℝ × Space => D.rb n x.1 x.2 := by
    have e : (fun x : ℝ × Space => D.rb n x.1 x.2) =
        fun x => ((D.level n).params D.Pl).corr z x.1 x.2 := by
      funext x
      rw [hrbf x.1]
    rw [e]
    exact UnforcedLeray.Short.IIIa.corr_continuous _ hP1 z
  have hC2 : ∀ τ, ContDiffOn ℝ 2 (D.rb n τ) axisᶜ := by
    intro τ
    rw [hrbf τ]
    refine bgCorr_contDiffOn_offAxis (V := D.V n) (pres := D.pres n) hst.planar.eigenpair
      hact.regime hN.1 rfl z hV ?_ τ
    have e : (fun τ y => D.V n τ y + ((D.level n).params D.Pl).corr z τ y) = (D.level n).U := by
      funext τ y
      simp only [ReturnLevel.U, ← hrbf τ]
      rfl
    rw [e]
    exact hact.profile
  have hper : ∀ τ, D.rb n (τ + 2 * cOf (D.level n).ν / (D.level n).ε⁻¹) = D.rb n τ := by
    intro τ
    have hperiod : ((D.level n).params D.Pl).period = 2 * cOf (D.level n).ν / (D.level n).ε⁻¹ :=
      UnforcedLeray.Cons.C03.Concrete.Params.period_eq ((D.level n).params D.Pl)
    rw [hrbf, hrbf, ← hperiod]
    exact (UnforcedLeray.Cons.C03.Concrete.Params.corr_periodic ((D.level n).params D.Pl) z) τ
  have hax : ∀ τ, AxiNoSwirlPt (D.rb n τ) := by
    intro τ
    have hcτ : Continuous (D.rb n τ) := by
      have h := hcont.comp (continuous_const.prodMk continuous_id : Continuous fun y : Space => (τ, y))
      exact h
    refine axiNoSwirlPt_of_ae hcτ ?_
    rw [hrbf τ]
    exact UnforcedLeray.Cons.C03.Concrete.Params.corr_isAxisymmetricNoSwirl
      ((D.level n).params D.Pl) hP1 z τ
  exact LpChartForm.axiChartForm_coefChgDens (R := (D.level n).ε⁻¹) (c := cOf (D.level n).ν)
    (f := fun τ y => D.rb n τ y) hR hcont.measurable hC2 hper hax

end UnforcedLeray.Short.PartIIIb.Concrete
