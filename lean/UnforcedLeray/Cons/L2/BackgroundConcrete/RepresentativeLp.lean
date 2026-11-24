import UnforcedLeray.Cons.L2.BackgroundConcrete.Operators
import UnforcedLeray.Units.B0411

/-!
# Joint period-cell Lq representative

The selected jointly measurable representative has the actual period-cell Lq integrability of
the phase-space element. This uses only the phase Lq norm, with no graph or PDE premise.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint
open UnforcedLeray.PhaseSpace

theorem memLp_rep_periodCell {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞}
    [Fact (1 ≤ q)] (hqtop : q ≠ ⊤) (w : Yq P q) :
    MemLp (fun z : SpaceTime => rep w z.1 z.2) q
      (volume.restrict (Ioc (0 : ℝ) P ×ˢ (univ : Set Space))) := by
  let S : Set SpaceTime := Ioc (0 : ℝ) P ×ˢ (univ : Set Space)
  let F : SpaceTime → CVec3 := fun z => rep w z.1 z.2
  have hqzero : q ≠ 0 := by
    have hq : (1 : ℝ≥0∞) ≤ q := Fact.out
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one hq)
  have hprod : (volume : Measure SpaceTime).restrict S =
      ((volume : Measure ℝ).restrict (Ioc 0 P)).prod (volume : Measure Space) := by
    simpa only [S, Measure.volume_eq_prod] using
      (Measure.restrict_prod_eq_prod_univ (μ := (volume : Measure ℝ))
        (ν := (volume : Measure Space)) (Ioc 0 P)).symm
  have hsm : AEStronglyMeasurable F ((volume : Measure SpaceTime).restrict S) :=
    (stronglyMeasurable_rep w).aestronglyMeasurable.restrict
  have hnorm : AEMeasurable (fun z : SpaceTime => ‖F z‖ₑ ^ q.toReal)
      (((volume : Measure ℝ).restrict (Ioc 0 P)).prod (volume : Measure Space)) := by
    rw [← hprod]
    exact hsm.enorm.pow_const _
  have hinner (τ : ℝ) :
      (∫⁻ y : Space, ‖F (τ, y)‖ₑ ^ q.toReal ∂volume) =
        ‖w (τ : AddCircle P)‖ₑ ^ q.toReal := by
    calc
      (∫⁻ y : Space, ‖F (τ, y)‖ₑ ^ q.toReal ∂volume) =
          ∫⁻ y : Space, ‖(w (τ : AddCircle P) : Space → CVec3) y‖ₑ ^ q.toReal
          ∂volume := by
            apply lintegral_congr_ae
            filter_upwards [rep_slice w τ] with y hy
            exact congrArg (fun v : CVec3 => ‖v‖ₑ ^ q.toReal) hy
      _ = ‖w (τ : AddCircle P)‖ₑ ^ q.toReal :=
        lintegral_enorm_rpow_Lp (w (τ : AddCircle P)) hqtop
  have hfinite :
      (∫⁻ z : SpaceTime, ‖F z‖ₑ ^ q.toReal ∂((volume : Measure SpaceTime).restrict S)) < ⊤ := by
    rw [hprod]
    have hfub := lintegral_prod (fun z : SpaceTime => ‖F z‖ₑ ^ q.toReal) hnorm
    rw [hfub]
    simp_rw [hinner]
    exact UnforcedLeray.B0411.lintegral_Ioc_lt_top w hqtop
  refine ⟨?_, ?_⟩
  · simpa [F, S] using hsm
  · apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hqzero hqtop).2
    simpa [F, S] using hfinite

#print axioms memLp_rep_periodCell

end UnforcedLeray.Cons.C03.Concrete
