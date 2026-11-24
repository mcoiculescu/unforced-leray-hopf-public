import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Int
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9_3.S1.Defs

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem tcIntW : TCIntW := by
  intro σ₁ σ₂ ν μ R P T τ y hctx
  obtain ⟨hσ, hν, hν1, hR1, hP, hμ, hT, hM, hA, hy⟩ := hctx
  have hμ' : -(1 / 4) < μ := lt_of_lt_of_le hσ hμ.1
  have hR : 0 < R := by linarith
  set rOut : ℝ := R * Real.sqrt (5 * ν / 6) with hrOut
  have hr0 : 0 ≤ rOut := by positivity
  have hrr : rOut < ϱ y := by
    have h1 : Real.sqrt (5 * ν / 6) < Real.sqrt ν :=
      Real.sqrt_lt_sqrt (by positivity) (by linarith)
    have h2 : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν := mul_lt_mul_of_pos_left h1 hR
    exact lt_of_lt_of_le h2 hy.1
  obtain ⟨Cb, hCb, hb⟩ := tcd_half hν hμ' hr0 hP hT hM hrr
  have hint : IntegrableOn (fun ρ : ℝ => Cb * (1 + |y 2|) * (ρ - rOut) ^ (-(3 / 2 : ℝ)))
      (Ioi (ϱ y)) := (tcd_int_shift rOut (ϱ y) (by linarith)).const_mul _
  have hsub : Ioi (ϱ y) ⊆ Ioi rOut := Ioi_subset_Ioi hrr.le
  have hcd := tcd_X0_cdOn hν hμ' hr0 hP hT hM τ
  have hz : (0 : ℝ) ≤ 1 + |y 2| := by positivity
  have hup : ∀ ρ ∈ Ioi (ϱ y), 0 ≤ (ρ - rOut) ^ (-(3 / 2 : ℝ)) := fun ρ hρ =>
    Real.rpow_nonneg (by have : ϱ y < ρ := hρ; linarith) _
  have hCb' : ∀ ρ ∈ Ioi (ϱ y), Cb * (ρ - rOut) ^ (-(3 / 2 : ℝ)) ≤
      Cb * (1 + |y 2|) * (ρ - rOut) ^ (-(3 / 2 : ℝ)) := by
    intro ρ hρ
    have := hup ρ hρ
    have h1 : Cb ≤ Cb * (1 + |y 2|) := by nlinarith [abs_nonneg (y 2)]
    exact mul_le_mul_of_nonneg_right h1 this
  have proj : ∀ (f : ℝ → Space), ContinuousOn f (Ioi (ϱ y)) →
      ContinuousOn (fun ρ => ρ * f ρ 2) (Ioi (ϱ y)) := fun f hf =>
    continuousOn_id.mul ((EuclideanSpace.proj (2 : Fin 3)).continuous.comp_continuousOn hf)
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine Integrable.mono' hint ?_ ?_
    · exact (proj _ ((tcd_cont_val hr0 hcd (y 2)).mono hsub)).aestronglyMeasurable
        measurableSet_Ioi
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun ρ hρ => ?_)
      have := (hb τ ρ (y 2) (le_of_lt hρ)).1
      rw [Real.norm_eq_abs]
      exact this.trans (hCb' ρ hρ)
  · refine Integrable.mono' hint ?_ ?_
    · have hW := tcd_Wre_cd hν hμ' hr0 hP hT hM τ
      have hc1 := (proj _ ((tcd_cont_val hr0 hW (y 2)).mono hsub))
      have hc2 : ContinuousOn (fun ρ : ℝ => fderiv ℝ (sepX0 ν μ T τ) (!₂[ρ, 0, y 2] : Space)
          (!₂[ρ, 0, y 2] : Space)) (Ioi (ϱ y)) :=
        ((tcd_cont_fderiv hr0 hcd (y 2)).mono hsub).clm_apply (tcd_pt_cont (y 2)).continuousOn
      have hc3 := (tcd_cont_lap hr0 hcd (y 2)).mono hsub
      have hc4 := (tcd_cont_val hr0 hcd (y 2)).mono hsub
      have hall := tcd_comb_cont (S := Ioi (ϱ y)) (ν := ν) (c := (μ + 1) - 1 / 2)
        ((tcd_cont_val hr0 hW (y 2)).mono hsub) hc2 hc3 hc4
      refine hall.aestronglyMeasurable measurableSet_Ioi |>.congr ?_
      refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun ρ hρ => ?_)
      have hρr : rOut < ϱ (!₂[ρ, 0, y 2] : Space) := by
        rw [tcd_varrho (hr0.trans (hrr.le.trans (le_of_lt hρ)))]
        exact lt_trans hrr hρ
      simp only
      rw [tcd_freeEq hν hμ' hr0 hP hT hM τ hρr]
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun ρ hρ => ?_)
      have := (hb τ ρ (y 2) (le_of_lt hρ)).2.2.2.2.2
      rw [Real.norm_eq_abs]
      exact this
  · refine Integrable.mono' hint ?_ ?_
    · have hc2 : ContinuousOn (fun ρ : ℝ => fderiv ℝ (sepX0 ν μ T τ) (!₂[ρ, 0, y 2] : Space)
          (!₂[ρ, 0, y 2] : Space)) (Ioi (ϱ y)) :=
        ((tcd_cont_fderiv hr0 hcd (y 2)).mono hsub).clm_apply (tcd_pt_cont (y 2)).continuousOn
      exact (proj _ hc2).aestronglyMeasurable measurableSet_Ioi
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun ρ hρ => ?_)
      have := (hb τ ρ (y 2) (le_of_lt hρ)).2.2.2.1
      rw [Real.norm_eq_abs]
      exact this
  · refine Integrable.mono' hint ?_ ?_
    · exact (proj _ ((tcd_cont_lap hr0 hcd (y 2)).mono hsub)).aestronglyMeasurable
        measurableSet_Ioi
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun ρ hρ => ?_)
      have := (hb τ ρ (y 2) (le_of_lt hρ)).2.2.2.2.1
      rw [Real.norm_eq_abs]
      exact this

end UnforcedLeray.Short.PartIIIb.Concrete

end
