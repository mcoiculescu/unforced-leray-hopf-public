import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_2_3_2.Fubini

/-!
# Local integrability of the slice pairing (helper for `pepsC0SliceDivFreeAE`)
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem hj3_pos_bound {K : Set ℝ} (hK : IsCompact K) (hpos : K ⊆ Ioi 0) :
    ∃ a b : ℝ, 0 < a ∧ K ⊆ Icc a b := by
  rcases K.eq_empty_or_nonempty with h | hne
  · exact ⟨1, 1, one_pos, by rw [h]; exact empty_subset _⟩
  obtain ⟨m, hm, hmin⟩ := hK.exists_isMinOn hne continuousOn_id
  obtain ⟨M, hM⟩ := hK.bddAbove
  exact ⟨m, M, hpos hm, fun x hx => ⟨(hmin hx : m ≤ x), (hM hx : x ≤ M)⟩⟩

theorem hj3_pd_eq_zero_of_far {R : ℝ} {ψ : ℝ × ℝ → ℝ}
    (hR : ∀ x : ℝ × ℝ, R < |x.2| → ψ x = 0) (j : Fin 2) (x : ℝ × ℝ) (hx : R < |x.2|) :
    UnforcedLeray.B0579.pd j ψ x = 0 := by
  unfold UnforcedLeray.B0579.pd
  have hopen : IsOpen {y : ℝ × ℝ | R < |y.2|} :=
    isOpen_lt continuous_const (continuous_abs.comp continuous_snd)
  have hev : ψ =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact hR y hy
  rw [hev.fderiv_eq]
  simp

theorem hj3_pd_continuous {c : ℝ} {ψ : ℝ × ℝ → ℝ} (hψ : UnforcedLeray.B0579.IsCylTest c ψ)
    (j : Fin 2) : Continuous (fun x => UnforcedLeray.B0579.pd j ψ x) := by
  unfold UnforcedLeray.B0579.pd
  have hD : Continuous fun x => fderiv ℝ ψ x := hψ.smooth.continuous_fderiv (by simp)
  exact hD.clm_apply continuous_const

/-- Integrability of the indicator of a band times a coordinate of `b` times a continuous
cylinder factor, with respect to `measureH c`. -/
theorem hj3_integrable_band {c : ℝ}
    {β : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC}
    (hβ : MemLp β 2 (UnforcedLeray.B0220.measureH c))
    {a b R : ℝ} (ha : 0 < a) {φ : ℝ × ℝ → ℝ} (hφ : Continuous φ) (j : Fin 2) :
    Integrable ((Icc a b ×ˢ (Icc 0 c ×ˢ Icc (-R) R)).indicator
        (fun p : UnforcedLeray.B0220.Profile => ((φ p.2 : ℝ) : ℂ) *
          (EuclideanSpace.proj j : UnforcedLeray.B0223.MeridC →L[ℂ] ℂ) (β p)))
      (UnforcedLeray.B0220.measureH c) := by
  have hEm : MeasurableSet (Icc a b ×ˢ (Icc 0 c ×ˢ Icc (-R) R)) :=
    measurableSet_Icc.prod (measurableSet_Icc.prod measurableSet_Icc)
  have hE : UnforcedLeray.B0220.measureH c (Icc a b ×ˢ (Icc 0 c ×ˢ Icc (-R) R)) ≠ ⊤ :=
    UnforcedLeray.B0226.measureH_band_ne_top c ha b R
  have hcomp : MemLp (fun p => (EuclideanSpace.proj j : UnforcedLeray.B0223.MeridC →L[ℂ] ℂ)
      (β p)) 2 (UnforcedLeray.B0220.measureH c) :=
    hβ.continuousLinearMap_comp _
  haveI : IsFiniteMeasure
      ((UnforcedLeray.B0220.measureH c).restrict (Icc a b ×ˢ (Icc 0 c ×ˢ Icc (-R) R))) :=
    isFiniteMeasure_restrict.2 hE
  have hL1 : Integrable (fun p => (EuclideanSpace.proj j : UnforcedLeray.B0223.MeridC →L[ℂ] ℂ)
      (β p))
      ((UnforcedLeray.B0220.measureH c).restrict (Icc a b ×ˢ (Icc 0 c ×ˢ Icc (-R) R))) :=
    MemLp.integrable (by norm_num) (hcomp.restrict _)
  have hK : IsCompact (Icc 0 c ×ˢ Icc (-R) R) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
      (f := fun x : ℝ × ℝ => ((φ x : ℝ) : ℂ)) (Complex.continuous_ofReal.comp hφ).continuousOn
  have hbd : ∀ᵐ p ∂((UnforcedLeray.B0220.measureH c).restrict
      (Icc a b ×ˢ (Icc 0 c ×ˢ Icc (-R) R))), ‖((φ p.2 : ℝ) : ℂ)‖ ≤ C := by
    filter_upwards [ae_restrict_mem hEm] with p hp
    exact hC p.2 hp.2
  have hmeas : AEStronglyMeasurable (fun p : UnforcedLeray.B0220.Profile => ((φ p.2 : ℝ) : ℂ))
      ((UnforcedLeray.B0220.measureH c).restrict (Icc a b ×ˢ (Icc 0 c ×ˢ Icc (-R) R))) :=
    (Complex.continuous_ofReal.comp (hφ.comp continuous_snd)).aestronglyMeasurable
  have hmul := hL1.bdd_mul hmeas hbd
  exact (integrable_indicator_iff hEm).2 hmul

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
