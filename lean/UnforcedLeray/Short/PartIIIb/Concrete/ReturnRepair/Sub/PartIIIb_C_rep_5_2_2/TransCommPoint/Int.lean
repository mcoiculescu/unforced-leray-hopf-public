import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_2_2_11
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Int.Cont

/-!
# `PartIII-b:C/rep/5/2/2/11/2` : `TCInt`, integrability along the half line

Source `the November 2 reference manuscript`
4176-4214, 4181-4192 ("the separated-kernel estimates prove convergence of this primitive and its
differentiated versions").

Route (all in `Int/`): Hölder in `z` against the gap kernel (`Int/Dil.lean`), the periodic
dilation sum for an arbitrary period (`Int/Phase.lean`), so that at every phase and every receiver
`|D^jW_m|, |D^jX₀| ≤ C (ϱ - r_o)^{-5/2-j}` (`Int/Bound.lean`, `Int/Deriv.lean`); the phase
derivative of `X₀` is expressed by the free equation `D_{μ+1}X₀ = W_μ` (`Int/Half.lean`), so that
all four integrands `ρ P_z(ρ,0,y₃)` are `≤ C(1+|y₃|)(ρ - r_o)^{-3/2}` (`Int/Half2.lean`).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem tcd_Wre_cd {ν μ rOut P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hr : 0 ≤ rOut) (hP : 0 < P)
    (hT : IIIa.IsSepSource P rOut T) (hM : SepMoment P T) (τ : ℝ) :
    ContDiffOn ℝ 2 (sepWre ν μ T τ) {y : Space | rOut < ϱ y} := by
  have hm1 : -(1 / 4) < ((μ : ℂ)).re := by simpa using hμ
  have hWa : ContDiffOn ℝ 2 (fun z => IIIa.sepW ν (μ : ℂ) T z τ) {y : Space | rOut < ϱ y} :=
    contDiffOn_pi.2 (fun i => sepWSmoothOn_of IIIa.sepKernelBounds ν (μ : ℂ) rOut P T hν
      hm1 hr hP hT hM τ i)
  have : sepWre ν μ T τ = fun z => reL (IIIa.sepW ν (μ : ℂ) T z τ) := rfl
  rw [this]
  exact reL.contDiff.comp_contDiffOn hWa

theorem tcd_X0_cdOn {ν μ rOut P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hr : 0 ≤ rOut) (hP : 0 < P)
    (hT : IIIa.IsSepSource P rOut T) (hM : SepMoment P T) (τ : ℝ) :
    ContDiffOn ℝ 2 (sepX0 ν μ T τ) {y : Space | rOut < ϱ y} := by
  have hU : IsOpen {y : Space | rOut < ϱ y} := isOpen_lt continuous_const continuous_ϱ
  intro y hy
  exact (tcd_X0_cd hν hμ hr hP hT hM τ hy).contDiffWithinAt

theorem tcd_comb_cont {S : Set ℝ} {g1 g2 g3 g4 : ℝ → Space} {ν c : ℝ}
    (h1 : ContinuousOn g1 S) (h2 : ContinuousOn g2 S) (h3 : ContinuousOn g3 S)
    (h4 : ContinuousOn g4 S) :
    ContinuousOn (fun ρ : ℝ => ρ * (g1 ρ + (1 / 2 : ℝ) • g2 ρ + ν • g3 ρ - c • g4 ρ) 2) S := by
  have : ContinuousOn (fun ρ => g1 ρ + (1 / 2 : ℝ) • g2 ρ + ν • g3 ρ - c • g4 ρ) S := by
    fun_prop
  have h5 : ContinuousOn (fun ρ => (g1 ρ + (1 / 2 : ℝ) • g2 ρ + ν • g3 ρ - c • g4 ρ) 2) S :=
    (EuclideanSpace.proj (2 : Fin 3)).continuous.comp_continuousOn this
  exact continuousOn_id.mul h5

/-- **`TCInt`** (source 4181-4192). -/
theorem tcInt : TCInt := by
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
