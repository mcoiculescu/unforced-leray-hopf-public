import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Int
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_3_Comb.S2

/-!
# `∂_τ` commutes with the outward primitive of `X₀ = sepX0`

Source `the November 2 reference manuscript` 4176-4214, 4181-4192 (the primitive
`Ψ_Z(r,z) = -∫_r^∞ ρ Z_z(ρ,0,z) dρ` is differentiated under the integral).  The majorant
`C(1+|z|)(ρ - r_o)^{-3/2}` of `ρ ∂_τX₀_z` is uniform in the phase (`Int/Half2.lean`).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem tcr_sepData {ν μ rOut P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hr : 0 ≤ rOut) (hP : 0 < P)
    (hT : IIIa.IsSepSource P rOut T) (hM : SepMoment P T) : SepData ν μ rOut P T :=
  ⟨hν, hμ, hr, hP, hT, hM⟩

/-- Pointwise differentiability in the phase. -/
theorem tcr_hasDerivAt_tau {ν μ rOut P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hr : 0 ≤ rOut) (hP : 0 < P)
    (hT : IIIa.IsSepSource P rOut T) (hM : SepMoment P T) (τ : ℝ) {y : Space}
    (hy : rOut < ϱ y) :
    HasDerivAt (fun t => sepX0 ν μ T t y) (deriv (fun t => sepX0 ν μ T t y) τ) τ := by
  have h := sepX0TauDeriv ν μ rOut P T (tcr_sepData hν hμ hr hP hT hM) τ y hy
  exact h.differentiableAt.hasDerivAt

theorem tcr_cont_tau {ν μ rOut P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hr : 0 ≤ rOut) (hP : 0 < P)
    (hT : IIIa.IsSepSource P rOut T) (hM : SepMoment P T) (τ z : ℝ) :
    ContinuousOn (fun ρ : ℝ => ρ * (deriv (fun s => sepX0 ν μ T s (!₂[ρ, 0, z] : Space)) τ) 2)
      (Ioi rOut) := by
  have hcd := tcd_X0_cdOn hν hμ hr hP hT hM τ
  have hW := tcd_Wre_cd hν hμ hr hP hT hM τ
  have hc2 : ContinuousOn (fun ρ : ℝ => fderiv ℝ (sepX0 ν μ T τ) (!₂[ρ, 0, z] : Space)
      (!₂[ρ, 0, z] : Space)) (Ioi rOut) :=
    (tcd_cont_fderiv hr hcd z).clm_apply (tcd_pt_cont z).continuousOn
  have hall := tcd_comb_cont (S := Ioi rOut) (ν := ν) (c := (μ + 1) - 1 / 2)
    (tcd_cont_val hr hW z) hc2 (tcd_cont_lap hr hcd z) (tcd_cont_val hr hcd z)
  refine hall.congr ?_
  intro ρ hρ
  have hρr : rOut < ϱ (!₂[ρ, 0, z] : Space) := by
    rw [tcd_varrho (hr.trans (le_of_lt hρ))]
    exact hρ
  simp only
  rw [tcd_freeEq hν hμ hr hP hT hM τ hρr]

/-- **The outward primitive of `X₀` is differentiable in the phase, with derivative the primitive
of `∂_τX₀`.** -/
theorem tcr_outPrim_tau {ν μ rOut P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hr : 0 ≤ rOut) (hP : 0 < P)
    (hT : IIIa.IsSepSource P rOut T) (hM : SepMoment P T) (τ : ℝ) {y : Space}
    (hy : rOut < ϱ y) :
    HasDerivAt (fun t => outPrim (sepX0 ν μ T) t (ϱ y) (y 2))
      (outPrim (fun t y' => deriv (fun s => sepX0 ν μ T s y') t) τ (ϱ y) (y 2)) τ := by
  obtain ⟨Cb, hCb, hb⟩ := tcd_half hν hμ hr hP hT hM hy
  have hint : Integrable (fun ρ : ℝ => Cb * (1 + |y 2|) * (ρ - rOut) ^ (-(3 / 2 : ℝ)))
      (volume.restrict (Ioi (ϱ y))) := (tcd_int_shift rOut (ϱ y) (by linarith)).const_mul _
  have hsub : Ioi (ϱ y) ⊆ Ioi rOut := Ioi_subset_Ioi hy.le
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
  have hmeas : ∀ t : ℝ, AEStronglyMeasurable
      (fun ρ : ℝ => ρ * sepX0 ν μ T t (!₂[ρ, 0, y 2] : Space) 2) (volume.restrict (Ioi (ϱ y))) :=
    fun t => (proj _ ((tcd_cont_val hr (tcd_X0_cdOn hν hμ hr hP hT hM t) (y 2)).mono hsub)
      ).aestronglyMeasurable measurableSet_Ioi
  have h0 := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (ϱ y)))
    (F := fun t ρ => ρ * sepX0 ν μ T t (!₂[ρ, 0, y 2] : Space) 2)
    (F' := fun t ρ => ρ * (deriv (fun s => sepX0 ν μ T s (!₂[ρ, 0, y 2] : Space)) t) 2)
    (x₀ := τ) (bound := fun ρ : ℝ => Cb * (1 + |y 2|) * (ρ - rOut) ^ (-(3 / 2 : ℝ)))
    (s := Set.univ) Filter.univ_mem (Eventually.of_forall hmeas)
    (by
      refine Integrable.mono' hint (hmeas τ) ?_
      refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun ρ hρ => ?_)
      have := (hb τ ρ (y 2) (le_of_lt hρ)).1
      rw [Real.norm_eq_abs]
      exact this.trans (hCb' ρ hρ))
    (((tcr_cont_tau hν hμ hr hP hT hM τ (y 2)).mono hsub).aestronglyMeasurable
      measurableSet_Ioi)
    (by
      refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun ρ hρ t _ => ?_)
      have := (hb t ρ (y 2) (le_of_lt hρ)).2.2.2.2.2
      rw [Real.norm_eq_abs]
      exact this)
    hint
    (by
      refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun ρ hρ t _ => ?_)
      have hρr : rOut < ϱ (!₂[ρ, 0, y 2] : Space) := by
        rw [tcd_varrho (hr.trans (hsub hρ).le)]
        exact hsub hρ
      have hd := tcr_hasDerivAt_tau hν hμ hr hP hT hM t hρr
      have hc : HasDerivAt (fun s => sepX0 ν μ T s (!₂[ρ, 0, y 2] : Space) 2)
          ((deriv (fun s => sepX0 ν μ T s (!₂[ρ, 0, y 2] : Space)) t) 2) t :=
        (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hd
      exact hc.const_mul ρ)
  have h1 := h0.2.neg
  unfold outPrim
  exact h1

end UnforcedLeray.Short.PartIIIb.Concrete

end
