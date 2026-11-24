import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5_5
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5.FcvGInt

/-!
# Proof of `FcvBochnerInt` (source 4610)

For `ρ > 0` the map `t ↦ t^μ 𝒰(ρ,t) g_B(t)` is continuous on `(0,ρ]` in `X_{m,c}`
(`jointCont` for the age variable at a fixed datum, `locBdd` for the operator norms, continuity of
`g_B` on `(0,∞)` by `gBD_continuousOn`), hence strongly measurable, and it is bounded by
`ρ^μ (C_U C_g)` on `(0,ρ]` (`locBdd`, `gBD_norm_le`).  A bounded strongly measurable function on a
set of finite measure is Bochner integrable.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- Continuity in the age of `t ↦ 𝒰(ρ,t) (g t)` on `(0,ρ]`: the datum moves continuously and the
operators `𝒰(ρ,t)` are uniformly bounded (`locBdd`), while `t ↦ 𝒰(ρ,t) x` is continuous
(`jointCont`). -/
theorem evU_continuousOn {ν c m : ℝ} [Fact (1 < m)] [Fact (0 < c)]
    {tr : UnforcedLeray.B0140.TrainSol ν c} (ev : TrainEvolution m tr) (ρ : ℝ)
    (g : ℝ → Xmc c m) (hg : ContinuousOn g (Ioc 0 ρ)) :
    ContinuousOn (fun t => ev.U ρ t (g t)) (Ioc 0 ρ) := by
  intro t0 ht0
  obtain ⟨C, hC⟩ := ev.locBdd ρ
  have hmaps : ∀ t ∈ Ioc 0 ρ, ((ρ, t) : ℝ × ℝ) ∈ {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ p.1} :=
    fun t ht => ⟨ht.1.le, ht.2⟩
  have hcont : ContinuousWithinAt (fun t : ℝ => (ρ, t)) (Ioc 0 ρ) t0 :=
    (continuous_const.prodMk continuous_id).continuousWithinAt
  have hx : ContinuousWithinAt (fun t => ev.U ρ t (g t0)) (Ioc 0 ρ) t0 :=
    (ev.jointCont (g t0) (ρ, t0) (hmaps t0 ht0)).comp hcont (fun t ht => hmaps t ht)
  have hgc : ContinuousWithinAt g (Ioc 0 ρ) t0 := hg t0 ht0
  have h1 : Tendsto (fun t => C * ‖g t - g t0‖) (𝓝[Ioc 0 ρ] t0) (𝓝 0) := by
    have := (tendsto_iff_norm_sub_tendsto_zero.1 hgc.tendsto).const_mul C
    simpa using this
  have h2 : Tendsto (fun t => ‖ev.U ρ t (g t0) - ev.U ρ t0 (g t0)‖) (𝓝[Ioc 0 ρ] t0) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 hx
  have h3 : Tendsto (fun t => C * ‖g t - g t0‖ + ‖ev.U ρ t (g t0) - ev.U ρ t0 (g t0)‖)
      (𝓝[Ioc 0 ρ] t0) (𝓝 0) := by
    simpa using h1.add h2
  rw [ContinuousWithinAt]
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ h3
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hUt : ‖ev.U ρ t‖ ≤ C := hC ρ t ht.1.le ht.2 le_rfl
  have e : ev.U ρ t (g t) - ev.U ρ t0 (g t0) =
      ev.U ρ t (g t - g t0) + (ev.U ρ t (g t0) - ev.U ρ t0 (g t0)) := by
    rw [map_sub]; abel
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
  refine ((ev.U ρ t).le_opNorm _).trans ?_
  exact mul_le_mul_of_nonneg_right hUt (norm_nonneg _)

theorem fcvBochnerInt : FcvBochnerInt := by
  intro κ ν c m _ _ tr D μ as χf A hν hμ hχ hA ρ hρ
  have hBc : ContinuousOn (Bmat ν μ χf A) (Ioi 0) := bmat_continuousOn hχ hA
  have hG : ContinuousOn (fun t => gBD D (Bmat ν μ χf A) t) (Ioi 0) :=
    gBD_continuousOn D hBc
  have hGI : ContinuousOn (fun t => gBD D (Bmat ν μ χf A) t) (Ioc 0 ρ) :=
    hG.mono Ioc_subset_Ioi_self
  have hF : ContinuousOn (fun t : ℝ => D.ev.U ρ t (gBD D (Bmat ν μ χf A) t)) (Ioc 0 ρ) :=
    evU_continuousOn D.ev ρ _ hGI
  have hp : ContinuousOn (fun t : ℝ => ((t : ℂ) ^ (μ : ℂ))) (Ioc 0 ρ) := by
    refine ContinuousOn.cpow_const Complex.continuous_ofReal.continuousOn ?_
    intro t ht
    exact Or.inl (by simpa using ht.1)
  have hPc : ContinuousOn (fun t : ℝ => ((t : ℂ) ^ (μ : ℂ)) •
      D.ev.U ρ t (gBD D (Bmat ν μ χf A) t)) (Ioc 0 ρ) := hp.smul hF
  have hmeas : AEStronglyMeasurable (fun t : ℝ => ((t : ℂ) ^ (μ : ℂ)) •
      D.ev.U ρ t (gBD D (Bmat ν μ χf A) t)) (volume.restrict (Ioc 0 ρ)) :=
    hPc.aestronglyMeasurable measurableSet_Ioc
  -- entrywise bound of `B` on `(0,ρ]`
  set K0 : ℝ := (1 + μ) * ((11 / 10) / ν) ^ (3 / 2 : ℝ) * |affM ν χf A| with hK0def
  have hK00 : 0 ≤ K0 := by
    rw [hK0def]
    have h1 : 0 ≤ (11 / 10 / ν : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
    have h2 : 0 ≤ 1 + μ := by linarith
    positivity
  have hBent : ∀ t, 0 < t → t ≤ ρ → ∀ i j, |Bmat ν μ χf A t i j| ≤ K0 := by
    intro t ht hts i j
    by_cases hle : t ≤ (11 / 10) / ν
    · have hbd := bmatBound as χf hχ ν μ hν hμ.le A hA t ht hle
      refine (abs_entry_le_frob _ i j).trans (hbd.trans ?_)
      have h1 : t ^ (3 / 2 : ℝ) ≤ ((11 / 10) / ν) ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow ht.le hle (by norm_num)
      have hX0 : 0 ≤ (1 + μ) * t ^ (3 / 2 : ℝ) := by
        have : 0 ≤ t ^ (3 / 2 : ℝ) := Real.rpow_nonneg ht.le _
        have : 0 ≤ 1 + μ := by linarith
        positivity
      calc (1 + μ) * t ^ (3 / 2 : ℝ) * affM ν χf A
          ≤ (1 + μ) * t ^ (3 / 2 : ℝ) * |affM ν χf A| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) hX0
        _ ≤ (1 + μ) * ((11 / 10) / ν) ^ (3 / 2 : ℝ) * |affM ν χf A| := by
            apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
            exact mul_le_mul_of_nonneg_left h1 (by linarith)
    · rw [bmat_zero_of_large hχ hν (not_le.1 hle)]
      simp only [Pi.zero_apply, abs_zero]
      exact hK00
  obtain ⟨C, hC⟩ := gBD_norm_le D (Bmat ν μ χf A) ρ K0 hK00 hBent
  obtain ⟨CU, hCU⟩ := D.ev.locBdd ρ
  have hfin : (volume.restrict (Ioc 0 ρ)) univ ≠ ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact measure_Ioc_lt_top.ne
  have hbound : ∀ᵐ t : ℝ ∂(volume.restrict (Ioc 0 ρ)),
      ‖((t : ℂ) ^ (μ : ℂ)) • D.ev.U ρ t (gBD D (Bmat ν μ χf A) t)‖ ≤ ρ ^ μ * (CU * C) := by
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
    have ht0 : 0 < t := ht.1
    have htρ : t ≤ ρ := ht.2
    have hUb : ‖D.ev.U ρ t‖ ≤ CU := hCU ρ t ht0.le htρ le_rfl
    have hgb : ‖gBD D (Bmat ν μ χf A) t‖ ≤ C := hC t ht0 htρ
    have hCU0 : 0 ≤ CU := (norm_nonneg (D.ev.U ρ t)).trans hUb
    have hx : ‖D.ev.U ρ t (gBD D (Bmat ν μ χf A) t)‖ ≤ CU * C :=
      ((D.ev.U ρ t).le_opNorm _).trans (mul_le_mul hUb hgb (norm_nonneg _) hCU0)
    have h1 : t ^ μ ≤ ρ ^ μ := Real.rpow_le_rpow ht0.le htρ hμ.le
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.ofReal_re]
    exact mul_le_mul h1 hx (norm_nonneg _) (Real.rpow_nonneg hρ.le _)
  have hbound' : ∀ᵐ t : ℝ ∂((volume.restrict (Ioc 0 ρ)).restrict univ),
      ‖((t : ℂ) ^ (μ : ℂ)) • D.ev.U ρ t (gBD D (Bmat ν μ χf A) t)‖ ≤ ρ ^ μ * (CU * C) := by
    rw [Measure.restrict_univ]
    exact hbound
  exact integrableOn_univ.1 (Measure.integrableOn_of_bounded hfin hmeas hbound')

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

#print axioms UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.fcvBochnerInt
