import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5.CellPairBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5.FcvGInt
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_3.FlatXiContinuous
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_9
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.FACoefBound.BmatBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_10

/-!
# Proof of `FcvMellin` (source 4610)

`s^μ ξ_B(s) = s^μ s^{-μ} ∫_{(0,s]} t^μ 𝒰(s,t)g_B(t) dt`, and the cell pairing `⟨·,φ⟩` is a
continuous linear functional on `X_{m,c}`, so it commutes with the Bochner integral
(`ContinuousLinearMap.integral_comp_comm`).  The integrand `t ↦ 𝒰(s,t)g_B(t)` is continuous on
`(0,s]` (`jointG_contOn`) and bounded there (`locBdd`, `gBD_norm_le`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- Entrywise bound of `Bmat ν μ χf A` on `(0,s]` (the cutoff vanishes past `11/(10ν)`). -/
theorem bmat_entry_bound_all {ν μ : ℝ} {χf : ℝ → ℝ} {as : ℝ} {A : ℝ → Mat3}
    (hν : 0 < ν) (hμ : 0 < μ) (hχ : IsSourceCutoffC χf) (hA : IsAffElem as A) (s : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t, 0 < t → t ≤ s → ∀ i j, |Bmat ν μ χf A t i j| ≤ K := by
  have h1 : 0 ≤ ((11 / 10) / ν : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
  have h2 : 0 ≤ 1 + μ := by linarith
  have hK00 : 0 ≤ (1 + μ) * ((11 / 10) / ν) ^ (3 / 2 : ℝ) * |affM ν χf A| :=
    mul_nonneg (mul_nonneg h2 h1) (abs_nonneg _)
  refine ⟨(1 + μ) * ((11 / 10) / ν) ^ (3 / 2 : ℝ) * |affM ν χf A|, hK00, ?_⟩
  intro t ht hts i j
  by_cases hle : t ≤ (11 / 10) / ν
  · have hbd := bmatBound as χf hχ ν μ hν hμ.le A hA t ht hle
    refine (abs_entry_le_frob _ i j).trans (hbd.trans ?_)
    have h3 : t ^ (3 / 2 : ℝ) ≤ ((11 / 10) / ν) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow ht.le hle (by norm_num)
    have hX0 : 0 ≤ (1 + μ) * t ^ (3 / 2 : ℝ) :=
      mul_nonneg h2 (Real.rpow_nonneg ht.le _)
    calc (1 + μ) * t ^ (3 / 2 : ℝ) * affM ν χf A
        ≤ (1 + μ) * t ^ (3 / 2 : ℝ) * |affM ν χf A| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) hX0
      _ ≤ (1 + μ) * ((11 / 10) / ν) ^ (3 / 2 : ℝ) * |affM ν χf A| := by
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
          exact mul_le_mul_of_nonneg_left h3 h2
  · rw [bmat_zero_of_large hχ hν (not_le.1 hle)]
    simp only [Pi.zero_apply, abs_zero]
    exact hK00

/-- The main identity of the Mellin form of `ξ_B`. -/
theorem fcvMellin : FcvMellin := by
  unfold FcvMellin
  intro κ ν c m hm hc tr D μ as χf A hν hμ hχ hA φ hφ s hs
  have hBc : ContinuousOn (Bmat ν μ χf A) (Ioi 0) := bmat_continuousOn hχ hA
  have hG : ContinuousOn (gBD D (Bmat ν μ χf A)) (Ioi 0) := gBD_contOn D _ hBc
  obtain ⟨K0, hK00, hBent⟩ := bmat_entry_bound_all hν hμ hχ hA s
  obtain ⟨Cg, hCg⟩ := gBD_norm_le D (Bmat ν μ χf A) s K0 hK00 hBent
  obtain ⟨CU, hCU⟩ := D.ev.locBdd s
  have hCU0 : 0 ≤ CU := (norm_nonneg (D.ev.U s s)).trans (hCU s s hs.le le_rfl le_rfl)
  -- pointwise bound of the integrand
  have hpt : ∀ t ∈ Ioc 0 s, ‖((t : ℂ) ^ (μ : ℂ)) •
      D.ev.U s t (gBD D (Bmat ν μ χf A) t)‖ ≤ s ^ μ * (CU * Cg) := by
    intro t ht
    have ht0 : 0 < t := ht.1
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.ofReal_re]
    have h1 : t ^ μ ≤ s ^ μ := Real.rpow_le_rpow ht0.le ht.2 hμ.le
    have h2 : ‖D.ev.U s t (gBD D (Bmat ν μ χf A) t)‖ ≤ CU * Cg :=
      ((D.ev.U s t).le_opNorm _).trans
        (mul_le_mul (hCU s t ht0.le ht.2 le_rfl) (hCg t ht0 ht.2) (norm_nonneg _) hCU0)
    exact mul_le_mul h1 h2 (norm_nonneg _) (Real.rpow_nonneg hs.le _)
  -- continuity of the integrand on `(0,s]`
  have hpow : ContinuousOn (fun t : ℝ => ((t : ℂ) ^ (μ : ℂ))) (Ioc 0 s) := by
    refine ContinuousOn.cpow_const ?_ ?_
    · exact Complex.continuous_ofReal.continuousOn
    · intro t ht
      exact Or.inl (by simpa using ht.1)
  have hU : ContinuousOn (fun t : ℝ => D.ev.U s t (gBD D (Bmat ν μ χf A) t)) (Ioc 0 s) := by
    have hj := jointG_contOn D.ev (gBD D (Bmat ν μ χf A)) hG
    have hcomp : ContinuousOn (fun t : ℝ => ((s, t) : ℝ × ℝ)) (Ioc 0 s) :=
      continuousOn_const.prodMk continuousOn_id
    have hmaps : MapsTo (fun t : ℝ => ((s, t) : ℝ × ℝ)) (Ioc 0 s)
        {p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ p.1} := fun t ht => ⟨ht.1, ht.2⟩
    exact hj.comp hcomp hmaps
  have hFc : ContinuousOn (fun t : ℝ => ((t : ℂ) ^ (μ : ℂ)) •
      D.ev.U s t (gBD D (Bmat ν μ χf A) t)) (Ioc 0 s) :=
    hpow.smul hU
  have hint : Integrable (fun t : ℝ => ((t : ℂ) ^ (μ : ℂ)) •
      D.ev.U s t (gBD D (Bmat ν μ χf A) t)) (volume.restrict (Ioc 0 s)) := by
    have hmeasR := hFc.aestronglyMeasurable (μ := volume) measurableSet_Ioc
    have hfin : (volume.restrict (Ioc 0 s)) univ ≠ ⊤ := by
      rw [Measure.restrict_apply_univ]
      exact measure_Ioc_lt_top.ne
    have hb' : ∀ᵐ t : ℝ ∂((volume.restrict (Ioc 0 s)).restrict univ),
        ‖((t : ℂ) ^ (μ : ℂ)) • D.ev.U s t (gBD D (Bmat ν μ χf A) t)‖ ≤ s ^ μ * (CU * Cg) := by
      rw [Measure.restrict_univ]
      exact ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => hpt t ht
    exact integrableOn_univ.1 (Measure.integrableOn_of_bounded hfin hmeasR hb')
  -- commute the pairing with the integral
  have key := (cellPairCLM hφ).integral_comp_comm hint
  simp only [cellPairCLM_apply] at key
  have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
  show ((s : ℂ) ^ (μ : ℂ)) * cellPair φ (((s : ℂ) ^ (-(μ : ℂ))) •
      ∫ t in Ioc 0 s, ((t : ℂ) ^ (μ : ℂ)) • D.ev.U s t (gBD D (Bmat ν μ χf A) t)) =
    ∫ t in Ioc 0 s, ((t : ℂ) ^ (μ : ℂ)) * cellPair φ (D.ev.U s t (gBD D (Bmat ν μ χf A) t))
  rw [cellPair_smul', ← key]
  simp only [cellPair_smul']
  rw [← mul_assoc, ← Complex.cpow_add _ _ hs0, add_neg_cancel, Complex.cpow_zero, one_mul]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
