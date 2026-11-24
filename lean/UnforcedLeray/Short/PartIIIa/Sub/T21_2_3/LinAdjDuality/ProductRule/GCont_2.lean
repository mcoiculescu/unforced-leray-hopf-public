import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_3_1_5
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.PairCont

/-!
# `L²`-continuity in `σ` of the cut-off flow and of the velocity (SP 3074-3075)

On the strip `|η| ≤ L` of the cell, the weight `⟨x⟩^{m}` is bounded above and below, so the
`L²(C_c)` norm of a strip-cut function is controlled by its `X_{m,c}` norm (`strip_le`). The
strong continuity of `w` in `X_{m,c}` (`IsLinearisedFlow.strongCont`) then gives the first
claim, and the Lipschitz hypothesis of `LadPRSetup` gives the second.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace GCont2Aux

/-- A positive lower bound of `⟨x⟩^{m/2}` on the box. -/
lemma exists_jb_lower (c L m : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ x ∈ B0579.box c L, κ ≤ B0579.jb x ^ (m / 2) := by
  rcases (B0579.box c L).eq_empty_or_nonempty with he | hne
  · exact ⟨1, one_pos, fun x hx => by simp [he] at hx⟩
  · obtain ⟨x0, hx0, hmin⟩ := (B0579.isCompact_box c L).exists_isMinOn hne
      ((B0579.continuous_jb_rpow (m / 2)).continuousOn)
    exact ⟨B0579.jb x0 ^ (m / 2), Real.rpow_pos_of_pos (B0579.jb_pos x0) _,
      fun x hx => isMinOn_iff.1 hmin x hx⟩

/-- Strip-cut `L²` norm bounded by the weighted norm. -/
lemma strip_le {c m L κ : ℝ} (hκ : 0 < κ) (hκle : ∀ x ∈ B0579.box c L, κ ≤ B0579.jb x ^ (m / 2))
    (g : ℝ × ℝ → ℂ) :
    eLpNorm (fun x => g x * (if |x.2| ≤ L then (1 : ℂ) else 0)) 2
        (volume.restrict (B0579.cell c)) ≤
      ENNReal.ofReal κ⁻¹ * Short.IIIa.xNorm c m g := by
  rw [Short.IIIa.xNorm, PairContAux.eLpNorm_cellMeasure_cx]
  have hG : ∀ x : ℝ × ℝ, ‖((B0579.jb x ^ (m / 2) : ℝ) : ℂ) * g x‖ =
      B0579.jb x ^ (m / 2) * ‖g x‖ := by
    intro x
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg
      (Real.rpow_nonneg (B0579.jb_pos x).le _)]
  calc eLpNorm (fun x => g x * (if |x.2| ≤ L then (1 : ℂ) else 0)) 2
        (volume.restrict (B0579.cell c))
      ≤ eLpNorm (fun x => κ⁻¹ • (((B0579.jb x ^ (m / 2) : ℝ) : ℂ) * g x)) 2
          (volume.restrict (B0579.cell c)) := by
        refine eLpNorm_mono_ae ?_
        filter_upwards [ae_restrict_mem (B0579.measurableSet_cell c)] with x hx
        by_cases hL : |x.2| ≤ L
        · have hk := hκle x (B0579.mem_box_of_mem_cell hx hL)
          rw [if_pos hL, mul_one, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hκ.le), hG]
          have h1 : 1 ≤ κ⁻¹ * B0579.jb x ^ (m / 2) := by
            rw [inv_mul_eq_div, le_div_iff₀ hκ]
            linarith
          have hpos : 0 ≤ ‖g x‖ := norm_nonneg _
          calc ‖g x‖ = 1 * ‖g x‖ := (one_mul _).symm
            _ ≤ κ⁻¹ * B0579.jb x ^ (m / 2) * ‖g x‖ := mul_le_mul_of_nonneg_right h1 hpos
            _ = κ⁻¹ * (B0579.jb x ^ (m / 2) * ‖g x‖) := by ring
        · rw [if_neg hL, mul_zero, norm_zero]
          positivity
    _ = ENNReal.ofReal κ⁻¹ * eLpNorm (fun x => ((B0579.jb x ^ (m / 2) : ℝ) : ℂ) * g x) 2
          (volume.restrict (B0579.cell c)) := by
        have h := eLpNorm_const_smul (κ⁻¹ : ℝ)
          (fun x : ℝ × ℝ => ((B0579.jb x ^ (m / 2) : ℝ) : ℂ) * g x) 2
          (volume.restrict (B0579.cell c))
        rw [Real.enorm_of_nonneg (inv_nonneg.2 hκ.le)] at h
        exact h

end GCont2Aux

open GCont2Aux in
theorem ladPR_w_u_L2_cont {ν c m : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c} {t s : ℝ} {f : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ} {φ : ℝ → ℝ × ℝ → ℂ} (h : LadPRSetup ν c m tr t s f w u φ) (L : ℝ) (ρ0 : ℝ) (hρ0 : t ≤ ρ0) : Filter.Tendsto (fun ρ => MeasureTheory.eLpNorm (fun x => w ρ x * (if |x.2| ≤ L then 1 else 0) - w ρ0 x * (if |x.2| ≤ L then 1 else 0)) 2 (MeasureTheory.volume.restrict (B0579.cell c))) (nhdsWithin ρ0 (Set.Ici t)) (nhds 0) ∧ ∀ j : Fin 2, Filter.Tendsto (fun ρ => MeasureTheory.eLpNorm (fun x => u ρ x j - u ρ0 x j) 2 (MeasureTheory.volume.restrict (B0579.cell c))) (nhdsWithin ρ0 (Set.Ici t)) (nhds 0) := by
  obtain ⟨κ, hκ, hκle⟩ := exists_jb_lower c L m
  have hstrong : Tendsto (fun ρ => Short.IIIa.xNorm c m (w ρ - w ρ0)) (𝓝[Ici t] ρ0) (𝓝 0) :=
    h.flow.strongCont ρ0 hρ0
  constructor
  · have hlim : Tendsto (fun ρ => ENNReal.ofReal κ⁻¹ * Short.IIIa.xNorm c m (w ρ - w ρ0))
        (𝓝[Ici t] ρ0) (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul hstrong
        (Or.inr (ENNReal.ofReal_ne_top : ENNReal.ofReal κ⁻¹ ≠ ⊤))
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun ρ => zero_le) (Eventually.of_forall fun ρ => ?_)
    have e : (fun x => w ρ x * (if |x.2| ≤ L then (1 : ℂ) else 0) -
        w ρ0 x * (if |x.2| ≤ L then (1 : ℂ) else 0)) =
        fun x => (w ρ - w ρ0) x * (if |x.2| ≤ L then (1 : ℂ) else 0) := by
      funext x
      simp only [Pi.sub_apply, sub_mul]
    rw [e]
    exact strip_le hκ hκle (w ρ - w ρ0)
  · intro j
    obtain ⟨C, hC⟩ := h.lip
    have hlim : Tendsto (fun ρ => ENNReal.ofReal C * Short.IIIa.xNorm c m (w ρ - w ρ0))
        (𝓝[Ici t] ρ0) (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul hstrong
        (Or.inr (ENNReal.ofReal_ne_top : ENNReal.ofReal C ≠ ⊤))
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun ρ => zero_le) ?_
    filter_upwards [self_mem_nhdsWithin] with ρ hρ
    exact hC ρ ρ0 (Set.mem_Ici.1 hρ) hρ0 j

end UnforcedLeray.Short.IIIa
