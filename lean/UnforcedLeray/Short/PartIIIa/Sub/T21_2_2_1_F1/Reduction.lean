import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2_1_F1.WtCore
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDualitySub

/-!
# Part III-a, `PartIII-a:T21/2/2/1/3/org`: continuity of `E_0`, `E_1` from the fields of the flow

Source of record: `the November 2 reference manuscript` (SP), lines 3036-3037, 3044,
3060-3071.

`IsAdjointFlow.strongContH1` says `φ ∈ C([t, s); H^1_{-m,c})`. With the fixed-cell form of `E_1`
(`adjF1_eq_coreF1`, `ChangeVar.lean`) and `wtCoreCont` (`WtCore.lean`) this gives `AdjF1Cont`
(`adjF1Cont_of`, `adjF1Cont_direct`). The same `wtCoreCont` with `strongCont` gives `AdjF0Core`
(`adjF0Core_of`, `adjF0Core_direct`), and the field gives `LadAdjGradInt` at once, since `‖∂_kφ(ρ)‖`
is then continuous on `[t, r]` (`ladAdjGradInt_direct`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

/-- The fixed-cell gradient energy is continuous on `[t, s)` for an adjoint flow. -/
theorem coreF1Cont_of (h : WtCoreCont) {ν c m : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c}
    {t s : ℝ} {g : ℝ × ℝ → ℂ} {φ : ℝ → ℝ × ℝ → ℂ} (hν : 0 < ν) (hc : 0 < c) (ht : 0 ≤ t)
    (hφ : IsAdjointFlow ν c m tr t s g φ) : ContinuousOn (coreF1 ν c m φ) (Ico t s) := by
  unfold coreF1
  refine continuousOn_finsetSum _ fun k _ => ?_
  exact h ν c m (Ico t s) (fun r => pdCx k (φ r)) hν hc (fun r hr => ht.trans hr.1)
    (fun r hr => hφ.memH1 r hr k) (fun r hr => hφ.strongContH1 r hr k)

/-- **`AdjF1Cont` from the continuity of the fixed-cell energy** (SP 3060-3071). -/
theorem adjF1Cont_of (h : WtCoreCont) : AdjF1Cont := by
  intro ν c m tr t s g φ hν hc ht _ hφ
  have hcore := coreF1Cont_of h hν hc ht hφ
  have hpos : ∀ r ∈ Ico t s, 0 < clockA ν r := by
    intro r hr
    unfold clockA
    have : 0 ≤ r := ht.trans hr.1
    positivity
  have hinv : ContinuousOn (fun r => (clockA ν r)⁻¹ ^ 2) (Ico t s) := by
    apply ContinuousOn.pow
    apply ContinuousOn.inv₀
    · unfold clockA; fun_prop
    · exact fun r hr => (hpos r hr).ne'
  refine (hinv.mul hcore).congr ?_
  intro r hr
  exact adjF1_eq_coreF1 hν hc (ht.trans hr.1) (hφ.smooth r hr)

/-- **`AdjF1Cont`** (SP 3060-3071). -/
theorem adjF1Cont_direct : AdjF1Cont := adjF1Cont_of wtCoreCont

/-- **`AdjF0Core` from the continuity of the fixed-cell energy** (SP 3060-3071). -/
theorem adjF0Core_of (h : WtCoreCont) : AdjF0Core := by
  intro ν c m tr t s g φ hν hc ht _ hφ
  exact h ν c m (Icc t s) φ hν hc (fun r hr => ht.trans hr.1) hφ.memX hφ.strongCont

/-- **`AdjF0Core`** (SP 3060-3071). -/
theorem adjF0Core_direct : AdjF0Core := adjF0Core_of wtCoreCont

/-- The `L²` norm is continuous along a strongly continuous path. -/
theorem tendsto_toReal_eLpNorm {μ : Measure (ℝ × ℝ)} {l : Filter ℝ} {f : ℝ → ℝ × ℝ → ℂ}
    {f₀ : ℝ × ℝ → ℂ} (hl : ∀ᶠ r in l, MemLp (f r) 2 μ) (h₀ : MemLp f₀ 2 μ)
    (h : Tendsto (fun r => eLpNorm (f r - f₀) 2 μ) l (𝓝 0)) :
    Tendsto (fun r => (eLpNorm (f r) 2 μ).toReal) l (𝓝 (eLpNorm f₀ 2 μ).toReal) := by
  have hn : Tendsto (fun r => (eLpNorm (f r - f₀) 2 μ).toReal) l (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    simpa [Function.comp_def] using this
  refine tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero' ?_ ?_ hn)
  · exact Eventually.of_forall fun _ => norm_nonneg _
  · filter_upwards [hl] with r hr
    have hs : MemLp (f r - f₀) 2 μ := hr.sub h₀
    have e1 : f r = (f r - f₀) + f₀ := by simp
    have e2 : f₀ = f r - (f r - f₀) := by simp
    have h1 : eLpNorm (f r) 2 μ ≤ eLpNorm (f r - f₀) 2 μ + eLpNorm f₀ 2 μ := by
      conv_lhs => rw [e1]
      exact eLpNorm_add_le hs.aestronglyMeasurable h₀.aestronglyMeasurable (by norm_num)
    have h2 : eLpNorm f₀ 2 μ ≤ eLpNorm (f r) 2 μ + eLpNorm (f r - f₀) 2 μ := by
      conv_lhs => rw [e2]
      exact eLpNorm_sub_le hr.aestronglyMeasurable hs.aestronglyMeasurable (by norm_num)
    have ta := hr.2.ne
    have tb := hs.2.ne
    have tc := h₀.2.ne
    have h1' := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨tb, tc⟩) h1
    have h2' := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨ta, tb⟩) h2
    rw [ENNReal.toReal_add tb tc] at h1'
    rw [ENNReal.toReal_add ta tb] at h2'
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith

/-- **`LadAdjGradInt`** (SP 3060-3071): `‖∂_kφ(ρ)‖_{X_{-m,c}}` is continuous on `[t, r]`, `r < s`, by
`IsAdjointFlow.strongContH1`, hence integrable. -/
theorem ladAdjGradInt_direct (m : ℝ) : LadAdjGradInt m := by
  intro ν c tr t s g φ _ _ _ _ _ hφ r hr k
  have hsub : Icc t r ⊆ Ico t s := fun ρ hρ => ⟨hρ.1, lt_of_le_of_lt hρ.2 hr.2⟩
  have hcont : ContinuousOn
      (fun ρ => (eLpNorm (pdCx k (φ ρ)) 2 (B0579.cellMeasure c (-m))).toReal) (Icc t r) := by
    intro ρ hρ
    have h1 : Tendsto (fun r' => (eLpNorm (pdCx k (φ r')) 2 (B0579.cellMeasure c (-m))).toReal)
        (𝓝[Ico t s] ρ) (𝓝 (eLpNorm (pdCx k (φ ρ)) 2 (B0579.cellMeasure c (-m))).toReal) :=
      tendsto_toReal_eLpNorm
        (by filter_upwards [self_mem_nhdsWithin] with r' hr' using hφ.memH1 r' hr' k)
        (hφ.memH1 ρ (hsub hρ) k) (hφ.strongContH1 ρ (hsub hρ) k)
    exact h1.mono_left (nhdsWithin_mono _ hsub)
  exact hcont.intervalIntegrable_of_Icc hr.1

end UnforcedLeray.Short.IIIa
