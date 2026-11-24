import UnforcedLeray.Short.PartIIIa.Sub.T21_c2_2

/-!
# Part III-a, task `PartIII-a:T21/c2/2/2`: `FmrTransfer`

Source of record: `the November 2 reference manuscript` lines 2937-2958.
Pure measure theory: `movFlowEnergy` depends on `ω σ` only through its a.e. class on the cell
(`integral_congr_ae`), and the regularity conclusion `FmeRegConc` transfers from the regular flow
`ω'` to the weak flow `ω` on `[t, s]` through the a.e. agreement on `Icc t T`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Short.IIb

namespace UnforcedLeray.Short.IIIa

theorem fmrTransfer : FmrTransfer := by
  intro ν m ε b t s T f ω ω' hts hsT hω't hae hreg
  unfold FmeRegConc at hreg
  unfold FmeConc FmeRegConc
  obtain ⟨hint', hcont', E', hE'⟩ := hreg
  have hsub : ∀ σ ∈ Icc t s, σ ∈ Icc t T := fun σ hσ => ⟨hσ.1, hσ.2.trans hsT⟩
  have key : ∀ σ ∈ Icc t T,
      (fun x : ℝ × ℝ => ω' σ x ^ 2 * (1 + (x.1 ^ 2 + x.2 ^ 2) / clockA ν σ) ^ m) =ᵐ[volume.restrict
          (B0579.cell (ν ^ (-2 : ℝ)))]
        (fun x : ℝ × ℝ => ω σ x ^ 2 * (1 + (x.1 ^ 2 + x.2 ^ 2) / clockA ν σ) ^ m) := by
    intro σ hσ
    filter_upwards [hae σ hσ] with x hx
    simp only [hx]
  have hI : ∀ σ ∈ Icc t T,
      ∫ x in B0579.cell (ν ^ (-2 : ℝ)), ω' σ x ^ 2 * (1 + (x.1 ^ 2 + x.2 ^ 2) / clockA ν σ) ^ m =
        ∫ x in B0579.cell (ν ^ (-2 : ℝ)), ω σ x ^ 2 * (1 + (x.1 ^ 2 + x.2 ^ 2) / clockA ν σ) ^ m :=
    fun σ hσ => integral_congr_ae (key σ hσ)
  have hME : ∀ σ ∈ Icc t T, movFlowEnergy ν (ν ^ (-2 : ℝ)) m ω' σ =
      movFlowEnergy ν (ν ^ (-2 : ℝ)) m ω σ := by
    intro σ hσ
    unfold movFlowEnergy movEnergy
    rw [hI σ hσ]
  have hint : ∀ σ ∈ Icc t s, IntegrableOn
      (fun x : ℝ × ℝ => ω σ x ^ 2 * (1 + (x.1 ^ 2 + x.2 ^ 2) / clockA ν σ) ^ m)
      (B0579.cell (ν ^ (-2 : ℝ))) := by
    intro σ hσ
    exact (hint' σ hσ).congr_fun_ae (key σ (hsub σ hσ))
  have hcont : ContinuousOn (movFlowEnergy ν (ν ^ (-2 : ℝ)) m ω) (Icc t s) :=
    hcont'.congr (fun σ hσ => (hME σ (hsub σ hσ)).symm)
  refine ⟨?_, hint, hcont, E', fun τ hτ => ?_⟩
  · have h0 := hint' t ⟨le_rfl, hts⟩
    rw [hω't] at h0
    exact h0
  · obtain ⟨hd, hb⟩ := hE' τ hτ
    have hτT : τ ∈ Icc t T := ⟨hτ.1, by linarith [hτ.2]⟩
    have hτs : τ < s := hτ.2
    have hev : movFlowEnergy ν (ν ^ (-2 : ℝ)) m ω =ᶠ[𝓝[Ici τ] τ]
        movFlowEnergy ν (ν ^ (-2 : ℝ)) m ω' := by
      filter_upwards [Icc_mem_nhdsGE hτs] with σ hσ
      exact (hME σ (⟨le_trans hτ.1 hσ.1, hσ.2.trans hsT⟩)).symm
    have hd' := hd.congr_of_eventuallyEq hev (hME τ hτT).symm
    refine ⟨hd', ?_⟩
    rw [hME τ hτT] at hb
    exact hb

end UnforcedLeray.Short.IIIa
