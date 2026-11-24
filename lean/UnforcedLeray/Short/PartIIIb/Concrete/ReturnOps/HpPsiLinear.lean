import UnforcedLeray.Short.PartIIIb.Concrete.ReturnOps.Targets

/-!
# `C/ret/9`: linearity of `h^p_A` and `ψ^p_A` in `A`

Source 4973-4975 (`h^p_A`, `ψ^p_A` are built from `A^y_mer` pointwise, through `merApply`,
`merTrace` and the derivatives of the fixed Gaussians `V_j`, `ψ_j`) and 4985.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem hpPsiLinear : HpPsiLinear := by
  intro ν χ A A' r s x hS1 hS2 hS3 hS4
  have hAyAdd : Ay ν χ (A + A') s = Ay ν χ A s + Ay ν χ A' s := by
    simp only [Ay, Pi.add_apply, smul_add]
  have hAyR : Ay ν χ (r • A) s = r • Ay ν χ A s := by
    simp only [Ay, Pi.smul_apply]
    exact smul_comm _ _ _
  have hmerAdd : ∀ (M M' : Mat3) (y : ℝ × ℝ),
      merApply (M + M') y = merApply M y + merApply M' y := by
    intro M M' y
    refine Prod.ext ?_ ?_ <;> simp only [merApply, Pi.add_apply, Prod.fst_add, Prod.snd_add] <;> ring
  have hmerSmul : ∀ (c : ℝ) (M : Mat3) (y : ℝ × ℝ),
      merApply (c • M) y = c • merApply M y := by
    intro c M y
    refine Prod.ext ?_ ?_ <;>
      simp only [merApply, Pi.smul_apply, smul_eq_mul, Prod.smul_fst, Prod.smul_snd] <;> ring
  have hTrAdd : ∀ M M' : Mat3, merTrace (M + M') = merTrace M + merTrace M' := by
    intro M M'
    simp only [merTrace, Pi.add_apply]
    ring
  have hTrSmul : ∀ (c : ℝ) (M : Mat3), merTrace (c • M) = c * merTrace M := by
    intro c M
    simp only [merTrace, Pi.smul_apply, smul_eq_mul]
    ring
  -- `h^p` terms
  have hHT : ∀ j : ℤ, hpATerm ν χ (A + A') s x j = hpATerm ν χ A s x j + hpATerm ν χ A' s x j := by
    intro j
    unfold hpATerm
    rw [hAyAdd]
    simp only [hmerAdd, map_add]
    abel
  have hHTs : ∀ j : ℤ, hpATerm ν χ (r • A) s x j = r • hpATerm ν χ A s x j := by
    intro j
    unfold hpATerm
    rw [hAyR]
    simp only [hmerSmul, map_smul]
    module
  -- `ψ^p` terms
  have hPT : ∀ j : ℤ, psipATerm ν χ (A + A') s x j
      = psipATerm ν χ A s x j + psipATerm ν χ A' s x j := by
    intro j
    unfold psipATerm
    rw [hAyAdd]
    simp only [hTrAdd, hmerAdd, map_add]
    ring
  have hPTs : ∀ j : ℤ, psipATerm ν χ (r • A) s x j = r • psipATerm ν χ A s x j := by
    intro j
    unfold psipATerm
    rw [hAyR]
    simp only [hTrSmul, hmerSmul, map_smul, smul_eq_mul]
    ring
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · simp only [hpA_eq]
    rw [tsum_congr hHT, Summable.tsum_add hS1 hS2]
  · simp only [hpA_eq]
    rw [tsum_congr hHTs, tsum_const_smul'']
  · simp only [psipA_eq]
    rw [tsum_congr hPT, Summable.tsum_add hS3 hS4]
  · simp only [psipA_eq]
    rw [tsum_congr hPTs, tsum_const_smul'']

end UnforcedLeray.Short.PartIIIb.Concrete
