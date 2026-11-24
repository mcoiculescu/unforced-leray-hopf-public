import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5_5
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5.FcvGInt
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5_4.Unif

/-!
# Proof of `FcvTriBound` (source 4610)

`‖ℓ_ρ(𝒰(ρ,t) g_B(t))‖ ≤ |C_E| (C_U C_g)` for `0 < t < ρ ≤ s`: the uniform bound
`‖ℓ_ρ ω‖ ≤ C_E ‖ω‖` for `0 < ρ ≤ s` (`fcvEllUnif`), the operator bound `‖𝒰(ρ,t)‖ ≤ C_U`
(`locBdd`), and `‖g_B(t)‖ ≤ C_g` on `(0,s]` (`gBD_norm_le`, entrywise bound of `B` as in `FcvGInt`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem fcvTriBound : FcvTriBound := by
  intro κ ν c m _ _ tr D μ as χf A hν hμ hχ hA φ hφ s hs
  set K0 : ℝ := (1 + μ) * ((11 / 10) / ν) ^ (3 / 2 : ℝ) * |affM ν χf A| with hK0def
  have hK00 : 0 ≤ K0 := by
    rw [hK0def]
    have h1 : 0 ≤ (11 / 10 / ν : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
    have h2 : 0 ≤ 1 + μ := by linarith
    positivity
  have hBent : ∀ t, 0 < t → t ≤ s → ∀ i j, |Bmat ν μ χf A t i j| ≤ K0 := by
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
  obtain ⟨C, hC⟩ := gBD_norm_le D (Bmat ν μ χf A) s K0 hK00 hBent
  obtain ⟨CU, hCU⟩ := D.ev.locBdd s
  obtain ⟨CE, hCE⟩ := (fcvEllUnif : FcvEllUnif) ν c m tr φ hφ s
  refine ⟨|CE| * (CU * C), fun t ρ ht htρ hρs => ?_⟩
  have hρ0 : 0 < ρ := ht.trans htρ
  have hts : t ≤ s := htρ.le.trans hρs
  have hUb : ‖D.ev.U ρ t‖ ≤ CU := hCU ρ t ht.le htρ.le hρs
  have hCU0 : 0 ≤ CU := (norm_nonneg (D.ev.U ρ t)).trans hUb
  have hgb : ‖gBD D (Bmat ν μ χf A) t‖ ≤ C := hC t ht hts
  have hx : ‖D.ev.U ρ t (gBD D (Bmat ν μ χf A) t)‖ ≤ CU * C :=
    ((D.ev.U ρ t).le_opNorm _).trans (mul_le_mul hUb hgb (norm_nonneg _) hCU0)
  calc ‖ellFn tr φ ρ (D.ev.U ρ t (gBD D (Bmat ν μ χf A) t))‖
      ≤ CE * ‖D.ev.U ρ t (gBD D (Bmat ν μ χf A) t)‖ :=
        hCE ρ hρ0 hρs _
    _ ≤ |CE| * ‖D.ev.U ρ t (gBD D (Bmat ν μ χf A) t)‖ :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
    _ ≤ |CE| * (CU * C) := mul_le_mul_of_nonneg_left hx (abs_nonneg _)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

#print axioms UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.fcvTriBound
