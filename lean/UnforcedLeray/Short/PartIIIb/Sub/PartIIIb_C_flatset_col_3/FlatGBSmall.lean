import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_3

/-!
# `flatGBSmall : FlatGBSmall` (decomposition of `PartIII-b:C/flatset/col/3`, leaf 3)

Source of record `the November 2 reference manuscript` lines 4605-4608, 4614.
`gBD D B s = a • H s + b • conjX (H s) - d • R s` (`gBD_apply`) with
`a = -(1/2)(Bd - i Be)`, `b = -(1/2)(Bd + i Be)`, `d = Bbeta`, all linear in the entries of `B s`.
`H, R` are continuous (`GaussSources.H_cont/R_cont`), hence bounded on `[0,1]`; `‖conjX x‖ = ‖x‖`
(`norm_conjX`).
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem flatGBSmall : FlatGBSmall := by
  intro κ ν c m _ _ tr D B C hB
  have hHc : Continuous (fun s => ‖D.src.H s‖) := D.src.H_cont.norm
  have hRc : Continuous (fun s => ‖D.src.R s‖) := D.src.R_cont.norm
  obtain ⟨KH, hKH⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hHc.continuousOn
  obtain ⟨KR, hKR⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hRc.continuousOn
  have hKH' : ∀ t ∈ Icc (0 : ℝ) 1, ‖D.src.H t‖ ≤ KH := fun t ht => by
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hKH t ht
  have hKR' : ∀ t ∈ Icc (0 : ℝ) 1, ‖D.src.R t‖ ≤ KR := fun t ht => by
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hKR t ht
  refine ⟨(2 * KH + KR) * C, ?_⟩
  intro s hs
  have hs0 : 0 < s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨hs0.le, hs1⟩
  have hb00 := abs_le.mp (hB s hs 0 0)
  have hb22 := abs_le.mp (hB s hs 2 2)
  have hb02 := abs_le.mp (hB s hs 0 2)
  have hb20 := abs_le.mp (hB s hs 2 0)
  have hBd : |Bd (B s)| ≤ C * s ^ (3 / 2 : ℝ) := by
    unfold Bd
    exact abs_le.mpr ⟨by linarith [hb00.1, hb22.2], by linarith [hb00.2, hb22.1]⟩
  have hBe : |Be (B s)| ≤ C * s ^ (3 / 2 : ℝ) := by
    unfold Be
    exact abs_le.mpr ⟨by linarith [hb02.1, hb20.2], by linarith [hb02.2, hb20.1]⟩
  have hBb : |ConcreteYF.Bbeta (B s)| ≤ C * s ^ (3 / 2 : ℝ) := by
    unfold ConcreteYF.Bbeta
    exact abs_le.mpr ⟨by linarith [hb00.1, hb22.1], by linarith [hb00.2, hb22.2]⟩
  have ha : ‖-(1 / 2 : ℂ) * (((Bd (B s) : ℝ) : ℂ) - Complex.I * ((Be (B s) : ℝ) : ℂ))‖
      ≤ C * s ^ (3 / 2 : ℝ) := by
    rw [norm_mul]
    have h1 : ‖-(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    have h2 : ‖((Bd (B s) : ℝ) : ℂ) - Complex.I * ((Be (B s) : ℝ) : ℂ)‖ ≤
        |Bd (B s)| + |Be (B s)| := by
      calc ‖((Bd (B s) : ℝ) : ℂ) - Complex.I * ((Be (B s) : ℝ) : ℂ)‖
          ≤ ‖((Bd (B s) : ℝ) : ℂ)‖ + ‖Complex.I * ((Be (B s) : ℝ) : ℂ)‖ := norm_sub_le _ _
        _ = |Bd (B s)| + |Be (B s)| := by
          simp [Real.norm_eq_abs]
    rw [h1]
    linarith [h2, hBd, hBe]
  have hb : ‖-(1 / 2 : ℂ) * (((Bd (B s) : ℝ) : ℂ) + Complex.I * ((Be (B s) : ℝ) : ℂ))‖
      ≤ C * s ^ (3 / 2 : ℝ) := by
    rw [norm_mul]
    have h1 : ‖-(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    have h2 : ‖((Bd (B s) : ℝ) : ℂ) + Complex.I * ((Be (B s) : ℝ) : ℂ)‖ ≤
        |Bd (B s)| + |Be (B s)| := by
      calc ‖((Bd (B s) : ℝ) : ℂ) + Complex.I * ((Be (B s) : ℝ) : ℂ)‖
          ≤ ‖((Bd (B s) : ℝ) : ℂ)‖ + ‖Complex.I * ((Be (B s) : ℝ) : ℂ)‖ := norm_add_le _ _
        _ = |Bd (B s)| + |Be (B s)| := by
          simp [Real.norm_eq_abs]
    rw [h1]
    linarith [h2, hBd, hBe]
  have hd : ‖((ConcreteYF.Bbeta (B s) : ℝ) : ℂ)‖ ≤ C * s ^ (3 / 2 : ℝ) := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using hBb
  have hC0 : 0 ≤ C * s ^ (3 / 2 : ℝ) := le_trans (norm_nonneg _) ha
  rw [gBD_apply]
  calc ‖(-(1 / 2 : ℂ) * (((Bd (B s) : ℝ) : ℂ) - Complex.I * ((Be (B s) : ℝ) : ℂ))) • D.src.H s
        + (-(1 / 2 : ℂ) * (((Bd (B s) : ℝ) : ℂ) + Complex.I * ((Be (B s) : ℝ) : ℂ))) •
            conjX (D.src.H s)
        - (((ConcreteYF.Bbeta (B s) : ℝ) : ℂ)) • D.src.R s‖
      ≤ ‖(-(1 / 2 : ℂ) * (((Bd (B s) : ℝ) : ℂ) - Complex.I * ((Be (B s) : ℝ) : ℂ))) • D.src.H s
        + (-(1 / 2 : ℂ) * (((Bd (B s) : ℝ) : ℂ) + Complex.I * ((Be (B s) : ℝ) : ℂ))) •
            conjX (D.src.H s)‖
        + ‖(((ConcreteYF.Bbeta (B s) : ℝ) : ℂ)) • D.src.R s‖ := norm_sub_le _ _
    _ ≤ ‖(-(1 / 2 : ℂ) * (((Bd (B s) : ℝ) : ℂ) - Complex.I * ((Be (B s) : ℝ) : ℂ))) • D.src.H s‖
        + ‖(-(1 / 2 : ℂ) * (((Bd (B s) : ℝ) : ℂ) + Complex.I * ((Be (B s) : ℝ) : ℂ))) •
            conjX (D.src.H s)‖
        + ‖(((ConcreteYF.Bbeta (B s) : ℝ) : ℂ)) • D.src.R s‖ :=
          add_le_add (norm_add_le _ _) le_rfl
    _ = ‖-(1 / 2 : ℂ) * (((Bd (B s) : ℝ) : ℂ) - Complex.I * ((Be (B s) : ℝ) : ℂ))‖ * ‖D.src.H s‖
        + ‖-(1 / 2 : ℂ) * (((Bd (B s) : ℝ) : ℂ) + Complex.I * ((Be (B s) : ℝ) : ℂ))‖ *
            ‖D.src.H s‖
        + ‖((ConcreteYF.Bbeta (B s) : ℝ) : ℂ)‖ * ‖D.src.R s‖ := by
          rw [norm_smul, norm_smul, norm_smul, norm_conjX]
    _ ≤ (C * s ^ (3 / 2 : ℝ)) * KH + (C * s ^ (3 / 2 : ℝ)) * KH
        + (C * s ^ (3 / 2 : ℝ)) * KR := by
          have t1 := mul_le_mul ha (hKH' s hsI) (norm_nonneg _) hC0
          have t2 := mul_le_mul hb (hKH' s hsI) (norm_nonneg _) hC0
          have t3 := mul_le_mul hd (hKR' s hsI) (norm_nonneg _) hC0
          linarith [t1, t2, t3]
    _ = (2 * KH + KR) * C * s ^ (3 / 2 : ℝ) := by ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
