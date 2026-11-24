import UnforcedLeray.Units.B0579

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory

namespace UnforcedLeray.Short.IIb.CCP

/-- A cylinder test function is bounded on the centered cell and vanishes for large `|η|`. -/
theorem test_single {c : ℝ} {ψ : B0579.Plane → ℝ} (hψ : B0579.IsCylTest c ψ) :
    ∃ R B : ℝ, 0 ≤ R ∧ 0 ≤ B ∧ ∀ x : B0579.Plane,
      (|x.1| ≤ c / 2 → |ψ x| ≤ B) ∧ (R < |x.2| → ψ x = 0) := by
  obtain ⟨R0, hR0⟩ := hψ.band
  set R := max R0 0 with hR
  have hK : IsCompact (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R : Set B0579.Plane) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hψ.continuous.continuousOn
  refine ⟨R, max B 0, le_max_right _ _, le_max_right _ _, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · by_cases h2 : |x.2| ≤ R
    · have := hB x ⟨abs_le.mp hx, abs_le.mp h2⟩
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_max_left _ _)
    · rw [hR0 x (lt_of_le_of_lt (le_max_left _ _) (not_le.mp h2)), abs_zero]
      exact le_max_right _ _
  · exact hR0 x (lt_of_le_of_lt (le_max_left _ _) hx)

theorem test_bounds {c : ℝ} {φ : B0579.Plane → ℝ} (hφ : B0579.IsCylTest c φ) :
    ∃ R B : ℝ, 0 ≤ R ∧ 0 ≤ B ∧ ∀ x : B0579.Plane, 
      (|x.1| ≤ c / 2 → |φ x| ≤ B ∧ |B0579.pd 0 φ x| ≤ B ∧ |B0579.pd 1 φ x| ≤ B ∧
        |B0579.pd 0 (B0579.pd 0 φ) x + B0579.pd 1 (B0579.pd 1 φ) x| ≤ 2 * B) ∧
      (R < |x.2| → φ x = 0 ∧ B0579.pd 0 φ x = 0 ∧ B0579.pd 1 φ x = 0 ∧
        B0579.pd 0 (B0579.pd 0 φ) x + B0579.pd 1 (B0579.pd 1 φ) x = 0) := by
  obtain ⟨R1, B1, hR1, hB1, h1⟩ := test_single hφ
  obtain ⟨R2, B2, hR2, hB2, h2⟩ := test_single (hφ.pd 0)
  obtain ⟨R3, B3, hR3, hB3, h3⟩ := test_single (hφ.pd 1)
  obtain ⟨R4, B4, hR4, hB4, h4⟩ := test_single ((hφ.pd 0).pd 0)
  obtain ⟨R5, B5, hR5, hB5, h5⟩ := test_single ((hφ.pd 1).pd 1)
  refine ⟨max R1 (max R2 (max R3 (max R4 R5))), max B1 (max B2 (max B3 (max B4 B5))),
    le_max_of_le_left hR1, le_max_of_le_left hB1, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · have e1 := (h1 x).1 hx
    have e2 := (h2 x).1 hx
    have e3 := (h3 x).1 hx
    have e4 := (h4 x).1 hx
    have e5 := (h5 x).1 hx
    have m1 : B1 ≤ max B1 (max B2 (max B3 (max B4 B5))) := le_max_left _ _
    have m2 : B2 ≤ max B1 (max B2 (max B3 (max B4 B5))) :=
      le_max_of_le_right (le_max_left _ _)
    have m3 : B3 ≤ max B1 (max B2 (max B3 (max B4 B5))) :=
      le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
    have m4 : B4 ≤ max B1 (max B2 (max B3 (max B4 B5))) :=
      le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
    have m5 : B5 ≤ max B1 (max B2 (max B3 (max B4 B5))) :=
      le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))
    refine ⟨e1.trans m1, e2.trans m2, e3.trans m3, ?_⟩
    calc _ ≤ |B0579.pd 0 (B0579.pd 0 φ) x| + |B0579.pd 1 (B0579.pd 1 φ) x| := abs_add_le _ _
      _ ≤ _ := by linarith
  · have n1 : R1 < |x.2| := lt_of_le_of_lt (le_max_left _ _) hx
    have n2 : R2 < |x.2| := lt_of_le_of_lt (le_max_of_le_right (le_max_left _ _)) hx
    have n3 : R3 < |x.2| :=
      lt_of_le_of_lt (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))) hx
    have n4 : R4 < |x.2| := lt_of_le_of_lt
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))) hx
    have n5 : R5 < |x.2| := lt_of_le_of_lt
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))) hx
    refine ⟨(h1 x).2 n1, (h2 x).2 n2, (h3 x).2 n3, ?_⟩
    rw [(h4 x).2 n4, (h5 x).2 n5, add_zero]

end UnforcedLeray.Short.IIb.CCP
