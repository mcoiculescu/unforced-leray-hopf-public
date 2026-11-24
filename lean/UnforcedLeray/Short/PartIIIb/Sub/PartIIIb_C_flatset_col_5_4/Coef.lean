import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5_4
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.ProductRule.GCont_3

/-!
# `FcvEllCoef`: uniform bounds of the tested coefficients (source 2819-2836)

On `0 ≤ r ≤ T` and `y` in the cell, the test-function coefficients are bounded: they are continuous
on the compact `[0,T] × box` (joint continuity `IIIa.train_joint_cont`), and vanish for `|y.2|`
large (cylinder test `φ`, `pd φ`, `lapP φ` all vanish outside a band).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem ellCoef_bound_y {c R : ℝ} {h : ℝ × ℝ → ℝ} (hh : Continuous h) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ B0579.box c R, |h y| ≤ M := by
  obtain ⟨M, hM⟩ := (B0579.isCompact_box c R).exists_bound_of_continuousOn hh.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun y hy => ?_⟩
  have := hM y hy
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

theorem ellCoef_bound_ry {c R T : ℝ} {g : ℝ × (ℝ × ℝ) → ℝ}
    (hg : ContinuousOn g (Ici 0 ×ˢ univ)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ r ∈ Icc (0 : ℝ) T, ∀ y ∈ B0579.box c R, |g (r, y)| ≤ M := by
  have hK : IsCompact (Icc (0 : ℝ) T ×ˢ B0579.box c R) :=
    isCompact_Icc.prod (B0579.isCompact_box c R)
  have hsub : Icc (0 : ℝ) T ×ˢ B0579.box c R ⊆ Ici 0 ×ˢ univ :=
    prod_mono (fun r hr => hr.1) (subset_univ _)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hg.mono hsub)
  refine ⟨max M 0, le_max_right _ _, fun r hr y hy => ?_⟩
  have := hM (r, y) (mk_mem_prod hr hy)
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

theorem train_coord_cont_aux {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (k : Fin 2) :
    ContinuousOn (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 k) (Ici 0 ×ˢ univ) := by
  have h := (UnforcedLeray.Short.IIIa.train_joint_cont tr).1
  exact ((EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).continuous.comp_continuousOn h)

theorem abs_comb_aux {a b p q V0 V1 P0 P1 : ℝ} (ha : |a| ≤ V0) (hb : |b| ≤ V1)
    (hp : |p| ≤ P0) (hq : |q| ≤ P1) (hV0 : 0 ≤ V0) (hV1 : 0 ≤ V1) :
    |a * p + b * q| ≤ V0 * P0 + V1 * P1 := by
  calc |a * p + b * q| ≤ |a * p| + |b * q| := abs_add_le _ _
    _ = |a| * |p| + |b| * |q| := by rw [abs_mul, abs_mul]
    _ ≤ V0 * P0 + V1 * P1 :=
        add_le_add (mul_le_mul ha hp (abs_nonneg _) hV0) (mul_le_mul hb hq (abs_nonneg _) hV1)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst in
theorem fcvEllCoef : UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FcvEllCoef := by
  unfold FcvEllCoef
  intro ν c tr φ hφ T
  obtain ⟨R0, hR0⟩ := hφ.band
  obtain ⟨R1, hR1⟩ := (hφ.pd 0).band
  obtain ⟨R2, hR2⟩ := (hφ.pd 1).band
  obtain ⟨R3, hR3⟩ := ((hφ.pd 0).pd 0).band
  obtain ⟨R4, hR4⟩ := ((hφ.pd 1).pd 1).band
  obtain ⟨Rb, hRb0, hRb1, hRb2, hRb3, hRb4⟩ : ∃ Rb : ℝ, R0 ≤ Rb ∧ R1 ≤ Rb ∧ R2 ≤ Rb ∧
      R3 ≤ Rb ∧ R4 ≤ Rb := ⟨max (max (max R0 R1) (max R2 R3)) R4, by simp [le_max_iff],
        by simp [le_max_iff], by simp [le_max_iff], by simp [le_max_iff], by simp [le_max_iff]⟩
  have hvan : ∀ y : ℝ × ℝ, Rb < |y.2| →
      φ y = 0 ∧ B0579.pd 0 φ y = 0 ∧ B0579.pd 1 φ y = 0 ∧
        B0579.pd 0 (B0579.pd 0 φ) y + B0579.pd 1 (B0579.pd 1 φ) y = 0 := by
    intro y hy
    refine ⟨hR0 y (lt_of_le_of_lt hRb0 hy), hR1 y (lt_of_le_of_lt hRb1 hy),
      hR2 y (lt_of_le_of_lt hRb2 hy), ?_⟩
    rw [hR3 y (lt_of_le_of_lt hRb3 hy), hR4 y (lt_of_le_of_lt hRb4 hy), add_zero]
  obtain ⟨Lp, hLp0, hLp⟩ := ellCoef_bound_y (c := c) (R := Rb)
    (h := fun y => B0579.pd 0 (B0579.pd 0 φ) y + B0579.pd 1 (B0579.pd 1 φ) y)
    (((hφ.pd 0).pd 0).continuous.add ((hφ.pd 1).pd 1).continuous)
  obtain ⟨P0, hP00, hP0⟩ := ellCoef_bound_y (c := c) (R := Rb) (h := B0579.pd 0 φ)
    (hφ.pd 0).continuous
  obtain ⟨P1, hP10, hP1⟩ := ellCoef_bound_y (c := c) (R := Rb) (h := B0579.pd 1 φ)
    (hφ.pd 1).continuous
  obtain ⟨Ph, hPh0, hPh⟩ := ellCoef_bound_y (c := c) (R := Rb) (h := φ) hφ.continuous
  obtain ⟨V0, hV00, hV0⟩ := ellCoef_bound_ry (c := c) (R := Rb) (T := T)
    (g := fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 0) (train_coord_cont_aux tr 0)
  obtain ⟨V1, hV10, hV1⟩ := ellCoef_bound_ry (c := c) (R := Rb) (T := T)
    (g := fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 1) (train_coord_cont_aux tr 1)
  obtain ⟨E0, hE00, hE0⟩ := ellCoef_bound_ry (c := c) (R := Rb) (T := T)
    (g := fun p : ℝ × (ℝ × ℝ) => B0579.pd 0 (fun x => UnforcedLeray.B0238.Ec tr p.1 x) p.2)
    ((UnforcedLeray.Short.IIIa.train_joint_cont tr).2 0)
  obtain ⟨E1, hE10, hE1⟩ := ellCoef_bound_ry (c := c) (R := Rb) (T := T)
    (g := fun p : ℝ × (ℝ × ℝ) => B0579.pd 1 (fun x => UnforcedLeray.B0238.Ec tr p.1 x) p.2)
    ((UnforcedLeray.Short.IIIa.train_joint_cont tr).2 1)
  refine ⟨|ν| * Lp + (V0 * P0 + V1 * P1), max E0 E1 * Ph, ?_⟩
  intro r hr y hy
  have hA0 : 0 ≤ |ν| * Lp + (V0 * P0 + V1 * P1) :=
    add_nonneg (mul_nonneg (abs_nonneg _) hLp0) (add_nonneg (mul_nonneg hV00 hP00)
      (mul_nonneg hV10 hP10))
  have hB0 : 0 ≤ max E0 E1 * Ph := mul_nonneg (le_trans hE00 (le_max_left _ _)) hPh0
  by_cases hyb : |y.2| ≤ Rb
  · have hybox : y ∈ B0579.box c Rb := B0579.mem_box_of_mem_cell hy hyb
    have hv0 := hV0 r hr y hybox
    have hv1 := hV1 r hr y hybox
    have hl := hLp y hybox
    have hp0 := hP0 y hybox
    have hp1 := hP1 y hybox
    have hf := hPh y hybox
    have he0 := hE0 r hr y hybox
    have he1 := hE1 r hr y hybox
    simp only at hv0 hv1 he0 he1
    refine ⟨?_, ?_⟩
    · have hc := abs_comb_aux (a := tr.v r y 0) (b := tr.v r y 1)
        (p := B0579.pd 0 φ y) (q := B0579.pd 1 φ y) hv0 hv1 hp0 hp1 hV00 hV10
      calc |ν * UnforcedLeray.Short.IIIa.lapP φ y +
            (tr.v r y 0 * B0579.pd 0 φ y + tr.v r y 1 * B0579.pd 1 φ y)|
          ≤ |ν * UnforcedLeray.Short.IIIa.lapP φ y| +
            |tr.v r y 0 * B0579.pd 0 φ y + tr.v r y 1 * B0579.pd 1 φ y| := abs_add_le _ _
        _ ≤ |ν| * Lp + (V0 * P0 + V1 * P1) := by
            refine add_le_add ?_ hc
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left hl (abs_nonneg _)
    · intro k
      have hb0 : |B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) y * φ y| ≤ max E0 E1 * Ph := by
        rw [abs_mul]
        exact mul_le_mul (le_trans he0 (le_max_left _ _)) hf (abs_nonneg _)
          (le_trans hE00 (le_max_left _ _))
      have hb1 : |B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) y * φ y| ≤ max E0 E1 * Ph := by
        rw [abs_mul]
        exact mul_le_mul (le_trans he1 (le_max_right _ _)) hf (abs_nonneg _)
          (le_trans hE00 (le_max_left _ _))
      fin_cases k
      · exact hb0
      · exact hb1
  · have hyb' : Rb < |y.2| := not_le.1 hyb
    obtain ⟨h1, h2, h3, h4⟩ := hvan y hyb'
    refine ⟨?_, ?_⟩
    · show |ν * UnforcedLeray.Short.IIIa.lapP φ y +
          (tr.v r y 0 * B0579.pd 0 φ y + tr.v r y 1 * B0579.pd 1 φ y)| ≤ _
      have hl : UnforcedLeray.Short.IIIa.lapP φ y = 0 := h4
      simp only [hl, h2, h3, mul_zero, zero_add, add_zero, abs_zero]
      exact hA0
    · intro k
      simp only [h1, mul_zero, abs_zero]
      exact hB0
