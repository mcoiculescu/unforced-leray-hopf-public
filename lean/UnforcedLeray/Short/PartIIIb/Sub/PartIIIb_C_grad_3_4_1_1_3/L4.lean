import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1_2.VjS
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1_2.Vj

/-!
# `PartIII-b:C/grad/3/4/1/1/3/4`: s-derivative bounds of `V_j` for `ν s ≤ 23/20`

Source `the November 2 reference manuscript`
4963-4980, 5036-5039, 5063-5079.

Range extension of `gradVjSBounds` (`VjS.lean`, `ν s ≤ 11/10`) to `ν s ≤ 23/20`, i.e.
`a = 1 + ν s ≤ 2.15 ≤ 9/4`.  The range-independent lemmas of `VjS.lean` are reused; the three
range-dependent ones are restated here: the Gaussian rate `vs9_exp_le` (`4a ≤ 9`) and the two
absorption bounds `vs9_bound3`, `vs9_bound4` with constant `23/20` in place of `11/10`.
-/

set_option autoImplicit false

noncomputable section

open Real

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Gaussian rate `4a ≤ 9` for `a ≤ 9/4` (range `ν s ≤ 23/20`). -/
lemma vs9_exp_le (S a : ℝ) (hS : 0 ≤ S) (ha1 : 1 ≤ a) (ha2 : a ≤ 9 / 4) :
    Real.exp (-S / (4 * a)) ≤ Real.exp (-(1 / 9) * S) := by
  apply Real.exp_le_exp.mpr
  have h1 : S / 9 ≤ S / (4 * a) := by
    gcongr <;> linarith
  rw [neg_div]
  linarith

lemma vs9_bound3 (B S E T ν s : ℝ) (hB : 1 ≤ B) (hS : 0 ≤ S) (hSB : S ≤ B ^ 2) (hE : 0 ≤ E)
    (hET : E ≤ T) (hν : 0 ≤ ν) (hs : 0 ≤ s) (hνs : ν * s ≤ 23 / 20) :
    B * (s * (ν * E * (2 + S / 4) * (1 + S))) ≤ 20 * (B ^ 12 * T) := by
  have hB0 : 0 ≤ B := by linarith
  have hT : 0 ≤ T := le_trans hE hET
  have p := vs_poly1 B S hB hS hSB
  have hB5 : B ^ 5 ≤ B ^ 12 := pow_le_pow_right₀ hB (by norm_num)
  have hEB : E * B ^ 5 ≤ T * B ^ 12 := mul_le_mul hET hB5 (by positivity) hT
  have hX : 0 ≤ (2 + S / 4) * (1 + S) := mul_nonneg (by linarith) (by linarith)
  calc B * (s * (ν * E * (2 + S / 4) * (1 + S)))
      = (ν * s) * (E * (B * ((2 + S / 4) * (1 + S)))) := by ring
    _ ≤ (23 / 20) * (E * (6 * B ^ 5)) :=
        mul_le_mul hνs (mul_le_mul_of_nonneg_left p hE) (mul_nonneg hE (mul_nonneg hB0 hX))
          (by norm_num)
    _ = (23 / 20) * 6 * (E * B ^ 5) := by ring
    _ ≤ (23 / 20) * 6 * (T * B ^ 12) := mul_le_mul_of_nonneg_left hEB (by norm_num)
    _ ≤ 20 * (B ^ 12 * T) := by nlinarith [mul_nonneg (pow_nonneg hB0 12) hT]

lemma vs9_bound4 (B S E T ν s : ℝ) (hB : 1 ≤ B) (hS : 0 ≤ S) (hSB : S ≤ B ^ 2) (hE : 0 ≤ E)
    (hET : E ≤ T) (hν : 0 ≤ ν) (hs : 0 ≤ s) (hνs : ν * s ≤ 23 / 20) :
    B * (s * (ν * E * ((2 + S / 4) + B * (5 + S / 2) * (1 + S)))) ≤ 20 * (B ^ 12 * T) := by
  have hB0 : 0 ≤ B := by linarith
  have hT : 0 ≤ T := le_trans hE hET
  have p := vs_poly2 B S hB hS hSB
  have hB6 : B ^ 6 ≤ B ^ 12 := pow_le_pow_right₀ hB (by norm_num)
  have hEB : E * B ^ 6 ≤ T * B ^ 12 := mul_le_mul hET hB6 (by positivity) hT
  have hK0 : 0 ≤ (2 + S / 4) + B * (5 + S / 2) * (1 + S) := by
    have := mul_nonneg (mul_nonneg hB0 (by linarith : (0:ℝ) ≤ 5 + S / 2))
      (by linarith : (0:ℝ) ≤ 1 + S)
    linarith
  calc B * (s * (ν * E * ((2 + S / 4) + B * (5 + S / 2) * (1 + S))))
      = (ν * s) * (E * (B * ((2 + S / 4) + B * (5 + S / 2) * (1 + S)))) := by ring
    _ ≤ (23 / 20) * (E * (15 * B ^ 6)) :=
        mul_le_mul hνs (mul_le_mul_of_nonneg_left p hE)
          (mul_nonneg hE (mul_nonneg hB0 hK0)) (by norm_num)
    _ = (23 / 20) * 15 * (E * B ^ 6) := by ring
    _ ≤ (23 / 20) * 15 * (T * B ^ 12) := mul_le_mul_of_nonneg_left hEB (by norm_num)
    _ ≤ 20 * (B ^ 12 * T) := by nlinarith [mul_nonneg (pow_nonneg hB0 12) hT]

theorem gradVjSBounds_ext : ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν s : ℝ) (j : ℤ) (x : ℝ × ℝ), 0 < ν → ν ≤ 1 → 0 < s → s ≤ (23 / 20) / ν → ∀ a : Fin 2, (∀ s' : ℝ, 0 < s' → DifferentiableAt ℝ (fun t => Vj ν t j x) s') ∧ (∀ s' : ℝ, 0 < s' → DifferentiableAt ℝ (fun t => fderiv ℝ (Vj ν t j) x (ei a)) s') ∧ (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) * (s * ‖deriv (fun t => Vj ν t j x) s‖) ≤ C * gradW ν x j ∧ (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) * (s * ‖deriv (fun t => fderiv ℝ (Vj ν t j) x (ei a)) s‖) ≤ C * gradW ν x j := by
  refine ⟨20, by norm_num, ?_⟩
  intro ν s j x hν hν1 hs hs1 a
  have hνs : ν * s ≤ 23 / 20 := by
    have h := (le_div_iff₀ hν).mp hs1
    linarith [mul_comm s ν]
  have hν0 : 0 ≤ ν := hν.le
  have hs0 : 0 ≤ s := hs.le
  have hA : 1 ≤ ageA ν s := vs_A_ge hν0 hs0
  have hA2 : ageA ν s ≤ 9 / 4 := by unfold ageA; linarith
  have hA' : ∀ s' : ℝ, 0 < s' → 1 ≤ ageA ν s' := fun s' hs' => vs_A_ge hν0 hs'.le
  have hS0 : 0 ≤ sq2 (xj ν j x) := hu_sq2_nonneg _
  have hSB : sq2 (xj ν j x) ≤ (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 2 :=
    gv_sq_le (x.1 - (j : ℝ) * cOf ν) x.2
  have hB1 : (1 : ℝ) ≤ 1 + |x.1 - (j : ℝ) * cOf ν| + |x.2| := by
    linarith [abs_nonneg (x.1 - (j : ℝ) * cOf ν), abs_nonneg x.2]
  have hBX : |(xj ν j x).1| + |(xj ν j x).2| ≤ 1 + |x.1 - (j : ℝ) * cOf ν| + |x.2| := by
    show |x.1 - (j : ℝ) * cOf ν| + |x.2| ≤ _
    linarith
  have hWeq : gradW ν x j = (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 12
      * Real.exp (-(1 / 9) * sq2 (xj ν j x)) :=
    gv_L_eq (x.1 - (j : ℝ) * cOf ν) x.2
  have hET : Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) ≤ Real.exp (-(1 / 9) * sq2 (xj ν j x)) :=
    vs9_exp_le _ _ hS0 hA hA2
  have hE0 : 0 ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := (Real.exp_pos _).le
  have hB0 : (0 : ℝ) ≤ 1 + |x.1 - (j : ℝ) * cOf ν| + |x.2| := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s' hs'
    exact (vs_Vj_hasDeriv ν j x s' (hA' s' hs')).differentiableAt
  · intro s' hs'
    rw [vs_fderiv_eq]
    exact (vs_hsG_hasDeriv ν j x a s' (hA' s' hs')).differentiableAt
  · rw [vs_deriv_Vj ν j x s hA, hs_smul_jrot, hWeq]
    have hd := vs_Ed_bound ν s j x hν0 hA hS0
    have hn := gv_norm_le (xj ν j x)
    calc (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) * (s * (|vsEd ν s j x| * ‖xj ν j x‖))
        ≤ (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) *
            (s * (ν * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (2 + sq2 (xj ν j x) / 4)
              * (1 + sq2 (xj ν j x)))) := by
          apply mul_le_mul_of_nonneg_left _ hB0
          apply mul_le_mul_of_nonneg_left _ hs0
          exact mul_le_mul hd hn (norm_nonneg _)
            (mul_nonneg (mul_nonneg hν0 hE0) (by linarith))
      _ ≤ 20 * ((1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 12
            * Real.exp (-(1 / 9) * sq2 (xj ν j x))) :=
          vs9_bound3 _ _ _ _ _ _ hB1 hS0 hSB hE0 hET hν0 hs0 hνs
  · rw [vs_fderiv_eq, (vs_hsG_hasDeriv ν j x a s hA).deriv, hWeq]
    have hd := vs_Ed_bound ν s j x hν0 hA hS0
    have hN : |vsN ν j x a| ≤ 2 * (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) := by
      obtain ⟨c1, c2⟩ := vs_ei_abs a
      exact vs_N_le _ _ _ _ _ c1 c2 hBX
    have hL := vs_hsL_le ν s j x a _ hB0 hA hN
    have hLd := vs_vsLd_le ν s j x a _ hν0 hB0 hA hN
    have hP := vs_hsE_le ν s j x hA
    have hk := vs_kappa _ _ _ _ _ _ _ _ hd (mul_nonneg (mul_nonneg hν0 hE0) (by linarith))
      hL hP hLd hE0
    have hn := gv_norm_le (xj ν j x)
    have hei := hs_ei_norm_le a
    have hGn := vs_norm2 (vsEd ν s j x) (vsEd ν s j x * hsL ν s j a x + hsE ν s j x * vsLd ν s j x a)
      (ei a) (xj ν j x)
    have hG : ‖vsEd ν s j x • Jrot (ei a)
        + ((vsEd ν s j x * hsL ν s j a x + hsE ν s j x * vsLd ν s j x a) • Jrot (xj ν j x))‖
        ≤ ν * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))
            * ((2 + sq2 (xj ν j x) / 4) + (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|)
              * (5 + sq2 (xj ν j x) / 2) * (1 + sq2 (xj ν j x))) := by
      refine hGn.trans ?_
      have hq1 : |vsEd ν s j x| * ‖ei a‖ ≤ |vsEd ν s j x| :=
        mul_le_of_le_one_right (abs_nonneg _) hei
      have hQ : 0 ≤ ν * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (2 + sq2 (xj ν j x) / 4) :=
        mul_nonneg (mul_nonneg hν0 hE0) (by linarith)
      have hQ' : 0 ≤ ν * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (2 + sq2 (xj ν j x) / 4) :=
        mul_nonneg (mul_nonneg hν0 hE0) (by linarith)
      have hq2 : |vsEd ν s j x * hsL ν s j a x + hsE ν s j x * vsLd ν s j x a| * ‖xj ν j x‖
          ≤ (ν * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (2 + sq2 (xj ν j x) / 4) * (2 * (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|)) + Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * ((1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) * ν)) * (1 + sq2 (xj ν j x)) :=
        mul_le_mul hk hn (norm_nonneg _)
          (add_nonneg (mul_nonneg hQ' (by linarith)) (mul_nonneg hE0 (mul_nonneg hB0 hν0)))
      calc _ ≤ ν * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (2 + sq2 (xj ν j x) / 4) + (ν * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (2 + sq2 (xj ν j x) / 4) * (2 * (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|)) + Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * ((1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) * ν)) * (1 + sq2 (xj ν j x)) :=
            add_le_add (hq1.trans hd) hq2
        _ = ν * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * ((2 + sq2 (xj ν j x) / 4) + (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) * (5 + sq2 (xj ν j x) / 2) * (1 + sq2 (xj ν j x))) := by ring
    calc (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) * (s * ‖vsEd ν s j x • Jrot (ei a)
          + ((vsEd ν s j x * hsL ν s j a x + hsE ν s j x * vsLd ν s j x a) • Jrot (xj ν j x))‖)
        ≤ (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) * (s * (ν * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))
            * ((2 + sq2 (xj ν j x) / 4) + (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|)
              * (5 + sq2 (xj ν j x) / 2) * (1 + sq2 (xj ν j x))))) := by
          apply mul_le_mul_of_nonneg_left _ hB0
          exact mul_le_mul_of_nonneg_left hG hs0
      _ ≤ 20 * ((1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 12
            * Real.exp (-(1 / 9) * sq2 (xj ν j x))) :=
          vs9_bound4 _ _ _ _ _ _ hB1 hS0 hSB hE0 hET hν0 hs0 hνs

end UnforcedLeray.Short.PartIIIb.Concrete
