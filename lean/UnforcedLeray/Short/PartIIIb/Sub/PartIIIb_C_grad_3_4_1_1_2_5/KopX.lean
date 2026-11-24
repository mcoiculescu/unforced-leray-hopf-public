import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1_2_5
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1_2_5.W2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1_2.Der

/-!
# `PartIII-b:C/grad/3/4/1/1/2/5/3`: `x`-part of the `𝒦` envelope of `h^p_A`

Source `the November 2 reference manuscript`
4963-4980, 5063-5079.  `𝒦ψ = η ∂_η ψ + 2 s ∂_s ψ`; the `x`-part is `η ∂_η` of the lattice term.
The derivative `∂_η` of `gradHpTm i` is the explicit `drDv` (Der.lean), and the extra factor
`|η| ≤ B` is absorbed by the weight-two bounds (`gradVjWeight2`, W2.lean).

Proved: `gradKopXEnv`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Splitting a weight-two sum bound into its three summands. -/
lemma kx_sum (w a b c K : ℝ) (hw : 0 ≤ w) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : w * (a + b + c) ≤ K) : w * a ≤ K ∧ w * b ≤ K ∧ w * c ≤ K := by
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith [mul_nonneg hw ha, mul_nonneg hw hb, mul_nonneg hw hc]

/-- Weight `B ≥ 1` is dominated by weight `B²`. -/
lemma kx_w (B K : ℝ) (v : ℝ × ℝ) (hB : 1 ≤ B) (hv : B ^ 2 * ‖v‖ ≤ K) : B * ‖v‖ ≤ K := by
  have hn := norm_nonneg v
  have hBB : B ≤ B ^ 2 := by nlinarith
  exact (mul_le_mul_of_nonneg_right hBB hn).trans hv

/-- Components of a vector are bounded by its norm. -/
lemma kx_fst_snd (w K : ℝ) (v : ℝ × ℝ) (hw : 0 ≤ w) (hv : w * ‖v‖ ≤ K) :
    w * |v.1| ≤ K ∧ w * |v.2| ≤ K :=
  ⟨(mul_le_mul_of_nonneg_left (norm_fst_le v) hw).trans hv,
    (mul_le_mul_of_nonneg_left (norm_snd_le v) hw).trans hv⟩

/-- Real estimate: `x_2` times the `e_p` directional derivative of the `j`-th lattice term. -/
lemma kx_core (G K B x1 x2 m00 m02 m20 m22 r1 r2 e1 e2 p1 p2 h0 h1 d0 d1 : ℝ)
    (hG : 0 ≤ G) (hK : 0 ≤ K) (hB : 1 ≤ B) (hx2 : |x2| ≤ B) (hBx : |x1| + |x2| ≤ B)
    (hm00 : |m00| ≤ G) (hm02 : |m02| ≤ G) (hm20 : |m20| ≤ G) (hm22 : |m22| ≤ G)
    (hr1 : |r1| ≤ G) (hr2 : |r2| ≤ G) (he1 : |e1| ≤ 1) (he2 : |e2| ≤ 1)
    (hp1 : B * |p1| ≤ K) (hp2 : B * |p2| ≤ K) (hh0 : B * |h0| ≤ K) (hh1 : B * |h1| ≤ K)
    (hd0 : B ^ 2 * |d0| ≤ K) (hd1 : B ^ 2 * |d1| ≤ K) :
    |x2 * ((r1 * p1 + r2 * p2) - (((m00 * x1 + m02 * x2) * d0 + (m00 * e1 + m02 * e2) * h0)
        + ((m20 * x1 + m22 * x2) * d1 + (m20 * e1 + m22 * e2) * h1)))| ≤ 8 * G * K := by
  have B0 : 0 ≤ B := by linarith
  have s3 : |m00 * x1 + m02 * x2| ≤ G * B := by
    calc |m00 * x1 + m02 * x2| ≤ |m00 * x1| + |m02 * x2| := abs_add_le _ _
      _ = |m00| * |x1| + |m02| * |x2| := by rw [abs_mul, abs_mul]
      _ ≤ G * |x1| + G * |x2| := add_le_add (mul_le_mul_of_nonneg_right hm00 (abs_nonneg _))
          (mul_le_mul_of_nonneg_right hm02 (abs_nonneg _))
      _ = G * (|x1| + |x2|) := by ring
      _ ≤ G * B := mul_le_mul_of_nonneg_left hBx hG
  have s4 : |m20 * x1 + m22 * x2| ≤ G * B := by
    calc |m20 * x1 + m22 * x2| ≤ |m20 * x1| + |m22 * x2| := abs_add_le _ _
      _ = |m20| * |x1| + |m22| * |x2| := by rw [abs_mul, abs_mul]
      _ ≤ G * |x1| + G * |x2| := add_le_add (mul_le_mul_of_nonneg_right hm20 (abs_nonneg _))
          (mul_le_mul_of_nonneg_right hm22 (abs_nonneg _))
      _ = G * (|x1| + |x2|) := by ring
      _ ≤ G * B := mul_le_mul_of_nonneg_left hBx hG
  have s1 : |m00 * e1 + m02 * e2| ≤ G + G := by
    calc |m00 * e1 + m02 * e2| ≤ |m00 * e1| + |m02 * e2| := abs_add_le _ _
      _ = |m00| * |e1| + |m02| * |e2| := by rw [abs_mul, abs_mul]
      _ ≤ G * 1 + G * 1 := add_le_add (mul_le_mul hm00 he1 (abs_nonneg _) hG)
          (mul_le_mul hm02 he2 (abs_nonneg _) hG)
      _ = G + G := by ring
  have s2 : |m20 * e1 + m22 * e2| ≤ G + G := by
    calc |m20 * e1 + m22 * e2| ≤ |m20 * e1| + |m22 * e2| := abs_add_le _ _
      _ = |m20| * |e1| + |m22| * |e2| := by rw [abs_mul, abs_mul]
      _ ≤ G * 1 + G * 1 := add_le_add (mul_le_mul hm20 he1 (abs_nonneg _) hG)
          (mul_le_mul hm22 he2 (abs_nonneg _) hG)
      _ = G + G := by ring
  -- the principal term `x_2 · (r · p)`
  have q1 : |x2 * (r1 * p1 + r2 * p2)| ≤ G * K + G * K := by
    have h1 : |r1 * p1 + r2 * p2| ≤ G * |p1| + G * |p2| := by
      calc |r1 * p1 + r2 * p2| ≤ |r1 * p1| + |r2 * p2| := abs_add_le _ _
        _ = |r1| * |p1| + |r2| * |p2| := by rw [abs_mul, abs_mul]
        _ ≤ G * |p1| + G * |p2| := add_le_add (mul_le_mul_of_nonneg_right hr1 (abs_nonneg _))
            (mul_le_mul_of_nonneg_right hr2 (abs_nonneg _))
    rw [abs_mul]
    calc |x2| * |r1 * p1 + r2 * p2| ≤ B * (G * |p1| + G * |p2|) :=
          mul_le_mul hx2 h1 (abs_nonneg _) B0
      _ = G * (B * |p1|) + G * (B * |p2|) := by ring
      _ ≤ G * K + G * K := add_le_add (mul_le_mul_of_nonneg_left hp1 hG)
          (mul_le_mul_of_nonneg_left hp2 hG)
  -- the `𝑑` terms with `x`-weight
  have q2 : |x2 * ((m00 * x1 + m02 * x2) * d0)| ≤ G * K := by
    have e : |x2 * ((m00 * x1 + m02 * x2) * d0)| = |x2| * |m00 * x1 + m02 * x2| * |d0| := by
      rw [abs_mul, abs_mul]; ring
    rw [e]
    calc |x2| * |m00 * x1 + m02 * x2| * |d0| ≤ B * (G * B) * |d0| :=
          mul_le_mul_of_nonneg_right (mul_le_mul hx2 s3 (abs_nonneg _) B0) (abs_nonneg _)
      _ = G * (B ^ 2 * |d0|) := by ring
      _ ≤ G * K := mul_le_mul_of_nonneg_left hd0 hG
  have q4 : |x2 * ((m20 * x1 + m22 * x2) * d1)| ≤ G * K := by
    have e : |x2 * ((m20 * x1 + m22 * x2) * d1)| = |x2| * |m20 * x1 + m22 * x2| * |d1| := by
      rw [abs_mul, abs_mul]; ring
    rw [e]
    calc |x2| * |m20 * x1 + m22 * x2| * |d1| ≤ B * (G * B) * |d1| :=
          mul_le_mul_of_nonneg_right (mul_le_mul hx2 s4 (abs_nonneg _) B0) (abs_nonneg _)
      _ = G * (B ^ 2 * |d1|) := by ring
      _ ≤ G * K := mul_le_mul_of_nonneg_left hd1 hG
  -- the `h` terms with `e`-weight
  have q3 : |x2 * ((m00 * e1 + m02 * e2) * h0)| ≤ (G + G) * K := by
    have e : |x2 * ((m00 * e1 + m02 * e2) * h0)| = |x2| * |m00 * e1 + m02 * e2| * |h0| := by
      rw [abs_mul, abs_mul]; ring
    rw [e]
    calc |x2| * |m00 * e1 + m02 * e2| * |h0| ≤ B * (G + G) * |h0| :=
          mul_le_mul_of_nonneg_right (mul_le_mul hx2 s1 (abs_nonneg _) B0) (abs_nonneg _)
      _ = (G + G) * (B * |h0|) := by ring
      _ ≤ (G + G) * K := mul_le_mul_of_nonneg_left hh0 (by linarith)
  have q5 : |x2 * ((m20 * e1 + m22 * e2) * h1)| ≤ (G + G) * K := by
    have e : |x2 * ((m20 * e1 + m22 * e2) * h1)| = |x2| * |m20 * e1 + m22 * e2| * |h1| := by
      rw [abs_mul, abs_mul]; ring
    rw [e]
    calc |x2| * |m20 * e1 + m22 * e2| * |h1| ≤ B * (G + G) * |h1| :=
          mul_le_mul_of_nonneg_right (mul_le_mul hx2 s2 (abs_nonneg _) B0) (abs_nonneg _)
      _ = (G + G) * (B * |h1|) := by ring
      _ ≤ (G + G) * K := mul_le_mul_of_nonneg_left hh1 (by linarith)
  have eq : x2 * ((r1 * p1 + r2 * p2) - (((m00 * x1 + m02 * x2) * d0 + (m00 * e1 + m02 * e2) * h0)
        + ((m20 * x1 + m22 * x2) * d1 + (m20 * e1 + m22 * e2) * h1)))
      = x2 * (r1 * p1 + r2 * p2) - (x2 * ((m00 * x1 + m02 * x2) * d0)
        + x2 * ((m00 * e1 + m02 * e2) * h0) + (x2 * ((m20 * x1 + m22 * x2) * d1)
        + x2 * ((m20 * e1 + m22 * e2) * h1))) := by ring
  rw [eq]
  obtain ⟨a1, a1'⟩ := abs_le.mp q1
  obtain ⟨a2, a2'⟩ := abs_le.mp q2
  obtain ⟨a3, a3'⟩ := abs_le.mp q3
  obtain ⟨a4, a4'⟩ := abs_le.mp q4
  obtain ⟨a5, a5'⟩ := abs_le.mp q5
  rw [abs_le]
  constructor <;> nlinarith

theorem gradKopXEnv : GradKopXEnv := by
  obtain ⟨C2, hC2, hW⟩ := gradVjWeight2
  refine ⟨8 * C2, by linarith, ?_⟩
  intro ν s χf A hd x i j
  obtain ⟨hν, hν1, hs, hs1, _⟩ := hd
  have hWd : 0 ≤ gradW ν x j := gradW_nonneg ν x j
  have hG : 0 ≤ gradF ν χf A s := gradF_nonneg _ _ _ _
  have hK : 0 ≤ C2 * gradW ν x j := mul_nonneg hC2 hWd
  have hB1 : (1 : ℝ) ≤ 1 + |x.1 - (j : ℝ) * cOf ν| + |x.2| := by
    linarith [abs_nonneg (x.1 - (j : ℝ) * cOf ν), abs_nonneg x.2]
  have hB0 : (0 : ℝ) ≤ 1 + |x.1 - (j : ℝ) * cOf ν| + |x.2| := by linarith
  have hx2 : |x.2| ≤ 1 + |x.1 - (j : ℝ) * cOf ν| + |x.2| := by
    linarith [abs_nonneg (x.1 - (j : ℝ) * cOf ν), abs_nonneg x.2]
  have hBx : |(xj ν j x).1| + |(xj ν j x).2| ≤ 1 + |x.1 - (j : ℝ) * cOf ν| + |x.2| := by
    show |x.1 - (j : ℝ) * cOf ν| + |x.2| ≤ _
    linarith
  have hW' := hW ν s j x hν hν1 hs hs1
  -- weight-two bounds on `V_j` and its derivatives
  have hD : ∀ a : Fin 2, (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 2
      * ‖fderiv ℝ (Vj ν s j) x (ei a)‖ ≤ C2 * gradW ν x j := fun a =>
    (kx_sum _ _ _ _ _ (sq_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (hW' a 0)).2.1
  have hDD : ∀ a b : Fin 2, (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 2
      * ‖fderiv ℝ (fun y => fderiv ℝ (Vj ν s j) y (ei a)) x (ei b)‖ ≤ C2 * gradW ν x j := fun a b =>
    (kx_sum _ _ _ _ _ (sq_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (hW' a b)).2.2
  -- the values `hsG_b x = ∂_b V_j(x)`
  have hGb : ∀ b : Fin 2, (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) * |(hsG ν s j b x).1| ≤ C2 * gradW ν x j
      ∧ (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) * |(hsG ν s j b x).2| ≤ C2 * gradW ν x j := by
    intro b
    have h : (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 2 * ‖hsG ν s j b x‖ ≤ C2 * gradW ν x j := by
      rw [← hs_eq ν s j b x]
      exact hD b
    exact kx_fst_snd _ _ _ hB0 (kx_w _ _ _ hB1 h)
  -- the derivatives `∂_p hsG_b x` (second derivative of `V_j`)
  have hDb : ∀ b p : Fin 2, (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 2
      * |(fderiv ℝ (hsG ν s j b) x (ei p)).1| ≤ C2 * gradW ν x j
      ∧ (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 2
      * |(fderiv ℝ (hsG ν s j b) x (ei p)).2| ≤ C2 * gradW ν x j := by
    intro b p
    have e : hsG ν s j b = fun y => fderiv ℝ (Vj ν s j) y (ei b) :=
      funext fun y => (hs_eq ν s j b y).symm
    rw [e]
    exact kx_fst_snd _ _ _ (sq_nonneg _) (hDD b p)
  have hent : ∀ a b : Fin 3, |Ay ν χf A s a b| ≤ gradF ν χf A s := by
    intro a b
    have hfr : 0 ≤ frob (sDeriv (Ay ν χf A) s) := Real.sqrt_nonneg _
    have hfr2 : 0 ≤ frob (sDeriv (sDeriv (Ay ν χf A)) s) := Real.sqrt_nonneg _
    have := dr_entry_le (Ay ν χf A s) a b
    unfold gradF
    linarith
  have hp1 := hGb 1
  have hd1 := hDb
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  rcases hi with rfl | rfl
  · have e : fderiv ℝ (gradHpTm 0 ν χf A j s) x (ei 1) = (drDv ν χf A s j x 1).1 :=
      dr_fderiv0 ν χf A s j x 1
    rw [e]
    have hc := kx_core (gradF ν χf A s) (C2 * gradW ν x j) (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|)
      (xj ν j x).1 x.2 (Ay ν χf A s 0 0) (Ay ν χf A s 0 2) (Ay ν χf A s 2 0) (Ay ν χf A s 2 2)
      (Ay ν χf A s 0 0) (Ay ν χf A s 0 2) (ei 1).1 (ei 1).2
      (hsG ν s j 1 x).1 (hsG ν s j 1 x).2 (hsG ν s j 0 x).1 (hsG ν s j 1 x).1
      (fderiv ℝ (hsG ν s j 0) x (ei 1)).1 (fderiv ℝ (hsG ν s j 1) x (ei 1)).1
      hG hK hB1 hx2 hBx (hent 0 0) (hent 0 2) (hent 2 0) (hent 2 2) (hent 0 0) (hent 0 2)
      (dr_ei_abs 1).1 (dr_ei_abs 1).2 (hp1.1) (hp1.2) (hGb 0).1 (hGb 1).1
      (hd1 0 1).1 (hd1 1 1).1
    unfold drDv
    simp only [merApply, Prod.fst_sub, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    calc _ ≤ 8 * gradF ν χf A s * (C2 * gradW ν x j) := hc
      _ = 8 * C2 * gradF ν χf A s * gradW ν x j := by ring
  · have e : fderiv ℝ (gradHpTm 1 ν χf A j s) x (ei 1) = (drDv ν χf A s j x 1).2 :=
      dr_fderiv1 ν χf A s j x 1
    rw [e]
    have hc := kx_core (gradF ν χf A s) (C2 * gradW ν x j) (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|)
      (xj ν j x).1 x.2 (Ay ν χf A s 0 0) (Ay ν χf A s 0 2) (Ay ν χf A s 2 0) (Ay ν χf A s 2 2)
      (Ay ν χf A s 2 0) (Ay ν χf A s 2 2) (ei 1).1 (ei 1).2
      (hsG ν s j 1 x).1 (hsG ν s j 1 x).2 (hsG ν s j 0 x).2 (hsG ν s j 1 x).2
      (fderiv ℝ (hsG ν s j 0) x (ei 1)).2 (fderiv ℝ (hsG ν s j 1) x (ei 1)).2
      hG hK hB1 hx2 hBx (hent 0 0) (hent 0 2) (hent 2 0) (hent 2 2) (hent 2 0) (hent 2 2)
      (dr_ei_abs 1).1 (dr_ei_abs 1).2 (hp1.1) (hp1.2) (hGb 0).2 (hGb 1).2
      (hd1 0 1).2 (hd1 1 1).2
    unfold drDv
    simp only [merApply, Prod.fst_sub, Prod.fst_add, Prod.smul_fst, Prod.snd_sub, Prod.snd_add,
      Prod.smul_snd, smul_eq_mul]
    calc _ ≤ 8 * gradF ν χf A s * (C2 * gradW ν x j) := hc
      _ = 8 * C2 * gradF ν χf A s * gradW ν x j := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
