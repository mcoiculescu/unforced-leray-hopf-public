import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1_2.Vj
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1_2

/-!
# `PartIII-b:C/grad/3/4/1/1/2/4`: `∂_q, ∂_η` envelope of the lattice term of `h^p_A`

Source `the November 2 reference manuscript`
4963-4980, 5036-5039, 5063-5079.

`dQ ψ s x = fderiv (ψ s) x (e_0)` and `dEta` uses `e_1` (`Concrete/AffineGradPin.lean`).  The
lattice term is `hpATerm = merApply (Ay) (V_j) - fderiv V_j x (merApply (Ay) (x_j))`; the
second term is rewritten through the explicit first derivative `hsG` (`hs_eq`), so the
directional derivative along `e_p` is an explicit expression in `hsG`, `fderiv hsG` and the
affine weight `merApply (Ay) (x_j)`.  The second derivative is bounded by `gradVjBounds`, the
affine weight `|x_j| ≤ B` absorbs the factor `x_j`, and the constant is `C = 8 * C1`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

lemma dr_line (x v : ℝ × ℝ) : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
  simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x

lemma dr_comp_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ × ℝ → E)
    (x v : ℝ × ℝ) (hf : DifferentiableAt ℝ f x) :
    HasDerivAt (fun t : ℝ => f (x + t • v)) (fderiv ℝ f x v) 0 :=
  hf.hasFDerivAt.comp_hasDerivAt_of_eq (0:ℝ) (dr_line x v) (by simp)

lemma dr_fst {g : ℝ → ℝ × ℝ} {g' : ℝ × ℝ} {t : ℝ} (hg : HasDerivAt g g' t) :
    HasDerivAt (fun u => (g u).1) g'.1 t :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hg

lemma dr_snd {g : ℝ → ℝ × ℝ} {g' : ℝ × ℝ} {t : ℝ} (hg : HasDerivAt g g' t) :
    HasDerivAt (fun u => (g u).2) g'.2 t :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hg

lemma dr_merApply (M : Mat3) {g : ℝ → ℝ × ℝ} {g' : ℝ × ℝ} {t : ℝ} (hg : HasDerivAt g g' t) :
    HasDerivAt (fun u => merApply M (g u)) (merApply M g') t := by
  have h1 := dr_fst hg
  have h2 := dr_snd hg
  exact ((h1.const_mul (M 0 0)).add (h2.const_mul (M 0 2))).prodMk
    ((h1.const_mul (M 2 0)).add (h2.const_mul (M 2 2)))

lemma dr_xj (ν : ℝ) (j : ℤ) (x v : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => xj ν j (x + t • v)) v 0 := by
  have e : (fun t : ℝ => xj ν j (x + t • v)) = fun t : ℝ => xj ν j x + t • v := by
    funext t
    ext <;> simp [xj] <;> ring
  rw [e]
  simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add (xj ν j x)

lemma dr_Vj_diff (ν s : ℝ) (j : ℤ) (y : ℝ × ℝ) : DifferentiableAt ℝ (Vj ν s j) y := by
  unfold Vj xj Jrot sq2
  fun_prop

lemma dr_lin_basis (L : ℝ × ℝ →L[ℝ] ℝ × ℝ) (w : ℝ × ℝ) :
    L w = w.1 • L (ei 0) + w.2 • L (ei 1) := by
  have hw : w = w.1 • ei 0 + w.2 • ei 1 := by
    ext <;> simp [ei]
  calc L w = L (w.1 • ei 0 + w.2 • ei 1) := by rw [← hw]
    _ = w.1 • L (ei 0) + w.2 • L (ei 1) := by rw [map_add, map_smul, map_smul]

lemma dr_ei_abs (a : Fin 2) : |(ei a).1| ≤ 1 ∧ |(ei a).2| ≤ 1 := by
  fin_cases a <;> simp [ei]

lemma dr_entry_le (A : Mat3) (a b : Fin 3) : |A a b| ≤ frob A := by
  unfold frob
  apply Real.abs_le_sqrt
  have h1 : A a b ^ 2 ≤ ∑ j, A a j ^ 2 :=
    Finset.single_le_sum (f := fun j => A a j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ b)
  have h2 : ∑ j, A a j ^ 2 ≤ ∑ i, ∑ j, A i j ^ 2 :=
    Finset.single_le_sum (f := fun i => ∑ j, A i j ^ 2)
      (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)) (Finset.mem_univ a)
  linarith

/-- The lattice term of `h^p_A` written through the explicit first derivative `hsG`. -/
def drPhi (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (j : ℤ) (y : ℝ × ℝ) : ℝ × ℝ :=
  merApply (Ay ν χ A s) (Vj ν s j y)
    - ((merApply (Ay ν χ A s) (xj ν j y)).1 • hsG ν s j 0 y
      + (merApply (Ay ν χ A s) (xj ν j y)).2 • hsG ν s j 1 y)

/-- Directional derivative of `drPhi` along `e_p` at `x`. -/
def drDv (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (j : ℤ) (x : ℝ × ℝ) (p : Fin 2) : ℝ × ℝ :=
  merApply (Ay ν χ A s) (hsG ν s j p x)
    - (((merApply (Ay ν χ A s) (xj ν j x)).1 • fderiv ℝ (hsG ν s j 0) x (ei p)
          + (merApply (Ay ν χ A s) (ei p)).1 • hsG ν s j 0 x)
        + ((merApply (Ay ν χ A s) (xj ν j x)).2 • fderiv ℝ (hsG ν s j 1) x (ei p)
          + (merApply (Ay ν χ A s) (ei p)).2 • hsG ν s j 1 x))

lemma dr_hpA_eq (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (j : ℤ) (y : ℝ × ℝ) :
    hpATerm ν χ A s y j = drPhi ν χ A s j y := by
  unfold hpATerm drPhi
  rw [dr_lin_basis (fderiv ℝ (Vj ν s j) y) (merApply (Ay ν χ A s) (xj ν j y))]
  simp only [hs_eq]

lemma dr_merApply_diff (M : Mat3) {g : ℝ × ℝ → ℝ × ℝ} {x : ℝ × ℝ}
    (hg : DifferentiableAt ℝ g x) : DifferentiableAt ℝ (fun y => merApply M (g y)) x := by
  have h1 : DifferentiableAt ℝ (fun y => (g y).1) x := hg.fst
  have h2 : DifferentiableAt ℝ (fun y => (g y).2) x := hg.snd
  unfold merApply
  exact ((h1.const_mul (M 0 0)).add (h2.const_mul (M 0 2))).prodMk
    ((h1.const_mul (M 2 0)).add (h2.const_mul (M 2 2)))

lemma dr_drPhi_diff (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (j : ℤ) (x : ℝ × ℝ) :
    DifferentiableAt ℝ (fun y => drPhi ν χ A s j y) x := by
  have hV : DifferentiableAt ℝ (fun y => Vj ν s j y) x := dr_Vj_diff ν s j x
  have hX : DifferentiableAt ℝ (fun y => xj ν j y) x := by
    unfold xj; fun_prop
  have hW : DifferentiableAt ℝ (fun y => merApply (Ay ν χ A s) (xj ν j y)) x :=
    dr_merApply_diff (Ay ν χ A s) hX
  have hW1 : DifferentiableAt ℝ (fun y => (merApply (Ay ν χ A s) (xj ν j y)).1) x := hW.fst
  have hW2 : DifferentiableAt ℝ (fun y => (merApply (Ay ν χ A s) (xj ν j y)).2) x := hW.snd
  have hA := dr_merApply_diff (Ay ν χ A s) hV
  exact hA.sub ((hW1.smul (hs_diff ν s j 0 x)).add (hW2.smul (hs_diff ν s j 1 x)))

lemma dr_drPhi_line (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (j : ℤ) (x : ℝ × ℝ) (p : Fin 2) :
    HasDerivAt (fun t : ℝ => drPhi ν χ A s j (x + t • ei p)) (drDv ν χ A s j x p) 0 := by
  have hVd := dr_comp_line (Vj ν s j) x (ei p) (dr_Vj_diff ν s j x)
  rw [hs_eq ν s j p x] at hVd
  have T1 := dr_merApply (Ay ν χ A s) hVd
  have hX := dr_merApply (Ay ν χ A s) (dr_xj (ν := ν) (j := j) x (ei p))
  have T2a := (dr_fst hX).smul (dr_comp_line (hsG ν s j 0) x (ei p) (hs_diff ν s j 0 x))
  have T2b := (dr_snd hX).smul (dr_comp_line (hsG ν s j 1) x (ei p) (hs_diff ν s j 1 x))
  have T := T1.sub (T2a.add T2b)
  unfold drPhi drDv
  exact T.congr_deriv (by simp only [zero_smul, add_zero])

lemma dr_fderiv0 (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (j : ℤ) (x : ℝ × ℝ) (p : Fin 2) :
    fderiv ℝ (gradHpTm 0 ν χ A j s) x (ei p) = (drDv ν χ A s j x p).1 := by
  have hfun : gradHpTm 0 ν χ A j s = fun y => (drPhi ν χ A s j y).1 := by
    funext y
    simp [gradHpTm, dr_hpA_eq]
  rw [hfun]
  have hd := (dr_drPhi_diff ν χ A s j x).fst
  have hl := dr_comp_line (fun y => (drPhi ν χ A s j y).1) x (ei p) hd
  have hr := dr_fst (dr_drPhi_line ν χ A s j x p)
  exact hl.unique hr

lemma dr_fderiv1 (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (j : ℤ) (x : ℝ × ℝ) (p : Fin 2) :
    fderiv ℝ (gradHpTm 1 ν χ A j s) x (ei p) = (drDv ν χ A s j x p).2 := by
  have hfun : gradHpTm 1 ν χ A j s = fun y => (drPhi ν χ A s j y).2 := by
    funext y
    simp [gradHpTm, dr_hpA_eq]
  rw [hfun]
  have hd := (dr_drPhi_diff ν χ A s j x).snd
  have hl := dr_comp_line (fun y => (drPhi ν χ A s j y).2) x (ei p) hd
  have hr := dr_snd (dr_drPhi_line ν χ A s j x p)
  exact hl.unique hr

/-- Real estimate: the two components of the directional derivative. -/
lemma dr_core (G K B x1 x2 m00 m02 m20 m22 r1 r2 e1 e2 p1 p2 h0 h1 d0 d1 : ℝ)
    (hG : 0 ≤ G) (hK : 0 ≤ K) (hB : 1 ≤ B) (hBx : |x1| + |x2| ≤ B)
    (hm00 : |m00| ≤ G) (hm02 : |m02| ≤ G) (hm20 : |m20| ≤ G) (hm22 : |m22| ≤ G)
    (hr1 : |r1| ≤ G) (hr2 : |r2| ≤ G) (he1 : |e1| ≤ 1) (he2 : |e2| ≤ 1)
    (hp1 : |p1| ≤ K) (hp2 : |p2| ≤ K) (hh0 : |h0| ≤ K) (hh1 : |h1| ≤ K)
    (hd0 : B * |d0| ≤ K) (hd1 : B * |d1| ≤ K) :
    |(r1 * p1 + r2 * p2) - (((m00 * x1 + m02 * x2) * d0 + (m00 * e1 + m02 * e2) * h0)
        + ((m20 * x1 + m22 * x2) * d1 + (m20 * e1 + m22 * e2) * h1))| ≤ 8 * G * K := by
  have hB0 : 0 ≤ B := by linarith
  have s0 : |r1 * p1 + r2 * p2| ≤ G * K + G * K :=
    (abs_add_le _ _).trans (add_le_add
      (by rw [abs_mul]; exact mul_le_mul hr1 hp1 (abs_nonneg _) hG)
      (by rw [abs_mul]; exact mul_le_mul hr2 hp2 (abs_nonneg _) hG))
  have s1 : |m00 * e1 + m02 * e2| ≤ G + G :=
    calc |m00 * e1 + m02 * e2| ≤ |m00 * e1| + |m02 * e2| := abs_add_le _ _
      _ = |m00| * |e1| + |m02| * |e2| := by rw [abs_mul, abs_mul]
      _ ≤ G * 1 + G * 1 := add_le_add (mul_le_mul hm00 he1 (abs_nonneg _) hG)
          (mul_le_mul hm02 he2 (abs_nonneg _) hG)
      _ = G + G := by ring
  have s2 : |m20 * e1 + m22 * e2| ≤ G + G :=
    calc |m20 * e1 + m22 * e2| ≤ |m20 * e1| + |m22 * e2| := abs_add_le _ _
      _ = |m20| * |e1| + |m22| * |e2| := by rw [abs_mul, abs_mul]
      _ ≤ G * 1 + G * 1 := add_le_add (mul_le_mul hm20 he1 (abs_nonneg _) hG)
          (mul_le_mul hm22 he2 (abs_nonneg _) hG)
      _ = G + G := by ring
  have s3 : |m00 * x1 + m02 * x2| ≤ G * B :=
    calc |m00 * x1 + m02 * x2| ≤ |m00 * x1| + |m02 * x2| := abs_add_le _ _
      _ = |m00| * |x1| + |m02| * |x2| := by rw [abs_mul, abs_mul]
      _ ≤ G * |x1| + G * |x2| := add_le_add (mul_le_mul_of_nonneg_right hm00 (abs_nonneg _))
          (mul_le_mul_of_nonneg_right hm02 (abs_nonneg _))
      _ = G * (|x1| + |x2|) := by ring
      _ ≤ G * B := mul_le_mul_of_nonneg_left hBx hG
  have s4 : |m20 * x1 + m22 * x2| ≤ G * B :=
    calc |m20 * x1 + m22 * x2| ≤ |m20 * x1| + |m22 * x2| := abs_add_le _ _
      _ = |m20| * |x1| + |m22| * |x2| := by rw [abs_mul, abs_mul]
      _ ≤ G * |x1| + G * |x2| := add_le_add (mul_le_mul_of_nonneg_right hm20 (abs_nonneg _))
          (mul_le_mul_of_nonneg_right hm22 (abs_nonneg _))
      _ = G * (|x1| + |x2|) := by ring
      _ ≤ G * B := mul_le_mul_of_nonneg_left hBx hG
  have t2a : |(m00 * e1 + m02 * e2) * h0| ≤ (G + G) * K := by
    rw [abs_mul]; exact mul_le_mul s1 hh0 (abs_nonneg _) (by linarith)
  have t2b : |(m20 * e1 + m22 * e2) * h1| ≤ (G + G) * K := by
    rw [abs_mul]; exact mul_le_mul s2 hh1 (abs_nonneg _) (by linarith)
  have t3a : |(m00 * x1 + m02 * x2) * d0| ≤ G * K := by
    rw [abs_mul]
    calc |m00 * x1 + m02 * x2| * |d0| ≤ (G * B) * |d0| :=
          mul_le_mul_of_nonneg_right s3 (abs_nonneg _)
      _ = G * (B * |d0|) := by ring
      _ ≤ G * K := mul_le_mul_of_nonneg_left hd0 hG
  have t3b : |(m20 * x1 + m22 * x2) * d1| ≤ G * K := by
    rw [abs_mul]
    calc |m20 * x1 + m22 * x2| * |d1| ≤ (G * B) * |d1| :=
          mul_le_mul_of_nonneg_right s4 (abs_nonneg _)
      _ = G * (B * |d1|) := by ring
      _ ≤ G * K := mul_le_mul_of_nonneg_left hd1 hG
  have hsum : |(r1 * p1 + r2 * p2) - (((m00 * x1 + m02 * x2) * d0 + (m00 * e1 + m02 * e2) * h0)
        + ((m20 * x1 + m22 * x2) * d1 + (m20 * e1 + m22 * e2) * h1))|
      ≤ (G * K + G * K) + ((G + G) * K + G * K) + ((G + G) * K + G * K) := by
    obtain ⟨a1, a2⟩ := abs_le.mp s0
    obtain ⟨b1, b2⟩ := abs_le.mp t2a
    obtain ⟨c1, c2⟩ := abs_le.mp t3a
    obtain ⟨d1', d2⟩ := abs_le.mp t2b
    obtain ⟨e1', e2'⟩ := abs_le.mp t3b
    rw [abs_le]
    constructor <;> linarith
  calc _ ≤ (G * K + G * K) + ((G + G) * K + G * K) + ((G + G) * K + G * K) := hsum
    _ = 8 * G * K := by ring

lemma dr_bound (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (j : ℤ) (x : ℝ × ℝ) (p : Fin 2)
    (K : ℝ) (hK : 0 ≤ K)
    (h2 : ∀ b : Fin 2, (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) * ‖fderiv ℝ (Vj ν s j) x (ei b)‖ ≤ K)
    (h3 : ∀ b : Fin 2, (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|)
        * ‖fderiv ℝ (fun y => fderiv ℝ (Vj ν s j) y (ei b)) x (ei p)‖ ≤ K) :
    |(drDv ν χ A s j x p).1| ≤ 8 * gradF ν χ A s * K ∧
      |(drDv ν χ A s j x p).2| ≤ 8 * gradF ν χ A s * K := by
  have hB1 : (1 : ℝ) ≤ 1 + |x.1 - (j : ℝ) * cOf ν| + |x.2| := by
    linarith [abs_nonneg (x.1 - (j : ℝ) * cOf ν), abs_nonneg x.2]
  have hB0 : (0 : ℝ) ≤ 1 + |x.1 - (j : ℝ) * cOf ν| + |x.2| := by linarith
  have hBx : |(xj ν j x).1| + |(xj ν j x).2| ≤ 1 + |x.1 - (j : ℝ) * cOf ν| + |x.2| := by
    show |x.1 - (j : ℝ) * cOf ν| + |x.2| ≤ _
    linarith
  have hG : 0 ≤ gradF ν χ A s := gradF_nonneg _ _ _ _
  have hent : ∀ a b : Fin 3, |Ay ν χ A s a b| ≤ gradF ν χ A s := by
    intro a b
    have hfr : 0 ≤ frob (sDeriv (Ay ν χ A) s) := Real.sqrt_nonneg _
    have hfr2 : 0 ≤ frob (sDeriv (sDeriv (Ay ν χ A)) s) := Real.sqrt_nonneg _
    have := dr_entry_le (Ay ν χ A s) a b
    unfold gradF
    linarith
  have hv1 : ∀ b : Fin 2, |(hsG ν s j b x).1| ≤ K := fun b => by
    have h := h2 b
    rw [hs_eq ν s j b x] at h
    have hn : ‖hsG ν s j b x‖ ≤ K := (le_mul_of_one_le_left (norm_nonneg _) hB1).trans h
    exact (norm_fst_le _).trans hn
  have hv2 : ∀ b : Fin 2, |(hsG ν s j b x).2| ≤ K := fun b => by
    have h := h2 b
    rw [hs_eq ν s j b x] at h
    have hn : ‖hsG ν s j b x‖ ≤ K := (le_mul_of_one_le_left (norm_nonneg _) hB1).trans h
    exact (norm_snd_le _).trans hn
  have hd1 : ∀ b : Fin 2, (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) * |(fderiv ℝ (hsG ν s j b) x (ei p)).1| ≤ K := fun b => by
    have e : hsG ν s j b = fun y => fderiv ℝ (Vj ν s j) y (ei b) :=
      funext fun y => (hs_eq ν s j b y).symm
    rw [e]
    exact (mul_le_mul_of_nonneg_left (norm_fst_le _) hB0).trans (h3 b)
  have hd2 : ∀ b : Fin 2, (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) * |(fderiv ℝ (hsG ν s j b) x (ei p)).2| ≤ K := fun b => by
    have e : hsG ν s j b = fun y => fderiv ℝ (Vj ν s j) y (ei b) :=
      funext fun y => (hs_eq ν s j b y).symm
    rw [e]
    exact (mul_le_mul_of_nonneg_left (norm_snd_le _) hB0).trans (h3 b)
  constructor
  · have hc := dr_core (gradF ν χ A s) K (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|)
      (xj ν j x).1 (xj ν j x).2 (Ay ν χ A s 0 0) (Ay ν χ A s 0 2) (Ay ν χ A s 2 0)
      (Ay ν χ A s 2 2) (Ay ν χ A s 0 0) (Ay ν χ A s 0 2) (ei p).1 (ei p).2
      (hsG ν s j p x).1 (hsG ν s j p x).2 (hsG ν s j 0 x).1 (hsG ν s j 1 x).1
      (fderiv ℝ (hsG ν s j 0) x (ei p)).1 (fderiv ℝ (hsG ν s j 1) x (ei p)).1
      hG hK hB1 hBx (hent 0 0) (hent 0 2) (hent 2 0) (hent 2 2) (hent 0 0) (hent 0 2)
      (dr_ei_abs p).1 (dr_ei_abs p).2 (hv1 p) (hv2 p) (hv1 0) (hv1 1)
      (hd1 0) (hd1 1)
    unfold drDv
    simp only [merApply, Prod.fst_sub, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    calc _ ≤ 8 * gradF ν χ A s * K := hc
      _ = 8 * gradF ν χ A s * K := rfl
  · have hc := dr_core (gradF ν χ A s) K (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|)
      (xj ν j x).1 (xj ν j x).2 (Ay ν χ A s 0 0) (Ay ν χ A s 0 2) (Ay ν χ A s 2 0)
      (Ay ν χ A s 2 2) (Ay ν χ A s 2 0) (Ay ν χ A s 2 2) (ei p).1 (ei p).2
      (hsG ν s j p x).1 (hsG ν s j p x).2 (hsG ν s j 0 x).2 (hsG ν s j 1 x).2
      (fderiv ℝ (hsG ν s j 0) x (ei p)).2 (fderiv ℝ (hsG ν s j 1) x (ei p)).2
      hG hK hB1 hBx (hent 0 0) (hent 0 2) (hent 2 0) (hent 2 2) (hent 2 0) (hent 2 2)
      (dr_ei_abs p).1 (dr_ei_abs p).2 (hv1 p) (hv2 p) (hv2 0) (hv2 1)
      (hd2 0) (hd2 1)
    unfold drDv
    simp only [merApply, Prod.fst_sub, Prod.fst_add, Prod.smul_fst, Prod.snd_sub, Prod.snd_add,
      Prod.smul_snd, smul_eq_mul]
    exact hc

/-- `∂_q, ∂_η` envelope of the lattice term of `h^p_A` (source 4973, 5063-5079). -/
theorem gradHpDerEnv : GradHpDerEnv := by
  obtain ⟨C1, hC1, hV⟩ := gradVjBounds
  refine ⟨8 * C1, by linarith, ?_⟩
  intro ν s χf A hd x i j
  obtain ⟨hν, hν1, hs, hs1, _⟩ := hd
  have hW : 0 ≤ gradW ν x j := gradW_nonneg ν x j
  have hK : 0 ≤ C1 * gradW ν x j := mul_nonneg hC1 hW
  have key : ∀ p : Fin 2,
      |(drDv ν χf A s j x p).1| ≤ 8 * gradF ν χf A s * (C1 * gradW ν x j) ∧
      |(drDv ν χf A s j x p).2| ≤ 8 * gradF ν χf A s * (C1 * gradW ν x j) := fun p =>
    dr_bound ν χf A s j x p (C1 * gradW ν x j) hK
      (fun b => (hV ν s j x hν hν1 hs hs1 b p).2.1)
      (fun b => (hV ν s j x hν hν1 hs hs1 b p).2.2)
  have hrw : 8 * gradF ν χf A s * (C1 * gradW ν x j)
      = 8 * C1 * gradF ν χf A s * gradW ν x j := by ring
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  rcases hi with rfl | rfl
  · refine ⟨?_, ?_⟩
    · have e : dQ (gradHpTm 0 ν χf A j) s x = (drDv ν χf A s j x 0).1 :=
        dr_fderiv0 ν χf A s j x 0
      rw [e]
      exact (key 0).1.trans (le_of_eq hrw)
    · have e : dEta (gradHpTm 0 ν χf A j) s x = (drDv ν χf A s j x 1).1 :=
        dr_fderiv0 ν χf A s j x 1
      rw [e]
      exact (key 1).1.trans (le_of_eq hrw)
  · refine ⟨?_, ?_⟩
    · have e : dQ (gradHpTm 1 ν χf A j) s x = (drDv ν χf A s j x 0).2 :=
        dr_fderiv1 ν χf A s j x 0
      rw [e]
      exact (key 0).2.trans (le_of_eq hrw)
    · have e : dEta (gradHpTm 1 ν χf A j) s x = (drDv ν χf A s j x 1).2 :=
        dr_fderiv1 ν χf A s j x 1
      rw [e]
      exact (key 1).2.trans (le_of_eq hrw)

end UnforcedLeray.Short.PartIIIb.Concrete
