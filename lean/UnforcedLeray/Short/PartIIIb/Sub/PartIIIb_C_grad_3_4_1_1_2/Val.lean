import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1_2.Vj

/-!
# `PartIII-b:C/grad/3/4/1/1/2/3`: value envelope of the lattice term of `h^p_A`

Source `the November 2 reference manuscript`
4963-4980 (`h^p_A`), 5036-5039, 5063-5079.

`hpATerm = merApply (Ay) (Vj) - fderiv Vj x (merApply (Ay) (x_j))`.  Each entry of `Ay` is at most
`frob (Ay) ≤ gradF`; the value `V_j` and the spatial derivatives `fderiv Vj x (e_a)` are bounded
by `gradVjBounds` (with the factor `1 + |x_j|` absorbing `|x_j|`).  Constant `C = 4 * C1`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Each entry of a matrix is at most its Frobenius norm. -/
lemma val_entry_le (A : Mat3) (a b : Fin 3) : |A a b| ≤ frob A := by
  unfold frob
  apply Real.abs_le_sqrt
  have h1 : A a b ^ 2 ≤ ∑ j, A a j ^ 2 :=
    Finset.single_le_sum (f := fun j => A a j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ b)
  have h2 : ∑ j, A a j ^ 2 ≤ ∑ i, ∑ j, A i j ^ 2 :=
    Finset.single_le_sum (f := fun i => ∑ j, A i j ^ 2)
      (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)) (Finset.mem_univ a)
  linarith

/-- Linearity of a continuous linear map on `ℝ × ℝ` in the basis `e_0, e_1`, first component. -/
lemma val_lin_fst (L : ℝ × ℝ →L[ℝ] ℝ × ℝ) (w : ℝ × ℝ) :
    (L w).1 = w.1 * (L (ei 0)).1 + w.2 * (L (ei 1)).1 := by
  have hw : w = w.1 • ei 0 + w.2 • ei 1 := by
    ext <;> simp [ei]
  have h : L w = w.1 • L (ei 0) + w.2 • L (ei 1) := by
    calc L w = L (w.1 • ei 0 + w.2 • ei 1) := by rw [← hw]
      _ = w.1 • L (ei 0) + w.2 • L (ei 1) := by rw [map_add, map_smul, map_smul]
  rw [h]
  simp [smul_eq_mul]

/-- Linearity of a continuous linear map on `ℝ × ℝ` in the basis `e_0, e_1`, second component. -/
lemma val_lin_snd (L : ℝ × ℝ →L[ℝ] ℝ × ℝ) (w : ℝ × ℝ) :
    (L w).2 = w.1 * (L (ei 0)).2 + w.2 * (L (ei 1)).2 := by
  have hw : w = w.1 • ei 0 + w.2 • ei 1 := by
    ext <;> simp [ei]
  have h : L w = w.1 • L (ei 0) + w.2 • L (ei 1) := by
    calc L w = L (w.1 • ei 0 + w.2 • ei 1) := by rw [← hw]
      _ = w.1 • L (ei 0) + w.2 • L (ei 1) := by rw [map_add, map_smul, map_smul]
  rw [h]
  simp [smul_eq_mul]

/-- The real estimate behind both components of the value envelope. -/
lemma val_core (G K B x1 x2 p0 p1 c0 c1 c2 c3 v1 v2 d1 d2 : ℝ)
    (hG : 0 ≤ G) (hK : 0 ≤ K) (hB : 1 ≤ B) (hBx : |x1| + |x2| ≤ B)
    (hp0 : |p0| ≤ G) (hp1 : |p1| ≤ G) (hc0 : |c0| ≤ G) (hc1 : |c1| ≤ G)
    (hc2 : |c2| ≤ G) (hc3 : |c3| ≤ G)
    (hv1 : B * |v1| ≤ K) (hv2 : B * |v2| ≤ K) (hd1 : B * |d1| ≤ K) (hd2 : B * |d2| ≤ K) :
    |p0 * v1 + p1 * v2 - ((c0 * x1 + c1 * x2) * d1 + (c2 * x1 + c3 * x2) * d2)| ≤ 4 * G * K := by
  have hV1 : |v1| ≤ K := le_trans (le_mul_of_one_le_left (abs_nonneg v1) hB) hv1
  have hV2 : |v2| ≤ K := le_trans (le_mul_of_one_le_left (abs_nonneg v2) hB) hv2
  have hw1 : |c0 * x1 + c1 * x2| ≤ G * B := by
    calc |c0 * x1 + c1 * x2| ≤ |c0 * x1| + |c1 * x2| := abs_add_le _ _
      _ = |c0| * |x1| + |c1| * |x2| := by rw [abs_mul, abs_mul]
      _ ≤ G * |x1| + G * |x2| :=
          add_le_add (mul_le_mul_of_nonneg_right hc0 (abs_nonneg _))
            (mul_le_mul_of_nonneg_right hc1 (abs_nonneg _))
      _ = G * (|x1| + |x2|) := by ring
      _ ≤ G * B := mul_le_mul_of_nonneg_left hBx hG
  have hw2 : |c2 * x1 + c3 * x2| ≤ G * B := by
    calc |c2 * x1 + c3 * x2| ≤ |c2 * x1| + |c3 * x2| := abs_add_le _ _
      _ = |c2| * |x1| + |c3| * |x2| := by rw [abs_mul, abs_mul]
      _ ≤ G * |x1| + G * |x2| :=
          add_le_add (mul_le_mul_of_nonneg_right hc2 (abs_nonneg _))
            (mul_le_mul_of_nonneg_right hc3 (abs_nonneg _))
      _ = G * (|x1| + |x2|) := by ring
      _ ≤ G * B := mul_le_mul_of_nonneg_left hBx hG
  have e1 : |p0 * v1| ≤ G * K := by
    rw [abs_mul]; exact mul_le_mul hp0 hV1 (abs_nonneg _) hG
  have e2 : |p1 * v2| ≤ G * K := by
    rw [abs_mul]; exact mul_le_mul hp1 hV2 (abs_nonneg _) hG
  have e3 : |(c0 * x1 + c1 * x2) * d1| ≤ G * K := by
    rw [abs_mul]
    calc |c0 * x1 + c1 * x2| * |d1| ≤ (G * B) * |d1| :=
          mul_le_mul_of_nonneg_right hw1 (abs_nonneg _)
      _ = G * (B * |d1|) := by ring
      _ ≤ G * K := mul_le_mul_of_nonneg_left hd1 hG
  have e4 : |(c2 * x1 + c3 * x2) * d2| ≤ G * K := by
    rw [abs_mul]
    calc |c2 * x1 + c3 * x2| * |d2| ≤ (G * B) * |d2| :=
          mul_le_mul_of_nonneg_right hw2 (abs_nonneg _)
      _ = G * (B * |d2|) := by ring
      _ ≤ G * K := mul_le_mul_of_nonneg_left hd2 hG
  obtain ⟨a1l, a1u⟩ := abs_le.mp e1
  obtain ⟨a2l, a2u⟩ := abs_le.mp e2
  obtain ⟨a3l, a3u⟩ := abs_le.mp e3
  obtain ⟨a4l, a4u⟩ := abs_le.mp e4
  have hfin : |p0 * v1 + p1 * v2 - ((c0 * x1 + c1 * x2) * d1 + (c2 * x1 + c3 * x2) * d2)|
      ≤ G * K + G * K + G * K + G * K := by
    rw [abs_le]; constructor <;> linarith
  calc _ ≤ G * K + G * K + G * K + G * K := hfin
    _ = 4 * G * K := by ring

theorem gradHpValEnv : GradHpValEnv := by
  obtain ⟨C1, hC1, hV⟩ := gradVjBounds
  refine ⟨4 * C1, by linarith, ?_⟩
  intro ν s χf A hd x i j
  obtain ⟨hν, hν1, hs, hs1, _⟩ := hd
  have hW : 0 ≤ gradW ν x j := gradW_nonneg ν x j
  have hG : 0 ≤ gradF ν χf A s := gradF_nonneg _ _ _ _
  obtain ⟨h1, h2, _⟩ := hV ν s j x hν hν1 hs hs1 0 0
  obtain ⟨_, h2', _⟩ := hV ν s j x hν hν1 hs hs1 1 0
  have hBx : |(xj ν j x).1| + |(xj ν j x).2| ≤ 1 + |(xj ν j x).1| + |(xj ν j x).2| := by
    linarith
  have hB : (1 : ℝ) ≤ 1 + |(xj ν j x).1| + |(xj ν j x).2| := by
    linarith [abs_nonneg (xj ν j x).1, abs_nonneg (xj ν j x).2]
  -- entries of `Ay`
  have hent : ∀ a b : Fin 3, |Ay ν χf A s a b| ≤ gradF ν χf A s := by
    intro a b
    have hfr : 0 ≤ frob (sDeriv (Ay ν χf A) s) := Real.sqrt_nonneg _
    have hfr2 : 0 ≤ frob (sDeriv (sDeriv (Ay ν χf A)) s) := Real.sqrt_nonneg _
    have := val_entry_le (Ay ν χf A s) a b
    unfold gradF
    linarith
  -- the linear decomposition of the first derivative
  have hcomp : ∀ (c : Fin 2), (gradHpTm 0 ν χf A j s x = 0) ∨ True := fun _ => Or.inr trivial
  clear hcomp
  set M := Ay ν χf A s with hM
  set B := 1 + |(xj ν j x).1| + |(xj ν j x).2| with hBdef
  set K := C1 * gradW ν x j with hKdef
  have hK : 0 ≤ K := mul_nonneg hC1 hW
  -- norms to components
  have hv1 : B * |(Vj ν s j x).1| ≤ K := by
    have := mul_le_mul_of_nonneg_left (norm_fst_le (Vj ν s j x)) (by linarith : (0:ℝ) ≤ B)
    exact this.trans h1
  have hv2 : B * |(Vj ν s j x).2| ≤ K := by
    have := mul_le_mul_of_nonneg_left (norm_snd_le (Vj ν s j x)) (by linarith : (0:ℝ) ≤ B)
    exact this.trans h1
  have hd0a : B * |(fderiv ℝ (Vj ν s j) x (ei 0)).1| ≤ K := by
    have := mul_le_mul_of_nonneg_left (norm_fst_le (fderiv ℝ (Vj ν s j) x (ei 0)))
      (by linarith : (0:ℝ) ≤ B)
    exact this.trans h2
  have hd0b : B * |(fderiv ℝ (Vj ν s j) x (ei 0)).2| ≤ K := by
    have := mul_le_mul_of_nonneg_left (norm_snd_le (fderiv ℝ (Vj ν s j) x (ei 0)))
      (by linarith : (0:ℝ) ≤ B)
    exact this.trans h2
  have hd1a : B * |(fderiv ℝ (Vj ν s j) x (ei 1)).1| ≤ K := by
    have := mul_le_mul_of_nonneg_left (norm_fst_le (fderiv ℝ (Vj ν s j) x (ei 1)))
      (by linarith : (0:ℝ) ≤ B)
    exact this.trans h2'
  have hd1b : B * |(fderiv ℝ (Vj ν s j) x (ei 1)).2| ≤ K := by
    have := mul_le_mul_of_nonneg_left (norm_snd_le (fderiv ℝ (Vj ν s j) x (ei 1)))
      (by linarith : (0:ℝ) ≤ B)
    exact this.trans h2'
  have eq0 : (hpATerm ν χf A s x j).1 =
      M 0 0 * (Vj ν s j x).1 + M 0 2 * (Vj ν s j x).2
        - ((M 0 0 * (xj ν j x).1 + M 0 2 * (xj ν j x).2) * (fderiv ℝ (Vj ν s j) x (ei 0)).1
          + (M 2 0 * (xj ν j x).1 + M 2 2 * (xj ν j x).2) * (fderiv ℝ (Vj ν s j) x (ei 1)).1) := by
    unfold hpATerm
    rw [Prod.fst_sub, val_lin_fst]
    simp only [merApply, hM]
  have eq1 : (hpATerm ν χf A s x j).2 =
      M 2 0 * (Vj ν s j x).1 + M 2 2 * (Vj ν s j x).2
        - ((M 0 0 * (xj ν j x).1 + M 0 2 * (xj ν j x).2) * (fderiv ℝ (Vj ν s j) x (ei 0)).2
          + (M 2 0 * (xj ν j x).1 + M 2 2 * (xj ν j x).2) * (fderiv ℝ (Vj ν s j) x (ei 1)).2) := by
    unfold hpATerm
    rw [Prod.snd_sub, val_lin_snd]
    simp only [merApply, hM]
  have key0 := val_core (gradF ν χf A s) K B (xj ν j x).1 (xj ν j x).2
    (M 0 0) (M 0 2) (M 0 0) (M 0 2) (M 2 0) (M 2 2) (Vj ν s j x).1 (Vj ν s j x).2
    (fderiv ℝ (Vj ν s j) x (ei 0)).1 (fderiv ℝ (Vj ν s j) x (ei 1)).1
    hG hK hB hBx (hent 0 0) (hent 0 2) (hent 0 0) (hent 0 2) (hent 2 0) (hent 2 2)
    hv1 hv2 hd0a hd1a
  have key1 := val_core (gradF ν χf A s) K B (xj ν j x).1 (xj ν j x).2
    (M 2 0) (M 2 2) (M 0 0) (M 0 2) (M 2 0) (M 2 2) (Vj ν s j x).1 (Vj ν s j x).2
    (fderiv ℝ (Vj ν s j) x (ei 0)).2 (fderiv ℝ (Vj ν s j) x (ei 1)).2
    hG hK hB hBx (hent 2 0) (hent 2 2) (hent 0 0) (hent 0 2) (hent 2 0) (hent 2 2)
    hv1 hv2 hd0b hd1b
  have hgoal : ∀ c : ℝ, c = 4 * gradF ν χf A s * K → c = 4 * C1 * gradF ν χf A s * gradW ν x j := by
    intro c hc; rw [hc, hKdef]; ring
  fin_cases i
  · show |(hpATerm ν χf A s x j).1| ≤ _
    rw [eq0]
    refine le_trans key0 (le_of_eq (hgoal _ rfl))
  · show |(hpATerm ν χf A s x j).2| ≤ _
    rw [eq1]
    refine le_trans key1 (le_of_eq (hgoal _ rfl))

end UnforcedLeray.Short.PartIIIb.Concrete
