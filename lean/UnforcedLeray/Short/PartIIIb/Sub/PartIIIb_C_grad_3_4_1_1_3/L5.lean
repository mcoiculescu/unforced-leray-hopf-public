import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1_3.L3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1_3.L4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1_2.Der
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1.Decomp

/-!
# `PartIII-b:C/grad/3/4/1/1/3/5`: s-derivative bound of the lattice term `h^p_A`

Source `the November 2 reference manuscript`
4963-4980, 5036-5039, 5063-5079.

For `ν s ≤ 23/20`, the `j`-th lattice term `hpATerm = merApply (Ay) (V_j) - fderiv V_j x (merApply (Ay) (x_j))`
is differentiable in `s` at every `t` where `Ay` is, and
`t * |∂_s (hpATerm)| ≤ C * (frob (Ay t) + t * frob (∂_s Ay t)) * gradW`.
The derivative is computed componentwise from the product rule; the two `x`-derivative factors
`V_j`, `fderiv V_j x (e_a)` and their `s`-derivatives are controlled by `gradVjBounds_ext` and
`gradVjSBounds_ext` (`L3.lean`, `L4.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

lemma gh5_comp_le (v : ℝ × ℝ) : |v.1| ≤ ‖v‖ ∧ |v.2| ≤ ‖v‖ := by
  refine ⟨?_, ?_⟩
  · have h := norm_fst_le v
    rwa [Real.norm_eq_abs] at h
  · have h := norm_snd_le v
    rwa [Real.norm_eq_abs] at h

lemma gh5_l1_le (v : ℝ × ℝ) : |v.1| + |v.2| ≤ 2 * ‖v‖ := by
  obtain ⟨h1, h2⟩ := gh5_comp_le v
  linarith

lemma gh5_mer_le (N : Mat3) (v : ℝ × ℝ) :
    |(merApply N v).1| ≤ frob N * (|v.1| + |v.2|) ∧
      |(merApply N v).2| ≤ frob N * (|v.1| + |v.2|) := by
  have a00 := dr_entry_le N 0 0
  have a02 := dr_entry_le N 0 2
  have a20 := dr_entry_le N 2 0
  have a22 := dr_entry_le N 2 2
  refine ⟨?_, ?_⟩
  · show |N 0 0 * v.1 + N 0 2 * v.2| ≤ _
    calc |N 0 0 * v.1 + N 0 2 * v.2| ≤ |N 0 0 * v.1| + |N 0 2 * v.2| := abs_add_le _ _
      _ = |N 0 0| * |v.1| + |N 0 2| * |v.2| := by rw [abs_mul, abs_mul]
      _ ≤ frob N * |v.1| + frob N * |v.2| :=
          add_le_add (mul_le_mul_of_nonneg_right a00 (abs_nonneg _))
            (mul_le_mul_of_nonneg_right a02 (abs_nonneg _))
      _ = frob N * (|v.1| + |v.2|) := by ring
  · show |N 2 0 * v.1 + N 2 2 * v.2| ≤ _
    calc |N 2 0 * v.1 + N 2 2 * v.2| ≤ |N 2 0 * v.1| + |N 2 2 * v.2| := abs_add_le _ _
      _ = |N 2 0| * |v.1| + |N 2 2| * |v.2| := by rw [abs_mul, abs_mul]
      _ ≤ frob N * |v.1| + frob N * |v.2| :=
          add_le_add (mul_le_mul_of_nonneg_right a20 (abs_nonneg _))
            (mul_le_mul_of_nonneg_right a22 (abs_nonneg _))
      _ = frob N * (|v.1| + |v.2|) := by ring

lemma gh5_mulb {p q r s : ℝ} (hp : |p| ≤ r) (hq : |q| ≤ s) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    |p * q| ≤ r * s := by
  rw [abs_mul]
  exact mul_le_mul hp hq (abs_nonneg _) hr

lemma gh5_tri (a b c d e f : ℝ) :
    |a + b - ((c + d) + (e + f))| ≤ |a| + |b| + (|c| + |d|) + (|e| + |f|) := by
  rw [abs_le]
  constructor <;>
    linarith [neg_abs_le a, neg_abs_le b, neg_abs_le c, neg_abs_le d, neg_abs_le e, neg_abs_le f,
      le_abs_self a, le_abs_self b, le_abs_self c, le_abs_self d, le_abs_self e, le_abs_self f,
      neg_le_abs a, neg_le_abs b, neg_le_abs c, neg_le_abs d, neg_le_abs e, neg_le_abs f]

/-- Product rule for `s ↦ merApply (M s) (g s)`. -/
lemma gh5_mer2 {M : ℝ → Mat3} {M' : Mat3} {g : ℝ → ℝ × ℝ} {g' : ℝ × ℝ} {t : ℝ}
    (hM : HasDerivAt M M' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun u => merApply (M u) (g u)) (merApply M' (g t) + merApply (M t) g') t := by
  have e : ∀ a b : Fin 3, HasDerivAt (fun u => M u a b) (M' a b) t :=
    fun a b => hasDerivAt_pi.1 (hasDerivAt_pi.1 hM a) b
  have h1 := dr_fst hg
  have h2 := dr_snd hg
  have k1 := ((e 0 0).mul h1).add ((e 0 2).mul h2)
  have k2 := ((e 2 0).mul h1).add ((e 2 2).mul h2)
  refine (k1.prodMk k2).congr_deriv ?_
  ext <;> simp [merApply] <;> ring

/-- Arithmetic closing the bound for one component of the derivative. -/
lemma gh5_fin (t K W C1 C2 fM fMd B nV nVd g0 g1 h0 h1 a b c d e f X : ℝ)
    (ht : 0 ≤ t) (hW : 0 ≤ W) (hfM : 0 ≤ fM) (hfMd : 0 ≤ fMd) (hB1 : 1 ≤ B)
    (hK1 : 4 * C1 ≤ K) (hK2 : 4 * C2 ≤ K) (hnV0 : 0 ≤ nV) (hnVd0 : 0 ≤ nVd)
    (hV : B * nV ≤ C1 * W) (hVd : B * (t * nVd) ≤ C2 * W)
    (hG0 : B * g0 ≤ C1 * W) (hG1 : B * g1 ≤ C1 * W)
    (hH0 : B * (t * h0) ≤ C2 * W) (hH1 : B * (t * h1) ≤ C2 * W)
    (ha : |a| ≤ fMd * (2 * nV)) (hb : |b| ≤ fM * (2 * nVd))
    (hc : |c| ≤ fM * B * h0) (hd : |d| ≤ fMd * B * g0)
    (he : |e| ≤ fM * B * h1) (hf : |f| ≤ fMd * B * g1)
    (hX : |X| ≤ |a| + |b| + (|c| + |d|) + (|e| + |f|)) :
    t * |X| ≤ K * (fM + t * fMd) * W := by
  have hnV : nV ≤ C1 * W := (le_mul_of_one_le_left hnV0 hB1).trans hV
  have hnVd : t * nVd ≤ C2 * W := (le_mul_of_one_le_left (mul_nonneg ht hnVd0) hB1).trans hVd
  have hG0' : t * (fMd * (B * g0)) ≤ t * (fMd * (C1 * W)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hG0 hfMd) ht
  have hG1' : t * (fMd * (B * g1)) ≤ t * (fMd * (C1 * W)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hG1 hfMd) ht
  have hH0' : fM * (B * (t * h0)) ≤ fM * (C2 * W) := mul_le_mul_of_nonneg_left hH0 hfM
  have hH1' : fM * (B * (t * h1)) ≤ fM * (C2 * W) := mul_le_mul_of_nonneg_left hH1 hfM
  have hnV' : t * (fMd * nV) ≤ t * (fMd * (C1 * W)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnV hfMd) ht
  have hnVd' : fM * (t * nVd) ≤ fM * (C2 * W) := mul_le_mul_of_nonneg_left hnVd hfM
  have hA : t * |a| ≤ t * (fMd * (2 * nV)) := mul_le_mul_of_nonneg_left ha ht
  have hB' : t * |b| ≤ t * (fM * (2 * nVd)) := mul_le_mul_of_nonneg_left hb ht
  have hC : t * |c| ≤ t * (fM * B * h0) := mul_le_mul_of_nonneg_left hc ht
  have hD : t * |d| ≤ t * (fMd * B * g0) := mul_le_mul_of_nonneg_left hd ht
  have hE : t * |e| ≤ t * (fM * B * h1) := mul_le_mul_of_nonneg_left he ht
  have hF : t * |f| ≤ t * (fMd * B * g1) := mul_le_mul_of_nonneg_left hf ht
  have hT : t * |X| ≤ t * (|a| + |b| + (|c| + |d|) + (|e| + |f|)) :=
    mul_le_mul_of_nonneg_left hX ht
  have g1' : 0 ≤ (K - 4 * C2) * (fM * W) := mul_nonneg (by linarith) (mul_nonneg hfM hW)
  have g2' : 0 ≤ (K - 4 * C1) * (t * fMd * W) :=
    mul_nonneg (by linarith) (mul_nonneg (mul_nonneg ht hfMd) hW)
  linarith

/-- The derivative of the lattice term `hpATerm` in `s`, with the componentwise bound. -/
lemma gh5_core (ν t : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (j : ℤ) (x : ℝ × ℝ) (B W C1 C2 K : ℝ)
    (hB1 : 1 ≤ B) (hBx : |(xj ν j x).1| + |(xj ν j x).2| ≤ B) (ht : 0 ≤ t) (hW : 0 ≤ W)
    (hK1 : 4 * C1 ≤ K) (hK2 : 4 * C2 ≤ K)
    (hVb : B * ‖Vj ν t j x‖ ≤ C1 * W)
    (hGb : ∀ a : Fin 2, B * ‖fderiv ℝ (Vj ν t j) x (ei a)‖ ≤ C1 * W)
    (hVd : B * (t * ‖deriv (fun s => Vj ν s j x) t‖) ≤ C2 * W)
    (hGd : ∀ a : Fin 2, B * (t * ‖deriv (fun s => fderiv ℝ (Vj ν s j) x (ei a)) t‖) ≤ C2 * W)
    (hVdiff : HasDerivAt (fun s => Vj ν s j x) (deriv (fun s => Vj ν s j x) t) t)
    (hGdiff : ∀ a : Fin 2, HasDerivAt (fun s => fderiv ℝ (Vj ν s j) x (ei a))
      (deriv (fun s => fderiv ℝ (Vj ν s j) x (ei a)) t) t)
    (hMd : HasDerivAt (Ay ν χf A) (deriv (Ay ν χf A) t) t) :
    ∃ Fd : ℝ × ℝ, HasDerivAt (fun s => hpATerm ν χf A s x j) Fd t ∧
      t * |Fd.1| ≤ K * (frob (Ay ν χf A t) + t * frob (deriv (Ay ν χf A) t)) * W ∧
      t * |Fd.2| ≤ K * (frob (Ay ν χf A t) + t * frob (deriv (Ay ν χf A) t)) * W := by
  have hfun : (fun s => hpATerm ν χf A s x j) = fun s => merApply (Ay ν χf A s) (Vj ν s j x) -
      ((merApply (Ay ν χf A s) (xj ν j x)).1 • fderiv ℝ (Vj ν s j) x (ei 0) +
        (merApply (Ay ν χf A s) (xj ν j x)).2 • fderiv ℝ (Vj ν s j) x (ei 1)) := by
    funext s
    unfold hpATerm
    rw [dr_lin_basis (fderiv ℝ (Vj ν s j) x) (merApply (Ay ν χf A s) (xj ν j x))]
  have hP1 := gh5_mer2 hMd hVdiff
  have hc : HasDerivAt (fun s => merApply (Ay ν χf A s) (xj ν j x))
      (merApply (deriv (Ay ν χf A) t) (xj ν j x)) t :=
    (gh5_mer2 hMd (hasDerivAt_const t (xj ν j x))).congr_deriv (by ext <;> simp [merApply])
  have hc0 := dr_fst hc
  have hc1 := dr_snd hc
  have hFull := hP1.sub ((hc0.smul (hGdiff 0)).add (hc1.smul (hGdiff 1)))
  have hfM : 0 ≤ frob (Ay ν χf A t) := Real.sqrt_nonneg _
  have hfMd : 0 ≤ frob (deriv (Ay ν χf A) t) := Real.sqrt_nonneg _
  have hB0 : 0 ≤ B := by linarith
  have bM1 : |(merApply (Ay ν χf A t) (xj ν j x)).1| ≤ frob (Ay ν χf A t) * B :=
    (gh5_mer_le (Ay ν χf A t) (xj ν j x)).1.trans (mul_le_mul_of_nonneg_left hBx hfM)
  have bM2 : |(merApply (Ay ν χf A t) (xj ν j x)).2| ≤ frob (Ay ν χf A t) * B :=
    (gh5_mer_le (Ay ν χf A t) (xj ν j x)).2.trans (mul_le_mul_of_nonneg_left hBx hfM)
  have bD1 : |(merApply (deriv (Ay ν χf A) t) (xj ν j x)).1| ≤
      frob (deriv (Ay ν χf A) t) * B :=
    (gh5_mer_le (deriv (Ay ν χf A) t) (xj ν j x)).1.trans (mul_le_mul_of_nonneg_left hBx hfMd)
  have bD2 : |(merApply (deriv (Ay ν χf A) t) (xj ν j x)).2| ≤
      frob (deriv (Ay ν χf A) t) * B :=
    (gh5_mer_le (deriv (Ay ν χf A) t) (xj ν j x)).2.trans (mul_le_mul_of_nonneg_left hBx hfMd)
  have ha1 : |(merApply (deriv (Ay ν χf A) t) (Vj ν t j x)).1| ≤
      frob (deriv (Ay ν χf A) t) * (2 * ‖Vj ν t j x‖) :=
    (gh5_mer_le (deriv (Ay ν χf A) t) (Vj ν t j x)).1.trans
      (mul_le_mul_of_nonneg_left (gh5_l1_le (Vj ν t j x)) hfMd)
  have ha2 : |(merApply (deriv (Ay ν χf A) t) (Vj ν t j x)).2| ≤
      frob (deriv (Ay ν χf A) t) * (2 * ‖Vj ν t j x‖) :=
    (gh5_mer_le (deriv (Ay ν χf A) t) (Vj ν t j x)).2.trans
      (mul_le_mul_of_nonneg_left (gh5_l1_le (Vj ν t j x)) hfMd)
  have hb1 : |(merApply (Ay ν χf A t) (deriv (fun s => Vj ν s j x) t)).1| ≤
      frob (Ay ν χf A t) * (2 * ‖deriv (fun s => Vj ν s j x) t‖) :=
    (gh5_mer_le (Ay ν χf A t) (deriv (fun s => Vj ν s j x) t)).1.trans
      (mul_le_mul_of_nonneg_left (gh5_l1_le (deriv (fun s => Vj ν s j x) t)) hfM)
  have hb2 : |(merApply (Ay ν χf A t) (deriv (fun s => Vj ν s j x) t)).2| ≤
      frob (Ay ν χf A t) * (2 * ‖deriv (fun s => Vj ν s j x) t‖) :=
    (gh5_mer_le (Ay ν χf A t) (deriv (fun s => Vj ν s j x) t)).2.trans
      (mul_le_mul_of_nonneg_left (gh5_l1_le (deriv (fun s => Vj ν s j x) t)) hfM)
  have hc1' := gh5_mulb bM1
    (gh5_comp_le (deriv (fun s => fderiv ℝ (Vj ν s j) x (ei 0)) t)).1
    (mul_nonneg hfM hB0) (norm_nonneg _)
  have hc2' := gh5_mulb bM1
    (gh5_comp_le (deriv (fun s => fderiv ℝ (Vj ν s j) x (ei 0)) t)).2
    (mul_nonneg hfM hB0) (norm_nonneg _)
  have hd1' := gh5_mulb bD1
    (gh5_comp_le (fderiv ℝ (Vj ν t j) x (ei 0))).1
    (mul_nonneg hfMd hB0) (norm_nonneg _)
  have hd2' := gh5_mulb bD1
    (gh5_comp_le (fderiv ℝ (Vj ν t j) x (ei 0))).2
    (mul_nonneg hfMd hB0) (norm_nonneg _)
  have he1' := gh5_mulb bM2
    (gh5_comp_le (deriv (fun s => fderiv ℝ (Vj ν s j) x (ei 1)) t)).1
    (mul_nonneg hfM hB0) (norm_nonneg _)
  have he2' := gh5_mulb bM2
    (gh5_comp_le (deriv (fun s => fderiv ℝ (Vj ν s j) x (ei 1)) t)).2
    (mul_nonneg hfM hB0) (norm_nonneg _)
  have hf1' := gh5_mulb bD2
    (gh5_comp_le (fderiv ℝ (Vj ν t j) x (ei 1))).1
    (mul_nonneg hfMd hB0) (norm_nonneg _)
  have hf2' := gh5_mulb bD2
    (gh5_comp_le (fderiv ℝ (Vj ν t j) x (ei 1))).2
    (mul_nonneg hfMd hB0) (norm_nonneg _)
  rw [hfun]
  refine ⟨_, hFull, ?_, ?_⟩
  · refine gh5_fin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ht hW hfM hfMd hB1 hK1 hK2
      (norm_nonneg _) (norm_nonneg _) hVb hVd (hGb 0) (hGb 1) (hGd 0) (hGd 1)
      ha1 hb1 hc1' hd1' he1' hf1' ?_
    simp only [Prod.fst_sub, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    exact gh5_tri _ _ _ _ _ _
  · refine gh5_fin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ht hW hfM hfMd hB1 hK1 hK2
      (norm_nonneg _) (norm_nonneg _) hVb hVd (hGb 0) (hGb 1) (hGd 0) (hGd 1)
      ha2 hb2 hc2' hd2' he2' hf2' ?_
    simp only [Prod.snd_sub, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    exact gh5_tri _ _ _ _ _ _

/-- `s`-derivative bound of the `j`-th lattice term of `h^p_A` for `ν s ≤ 23/20`
(source 4963-4980, 5036-5039, 5063-5079). -/
theorem gradHpTm_sDeriv : ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν t : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (j : ℤ)
    (x : ℝ × ℝ) (i : Fin 2), 0 < ν → ν ≤ 1 → 0 < t → t ≤ (23 / 20) / ν →
    DifferentiableAt ℝ (Ay ν χf A) t →
    DifferentiableAt ℝ (fun t' => gradHpTm i ν χf A j t' x) t ∧
      t * ‖deriv (fun t' => gradHpTm i ν χf A j t' x) t‖ ≤
        C * (frob (Ay ν χf A t) + t * frob (deriv (Ay ν χf A) t)) * gradW ν x j := by
  obtain ⟨C1, hC1, hV1⟩ := gradVjBounds_ext
  obtain ⟨C2, hC2, hS2⟩ := gradVjSBounds_ext
  refine ⟨4 * (C1 + C2), by linarith, ?_⟩
  intro ν t χf A j x i hν hν1 ht htb hAd
  have hW : 0 ≤ gradW ν x j := gradW_nonneg ν x j
  have hB1 : (1 : ℝ) ≤ 1 + |x.1 - (j : ℝ) * cOf ν| + |x.2| := by
    linarith [abs_nonneg (x.1 - (j : ℝ) * cOf ν), abs_nonneg x.2]
  have hBx : |(xj ν j x).1| + |(xj ν j x).2| ≤ 1 + |x.1 - (j : ℝ) * cOf ν| + |x.2| := by
    show |x.1 - (j : ℝ) * cOf ν| + |x.2| ≤ _
    linarith
  have hS0 := hS2 ν t j x hν hν1 ht htb 0
  have hV0 := hV1 ν t j x hν hν1 ht htb 0 0
  have hVdiff : HasDerivAt (fun s => Vj ν s j x) (deriv (fun s => Vj ν s j x) t) t :=
    (hS0.1 t ht).hasDerivAt
  have hGdiff : ∀ a : Fin 2, HasDerivAt (fun s => fderiv ℝ (Vj ν s j) x (ei a))
      (deriv (fun s => fderiv ℝ (Vj ν s j) x (ei a)) t) t := fun a =>
    ((hS2 ν t j x hν hν1 ht htb a).2.1 t ht).hasDerivAt
  have hMd : HasDerivAt (Ay ν χf A) (deriv (Ay ν χf A) t) t := hAd.hasDerivAt
  obtain ⟨Fd, hF, b1, b2⟩ := gh5_core ν t χf A j x (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|)
    (gradW ν x j) C1 C2 (4 * (C1 + C2)) hB1 hBx ht.le hW (by linarith) (by linarith)
    hV0.1 (fun a => (hV1 ν t j x hν hν1 ht htb a 0).2.1) hS0.2.2.1
    (fun a => (hS2 ν t j x hν hν1 ht htb a).2.2.2) hVdiff hGdiff hMd
  obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  · have hfun : (fun t' => gradHpTm 0 ν χf A j t' x) = fun s => (hpATerm ν χf A s x j).1 := by
      funext s
      simp [gradHpTm]
    have h1 : HasDerivAt (fun s => (hpATerm ν χf A s x j).1) Fd.1 t := dr_fst hF
    rw [hfun]
    refine ⟨h1.differentiableAt, ?_⟩
    rw [h1.deriv, Real.norm_eq_abs]
    exact b1
  · have hfun : (fun t' => gradHpTm 1 ν χf A j t' x) = fun s => (hpATerm ν χf A s x j).2 := by
      funext s
      simp [gradHpTm]
    have h2 : HasDerivAt (fun s => (hpATerm ν χf A s x j).2) Fd.2 t := dr_snd hF
    rw [hfun]
    refine ⟨h2.differentiableAt, ?_⟩
    rw [h2.deriv, Real.norm_eq_abs]
    exact b2

end UnforcedLeray.Short.PartIIIb.Concrete
