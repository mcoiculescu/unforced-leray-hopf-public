import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1_2_5
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1_2_5.W2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1_2_5.W2S
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1_2.Der
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1_2.VjS

/-!
# `PartIII-b:C/grad/3/4/1/1/2/5/4`: `s`-part of the `𝒦` envelope of `h^p_A`

Source `the November 2 reference manuscript`
4963-4980, 5063-5079.  `𝒦ψ = η ∂_η ψ + 2 s ∂_s ψ`; the `s`-part is `s ∂_s` of the lattice term.

The lattice term is `drPhi` (Der.lean), `h^p_A`'s `j`-th term at time `t`:
`M(t) V_t(x) - [(M(t) x_j)_1 G_0(t) + (M(t) x_j)_2 G_1(t)]` with `M = A^y`, `G_b(t) = hsG_t b x`.
Its `t`-derivative is the explicit `kSD` (product rule), and each term is absorbed by the
weight-two bounds `gradVjWeight2` (W2) and `gradVjSWeight2` (W2S).

Proved: `gradKopSEnv`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Entries of a `t`-derivative of a matrix-valued function. -/
lemma ks_entry {M : ℝ → Mat3} {M' : Mat3} {s : ℝ} (hM : HasDerivAt M M' s) (a b : Fin 3) :
    HasDerivAt (fun t => M t a b) (M' a b) s :=
  hasDerivAt_pi.1 (hasDerivAt_pi.1 hM a) b

/-- Product rule for `merApply (M t) (v t)`. -/
lemma ks_merApply {M : ℝ → Mat3} {M' : Mat3} {v : ℝ → ℝ × ℝ} {v' : ℝ × ℝ} {s : ℝ}
    (hM : HasDerivAt M M' s) (hv : HasDerivAt v v' s) :
    HasDerivAt (fun t => merApply (M t) (v t)) (merApply M' (v s) + merApply (M s) v') s := by
  have c1 := ((ks_entry hM 0 0).mul (dr_fst hv)).add ((ks_entry hM 0 2).mul (dr_snd hv))
  have c2 := ((ks_entry hM 2 0).mul (dr_fst hv)).add ((ks_entry hM 2 2).mul (dr_snd hv))
  refine (c1.prodMk c2).congr_deriv ?_
  ext <;> simp only [merApply, Prod.fst_add, Prod.snd_add] <;> ring

/-- Sum of three summands under a common weight. -/
lemma ks_sum (w a b c K : ℝ) (hw : 0 ≤ w) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : w * (a + b + c) ≤ K) : w * a ≤ K ∧ w * b ≤ K ∧ w * c ≤ K := by
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith [mul_nonneg hw ha, mul_nonneg hw hb, mul_nonneg hw hc]

/-- Weight `B²` dominates `t` when `B ≥ 1`. -/
lemma ks_le (B t K : ℝ) (hB : 1 ≤ B) (ht : 0 ≤ t) (h : B ^ 2 * t ≤ K) : t ≤ K := by
  have h1 : 1 ≤ B ^ 2 := one_le_pow₀ hB
  have h2 : 1 * t ≤ B ^ 2 * t := mul_le_mul_of_nonneg_right h1 ht
  linarith

/-- `B * ‖v‖ ≤ K` from `B² ‖v‖ ≤ K`. -/
lemma ks_w (B K : ℝ) (v : ℝ × ℝ) (hB : 1 ≤ B) (hv : B ^ 2 * ‖v‖ ≤ K) : B * ‖v‖ ≤ K := by
  have hn := norm_nonneg v
  have hBB : B ≤ B ^ 2 := by nlinarith
  exact (mul_le_mul_of_nonneg_right hBB hn).trans hv

/-- Components of a vector under a weight. -/
lemma ks_w_fs (w K : ℝ) (v : ℝ × ℝ) (hw : 0 ≤ w) (hv : w * ‖v‖ ≤ K) :
    w * |v.1| ≤ K ∧ w * |v.2| ≤ K :=
  ⟨(mul_le_mul_of_nonneg_left (norm_fst_le v) hw).trans hv,
    (mul_le_mul_of_nonneg_left (norm_snd_le v) hw).trans hv⟩

/-- Components of `s • v` under weight `B`. -/
lemma ks_comp_s (B s K : ℝ) (v : ℝ × ℝ) (hB : 1 ≤ B) (hs : 0 ≤ s)
    (hv : B ^ 2 * (s * ‖v‖) ≤ K) : B * |s * v.1| ≤ K ∧ B * |s * v.2| ≤ K := by
  have hn := norm_nonneg v
  have ht : 0 ≤ s * ‖v‖ := mul_nonneg hs hn
  have hBB : B ≤ B ^ 2 := by nlinarith
  have hB0 : 0 ≤ B := by linarith
  have h1 : |s * v.1| ≤ s * ‖v‖ := by
    rw [abs_mul, abs_of_nonneg hs]; exact mul_le_mul_of_nonneg_left (norm_fst_le v) hs
  have h2 : |s * v.2| ≤ s * ‖v‖ := by
    rw [abs_mul, abs_of_nonneg hs]; exact mul_le_mul_of_nonneg_left (norm_snd_le v) hs
  exact ⟨(mul_le_mul_of_nonneg_left h1 hB0).trans ((mul_le_mul_of_nonneg_right hBB ht).trans hv),
    (mul_le_mul_of_nonneg_left h2 hB0).trans ((mul_le_mul_of_nonneg_right hBB ht).trans hv)⟩

/-- Components of `s • v` under no weight. -/
lemma ks_u (B s K : ℝ) (v : ℝ × ℝ) (hB : 1 ≤ B) (hs : 0 ≤ s)
    (hv : B ^ 2 * (s * ‖v‖) ≤ K) : |s * v.1| ≤ K ∧ |s * v.2| ≤ K := by
  have hn := norm_nonneg v
  have ht : 0 ≤ s * ‖v‖ := mul_nonneg hs hn
  have hle : s * ‖v‖ ≤ K := ks_le B _ K hB ht hv
  have h1 : |s * v.1| ≤ s * ‖v‖ := by
    rw [abs_mul, abs_of_nonneg hs]; exact mul_le_mul_of_nonneg_left (norm_fst_le v) hs
  have h2 : |s * v.2| ≤ s * ‖v‖ := by
    rw [abs_mul, abs_of_nonneg hs]; exact mul_le_mul_of_nonneg_left (norm_snd_le v) hs
  exact ⟨h1.trans hle, h2.trans hle⟩

lemma ks_two (G K a0 a2 x0 x2 : ℝ) (hG : 0 ≤ G) (hK : 0 ≤ K) (h0 : |a0| ≤ G) (h2 : |a2| ≤ G)
    (hx0 : |x0| ≤ K) (hx2 : |x2| ≤ K) : |a0 * x0 + a2 * x2| ≤ G * K + G * K := by
  calc |a0 * x0 + a2 * x2| ≤ |a0 * x0| + |a2 * x2| := abs_add_le _ _
    _ = |a0| * |x0| + |a2| * |x2| := by rw [abs_mul, abs_mul]
    _ ≤ G * K + G * K := add_le_add (mul_le_mul h0 hx0 (abs_nonneg _) hG)
        (mul_le_mul h2 hx2 (abs_nonneg _) hG)

lemma ks_lin (G K B X1 X2 p0 p2 g : ℝ) (hG : 0 ≤ G) (hK : 0 ≤ K) (hB : 1 ≤ B)
    (hX : |X1| + |X2| ≤ B) (hp0 : |p0| ≤ G) (hp2 : |p2| ≤ G) (hg : B * |g| ≤ K) :
    |(p0 * X1 + p2 * X2) * g| ≤ G * K := by
  have hB0 : 0 ≤ B := by linarith
  have h1 : |p0 * X1 + p2 * X2| ≤ G * B := by
    calc |p0 * X1 + p2 * X2| ≤ |p0 * X1| + |p2 * X2| := abs_add_le _ _
      _ = |p0| * |X1| + |p2| * |X2| := by rw [abs_mul, abs_mul]
      _ ≤ G * |X1| + G * |X2| := add_le_add (mul_le_mul_of_nonneg_right hp0 (abs_nonneg _))
          (mul_le_mul_of_nonneg_right hp2 (abs_nonneg _))
      _ = G * (|X1| + |X2|) := by ring
      _ ≤ G * B := mul_le_mul_of_nonneg_left hX hG
  rw [abs_mul]
  calc |p0 * X1 + p2 * X2| * |g| ≤ (G * B) * |g| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ = G * (B * |g|) := by ring
    _ ≤ G * K := mul_le_mul_of_nonneg_left hg hG

/-- Real estimate for one component of `s ∂_s` of the lattice term. -/
lemma ks_core (G K B X1 X2 V1 V2 U1 U2 g0 g1 H0 H1 e0 e2 m0 m2 p0 p2 q0 q2 r0 r2 t0 t2 : ℝ)
    (hG : 0 ≤ G) (hK : 0 ≤ K) (hB : 1 ≤ B) (hX : |X1| + |X2| ≤ B)
    (he0 : |e0| ≤ G) (he2 : |e2| ≤ G) (hm0 : |m0| ≤ G) (hm2 : |m2| ≤ G)
    (hp0 : |p0| ≤ G) (hp2 : |p2| ≤ G) (hq0 : |q0| ≤ G) (hq2 : |q2| ≤ G)
    (hr0 : |r0| ≤ G) (hr2 : |r2| ≤ G) (ht0 : |t0| ≤ G) (ht2 : |t2| ≤ G)
    (hV1 : |V1| ≤ K) (hV2 : |V2| ≤ K) (hU1 : |U1| ≤ K) (hU2 : |U2| ≤ K)
    (hg0 : B * |g0| ≤ K) (hg1 : B * |g1| ≤ K) (hH0 : B * |H0| ≤ K) (hH1 : B * |H1| ≤ K) :
    |(e0 * V1 + e2 * V2) + (m0 * U1 + m2 * U2)
        - (((p0 * X1 + p2 * X2) * g0 + (q0 * X1 + q2 * X2) * H0)
          + ((r0 * X1 + r2 * X2) * g1 + (t0 * X1 + t2 * X2) * H1))| ≤ 8 * G * K := by
  have A1 := ks_two G K e0 e2 V1 V2 hG hK he0 he2 hV1 hV2
  have A2 := ks_two G K m0 m2 U1 U2 hG hK hm0 hm2 hU1 hU2
  have A3 := ks_lin G K B X1 X2 p0 p2 g0 hG hK hB hX hp0 hp2 hg0
  have A4 := ks_lin G K B X1 X2 q0 q2 H0 hG hK hB hX hq0 hq2 hH0
  have A5 := ks_lin G K B X1 X2 r0 r2 g1 hG hK hB hX hr0 hr2 hg1
  have A6 := ks_lin G K B X1 X2 t0 t2 H1 hG hK hB hX ht0 ht2 hH1
  obtain ⟨a1, a1'⟩ := abs_le.mp A1
  obtain ⟨a2, a2'⟩ := abs_le.mp A2
  obtain ⟨a3, a3'⟩ := abs_le.mp A3
  obtain ⟨a4, a4'⟩ := abs_le.mp A4
  obtain ⟨a5, a5'⟩ := abs_le.mp A5
  obtain ⟨a6, a6'⟩ := abs_le.mp A6
  rw [abs_le]
  constructor <;> linarith

/-- The derivative of the `j`-th lattice term of `h^p_A` in `s` (product rule). -/
def kSD (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (j : ℤ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (merApply (deriv (Ay ν χ A) s) (Vj ν s j x) + merApply (Ay ν χ A s) (deriv (fun t => Vj ν t j x) s))
    - (((merApply (Ay ν χ A s) (xj ν j x)).1 • deriv (fun t => hsG ν t j 0 x) s
          + (merApply (deriv (Ay ν χ A) s) (xj ν j x)).1 • hsG ν s j 0 x)
        + ((merApply (Ay ν χ A s) (xj ν j x)).2 • deriv (fun t => hsG ν t j 1 x) s
          + (merApply (deriv (Ay ν χ A) s) (xj ν j x)).2 • hsG ν s j 1 x))

lemma ks_hasDeriv (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (j : ℤ) (x : ℝ × ℝ)
    (hC : ContDiffAt ℝ 2 (Ay ν χ A) s) (hA : 1 ≤ ageA ν s) :
    HasDerivAt (fun t => drPhi ν χ A t j x) (kSD ν χ A s j x) s := by
  have hM : HasDerivAt (Ay ν χ A) (deriv (Ay ν χ A) s) s :=
    (hC.differentiableAt (by norm_num)).hasDerivAt
  have hV : HasDerivAt (fun t => Vj ν t j x) (deriv (fun t => Vj ν t j x) s) s :=
    (vs_Vj_hasDeriv ν j x s hA).differentiableAt.hasDerivAt
  have hG : ∀ a : Fin 2, HasDerivAt (fun t => hsG ν t j a x) (deriv (fun t => hsG ν t j a x) s) s :=
    fun a => (vs_hsG_hasDeriv ν j x a s hA).differentiableAt.hasDerivAt
  have hX : HasDerivAt (fun t => merApply (Ay ν χ A t) (xj ν j x))
      (merApply (deriv (Ay ν χ A) s) (xj ν j x)) s := by
    have h := ks_merApply hM (hasDerivAt_const s (xj ν j x))
    refine h.congr_deriv ?_
    simp [merApply]
  exact (ks_merApply hM hV).sub (((dr_fst hX).smul (hG 0)).add ((dr_snd hX).smul (hG 1)))

theorem gradKopSEnv : GradKopSEnv := by
  obtain ⟨C2, hC2, hW⟩ := gradVjWeight2
  obtain ⟨CS, hCS, hWS⟩ := gradVjSWeight2
  refine ⟨8 * (C2 + CS), by linarith, ?_⟩
  intro ν s χf A hd x i j
  obtain ⟨hν, hν1, hs, hs1, hC⟩ := hd
  have hA : 1 ≤ ageA ν s := vs_A_ge hν.le hs.le
  have hB1 : (1 : ℝ) ≤ 1 + |x.1 - (j : ℝ) * cOf ν| + |x.2| := by
    linarith [abs_nonneg (x.1 - (j : ℝ) * cOf ν), abs_nonneg x.2]
  have hB0 : (0 : ℝ) ≤ 1 + |x.1 - (j : ℝ) * cOf ν| + |x.2| := by linarith
  have hWd : 0 ≤ gradW ν x j := gradW_nonneg ν x j
  have hGF : 0 ≤ gradF ν χf A s := gradF_nonneg _ _ _ _
  have hK0 : 0 ≤ (C2 + CS) * gradW ν x j := mul_nonneg (by linarith) hWd
  have hKC2 : C2 * gradW ν x j ≤ (C2 + CS) * gradW ν x j := by
    nlinarith [mul_nonneg hCS hWd]
  have hKCS : CS * gradW ν x j ≤ (C2 + CS) * gradW ν x j := by
    nlinarith [mul_nonneg hC2 hWd]
  have hW' := hW ν s j x hν hν1 hs hs1
  have hWS' := (hWS ν s j x hν hν1 hs hs1 0).1
  -- the value `V_j`
  have hVb : (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 2 * ‖Vj ν s j x‖ ≤ (C2 + CS) * gradW ν x j :=
    (ks_sum _ _ _ _ _ (sq_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      (hW' 0 0)).1.trans hKC2
  have hVn : ‖Vj ν s j x‖ ≤ (C2 + CS) * gradW ν x j :=
    ks_le _ _ _ hB1 (norm_nonneg _) hVb
  have hV1 : |(Vj ν s j x).1| ≤ (C2 + CS) * gradW ν x j := (norm_fst_le _).trans hVn
  have hV2 : |(Vj ν s j x).2| ≤ (C2 + CS) * gradW ν x j := (norm_snd_le _).trans hVn
  -- the `s`-derivative of `V_j`
  have hUb := ks_u _ _ _ _ hB1 hs.le (hWS'.trans hKCS)
  -- the values and `s`-derivatives of `hsG`
  have hGb : ∀ b : Fin 2, (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) * |(hsG ν s j b x).1|
        ≤ (C2 + CS) * gradW ν x j
      ∧ (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) * |(hsG ν s j b x).2|
        ≤ (C2 + CS) * gradW ν x j := by
    intro b
    have h : (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 2 * ‖hsG ν s j b x‖
        ≤ (C2 + CS) * gradW ν x j := by
      rw [← hs_eq ν s j b x]
      exact (ks_sum _ _ _ _ _ (sq_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
        (hW' b 0)).2.1.trans hKC2
    exact ks_w_fs _ _ _ hB0 (ks_w _ _ _ hB1 h)
  have hHb : ∀ b : Fin 2, (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|)
        * |s * (deriv (fun t => hsG ν t j b x) s).1| ≤ (C2 + CS) * gradW ν x j
      ∧ (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|)
        * |s * (deriv (fun t => hsG ν t j b x) s).2| ≤ (C2 + CS) * gradW ν x j := by
    intro b
    have h := (hWS ν s j x hν hν1 hs hs1 b).2
    rw [vs_fderiv_eq ν j x b] at h
    exact ks_comp_s _ _ _ _ hB1 hs.le (h.trans hKCS)
  -- entries of `A^y` and of `s ∂_s A^y`
  have hMb : ∀ a b : Fin 3, |Ay ν χf A s a b| ≤ gradF ν χf A s := by
    intro a b
    have h1 := dr_entry_le (Ay ν χf A s) a b
    have h2 : 0 ≤ frob (sDeriv (Ay ν χf A) s) := Real.sqrt_nonneg _
    have h3 : 0 ≤ frob (sDeriv (sDeriv (Ay ν χf A)) s) := Real.sqrt_nonneg _
    unfold gradF
    linarith
  have hEb : ∀ a b : Fin 3, |s * deriv (Ay ν χf A) s a b| ≤ gradF ν χf A s := by
    intro a b
    have h1 : |s * deriv (Ay ν χf A) s a b| ≤ frob (sDeriv (Ay ν χf A) s) :=
      dr_entry_le (sDeriv (Ay ν χf A) s) a b
    have h2 : 0 ≤ frob (Ay ν χf A s) := Real.sqrt_nonneg _
    have h3 : 0 ≤ frob (sDeriv (sDeriv (Ay ν χf A)) s) := Real.sqrt_nonneg _
    unfold gradF
    linarith
  have hX : |(xj ν j x).1| + |(xj ν j x).2| ≤ 1 + |x.1 - (j : ℝ) * cOf ν| + |x.2| := by
    show |x.1 - (j : ℝ) * cOf ν| + |x.2| ≤ _
    linarith
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  rcases hi with rfl | rfl
  · have hfun : (fun s' => gradHpTm 0 ν χf A j s' x) = fun s' => (drPhi ν χf A s' j x).1 := by
      funext s'
      simp [gradHpTm, dr_hpA_eq]
    have hder : deriv (fun s' => gradHpTm 0 ν χf A j s' x) s = (kSD ν χf A s j x).1 := by
      rw [hfun]
      exact (dr_fst (ks_hasDeriv ν χf A s j x hC hA)).deriv
    rw [hder]
    have key := ks_core (gradF ν χf A s) ((C2 + CS) * gradW ν x j)
      (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) (xj ν j x).1 (xj ν j x).2
      (Vj ν s j x).1 (Vj ν s j x).2
      (s * (deriv (fun t => Vj ν t j x) s).1) (s * (deriv (fun t => Vj ν t j x) s).2)
      (hsG ν s j 0 x).1 (hsG ν s j 1 x).1
      (s * (deriv (fun t => hsG ν t j 0 x) s).1) (s * (deriv (fun t => hsG ν t j 1 x) s).1)
      (s * deriv (Ay ν χf A) s 0 0) (s * deriv (Ay ν χf A) s 0 2)
      (Ay ν χf A s 0 0) (Ay ν χf A s 0 2)
      (s * deriv (Ay ν χf A) s 0 0) (s * deriv (Ay ν χf A) s 0 2)
      (Ay ν χf A s 0 0) (Ay ν χf A s 0 2)
      (s * deriv (Ay ν χf A) s 2 0) (s * deriv (Ay ν χf A) s 2 2)
      (Ay ν χf A s 2 0) (Ay ν χf A s 2 2)
      hGF (by linarith) hB1 hX
      (hEb 0 0) (hEb 0 2) (hMb 0 0) (hMb 0 2) (hEb 0 0) (hEb 0 2) (hMb 0 0) (hMb 0 2)
      (hEb 2 0) (hEb 2 2) (hMb 2 0) (hMb 2 2)
      hV1 hV2 hUb.1 hUb.2 (hGb 0).1 (hGb 1).1 (hHb 0).1 (hHb 1).1
    have hfin : |s * (kSD ν χf A s j x).1| ≤ 8 * gradF ν χf A s * ((C2 + CS) * gradW ν x j) := by
      refine le_trans (le_of_eq (congrArg (fun z => |z|) ?_)) key
      unfold kSD
      simp only [merApply, Prod.fst_add, Prod.fst_sub, Prod.snd_add, Prod.snd_sub,
        Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    calc _ ≤ _ := hfin
      _ = 8 * (C2 + CS) * gradF ν χf A s * gradW ν x j := by ring
  · have hfun : (fun s' => gradHpTm 1 ν χf A j s' x) = fun s' => (drPhi ν χf A s' j x).2 := by
      funext s'
      simp [gradHpTm, dr_hpA_eq]
    have hder : deriv (fun s' => gradHpTm 1 ν χf A j s' x) s = (kSD ν χf A s j x).2 := by
      rw [hfun]
      exact (dr_snd (ks_hasDeriv ν χf A s j x hC hA)).deriv
    rw [hder]
    have key := ks_core (gradF ν χf A s) ((C2 + CS) * gradW ν x j)
      (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) (xj ν j x).1 (xj ν j x).2
      (Vj ν s j x).1 (Vj ν s j x).2
      (s * (deriv (fun t => Vj ν t j x) s).1) (s * (deriv (fun t => Vj ν t j x) s).2)
      (hsG ν s j 0 x).2 (hsG ν s j 1 x).2
      (s * (deriv (fun t => hsG ν t j 0 x) s).2) (s * (deriv (fun t => hsG ν t j 1 x) s).2)
      (s * deriv (Ay ν χf A) s 2 0) (s * deriv (Ay ν χf A) s 2 2)
      (Ay ν χf A s 2 0) (Ay ν χf A s 2 2)
      (s * deriv (Ay ν χf A) s 0 0) (s * deriv (Ay ν χf A) s 0 2)
      (Ay ν χf A s 0 0) (Ay ν χf A s 0 2)
      (s * deriv (Ay ν χf A) s 2 0) (s * deriv (Ay ν χf A) s 2 2)
      (Ay ν χf A s 2 0) (Ay ν χf A s 2 2)
      hGF (by linarith) hB1 hX
      (hEb 2 0) (hEb 2 2) (hMb 2 0) (hMb 2 2) (hEb 0 0) (hEb 0 2) (hMb 0 0) (hMb 0 2)
      (hEb 2 0) (hEb 2 2) (hMb 2 0) (hMb 2 2)
      hV1 hV2 hUb.1 hUb.2 (hGb 0).2 (hGb 1).2 (hHb 0).2 (hHb 1).2
    have hfin : |s * (kSD ν χf A s j x).2| ≤ 8 * gradF ν χf A s * ((C2 + CS) * gradW ν x j) := by
      refine le_trans (le_of_eq (congrArg (fun z => |z|) ?_)) key
      unfold kSD
      simp only [merApply, Prod.fst_add, Prod.fst_sub, Prod.snd_add, Prod.snd_sub,
        Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    calc _ ≤ _ := hfin
      _ = 8 * (C2 + CS) * gradF ν χf A s * gradW ν x j := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
