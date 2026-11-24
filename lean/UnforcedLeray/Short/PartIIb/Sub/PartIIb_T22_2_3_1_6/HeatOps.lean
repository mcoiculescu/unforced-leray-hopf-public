import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_1_6.Kernel

/-!


Source: `the November 2 reference manuscript`, lines 2100-2105.  For `F` jointly
continuous with `|F(r)| ≤ b(r)`: the operators `e^{aΔ} F(r)`, `(∂_i K_a) * F(r)`, `(∂_i ∂_j K_a) * F(r)`
are jointly continuous for `a > 0` (scaled representation, `opCont`) with sizes `b`, `a^{-1/2} b`,
`a^{-1} b`; `(∂_j K_a) * g` is differentiable with derivative `(∂_i ∂_j K_a) * g`
(`heatSGd_hasFDeriv`); and the commutator `ψ (∂_i ∂_j K_a) * g - (∂_i ∂_j K_a) * (ψ g)` has the size
`a^{-1/2}` (`comm_dd_le`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb.BwdRoute

namespace LS

open CylPDE

variable {T : ℝ}

/-! ## Sizes -/

/-- A convolution with a kernel dominated by a Gaussian. -/
theorem conv_abs_le {b c M : ℝ} (hb : 0 < b) {Q g : Pl → ℝ} (hQ : ∀ z, |Q z| ≤ c * heatK b z)
    (hg : ∀ y, |g y| ≤ M) (hc : 0 ≤ c) (x : Pl) : |∫ y : Pl, Q (x - y) * g y| ≤ c * M := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hg 0)
  have h := norm_integral_le_of_norm_le (f := fun y : Pl => Q (x - y) * g y)
    (g := fun y => c * M * heatK b (x - y)) ((heatK_sub_int hb x).const_mul (c * M))
    (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_mul]
      have h1 := mul_le_mul (hQ (x - y)) (hg y) (abs_nonneg _)
        (mul_nonneg hc (heatK_pos' hb _).le)
      refine h1.trans (le_of_eq ?_)
      ring)
  rw [integral_const_mul, integral_heatK_sub hb, mul_one, Real.norm_eq_abs] at h
  exact h

theorem heatSG_abs_le {a M : ℝ} (ha : 0 < a) {g : Pl → ℝ} (hg : ∀ y, |g y| ≤ M) (x : Pl) :
    |heatSG a g x| ≤ M := by
  unfold heatSG
  rw [ite_cond_eq_false _ _ (eq_false (not_le.2 ha))]
  have h := conv_abs_le (c := 1) ha (Q := heatK a) (fun z => by
    rw [abs_of_pos (heatK_pos' ha z), one_mul]) hg zero_le_one x
  simpa using h

theorem heatSGd_abs_le {a M : ℝ} (ha : 0 < a) (i : Fin 2) {g : Pl → ℝ} (hg : ∀ y, |g y| ≤ M)
    (x : Pl) : |heatSGd i a g x| ≤ 9 * (Real.sqrt a)⁻¹ * M := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  exact conv_abs_le (by linarith : 0 < 2 * a) (heatKd_le ha i) hg (by positivity) x

theorem heatSGdd_abs_le {a M : ℝ} (ha : 0 < a) (i j : Fin 2) {g : Pl → ℝ} (hg : ∀ y, |g y| ≤ M)
    (x : Pl) : |heatSGdd i j a g x| ≤ 5 * a⁻¹ * M := by
  have hs : 0 < a⁻¹ := inv_pos.2 ha
  exact conv_abs_le (by linarith : 0 < 2 * a) (heatKdd_le ha i j) hg (by positivity) x

theorem rpow_neg_half {a : ℝ} (ha : 0 < a) : a ^ (-(1 / 2 : ℝ)) = (Real.sqrt a)⁻¹ := by
  rw [Real.rpow_neg ha.le, Real.sqrt_eq_rpow]

/-! ## Differentiation of `(∂_j K_a) * g` -/

theorem kdd_int {a M : ℝ} (ha : 0 < a) (i j : Fin 2) {g : Pl → ℝ} (hgc : Continuous g)
    (hg : ∀ y, |g y| ≤ M) (x : Pl) : Integrable (fun y : Pl => heatKdd i j a (x - y) * g y) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hg 0)
  have hs : 0 < a⁻¹ := inv_pos.2 ha
  refine Integrable.mono' ((heatK_sub_int (by linarith : 0 < 2 * a) x).const_mul (5 * a⁻¹ * M))
    (((heatKdd_cont i j a).comp (continuous_const.sub continuous_id)).mul hgc).aestronglyMeasurable
    (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have h1 := mul_le_mul (heatKdd_le ha i j (x - y)) (hg y) (abs_nonneg _)
    (mul_nonneg (by positivity) (heatK_pos' (by linarith : 0 < 2 * a) _).le)
  refine h1.trans (le_of_eq ?_)
  ring

theorem kd_int {a M : ℝ} (ha : 0 < a) (i : Fin 2) {g : Pl → ℝ} (hgc : Continuous g)
    (hg : ∀ y, |g y| ≤ M) (x : Pl) : Integrable (fun y : Pl => heatKd i a (x - y) * g y) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hg 0)
  have hs : 0 < (Real.sqrt a)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 ha)
  refine Integrable.mono' ((heatK_sub_int (by linarith : 0 < 2 * a) x).const_mul
    (9 * (Real.sqrt a)⁻¹ * M))
    (((heatKd_cont i a).comp (continuous_const.sub continuous_id)).mul hgc).aestronglyMeasurable
    (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have h1 := mul_le_mul (heatKd_le ha i (x - y)) (hg y) (abs_nonneg _)
    (mul_nonneg (by positivity) (heatK_pos' (by linarith : 0 < 2 * a) _).le)
  refine h1.trans (le_of_eq ?_)
  ring

theorem k_int {a M : ℝ} (ha : 0 < a) {g : Pl → ℝ} (hgc : Continuous g)
    (hg : ∀ y, |g y| ≤ M) (x : Pl) : Integrable (fun y : Pl => heatK a (x - y) * g y) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hg 0)
  refine Integrable.mono' ((heatK_sub_int ha x).const_mul M)
    (((heatK_cont' a).comp (continuous_const.sub continuous_id)).mul hgc).aestronglyMeasurable
    (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (heatK_pos' ha _)]
  have := mul_le_mul_of_nonneg_left (hg y) (heatK_pos' ha (x - y)).le
  linarith

theorem norm_kddCLM_le {a : ℝ} (ha : 0 < a) (j : Fin 2) (z : Pl) :
    ‖kddCLM j a z‖ ≤ (5 * a⁻¹ + 5 * a⁻¹) * heatK (2 * a) z := by
  refine (DiffC.norm_clm_le _ _).trans ?_
  have h0 := heatKdd_le ha 0 j z
  have h1 := heatKdd_le ha 1 j z
  linarith

/-- `(∂_j K_a) * g` is differentiable with derivative `(∂_i ∂_j K_a) * g`. -/
theorem heatSGd_hasFDeriv {a M : ℝ} (ha : 0 < a) (j : Fin 2) {g : Pl → ℝ} (hgc : Continuous g)
    (hg : ∀ y, |g y| ≤ M) (x₀ : Pl) :
    HasFDerivAt (heatSGd j a g)
      (heatSGdd 0 j a g x₀ • ContinuousLinearMap.fst ℝ ℝ ℝ +
        heatSGdd 1 j a g x₀ • ContinuousLinearMap.snd ℝ ℝ ℝ) x₀ := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hg 0)
  have hA : 0 < a⁻¹ := inv_pos.2 ha
  have hE : 0 ≤ 2 * Real.exp (1 / (4 * a)) := by positivity
  have hsub : ∀ x : Pl, Continuous (fun y : Pl => x - y) := fun x =>
    continuous_const.sub continuous_id
  have hkc : ∀ x : Pl, Continuous (fun y : Pl => kddCLM j a (x - y)) := by
    intro x
    unfold kddCLM
    exact ((((heatKdd_cont 0 j a).comp (hsub x)).smul continuous_const).add
      (((heatKdd_cont 1 j a).comp (hsub x)).smul continuous_const))
  have hmain : HasFDerivAt (fun x : Pl => ∫ y : Pl, heatKd j a (x - y) * g y)
      (∫ y : Pl, g y • kddCLM j a (x₀ - y)) x₀ := by
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := ball x₀ 1)
      (F := fun x y => heatKd j a (x - y) * g y)
      (F' := fun x y => g y • kddCLM j a (x - y))
      (bound := fun y => M * ((5 * a⁻¹ + 5 * a⁻¹) *
        (2 * Real.exp (1 / (4 * a)) * heatK (4 * a) (x₀ - y))))
      (ball_mem_nhds x₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun x =>
        (((heatKd_cont j a).comp (hsub x)).mul hgc).aestronglyMeasurable
    · exact kd_int ha j hgc hg x₀
    · exact (hgc.smul (hkc x₀)).aestronglyMeasurable
    · refine ae_of_all _ fun y x hx => ?_
      rw [norm_smul, Real.norm_eq_abs]
      refine mul_le_mul (hg y) ?_ (norm_nonneg _) hM
      refine (norm_kddCLM_le ha j (x - y)).trans ?_
      exact mul_le_mul_of_nonneg_left (heatK_shift ha hx y) (by positivity)
    · exact (((heatK_sub_int (by linarith : 0 < 4 * a) x₀).const_mul _).const_mul _).const_mul _
    · refine ae_of_all _ fun y x _ => ?_
      have h1 : HasFDerivAt (fun x : Pl => heatKd j a (x - y)) (kddCLM j a (x - y)) x := by
        have h2 := (heatKd_hasFDeriv ha j (x - y)).comp x
          (hasFDerivAt_sub_const (𝕜 := ℝ) (x := x) y)
        rw [ContinuousLinearMap.comp_id] at h2
        exact h2
      have h3 := h1.mul_const (g y)
      exact h3
  have hval : (∫ y : Pl, g y • kddCLM j a (x₀ - y)) =
      heatSGdd 0 j a g x₀ • ContinuousLinearMap.fst ℝ ℝ ℝ +
        heatSGdd 1 j a g x₀ • ContinuousLinearMap.snd ℝ ℝ ℝ := by
    have hpt : ∀ y : Pl, g y • kddCLM j a (x₀ - y) =
        (heatKdd 0 j a (x₀ - y) * g y) • ContinuousLinearMap.fst ℝ ℝ ℝ +
          (heatKdd 1 j a (x₀ - y) * g y) • ContinuousLinearMap.snd ℝ ℝ ℝ := by
      intro y
      unfold kddCLM
      rw [smul_add, smul_smul, smul_smul, mul_comm (g y), mul_comm (g y)]
    simp_rw [hpt]
    rw [integral_add ((kdd_int ha 0 j hgc hg x₀).smul_const _)
      ((kdd_int ha 1 j hgc hg x₀).smul_const _), integral_smul_const, integral_smul_const]
    rfl
  rw [hval] at hmain
  exact hmain

/-! ## The commutator -/

/-- **The commutator of `ψ` with `(∂_i ∂_j K_a) *` has the integrable size `a^{-1/2}`.** -/
theorem comm_dd_le {a L M : ℝ} (ha : 0 < a) {ψ : ℝ → ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ s t, |ψ s - ψ t| ≤ L * |s - t|) (hψc : Continuous ψ) {Cψ : ℝ} (hCψ : ∀ t, |ψ t| ≤ Cψ)
    {g : Pl → ℝ} (hgc : Continuous g) (hg : ∀ y, |g y| ≤ M) (i j : Fin 2) (x : Pl) :
    |ψ x.2 * heatSGdd i j a g x - heatSGdd i j a (fun y => ψ y.2 * g y) x| ≤
      L * (77 * (Real.sqrt a)⁻¹) * M := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hg 0)
  have hs : 0 < (Real.sqrt a)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 ha)
  have ha2 : 0 < 2 * a := by linarith
  have hψg : ∀ y : Pl, |ψ y.2 * g y| ≤ Cψ * M := fun y => by
    rw [abs_mul]
    exact mul_le_mul (hCψ _) (hg y) (abs_nonneg _) ((abs_nonneg _).trans (hCψ 0))
  have hψgc : Continuous (fun y : Pl => ψ y.2 * g y) := (hψc.comp continuous_snd).mul hgc
  have h1 := kdd_int ha i j hgc hg x
  have h2 := kdd_int ha i j hψgc hψg x
  have hid : ψ x.2 * heatSGdd i j a g x - heatSGdd i j a (fun y => ψ y.2 * g y) x =
      ∫ y : Pl, (ψ x.2 - ψ y.2) * (heatKdd i j a (x - y) * g y) := by
    unfold heatSGdd
    rw [← integral_const_mul, ← integral_sub (h1.const_mul _) h2]
    congr 1
    funext y
    ring
  rw [hid]
  have hb := norm_integral_le_of_norm_le
    (f := fun y : Pl => (ψ x.2 - ψ y.2) * (heatKdd i j a (x - y) * g y))
    (g := fun y => L * (77 * (Real.sqrt a)⁻¹) * M * heatK (2 * a) (x - y))
    ((heatK_sub_int ha2 x).const_mul _) (ae_of_all _ fun y => ?_)
  · rw [integral_const_mul, integral_heatK_sub ha2, mul_one, Real.norm_eq_abs] at hb
    exact hb
  · have hz := z_heatKdd_le ha i j (x - y)
    have hzz : (x - y).2 = x.2 - y.2 := rfl
    rw [hzz] at hz
    have hK := heatK_pos' ha2 (x - y)
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    calc |ψ x.2 - ψ y.2| * (|heatKdd i j a (x - y)| * |g y|)
        ≤ (L * |x.2 - y.2|) * (|heatKdd i j a (x - y)| * M) := by
          gcongr
          · exact hL _ _
          · exact hg y
      _ = L * (|x.2 - y.2| * |heatKdd i j a (x - y)|) * M := by ring
      _ ≤ L * (77 * (Real.sqrt a)⁻¹ * heatK (2 * a) (x - y)) * M := by gcongr
      _ = _ := by ring

/-! ## Joint continuity for `a > 0` -/

/-- Joint continuity of a scaled kernel operator. -/
theorem opCont {κ : ℝ → ℝ} {ℓ : Pl → ℝ} (hκ : ContinuousOn κ (Ioi 0)) (hℓ : Continuous ℓ)
    (hℓi : Integrable (fun w : Pl => |ℓ w| * heatK 1 w)) {G : ℝ → Pl → ℝ} (hG : CB0 T G) :
    ContinuousOn (fun p : ℝ × ℝ × Pl => ∫ w : Pl,
      κ p.1 * ℓ w * heatK 1 w * G p.2.1 (p.2.2 - Real.sqrt p.1 • w))
      (Ioi 0 ×ˢ (Icc 0 T ×ˢ univ)) := by
  obtain ⟨hGc, C, hC⟩ := hG
  intro p₀ hp₀
  have hK1 : ∀ w : Pl, 0 < heatK 1 w := heatK_pos' one_pos
  have hslice : ∀ r ∈ Icc 0 T, Continuous (G r) := fun r hr =>
    DiffC.cont_slice hGc hr
  have hκp : ContinuousWithinAt (fun p : ℝ × ℝ × Pl => κ p.1) (Ioi 0 ×ˢ (Icc 0 T ×ˢ univ)) p₀ :=
    (hκ p₀.1 hp₀.1).comp continuous_fst.continuousWithinAt fun p hp => hp.1
  have hev : ∀ᶠ p in 𝓝[Ioi 0 ×ˢ (Icc 0 T ×ˢ univ)] p₀, |κ p.1| < |κ p₀.1| + 1 := by
    have h1 : Tendsto (fun p : ℝ × ℝ × Pl => |κ p.1|) (𝓝[Ioi 0 ×ˢ (Icc 0 T ×ˢ univ)] p₀)
        (𝓝 |κ p₀.1|) := continuous_abs.continuousAt.comp_continuousWithinAt hκp
    exact h1.eventually (gt_mem_nhds (lt_add_one _))
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC p₀.2.1 hp₀.2.1 0)
  refine continuousWithinAt_of_dominated
    (bound := fun w => (|κ p₀.1| + 1) * C * (|ℓ w| * heatK 1 w)) ?_ ?_ (hℓi.const_mul _) ?_
  · filter_upwards [self_mem_nhdsWithin] with p hp
    have hc1 : Continuous (fun w : Pl => G p.2.1 (p.2.2 - Real.sqrt p.1 • w)) :=
      (hslice _ hp.2.1).comp (by fun_prop)
    have hc2 : Continuous (fun w : Pl => κ p.1 * ℓ w * heatK 1 w) :=
      (continuous_const.mul hℓ).mul (heatK_cont' 1)
    exact (hc2.mul hc1).aestronglyMeasurable
  · filter_upwards [hev, self_mem_nhdsWithin] with p hκ1 hp
    refine ae_of_all _ fun w => ?_
    have h2 := hC p.2.1 hp.2.1 (p.2.2 - Real.sqrt p.1 • w)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos (hK1 w)]
    calc |κ p.1| * |ℓ w| * heatK 1 w * |G p.2.1 (p.2.2 - Real.sqrt p.1 • w)|
        = |κ p.1| * |G p.2.1 (p.2.2 - Real.sqrt p.1 • w)| * (|ℓ w| * heatK 1 w) := by ring
      _ ≤ (|κ p₀.1| + 1) * C * (|ℓ w| * heatK 1 w) :=
          mul_le_mul_of_nonneg_right (mul_le_mul hκ1.le h2 (abs_nonneg _) (by positivity))
            (mul_nonneg (abs_nonneg _) (hK1 w).le)
  · refine ae_of_all _ fun w => ?_
    have hmap : ContinuousWithinAt
        (fun p : ℝ × ℝ × Pl => ((p.2.1, p.2.2 - Real.sqrt p.1 • w) : ℝ × Pl))
        (Ioi 0 ×ˢ (Icc 0 T ×ˢ univ)) p₀ := by
      apply Continuous.continuousWithinAt
      fun_prop
    have h3 : ContinuousWithinAt (fun p : ℝ × ℝ × Pl => G p.2.1 (p.2.2 - Real.sqrt p.1 • w))
        (Ioi 0 ×ˢ (Icc 0 T ×ˢ univ)) p₀ :=
      ContinuousWithinAt.comp (g := fun z : ℝ × Pl => G z.1 z.2)
        (f := fun p : ℝ × ℝ × Pl => ((p.2.1, p.2.2 - Real.sqrt p.1 • w) : ℝ × Pl))
        (hGc _ ⟨hp₀.2.1, mem_univ _⟩) hmap fun p hp => ⟨hp.2.1, mem_univ _⟩
    exact ((hκp.mul continuousWithinAt_const).mul continuousWithinAt_const).mul h3

/-- The scaled profile of `∂_i ∂_j K`. -/
def lDD (i j : Fin 2) (w : Pl) : ℝ :=
  ![w.1, w.2] i * ![w.1, w.2] j / 4 - (if i = j then 1 / 2 else 0)

theorem lDD_cont (i j : Fin 2) : Continuous (lDD i j) := by
  unfold lDD
  have hi : ∀ i : Fin 2, Continuous (fun z : Pl => (![z.1, z.2] : Fin 2 → ℝ) i) := by
    intro i
    fin_cases i <;> simp <;> fun_prop
  exact (((hi i).mul (hi j)).div_const _).sub continuous_const

/-- The scaled representation of `(∂_i ∂_j K_a) * g`. -/
theorem heatSGdd_pos_eq {a : ℝ} (ha : 0 < a) (i j : Fin 2) (g : Pl → ℝ) (x : Pl) :
    heatSGdd i j a g x = ∫ w : Pl, a⁻¹ * lDD i j w * heatK 1 w * g (x - Real.sqrt a • w) := by
  unfold heatSGdd
  have h1 : ∫ y : Pl, heatKdd i j a (x - y) * g y = ∫ u : Pl, heatKdd i j a u * g (x - u) := by
    rw [← integral_sub_left_eq_self (fun u : Pl => heatKdd i j a u * g (x - u)) volume x]
    congr 1
    funext y
    simp
  have h2 := MeasureTheory.Measure.integral_comp_smul (volume : Measure Pl)
    (fun u : Pl => heatKdd i j a u * g (x - u)) (Real.sqrt a)
  rw [HC.finrank_pl] at h2
  have hs : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  rw [hs, abs_of_pos (inv_pos.2 ha), smul_eq_mul] at h2
  have hpt : ∀ w : Pl, a * (heatKdd i j a (Real.sqrt a • w) * g (x - Real.sqrt a • w)) =
      a⁻¹ * lDD i j w * heatK 1 w * g (x - Real.sqrt a • w) := by
    intro w
    have hsc := HC.heatK_scale ha w
    have hvec : ∀ k : Fin 2, ![(Real.sqrt a • w).1, (Real.sqrt a • w).2] k =
        Real.sqrt a * ![w.1, w.2] k := by
      intro k
      fin_cases k <;> simp
    have hsq : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha.le
    have hsqpos : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
    unfold heatKdd lDD
    rw [hvec, hvec, ← hsc]
    generalize heatK a (Real.sqrt a • w) = K
    generalize g (x - Real.sqrt a • w) = G'
    obtain ⟨s, hs_eq⟩ : ∃ s, s = Real.sqrt a := ⟨_, rfl⟩
    have hsa : a = s * s := by rw [hs_eq, hsq]
    have hspos : s ≠ 0 := by rw [hs_eq]; exact hsqpos.ne'
    rw [← hs_eq, hsa]
    by_cases hij : i = j
    · simp only [hij, ite_true]
      field_simp
    · simp only [hij, ite_false]
      field_simp
      ring
  rw [h1]
  calc ∫ u : Pl, heatKdd i j a u * g (x - u)
      = a * ∫ w : Pl, heatKdd i j a (Real.sqrt a • w) * g (x - Real.sqrt a • w) := by
        rw [h2, ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]
    _ = ∫ w : Pl, a * (heatKdd i j a (Real.sqrt a • w) * g (x - Real.sqrt a • w)) :=
        (integral_const_mul _ _).symm
    _ = _ := by
        congr 1
        funext w
        exact hpt w

theorem lDD_int (i j : Fin 2) : Integrable (fun w : Pl => |lDD i j w| * heatK 1 w) := by
  have hb : ∀ w : Pl, |lDD i j w| * heatK 1 w = |heatKdd i j 1 w| := by
    intro w
    unfold heatKdd lDD
    rw [abs_mul, abs_of_pos (heatK_pos' one_pos w)]
    congr 2
    norm_num
  refine Integrable.mono' ((heatK_int (by norm_num : (0 : ℝ) < 2 * 1)).const_mul (5 * 1⁻¹))
    ((continuous_abs.comp (lDD_cont i j)).mul (heatK_cont' 1)).aestronglyMeasurable
    (ae_of_all _ fun w => ?_)
  rw [hb, Real.norm_eq_abs, abs_abs]
  exact heatKdd_le one_pos i j w

theorem contOn_inv : ContinuousOn (fun a : ℝ => a⁻¹) (Ioi 0) :=
  continuousOn_inv₀.mono fun _ ha => ne_of_gt ha

theorem heatSG_joint {G : ℝ → Pl → ℝ} (hG : CB0 T G) :
    ContinuousOn (fun p : ℝ × ℝ × Pl => heatSG p.1 (G p.2.1) p.2.2)
      (Ioi 0 ×ˢ (Icc 0 T ×ˢ univ)) := by
  have hi : Integrable (fun w : Pl => |(fun _ : Pl => (1 : ℝ)) w| * heatK 1 w) := by
    simpa using heatK_int one_pos
  refine (opCont (κ := fun _ => 1) (ℓ := fun _ => 1) continuousOn_const continuous_const hi hG).congr
    fun p hp => ?_
  rw [HC.heatSG_pos_eq hp.1]
  simp

theorem heatSGd_joint (i : Fin 2) {G : ℝ → Pl → ℝ} (hG : CB0 T G) :
    ContinuousOn (fun p : ℝ × ℝ × Pl => heatSGd i p.1 (G p.2.1) p.2.2)
      (Ioi 0 ×ˢ (Icc 0 T ×ˢ univ)) := by
  have hκ : ContinuousOn (fun a : ℝ => -1 / (2 * Real.sqrt a)) (Ioi 0) := by
    refine continuousOn_const.div (continuousOn_const.mul Real.continuous_sqrt.continuousOn) ?_
    intro a ha
    exact (mul_pos two_pos (Real.sqrt_pos.2 ha)).ne'
  refine (opCont (ℓ := fun w : Pl => ![w.1, w.2] i) hκ (CC.hv_coord i) (CC.abs_coord_int i) hG).congr
    fun p hp => ?_
  rw [DPC.heatSGd_pos_eq hp.1]
  congr 1
  funext w
  ring

theorem heatSGdd_joint (i j : Fin 2) {G : ℝ → Pl → ℝ} (hG : CB0 T G) :
    ContinuousOn (fun p : ℝ × ℝ × Pl => heatSGdd i j p.1 (G p.2.1) p.2.2)
      (Ioi 0 ×ˢ (Icc 0 T ×ˢ univ)) := by
  refine (opCont contOn_inv (lDD_cont i j) (lDD_int i j) hG).congr fun p hp => ?_
  rw [heatSGdd_pos_eq hp.1]

/-! ## Admissibility -/

theorem DAdm.mono {C C' : ℝ} {b : ℝ → ℝ} {A : ℝ → ℝ → Pl → ℝ} (h : DAdm T C b A) (hC : C ≤ C')
    (hb0 : ∀ r ∈ Icc 0 T, 0 ≤ b r) : DAdm T C' b A := by
  refine ⟨h.cont, fun a ha r hr x => (h.bound a ha r hr x).trans ?_⟩
  have h1 : 0 ≤ a ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg ha.le _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (by linarith)) (hb0 r hr)

theorem one_le_kernel {a : ℝ} (ha : 0 < a) : 1 ≤ 1 + a ^ (-(1 / 2 : ℝ)) := by
  have h1 : 0 ≤ a ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg ha.le _
  linarith

theorem sqrt_inv_le_kernel {a : ℝ} (ha : 0 < a) : (Real.sqrt a)⁻¹ ≤ 1 + a ^ (-(1 / 2 : ℝ)) := by
  rw [rpow_neg_half ha]
  linarith

theorem admH {b : ℝ → ℝ} {G : ℝ → Pl → ℝ} (hG : CB0 T G) (hb : CBle T 0 G b)
    (hb0 : ∀ r ∈ Icc 0 T, 0 ≤ b r) : DAdm T 1 b (fun a r x => heatSG a (G r) x) := by
  refine ⟨heatSG_joint hG, fun a ha r hr x => ?_⟩
  refine (heatSG_abs_le ha (hb r hr) x).trans ?_
  have := mul_le_mul_of_nonneg_right (one_le_kernel ha) (hb0 r hr)
  linarith

theorem admHd (i : Fin 2) {b : ℝ → ℝ} {G : ℝ → Pl → ℝ} (hG : CB0 T G) (hb : CBle T 0 G b)
    (hb0 : ∀ r ∈ Icc 0 T, 0 ≤ b r) : DAdm T 9 b (fun a r x => heatSGd i a (G r) x) := by
  refine ⟨heatSGd_joint i hG, fun a ha r hr x => ?_⟩
  refine (heatSGd_abs_le ha i (hb r hr) x).trans ?_
  have h1 := sqrt_inv_le_kernel ha
  exact mul_le_mul_of_nonneg_right (by linarith) (hb0 r hr)

end LS

end UnforcedLeray.Short.IIb.BwdRoute
