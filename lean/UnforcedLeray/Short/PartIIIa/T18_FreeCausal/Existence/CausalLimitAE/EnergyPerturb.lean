import UnforcedLeray.Short.PartIIIa.Sub.T18_2_1
import UnforcedLeray.Short.PartIIIa.Sub.T18_2_Gain

/-!
# Part III-a, task `PartIII-a:T18/2/1/5`: stability of `energyLoc` and `zeroEntrance` under an
`𝓗 × 𝒯` perturbation

Proves `UnforcedLeray.Short.IIIa.CausalEnergyPerturb` (statement in `Sub/T18_2_1.lean`).
Source of record: `the November 2 reference manuscript`, lines 3427-3440
("b - bn N in H", "|x| <= g |g⁻¹x|", "the zeroEntrance of bn N").

Proof. Put `g = gainG γ ν`, `Wb = gainConj γ ν (b' - b)`, `WG = gainConj γ ν (G' - G)`. Then
`b' - b = g • Wb` and `0 < g ≤ K := exp(|γ|/ν)` on `s ≥ 0`, so pointwise
`|b|² ≤ 2|b'|² + 2K²|Wb|²` and `|G|² ≤ 2|G'|² + 2K²|WG|²` (`ceP_pointwise_vec`,
`ceP_pointwise_tensor`).
* `zeroEntrance`: take the `δ` of `b'`; on `(ageμ c (-3/2)).restrict (Ioo 0 δ ×ˢ univ)` the
  pointwise bound and `Measure.restrict_le_self` give finiteness.
* `energyLoc`: on `Icc s₁ s₂ ×ˢ cell` the Lebesgue integral of a nonnegative `f` is at most
  `m⁻¹ ∫⁻ f d(ageμ c a)` with `m = ofReal (c⁻¹ s₂^a) > 0` for `a ≤ 0`
  (`lintegral_ageμ`, `ceP_lintegral_Icc_lt_top`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## Scaling of the norms -/

theorem ceP_vnorm2_smul_sq (r : ℝ) (a : Fin 2 → ℂ) :
    vnorm2 (fun i => r • a i) ^ 2 = r ^ 2 * vnorm2 a ^ 2 := by
  rw [causalLin_vnorm2_sq, causalLin_vnorm2_sq]
  simp only [Fin.sum_univ_two, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem ceP_tnorm2_smul_sq (r : ℝ) (T : Fin 2 → Fin 2 → ℂ) :
    tnorm2 (fun i j => r • T i j) ^ 2 = r ^ 2 * tnorm2 T ^ 2 := by
  rw [causalLin_tnorm2_sq, causalLin_tnorm2_sq]
  simp only [Fin.sum_univ_two, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-! ## Pointwise bounds through the gain -/

theorem ceP_pointwise_vec (g E : ℝ) (hg : 0 < g) (hgE : g ≤ E) (x y w : Fin 2 → ℂ)
    (hw : ∀ i, w i = g⁻¹ • (x i - y i)) :
    vnorm2 y ^ 2 ≤ 2 * vnorm2 x ^ 2 + 2 * (E ^ 2 * vnorm2 w ^ 2) := by
  have hg0 : g ≠ 0 := hg.ne'
  have hE2 : g ^ 2 ≤ E ^ 2 := by nlinarith
  have hw' : w = fun i => g⁻¹ • (x i - y i) := funext hw
  subst hw'
  have h0 : vnorm2 (fun i => x i - (x i - y i)) ^ 2 ≤
      2 * vnorm2 x ^ 2 + 2 * vnorm2 (fun i => x i - y i) ^ 2 :=
    causalLin_vnorm2_sub_sq_le x (fun i => x i - y i)
  have e : (fun i => x i - (x i - y i)) = y := by
    funext i
    ring
  rw [e] at h0
  have h1 : vnorm2 (fun i => x i - y i) ^ 2 =
      g ^ 2 * vnorm2 (fun i => g⁻¹ • (x i - y i)) ^ 2 := by
    rw [ceP_vnorm2_smul_sq, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hg0, one_pow, one_mul]
  have hw2 := mul_le_mul_of_nonneg_right hE2
    (sq_nonneg (vnorm2 (fun i => g⁻¹ • (x i - y i))))
  linarith

theorem ceP_pointwise_tensor (g E : ℝ) (hg : 0 < g) (hgE : g ≤ E) (x y w : Fin 2 → Fin 2 → ℂ)
    (hw : ∀ i j, w i j = g⁻¹ • (x i j - y i j)) :
    tnorm2 y ^ 2 ≤ 2 * tnorm2 x ^ 2 + 2 * (E ^ 2 * tnorm2 w ^ 2) := by
  have hg0 : g ≠ 0 := hg.ne'
  have hE2 : g ^ 2 ≤ E ^ 2 := by nlinarith
  have hw' : w = fun i j => g⁻¹ • (x i j - y i j) :=
    funext fun i => funext fun j => hw i j
  subst hw'
  have h0 : tnorm2 (fun i j => x i j - (x i j - y i j)) ^ 2 ≤
      2 * tnorm2 x ^ 2 + 2 * tnorm2 (fun i j => x i j - y i j) ^ 2 :=
    causalLin_tnorm2_sub_sq_le x (fun i j => x i j - y i j)
  have e : (fun i j => x i j - (x i j - y i j)) = y := by
    funext i j
    ring
  rw [e] at h0
  have h1 : tnorm2 (fun i j => x i j - y i j) ^ 2 =
      g ^ 2 * tnorm2 (fun i j => g⁻¹ • (x i j - y i j)) ^ 2 := by
    rw [ceP_tnorm2_smul_sq, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hg0, one_pow, one_mul]
  have hw2 := mul_le_mul_of_nonneg_right hE2
    (sq_nonneg (tnorm2 (fun i j => g⁻¹ • (x i j - y i j))))
  linarith

theorem ceP_measurable_gainG (γ ν : ℝ) : Measurable fun s : ℝ => gainG γ ν s := by
  unfold gainG
  fun_prop

/-! ## Elementary facts about sums and products of lower integrals -/

theorem ceP_ofReal_add3_le (u v w : ℝ) :
    ENNReal.ofReal (u + v + w) ≤ ENNReal.ofReal u + ENNReal.ofReal v + ENNReal.ofReal w :=
  ENNReal.ofReal_add_le.trans (add_le_add ENNReal.ofReal_add_le le_rfl)

theorem ceP_lintegral_add3_lt_top {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F₁ F₂ F₃ : α → ℝ≥0∞} (h₁ : Measurable F₁) (h₂ : Measurable F₂)
    (hF₁ : ∫⁻ a, F₁ a ∂μ < ⊤) (hF₂ : ∫⁻ a, F₂ a ∂μ < ⊤) (hF₃ : ∫⁻ a, F₃ a ∂μ < ⊤) :
    ∫⁻ a, (F₁ a + F₂ a + F₃ a) ∂μ < ⊤ := by
  have hm : Measurable fun a => F₁ a + F₂ a := h₁.add h₂
  calc ∫⁻ a, (F₁ a + F₂ a + F₃ a) ∂μ = ∫⁻ a, (F₁ a + F₂ a) ∂μ + ∫⁻ a, F₃ a ∂μ :=
        lintegral_add_left hm F₃
    _ = ∫⁻ a, F₁ a ∂μ + ∫⁻ a, F₂ a ∂μ + ∫⁻ a, F₃ a ∂μ := by
        rw [lintegral_add_left h₁ F₂]
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨hF₁, hF₂⟩, hF₃⟩

theorem ceP_lintegral_ofReal_mul_lt_top {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {r : ℝ} (hr : 0 ≤ r) {Z : α → ℝ} (hZ : ∫⁻ a, ENNReal.ofReal (Z a) ∂μ < ⊤) :
    ∫⁻ a, ENNReal.ofReal (r * Z a) ∂μ < ⊤ := by
  simp only [ENNReal.ofReal_mul hr]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hZ

/-- From a finite `eLpNorm` in `L²` to a finite lower integral of the squares. -/
theorem ceP_lintegral_sq_lt_top {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (h : eLpNorm f 2 μ < ⊤) : ∫⁻ a, ENNReal.ofReal (f a ^ 2) ∂μ < ⊤ := by
  have h2 : ∫⁻ a, ‖f a‖ₑ ^ ENNReal.toReal 2 ∂μ < ⊤ :=
    (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) ENNReal.ofNat_ne_top).1 h
  have e : ∀ a, ENNReal.ofReal (f a ^ 2) = ‖f a‖ₑ ^ ENNReal.toReal 2 := by
    intro a
    have h22 : ENNReal.toReal 2 = 2 := by norm_num
    rw [h22, ENNReal.rpow_two, Real.enorm_eq_ofReal_abs,
      ← ENNReal.ofReal_pow (abs_nonneg (f a)), sq_abs]
  rw [lintegral_congr e]
  exact h2

/-! ## The cell and the age density -/

theorem ceP_cell_eq (c : ℝ) :
    B0579.cell c = Ico (-c / 2) (c / 2) ×ˢ (univ : Set ℝ) := by
  unfold B0579.cell
  rw [neg_div]

theorem ceP_measurableSet_cell (c : ℝ) : MeasurableSet (B0579.cell c) := by
  unfold B0579.cell
  exact measurableSet_Ico.prod MeasurableSet.univ

/-- On `Icc s₁ s₂ ×ˢ cell` with `0 < s₁`, the Lebesgue lower integral of `f` is controlled by its
integral against `ageμ c a` for `a ≤ 0`: the density `c⁻¹ s^a` is at least `c⁻¹ s₂^a > 0`. -/
theorem ceP_lintegral_Icc_lt_top (c a s₁ s₂ : ℝ) (hc : 0 < c) (ha : a ≤ 0) (hs₁ : 0 < s₁)
    (hs₁₂ : s₁ ≤ s₂) {f : ℝ × (ℝ × ℝ) → ℝ≥0∞} (hf : Measurable f)
    (hfin : ∫⁻ p, f p ∂ageμ c a < ⊤) :
    ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, f p < ⊤ := by
  have hs₂ : 0 < s₂ := lt_of_lt_of_le hs₁ hs₁₂
  have hsub : Icc s₁ s₂ ×ˢ B0579.cell c ⊆
      Ioi (0 : ℝ) ×ˢ (Ico (-c / 2) (c / 2) ×ˢ (univ : Set ℝ)) := by
    rw [ceP_cell_eq]
    exact Set.prod_mono (fun x hx => lt_of_lt_of_le hs₁ hx.1) (Subset.refl _)
  have hS : MeasurableSet (Icc s₁ s₂ ×ˢ B0579.cell c) :=
    measurableSet_Icc.prod (ceP_measurableSet_cell c)
  have hm0 : ENNReal.ofReal (c⁻¹ * s₂ ^ a) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (mul_pos (inv_pos.2 hc) (Real.rpow_pos_of_pos hs₂ a))).ne'
  have hmtop : ENNReal.ofReal (c⁻¹ * s₂ ^ a) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpt : ∀ x ∈ Icc s₁ s₂ ×ˢ B0579.cell c,
      ENNReal.ofReal (c⁻¹ * s₂ ^ a) * f x ≤ ENNReal.ofReal (c⁻¹ * x.1 ^ a) * f x := by
    intro x hx
    have hx1 : 0 < x.1 := lt_of_lt_of_le hs₁ hx.1.1
    have hpow : s₂ ^ a ≤ x.1 ^ a := Real.rpow_le_rpow_of_nonpos hx1 hx.1.2 ha
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left hpow (inv_nonneg.2 hc.le))) zero_le
  have hA : ENNReal.ofReal (c⁻¹ * s₂ ^ a) * ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, f p ≤
      ∫⁻ p, f p ∂ageμ c a := by
    rw [← lintegral_const_mul' _ _ hmtop]
    calc ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (c⁻¹ * s₂ ^ a) * f p
        ≤ ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (c⁻¹ * p.1 ^ a) * f p :=
          setLIntegral_mono' hS hpt
      _ ≤ ∫⁻ p in Ioi (0 : ℝ) ×ˢ (Ico (-c / 2) (c / 2) ×ˢ (univ : Set ℝ)),
            ENNReal.ofReal (c⁻¹ * p.1 ^ a) * f p := lintegral_mono_set hsub
      _ = ∫⁻ p, f p ∂ageμ c a := (lintegral_ageμ hc a hf).symm
  rcases ENNReal.mul_lt_top_iff.1 (lt_of_le_of_lt hA hfin) with h | h | h
  · exact h.2
  · exact absurd h hm0
  · rw [h]
    exact ENNReal.zero_lt_top

/-! ## The stability statement -/

/-- **Stability of `energyLoc` and `zeroEntrance` under an `𝓗 × 𝒯` perturbation**
(`PartIII-a:T18/2/1/5`; SP 3427-3440). -/
theorem causalEnergyPerturb : UnforcedLeray.Short.IIIa.CausalEnergyPerturb := by
  intro c ν γ hc hν b' b G' G hbm hGm hb'm hG'm hE hZ hH hT
  have hH' := hH
  have hT' := hT
  unfold hCalNorm at hH'
  unfold tCalNorm at hT'
  -- pointwise bounds through the gain
  have hgpos : ∀ p : ℝ × (ℝ × ℝ), 0 < gainG γ ν p.1 := fun p => by
    unfold gainG
    exact Real.exp_pos _
  have hgE : ∀ p : ℝ × (ℝ × ℝ), 0 ≤ p.1 → gainG γ ν p.1 ≤ Real.exp (|γ| / ν) :=
    fun p hp => (gainG_bounds hν hp).2
  have hpB : ∀ p : ℝ × (ℝ × ℝ), 0 ≤ p.1 →
      vnorm2 (b p) ^ 2 ≤ 2 * vnorm2 (b' p) ^ 2 +
        2 * (Real.exp (|γ| / ν) ^ 2 * vnorm2 (gainConj γ ν (fun p i => b' p i - b p i) p) ^ 2) :=
    fun p hp => ceP_pointwise_vec (gainG γ ν p.1) (Real.exp (|γ| / ν)) (hgpos p) (hgE p hp)
      (b' p) (b p) (gainConj γ ν (fun p i => b' p i - b p i) p) (fun i => rfl)
  have hpG : ∀ p : ℝ × (ℝ × ℝ), 0 ≤ p.1 →
      tnorm2 (G p) ^ 2 ≤ 2 * tnorm2 (G' p) ^ 2 +
        2 * (Real.exp (|γ| / ν) ^ 2 *
          tnorm2 (gainConj γ ν (fun p i j => G' p i j - G p i j) p) ^ 2) :=
    fun p hp => ceP_pointwise_tensor (gainG γ ν p.1) (Real.exp (|γ| / ν)) (hgpos p) (hgE p hp)
      (G' p) (G p) (gainConj γ ν (fun p i j => G' p i j - G p i j) p) (fun i j => rfl)
  -- measurability
  have hgm : Measurable fun p : ℝ × (ℝ × ℝ) => (gainG γ ν p.1)⁻¹ :=
    ((ceP_measurable_gainG γ ν).comp measurable_fst).inv
  have hWbm : ∀ i, Measurable fun p => gainConj γ ν (fun p i => b' p i - b p i) p i :=
    fun i => hgm.smul ((hb'm i).sub (hbm i))
  have hWGm : ∀ i j, Measurable fun p => gainConj γ ν (fun p i j => G' p i j - G p i j) p i j :=
    fun i j => hgm.smul ((hG'm i j).sub (hGm i j))
  have hY1m : Measurable fun p => vnorm2 (gainConj γ ν (fun p i => b' p i - b p i) p) :=
    causalLin_measurable_vnorm2 (f := fun p => gainConj γ ν (fun p i => b' p i - b p i) p) hWbm
  have hY2m : Measurable fun p => tnorm2 (gainConj γ ν (fun p i j => G' p i j - G p i j) p) :=
    causalLin_measurable_tnorm2
      (f := fun p => gainConj γ ν (fun p i j => G' p i j - G p i j) p) hWGm
  have hXm : Measurable fun p => vnorm2 (b' p) ^ 2 + tnorm2 (G' p) ^ 2 :=
    ((causalLin_measurable_vnorm2 hb'm).pow_const 2).add
      ((causalLin_measurable_tnorm2 hG'm).pow_const 2)
  have hcellM : MeasurableSet (B0579.cell c) := ceP_measurableSet_cell c
  -- energyLoc for (b, G)
  have hEnergy : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
        ENNReal.ofReal (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) < ⊤ := by
    intro s₁ s₂ h₁ h₂
    have hS : MeasurableSet (Icc s₁ s₂ ×ˢ B0579.cell c) := measurableSet_Icc.prod hcellM
    have hI1 : ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
        ENNReal.ofReal (vnorm2 (b' p) ^ 2 + tnorm2 (G' p) ^ 2) < ⊤ := hE s₁ s₂ h₁ h₂
    have hI2 : ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
        ENNReal.ofReal (vnorm2 (gainConj γ ν (fun p i => b' p i - b p i) p) ^ 2) < ⊤ :=
      ceP_lintegral_Icc_lt_top c (-3 / 2) s₁ s₂ hc (by norm_num) h₁ h₂.le
        (ENNReal.measurable_ofReal.comp (hY1m.pow_const 2)) (ceP_lintegral_sq_lt_top hH')
    have hI3 : ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
        ENNReal.ofReal (tnorm2 (gainConj γ ν (fun p i j => G' p i j - G p i j) p) ^ 2) < ⊤ :=
      ceP_lintegral_Icc_lt_top c (-1 / 2) s₁ s₂ hc (by norm_num) h₁ h₂.le
        (ENNReal.measurable_ofReal.comp (hY2m.pow_const 2)) (ceP_lintegral_sq_lt_top hT')
    have hm1 : Measurable fun p : ℝ × (ℝ × ℝ) =>
        ENNReal.ofReal (2 * (vnorm2 (b' p) ^ 2 + tnorm2 (G' p) ^ 2)) :=
      ENNReal.measurable_ofReal.comp (hXm.const_mul 2)
    have hm2 : Measurable fun p : ℝ × (ℝ × ℝ) =>
        ENNReal.ofReal ((2 * Real.exp (|γ| / ν) ^ 2) *
          vnorm2 (gainConj γ ν (fun p i => b' p i - b p i) p) ^ 2) :=
      ENNReal.measurable_ofReal.comp ((hY1m.pow_const 2).const_mul _)
    have hfin1 : ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
        ENNReal.ofReal (2 * (vnorm2 (b' p) ^ 2 + tnorm2 (G' p) ^ 2)) < ⊤ :=
      ceP_lintegral_ofReal_mul_lt_top (by norm_num) hI1
    have hfin2 : ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
        ENNReal.ofReal ((2 * Real.exp (|γ| / ν) ^ 2) *
          vnorm2 (gainConj γ ν (fun p i => b' p i - b p i) p) ^ 2) < ⊤ :=
      ceP_lintegral_ofReal_mul_lt_top (by positivity) hI2
    have hfin3 : ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
        ENNReal.ofReal ((2 * Real.exp (|γ| / ν) ^ 2) *
          tnorm2 (gainConj γ ν (fun p i j => G' p i j - G p i j) p) ^ 2) < ⊤ :=
      ceP_lintegral_ofReal_mul_lt_top (by positivity) hI3
    have hpt : ∀ p ∈ Icc s₁ s₂ ×ˢ B0579.cell c,
        ENNReal.ofReal (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) ≤
          ENNReal.ofReal (2 * (vnorm2 (b' p) ^ 2 + tnorm2 (G' p) ^ 2)) +
            ENNReal.ofReal ((2 * Real.exp (|γ| / ν) ^ 2) *
              vnorm2 (gainConj γ ν (fun p i => b' p i - b p i) p) ^ 2) +
            ENNReal.ofReal ((2 * Real.exp (|γ| / ν) ^ 2) *
              tnorm2 (gainConj γ ν (fun p i j => G' p i j - G p i j) p) ^ 2) := by
      intro p hp
      have hp0 : 0 ≤ p.1 := le_trans h₁.le hp.1.1
      have hA := hpB p hp0
      have hB := hpG p hp0
      have hsum : vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2 ≤
          2 * (vnorm2 (b' p) ^ 2 + tnorm2 (G' p) ^ 2) +
            (2 * Real.exp (|γ| / ν) ^ 2) *
              vnorm2 (gainConj γ ν (fun p i => b' p i - b p i) p) ^ 2 +
            (2 * Real.exp (|γ| / ν) ^ 2) *
              tnorm2 (gainConj γ ν (fun p i j => G' p i j - G p i j) p) ^ 2 := by
        linarith
      exact (ENNReal.ofReal_le_ofReal hsum).trans (ceP_ofReal_add3_le _ _ _)
    calc ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2)
        ≤ ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
            (ENNReal.ofReal (2 * (vnorm2 (b' p) ^ 2 + tnorm2 (G' p) ^ 2)) +
              ENNReal.ofReal ((2 * Real.exp (|γ| / ν) ^ 2) *
                vnorm2 (gainConj γ ν (fun p i => b' p i - b p i) p) ^ 2) +
              ENNReal.ofReal ((2 * Real.exp (|γ| / ν) ^ 2) *
                tnorm2 (gainConj γ ν (fun p i j => G' p i j - G p i j) p) ^ 2)) :=
          setLIntegral_mono' hS hpt
      _ < ⊤ := ceP_lintegral_add3_lt_top hm1 hm2 hfin1 hfin2 hfin3
  refine ⟨hEnergy, ?_⟩
  -- zeroEntrance for (b, G), with the δ of b'
  obtain ⟨δ, hδ, hI⟩ := hZ
  refine ⟨δ, hδ, ?_⟩
  have hSδ : MeasurableSet (Ioo (0 : ℝ) δ ×ˢ (univ : Set (ℝ × ℝ))) :=
    measurableSet_Ioo.prod MeasurableSet.univ
  have hae0 : ∀ᵐ p ∂((ageμ c (-3 / 2)).restrict (Ioo (0 : ℝ) δ ×ˢ (univ : Set (ℝ × ℝ)))),
      p ∈ Ioo (0 : ℝ) δ ×ˢ (univ : Set (ℝ × ℝ)) := ae_restrict_mem hSδ
  have hpz : ∀ p ∈ Ioo (0 : ℝ) δ ×ˢ (univ : Set (ℝ × ℝ)),
      ENNReal.ofReal (vnorm2 (b p) ^ 2) ≤
        ENNReal.ofReal (2 * vnorm2 (b' p) ^ 2) +
          ENNReal.ofReal ((2 * Real.exp (|γ| / ν) ^ 2) *
            vnorm2 (gainConj γ ν (fun p i => b' p i - b p i) p) ^ 2) := by
    intro p hp
    have hp0 : 0 ≤ p.1 := le_of_lt hp.1.1
    have hA := hpB p hp0
    have hsum : vnorm2 (b p) ^ 2 ≤ 2 * vnorm2 (b' p) ^ 2 +
        (2 * Real.exp (|γ| / ν) ^ 2) *
          vnorm2 (gainConj γ ν (fun p i => b' p i - b p i) p) ^ 2 := by
      linarith
    exact (ENNReal.ofReal_le_ofReal hsum).trans ENNReal.ofReal_add_le
  have hae := hae0.mono fun p hp => hpz p hp
  have hmF : Measurable fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (2 * vnorm2 (b' p) ^ 2) :=
    ENNReal.measurable_ofReal.comp (((causalLin_measurable_vnorm2 hb'm).pow_const 2).const_mul 2)
  have hfin1 : ∫⁻ p, ENNReal.ofReal (2 * vnorm2 (b' p) ^ 2)
      ∂((ageμ c (-3 / 2)).restrict (Ioo (0 : ℝ) δ ×ˢ (univ : Set (ℝ × ℝ)))) < ⊤ :=
    ceP_lintegral_ofReal_mul_lt_top (by norm_num) hI
  have hfin2full : ∫⁻ p, ENNReal.ofReal ((2 * Real.exp (|γ| / ν) ^ 2) *
      vnorm2 (gainConj γ ν (fun p i => b' p i - b p i) p) ^ 2) ∂(ageμ c (-3 / 2)) < ⊤ :=
    ceP_lintegral_ofReal_mul_lt_top (by positivity) (ceP_lintegral_sq_lt_top hH')
  have hfin2 : ∫⁻ p, ENNReal.ofReal ((2 * Real.exp (|γ| / ν) ^ 2) *
      vnorm2 (gainConj γ ν (fun p i => b' p i - b p i) p) ^ 2)
      ∂((ageμ c (-3 / 2)).restrict (Ioo (0 : ℝ) δ ×ˢ (univ : Set (ℝ × ℝ)))) < ⊤ :=
    lt_of_le_of_lt (lintegral_mono' Measure.restrict_le_self le_rfl) hfin2full
  refine lt_of_le_of_lt (lintegral_mono_ae hae) ?_
  rw [lintegral_add_left hmF]
  exact ENNReal.add_lt_top.2 ⟨hfin1, hfin2⟩

end UnforcedLeray.Short.IIIa
