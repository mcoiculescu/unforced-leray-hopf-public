import UnforcedLeray.Short.PartIIIa.Sub.T18

/-!
# T18 linear class: `CausalSolSub` (`PartIII-a:T18/1`)

Proves `UnforcedLeray.Short.IIIa.CausalSolSub` (statement in `Sub/T18.lean`).
Source of record: `the November 2 reference manuscript`, lines 3541-3552
("a homogeneous difference in the energy class").

Proof. Every clause of `IsCausalEnergySolution` is linear in `(F, b, G)`:
* energy clauses: `‖x - y‖² ≤ 2‖x‖² + 2‖y‖²` pointwise, then monotonicity and additivity of the
  lower Lebesgue integral with finite integrals on both sides;
* zero entrance: the smaller of the two `δ`, with the restricted measures compared by monotonicity;
* divergence-free and weak gradient: `integral_sub` on integrable pieces;
* integrability and weak equation: the pointwise identity `flatIntegrand_sub`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-! ## Elementary inequalities for the norms -/

theorem causalLin_norm_sub_sq_le (x y : ℂ) : ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h1 : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
  have h0 : 0 ≤ ‖x - y‖ := norm_nonneg _
  nlinarith [mul_le_mul h1 h1 h0 (add_nonneg (norm_nonneg x) (norm_nonneg y)),
    sq_nonneg (‖x‖ - ‖y‖)]

theorem causalLin_vnorm2_sq (a : Fin 2 → ℂ) : vnorm2 a ^ 2 = ∑ i, ‖a i‖ ^ 2 := by
  unfold vnorm2
  exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)

theorem causalLin_tnorm2_sq (T : Fin 2 → Fin 2 → ℂ) :
    tnorm2 T ^ 2 = ∑ i, ∑ j, ‖T i j‖ ^ 2 := by
  unfold tnorm2
  exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)

theorem causalLin_vnorm2_sub_sq_le (a a' : Fin 2 → ℂ) :
    vnorm2 (fun i => a i - a' i) ^ 2 ≤ 2 * vnorm2 a ^ 2 + 2 * vnorm2 a' ^ 2 := by
  rw [causalLin_vnorm2_sq, causalLin_vnorm2_sq, causalLin_vnorm2_sq]
  simp only [Fin.sum_univ_two]
  linarith [causalLin_norm_sub_sq_le (a 0) (a' 0), causalLin_norm_sub_sq_le (a 1) (a' 1)]

theorem causalLin_tnorm2_sub_sq_le (T T' : Fin 2 → Fin 2 → ℂ) :
    tnorm2 (fun i j => T i j - T' i j) ^ 2 ≤ 2 * tnorm2 T ^ 2 + 2 * tnorm2 T' ^ 2 := by
  rw [causalLin_tnorm2_sq, causalLin_tnorm2_sq, causalLin_tnorm2_sq]
  simp only [Fin.sum_univ_two]
  linarith [causalLin_norm_sub_sq_le (T 0 0) (T' 0 0), causalLin_norm_sub_sq_le (T 0 1) (T' 0 1),
    causalLin_norm_sub_sq_le (T 1 0) (T' 1 0), causalLin_norm_sub_sq_le (T 1 1) (T' 1 1)]

/-! ## Measurability of the norms -/

theorem causalLin_measurable_vnorm2 {α : Type*} [MeasurableSpace α] {f : α → Fin 2 → ℂ}
    (hf : ∀ i, Measurable fun a => f a i) : Measurable fun a => vnorm2 (f a) := by
  unfold vnorm2
  apply Measurable.sqrt
  apply Finset.measurable_sum
  intro i _
  exact ((hf i).norm).pow_const 2

theorem causalLin_measurable_tnorm2 {α : Type*} [MeasurableSpace α]
    {f : α → Fin 2 → Fin 2 → ℂ} (hf : ∀ i j, Measurable fun a => f a i j) :
    Measurable fun a => tnorm2 (f a) := by
  unfold tnorm2
  apply Measurable.sqrt
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  exact ((hf i j).norm).pow_const 2

/-! ## A lower-integral bound for a pointwise quadratic inequality -/

theorem causalLin_lintegral_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {X X' D : α → ℝ} (hX : Measurable X)
    (hD : ∀ a, D a ≤ 2 * X a + 2 * X' a) :
    ∫⁻ a, ENNReal.ofReal (D a) ∂μ ≤
      2 * ∫⁻ a, ENNReal.ofReal (X a) ∂μ + 2 * ∫⁻ a, ENNReal.ofReal (X' a) ∂μ := by
  have hm : Measurable fun a => 2 * ENNReal.ofReal (X a) :=
    measurable_const.mul (ENNReal.measurable_ofReal.comp hX)
  calc ∫⁻ a, ENNReal.ofReal (D a) ∂μ
      ≤ ∫⁻ a, (2 * ENNReal.ofReal (X a) + 2 * ENNReal.ofReal (X' a)) ∂μ := by
        refine lintegral_mono fun a => ?_
        calc ENNReal.ofReal (D a) ≤ ENNReal.ofReal (2 * X a + 2 * X' a) :=
              ENNReal.ofReal_le_ofReal (hD a)
          _ ≤ ENNReal.ofReal (2 * X a) + ENNReal.ofReal (2 * X' a) := ENNReal.ofReal_add_le
          _ = 2 * ENNReal.ofReal (X a) + 2 * ENNReal.ofReal (X' a) := by
              rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
                ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
    _ = 2 * ∫⁻ a, ENNReal.ofReal (X a) ∂μ + 2 * ∫⁻ a, ENNReal.ofReal (X' a) ∂μ := by
        rw [lintegral_add_left hm, lintegral_const_mul' 2 _ (by simp),
          lintegral_const_mul' 2 _ (by simp)]

/-! ## The pointwise identity for the tested integrand -/

theorem causalLin_flatIntegrand_sub (ν : ℝ) (μ : ℂ) (vel : ℝ → ℝ × ℝ → Fin 2 → ℝ)
    (F F' : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b b' : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (p : ℝ × (ℝ × ℝ)) :
    flatIntegrand ν μ vel (fun p i j => F p i j - F' p i j) (fun p i => b p i - b' p i) Φ p =
      flatIntegrand ν μ vel F b Φ p - flatIntegrand ν μ vel F' b' Φ p := by
  unfold flatIntegrand
  try dsimp only
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hS : ∑ j : Fin 2,
      (F p i j - F' p i j - ((vel p.1 p.2 i : ℂ) * (b p j - b' p j) +
        (b p i - b' p i) * (vel p.1 p.2 j : ℂ))) * (flatGrad Φ p.1 p.2 i j : ℂ) =
      (∑ j : Fin 2, (F p i j - ((vel p.1 p.2 i : ℂ) * b p j + b p i * (vel p.1 p.2 j : ℂ))) *
        (flatGrad Φ p.1 p.2 i j : ℂ)) -
      ∑ j : Fin 2, (F' p i j - ((vel p.1 p.2 i : ℂ) * b' p j + b' p i * (vel p.1 p.2 j : ℂ))) *
        (flatGrad Φ p.1 p.2 i j : ℂ) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  linear_combination hS

/-! ## Linearity of the solution class -/

/-- **Linearity of the solution class** (`PartIII-a:T18/1`; SP 3541-3552, "a homogeneous
difference in the energy class"). -/
theorem causalSolSub : UnforcedLeray.Short.IIIa.CausalSolSub := by
  intro c ν μ vel F F' b b' G G' hb hb'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- measurable
  · intro i
    exact (hb.measurable i).sub (hb'.measurable i)
  -- gradMeasurable
  · intro i j
    exact (hb.gradMeasurable i j).sub (hb'.gradMeasurable i j)
  -- energyLoc
  · intro s₁ s₂ h₁ h₂
    have hI := hb.energyLoc s₁ s₂ h₁ h₂
    have hI' := hb'.energyLoc s₁ s₂ h₁ h₂
    have hX : Measurable fun p : ℝ × (ℝ × ℝ) => vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2 :=
      ((causalLin_measurable_vnorm2 hb.measurable).pow_const 2).add
        ((causalLin_measurable_tnorm2 hb.gradMeasurable).pow_const 2)
    have hD : ∀ p : ℝ × (ℝ × ℝ),
        vnorm2 (fun i => b p i - b' p i) ^ 2 + tnorm2 (fun i j => G p i j - G' p i j) ^ 2 ≤
          2 * (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) +
            2 * (vnorm2 (b' p) ^ 2 + tnorm2 (G' p) ^ 2) := fun p => by
      linarith [causalLin_vnorm2_sub_sq_le (b p) (b' p), causalLin_tnorm2_sub_sq_le (G p) (G' p)]
    have key := causalLin_lintegral_le (volume.restrict (Icc s₁ s₂ ×ˢ B0579.cell c)) hX hD
    exact lt_of_le_of_lt key (by finiteness)
  -- zeroEntrance
  · obtain ⟨δ₁, hδ₁, hI₁⟩ := hb.zeroEntrance
    obtain ⟨δ₂, hδ₂, hI₂⟩ := hb'.zeroEntrance
    have hpos : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
    refine ⟨min δ₁ δ₂, hpos, ?_⟩
    have hsub₁ : Ioo (0 : ℝ) (min δ₁ δ₂) ×ˢ (univ : Set (ℝ × ℝ)) ⊆
        Ioo (0 : ℝ) δ₁ ×ˢ (univ : Set (ℝ × ℝ)) :=
      prod_mono (Ioo_subset_Ioo_right (min_le_left _ _)) Subset.rfl
    have hsub₂ : Ioo (0 : ℝ) (min δ₁ δ₂) ×ˢ (univ : Set (ℝ × ℝ)) ⊆
        Ioo (0 : ℝ) δ₂ ×ˢ (univ : Set (ℝ × ℝ)) :=
      prod_mono (Ioo_subset_Ioo_right (min_le_right _ _)) Subset.rfl
    have hfin₁ : ∫⁻ p, ENNReal.ofReal (vnorm2 (b p) ^ 2)
        ∂((ageμ c (-3 / 2)).restrict (Ioo (0 : ℝ) (min δ₁ δ₂) ×ˢ univ)) < ⊤ :=
      lt_of_le_of_lt (lintegral_mono' (Measure.restrict_mono hsub₁ le_rfl) le_rfl) hI₁
    have hfin₂ : ∫⁻ p, ENNReal.ofReal (vnorm2 (b' p) ^ 2)
        ∂((ageμ c (-3 / 2)).restrict (Ioo (0 : ℝ) (min δ₁ δ₂) ×ˢ univ)) < ⊤ :=
      lt_of_le_of_lt (lintegral_mono' (Measure.restrict_mono hsub₂ le_rfl) le_rfl) hI₂
    have hXb : Measurable fun p : ℝ × (ℝ × ℝ) => vnorm2 (b p) ^ 2 :=
      (causalLin_measurable_vnorm2 hb.measurable).pow_const 2
    have hD0 : ∀ p : ℝ × (ℝ × ℝ),
        vnorm2 (fun i => b p i - b' p i) ^ 2 ≤ 2 * vnorm2 (b p) ^ 2 + 2 * vnorm2 (b' p) ^ 2 :=
      fun p => causalLin_vnorm2_sub_sq_le (b p) (b' p)
    have key := causalLin_lintegral_le
      ((ageμ c (-3 / 2)).restrict (Ioo (0 : ℝ) (min δ₁ δ₂) ×ˢ univ)) hXb hD0
    exact lt_of_le_of_lt key (by finiteness)
  -- divFree
  · intro s hs ψ hψ
    have h0 := hb.divFree s hs ψ hψ
    have h0' := hb'.divFree s hs ψ hψ
    have I0 : IntegrableOn (fun x => b (s, x) 0 * (B0579.pd 0 ψ x : ℂ)) (B0579.cell c) :=
      ((hb.weakGrad s hs 0 0).1 ψ hψ).1
    have I1 : IntegrableOn (fun x => b (s, x) 1 * (B0579.pd 1 ψ x : ℂ)) (B0579.cell c) :=
      ((hb.weakGrad s hs 1 1).1 ψ hψ).1
    have J0 : IntegrableOn (fun x => b' (s, x) 0 * (B0579.pd 0 ψ x : ℂ)) (B0579.cell c) :=
      ((hb'.weakGrad s hs 0 0).1 ψ hψ).1
    have J1 : IntegrableOn (fun x => b' (s, x) 1 * (B0579.pd 1 ψ x : ℂ)) (B0579.cell c) :=
      ((hb'.weakGrad s hs 1 1).1 ψ hψ).1
    show ∫ x in B0579.cell c, ((b (s, x) 0 - b' (s, x) 0) * (B0579.pd 0 ψ x : ℂ) +
      (b (s, x) 1 - b' (s, x) 1) * (B0579.pd 1 ψ x : ℂ)) = 0
    have eqfun : (fun x => (b (s, x) 0 - b' (s, x) 0) * (B0579.pd 0 ψ x : ℂ) +
        (b (s, x) 1 - b' (s, x) 1) * (B0579.pd 1 ψ x : ℂ)) =
        fun x => (b (s, x) 0 * (B0579.pd 0 ψ x : ℂ) + b (s, x) 1 * (B0579.pd 1 ψ x : ℂ)) -
          (b' (s, x) 0 * (B0579.pd 0 ψ x : ℂ) + b' (s, x) 1 * (B0579.pd 1 ψ x : ℂ)) := by
      funext x
      ring
    have hI : IntegrableOn (fun x => b (s, x) 0 * (B0579.pd 0 ψ x : ℂ) +
        b (s, x) 1 * (B0579.pd 1 ψ x : ℂ)) (B0579.cell c) := Integrable.add I0 I1
    have hJ : IntegrableOn (fun x => b' (s, x) 0 * (B0579.pd 0 ψ x : ℂ) +
        b' (s, x) 1 * (B0579.pd 1 ψ x : ℂ)) (B0579.cell c) := Integrable.add J0 J1
    rw [eqfun, integral_sub hI hJ, h0, h0', sub_self]
  -- weakGrad
  · intro s hs i j
    have hE := hb.weakGrad s hs i j
    have hE' := hb'.weakGrad s hs i j
    unfold HasWeakCellDerivC at hE hE' ⊢
    refine ⟨fun ψ hψ => ?_, fun ψ hψ => ?_⟩
    · obtain ⟨hA1, hA2⟩ := hE.1 ψ hψ
      obtain ⟨hB1, hB2⟩ := hE'.1 ψ hψ
      refine ⟨?_, ?_⟩
      · have e : (fun x => (b (s, x) i - b' (s, x) i) * (B0579.pd j ψ x : ℂ)) =
            fun x => b (s, x) i * (B0579.pd j ψ x : ℂ) - b' (s, x) i * (B0579.pd j ψ x : ℂ) := by
          funext x
          ring
        show IntegrableOn (fun x => (b (s, x) i - b' (s, x) i) * (B0579.pd j ψ x : ℂ))
          (B0579.cell c)
        rw [e]
        exact Integrable.sub hA1 hB1
      · have e : (fun x => (G (s, x) i j - G' (s, x) i j) * (ψ x : ℂ)) =
            fun x => G (s, x) i j * (ψ x : ℂ) - G' (s, x) i j * (ψ x : ℂ) := by
          funext x
          ring
        show IntegrableOn (fun x => (G (s, x) i j - G' (s, x) i j) * (ψ x : ℂ))
          (B0579.cell c)
        rw [e]
        exact Integrable.sub hA2 hB2
    · have hA1 : IntegrableOn (fun x => b (s, x) i * (B0579.pd j ψ x : ℂ)) (B0579.cell c) :=
        ((hE.1 ψ hψ).1)
      have hB1 : IntegrableOn (fun x => b' (s, x) i * (B0579.pd j ψ x : ℂ)) (B0579.cell c) :=
        ((hE'.1 ψ hψ).1)
      have hA2 : IntegrableOn (fun x => G (s, x) i j * (ψ x : ℂ)) (B0579.cell c) :=
        ((hE.1 ψ hψ).2)
      have hB2 : IntegrableOn (fun x => G' (s, x) i j * (ψ x : ℂ)) (B0579.cell c) :=
        ((hE'.1 ψ hψ).2)
      have eq1 : ∫ x in B0579.cell c, b (s, x) i * (B0579.pd j ψ x : ℂ) =
          -∫ x in B0579.cell c, G (s, x) i j * (ψ x : ℂ) := hE.2 ψ hψ
      have eq2 : ∫ x in B0579.cell c, b' (s, x) i * (B0579.pd j ψ x : ℂ) =
          -∫ x in B0579.cell c, G' (s, x) i j * (ψ x : ℂ) := hE'.2 ψ hψ
      have eA : ∫ x in B0579.cell c, (b (s, x) i - b' (s, x) i) * (B0579.pd j ψ x : ℂ) =
          (∫ x in B0579.cell c, b (s, x) i * (B0579.pd j ψ x : ℂ)) -
            ∫ x in B0579.cell c, b' (s, x) i * (B0579.pd j ψ x : ℂ) := by
        rw [← integral_sub hA1 hB1]
        congr 1
        funext x
        ring
      have eB : ∫ x in B0579.cell c, (G (s, x) i j - G' (s, x) i j) * (ψ x : ℂ) =
          (∫ x in B0579.cell c, G (s, x) i j * (ψ x : ℂ)) -
            ∫ x in B0579.cell c, G' (s, x) i j * (ψ x : ℂ) := by
        rw [← integral_sub hA2 hB2]
        congr 1
        funext x
        ring
      show ∫ x in B0579.cell c, (b (s, x) i - b' (s, x) i) * (B0579.pd j ψ x : ℂ) =
        -∫ x in B0579.cell c, (G (s, x) i j - G' (s, x) i j) * (ψ x : ℂ)
      linear_combination eA + eB + eq1 - eq2
  -- integrable
  · intro Φ hΦ
    have hfun : flatIntegrand ν μ vel (fun p i j => F p i j - F' p i j)
        (fun p i => b p i - b' p i) Φ =
        fun p => flatIntegrand ν μ vel F b Φ p - flatIntegrand ν μ vel F' b' Φ p :=
      funext fun p => causalLin_flatIntegrand_sub ν μ vel F F' b b' Φ p
    rw [hfun]
    exact Integrable.sub (hb.integrable Φ hΦ) (hb'.integrable Φ hΦ)
  -- weak
  · intro Φ hΦ
    have hfun : flatIntegrand ν μ vel (fun p i j => F p i j - F' p i j)
        (fun p i => b p i - b' p i) Φ =
        fun p => flatIntegrand ν μ vel F b Φ p - flatIntegrand ν μ vel F' b' Φ p :=
      funext fun p => causalLin_flatIntegrand_sub ν μ vel F F' b b' Φ p
    rw [hfun, integral_sub (hb.integrable Φ hΦ) (hb'.integrable Φ hΦ), hb.weak Φ hΦ,
      hb'.weak Φ hΦ, sub_self]

end UnforcedLeray.Short.IIIa
