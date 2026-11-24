import UnforcedLeray.Short.PartIIa.Tasks.R01.EarlyCalculus.Closure

/-!
# Helper for `PartII-a:R01`, target `earlyCalculus`: closure of `EarlyBdd` under products

Source of record: `the November 2 reference manuscript`, lines 1294-1297 (the
zero-age bounds behind the early table), with the calculus `EarlyCalculus` of `Sub/R01.lean`.

Method. The jet `jet ℓ a b f = ∂_s^ℓ ∂_η^a ∂_q^b f` applies the `∂_q` iterates first. Peeling the
innermost derivative of a product gives the Leibniz rule for one directional derivative on the age
domain `AgeSet`: a sum of two products, each of total order one lower. No commutation of the three
derivatives is needed. The induction runs over the total order `n = a + b + ℓ`, generalizing over
all pairs of zero-age bounded families, and the constants are combined with `polyConst_add_le`.

Final statements: `earlyBdd_mul_core` (products of `EarlyBdd` families) and `earlyBdd_mul : EarlyMulClosure`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.EarlyCalc

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0187 UnforcedLeray.B0188
  UnforcedLeray.B0190

/-! ### Jets: congruence, splitting, and peeling the innermost derivative -/

/-- Equal functions on the age domain have equal jets there. -/
theorem jet_congr (ℓ a b : ℕ) {f g : ProfilePoint → ℝ} (h : EqOn f g AgeSet) :
    EqOn (jet ℓ a b f) (jet ℓ a b g) AgeSet :=
  iter_congr esDir ℓ (iter_congr eηDir a (iter_congr eqDir b h))

/-- The jet of a function that agrees on the age domain with a sum of two smooth functions splits
into the sum of the two jets. -/
theorem jet_split (ℓ a b : ℕ) {H A B : ProfilePoint → ℝ} (hA : ContDiffOn ℝ ∞ A AgeSet)
    (hB : ContDiffOn ℝ ∞ B AgeSet) (hH : EqOn H (fun y => A y + B y) AgeSet)
    {x : ProfilePoint} (hx : x ∈ AgeSet) :
    jet ℓ a b H x = jet ℓ a b A x + jet ℓ a b B x :=
  ((jet_congr ℓ a b hH).trans (jet_add ℓ a b hA hB)) hx

theorem jet_succ_q (ℓ a b : ℕ) (f : ProfilePoint → ℝ) :
    jet ℓ a (b + 1) f = jet ℓ a b (Dir eqDir f) := by
  unfold jet
  rw [Function.iterate_succ_apply]

theorem jet_succ_eta (ℓ a : ℕ) (f : ProfilePoint → ℝ) :
    jet ℓ (a + 1) 0 f = jet ℓ a 0 (Dir eηDir f) := by
  unfold jet
  simp only [Function.iterate_zero, id_eq, Function.iterate_succ_apply]

theorem jet_succ_s (ℓ : ℕ) (f : ProfilePoint → ℝ) :
    jet (ℓ + 1) 0 0 f = jet ℓ 0 0 (Dir esDir f) := by
  unfold jet
  simp only [Function.iterate_zero, id_eq, Function.iterate_succ_apply]

/-- Leibniz rule for the innermost `∂_q`. -/
theorem jet_mul_q (ℓ a b : ℕ) {f g : ProfilePoint → ℝ} (hf : ContDiffOn ℝ ∞ f AgeSet)
    (hg : ContDiffOn ℝ ∞ g AgeSet) {x : ProfilePoint} (hx : x ∈ AgeSet) :
    jet ℓ a (b + 1) (fun y => f y * g y) x =
      jet ℓ a b (fun y => Dir eqDir f y * g y) x + jet ℓ a b (fun y => f y * Dir eqDir g y) x := by
  have hH : EqOn (Dir eqDir (fun y => f y * g y))
      (fun y => Dir eqDir f y * g y + f y * Dir eqDir g y) AgeSet :=
    fun y hy => Dir_mul eqDir hf hg hy
  rw [jet_succ_q]
  exact jet_split ℓ a b ((smooth_Dir eqDir hf).mul hg) (hf.mul (smooth_Dir eqDir hg)) hH hx

/-- Leibniz rule for the innermost `∂_η`, when there is no `∂_q`. -/
theorem jet_mul_eta (ℓ a : ℕ) {f g : ProfilePoint → ℝ} (hf : ContDiffOn ℝ ∞ f AgeSet)
    (hg : ContDiffOn ℝ ∞ g AgeSet) {x : ProfilePoint} (hx : x ∈ AgeSet) :
    jet ℓ (a + 1) 0 (fun y => f y * g y) x =
      jet ℓ a 0 (fun y => Dir eηDir f y * g y) x + jet ℓ a 0 (fun y => f y * Dir eηDir g y) x := by
  have hH : EqOn (Dir eηDir (fun y => f y * g y))
      (fun y => Dir eηDir f y * g y + f y * Dir eηDir g y) AgeSet :=
    fun y hy => Dir_mul eηDir hf hg hy
  rw [jet_succ_eta]
  exact jet_split ℓ a 0 ((smooth_Dir eηDir hf).mul hg) (hf.mul (smooth_Dir eηDir hg)) hH hx

/-- Leibniz rule for the innermost `∂_s`, when there is no `∂_q` and no `∂_η`. -/
theorem jet_mul_s (ℓ : ℕ) {f g : ProfilePoint → ℝ} (hf : ContDiffOn ℝ ∞ f AgeSet)
    (hg : ContDiffOn ℝ ∞ g AgeSet) {x : ProfilePoint} (hx : x ∈ AgeSet) :
    jet (ℓ + 1) 0 0 (fun y => f y * g y) x =
      jet ℓ 0 0 (fun y => Dir esDir f y * g y) x + jet ℓ 0 0 (fun y => f y * Dir esDir g y) x := by
  have hH : EqOn (Dir esDir (fun y => f y * g y))
      (fun y => Dir esDir f y * g y + f y * Dir esDir g y) AgeSet :=
    fun y hy => Dir_mul esDir hf hg hy
  rw [jet_succ_s]
  exact jet_split ℓ 0 0 ((smooth_Dir esDir hf).mul hg) (hf.mul (smooth_Dir esDir hg)) hH hx

/-! ### Weighted bounds -/

/-- Weighted triangle inequality. -/
theorem weight_add_bound {w A B P Q : ℝ} (hw : 0 ≤ w) (h1 : w * |A| ≤ P) (h2 : w * |B| ≤ Q) :
    w * |A + B| ≤ P + Q := by
  calc w * |A + B| ≤ w * (|A| + |B|) := mul_le_mul_of_nonneg_left (abs_add_le _ _) hw
    _ = w * |A| + w * |B| := by ring
    _ ≤ P + Q := add_le_add h1 h2

/-- Product of two polynomial constants, with the constants made nonnegative. -/
theorem polyConst_mul_le {C₁ C₂ : ℝ} {d₁ d₂ : ℕ} {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (h1 : 0 ≤ polyConst C₁ d₁ ν c) (h2 : 0 ≤ polyConst C₂ d₂ ν c) :
    polyConst C₁ d₁ ν c * polyConst C₂ d₂ ν c ≤
      polyConst (max C₁ 0 * max C₂ 0) (d₁ + d₂) ν c := by
  have e1 : polyConst C₁ d₁ ν c ≤ polyConst (max C₁ 0) d₁ ν c :=
    polyConst_mono hν hc (le_max_left _ _) (le_max_right _ _) le_rfl
  have e2 : polyConst C₂ d₂ ν c ≤ polyConst (max C₂ 0) d₂ ν c :=
    polyConst_mono hν hc (le_max_left _ _) (le_max_right _ _) le_rfl
  have hb : 0 ≤ polyConst (max C₁ 0) d₁ ν c := le_trans h1 e1
  have e3 : polyConst C₁ d₁ ν c * polyConst C₂ d₂ ν c ≤
      polyConst (max C₁ 0) d₁ ν c * polyConst (max C₂ 0) d₂ ν c :=
    mul_le_mul e1 e2 h2 hb
  have e4 : polyConst (max C₁ 0) d₁ ν c * polyConst (max C₂ 0) d₂ ν c =
      polyConst (max C₁ 0 * max C₂ 0) (d₁ + d₂) ν c := by
    unfold polyConst
    rw [pow_add]
    ring
  exact e3.trans (le_of_eq e4)

/-! ### The product bound, by induction on the total order -/

/-- Base case: order zero, the product of the weight-`m` bound of `F` and the weight-zero bound
of `G`. -/
theorem mul_jet_zero (ρ : ℝ) (F G : ProfFam) (hF : EarlyBdd ρ F) (hG : EarlyBdd ρ G) (m : ℕ) :
    ∃ (ν₀ C : ℝ) (d : ℕ), 0 < ν₀ ∧
      ∀ ν ∈ Ioo 0 ν₀, ∀ ψ p : ProfilePoint → ℝ, IsExactPlanarTrain ν (ν ^ (-ρ)) ψ p →
        ∀ x : ProfilePoint, 0 < x.2.2 → x.2.2 ≤ 1 →
          (1 + x.2.1 ^ 2) ^ m * |jet 0 0 0 (fun y => F ν ψ p y * G ν ψ p y) x| ≤
            polyConst C d ν (ν ^ (-ρ)) := by
  obtain ⟨ν₁, C₁, d₁, hν₁, H₁⟩ := hF.bound0 m
  obtain ⟨ν₂, C₂, d₂, hν₂, H₂⟩ := hG.bound0 0
  refine ⟨min ν₁ ν₂, max C₁ 0 * max C₂ 0, d₁ + d₂, lt_min hν₁ hν₂,
    fun ν hν ψ p hψ x hx0 hx1 => ?_⟩
  have hν0 : 0 < ν := hν.1
  have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν0 _
  have hνX : ν ∈ Ioo 0 ν₁ := ⟨hν0, lt_of_lt_of_le hν.2 (min_le_left _ _)⟩
  have hνY : ν ∈ Ioo 0 ν₂ := ⟨hν0, lt_of_lt_of_le hν.2 (min_le_right _ _)⟩
  have t1 := H₁ ν hνX ψ p hψ x hx0 hx1
  have t2 := H₂ ν hνY ψ p hψ x hx0 hx1
  simp only [pow_zero, one_mul] at t2
  have w : 0 ≤ (1 + x.2.1 ^ 2) ^ m := by positivity
  have hP1 : 0 ≤ polyConst C₁ d₁ ν (ν ^ (-ρ)) := le_trans (mul_nonneg w (abs_nonneg _)) t1
  have hP2 : 0 ≤ polyConst C₂ d₂ ν (ν ^ (-ρ)) := le_trans (abs_nonneg _) t2
  have e : jet 0 0 0 (fun y => F ν ψ p y * G ν ψ p y) x = F ν ψ p x * G ν ψ p x := rfl
  rw [e, abs_mul]
  calc (1 + x.2.1 ^ 2) ^ m * (|F ν ψ p x| * |G ν ψ p x|)
      = ((1 + x.2.1 ^ 2) ^ m * |F ν ψ p x|) * |G ν ψ p x| := by ring
    _ ≤ polyConst C₁ d₁ ν (ν ^ (-ρ)) * polyConst C₂ d₂ ν (ν ^ (-ρ)) :=
        mul_le_mul t1 t2 (abs_nonneg _) hP1
    _ ≤ polyConst (max C₁ 0 * max C₂ 0) (d₁ + d₂) ν (ν ^ (-ρ)) :=
        polyConst_mul_le hν0 hc hP1 hP2

/-- **Product bound for the jets of total order `n`.** For all pairs of zero-age bounded families
`F, G` and all weights `m` and jet indices `a, b, ℓ` with `a + b + ℓ = n`, the jet
`∂_s^ℓ ∂_η^a ∂_q^b (F G)` satisfies the zero-age bound with weight `(1+η²)^m`. -/
theorem mul_jet_all (ρ : ℝ) : ∀ n : ℕ, ∀ (F G : ProfFam), EarlyBdd ρ F → EarlyBdd ρ G →
    ∀ (m a b ℓ : ℕ), a + b + ℓ = n →
      ∃ (ν₀ C : ℝ) (d : ℕ), 0 < ν₀ ∧ ∀ ν ∈ Ioo 0 ν₀, ∀ ψ p : ProfilePoint → ℝ,
        IsExactPlanarTrain ν (ν ^ (-ρ)) ψ p → ∀ x : ProfilePoint, 0 < x.2.2 → x.2.2 ≤ 1 →
          (1 + x.2.1 ^ 2) ^ m * |jet ℓ a b (fun y => F ν ψ p y * G ν ψ p y) x| ≤
            polyConst C d ν (ν ^ (-ρ)) := by
  intro n
  induction n with
  | zero =>
    intro F G hF hG m a b ℓ hn
    obtain rfl : a = 0 := by omega
    obtain rfl : b = 0 := by omega
    obtain rfl : ℓ = 0 := by omega
    exact mul_jet_zero ρ F G hF hG m
  | succ n ih =>
    intro F G hF hG m a b ℓ hn
    rcases b with _ | b
    · rcases a with _ | a
      · rcases ℓ with _ | ℓ
        · exfalso
          omega
        · -- the innermost derivative is `∂_s`
          obtain ⟨ν₁, C₁, d₁, hν₁, H₁⟩ :=
            ih (fun ν ψ p => partialAge (F ν ψ p)) G (earlyBdd_dAge hF) hG m 0 0 ℓ (by omega)
          obtain ⟨ν₂, C₂, d₂, hν₂, H₂⟩ :=
            ih F (fun ν ψ p => partialAge (G ν ψ p)) hF (earlyBdd_dAge hG) m 0 0 ℓ (by omega)
          refine ⟨min ν₁ ν₂, max C₁ 0 + max C₂ 0, max d₁ d₂, lt_min hν₁ hν₂,
            fun ν hν ψ p hψ x hx0 hx1 => ?_⟩
          have hν0 : 0 < ν := hν.1
          have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν0 _
          have hνX : ν ∈ Ioo 0 ν₁ := ⟨hν0, lt_of_lt_of_le hν.2 (min_le_left _ _)⟩
          have hνY : ν ∈ Ioo 0 ν₂ := ⟨hν0, lt_of_lt_of_le hν.2 (min_le_right _ _)⟩
          have t1 := H₁ ν hνX ψ p hψ x hx0 hx1
          have t2 := H₂ ν hνY ψ p hψ x hx0 hx1
          have w : 0 ≤ (1 + x.2.1 ^ 2) ^ m := by positivity
          rw [jet_mul_s ℓ (hF.1 ν hν0 ψ p hψ) (hG.1 ν hν0 ψ p hψ) (show x ∈ AgeSet from hx0)]
          exact (weight_add_bound w t1 t2).trans (polyConst_add_le hν0 hc)
      · -- the innermost derivative is `∂_η`
        obtain ⟨ν₁, C₁, d₁, hν₁, H₁⟩ :=
          ih (fun ν ψ p => partialEta (F ν ψ p)) G (earlyBdd_dEta hF) hG m a 0 ℓ (by omega)
        obtain ⟨ν₂, C₂, d₂, hν₂, H₂⟩ :=
          ih F (fun ν ψ p => partialEta (G ν ψ p)) hF (earlyBdd_dEta hG) m a 0 ℓ (by omega)
        refine ⟨min ν₁ ν₂, max C₁ 0 + max C₂ 0, max d₁ d₂, lt_min hν₁ hν₂,
          fun ν hν ψ p hψ x hx0 hx1 => ?_⟩
        have hν0 : 0 < ν := hν.1
        have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν0 _
        have hνX : ν ∈ Ioo 0 ν₁ := ⟨hν0, lt_of_lt_of_le hν.2 (min_le_left _ _)⟩
        have hνY : ν ∈ Ioo 0 ν₂ := ⟨hν0, lt_of_lt_of_le hν.2 (min_le_right _ _)⟩
        have t1 := H₁ ν hνX ψ p hψ x hx0 hx1
        have t2 := H₂ ν hνY ψ p hψ x hx0 hx1
        have w : 0 ≤ (1 + x.2.1 ^ 2) ^ m := by positivity
        rw [jet_mul_eta ℓ a (hF.1 ν hν0 ψ p hψ) (hG.1 ν hν0 ψ p hψ) (show x ∈ AgeSet from hx0)]
        exact (weight_add_bound w t1 t2).trans (polyConst_add_le hν0 hc)
    · -- the innermost derivative is `∂_q`
      obtain ⟨ν₁, C₁, d₁, hν₁, H₁⟩ :=
        ih (fun ν ψ p => partialQ (F ν ψ p)) G (earlyBdd_dQ hF) hG m a b ℓ (by omega)
      obtain ⟨ν₂, C₂, d₂, hν₂, H₂⟩ :=
        ih F (fun ν ψ p => partialQ (G ν ψ p)) hF (earlyBdd_dQ hG) m a b ℓ (by omega)
      refine ⟨min ν₁ ν₂, max C₁ 0 + max C₂ 0, max d₁ d₂, lt_min hν₁ hν₂,
        fun ν hν ψ p hψ x hx0 hx1 => ?_⟩
      have hν0 : 0 < ν := hν.1
      have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν0 _
      have hνX : ν ∈ Ioo 0 ν₁ := ⟨hν0, lt_of_lt_of_le hν.2 (min_le_left _ _)⟩
      have hνY : ν ∈ Ioo 0 ν₂ := ⟨hν0, lt_of_lt_of_le hν.2 (min_le_right _ _)⟩
      have t1 := H₁ ν hνX ψ p hψ x hx0 hx1
      have t2 := H₂ ν hνY ψ p hψ x hx0 hx1
      have w : 0 ≤ (1 + x.2.1 ^ 2) ^ m := by positivity
      rw [jet_mul_q ℓ a b (hF.1 ν hν0 ψ p hψ) (hG.1 ν hν0 ψ p hψ) (show x ∈ AgeSet from hx0)]
      exact (weight_add_bound w t1 t2).trans (polyConst_add_le hν0 hc)

/-- Closure of `EarlyBdd` under products, for all `ρ` (the bound is a statement about the jets of
the product family). -/
theorem earlyBdd_mul_core {ρ : ℝ} {X Y : ProfFam} (hX : EarlyBdd ρ X) (hY : EarlyBdd ρ Y) :
    EarlyBdd ρ (fun ν ψ p => X ν ψ p * Y ν ψ p) := by
  unfold EarlyBdd at hX hY ⊢
  refine ⟨fun ν hν ψ p hψ => (hX.1 ν hν ψ p hψ).mul (hY.1 ν hν ψ p hψ), fun m a b ℓ => ?_⟩
  obtain ⟨ν₀, C, d, hν₀, H⟩ := mul_jet_all ρ (a + b + ℓ) X Y hX hY m a b ℓ rfl
  exact ⟨ν₀, C, d, hν₀, H⟩

end UnforcedLeray.Short.PartIIa.EarlyCalc

namespace UnforcedLeray.Short.PartIIa

/-- The product field of `EarlyCalculus`: bounded families are closed under pointwise products. -/
def EarlyMulClosure : Prop :=
  ∀ (ρ : ℝ) (X Y : ProfFam), 1 / 2 < ρ → EarlyBdd ρ X → EarlyBdd ρ Y →
    EarlyBdd ρ (fun ν ψ p => X ν ψ p * Y ν ψ p)

/-- **The product field.** Holds for every `ρ`; the hypothesis `1 / 2 < ρ` is not used. -/
theorem earlyBdd_mul : EarlyMulClosure := by
  intro ρ X Y _ hX hY
  exact EarlyCalc.earlyBdd_mul_core hX hY

end UnforcedLeray.Short.PartIIa
