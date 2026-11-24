import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_6_1_3_1_org_1_org_1_2_2_1
import UnforcedLeray.Short.PartI.StatementsTrain

/-!
# `PsiJetWtd` from the transverse tails and the band bound

Source: `the November 2 reference manuscript`,
SP 460-467 (`sct:transverse` = `PartI.TrainTransverseTails`, `StatementsTrain.lean:284`: for orders
`ℓ, j` the constants `b, C₀, C', C, N, ν₀` are fixed before the age bound `S_*`, and
`‖∂_s^ℓ D^j ψ(s, z)‖ ≤ P_{S_*} {e^{-bl/c} + e^{-bl²/(C₀+νS_*)}}` for `|η| ≥ C'/ν + 2 + l`), SP 247-258
(thresholds after the finite collection of orders).

* Outside the band, `|η| > R`, with `l = |η| - C'/ν - 2`: `(1+|η|)^m ≤ (1 + C'/ν + 2)^m (1+l)^m`, and
  `(1+l)^m (e^{-bl/c} + e^{-bl²/D})` is bounded at fixed `b, c, D` (absorption, proved here).
* Inside the band, `|η| ≤ R`: `PsiJetInterior` (the jets of `ψ` on `0 < s ≤ S`, `|η| ≤ R`, all `q`,
  given the bound of `∂_s^ℓ ψ` on the band edge `η = R`, which is the tail of order `(ℓ, 0)` at
  `l = 0`).

The threshold is the minimum of those of `TrainTransverseTails` at the orders `(ℓ, j)` and `(ℓ, 0)`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open Set Filter Topology
open UnforcedLeray.Cyl (Plane)

/-- **Jets of the train stream on the transverse band, bounded ages** (SP 261-288: the train is
smooth on `[0,∞) × ℝ²` with `v = ∇^⊥ψ`, `B0140.IsTrain.smooth_v`, `stream`; periodic in `q`,
`IsTrain.periodic_v`; SP 468-478: on the band all jets are bounded at fixed parameters).  For a BUC
train at `ν, c > 0`, orders `ℓ, j`, an age bound `S` and a band `|η| ≤ R`: if `∂_s^ℓ ψ` is bounded by
`K` on the band edge `η = R` for `0 < s ≤ S`, then `‖∂_s^ℓ D^j ψ(s, z)‖ ≤ C` for `0 < s ≤ S`,
`|z.2| ≤ R`.  (For `j ≥ 1`, `D_z ψ` is a fixed linear image of `v`, whose age/space jets are
continuous up to `s = 0` and `c`-periodic in `q`, hence bounded on `[0, S] × ℝ × [-R, R]`; for
`j = 0`, compare with the edge value along `η` by the mean value theorem.) -/
def PsiJetInterior : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr : B0140.TrainSol ν c, Short.PartI.IsBUCTrain tr →
    ∀ (ℓ j : ℕ) (S R K : ℝ),
      (∀ s : ℝ, 0 < s → s ≤ S → ∀ q : ℝ, ‖Short.PartI.ageJet ℓ 0 tr.ψ s (q, R)‖ ≤ K) →
      ∃ C : ℝ, ∀ s : ℝ, 0 < s → s ≤ S → ∀ z : Plane, |z.2| ≤ R →
        ‖Short.PartI.ageJet ℓ j tr.ψ s z‖ ≤ C

namespace PsiJetWtdSub

private theorem pow_mul_exp_neg_le (k : ℕ) {β x : ℝ} (hβ : 0 < β) (hx : 0 ≤ x) :
    x ^ k * Real.exp (-(β * x)) ≤ k.factorial / β ^ k := by
  have h := Real.pow_div_factorial_le_exp (β * x) (by positivity) k
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  rw [div_le_iff₀ hf, mul_pow] at h
  have hβk : (0 : ℝ) < β ^ k := by positivity
  rw [le_div_iff₀ hβk]
  have e1 : Real.exp (-(β * x)) * Real.exp (β * x) = 1 := by
    rw [← Real.exp_add]; simp
  calc x ^ k * Real.exp (-(β * x)) * β ^ k
      = (β ^ k * x ^ k) * Real.exp (-(β * x)) := by ring
    _ ≤ (Real.exp (β * x) * k.factorial) * Real.exp (-(β * x)) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = k.factorial := by
        calc (Real.exp (β * x) * k.factorial) * Real.exp (-(β * x))
            = (Real.exp (-(β * x)) * Real.exp (β * x)) * k.factorial := by ring
          _ = k.factorial := by rw [e1, one_mul]

/-- The exponential core: `(1+l)^m e^{-b l} ≤ e^b m!/b^m`. -/
private theorem core1 (m : ℕ) {b l : ℝ} (hb : 0 < b) (hl : 0 ≤ l) :
    (1 + l) ^ m * Real.exp (-(b * l)) ≤ Real.exp b * (m.factorial / b ^ m) := by
  have h := pow_mul_exp_neg_le m hb (by linarith : 0 ≤ 1 + l)
  have : Real.exp (-(b * l)) = Real.exp b * Real.exp (-(b * (1 + l))) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [this]
  calc (1 + l) ^ m * (Real.exp b * Real.exp (-(b * (1 + l))))
      = Real.exp b * ((1 + l) ^ m * Real.exp (-(b * (1 + l)))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (Real.exp_pos _).le

/-- The Gaussian core: `(1+l)^m e^{-b l²/D} ≤ e^{b/D} m! (2D/b)^m` for `D > 0`. -/
private theorem core2 (m : ℕ) {b D l : ℝ} (hb : 0 < b) (hD0 : 0 < D) (hl : 0 ≤ l) :
    (1 + l) ^ m * Real.exp (-(b * l ^ 2 / D)) ≤
      Real.exp (b / D) * (m.factorial / (b / (2 * D)) ^ m) := by
  set x := 1 + l with hx
  have hx1 : 1 ≤ x := by linarith
  have hl2 : x ^ 2 ≤ 2 + 2 * l ^ 2 := by nlinarith [sq_nonneg (l - 1)]
  have hβ : 0 < b / (2 * D) := by positivity
  have h := pow_mul_exp_neg_le m hβ (by positivity : 0 ≤ x ^ 2)
  have e1 : Real.exp (-(b * l ^ 2 / D)) ≤
      Real.exp (b / D) * Real.exp (-(b / (2 * D) * x ^ 2)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have h2 : b / (2 * D) * x ^ 2 ≤ b / (2 * D) * (2 + 2 * l ^ 2) :=
      mul_le_mul_of_nonneg_left hl2 hβ.le
    have h3 : b / (2 * D) * (2 + 2 * l ^ 2) = b / D + b * l ^ 2 / D := by
      field_simp
    linarith
  have hxm : x ^ m ≤ (x ^ 2) ^ m := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ hx1 (by omega)
  calc x ^ m * Real.exp (-(b * l ^ 2 / D))
      ≤ x ^ m * (Real.exp (b / D) * Real.exp (-(b / (2 * D) * x ^ 2))) :=
        mul_le_mul_of_nonneg_left e1 (by positivity)
    _ ≤ (x ^ 2) ^ m * (Real.exp (b / D) * Real.exp (-(b / (2 * D) * x ^ 2))) :=
        mul_le_mul_of_nonneg_right hxm (by positivity)
    _ = Real.exp (b / D) * ((x ^ 2) ^ m * Real.exp (-(b / (2 * D) * x ^ 2))) := by ring
    _ ≤ Real.exp (b / D) * (m.factorial / (b / (2 * D)) ^ m) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le

/-- **Absorption of a polynomial weight by the transverse tail** (SP 463-467 at fixed `b, c, D`):
`(1+l)^m (e^{-bl/c} + e^{-bl²/D})` is bounded on `l ≥ 0`. -/
theorem tailAbsorb (m : ℕ) {b c D : ℝ} (hb : 0 < b) (hc : 0 < c) (hD : 0 < D) :
    ∃ A : ℝ, ∀ l : ℝ, 0 ≤ l →
      (1 + l) ^ m * (Real.exp (-(b * l / c)) + Real.exp (-(b * l ^ 2 / D))) ≤ A := by
  refine ⟨Real.exp (b / c) * (m.factorial / (b / c) ^ m) +
    Real.exp (b / D) * (m.factorial / (b / (2 * D)) ^ m), fun l hl => ?_⟩
  have h1 := core1 m (div_pos hb hc) hl
  have h2 := core2 m hb hD hl
  have e : -(b * l / c) = -(b / c * l) := by ring
  rw [mul_add, e]
  exact add_le_add h1 h2

end PsiJetWtdSub

open PsiJetWtdSub in
/-- **`PsiJetWtd` from `sct:transverse` and the band bound** (SP 460-467, 247-258). -/
theorem psiJetWtd_of (hT : Short.PartI.TrainTransverseTails) (hI : PsiJetInterior) :
    PsiJetWtd := by
  intro ρ hρ ℓ j
  obtain ⟨b, C₀, C', hb, hC₀, hC', C, N, ν₁, hC, hν₁, hT1⟩ := hT ρ hρ ℓ j
  obtain ⟨b₀, D₀, D', hb₀, hD₀, hD', K₀, N₀, ν₂, hK₀, hν₂, hT0⟩ := hT ρ hρ ℓ 0
  refine ⟨min ν₁ ν₂, lt_min hν₁ hν₂, fun ν c hν hle hc tr htr m S => ?_⟩
  have hle1 : ν ≤ ν₁ := hle.trans (min_le_left _ _)
  have hle2 : ν ≤ ν₂ := hle.trans (min_le_right _ _)
  subst hc
  have hc0 : 0 < Short.PartI.trainPeriod ρ ν := Real.rpow_pos_of_pos hν _
  set S' : ℝ := max S 0 with hS'
  have hS'0 : 0 ≤ S' := le_max_right _ _
  have hSS' : S ≤ S' := le_max_left _ _
  set A₁ : ℝ := C' / ν + 2 with hA₁
  have hA₁0 : 0 < A₁ := by positivity
  set R : ℝ := max A₁ (D' / ν + 2) with hR
  have hR0 : 0 < R := lt_of_lt_of_le hA₁0 (le_max_left _ _)
  -- the band edge `η = R`: the tail of order `(ℓ, 0)` at `l = 0`
  have hedge : ∀ s : ℝ, 0 < s → s ≤ S' → ∀ q : ℝ,
      ‖Short.PartI.ageJet ℓ 0 tr.ψ s (q, R)‖ ≤
        Short.PartI.polyPS K₀ N₀ ν (Short.PartI.trainPeriod ρ ν) S' *
          (Real.exp (-(b₀ * 0 / Short.PartI.trainPeriod ρ ν)) +
            Real.exp (-(b₀ * 0 ^ 2 / (D₀ + ν * S')))) := by
    intro s hs hsS q
    have hz : D' / ν + 2 + 0 ≤ |((q, R) : Plane).2| := by
      rw [abs_of_pos hR0, add_zero]
      exact le_max_right _ _
    exact (hT0 S' hS'0 ν hν hle2 tr htr 0 le_rfl s hs hsS (q, R) hz).1
  obtain ⟨Ci, hCi⟩ := hI ν _ hν hc0 tr htr ℓ j S' R _ hedge
  -- absorption of the weight outside the band
  have hDpos : 0 < C₀ + ν * S' := by positivity
  obtain ⟨Aab, hAab⟩ := tailAbsorb m hb hc0 hDpos
  set P : ℝ := Short.PartI.polyPS C N ν (Short.PartI.trainPeriod ρ ν) S' with hP
  have hP0 : 0 ≤ P := by
    rw [hP]; unfold Short.PartI.polyPS
    have : 0 ≤ (1 + Short.PartI.trainPeriod ρ ν + ν⁻¹) * (1 + S') := by positivity
    positivity
  refine ⟨(1 + R) ^ m * |Ci| + (1 + A₁) ^ m * (P * |Aab|), fun s hs hsS z => ?_⟩
  have hsS' : s ≤ S' := hsS.trans hSS'
  have hf0 : 0 ≤ ‖Short.PartI.ageJet ℓ j tr.ψ s z‖ := norm_nonneg _
  have hT2 : 0 ≤ (1 + A₁) ^ m * (P * |Aab|) := by positivity
  have hT3 : 0 ≤ (1 + R) ^ m * |Ci| := by positivity
  by_cases hz : |z.2| ≤ R
  · -- inside the band
    have h1 : ‖Short.PartI.ageJet ℓ j tr.ψ s z‖ ≤ |Ci| := (hCi s hs hsS' z hz).trans (le_abs_self _)
    have hw : (1 + |z.2|) ^ m ≤ (1 + R) ^ m :=
      pow_le_pow_left₀ (by positivity) (by linarith) m
    calc (1 + |z.2|) ^ m * ‖Short.PartI.ageJet ℓ j tr.ψ s z‖
        ≤ (1 + R) ^ m * |Ci| := mul_le_mul hw h1 hf0 (by positivity)
      _ ≤ _ := le_add_of_nonneg_right hT2
  · -- outside the band
    push Not at hz
    have hAR : A₁ ≤ R := le_max_left _ _
    set l : ℝ := |z.2| - A₁ with hl
    have hl0 : 0 ≤ l := by rw [hl]; linarith
    have hzl : C' / ν + 2 + l ≤ |z.2| := by rw [hl, hA₁]; linarith
    have ht : ‖Short.PartI.ageJet ℓ j tr.ψ s z‖ ≤
        P * (Real.exp (-(b * l / Short.PartI.trainPeriod ρ ν)) +
          Real.exp (-(b * l ^ 2 / (C₀ + ν * S')))) :=
      (hT1 S' hS'0 ν hν hle1 tr htr l hl0 s hs hsS' z hzl).1
    have hw : (1 + |z.2|) ^ m ≤ (1 + A₁) ^ m * (1 + l) ^ m := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      have : |z.2| = A₁ + l := by rw [hl]; ring
      rw [this]; nlinarith [mul_nonneg hA₁0.le hl0]
    have hE0 : 0 ≤ Real.exp (-(b * l / Short.PartI.trainPeriod ρ ν)) +
        Real.exp (-(b * l ^ 2 / (C₀ + ν * S'))) := by positivity
    have hab := hAab l hl0
    calc (1 + |z.2|) ^ m * ‖Short.PartI.ageJet ℓ j tr.ψ s z‖
        ≤ ((1 + A₁) ^ m * (1 + l) ^ m) *
            (P * (Real.exp (-(b * l / Short.PartI.trainPeriod ρ ν)) +
              Real.exp (-(b * l ^ 2 / (C₀ + ν * S'))))) :=
          mul_le_mul hw ht hf0 (by positivity)
      _ = (1 + A₁) ^ m * (P * ((1 + l) ^ m *
            (Real.exp (-(b * l / Short.PartI.trainPeriod ρ ν)) +
              Real.exp (-(b * l ^ 2 / (C₀ + ν * S')))))) := by ring
      _ ≤ (1 + A₁) ^ m * (P * |Aab|) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left (hab.trans (le_abs_self _)) hP0
      _ ≤ _ := le_add_of_nonneg_left hT3

end UnforcedLeray.Short.PartIIIb.Concrete
