import UnforcedLeray.Short.PartIIa.Calc.JetClass

/-!
# Part II-a, jet-class calculus: sizes of products (`WAlgMul`)

Target: `UnforcedLeray.Short.PartIIa.Jet.wAlgMul : WAlgMul` (`Calc/JetClass.lean`).

Source of record: `the November 2 reference manuscript`, lines 1269-1272
(sizes of products in the late table).

* Weighted sizes multiply: `(1+η²/s)^m |FG| ≤ ((1+η²/s)^m |F|) |G|`, the second factor at weight
  `0` (`s^{-a} s^{-a'} = s^{-(a+a')}`, `polyConst C d · polyConst C' d' = polyConst (C C') (d+d')`).
* A weight-`0` weighted bound on `F` times an exponentially small `G` is exponentially small;
  the order of the factors is irrelevant (`mul_comm`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.Jet

/-- Product of weighted sizes: `s^{-a} · s^{-a'} = s^{-(a+a')}`. -/
theorem wam_mul_W (a a' : ℝ) (F G : Fam) (hF : WW a F) (hG : WW a' G) :
    WW (a + a') (F * G) := by
  intro ρ m hρ
  obtain ⟨C₁, d₁, ν₁, hν₁, H₁⟩ := hF ρ m hρ
  obtain ⟨C₂, d₂, ν₂, hν₂, H₂⟩ := hG ρ 0 hρ
  refine ⟨C₁ * C₂, d₁ + d₂, min ν₁ ν₂, lt_min hν₁ hν₂, fun ν hν hνle tr htr => ?_⟩
  have hc : 0 < ν ^ (-ρ) := rpow_neg_pos hν
  have h1 := H₁ ν hν (hνle.trans (min_le_left _ _)) tr htr
  have h2 := H₂ ν hν (hνle.trans (min_le_right _ _)) tr htr
  have hB1 : 0 ≤ polyConst C₁ d₁ ν (ν ^ (-ρ)) := WtdBound.nonneg h1
  have e2 : polyConst (C₁ * C₂) (d₁ + d₂) ν (ν ^ (-ρ)) =
      polyConst C₁ d₁ ν (ν ^ (-ρ)) * polyConst C₂ d₂ ν (ν ^ (-ρ)) := by
    unfold polyConst
    rw [pow_add]
    ring
  intro x hx
  have hpos : 0 < x.2.2 := by linarith
  have e : x.2.2 ^ (-(a + a')) = x.2.2 ^ (-a) * x.2.2 ^ (-a') := by
    rw [← Real.rpow_add hpos, neg_add]
  have hX := h1 x hx
  have hY := h2 x hx
  rw [pow_zero, one_mul] at hY
  have hnn : 0 ≤ polyConst C₁ d₁ ν (ν ^ (-ρ)) * x.2.2 ^ (-a) :=
    mul_nonneg hB1 (Real.rpow_nonneg hpos.le _)
  have hprod := mul_le_mul hX hY (abs_nonneg _) hnn
  show (1 + x.2.1 ^ 2 / x.2.2) ^ m * |F ν (ν ^ (-ρ)) tr x * G ν (ν ^ (-ρ)) tr x| ≤
    polyConst (C₁ * C₂) (d₁ + d₂) ν (ν ^ (-ρ)) * x.2.2 ^ (-(a + a'))
  rw [abs_mul, e2, e]
  calc (1 + x.2.1 ^ 2 / x.2.2) ^ m * (|F ν (ν ^ (-ρ)) tr x| * |G ν (ν ^ (-ρ)) tr x|)
      = ((1 + x.2.1 ^ 2 / x.2.2) ^ m * |F ν (ν ^ (-ρ)) tr x|) * |G ν (ν ^ (-ρ)) tr x| := by
        ring
    _ ≤ (polyConst C₁ d₁ ν (ν ^ (-ρ)) * x.2.2 ^ (-a)) *
          (polyConst C₂ d₂ ν (ν ^ (-ρ)) * x.2.2 ^ (-a')) := hprod
    _ = polyConst C₁ d₁ ν (ν ^ (-ρ)) * polyConst C₂ d₂ ν (ν ^ (-ρ)) *
          (x.2.2 ^ (-a) * x.2.2 ^ (-a')) := by ring

/-- A weight-`0` weighted bound times an exponentially small bound is exponentially small. -/
theorem wam_mul_E (F G : Fam) (hF : WW 0 F) (hG : WE G) : WE (F * G) := by
  intro ρ m hρ
  obtain ⟨C₁, d₁, ν₁, hν₁, H₁⟩ := hF ρ 0 hρ
  obtain ⟨C₂, d₂, κ, ν₂, hκ, hν₂, H₂⟩ := hG ρ m hρ
  refine ⟨C₁ * C₂, d₁ + d₂, κ, min ν₁ ν₂, hκ, lt_min hν₁ hν₂,
    fun ν hν hνle tr htr => ?_⟩
  have hc : 0 < ν ^ (-ρ) := rpow_neg_pos hν
  have h1 := H₁ ν hν (hνle.trans (min_le_left _ _)) tr htr
  have h2 := H₂ ν hν (hνle.trans (min_le_right _ _)) tr htr
  have hB1 : 0 ≤ polyConst C₁ d₁ ν (ν ^ (-ρ)) := WtdBound.nonneg h1
  have e2 : polyConst (C₁ * C₂) (d₁ + d₂) ν (ν ^ (-ρ)) =
      polyConst C₁ d₁ ν (ν ^ (-ρ)) * polyConst C₂ d₂ ν (ν ^ (-ρ)) := by
    unfold polyConst
    rw [pow_add]
    ring
  intro x hx
  have hX := h1 x hx
  rw [pow_zero, one_mul, neg_zero, Real.rpow_zero, mul_one] at hX
  have hY := h2 x hx
  have hw : 0 ≤ (1 + x.2.1 ^ 2 / x.2.2) ^ m := weight_nonneg m hx
  have hE : 0 ≤ (1 + x.2.1 ^ 2 / x.2.2) ^ m * |G ν (ν ^ (-ρ)) tr x| :=
    mul_nonneg hw (abs_nonneg _)
  show (1 + x.2.1 ^ 2 / x.2.2) ^ m * |F ν (ν ^ (-ρ)) tr x * G ν (ν ^ (-ρ)) tr x| ≤
    polyConst (C₁ * C₂) (d₁ + d₂) ν (ν ^ (-ρ)) * Real.exp (-(κ * ν * x.2.2 / (ν ^ (-ρ)) ^ 2))
  rw [abs_mul, e2]
  calc (1 + x.2.1 ^ 2 / x.2.2) ^ m * (|F ν (ν ^ (-ρ)) tr x| * |G ν (ν ^ (-ρ)) tr x|)
      = |F ν (ν ^ (-ρ)) tr x| * ((1 + x.2.1 ^ 2 / x.2.2) ^ m * |G ν (ν ^ (-ρ)) tr x|) := by
        ring
    _ ≤ polyConst C₁ d₁ ν (ν ^ (-ρ)) * ((1 + x.2.1 ^ 2 / x.2.2) ^ m * |G ν (ν ^ (-ρ)) tr x|) :=
        mul_le_mul_of_nonneg_right hX hE
    _ ≤ polyConst C₁ d₁ ν (ν ^ (-ρ)) *
          (polyConst C₂ d₂ ν (ν ^ (-ρ)) * Real.exp (-(κ * ν * x.2.2 / (ν ^ (-ρ)) ^ 2))) :=
        mul_le_mul_of_nonneg_left hY hB1
    _ = polyConst C₁ d₁ ν (ν ^ (-ρ)) * polyConst C₂ d₂ ν (ν ^ (-ρ)) *
          Real.exp (-(κ * ν * x.2.2 / (ν ^ (-ρ)) ^ 2)) := by ring

/-- **Sizes multiply** (`WAlgMul`). -/
theorem wAlgMul : WAlgMul := by
  unfold WAlgMul
  refine ⟨fun a a' F G hF hG => wam_mul_W a a' F G hF hG, ?_⟩
  intro F G hF hG
  refine ⟨wam_mul_E F G hF hG, ?_⟩
  rw [mul_comm]
  exact wam_mul_E F G hF hG

end UnforcedLeray.Short.PartIIa.Jet
