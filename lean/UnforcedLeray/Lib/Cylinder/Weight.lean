import UnforcedLeray.Lib.Cylinder.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The centred seam weight `ρc` and the smooth periodic weight `ρw` (INF13, target CY02)


§5 CY02 and §4 "Not recommended (a)"; decision D12 of `scoping/README.md` §3 (keep both
weights, with a uniform equivalence).

* `ρc z = 1 + q² + η²` is the centred weight of `X_c = L²(C_c, (1+q²+η²)^m dq dη)`
  (`paper/main.tex` lines 4171-4184, unit B0242; lines 6166-6188, B0319; lines 6494-6518,
  B0343).  On the cell it is used through its restriction to `[-c/2, c/2] × ℝ`; it takes the
  same value on both seams (`ρc_neg_half`).
* `ρw ℓ z = 1 + (ℓ/π)² sin²(πq/ℓ) + η²` is a smooth `ℓ`-periodic weight (B0271, tex
  4569-4578: "a smooth periodic weight, uniformly comparable to (1+q²+η²)^m").

Uniform equivalence (D12): on the centred cell, `(4/π²) ρc ≤ ρw ℓ ≤ ρc` for every `ℓ > 0`
(`ρw_comparable`), hence `(4/π²)^m ρc^m ≤ ρw^m ≤ ρc^m` for `m ≥ 0` (`rpow_ρw_comparable`).
The constant `4/π²` does not depend on `ℓ`.

Main declarations: `ρw`, `ρc`, `contDiff_ρw`, `contDiff_ρc`, `isPeriodic_ρw`, `ρw_le_ρc`,
`ρw_comparable`, `rpow_ρw_comparable`, `ρw_dilate`, `integrable_rpow_neg_ρc`,
`integrableOn_rpow_neg_ρw`, `setIntegral_rpow_neg_ρw_le`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Real
open scoped ENNReal ContDiff

namespace UnforcedLeray.Cyl

/-- The smooth `ℓ`-periodic weight `1 + (ℓ/π)² sin²(πq/ℓ) + η²` (B0271, tex 4569-4578). -/
def ρw (ℓ : ℝ) (z : Plane) : ℝ := 1 + (ℓ / π) ^ 2 * Real.sin (π * z.1 / ℓ) ^ 2 + z.2 ^ 2

/-- The centred weight `1 + q² + η²` (B0242, tex 4171-4184). -/
def ρc (z : Plane) : ℝ := 1 + z.1 ^ 2 + z.2 ^ 2

theorem contDiff_ρw (ℓ : ℝ) : ContDiff ℝ ∞ (ρw ℓ) := by
  unfold ρw; fun_prop

theorem contDiff_ρc : ContDiff ℝ ∞ ρc := by
  unfold ρc; fun_prop

theorem one_le_ρw (ℓ : ℝ) (z : Plane) : 1 ≤ ρw ℓ z := by
  unfold ρw; nlinarith [sq_nonneg (ℓ / π), sq_nonneg (Real.sin (π * z.1 / ℓ)), sq_nonneg z.2,
    mul_nonneg (sq_nonneg (ℓ / π)) (sq_nonneg (Real.sin (π * z.1 / ℓ)))]

theorem ρw_pos (ℓ : ℝ) (z : Plane) : 0 < ρw ℓ z := lt_of_lt_of_le one_pos (one_le_ρw ℓ z)

theorem one_le_ρc (z : Plane) : 1 ≤ ρc z := by
  unfold ρc; nlinarith [sq_nonneg z.1, sq_nonneg z.2]

theorem ρc_pos (z : Plane) : 0 < ρc z := lt_of_lt_of_le one_pos (one_le_ρc z)

/-- The centred weight agrees on the two seams `q = ± c/2`. -/
theorem ρc_neg_half (c η : ℝ) : ρc (-c / 2, η) = ρc (c / 2, η) := by
  simp only [ρc]; ring

theorem ρc_neg_fst (z : Plane) : ρc (-z.1, z.2) = ρc z := by
  simp only [ρc]; ring

theorem isPeriodic_ρw {ℓ : ℝ} (hℓ : ℓ ≠ 0) : IsPeriodic ℓ (ρw ℓ) := by
  intro z
  simp only [ρw]
  have : π * (z.1 + ℓ) / ℓ = π * z.1 / ℓ + π := by field_simp
  rw [this, Real.sin_add_pi, neg_sq]

/-- The smooth weight is dominated by the centred weight everywhere. -/
theorem ρw_le_ρc (ℓ : ℝ) (z : Plane) : ρw ℓ z ≤ ρc z := by
  unfold ρw ρc
  rcases eq_or_ne ℓ 0 with rfl | hℓ
  · simp; positivity
  · have h1 : Real.sin (π * z.1 / ℓ) ^ 2 ≤ (π * z.1 / ℓ) ^ 2 := Real.sin_sq_le_sq
    have h2 : (ℓ / π) ^ 2 * (π * z.1 / ℓ) ^ 2 = z.1 ^ 2 := by
      field_simp
    have h3 : (ℓ / π) ^ 2 * Real.sin (π * z.1 / ℓ) ^ 2 ≤ (ℓ / π) ^ 2 * (π * z.1 / ℓ) ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    linarith

theorem four_div_pi_sq_le_one : 4 / π ^ 2 ≤ 1 := by
  rw [div_le_one (by positivity)]
  nlinarith [Real.two_le_pi]

theorem four_div_pi_sq_pos : 0 < 4 / π ^ 2 := by positivity

/-- **Uniform equivalence of the two weights (D12).**  On the centred cell,
`(4/π²) ρc ≤ ρw ℓ ≤ ρc`, with a constant independent of `ℓ` (Jordan's inequality). -/
theorem ρw_comparable {ℓ : ℝ} (hℓ : 0 < ℓ) {z : Plane} (hz : z ∈ cell ℓ) :
    (4 / π ^ 2) * ρc z ≤ ρw ℓ z ∧ ρw ℓ z ≤ ρc z := by
  refine ⟨?_, ρw_le_ρc ℓ z⟩
  rw [mem_cell] at hz
  have habs : |z.1| ≤ ℓ / 2 := abs_le.2 ⟨by linarith [hz.1], hz.2.le⟩
  have hx0 : 0 ≤ π * |z.1| / ℓ := by positivity
  have hx1 : π * |z.1| / ℓ ≤ π / 2 := by
    rw [div_le_iff₀ hℓ]; nlinarith [Real.pi_pos]
  have hs := Real.mul_le_sin hx0 hx1
  have hs' : 2 / π * (π * |z.1| / ℓ) = 2 * |z.1| / ℓ := by field_simp
  rw [hs'] at hs
  have hsq : (2 * |z.1| / ℓ) ^ 2 ≤ Real.sin (π * |z.1| / ℓ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hs 2
  have hsym : Real.sin (π * |z.1| / ℓ) ^ 2 = Real.sin (π * z.1 / ℓ) ^ 2 := by
    rcases abs_cases z.1 with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, show π * -z.1 / ℓ = -(π * z.1 / ℓ) by ring, Real.sin_neg, neg_sq]
  rw [hsym] at hsq
  have hq : 4 / π ^ 2 * z.1 ^ 2 ≤ (ℓ / π) ^ 2 * Real.sin (π * z.1 / ℓ) ^ 2 := by
    calc 4 / π ^ 2 * z.1 ^ 2 = (ℓ / π) ^ 2 * (2 * |z.1| / ℓ) ^ 2 := by
          field_simp; rw [sq_abs]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
  have h41 := four_div_pi_sq_le_one
  have h40 := four_div_pi_sq_pos
  unfold ρw ρc
  nlinarith [sq_nonneg z.2]

/-- Powers of the two weights are uniformly comparable on the centred cell (D12, B0271). -/
theorem rpow_ρw_comparable {ℓ m : ℝ} (hℓ : 0 < ℓ) (hm : 0 ≤ m) {z : Plane} (hz : z ∈ cell ℓ) :
    (4 / π ^ 2) ^ m * ρc z ^ m ≤ ρw ℓ z ^ m ∧ ρw ℓ z ^ m ≤ ρc z ^ m := by
  obtain ⟨h1, h2⟩ := ρw_comparable hℓ hz
  refine ⟨?_, Real.rpow_le_rpow (ρw_pos ℓ z).le h2 hm⟩
  rw [← Real.mul_rpow four_div_pi_sq_pos.le (ρc_pos z).le]
  exact Real.rpow_le_rpow (mul_pos four_div_pi_sq_pos (ρc_pos z)).le h1 hm

/-- Negative powers: `ρc^{-m} ≤ ρw^{-m} ≤ (π²/4)^m ρc^{-m}` on the cell, `m ≥ 0`. -/
theorem rpow_neg_ρw_comparable {ℓ m : ℝ} (hℓ : 0 < ℓ) (hm : 0 ≤ m) {z : Plane}
    (hz : z ∈ cell ℓ) :
    ρc z ^ (-m) ≤ ρw ℓ z ^ (-m) ∧ ρw ℓ z ^ (-m) ≤ (4 / π ^ 2) ^ (-m) * ρc z ^ (-m) := by
  obtain ⟨h1, h2⟩ := ρw_comparable hℓ hz
  refine ⟨Real.rpow_le_rpow_of_nonpos (ρw_pos ℓ z) h2 (by linarith), ?_⟩
  rw [← Real.mul_rpow four_div_pi_sq_pos.le (ρc_pos z).le]
  exact Real.rpow_le_rpow_of_nonpos (mul_pos four_div_pi_sq_pos (ρc_pos z)) h1 (by linarith)

/-- Dilation identity for the smooth weight (scoping CY02). -/
theorem ρw_dilate {ℓ a : ℝ} (ha : 0 < a) (z : Plane) :
    ρw ℓ (√a • z) = 1 + a * (ρw (ℓ / √a) z - 1) := by
  have hs : 0 < √a := Real.sqrt_pos.2 ha
  have hsq : √a ^ 2 = a := Real.sq_sqrt ha.le
  simp only [ρw, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rcases eq_or_ne ℓ 0 with rfl | hℓ
  · simp [mul_pow, hsq]
  · have harg : π * (√a * z.1) / ℓ = π * z.1 / (ℓ / √a) := by field_simp
    rw [harg]
    have h1 : (ℓ / √a / π) ^ 2 = (ℓ / π) ^ 2 / a := by
      rw [div_div, div_pow, mul_pow, hsq, div_pow]; field_simp
    rw [h1, mul_pow, hsq]
    field_simp
    ring

/-! ### Integrability of negative powers -/

theorem norm_sq_le_ρc (z : Plane) : (1 + ‖z‖) ^ 2 ≤ 2 * ρc z := by
  have h1 : ‖z‖ ^ 2 ≤ z.1 ^ 2 + z.2 ^ 2 := by
    rw [Prod.norm_def]
    rcases le_total ‖z.1‖ ‖z.2‖ with h | h
    · rw [max_eq_right h, Real.norm_eq_abs, sq_abs]; nlinarith [sq_nonneg z.1]
    · rw [max_eq_left h, Real.norm_eq_abs, sq_abs]; nlinarith [sq_nonneg z.2]
  unfold ρc
  nlinarith [sq_nonneg (1 - ‖z‖), norm_nonneg z]

theorem rpow_neg_ρc_le {m : ℝ} (hm : 0 ≤ m) (z : Plane) :
    ρc z ^ (-m) ≤ 2 ^ m * (1 + ‖z‖) ^ (-(2 * m)) := by
  have hn : 0 < 1 + ‖z‖ := by positivity
  rw [Real.rpow_neg (ρc_pos z).le, Real.rpow_neg hn.le, ← div_eq_mul_inv,
    le_div_iff₀ (by positivity), Real.rpow_mul hn.le]
  rw [show ((1 + ‖z‖) ^ (2 : ℝ)) = (1 + ‖z‖) ^ (2 : ℕ) by norm_cast]
  rw [← div_eq_inv_mul, div_le_iff₀ (Real.rpow_pos_of_pos (ρc_pos z) m)]
  rw [← Real.mul_rpow (by norm_num) (ρc_pos z).le]
  exact Real.rpow_le_rpow (by positivity) (norm_sq_le_ρc z) hm

/-- `ρc^{-m}` is integrable on the plane for `m > 1`. -/
theorem integrable_rpow_neg_ρc {m : ℝ} (hm : 1 < m) :
    Integrable (fun z : Plane => ρc z ^ (-m)) := by
  have hint : Integrable (fun z : Plane => (1 + ‖z‖) ^ (-(2 * m))) := by
    apply integrable_one_add_norm
    simp only [Module.finrank_prod, Module.finrank_self]
    push_cast; linarith
  refine (hint.const_mul (2 ^ m)).mono' ?_ ?_
  · exact (Continuous.aestronglyMeasurable (by
      unfold ρc
      exact Continuous.rpow_const (by fun_prop) fun z => Or.inl (by
        have := one_le_ρc z; unfold ρc at this; linarith)))
  · refine Filter.Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (ρc_pos z).le _)]
    exact rpow_neg_ρc_le (by linarith) z

theorem continuous_rpow_ρw (ℓ m : ℝ) : Continuous fun z => ρw ℓ z ^ m :=
  Continuous.rpow_const (contDiff_ρw ℓ).continuous fun z => Or.inl (ρw_pos ℓ z).ne'

theorem continuous_rpow_ρc (m : ℝ) : Continuous fun z => ρc z ^ m :=
  Continuous.rpow_const contDiff_ρc.continuous fun z => Or.inl (ρc_pos z).ne'

theorem integrableOn_rpow_neg_ρw {ℓ m : ℝ} (hℓ : 0 < ℓ) (hm : 1 < m) :
    IntegrableOn (fun z => ρw ℓ z ^ (-m)) (cell ℓ) := by
  have hint := ((integrable_rpow_neg_ρc hm).const_mul ((4 / π ^ 2) ^ (-m))).integrableOn
    (s := cell ℓ)
  refine hint.mono' (continuous_rpow_ρw ℓ (-m)).aestronglyMeasurable.restrict ?_
  refine (ae_restrict_iff' (measurableSet_cell ℓ)).2 (Filter.Eventually.of_forall fun z hz => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (ρw_pos ℓ z).le _)]
  exact (rpow_neg_ρw_comparable hℓ (by linarith) hz).2

/-- The cell integral of `ρw^{-m}`, `m > 1`, is bounded uniformly in the period (CY02). -/
theorem setIntegral_rpow_neg_ρw_le {m : ℝ} (hm : 1 < m) :
    ∃ C, ∀ ℓ > 0, ∫ z in cell ℓ, ρw ℓ z ^ (-m) ≤ C := by
  refine ⟨(4 / π ^ 2) ^ (-m) * ∫ z, ρc z ^ (-m), fun ℓ hℓ => ?_⟩
  rw [← integral_const_mul]
  calc ∫ z in cell ℓ, ρw ℓ z ^ (-m)
      ≤ ∫ z in cell ℓ, (4 / π ^ 2) ^ (-m) * ρc z ^ (-m) := by
        refine setIntegral_mono_on (integrableOn_rpow_neg_ρw hℓ hm)
          ((integrable_rpow_neg_ρc hm).const_mul _).integrableOn (measurableSet_cell ℓ)
          fun z hz => (rpow_neg_ρw_comparable hℓ (by linarith) hz).2
    _ ≤ ∫ z, (4 / π ^ 2) ^ (-m) * ρc z ^ (-m) :=
        setIntegral_le_integral ((integrable_rpow_neg_ρc hm).const_mul _)
          (Filter.Eventually.of_forall fun z =>
            mul_nonneg (Real.rpow_nonneg four_div_pi_sq_pos.le _)
              (Real.rpow_nonneg (ρc_pos z).le _))

end UnforcedLeray.Cyl
