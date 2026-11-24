import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_1
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Proofs.FlatCurlTerm
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

/-!
# The lattice sum of the term curls is `g_B` (source 4597-4608)

`FlatForceGB`: for `c = cOf ν`, `s > 0`, `gBProf ν c s B x = ((-∑' j, curlTermProf a B (xj ν j x) : ℝ) : ℂ)`
with `a = ageA ν s`.

Route: `HProf ν c s x = ∑' j, hMode a (xj ν j x)` and likewise for `RProf`, `rMode` (`srcA ν s = ageA ν s`
for `s > 0`); the per-term identity `gb_term` (algebra with `I² = -1`, `angTwo` and its conjugate);
summability of the three lattice sums from a Gaussian bound (`gb_gauss_bound`, `gb_poly_exp`,
`gb_gauss_summable`); then `tsum` linearity and `Complex.conj_tsum`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-! ## 1. Pointwise identity -/

theorem gb_planeR_sq (y : ℝ × ℝ) : planeR y ^ 2 = y.1 ^ 2 + y.2 ^ 2 := by
  unfold planeR
  exact Real.sq_sqrt (by positivity)

theorem gb_angTwo_norm_le (y : ℝ × ℝ) : ‖IIIa.angTwo y‖ ≤ 1 := by
  have hs : (0 : ℝ) ≤ y.1 ^ 2 + y.2 ^ 2 := by positivity
  unfold IIIa.angTwo
  rw [norm_div, norm_pow, Complex.norm_add_mul_I, Real.sq_sqrt hs, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hs]
  exact div_le_one_of_le₀ le_rfl hs

theorem gb_term (a : ℝ) (B : Mat3) (y : ℝ × ℝ) :
    (-(1 / 2 : ℂ) * (((Bd B : ℝ) : ℂ) - Complex.I * ((Be B : ℝ) : ℂ))) * hMode a y
      + (-(1 / 2 : ℂ) * (((Bd B : ℝ) : ℂ) + Complex.I * ((Be B : ℝ) : ℂ))) * conj (hMode a y)
      - ((ConcreteYF.Bbeta B : ℝ) : ℂ) * rMode a y
      = -((curlTermProf a B y : ℝ) : ℂ) := by
  rcases eq_or_ne (y.1 ^ 2 + y.2 ^ 2) 0 with h0 | h0
  · have hy1 : y.1 = 0 := by nlinarith [sq_nonneg y.1, sq_nonneg y.2]
    have hy2 : y.2 = 0 := by nlinarith [sq_nonneg y.1, sq_nonneg y.2]
    unfold hMode rMode curlTermProf
    simp [IIIa.angTwo, hy1, hy2] <;> ring
  · have hD : ((y.1 : ℂ) ^ 2 + (y.2 : ℂ) ^ 2) ≠ 0 := by
      have h' : ((y.1 ^ 2 + y.2 ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h0
      push_cast at h'
      exact h'
    have hconj : conj (((y.1 : ℂ) + (y.2 : ℂ) * Complex.I) ^ 2 / ((y.1 ^ 2 + y.2 ^ 2 : ℝ) : ℂ))
        = ((y.1 : ℂ) - (y.2 : ℂ) * Complex.I) ^ 2 / ((y.1 : ℂ) ^ 2 + (y.2 : ℂ) ^ 2) := by
      simp only [map_div₀, map_pow, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast
      ring
    unfold hMode rMode curlTermProf
    simp only [map_mul, Complex.conj_ofReal]
    unfold IIIa.angTwo
    rw [hconj]
    push_cast
    linear_combination
      ((((gaussRdE a (planeR y)) : ℝ) : ℂ) / ((y.1 : ℂ) ^ 2 + (y.2 : ℂ) ^ 2))
        * (2 * ((Be B : ℝ) : ℂ) * (y.1 : ℂ) * (y.2 : ℂ) - ((Bd B : ℝ) : ℂ) * (y.2 : ℂ) ^ 2)
        * Complex.I_sq

/-! ## 2. Bounds for the Gaussian profiles -/

theorem gb_hMode_norm (a : ℝ) (y : ℝ × ℝ) :
    ‖hMode a y‖ ≤ |gaussRdE a (planeR y)| := by
  unfold hMode
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) (gb_angTwo_norm_le y)

theorem gb_rMode_norm (a : ℝ) (y : ℝ × ℝ) :
    ‖rMode a y‖ ≤ |gaussRdE a (planeR y)| + 2 * |gaussE a (planeR y)| := by
  unfold rMode
  rw [Complex.norm_real, Real.norm_eq_abs]
  have h := abs_add_le (gaussRdE a (planeR y)) (2 * gaussE a (planeR y))
  rw [abs_mul, abs_two] at h
  exact h

theorem gb_gauss_bound (a : ℝ) (ha : 0 < a) : ∃ K : ℝ, 0 ≤ K ∧ ∀ r : ℝ,
    |gaussRdE a r| ≤ K * ((1 + r ^ 2) ^ 2 * Real.exp (-(r ^ 2) / (4 * a))) ∧
    |gaussE a r| ≤ K * ((1 + r ^ 2) ^ 2 * Real.exp (-(r ^ 2) / (4 * a))) := by
  refine ⟨(a ^ 2)⁻¹ * (2 / a + 1 / (4 * a ^ 2) + 2 + 1 / (2 * a)), ?_, fun r => ?_⟩
  · positivity
  have hp : 0 ≤ r ^ 2 := sq_nonneg r
  have hw : 0 ≤ Real.exp (-(r ^ 2) / (4 * a)) := (Real.exp_pos _).le
  have hM1 : r ^ 2 ≤ (1 + r ^ 2) ^ 2 := by nlinarith
  have hM2 : (r ^ 2) ^ 2 ≤ (1 + r ^ 2) ^ 2 := by nlinarith
  have hM3 : (1 : ℝ) ≤ (1 + r ^ 2) ^ 2 := by nlinarith
  have hM0 : 0 ≤ (1 + r ^ 2) ^ 2 := by positivity
  have hcoef : 0 ≤ (a ^ 2)⁻¹ := by positivity
  have hcw : 0 ≤ (a ^ 2)⁻¹ * Real.exp (-(r ^ 2) / (4 * a)) := mul_nonneg hcoef hw
  constructor
  · rw [ft_gaussRdE_eq, abs_mul, abs_mul, abs_of_nonneg hcoef, abs_of_nonneg hw]
    have hX : -2 * r ^ 2 / a + (r ^ 2) ^ 2 / (4 * a ^ 2)
        = -((2 / a) * r ^ 2) + (1 / (4 * a ^ 2)) * (r ^ 2) ^ 2 := by ring
    have hA0 : 0 ≤ (2 / a) * r ^ 2 := by positivity
    have hC0 : 0 ≤ (1 / (4 * a ^ 2)) * (r ^ 2) ^ 2 := by positivity
    have hXa : |-2 * r ^ 2 / a + (r ^ 2) ^ 2 / (4 * a ^ 2)|
        ≤ (2 / a) * (1 + r ^ 2) ^ 2 + (1 / (4 * a ^ 2)) * (1 + r ^ 2) ^ 2 := by
      rw [hX, abs_le]
      have h3 : (2 / a) * r ^ 2 ≤ (2 / a) * (1 + r ^ 2) ^ 2 :=
        mul_le_mul_of_nonneg_left hM1 (by positivity)
      have h4 : (1 / (4 * a ^ 2)) * (r ^ 2) ^ 2 ≤ (1 / (4 * a ^ 2)) * (1 + r ^ 2) ^ 2 :=
        mul_le_mul_of_nonneg_left hM2 (by positivity)
      constructor <;> linarith
    have h5 := mul_le_mul_of_nonneg_left hXa hcw
    have hextra : 0 ≤ (a ^ 2)⁻¹ * (2 + 1 / (2 * a)) * ((1 + r ^ 2) ^ 2 * Real.exp (-(r ^ 2) / (4 * a))) := by
      positivity
    nlinarith [h5, hextra]
  · have hY : |2 - r ^ 2 / (2 * a)| ≤ (2 + 1 / (2 * a)) * (1 + r ^ 2) ^ 2 := by
      have e : 2 - r ^ 2 / (2 * a) = 2 - (1 / (2 * a)) * r ^ 2 := by ring
      have h6 : 0 ≤ (1 / (2 * a)) * r ^ 2 := by positivity
      have h7 : (1 / (2 * a)) * r ^ 2 ≤ (1 / (2 * a)) * (1 + r ^ 2) ^ 2 :=
        mul_le_mul_of_nonneg_left hM1 (by positivity)
      have h9 : 0 ≤ (1 / (2 * a)) * (1 + r ^ 2) ^ 2 := by positivity
      rw [e, abs_le]
      constructor <;> nlinarith [h6, h7, h9, hM3, hM0]
    have hY2 : |(a ^ 2)⁻¹ * (2 - r ^ 2 / (2 * a)) * Real.exp (-(r ^ 2) / (4 * a))|
        = (a ^ 2)⁻¹ * |2 - r ^ 2 / (2 * a)| * Real.exp (-(r ^ 2) / (4 * a)) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hcoef, abs_of_nonneg hw]
    show |(a ^ 2)⁻¹ * (2 - r ^ 2 / (2 * a)) * Real.exp (-(r ^ 2) / (4 * a))| ≤ _
    rw [hY2]
    have h8 := mul_le_mul_of_nonneg_left hY (mul_nonneg hcoef hw)
    have hextra : 0 ≤ (a ^ 2)⁻¹ * (2 / a + 1 / (4 * a ^ 2))
        * ((1 + r ^ 2) ^ 2 * Real.exp (-(r ^ 2) / (4 * a))) := by
      positivity
    nlinarith [h8, hextra]

/-! ## 3. Gaussian lattice summability -/

theorem gb_gauss_dom (t α c : ℝ) (hα : 0 < α) (hc : 0 ≤ c) (j : ℤ) :
    Real.exp (-α * (t - (j : ℝ) * c) ^ 2) ≤
      Real.exp (-Real.pi * ((α * c ^ 2 / Real.pi) * (j : ℝ) ^ 2
        - 2 * (α * |t| * c / Real.pi) * |(j : ℝ)|)) := by
  apply Real.exp_le_exp.mpr
  have hReal.pi : Real.pi ≠ 0 := Real.pi_ne_zero
  have key : -Real.pi * ((α * c ^ 2 / Real.pi) * (j : ℝ) ^ 2 - 2 * (α * |t| * c / Real.pi) * |(j : ℝ)|)
      = -(α * c ^ 2 * (j : ℝ) ^ 2) + 2 * α * c * (|t| * |(j : ℝ)|) := by
    field_simp
    ring
  rw [key]
  have h1 : t * (j : ℝ) ≤ |t| * |(j : ℝ)| := by
    rw [← abs_mul]
    exact le_abs_self _
  nlinarith [mul_nonneg (mul_nonneg hα.le hc) (sub_nonneg.mpr h1), mul_nonneg hα.le (sq_nonneg t)]

theorem gb_pow_summable (t α c : ℝ) (hα : 0 < α) (hc : 0 < c) (k : ℕ) :
    Summable (fun j : ℤ => |(j : ℝ)| ^ k * Real.exp (-α * (t - (j : ℝ) * c) ^ 2)) := by
  have hT : 0 < α * c ^ 2 / Real.pi := div_pos (mul_pos hα (pow_pos hc 2)) Real.pi_pos
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
    (summable_pow_mul_jacobiTheta₂_term_bound (α * |t| * c / Real.pi) hT k)
  simp only [Int.cast_abs]
  exact mul_le_mul_of_nonneg_left (gb_gauss_dom t α c hα hc.le j) (pow_nonneg (abs_nonneg _) k)

theorem gb_gauss_summable (t α c : ℝ) (hα : 0 < α) (hc : 0 < c) :
    Summable (fun j : ℤ => Real.exp (-α * (t - (j : ℝ) * c) ^ 2)) := by
  simpa using gb_pow_summable t α c hα hc 0

theorem gb_poly_exp (α : ℝ) (hα : 0 < α) (m : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ u : ℝ,
    (1 + u ^ 2) ^ m * Real.exp (-α * u ^ 2) ≤ K * Real.exp (-(α / 2) * u ^ 2) := by
  refine ⟨(m.factorial : ℝ) * (2 / α) ^ m * Real.exp (α / 2), by positivity, fun u => ?_⟩
  set x : ℝ := (α / 2) * (1 + u ^ 2) with hx
  have hx0 : 0 ≤ x := by positivity
  have h := Real.pow_div_factorial_le_exp x hx0 m
  have hm : (0 : ℝ) < (m.factorial : ℝ) := by positivity
  have hxm : x ^ m = (α / 2) ^ m * (1 + u ^ 2) ^ m := by rw [hx, mul_pow]
  have e1 : (1 + u ^ 2) ^ m = (2 / α) ^ m * x ^ m := by
    rw [hxm, ← mul_assoc, ← mul_pow, show (2 / α) * (α / 2) = (1 : ℝ) by field_simp,
      one_pow, one_mul]
  have h2 : x ^ m ≤ (m.factorial : ℝ) * Real.exp x := by
    rw [div_le_iff₀ hm] at h
    linarith
  have hexp : Real.exp x * Real.exp (-α * u ^ 2)
      = Real.exp (α / 2) * Real.exp (-(α / 2) * u ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [hx]
    ring
  calc (1 + u ^ 2) ^ m * Real.exp (-α * u ^ 2)
      = (2 / α) ^ m * x ^ m * Real.exp (-α * u ^ 2) := by rw [e1]
    _ ≤ (2 / α) ^ m * ((m.factorial : ℝ) * Real.exp x) * Real.exp (-α * u ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (2 / α) ^ m * ((m.factorial : ℝ) * (Real.exp x * Real.exp (-α * u ^ 2))) := by ring
    _ = (2 / α) ^ m * ((m.factorial : ℝ) * (Real.exp (α / 2) * Real.exp (-(α / 2) * u ^ 2))) := by
        rw [hexp]
    _ = (m.factorial : ℝ) * (2 / α) ^ m * Real.exp (α / 2) * Real.exp (-(α / 2) * u ^ 2) := by
        ring

/-- The lattice sums of the Gaussian profiles are summable. -/
theorem gb_summable_gen (a c : ℝ) (ha : 0 < a) (hc : 0 < c) (t η : ℝ) :
    Summable (fun j : ℤ => ‖hMode a (t - (j : ℝ) * c, η)‖) ∧
    Summable (fun j : ℤ => ‖rMode a (t - (j : ℝ) * c, η)‖) := by
  obtain ⟨K, hK0, hK⟩ := gb_gauss_bound a ha
  obtain ⟨K2, hK20, hK2⟩ := gb_poly_exp (1 / (4 * a)) (by positivity) 2
  have hS := gb_gauss_summable t (1 / (4 * a) / 2) c (by positivity) hc
  set C0 : ℝ := K * (1 + η ^ 2) ^ 2 * K2 with hC0
  have hC00 : 0 ≤ C0 := by
    rw [hC0]
    positivity
  have key : ∀ j : ℤ, |gaussRdE a (planeR (t - (j : ℝ) * c, η))| ≤
      C0 * Real.exp (-(1 / (4 * a) / 2) * (t - (j : ℝ) * c) ^ 2) ∧
      |gaussE a (planeR (t - (j : ℝ) * c, η))| ≤
      C0 * Real.exp (-(1 / (4 * a) / 2) * (t - (j : ℝ) * c) ^ 2) := by
    intro j
    set u : ℝ := t - (j : ℝ) * c with hu
    have hr2 : planeR (u, η) ^ 2 = u ^ 2 + η ^ 2 := gb_planeR_sq (u, η)
    obtain ⟨hR, hE⟩ := hK (planeR (u, η))
    rw [hr2] at hR hE
    have hB : Real.exp (-(u ^ 2 + η ^ 2) / (4 * a)) ≤ Real.exp (-(1 / (4 * a)) * u ^ 2) := by
      apply Real.exp_le_exp.mpr
      have e : -(u ^ 2 + η ^ 2) / (4 * a) = -(1 / (4 * a)) * u ^ 2 - η ^ 2 / (4 * a) := by ring
      have : 0 ≤ η ^ 2 / (4 * a) := by positivity
      rw [e]
      linarith
    have hA : (1 + (u ^ 2 + η ^ 2)) ^ 2 ≤ ((1 + η ^ 2) * (1 + u ^ 2)) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity)
      nlinarith [sq_nonneg u, sq_nonneg η, mul_nonneg (sq_nonneg u) (sq_nonneg η)]
    have hG : (1 + (u ^ 2 + η ^ 2)) ^ 2 * Real.exp (-(u ^ 2 + η ^ 2) / (4 * a))
        ≤ (1 + η ^ 2) ^ 2 * K2 * Real.exp (-(1 / (4 * a) / 2) * u ^ 2) := by
      calc (1 + (u ^ 2 + η ^ 2)) ^ 2 * Real.exp (-(u ^ 2 + η ^ 2) / (4 * a))
          ≤ ((1 + η ^ 2) * (1 + u ^ 2)) ^ 2 * Real.exp (-(1 / (4 * a)) * u ^ 2) :=
            mul_le_mul hA hB (Real.exp_pos _).le (by positivity)
        _ = (1 + η ^ 2) ^ 2 * ((1 + u ^ 2) ^ 2 * Real.exp (-(1 / (4 * a)) * u ^ 2)) := by ring
        _ ≤ (1 + η ^ 2) ^ 2 * (K2 * Real.exp (-(1 / (4 * a) / 2) * u ^ 2)) :=
            mul_le_mul_of_nonneg_left (hK2 u) (by positivity)
        _ = (1 + η ^ 2) ^ 2 * K2 * Real.exp (-(1 / (4 * a) / 2) * u ^ 2) := by ring
    constructor
    · calc |gaussRdE a (planeR (u, η))|
          ≤ K * ((1 + (u ^ 2 + η ^ 2)) ^ 2 * Real.exp (-(u ^ 2 + η ^ 2) / (4 * a))) := hR
        _ ≤ K * ((1 + η ^ 2) ^ 2 * K2 * Real.exp (-(1 / (4 * a) / 2) * u ^ 2)) :=
            mul_le_mul_of_nonneg_left hG hK0
        _ = C0 * Real.exp (-(1 / (4 * a) / 2) * u ^ 2) := by rw [hC0]; ring
    · calc |gaussE a (planeR (u, η))|
          ≤ K * ((1 + (u ^ 2 + η ^ 2)) ^ 2 * Real.exp (-(u ^ 2 + η ^ 2) / (4 * a))) := hE
        _ ≤ K * ((1 + η ^ 2) ^ 2 * K2 * Real.exp (-(1 / (4 * a) / 2) * u ^ 2)) :=
            mul_le_mul_of_nonneg_left hG hK0
        _ = C0 * Real.exp (-(1 / (4 * a) / 2) * u ^ 2) := by rw [hC0]; ring
  refine ⟨Summable.of_nonneg_of_le (fun j => norm_nonneg _) ?_ (hS.mul_left C0),
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) ?_ (hS.mul_left (3 * C0))⟩
  · intro j
    exact le_trans (gb_hMode_norm a _) (key j).1
  · intro j
    have h1 := (key j).1
    have h2 := (key j).2
    refine le_trans (gb_rMode_norm a _) ?_
    nlinarith [h1, h2, hC00]

/-! ## 4. The lattice sums of the profiles -/

theorem flatForceGB_hProf (ν s : ℝ) (hs : 0 < s) (x : ℝ × ℝ) :
    HProf ν (cOf ν) s x = ∑' j : ℤ, hMode (ageA ν s) (xj ν j x) := by
  have hsrc : srcA ν s = ageA ν s := by
    unfold srcA
    rw [max_eq_left hs.le]
  show (∑' n : ℤ, hMode (srcA ν s) (x.1 - (n : ℝ) * cOf ν, x.2)) = _
  rw [hsrc]
  rfl

theorem flatForceGB_rProf (ν s : ℝ) (hs : 0 < s) (x : ℝ × ℝ) :
    RProf ν (cOf ν) s x = ∑' j : ℤ, rMode (ageA ν s) (xj ν j x) := by
  have hsrc : srcA ν s = ageA ν s := by
    unfold srcA
    rw [max_eq_left hs.le]
  show (∑' n : ℤ, rMode (srcA ν s) (x.1 - (n : ℝ) * cOf ν, x.2)) = _
  rw [hsrc]
  rfl

/-- **The lattice sum of the term curls is `g_B`** (source 4597-4608). -/
theorem flatForceGB : FlatForceGB := by
  intro ν μ χ A s hν hs x
  have ha : 0 < ageA ν s := by
    unfold ageA
    nlinarith [mul_pos hν hs]
  have hc : 0 < cOf ν := by
    unfold cOf
    exact inv_pos.mpr (pow_pos hν 2)
  have hn1 : Summable (fun j : ℤ => ‖hMode (ageA ν s) (xj ν j x)‖) :=
    (gb_summable_gen (ageA ν s) (cOf ν) ha hc x.1 x.2).1
  have hn2 : Summable (fun j : ℤ => ‖rMode (ageA ν s) (xj ν j x)‖) :=
    (gb_summable_gen (ageA ν s) (cOf ν) ha hc x.1 x.2).2
  have sh : Summable (fun j : ℤ => hMode (ageA ν s) (xj ν j x)) := Summable.of_norm hn1
  have shc : Summable (fun j : ℤ => conj (hMode (ageA ν s) (xj ν j x))) :=
    Summable.of_norm (by simpa only [Complex.norm_conj] using hn1)
  have sr : Summable (fun j : ℤ => rMode (ageA ν s) (xj ν j x)) := Summable.of_norm hn2
  have hH := flatForceGB_hProf ν s hs x
  have hR := flatForceGB_rProf ν s hs x
  have hHc : conj (HProf ν (cOf ν) s x) = ∑' j : ℤ, conj (hMode (ageA ν s) (xj ν j x)) := by
    rw [hH, Complex.conj_tsum]
  unfold gBProf
  rw [hHc, hH, hR]
  have hcomb : (∑' j : ℤ, ((-(1 / 2 : ℂ) * (((Bd (Bmat ν μ χ A s) : ℝ) : ℂ)
        - Complex.I * ((Be (Bmat ν μ χ A s) : ℝ) : ℂ))) * hMode (ageA ν s) (xj ν j x)
      + (-(1 / 2 : ℂ) * (((Bd (Bmat ν μ χ A s) : ℝ) : ℂ)
        + Complex.I * ((Be (Bmat ν μ χ A s) : ℝ) : ℂ))) * conj (hMode (ageA ν s) (xj ν j x))
      - ((ConcreteYF.Bbeta (Bmat ν μ χ A s) : ℝ) : ℂ) * rMode (ageA ν s) (xj ν j x)))
      = (-(1 / 2 : ℂ) * (((Bd (Bmat ν μ χ A s) : ℝ) : ℂ)
        - Complex.I * ((Be (Bmat ν μ χ A s) : ℝ) : ℂ))) * (∑' j : ℤ, hMode (ageA ν s) (xj ν j x))
      + (-(1 / 2 : ℂ) * (((Bd (Bmat ν μ χ A s) : ℝ) : ℂ)
        + Complex.I * ((Be (Bmat ν μ χ A s) : ℝ) : ℂ))) * (∑' j : ℤ, conj (hMode (ageA ν s) (xj ν j x)))
      - ((ConcreteYF.Bbeta (Bmat ν μ χ A s) : ℝ) : ℂ) * (∑' j : ℤ, rMode (ageA ν s) (xj ν j x)) := by
    rw [Summable.tsum_sub ((sh.mul_left _).add (shc.mul_left _)) (sr.mul_left _),
      Summable.tsum_add (sh.mul_left _) (shc.mul_left _), tsum_mul_left, tsum_mul_left,
      tsum_mul_left]
  rw [← hcomb]
  simp only [gb_term]
  rw [tsum_neg, Complex.ofReal_neg, Complex.ofReal_tsum]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
