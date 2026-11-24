import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_2_1
import Mathlib.Analysis.Complex.Exponential

/-!
# `PartIII-b:C/grad/3/4/1/2/1/1`: domination of every kernel expression by `latticeW`

Source `the November 2 reference manuscript`
5063-5079.  Proof: for `1 ≤ a ≤ 2.1` one has `a⁻¹ᵐ ≤ 1` and `exp(-r²/(4a)) ≤ exp(-r²/8.4)`,
and `1/8.4 = 1/9 + 1/126`.  The factor `|u|^p ≤ p! e^{|u|}` is absorbed by the
Gaussian `e^{-u²/126}` since `|u| - u²/126 ≤ 63`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `e^{|u|} e^{-u²/126} ≤ e^{63}`. -/
lemma exp_abs_mul_gauss_le (u : ℝ) :
    Real.exp |u| * Real.exp (-(u ^ 2) / 126) ≤ Real.exp 63 := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (|u| - 63), sq_abs u, abs_nonneg u]

/-- `|u|^p ≤ p! e^{|u|}`. -/
lemma pow_abs_le_fact_exp (p : ℕ) (u : ℝ) :
    |u| ^ p ≤ (p.factorial : ℝ) * Real.exp |u| := by
  have h := Real.pow_div_factorial_le_exp |u| (abs_nonneg u) p
  have hf : (0 : ℝ) < (p.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos p)
  have h2 := (div_le_iff₀ hf).mp h
  linarith [mul_comm (Real.exp |u|) (p.factorial : ℝ)]

/-- Real-variable monomial bound: `a ∈ [1, 2.1]`. -/
lemma mon_real_bound (c a u η : ℝ) (m p q : ℕ) (ha1 : 1 ≤ a) (ha2 : a ≤ 21 / 10) :
    |c * (a⁻¹) ^ m * u ^ p * η ^ q * Real.exp (-(u ^ 2 + η ^ 2) / (4 * a))| ≤
      |c| * ((p.factorial : ℝ) * (q.factorial : ℝ) * Real.exp 63 * Real.exp 63) *
        Real.exp (-(u ^ 2 + η ^ 2) / 9) := by
  have ha0 : 0 < a := by linarith
  have hA0 : 0 ≤ (a⁻¹) ^ m := pow_nonneg (inv_nonneg.mpr ha0.le) m
  have hA1 : (a⁻¹) ^ m ≤ 1 := by
    apply pow_le_one₀ (inv_nonneg.mpr ha0.le)
    rw [inv_le_one₀ ha0]; exact ha1
  have hEpos : 0 < Real.exp (-(u ^ 2 + η ^ 2) / (4 * a)) := Real.exp_pos _
  have hR : 0 ≤ u ^ 2 + η ^ 2 := by positivity
  have key : (5 / 42) * (u ^ 2 + η ^ 2) ≤ (u ^ 2 + η ^ 2) / (4 * a) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith [mul_nonneg hR (sub_nonneg.mpr ha2)]
  have hE : Real.exp (-(u ^ 2 + η ^ 2) / (4 * a)) ≤
      Real.exp (-(u ^ 2 + η ^ 2) / 9) * Real.exp (-(u ^ 2) / 126) * Real.exp (-(η ^ 2) / 126) := by
    simp only [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [neg_div]
    have e1 : -(u ^ 2 + η ^ 2) / 9 + -(u ^ 2) / 126 + -(η ^ 2) / 126
        = -((5 / 42) * (u ^ 2 + η ^ 2)) := by ring
    rw [e1]
    linarith [key]
  have hEq : |c * (a⁻¹) ^ m * u ^ p * η ^ q * Real.exp (-(u ^ 2 + η ^ 2) / (4 * a))| =
      |c| * (a⁻¹) ^ m * |u| ^ p * |η| ^ q * Real.exp (-(u ^ 2 + η ^ 2) / (4 * a)) := by
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hA0, abs_pow, abs_pow,
      abs_of_pos hEpos]
  have hU := pow_abs_le_fact_exp p u
  have hη := pow_abs_le_fact_exp q η
  have hu2 := exp_abs_mul_gauss_le u
  have hη2 := exp_abs_mul_gauss_le η
  have hpos_c : 0 ≤ |c| := abs_nonneg c
  rw [hEq]
  calc |c| * (a⁻¹) ^ m * |u| ^ p * |η| ^ q * Real.exp (-(u ^ 2 + η ^ 2) / (4 * a))
      ≤ |c| * 1 * ((p.factorial : ℝ) * Real.exp |u|) * ((q.factorial : ℝ) * Real.exp |η|) *
          (Real.exp (-(u ^ 2 + η ^ 2) / 9) * Real.exp (-(u ^ 2) / 126) *
            Real.exp (-(η ^ 2) / 126)) := by
        gcongr
    _ = |c| * ((p.factorial : ℝ) * (q.factorial : ℝ)) *
          ((Real.exp |u| * Real.exp (-(u ^ 2) / 126)) *
            (Real.exp |η| * Real.exp (-(η ^ 2) / 126))) * Real.exp (-(u ^ 2 + η ^ 2) / 9) := by
        ring
    _ ≤ |c| * ((p.factorial : ℝ) * (q.factorial : ℝ)) * (Real.exp 63 * Real.exp 63) *
          Real.exp (-(u ^ 2 + η ^ 2) / 9) := by
        have hpq : 0 ≤ |c| * ((p.factorial : ℝ) * (q.factorial : ℝ)) := by positivity
        have hprod : (Real.exp |u| * Real.exp (-(u ^ 2) / 126)) *
            (Real.exp |η| * Real.exp (-(η ^ 2) / 126)) ≤ Real.exp 63 * Real.exp 63 :=
          mul_le_mul hu2 hη2 (by positivity) (by positivity)
        have hg : 0 ≤ Real.exp (-(u ^ 2 + η ^ 2) / 9) := Real.exp_nonneg _
        nlinarith [mul_le_mul_of_nonneg_right hprod hg, mul_le_mul_of_nonneg_left hprod hpq]
    _ = |c| * ((p.factorial : ℝ) * (q.factorial : ℝ) * Real.exp 63 * Real.exp 63) *
          Real.exp (-(u ^ 2 + η ^ 2) / 9) := by
        ring

theorem gMon_dom (t : ℝ × ℕ × ℕ × ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ν : ℝ) (j : ℤ) (s : ℝ) (x : ℝ × ℝ),
      0 < ν → ν ≤ 1 → 0 < s → ν * s ≤ 11 / 10 →
        |gMon ν j t s x| ≤ K * latticeW gradAlpha gradK (x.1 - (j : ℝ) * cOf ν) x.2 := by
  refine ⟨|t.1| * ((t.2.2.1.factorial : ℝ) * (t.2.2.2.factorial : ℝ) * Real.exp 63 * Real.exp 63),
    by positivity, ?_⟩
  intro ν j s x hν _ hs hνs
  have hns : 0 < ν * s := mul_pos hν hs
  have ha1 : 1 ≤ ageA ν s := by unfold ageA; linarith
  have ha2 : ageA ν s ≤ 21 / 10 := by unfold ageA; linarith
  have hmon := mon_real_bound t.1 (ageA ν s) (x.1 - (j : ℝ) * cOf ν) x.2 t.2.1 t.2.2.1 t.2.2.2
    ha1 ha2
  have hK : 0 ≤ |t.1| * ((t.2.2.1.factorial : ℝ) * (t.2.2.2.factorial : ℝ) * Real.exp 63 *
      Real.exp 63) := by positivity
  have hpow : (1 : ℝ) ≤ (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 12 := by
    apply one_le_pow₀
    linarith [abs_nonneg (x.1 - (j : ℝ) * cOf ν), abs_nonneg x.2]
  have hexp : Real.exp (-((x.1 - (j : ℝ) * cOf ν) ^ 2 + x.2 ^ 2) / 9) ≤
      (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 12 *
        Real.exp (-(1 / 9 : ℝ) * ((x.1 - (j : ℝ) * cOf ν) ^ 2 + x.2 ^ 2)) := by
    have e : -((x.1 - (j : ℝ) * cOf ν) ^ 2 + x.2 ^ 2) / 9
        = -(1 / 9 : ℝ) * ((x.1 - (j : ℝ) * cOf ν) ^ 2 + x.2 ^ 2) := by ring
    rw [e]
    exact le_mul_of_one_le_left (Real.exp_nonneg _) hpow
  unfold gMon
  simp only [latticeW, gradAlpha, gradK]
  calc _ ≤ _ := hmon
    _ ≤ |t.1| * ((t.2.2.1.factorial : ℝ) * (t.2.2.2.factorial : ℝ) * Real.exp 63 *
          Real.exp 63) * ((1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 12 *
          Real.exp (-(1 / 9 : ℝ) * ((x.1 - (j : ℝ) * cOf ν) ^ 2 + x.2 ^ 2))) :=
        mul_le_mul_of_nonneg_left hexp hK
    _ = _ := by ring

theorem gDomProp : GDomProp := by
  unfold GDomProp
  intro e
  induction e with
  | nil =>
    exact ⟨0, le_rfl, fun ν j s x _ _ _ _ => by simp [gEval]⟩
  | cons t l ih =>
    obtain ⟨K, hK, hKb⟩ := gMon_dom t
    obtain ⟨C, hC, hCb⟩ := ih
    refine ⟨K + C, add_nonneg hK hC, ?_⟩
    intro ν j s x hν hν1 hs hνs
    have hsplit : gEval (t :: l) ν j s x = gMon ν j t s x + gEval l ν j s x := by
      simp [gEval]
    rw [hsplit]
    have h1 := hKb ν j s x hν hν1 hs hνs
    have h2 := hCb ν j s x hν hν1 hs hνs
    have hW : 0 ≤ latticeW gradAlpha gradK (x.1 - (j : ℝ) * cOf ν) x.2 := by
      unfold latticeW; positivity
    calc |gMon ν j t s x + gEval l ν j s x|
        ≤ |gMon ν j t s x| + |gEval l ν j s x| := abs_add_le _ _
      _ ≤ K * latticeW gradAlpha gradK (x.1 - (j : ℝ) * cOf ν) x.2 +
            C * latticeW gradAlpha gradK (x.1 - (j : ℝ) * cOf ν) x.2 := add_le_add h1 h2
      _ = (K + C) * latticeW gradAlpha gradK (x.1 - (j : ℝ) * cOf ν) x.2 := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
