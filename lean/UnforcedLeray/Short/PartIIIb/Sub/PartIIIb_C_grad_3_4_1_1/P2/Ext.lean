import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_2_1.L2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_2_1.L9
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_2_1.L10
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_2_1.L11
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_2_1.L12
import Mathlib.Analysis.Complex.Exponential

/-!
# `PartIII-b:C/grad/3/4/1/2/2` (ext): termwise envelope of `ψ^p_A` on `νs ≤ 23/20`

Source `the November 2 reference manuscript`
5063-5079.  The envelopes of the seven operators on the lattice terms, re-proved on the range
`ν s ≤ 23/20` (`a ≤ 2.15`, Gaussian rate `1/(4a) ≥ 1/8.6 > 1/9 + 1/200`), so that they hold on
a neighbourhood of the endpoint `s = 1.1/ν`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

def GDomPropX : Prop :=
  ∀ e : GExpr, ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν : ℝ) (j : ℤ) (s : ℝ) (x : ℝ × ℝ),
    0 < ν → ν ≤ 1 → 0 < s → ν * s ≤ 23 / 20 →
      |gEval e ν j s x| ≤ C * latticeW gradAlpha gradK (x.1 - (j : ℝ) * cOf ν) x.2

def GBoundPropX : Prop :=
  ∀ e : Fin 3 → Fin 2 → Fin 2 → GExpr, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (ν : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (j : ℤ) (s : ℝ) (x : ℝ × ℝ),
      0 < ν → ν ≤ 1 → 0 < s → ν * s ≤ 23 / 20 →
        |GSum e ν j (Ay ν χf A) s x| ≤ C * gradF ν χf A s * gradW ν x j


/-- `e^{|u|} e^{-u²/126} ≤ e^{63}`. -/
lemma exp_abs_mul_gauss_leX (u : ℝ) :
    Real.exp |u| * Real.exp (-(u ^ 2) / 200) ≤ Real.exp 50 := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (|u| - 100), sq_abs u, abs_nonneg u]

/-- `|u|^p ≤ p! e^{|u|}`. -/
lemma pow_abs_le_fact_expX (p : ℕ) (u : ℝ) :
    |u| ^ p ≤ (p.factorial : ℝ) * Real.exp |u| := by
  have h := Real.pow_div_factorial_le_exp |u| (abs_nonneg u) p
  have hf : (0 : ℝ) < (p.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos p)
  have h2 := (div_le_iff₀ hf).mp h
  linarith [mul_comm (Real.exp |u|) (p.factorial : ℝ)]

/-- Real-variable monomial bound: `a ∈ [1, 2.1]`. -/
lemma mon_real_boundX (c a u η : ℝ) (m p q : ℕ) (ha1 : 1 ≤ a) (ha2 : a ≤ 43 / 20) :
    |c * (a⁻¹) ^ m * u ^ p * η ^ q * Real.exp (-(u ^ 2 + η ^ 2) / (4 * a))| ≤
      |c| * ((p.factorial : ℝ) * (q.factorial : ℝ) * Real.exp 50 * Real.exp 50) *
        Real.exp (-(u ^ 2 + η ^ 2) / 9) := by
  have ha0 : 0 < a := by linarith
  have hA0 : 0 ≤ (a⁻¹) ^ m := pow_nonneg (inv_nonneg.mpr ha0.le) m
  have hA1 : (a⁻¹) ^ m ≤ 1 := by
    apply pow_le_one₀ (inv_nonneg.mpr ha0.le)
    rw [inv_le_one₀ ha0]; exact ha1
  have hEpos : 0 < Real.exp (-(u ^ 2 + η ^ 2) / (4 * a)) := Real.exp_pos _
  have hR : 0 ≤ u ^ 2 + η ^ 2 := by positivity
  have key : (209 / 1800) * (u ^ 2 + η ^ 2) ≤ (u ^ 2 + η ^ 2) / (4 * a) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith [mul_nonneg hR (sub_nonneg.mpr ha2)]
  have hE : Real.exp (-(u ^ 2 + η ^ 2) / (4 * a)) ≤
      Real.exp (-(u ^ 2 + η ^ 2) / 9) * Real.exp (-(u ^ 2) / 200) * Real.exp (-(η ^ 2) / 200) := by
    simp only [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [neg_div]
    have e1 : -(u ^ 2 + η ^ 2) / 9 + -(u ^ 2) / 200 + -(η ^ 2) / 200
        = -((209 / 1800) * (u ^ 2 + η ^ 2)) := by ring
    rw [e1]
    linarith [key]
  have hEq : |c * (a⁻¹) ^ m * u ^ p * η ^ q * Real.exp (-(u ^ 2 + η ^ 2) / (4 * a))| =
      |c| * (a⁻¹) ^ m * |u| ^ p * |η| ^ q * Real.exp (-(u ^ 2 + η ^ 2) / (4 * a)) := by
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hA0, abs_pow, abs_pow,
      abs_of_pos hEpos]
  have hU := pow_abs_le_fact_expX p u
  have hη := pow_abs_le_fact_expX q η
  have hu2 := exp_abs_mul_gauss_leX u
  have hη2 := exp_abs_mul_gauss_leX η
  have hpos_c : 0 ≤ |c| := abs_nonneg c
  rw [hEq]
  calc |c| * (a⁻¹) ^ m * |u| ^ p * |η| ^ q * Real.exp (-(u ^ 2 + η ^ 2) / (4 * a))
      ≤ |c| * 1 * ((p.factorial : ℝ) * Real.exp |u|) * ((q.factorial : ℝ) * Real.exp |η|) *
          (Real.exp (-(u ^ 2 + η ^ 2) / 9) * Real.exp (-(u ^ 2) / 200) *
            Real.exp (-(η ^ 2) / 200)) := by
        gcongr
    _ = |c| * ((p.factorial : ℝ) * (q.factorial : ℝ)) *
          ((Real.exp |u| * Real.exp (-(u ^ 2) / 200)) *
            (Real.exp |η| * Real.exp (-(η ^ 2) / 200))) * Real.exp (-(u ^ 2 + η ^ 2) / 9) := by
        ring
    _ ≤ |c| * ((p.factorial : ℝ) * (q.factorial : ℝ)) * (Real.exp 50 * Real.exp 50) *
          Real.exp (-(u ^ 2 + η ^ 2) / 9) := by
        have hpq : 0 ≤ |c| * ((p.factorial : ℝ) * (q.factorial : ℝ)) := by positivity
        have hprod : (Real.exp |u| * Real.exp (-(u ^ 2) / 200)) *
            (Real.exp |η| * Real.exp (-(η ^ 2) / 200)) ≤ Real.exp 50 * Real.exp 50 :=
          mul_le_mul hu2 hη2 (by positivity) (by positivity)
        have hg : 0 ≤ Real.exp (-(u ^ 2 + η ^ 2) / 9) := Real.exp_nonneg _
        nlinarith [mul_le_mul_of_nonneg_right hprod hg, mul_le_mul_of_nonneg_left hprod hpq]
    _ = |c| * ((p.factorial : ℝ) * (q.factorial : ℝ) * Real.exp 50 * Real.exp 50) *
          Real.exp (-(u ^ 2 + η ^ 2) / 9) := by
        ring

theorem gMon_domX (t : ℝ × ℕ × ℕ × ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ν : ℝ) (j : ℤ) (s : ℝ) (x : ℝ × ℝ),
      0 < ν → ν ≤ 1 → 0 < s → ν * s ≤ 23 / 20 →
        |gMon ν j t s x| ≤ K * latticeW gradAlpha gradK (x.1 - (j : ℝ) * cOf ν) x.2 := by
  refine ⟨|t.1| * ((t.2.2.1.factorial : ℝ) * (t.2.2.2.factorial : ℝ) * Real.exp 50 * Real.exp 50),
    by positivity, ?_⟩
  intro ν j s x hν _ hs hνs
  have hns : 0 < ν * s := mul_pos hν hs
  have ha1 : 1 ≤ ageA ν s := by unfold ageA; linarith
  have ha2 : ageA ν s ≤ 43 / 20 := by unfold ageA; linarith
  have hmon := mon_real_boundX t.1 (ageA ν s) (x.1 - (j : ℝ) * cOf ν) x.2 t.2.1 t.2.2.1 t.2.2.2
    ha1 ha2
  have hK : 0 ≤ |t.1| * ((t.2.2.1.factorial : ℝ) * (t.2.2.2.factorial : ℝ) * Real.exp 50 *
      Real.exp 50) := by positivity
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
    _ ≤ |t.1| * ((t.2.2.1.factorial : ℝ) * (t.2.2.2.factorial : ℝ) * Real.exp 50 *
          Real.exp 50) * ((1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 12 *
          Real.exp (-(1 / 9 : ℝ) * ((x.1 - (j : ℝ) * cOf ν) ^ 2 + x.2 ^ 2))) :=
        mul_le_mul_of_nonneg_left hexp hK
    _ = _ := by ring

theorem gDomPropX : GDomPropX := by
  unfold GDomPropX
  intro e
  induction e with
  | nil =>
    exact ⟨0, le_rfl, fun ν j s x _ _ _ _ => by simp [gEval]⟩
  | cons t l ih =>
    obtain ⟨K, hK, hKb⟩ := gMon_domX t
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


theorem gBoundPropX : GBoundPropX := by
  have hD := gDomPropX
  unfold GDomPropX at hD
  choose Cf hCf0 hCf using hD
  unfold GBoundPropX
  intro e
  refine ⟨∑ r : Fin 3, ∑ a : Fin 2, ∑ b : Fin 2, Cf (e r a b), ?_, ?_⟩
  · exact Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun a _ =>
      Finset.sum_nonneg fun b _ => hCf0 (e r a b)
  · intro ν χf A j s x hν hν1 hs hνs
    have hG := gradF_nonneg ν χf A s
    have key : ∀ (r : Fin 3) (a b : Fin 2),
        |gCoef (Ay ν χf A) r s (mi a) (mi b) * gEval (e r a b) ν j s x| ≤
          gradF ν χf A s * (Cf (e r a b) * gradW ν x j) := by
      intro r a b
      rw [abs_mul]
      exact mul_le_mul (gb_coef_le ν χf A s r a b)
        (hCf (e r a b) ν j s x hν hν1 hs hνs) (abs_nonneg _) hG
    have hsum : |GSum e ν j (Ay ν χf A) s x| ≤ ∑ r : Fin 3, ∑ a : Fin 2, ∑ b : Fin 2,
        gradF ν χf A s * (Cf (e r a b) * gradW ν x j) := by
      unfold GSum
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ => ?_)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
      exact key r a b
    refine hsum.trans (le_of_eq ?_)
    simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun b _ => ?_
    ring


theorem psiExprs : ∃ (e0 e0q e0e e1 e1q e1e e2 : Fin 3 → Fin 2 → Fin 2 → GExpr),
    GLevel 0 e0 ∧ GLevel 1 e1 ∧
    ∀ (ν : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (j : ℤ) (s : ℝ), 0 < ν → 0 < s →
      ContDiffAt ℝ 2 (Ay ν χf A) s →
      GCombo e0 ν j (Ay ν χf A) s (gradPsiTm ν χf A j) ∧
      (∀ x, dQ (gradPsiTm ν χf A j) s x = GSum e0q ν j (Ay ν χf A) s x) ∧
      (∀ x, dEta (gradPsiTm ν χf A j) s x = GSum e0e ν j (Ay ν χf A) s x) ∧
      GCombo e1 ν j (Ay ν χf A) s (fun s' y => Kop (gradPsiTm ν χf A j) s' y) ∧
      (∀ x, dQ (fun s' y => Kop (gradPsiTm ν χf A j) s' y) s x
        = GSum e1q ν j (Ay ν χf A) s x) ∧
      (∀ x, dEta (fun s' y => Kop (gradPsiTm ν χf A j) s' y) s x
        = GSum e1e ν j (Ay ν χf A) s x) ∧
      GCombo e2 ν j (Ay ν χf A) s
        (fun s' y => Kop (fun s'' z => Kop (gradPsiTm ν χf A j) s'' z) s' y) := by
  obtain ⟨e0, hl0, hψ⟩ := gPsiProp
  obtain ⟨e0q, hl0q, hq0⟩ := gDqProp 0 e0 hl0
  obtain ⟨e0e, hl0e, he0⟩ := gDetaProp 0 e0 hl0
  obtain ⟨e1, hl1, hk1⟩ := gKopProp 0 (by norm_num) e0 hl0
  obtain ⟨e1q, hl1q, hq1⟩ := gDqProp 1 e1 hl1
  obtain ⟨e1e, hl1e, he1⟩ := gDetaProp 1 e1 hl1
  obtain ⟨e2, hl2, hk2⟩ := gKopProp 1 le_rfl e1 hl1
  refine ⟨e0, e0q, e0e, e1, e1q, e1e, e2, hl0, hl1, ?_⟩
  intro ν χf A j s hν hs hC2
  have hF0 := hψ ν χf A j hν s hs
  have hK1 := hk1 ν j _ s _ hν hs hC2 hF0
  have hK2 := hk2 ν j _ s _ hν hs hC2 hK1
  exact ⟨hF0, fun x => hq0 ν j _ s _ hν hs hF0 x, fun x => he0 ν j _ s _ hν hs hF0 x, hK1,
    fun x => hq1 ν j _ s _ hν hs hK1 x, fun x => he1 ν j _ s _ hν hs hK1 x, hK2⟩

def GradPsiTermEnvExt : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν s : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3), 0 < ν → ν ≤ 1 → 0 < s →
    ν * s ≤ 23 / 20 → ContDiffAt ℝ 2 (Ay ν χf A) s →
    ∀ (x : ℝ × ℝ) (m : Fin 7) (j : ℤ),
      |gradPsiOps m (gradPsiTm ν χf A j) s x| ≤ C * gradF ν χf A s * gradW ν x j

theorem gradPsiTermEnvExt : GradPsiTermEnvExt := by
  obtain ⟨e0, e0q, e0e, e1, e1q, e1e, e2, hl0, hl1, hS⟩ := psiExprs
  obtain ⟨C0, h0, b0⟩ := gBoundPropX e0
  obtain ⟨C1, h1, b1⟩ := gBoundPropX e0q
  obtain ⟨C2, h2, b2⟩ := gBoundPropX e0e
  obtain ⟨C3, h3, b3⟩ := gBoundPropX e1
  obtain ⟨C4, h4, b4⟩ := gBoundPropX e1q
  obtain ⟨C5, h5, b5⟩ := gBoundPropX e1e
  obtain ⟨C6, h6, b6⟩ := gBoundPropX e2
  refine ⟨C0 + C1 + C2 + C3 + C4 + C5 + C6, by positivity, ?_⟩
  intro ν s χf A hν hν1 hs hνs hC2 x m j
  have hFW : 0 ≤ gradF ν χf A s * gradW ν x j :=
    mul_nonneg (gradF_nonneg _ _ _ _) (gradW_nonneg _ _ _)
  have up : ∀ {v C' : ℝ}, 0 ≤ C' → C' ≤ C0 + C1 + C2 + C3 + C4 + C5 + C6 →
      |v| ≤ C' * gradF ν χf A s * gradW ν x j →
      |v| ≤ (C0 + C1 + C2 + C3 + C4 + C5 + C6) * gradF ν χf A s * gradW ν x j := by
    intro v C' hC' hle hv
    refine hv.trans ?_
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right hle hFW
  obtain ⟨hF0, hq0, he0, hK1, hq1, he1, hK2⟩ := hS ν χf A j s hν hs hC2
  fin_cases m
  · show |gradPsiTm ν χf A j s x| ≤ _
    rw [gCombo_self hF0 x]
    exact up h0 (by linarith) (b0 ν χf A j s x hν hν1 hs hνs)
  · show |dQ (gradPsiTm ν χf A j) s x| ≤ _
    rw [hq0 x]
    exact up h1 (by linarith) (b1 ν χf A j s x hν hν1 hs hνs)
  · show |dEta (gradPsiTm ν χf A j) s x| ≤ _
    rw [he0 x]
    exact up h2 (by linarith) (b2 ν χf A j s x hν hν1 hs hνs)
  · show |Kop (gradPsiTm ν χf A j) s x| ≤ _
    rw [show Kop (gradPsiTm ν χf A j) s x = GSum e1 ν j (Ay ν χf A) s x from
      gCombo_self hK1 x]
    exact up h3 (by linarith) (b3 ν χf A j s x hν hν1 hs hνs)
  · show |dQ (fun s' y => Kop (gradPsiTm ν χf A j) s' y) s x| ≤ _
    rw [hq1 x]
    exact up h4 (by linarith) (b4 ν χf A j s x hν hν1 hs hνs)
  · show |dEta (fun s' y => Kop (gradPsiTm ν χf A j) s' y) s x| ≤ _
    rw [he1 x]
    exact up h5 (by linarith) (b5 ν χf A j s x hν hν1 hs hνs)
  · show |Kop (fun s' y => Kop (gradPsiTm ν χf A j) s' y) s x| ≤ _
    rw [show Kop (fun s' y => Kop (gradPsiTm ν χf A j) s' y) s x
      = GSum e2 ν j (Ay ν χf A) s x from gCombo_self hK2 x]
    exact up h6 (by linarith) (b6 ν χf A j s x hν hν1 hs hνs)

end UnforcedLeray.Short.PartIIIb.Concrete
