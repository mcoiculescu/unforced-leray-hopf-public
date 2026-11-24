import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_5_2.T2
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# `PartIII-b:C/grad/3/5/2/2`: `PsipALocUnif` from jet bounds of `ψ_j` and `A^y`

Source `the November 2 reference manuscript`
5063-5079, 4974-4980.  The term `ψ^p_A,j = (tr A^y_mer) ψ_j - (A^y_mer x_j)·∇ψ_j` is bounded
(with its derivatives of order `≤ 2`) by the Leibniz rule from

* `PsijJets`: derivatives of order `≤ 3` of `(s,x) ↦ ψ_j` are `≤ C (1+|j|)^m e^{-c j²}` on `U`
  (Gaussian in `x_j`, `|x_j| ≥ c₀|j| - R`, `s ∈ [s₀,s₁]`, `s₀>0`);
* `AyJets`: derivatives of order `≤ 2` of `tr A^y_mer` are bounded, and of `A^y_mer x_j` by
  `M (1+|j|)` (`A^y` is `C^6` on `(0,∞)`, compactness of `closure U`).

Proved: `psipALocUnif_of`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Source 5063-5079: jet bounds of order `≤ 3` for `ψ_j` on a bounded convex open `U`
with closure in `{s>0}`. -/
def PsijJets : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ U : Set Chart, IsOpen U → Convex ℝ U → closure U ⊆ {p : Chart | 0 < p.1} →
    Bornology.IsBounded (closure U) →
    ∃ (C c : ℝ) (m : ℕ), 0 ≤ C ∧ 0 < c ∧ ∀ k ≤ 3, ∀ j : ℤ, ∀ p ∈ U,
      ‖iteratedFDerivWithin ℝ k (fun q : Chart => psij ν q.1 j q.2) U p‖
        ≤ C * (1 + |(j : ℝ)|) ^ m * Real.exp (-c * (j : ℝ) ^ 2)

/-- Source 4974-4980, 5063-5079: jet bounds of order `≤ 2` for the `A^y` factors. -/
def AyJets (as : ℝ) : Prop :=
  ∀ (χ : ℝ → ℝ), IsSourceCutoffC χ → ∀ (ν : ℝ), 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A →
    ∀ U : Set Chart, IsOpen U → Convex ℝ U → closure U ⊆ {p : Chart | 0 < p.1} →
      Bornology.IsBounded (closure U) →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ k ≤ 2, ∀ p ∈ U,
        ‖iteratedFDerivWithin ℝ k (fun q : Chart => merTrace (Ay ν χ A q.1)) U p‖ ≤ M ∧
        ∀ j : ℤ, ‖iteratedFDerivWithin ℝ k
          (fun q : Chart => merApply (Ay ν χ A q.1) (xj ν j q.2)) U p‖ ≤ M * (1 + |(j : ℝ)|)

lemma pla_summable_poly_gauss (m : ℕ) (c : ℝ) (hc : 0 < c) :
    Summable (fun j : ℤ => (1 + |(j : ℝ)|) ^ m * Real.exp (-c * (j : ℝ) ^ 2)) := by
  have hnat : Summable (fun n : ℕ => (1 + |((n : ℤ) : ℝ)|) ^ m * Real.exp (-c * ((n : ℤ) : ℝ) ^ 2)) := by
    have h1 := (Real.summable_pow_mul_exp_neg_nat_mul 0 hc)
    have h2 := (Real.summable_pow_mul_exp_neg_nat_mul m hc)
    have h3 : Summable (fun n : ℕ => (2 : ℝ) ^ m * (Real.exp (-c * n) + (n : ℝ) ^ m * Real.exp (-c * n))) :=
      ((by simpa using h1 : Summable (fun n : ℕ => Real.exp (-c * n))).add h2).mul_left _
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) h3
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have e1 : Real.exp (-c * ((n : ℤ) : ℝ) ^ 2) ≤ Real.exp (-c * n) := by
      apply Real.exp_le_exp.2
      have : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
        rcases Nat.eq_zero_or_pos n with h | h
        · simp [h]
        · have : (1 : ℝ) ≤ n := by exact_mod_cast h
          nlinarith
      simp only [Int.cast_natCast]
      nlinarith
    have e2 : (1 + |((n : ℤ) : ℝ)|) ^ m ≤ (2 : ℝ) ^ m * (1 + (n : ℝ) ^ m) := by
      simp only [Int.cast_natCast, abs_of_nonneg hn]
      rcases le_total (n : ℝ) 1 with h | h
      · calc (1 + (n : ℝ)) ^ m ≤ 2 ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
          _ ≤ _ := by nlinarith [pow_nonneg hn m, pow_pos (by norm_num : (0:ℝ) < 2) m]
      · calc (1 + (n : ℝ)) ^ m ≤ (2 * n) ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
          _ = 2 ^ m * (n : ℝ) ^ m := mul_pow _ _ _
          _ ≤ _ := by nlinarith [pow_nonneg hn m, pow_pos (by norm_num : (0:ℝ) < 2) m]
    calc (1 + |((n : ℤ) : ℝ)|) ^ m * Real.exp (-c * ((n : ℤ) : ℝ) ^ 2)
        ≤ ((2 : ℝ) ^ m * (1 + (n : ℝ) ^ m)) * Real.exp (-c * n) :=
          mul_le_mul e2 e1 (Real.exp_pos _).le (by positivity)
      _ = _ := by ring
  have hneg : Summable (fun n : ℕ => (1 + |((-(n : ℤ) : ℤ) : ℝ)|) ^ m * Real.exp (-c * ((-(n : ℤ) : ℤ) : ℝ) ^ 2)) := by
    refine hnat.congr (fun n => ?_)
    simp
  exact Summable.of_nat_of_neg hnat hneg

lemma pla_sum_choose_le (k : ℕ) (a b : ℕ → ℝ) (A B : ℝ) (hA : ∀ i ≤ k, a i ≤ A)
    (hB : ∀ i ≤ k, b i ≤ B) (_ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hA0 : 0 ≤ A) :
    ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * a i * b (k - i) ≤ 2 ^ k * A * B := by
  have hB0 : 0 ≤ B := le_trans (hb 0) (hB 0 (Nat.zero_le _))
  calc ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * a i * b (k - i)
      ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * A * B := by
        apply Finset.sum_le_sum
        intro i hi
        have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        have h1 := hA i hik
        have h2 := hB (k - i) (Nat.sub_le _ _)
        have := Nat.cast_nonneg (α := ℝ) (k.choose i)
        exact mul_le_mul (mul_le_mul_of_nonneg_left h1 this) h2 (hb _) (mul_nonneg this hA0)
    _ = (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)) * A * B := by
        rw [Finset.sum_mul, Finset.sum_mul]
    _ = 2 ^ k * A * B := by
        have : (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)) = 2 ^ k := by
          exact_mod_cast Nat.sum_range_choose k
        rw [this]


/-- Source 5063-5079: jet bounds of order `≤ 3` for the Gaussian factor `exp(-|x_j|²/(4a))`. -/
def PsijExpJets : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ U : Set Chart, IsOpen U → Convex ℝ U → closure U ⊆ {p : Chart | 0 < p.1} →
    Bornology.IsBounded (closure U) →
    ∃ (C c : ℝ) (m : ℕ), 0 ≤ C ∧ 0 < c ∧ ∀ k ≤ 3, ∀ j : ℤ, ∀ p ∈ U,
      ‖iteratedFDerivWithin ℝ k
        (fun q : Chart => Real.exp (-(sq2 (xj ν j q.2)) / (4 * ageA ν q.1))) U p‖
        ≤ C * (1 + |(j : ℝ)|) ^ m * Real.exp (-c * (j : ℝ) ^ 2)

/-- Source 5063-5079: jet bounds of order `≤ 3` for the prefactor `-2 a⁻¹`, `a = 1+νs`. -/
def AgeInvJets : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ U : Set Chart, IsOpen U → Convex ℝ U → closure U ⊆ {p : Chart | 0 < p.1} →
    Bornology.IsBounded (closure U) →
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k ≤ 3, ∀ p ∈ U,
      ‖iteratedFDerivWithin ℝ k (fun q : Chart => -2 * (ageA ν q.1)⁻¹) U p‖ ≤ M

theorem psijJets_of (h1 : PsijExpJets) (h2 : AgeInvJets) : PsijJets := by
  intro ν hν U hUo hUc hcl hbd
  obtain ⟨C, c, m, hC0, hc, hE⟩ := h1 ν hν U hUo hUc hcl hbd
  obtain ⟨M, hM0, hI⟩ := h2 ν hν U hUo hUc hcl hbd
  have hUU : UniqueDiffOn ℝ U := hUo.uniqueDiffOn
  have hUpos : U ⊆ {p : Chart | 0 < p.1} := fun p hp => hcl (subset_closure hp)
  refine ⟨8 * M * C, c, m, by positivity, hc, ?_⟩
  intro k hk j p hp
  have ha : ContDiff ℝ 3 (fun p : Chart => ageA ν p.1) := by
    unfold ageA
    fun_prop
  have hden : ContDiff ℝ 3 (fun p : Chart => 4 * ageA ν p.1) := by
    unfold ageA
    fun_prop
  have hg : ContDiff ℝ 3 (fun p : Chart => -(sq2 (xj ν j p.2))) := by
    unfold sq2 xj
    fun_prop
  have hinv : ContDiffOn ℝ 3 (fun p : Chart => (ageA ν p.1)⁻¹) {p : Chart | 0 < p.1} :=
    ContDiffOn.inv ha.contDiffOn (fun p hp => psc2_ageA_ne ν hν p hp)
  have hdiv : ContDiffOn ℝ 3 (fun p : Chart => -(sq2 (xj ν j p.2)) / (4 * ageA ν p.1))
      {p : Chart | 0 < p.1} :=
    ContDiffOn.div hg.contDiffOn hden.contDiffOn
      (fun p hp => mul_ne_zero (by norm_num) (psc2_ageA_ne ν hν p hp))
  have hexp : ContDiffOn ℝ 3 (fun p : Chart => Real.exp (-(sq2 (xj ν j p.2)) / (4 * ageA ν p.1)))
      {p : Chart | 0 < p.1} :=
    Real.contDiff_exp.comp_contDiffOn hdiv
  have hI3 : ContDiffOn ℝ 3 (fun p : Chart => -2 * (ageA ν p.1)⁻¹) U :=
    ((contDiffOn_const (c := (-2 : ℝ))).mul hinv).mono hUpos
  have hE3 := hexp.mono hUpos
  have hkN : (k : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hk
  have hP := norm_iteratedFDerivWithin_mul_le hI3 hE3 hUU hp hkN
  refine hP.trans ?_
  have hBp0 : 0 ≤ C * (1 + |(j : ℝ)|) ^ m * Real.exp (-c * (j : ℝ) ^ 2) := by positivity
  refine (pla_sum_choose_le k (fun i => ‖iteratedFDerivWithin ℝ i
      (fun q : Chart => -2 * (ageA ν q.1)⁻¹) U p‖)
    (fun i => ‖iteratedFDerivWithin ℝ i
      (fun q : Chart => Real.exp (-(sq2 (xj ν j q.2)) / (4 * ageA ν q.1))) U p‖) M
    (C * (1 + |(j : ℝ)|) ^ m * Real.exp (-c * (j : ℝ) ^ 2))
    (fun i hi => hI i (hi.trans hk) p hp) (fun i hi => hE i (hi.trans hk) j p hp)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) hM0).trans ?_
  have hk8 : (2 : ℝ) ^ k ≤ 8 := by
    interval_cases k <;> norm_num
  have := mul_nonneg hM0 hBp0
  nlinarith

theorem psipALocUnif_of (as : ℝ) (h1 : PsijJets) (h2 : AyJets as) : PsipALocUnif as := by
  intro χ hχ ν hν A hA U hUo hUc hcl hbd
  obtain ⟨C, c, m, hC0, hc, hψ⟩ := h1 ν hν U hUo hUc hcl hbd
  obtain ⟨M, hM0, hTW⟩ := h2 χ hχ ν hν A hA U hUo hUc hcl hbd
  have hUU : UniqueDiffOn ℝ U := hUo.uniqueDiffOn
  have hUpos : U ⊆ {p : Chart | 0 < p.1} := fun p hp => hcl (subset_closure hp)
  refine ⟨fun _ j => 8 * M * C * ((1 + |(j : ℝ)|) ^ (m + 1) * Real.exp (-c * (j : ℝ) ^ 2)),
    fun k _ => ((pla_summable_poly_gauss (m + 1) c hc).mul_left _), ?_⟩
  intro k hk j p hp
  -- smoothness
  have hA6 : ContDiffOn ℝ 6 (Ay ν χ A) (Ioi 0) := psc2_Ay_contDiffOn ν χ hχ A hA.smooth
  have hAy2 : ContDiffOn ℝ 2 (fun p : Chart => Ay ν χ A p.1) {p : Chart | 0 < p.1} :=
    (hA6.of_le (by norm_num)).comp contDiff_fst.contDiffOn (fun p hp => hp)
  have hxj2 : ContDiffOn ℝ 2 (fun p : Chart => xj ν j p.2) {p : Chart | 0 < p.1} := by
    have : ContDiff ℝ 2 (fun p : Chart => xj ν j p.2) := by
      unfold xj
      fun_prop
    exact this.contDiffOn
  have hW : ContDiffOn ℝ 2 (fun p : Chart => merApply (Ay ν χ A p.1) (xj ν j p.2))
      {p : Chart | 0 < p.1} :=
    psc2_merApply_contDiffOn (fun p : Chart => Ay ν χ A p.1) (fun p : Chart => xj ν j p.2)
      hAy2 hxj2
  have hT : ContDiffOn ℝ 2 (fun p : Chart => merTrace (Ay ν χ A p.1)) {p : Chart | 0 < p.1} := by
    unfold merTrace
    exact (psc2_entry_contDiffOn (fun p : Chart => Ay ν χ A p.1) hAy2 0 0).add
      (psc2_entry_contDiffOn (fun p : Chart => Ay ν χ A p.1) hAy2 2 2)
  have hG3 := psc2_psij_contDiffOn ν hν j
  have hG1 : ContDiffOn ℝ 1 (fun p : Chart => psij ν p.1 j p.2) {p : Chart | 0 < p.1} :=
    hG3.of_le (by norm_num)
  set ψ : Chart → ℝ := fun q => psij ν q.1 j q.2 with hψdef
  have hψ3 : ContDiffOn ℝ 3 ψ U := hG3.mono hUpos
  have hψ2 : ContDiffOn ℝ 2 ψ U := hψ3.of_le (by norm_num)
  have hT2 := hT.mono hUpos
  have hW2 := hW.mono hUpos
  set Tf : Chart → ℝ := fun q => merTrace (Ay ν χ A q.1) with hTf
  set Wf : Chart → ℝ × ℝ := fun q => merApply (Ay ν χ A q.1) (xj ν j q.2) with hWf
  have hFd : ContDiffOn ℝ 2 (fderivWithin ℝ ψ U) U := hψ3.fderivWithin hUU (by norm_num)
  have hg : ContDiffOn ℝ 2 (fun q : Chart => ((0 : ℝ), Wf q)) U :=
    contDiffOn_const.prodMk hW2
  -- rewrite the term
  have hEq : EqOn (psipATm ν χ A j)
      ((fun q => Tf q * ψ q) - (fun q => (fderivWithin ℝ ψ U q) ((0 : ℝ), Wf q))) U := by
    intro q hq
    have hq0 : 0 < q.1 := hUpos hq
    have e1 : fderiv ℝ (psij ν q.1 j) q.2 (Wf q) = fderivWithin ℝ ψ U q ((0 : ℝ), Wf q) := by
      rw [psc2_fderiv_x ψ hG1 q hq0, fderivWithin_of_isOpen hUo hq]
    simp only [psipATm, Pi.sub_apply, Tf, ψ]
    rw [e1]
  rw [iteratedFDerivWithin_congr hEq hp,
    iteratedFDerivWithin_sub_apply ((hT2.mul hψ2).contDiffWithinAt hp |>.of_le (by exact_mod_cast hk))
      ((hFd.clm_apply hg).contDiffWithinAt hp |>.of_le (by exact_mod_cast hk)) hUU hp]
  show _ ≤ 8 * M * C * ((1 + |(j : ℝ)|) ^ (m + 1) * Real.exp (-c * (j : ℝ) ^ 2))
  set Bp : ℝ := C * (1 + |(j : ℝ)|) ^ m * Real.exp (-c * (j : ℝ) ^ 2) with hBp
  have hBp0 : 0 ≤ Bp := by positivity
  have hj1 : (1 : ℝ) ≤ 1 + |(j : ℝ)| := by linarith [abs_nonneg (j : ℝ)]
  have hk2 : (2 : ℝ) ^ k ≤ 4 := by
    interval_cases k <;> norm_num
  have hkN : (k : WithTop ℕ∞) ≤ 2 := by exact_mod_cast hk
  have hP : ‖iteratedFDerivWithin ℝ k (fun x => Tf x * ψ x) U p‖ ≤ 4 * M * Bp := by
    refine (norm_iteratedFDerivWithin_mul_le hT2 hψ2 hUU hp hkN).trans ?_
    refine (pla_sum_choose_le k (fun i => ‖iteratedFDerivWithin ℝ i Tf U p‖)
      (fun i => ‖iteratedFDerivWithin ℝ i ψ U p‖) M Bp
      (fun i hi => (hTW i (hi.trans hk) p hp).1) (fun i hi => hψ i (by omega) j p hp)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) hM0).trans ?_
    have := mul_nonneg hM0 hBp0
    nlinarith
  have hinr : (fun q : Chart => ((0 : ℝ), Wf q)) =
      (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) ∘ Wf := by
    funext q; simp
  have hF : ‖iteratedFDerivWithin ℝ k (fun x => (fderivWithin ℝ ψ U x) ((0 : ℝ), Wf x)) U p‖
      ≤ 4 * Bp * (M * (1 + |(j : ℝ)|)) := by
    refine (norm_iteratedFDerivWithin_clm_apply hFd hg hUU hp hkN).trans ?_
    have hnb : ∀ i ≤ k, ‖iteratedFDerivWithin ℝ i (fun q : Chart => ((0 : ℝ), Wf q)) U p‖
        ≤ M * (1 + |(j : ℝ)|) := by
      intro i hi
      rw [hinr]
      refine ((ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)).norm_iteratedFDerivWithin_comp_left
        (hW2.contDiffWithinAt hp) hUU hp (by exact_mod_cast hi.trans hk)).trans ?_
      have h1 : ‖ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)‖ ≤ 1 :=
        ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun y => by simp)
      calc _ ≤ 1 * ‖iteratedFDerivWithin ℝ i Wf U p‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact (hTW i (hi.trans hk) p hp).2 j
    refine (pla_sum_choose_le k (fun i => ‖iteratedFDerivWithin ℝ i (fderivWithin ℝ ψ U) U p‖)
      (fun i => ‖iteratedFDerivWithin ℝ i (fun q : Chart => ((0 : ℝ), Wf q)) U p‖) Bp
      (M * (1 + |(j : ℝ)|)) (fun i hi => ?_) hnb (fun _ => norm_nonneg _)
      (fun _ => norm_nonneg _) hBp0).trans ?_
    · rw [norm_iteratedFDerivWithin_fderivWithin hUU hp]
      exact hψ (i + 1) (by omega) j p hp
    · have := mul_nonneg (mul_nonneg hM0 (by linarith : (0:ℝ) ≤ 1 + |(j : ℝ)|)) hBp0
      nlinarith
  have hx : 4 * M * Bp ≤ 4 * M * Bp * (1 + |(j : ℝ)|) :=
    le_mul_of_one_le_right (by positivity) hj1
  have hrw : 8 * M * C * ((1 + |(j : ℝ)|) ^ (m + 1) * Real.exp (-c * (j : ℝ) ^ 2))
      = 8 * M * Bp * (1 + |(j : ℝ)|) := by
    rw [hBp]; ring
  rw [hrw]
  refine (norm_sub_le _ _).trans ?_
  nlinarith

end UnforcedLeray.Short.PartIIIb.Concrete
