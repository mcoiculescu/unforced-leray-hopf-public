import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_2_1.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.HpPsiTermSummable.Gauss

/-!
# `psiEnvLocSumm` (task `PartIII-b:C/asrc/ra/9/1/2/9/2/1/2`)
Source `the November 2 reference manuscript` lines 5063-5071, 5076-5079, 4979.
Scalar copy of `envLocSumm` (`ra_9_1_2_9_1_1/T3.lean`). A pointwise envelope bound
`|G j p| ≤ K s^{5/2} envTerm` on `s > 0` yields a locally uniform summable majorant near each `p`:
on a neighbourhood with `s/2 < s' < 2s`, `|x'-x| < 1`, the age is bounded and the Gaussian is
dominated by `exp(-α(x_1-jc)²)`; `gp_gauss_pow_summable` and `gp_gauss_summable` finish. The Hp
proof is run in norm form (`‖·‖ = |·|` on `ℝ`) and transported to `PsiLocSumm`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

lemma envT_one_add_pow_le_r (r : ℝ) (hr : 0 ≤ r) (m : ℕ) :
    (1 + r) ^ m ≤ 2 ^ m * (1 + r ^ m) := by
  rcases le_total r 1 with h | h
  · calc (1 + r) ^ m ≤ (2:ℝ) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
      _ ≤ 2 ^ m * (1 + r ^ m) :=
          le_mul_of_one_le_right (by positivity) (by linarith [pow_nonneg hr m])
  · calc (1 + r) ^ m ≤ (2 * r) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
      _ = 2 ^ m * r ^ m := mul_pow _ _ _
      _ ≤ 2 ^ m * (1 + r ^ m) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

set_option maxHeartbeats 2000000 in

theorem psiEnvLocSumm : PsiEnvLocSumm := by
  unfold PsiEnvLocSumm
  intro m ν K hν G hG0
  have hG : ∀ j, ∀ p ∈ UChart, ‖G j p‖ ≤ K * p.1 ^ (5 / 2 : ℝ) * envTerm m ν j p :=
    fun j p hp => by rw [Real.norm_eq_abs]; exact hG0 j p hp
  unfold PsiLocSumm
  suffices H : ∀ p ∈ UChart, ∃ N ∈ 𝓝 p, ∃ u : ℤ → ℝ, Summable u ∧ ∀ j, ∀ q ∈ N, ‖G j q‖ ≤ u j by
    intro p hp
    obtain ⟨N, hN, u, hu, hb⟩ := H p hp
    exact ⟨N, hN, u, hu, fun j q hq => by rw [← Real.norm_eq_abs]; exact hb j q hq⟩
  intro p hp
  have hs0 : 0 < p.1 := hp.1
  have hc : 0 < cOf ν := by unfold cOf; positivity
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = 1 + 2 * ν * p.1 := ⟨_, rfl⟩
  have hA : 0 < A := by rw [hAdef]; have := mul_pos hν hs0; linarith
  have hA8 : 0 < 8 * A := by linarith
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = 1 / (16 * A) := ⟨_, rfl⟩
  have hα : 0 < α := by rw [hαdef]; positivity
  have hαe : α = (1 / (8 * A)) / 2 := by rw [hαdef]; field_simp; ring
  have hTnn : 0 ≤ 1 + (|p.2.1| + |p.2.2| + 2) + cOf ν := by
    have := abs_nonneg p.2.1; have := abs_nonneg p.2.2; linarith
  have ht : 0 < 1 / (8 * A) := one_div_pos.mpr hA8
  -- neighbourhood
  have h1 : ∀ᶠ q : Chart in 𝓝 p, p.1 / 2 < q.1 :=
    continuousAt_const.eventually_lt continuous_fst.continuousAt (by show p.1 / 2 < p.1; linarith)
  have h2 : ∀ᶠ q : Chart in 𝓝 p, q.1 < 2 * p.1 :=
    continuous_fst.continuousAt.eventually_lt continuousAt_const (by show p.1 < 2 * p.1; linarith)
  have h3 : ∀ᶠ q : Chart in 𝓝 p, |q.2.1 - p.2.1| < 1 :=
    (show Continuous fun q : Chart => |q.2.1 - p.2.1| by fun_prop).continuousAt.eventually_lt
      continuousAt_const (by simp)
  have h4 : ∀ᶠ q : Chart in 𝓝 p, |q.2.2 - p.2.2| < 1 :=
    (show Continuous fun q : Chart => |q.2.2 - p.2.2| by fun_prop).continuousAt.eventually_lt
      continuousAt_const (by simp)
  have hN : ∀ᶠ q : Chart in 𝓝 p,
      (p.1 / 2 < q.1 ∧ q.1 < 2 * p.1) ∧ |q.2.1 - p.2.1| < 1 ∧ |q.2.2 - p.2.2| < 1 :=
    (h1.and h2).and (h3.and h4)
  -- summable majorant
  have hsum : Summable (fun j : ℤ =>
      (|K| * (2 * p.1) ^ (5 / 2 : ℝ) * (1 + (|p.2.1| + |p.2.2| + 2) + cOf ν) ^ m * 2 ^ m
        * Real.exp (1 / (8 * A))) *
        (|(j : ℝ)| ^ m * Real.exp (-α * (p.2.1 - (j : ℝ) * cOf ν) ^ 2)
          + Real.exp (-α * (p.2.1 - (j : ℝ) * cOf ν) ^ 2))) :=
    ((gp_gauss_pow_summable p.2.1 α (cOf ν) hα hc m).add
      (gp_gauss_summable p.2.1 α (cOf ν) hα hc)).mul_left _
  refine ⟨{q : Chart | (p.1 / 2 < q.1 ∧ q.1 < 2 * p.1) ∧ |q.2.1 - p.2.1| < 1 ∧ |q.2.2 - p.2.2| < 1},
    hN, _, hsum, ?_⟩
  intro j q hq
  obtain ⟨⟨hq1, hq2⟩, hq3, hq4⟩ := hq
  have hq0 : 0 < q.1 := by linarith
  have hqU : q ∈ UChart := ⟨hq0, Set.mem_univ _⟩
  have hGq := hG j q hqU
  have hage : 0 < ageA ν q.1 := by
    unfold ageA; have := mul_pos hν hq0; linarith
  have hageA : ageA ν q.1 ≤ A := by
    unfold ageA; rw [hAdef]; have := mul_le_mul_of_nonneg_left hq2.le hν.le; linarith
  have hrp : q.1 ^ (5 / 2 : ℝ) ≤ (2 * p.1) ^ (5 / 2 : ℝ) :=
    Real.rpow_le_rpow hq0.le (by linarith) (by norm_num)
  have hKs : K * q.1 ^ (5 / 2 : ℝ) ≤ |K| * (2 * p.1) ^ (5 / 2 : ℝ) :=
    calc K * q.1 ^ (5 / 2 : ℝ) ≤ |K| * q.1 ^ (5 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right (le_abs_self K) (Real.rpow_nonneg hq0.le _)
      _ ≤ |K| * (2 * p.1) ^ (5 / 2 : ℝ) := mul_le_mul_of_nonneg_left hrp (abs_nonneg K)
  -- exponent
  have hSnn : 0 ≤ sq2 (xj ν j q.2) := by unfold sq2; positivity
  have hsq : sq2 (xj ν j q.2) = (q.2.1 - (j : ℝ) * cOf ν) ^ 2 + q.2.2 ^ 2 := rfl
  have hS_ge : (q.2.1 - (j : ℝ) * cOf ν) ^ 2 ≤ sq2 (xj ν j q.2) := by
    rw [hsq]; linarith [sq_nonneg q.2.2]
  have hb2 : (q.2.1 - p.2.1) ^ 2 < 1 := by
    have h := abs_lt.mp hq3
    nlinarith [mul_pos (show (0:ℝ) < 1 - (q.2.1 - p.2.1) by linarith [h.2])
      (show (0:ℝ) < 1 + (q.2.1 - p.2.1) by linarith [h.1])]
  have hd : (p.2.1 - (j : ℝ) * cOf ν) ^ 2 ≤ 2 * (q.2.1 - (j : ℝ) * cOf ν) ^ 2 + 2 := by
    linarith [sq_nonneg ((q.2.1 - (j : ℝ) * cOf ν) - (p.2.1 - q.2.1))]
  have e1 : -(sq2 (xj ν j q.2)) / (8 * ageA ν q.1) ≤ -(sq2 (xj ν j q.2)) / (8 * A) := by
    have h8 : 0 < 8 * ageA ν q.1 := mul_pos (by norm_num) hage
    rw [neg_div, neg_div]
    apply neg_le_neg
    exact div_le_div_of_nonneg_left hSnn h8 (by linarith)
  have key : -(sq2 (xj ν j q.2)) / (8 * A)
      ≤ -α * (p.2.1 - (j : ℝ) * cOf ν) ^ 2 + 1 / (8 * A) := by
    have e2 : -(sq2 (xj ν j q.2)) / (8 * A) = -(sq2 (xj ν j q.2)) * (1 / (8 * A)) := by ring
    rw [e2, hαe]
    have k1 := mul_le_mul_of_nonneg_right hS_ge ht.le
    have k2 := mul_le_mul_of_nonneg_right hd ht.le
    linarith
  have hexp : Real.exp (-(sq2 (xj ν j q.2)) / (8 * ageA ν q.1))
      ≤ Real.exp (1 / (8 * A)) * Real.exp (-α * (p.2.1 - (j : ℝ) * cOf ν) ^ 2) := by
    calc Real.exp (-(sq2 (xj ν j q.2)) / (8 * ageA ν q.1))
        ≤ Real.exp (-α * (p.2.1 - (j : ℝ) * cOf ν) ^ 2 + 1 / (8 * A)) :=
          Real.exp_le_exp.mpr (le_trans e1 key)
      _ = Real.exp (1 / (8 * A)) * Real.exp (-α * (p.2.1 - (j : ℝ) * cOf ν) ^ 2) := by
          rw [add_comm, Real.exp_add]
  -- polynomial factor
  have hc' : 0 ≤ cOf ν := hc.le
  have hnorm : ‖xj ν j q.2‖ ≤ |p.2.1| + |p.2.2| + 2 + cOf ν * |(j : ℝ)| := by
    have hj : (j : ℝ) * cOf ν ≤ |(j : ℝ)| * cOf ν :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hc'
    have hj' : -|(j : ℝ)| * cOf ν ≤ (j : ℝ) * cOf ν :=
      mul_le_mul_of_nonneg_right (neg_abs_le _) hc'
    have hA1 := abs_lt.mp hq3
    have hA2 := abs_lt.mp hq4
    have hn1 := neg_abs_le p.2.1
    have hn2 := le_abs_self p.2.1
    have hn3 := neg_abs_le p.2.2
    have hn4 := le_abs_self p.2.2
    have hp1 := abs_nonneg p.2.1
    have hp2 := abs_nonneg p.2.2
    have hq5 := mul_nonneg hc' (abs_nonneg (j : ℝ))
    rw [Prod.norm_def]
    apply max_le
    · rw [Real.norm_eq_abs]
      show |q.2.1 - (j : ℝ) * cOf ν| ≤ _
      rw [abs_le]
      constructor
      · linarith [hA1.1, hA1.2, hn1, hj, hp2, hq5]
      · linarith [hA1.1, hA1.2, hn2, hj', hp2, hq5]
    · rw [Real.norm_eq_abs]
      show |q.2.2| ≤ _
      rw [abs_le]
      constructor
      · linarith [hA2.1, hA2.2, hn3, hp1, hq5]
      · linarith [hA2.1, hA2.2, hn4, hp1, hq5]
  have hpoly1 : 1 + ‖xj ν j q.2‖
      ≤ (1 + (|p.2.1| + |p.2.2| + 2) + cOf ν) * (1 + |(j : ℝ)|) := by
    have := mul_nonneg (abs_nonneg (j : ℝ))
      (by positivity : (0:ℝ) ≤ 1 + (|p.2.1| + |p.2.2| + 2))
    linarith [hc, hnorm]
  have hpoly : (1 + ‖xj ν j q.2‖) ^ m
      ≤ (1 + (|p.2.1| + |p.2.2| + 2) + cOf ν) ^ m * (2 ^ m * (1 + |(j : ℝ)| ^ m)) := by
    calc (1 + ‖xj ν j q.2‖) ^ m
        ≤ ((1 + (|p.2.1| + |p.2.2| + 2) + cOf ν) * (1 + |(j : ℝ)|)) ^ m :=
          pow_le_pow_left₀ (by positivity) hpoly1 m
      _ = (1 + (|p.2.1| + |p.2.2| + 2) + cOf ν) ^ m * (1 + |(j : ℝ)|) ^ m := mul_pow _ _ _
      _ ≤ (1 + (|p.2.1| + |p.2.2| + 2) + cOf ν) ^ m * (2 ^ m * (1 + |(j : ℝ)| ^ m)) :=
          mul_le_mul_of_nonneg_left (envT_one_add_pow_le_r _ (abs_nonneg _) m)
            (pow_nonneg hTnn m)
  -- the envelope term
  have hEnvNN : 0 ≤ envTerm m ν j q := by unfold envTerm; positivity
  have henv : envTerm m ν j q ≤
      ((1 + (|p.2.1| + |p.2.2| + 2) + cOf ν) ^ m * (2 ^ m * (1 + |(j : ℝ)| ^ m)))
        * (Real.exp (1 / (8 * A)) * Real.exp (-α * (p.2.1 - (j : ℝ) * cOf ν) ^ 2)) := by
    unfold envTerm
    exact mul_le_mul hpoly hexp (Real.exp_pos _).le
      (mul_nonneg (pow_nonneg hTnn m) (by positivity))
  have hC0 : 0 ≤ |K| * (2 * p.1) ^ (5 / 2 : ℝ) :=
    mul_nonneg (abs_nonneg K) (Real.rpow_nonneg (by linarith) _)
  calc ‖G j q‖ ≤ K * q.1 ^ (5 / 2 : ℝ) * envTerm m ν j q := hGq
    _ ≤ |K| * (2 * p.1) ^ (5 / 2 : ℝ) * envTerm m ν j q :=
        mul_le_mul_of_nonneg_right hKs hEnvNN
    _ ≤ |K| * (2 * p.1) ^ (5 / 2 : ℝ) *
          (((1 + (|p.2.1| + |p.2.2| + 2) + cOf ν) ^ m * (2 ^ m * (1 + |(j : ℝ)| ^ m)))
            * (Real.exp (1 / (8 * A)) * Real.exp (-α * (p.2.1 - (j : ℝ) * cOf ν) ^ 2))) :=
        mul_le_mul_of_nonneg_left henv hC0
    _ = (|K| * (2 * p.1) ^ (5 / 2 : ℝ) * (1 + (|p.2.1| + |p.2.2| + 2) + cOf ν) ^ m * 2 ^ m
          * Real.exp (1 / (8 * A))) *
          (|(j : ℝ)| ^ m * Real.exp (-α * (p.2.1 - (j : ℝ) * cOf ν) ^ 2)
            + Real.exp (-α * (p.2.1 - (j : ℝ) * cOf ν) ^ 2)) := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
