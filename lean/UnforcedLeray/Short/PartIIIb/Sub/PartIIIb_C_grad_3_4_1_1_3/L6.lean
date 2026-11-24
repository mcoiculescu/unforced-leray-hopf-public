import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1_3.L5
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1.L1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1_2

/-!
# `PartIII-b:C/grad/3/4/1/1/3/6`: s-local majorants of the lattice terms of `h^p_A`

Source `the November 2 reference manuscript`
4963-4980, 5036-5039, 5063-5079.

`hpSData : HpSData` from `gradHpTm_sDeriv` (L5): near `s`, `t ≥ s/2`, `ν t ≤ 23/20`, and
`Ay` is `C²` so `frob (Ay t)` and `frob (deriv (Ay) t)` are bounded.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem hpSData : HpSData := by
  unfold HpSData
  intro ν s χf A hd x i
  unfold GradData at hd
  obtain ⟨hν, hν1, hs, hsb, hC2⟩ := hd
  obtain ⟨C, hC, hD⟩ := gradHpTm_sDeriv
  have hfro : Continuous frob := by unfold frob; fun_prop
  have hf0 : ∀ B : Mat3, 0 ≤ frob B := fun B => by unfold frob; positivity
  have hsν : s * ν ≤ 11 / 10 := (le_div_iff₀ hν).mp hsb
  have hC1 : ContDiffAt ℝ 1 (deriv (Ay ν χf A)) s := hC2.derivWithin (by norm_num)
  have hcont0 : ContinuousAt (fun t => frob (Ay ν χf A t)) s :=
    hfro.continuousAt.comp hC2.continuousAt
  have hcont1 : ContinuousAt (fun t => frob (deriv (Ay ν χf A) t)) s :=
    hfro.continuousAt.comp hC1.continuousAt
  have hev0 : ∀ᶠ t in nhds s, frob (Ay ν χf A t) < frob (Ay ν χf A s) + 1 :=
    hcont0.eventually_lt continuousAt_const (lt_add_one _)
  have hev1 : ∀ᶠ t in nhds s, frob (deriv (Ay ν χf A) t) < frob (deriv (Ay ν χf A) s) + 1 :=
    hcont1.eventually_lt continuousAt_const (lt_add_one _)
  have hev2 : ∀ᶠ t in nhds s, ContDiffAt ℝ 2 (Ay ν χf A) t :=
    hC2.eventually (by norm_num)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hev0.and (hev1.and hev2))
  obtain ⟨r, hr_def⟩ : ∃ r : ℝ, r = min ε (min (s / 2) (1 / (20 * ν))) := ⟨_, rfl⟩
  have hr : 0 < r := by
    rw [hr_def]
    exact lt_min hε (lt_min (by linarith) (by positivity))
  have hrε : r ≤ ε := by rw [hr_def]; exact min_le_left _ _
  have hrs : r ≤ s / 2 := by rw [hr_def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hrν : r ≤ 1 / (20 * ν) := by
    rw [hr_def]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hrν' : r * ν ≤ 1 / 20 := by
    have h := (le_div_iff₀ (by positivity : (0 : ℝ) < 20 * ν)).mp hrν
    have e : r * (20 * ν) = 20 * (r * ν) := by ring
    linarith
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (2 / s) * (C * ((frob (Ay ν χf A s) + 1) +
      (23 / 20) / ν * (frob (deriv (Ay ν χf A) s) + 1))) := ⟨_, rfl⟩
  refine ⟨r, hr, fun j => K * gradW ν x j,
    (gradW_summable gradLatticeSummable ν hν x).mul_left K, ?_⟩
  intro j t ht
  have ht' := Metric.mem_ball.mp ht
  have hdist : dist t s < ε := lt_of_lt_of_le ht' hrε
  obtain ⟨hP0, hP1, hP2⟩ := hball hdist
  rw [Real.dist_eq, abs_sub_lt_iff] at ht'
  obtain ⟨h1, h2⟩ := ht'
  have htpos : 0 < t := by linarith
  have hs2 : s / 2 ≤ t := by linarith
  have htν : t * ν ≤ 23 / 20 := by
    have e : t * ν = s * ν + (t - s) * ν := by ring
    have h3 : (t - s) * ν ≤ r * ν := mul_le_mul_of_nonneg_right h1.le hν.le
    linarith
  have htb : t ≤ (23 / 20) / ν := (le_div_iff₀ hν).mpr htν
  have hAd : DifferentiableAt ℝ (Ay ν χf A) t := hP2.differentiableAt (by norm_num)
  obtain ⟨hdiff, hbound⟩ := hD ν t χf A j x i hν hν1 htpos htb hAd
  refine ⟨hdiff, ?_⟩
  have hW := gradW_nonneg ν x j
  have hsum_bd : frob (Ay ν χf A t) + t * frob (deriv (Ay ν χf A) t) ≤
      (frob (Ay ν χf A s) + 1) + (23 / 20) / ν * (frob (deriv (Ay ν χf A) s) + 1) := by
    have h4 : t * frob (deriv (Ay ν χf A) t) ≤ (23 / 20) / ν * (frob (deriv (Ay ν χf A) s) + 1) :=
      mul_le_mul htb hP1.le (hf0 _) (div_nonneg (by norm_num) hν.le)
    linarith [hP0.le]
  have hmain : t * ‖deriv (fun t' => gradHpTm i ν χf A j t' x) t‖ ≤
      C * ((frob (Ay ν χf A s) + 1) + (23 / 20) / ν * (frob (deriv (Ay ν χf A) s) + 1)) *
        gradW ν x j :=
    le_trans hbound (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum_bd hC) hW)
  have hsne : s ≠ 0 := hs.ne'
  have hdnorm : ‖deriv (fun t' => gradHpTm i ν χf A j t' x) t‖ ≤
      (2 / s) * (t * ‖deriv (fun t' => gradHpTm i ν χf A j t' x) t‖) := by
    have hm : (s / 2) * ‖deriv (fun t' => gradHpTm i ν χf A j t' x) t‖ ≤
        t * ‖deriv (fun t' => gradHpTm i ν χf A j t' x) t‖ :=
      mul_le_mul_of_nonneg_right hs2 (norm_nonneg _)
    calc ‖deriv (fun t' => gradHpTm i ν χf A j t' x) t‖
        = (2 / s) * ((s / 2) * ‖deriv (fun t' => gradHpTm i ν χf A j t' x) t‖) := by
          field_simp
      _ ≤ (2 / s) * (t * ‖deriv (fun t' => gradHpTm i ν χf A j t' x) t‖) :=
          mul_le_mul_of_nonneg_left hm (div_nonneg (by norm_num) hs.le)
  show ‖deriv (fun t' => gradHpTm i ν χf A j t' x) t‖ ≤ K * gradW ν x j
  calc ‖deriv (fun t' => gradHpTm i ν χf A j t' x) t‖
      ≤ (2 / s) * (t * ‖deriv (fun t' => gradHpTm i ν χf A j t' x) t‖) := hdnorm
    _ ≤ (2 / s) * (C * ((frob (Ay ν χf A s) + 1) + (23 / 20) / ν *
          (frob (deriv (Ay ν χf A) s) + 1)) * gradW ν x j) :=
          mul_le_mul_of_nonneg_left hmain (div_nonneg (by norm_num) hs.le)
    _ = K * gradW ν x j := by rw [hK]; ring

end UnforcedLeray.Short.PartIIIb.Concrete
