import UnforcedLeray.Short.PartIIIb.Concrete.YoungBlocks

/-!
# Application of the block Gronwall step to the retained estimates (source 4396-4411)

Shared by `Ybe1.lean` and `Ybe4.lean`: from `BlockGronwall` and `BlockSetup` we get uniform
constants `K2, g` with, for `n ≥ N`, `0 ≤ t ≤ α/ν_n` and every datum `x`,
`|A_j(H) - A_j(t)| ≤ K2 ν a` and `R(H) ≤ K2 (e^{-g(H-t)} R(t) + ν a)`,
`a = |A_+(t)| + |A_-(t)| + R(t)`, `H = Σ/ν_n`.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb

namespace ConcreteYF

theorem tail_ineq {K E ρ a ν CΔ Sg : ℝ} (hK0 : 0 ≤ K) (_hSg : 0 ≤ Sg) (hCS : 0 ≤ CΔ * Sg)
    (hC2 : 0 ≤ (1 + CΔ) ^ 2 * Sg) (hCΔ : 0 ≤ CΔ) (hE : 0 ≤ E) (hρ : 0 ≤ ρ) (ha : 0 ≤ a)
    (_ : True) :
    K * (E * ρ + ((CΔ * Sg + (1 + CΔ) + (1 + CΔ) ^ 2 * Sg + (1 + CΔ)) * ν) * a) ≤
      K * (CΔ * Sg + (1 + CΔ) + (1 + CΔ) ^ 2 * Sg + (1 + CΔ)) * (E * ρ + ν * a) := by
  have hEρ : 0 ≤ E * ρ := mul_nonneg hE hρ
  have hCc : 1 ≤ CΔ * Sg + (1 + CΔ) + (1 + CΔ) ^ 2 * Sg + (1 + CΔ) := by linarith
  obtain ⟨c, hc⟩ : ∃ c, c = CΔ * Sg + (1 + CΔ) + (1 + CΔ) ^ 2 * Sg + (1 + CΔ) := ⟨_, rfl⟩
  rw [← hc] at hCc ⊢
  have h2 : E * ρ ≤ c * (E * ρ) := by nlinarith
  have h3 := mul_le_mul_of_nonneg_left h2 hK0
  have h4 : K * (E * ρ + (c * ν) * a) = K * (E * ρ) + K * (c * (ν * a)) := by ring
  have h5 : K * c * (E * ρ + ν * a) = K * (c * (E * ρ)) + K * (c * (ν * a)) := by ring
  rw [h4, h5]
  linarith

theorem gronwall_apply (hGr : BlockGronwall) {pk : ℕ → YoungPkg} {ν : ℕ → ℝ} {lam κ : ℂ}
    {Sg α : ℝ} {δ : ℕ → ℝ} (hS : BlockSetup pk ν lam κ Sg α δ) :
    ∃ (K2 g : ℝ) (N : ℕ), 0 < g ∧ 0 ≤ K2 ∧ ∀ n ≥ N, ∀ t ∈ Icc (0 : ℝ) (α / ν n),
      ∀ x : (pk n).X,
      (∀ j, ‖ampN (pk n) lam κ (ν n) t x j (Sg / ν n) - ampN (pk n) lam κ (ν n) t x j t‖ ≤
        K2 * ν n * (‖ampN (pk n) lam κ (ν n) t x true t‖ +
          ‖ampN (pk n) lam κ (ν n) t x false t‖ + cmpN (pk n) lam κ (ν n) t x t)) ∧
      cmpN (pk n) lam κ (ν n) t x (Sg / ν n) ≤
        K2 * (Real.exp (-g * (Sg / ν n - t)) * cmpN (pk n) lam κ (ν n) t x t +
          ν n * (‖ampN (pk n) lam κ (ν n) t x true t‖ +
          ‖ampN (pk n) lam κ (ν n) t x false t‖ + cmpN (pk n) lam κ (ν n) t x t)) := by
  obtain ⟨hpos, hlim, -, hα, hαS⟩ := hS.hyp
  obtain ⟨C, g, N, hC, hg, hret⟩ := hS.ret
  obtain ⟨CΔ, hΔ⟩ := hS.small
  have hCΔ : 0 ≤ CΔ := by
    have h1 := (hΔ 0).1.trans (hΔ 0).2
    have : 0 < ν 0 ^ 2 := pow_pos (hpos 0) 2
    by_contra h
    push_neg at h
    nlinarith
  have hSg : 0 < Sg := hα.trans hαS
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = 1 + CΔ * Sg + (1 + CΔ) + (1 + CΔ) ^ 2 * Sg := ⟨_, rfl⟩
  have hB : 0 < B := by rw [hBdef]; positivity
  obtain ⟨K, hK0, hK⟩ := hGr C g B hC hg hB
  have hev : ∀ᶠ n in atTop, ν n ≤ 1 := hlim.eventually (ge_mem_nhds one_pos)
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 hev
  refine ⟨K * (CΔ * Sg + (1 + CΔ) + (1 + CΔ) ^ 2 * Sg + (1 + CΔ)), g, max N N1, hg,
    by positivity, ?_⟩
  intro n hn t ht x
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hnN1 : N1 ≤ n := (le_max_right _ _).trans hn
  have hv : 0 < ν n := hpos n
  have hv1 : ν n ≤ 1 := hN1 n hnN1
  obtain ⟨hδ0, hδ2⟩ := hΔ n
  have ht0 : 0 ≤ t := ht.1
  have htH : t ≤ Sg / ν n :=
    ht.2.trans (div_le_div_of_nonneg_right hαS.le hv.le)
  have hL0 : 0 ≤ Sg / ν n - t := by linarith
  have hLH : Sg / ν n - t ≤ Sg / ν n := by linarith
  have hεL : δ n * (Sg / ν n - t) ≤ CΔ * Sg * ν n := by
    calc δ n * (Sg / ν n - t) ≤ (CΔ * ν n ^ 2) * (Sg / ν n) :=
          mul_le_mul hδ2 hLH hL0 (by positivity)
      _ = CΔ * Sg * ν n := by field_simp
  have hk : ν n + δ n ≤ (1 + CΔ) * ν n := by
    nlinarith [mul_nonneg (mul_nonneg hCΔ hv.le) (sub_nonneg.2 hv1)]
  have hk0 : 0 ≤ ν n + δ n := by linarith
  have hk2L : (ν n + δ n) ^ 2 * (Sg / ν n - t) ≤ (1 + CΔ) ^ 2 * Sg * ν n := by
    calc (ν n + δ n) ^ 2 * (Sg / ν n - t) ≤ ((1 + CΔ) * ν n) ^ 2 * (Sg / ν n) :=
          mul_le_mul (pow_le_pow_left₀ hk0 hk 2) hLH hL0 (by positivity)
      _ = (1 + CΔ) ^ 2 * Sg * ν n := by field_simp
  have hCS : 0 ≤ CΔ * Sg := by positivity
  have hC2 : 0 ≤ (1 + CΔ) ^ 2 * Sg := by positivity
  obtain ⟨hc1, hc2, hr1, hr2⟩ := hret n hnN t ht x
  have e : t + (Sg / ν n - t) = Sg / ν n := by ring
  have hρ : ∀ s, 0 ≤ cmpN (pk n) lam κ (ν n) t x s := fun s =>
    div_nonneg (norm_nonneg _) (norm_nonneg _)
  have hmem : Sg / ν n ∈ Icc t (t + (Sg / ν n - t)) := by
    rw [e]; exact ⟨htH, le_rfl⟩
  have key := hK (δ n) (ν n + δ n) (Sg / ν n - t) t (ampN (pk n) lam κ (ν n) t x)
    (cmpN (pk n) lam κ (ν n) t x) hδ0 hk0 hL0
    (by nlinarith [mul_nonneg hCS hv.le]) (by nlinarith) (by nlinarith [mul_nonneg hC2 hv.le])
    hρ (by rw [e]; exact hc1) (by rw [e]; exact hc2) (by rw [e]; exact hr1)
    (by rw [e]; exact hr2) (Sg / ν n) hmem
  obtain ⟨-, k2, k3⟩ := key
  have ha : 0 ≤ ‖ampN (pk n) lam κ (ν n) t x true t‖ + ‖ampN (pk n) lam κ (ν n) t x false t‖
      + cmpN (pk n) lam κ (ν n) t x t := by
    have := hρ t; positivity
  refine ⟨?_, ?_⟩
  · intro j
    refine (k2 j).trans ?_
    have : K * (δ n * (Sg / ν n - t) + (ν n + δ n) + (ν n + δ n) ^ 2 * (Sg / ν n - t)) ≤
        K * (CΔ * Sg + (1 + CΔ) + (1 + CΔ) ^ 2 * Sg + (1 + CΔ)) * ν n := by
      have : δ n * (Sg / ν n - t) + (ν n + δ n) + (ν n + δ n) ^ 2 * (Sg / ν n - t) ≤
          (CΔ * Sg + (1 + CΔ) + (1 + CΔ) ^ 2 * Sg + (1 + CΔ)) * ν n := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left this hK0]
    exact mul_le_mul_of_nonneg_right this ha
  · refine k3.trans ?_
    have hkn : (ν n + δ n) * (‖ampN (pk n) lam κ (ν n) t x true t‖ +
        ‖ampN (pk n) lam κ (ν n) t x false t‖ + cmpN (pk n) lam κ (ν n) t x t) ≤
        ((CΔ * Sg + (1 + CΔ) + (1 + CΔ) ^ 2 * Sg + (1 + CΔ)) * ν n) *
        (‖ampN (pk n) lam κ (ν n) t x true t‖ +
        ‖ampN (pk n) lam κ (ν n) t x false t‖ + cmpN (pk n) lam κ (ν n) t x t) := by
      apply mul_le_mul_of_nonneg_right _ ha
      nlinarith
    have : K * (Real.exp (-g * (Sg / ν n - t)) * cmpN (pk n) lam κ (ν n) t x t +
        (ν n + δ n) * (‖ampN (pk n) lam κ (ν n) t x true t‖ +
        ‖ampN (pk n) lam κ (ν n) t x false t‖ + cmpN (pk n) lam κ (ν n) t x t)) ≤
        K * (Real.exp (-g * (Sg / ν n - t)) * cmpN (pk n) lam κ (ν n) t x t +
        ((CΔ * Sg + (1 + CΔ) + (1 + CΔ) ^ 2 * Sg + (1 + CΔ)) * ν n) *
        (‖ampN (pk n) lam κ (ν n) t x true t‖ +
        ‖ampN (pk n) lam κ (ν n) t x false t‖ + cmpN (pk n) lam κ (ν n) t x t)) := by
      apply mul_le_mul_of_nonneg_left _ hK0
      linarith
    refine this.trans ?_
    exact tail_ineq hK0 hSg.le hCS hC2 hCΔ (Real.exp_pos _).le (hρ t) ha trivial

end ConcreteYF

end UnforcedLeray.Short.PartIIIb
