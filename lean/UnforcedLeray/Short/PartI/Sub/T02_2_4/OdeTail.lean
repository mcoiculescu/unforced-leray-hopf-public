import UnforcedLeray.Short.PartI.Tasks.LerayPressureGauge.OscillationDecay.HalfLineMaxPrinciple

/-!
# One-dimensional comparison for the slice energy (helper of `PartI:T02/2/4`)

If `m ≥ 0` is a bounded `C²` function with `m'' ≥ λ² m - g` where `g → 0` at `±∞`, then
`m → 0` at `±∞`.  Proof: on `[R, ∞)` with `g ≤ γ`, the function
`D = m - A - B e^{-λ(η-R)}`, `A = γ/λ⁴`, `B = max (m R - A) 0`, satisfies `D'' ≥ λ² D`, is bounded
above and `D R ≤ 0`, so `D ≤ 0` by `halfLine_nonpos`; the left half-line follows by reflection.
-/

set_option autoImplicit false

noncomputable section

open Set Filter

namespace UnforcedLeray.Short.PartI.OscDecay

open UnforcedLeray.Short.PartI.LerayPressureGauge

theorem hasDerivAt_expNeg (lam R η : ℝ) :
    HasDerivAt (fun x => Real.exp (-lam * (x - R))) (-lam * Real.exp (-lam * (η - R))) η := by
  have h := (((hasDerivAt_id' η).sub_const R).const_mul (-lam)).exp
  convert h using 1
  ring

/-- Tail bound on a right half-line. -/
theorem tail_bound {lam A Mb R : ℝ} (hlam : 0 < lam) (hA : 0 ≤ A) {m m1 m2 : ℝ → ℝ}
    (hm : ∀ η, HasDerivAt m (m1 η) η) (hm1 : ∀ η, HasDerivAt m1 (m2 η) η)
    (hb : ∀ η, m η ≤ Mb)
    (hsub : ∀ η, R ≤ η → lam ^ 2 * (m η - A) ≤ m2 η) :
    ∀ η, R ≤ η → m η ≤ A + max (m R - A) 0 * Real.exp (-lam * (η - R)) := by
  set B := max (m R - A) 0 with hB
  have hB0 : 0 ≤ B := le_max_right _ _
  have hD : ∀ η, HasDerivAt (fun x => m x - A - B * Real.exp (-lam * (x - R)))
      (m1 η - B * (-lam * Real.exp (-lam * (η - R)))) η := by
    intro η
    exact ((hm η).sub_const A).sub ((hasDerivAt_expNeg lam R η).const_mul B)
  have hD1 : ∀ η, HasDerivAt (fun x => m1 x - B * (-lam * Real.exp (-lam * (x - R))))
      (m2 η - B * (-lam * (-lam * Real.exp (-lam * (η - R))))) η := by
    intro η
    exact (hm1 η).sub (((hasDerivAt_expNeg lam R η).const_mul (-lam)).const_mul B)
  have hsub' : ∀ η, R ≤ η → lam ^ 2 * (m η - A - B * Real.exp (-lam * (η - R))) ≤
      m2 η - B * (-lam * (-lam * Real.exp (-lam * (η - R)))) := by
    intro η hη
    have := hsub η hη
    nlinarith
  have hbd : ∀ η, R ≤ η → m η - A - B * Real.exp (-lam * (η - R)) ≤ Mb := by
    intro η _
    have := mul_nonneg hB0 (Real.exp_pos (-lam * (η - R))).le
    linarith [hb η]
  have hR : m R - A - B * Real.exp (-lam * (R - R)) ≤ 0 := by
    simp only [sub_self, mul_zero, Real.exp_zero, mul_one]
    have : m R - A ≤ B := le_max_left _ _
    linarith
  have key := halfLine_nonpos (lam := lam) (R := R) (M := Mb) hlam hD hD1 hsub' hbd hR
  intro η hη
  have := key η hη
  linarith

/-- Reflection `η ↦ -η` preserves the differential structure. -/
theorem reflect {m m1 m2 : ℝ → ℝ} (hm : ∀ η, HasDerivAt m (m1 η) η)
    (hm1 : ∀ η, HasDerivAt m1 (m2 η) η) :
    (∀ η, HasDerivAt (fun x => m (-x)) (-m1 (-η)) η) ∧
      (∀ η, HasDerivAt (fun x => -m1 (-x)) (m2 (-η)) η) := by
  constructor
  · intro η
    have h := (hm (-η)).comp η (hasDerivAt_neg η)
    exact h.congr_deriv (by ring)
  · intro η
    have h := ((hm1 (-η)).comp η (hasDerivAt_neg η)).neg
    exact h.congr_deriv (by ring)

/-- Eventual smallness on a right half-line: `m ≤ 2A` for large `η`. -/
theorem right_decay {lam A Mb R : ℝ} (hlam : 0 < lam) (hA : 0 < A) {m m1 m2 : ℝ → ℝ}
    (hm : ∀ η, HasDerivAt m (m1 η) η) (hm1 : ∀ η, HasDerivAt m1 (m2 η) η)
    (hb : ∀ η, m η ≤ Mb)
    (hsub : ∀ η, R ≤ η → lam ^ 2 * (m η - A) ≤ m2 η) :
    ∃ R' : ℝ, ∀ η, R' ≤ η → m η ≤ 2 * A := by
  have htail := tail_bound hlam hA.le hm hm1 hb hsub
  set B := max (m R - A) 0 with hB
  have hB0 : 0 ≤ B := le_max_right _ _
  have hlim : Tendsto (fun x : ℝ => B * Real.exp (-lam * (x - R))) atTop (nhds 0) := by
    have h1 : Tendsto (fun x : ℝ => -lam * (x - R)) atTop atBot := by
      apply Tendsto.const_mul_atTop_of_neg (by linarith)
      exact tendsto_atTop_add_const_right _ _ tendsto_id
    have h2 := Real.tendsto_exp_atBot.comp h1
    simpa using h2.const_mul B
  have hev : ∀ᶠ x : ℝ in atTop, B * Real.exp (-lam * (x - R)) < A :=
    (hlim.eventually (gt_mem_nhds hA))
  obtain ⟨R', hR'⟩ := eventually_atTop.1 hev
  refine ⟨max R' R, fun η hη => ?_⟩
  have h1 := htail η (le_trans (le_max_right _ _) hη)
  have h2 := hR' η (le_trans (le_max_left _ _) hη)
  linarith

/-- Decay of a bounded above `C²` function with `m'' ≥ λ² m - g`, `g → 0` at `±∞`:
explicit `ε`-`R` form. -/
theorem decay_of_ode {lam Mb : ℝ} (hlam : 0 < lam) {m m1 m2 g : ℝ → ℝ}
    (hm : ∀ η, HasDerivAt m (m1 η) η) (hm1 : ∀ η, HasDerivAt m1 (m2 η) η)
    (hb : ∀ η, m η ≤ Mb)
    (hineq : ∀ η, lam ^ 2 * m η - g η / lam ^ 2 ≤ m2 η)
    (hg : ∀ γ : ℝ, 0 < γ → ∃ R : ℝ, ∀ η, R ≤ |η| → g η ≤ γ) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ η, R ≤ |η| → m η < ε := by
  intro ε hε
  obtain ⟨hr1, hr2⟩ := reflect hm hm1
  set γ : ℝ := lam ^ 4 * ε / 4 with hγ
  have hγpos : 0 < γ := by positivity
  set A : ℝ := γ / lam ^ 4 with hA
  have hApos : 0 < A := by positivity
  have hA2 : 2 * A < ε := by
    have : A = ε / 4 := by rw [hA, hγ]; field_simp
    rw [this]; linarith
  obtain ⟨R1, hR1⟩ := hg γ hγpos
  have hsubA : ∀ η, R1 ≤ |η| → lam ^ 2 * (m η - A) ≤ m2 η := by
    intro η hη
    have h1 := hineq η
    have h2 : g η / lam ^ 2 ≤ γ / lam ^ 2 := by
      apply div_le_div_of_nonneg_right (hR1 η hη) (by positivity)
    have h3 : γ / lam ^ 2 = lam ^ 2 * A := by rw [hA]; field_simp
    nlinarith
  obtain ⟨Rp, hRp⟩ := right_decay (R := max R1 0) hlam hApos hm hm1 hb
    (fun η hη => hsubA η (by
      rw [abs_of_nonneg (le_trans (le_max_right _ _) hη)]
      exact le_trans (le_max_left _ _) hη))
  obtain ⟨Rn, hRn⟩ := right_decay (R := max R1 0) (m := fun x => m (-x)) hlam hApos hr1 hr2
    (fun η => hb _)
    (fun η hη => by
      have := hsubA (-η) (by
        rw [abs_neg, abs_of_nonneg (le_trans (le_max_right _ _) hη)]
        exact le_trans (le_max_left _ _) hη)
      simpa using this)
  refine ⟨max Rp Rn, fun η hη => ?_⟩
  rcases le_total 0 η with h0 | h0
  · rw [abs_of_nonneg h0] at hη
    have := hRp η (le_trans (le_max_left _ _) hη)
    linarith
  · rw [abs_of_nonpos h0] at hη
    have := hRn (-η) (le_trans (le_max_right _ _) hη)
    simp only [neg_neg] at this
    linarith

end UnforcedLeray.Short.PartI.OscDecay
