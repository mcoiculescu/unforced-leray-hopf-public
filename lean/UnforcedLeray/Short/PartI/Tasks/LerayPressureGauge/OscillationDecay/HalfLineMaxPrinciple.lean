import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Exponential

/-!
# Half-line maximum principle for `D'' ≥ λ² D`

Helper for the oscillation-decay task `PartI:T02/2` (`OscillationDecay`, source line 447 of
`the November 2 reference manuscript`). This is the one-dimensional comparison
step of the `L²`-in-`q` route: if `D` is bounded above on `[R, ∞)`, `D'' ≥ λ² D` there, and
`D R ≤ 0`, then `D ≤ 0` on `[R, ∞)`.

Proof. `ψ = D' + λ D` satisfies `ψ' ≥ λ ψ`, so `e^{-λη} ψ` is nondecreasing on `[R, ∞)`.
If `ψ(η₁) > 0` for some `η₁ ≥ R`, then `ψ(η) ≥ a e^{λη}` with `a > 0`, hence
`D' ≥ a e^{λη} - λ M`, so `D η - (a/λ) e^{λη} + λ M η` is nondecreasing and `D` is unbounded:
a contradiction. Therefore `ψ ≤ 0`, so `η ↦ e^{λη} D(η)` is nonincreasing and
`D η ≤ e^{λ(R - η)} D R ≤ 0`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartI.LerayPressureGauge

/-- **Half-line maximum principle.** -/
theorem halfLine_nonpos {lam R M : ℝ} (hlam : 0 < lam) {D D1 D2 : ℝ → ℝ}
    (hD : ∀ η, HasDerivAt D (D1 η) η) (hD1 : ∀ η, HasDerivAt D1 (D2 η) η)
    (hsub : ∀ η, R ≤ η → lam ^ 2 * D η ≤ D2 η)
    (hbd : ∀ η, R ≤ η → D η ≤ M) (hR : D R ≤ 0) :
    ∀ η, R ≤ η → D η ≤ 0 := by
  have hlam0 : lam ≠ 0 := hlam.ne'
  -- Step 1: `e^{-λη} (D' + λD)` is nondecreasing on `[R, ∞)`.
  have hφ : ∀ x, HasDerivAt (fun y => Real.exp (-lam * y) * (D1 y + lam * D y))
      (Real.exp (-lam * x) * (-lam) * (D1 x + lam * D x)
        + Real.exp (-lam * x) * (D2 x + lam * D1 x)) x := by
    intro x
    have hE : HasDerivAt (fun y => Real.exp (-lam * y)) (Real.exp (-lam * x) * (-lam)) x := by
      simpa using ((hasDerivAt_id' x).const_mul (-lam)).exp
    exact hE.mul ((hD1 x).add ((hD x).const_mul lam))
  have hφmono : MonotoneOn (fun y => Real.exp (-lam * y) * (D1 y + lam * D y)) (Ici R) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici R)
    · exact fun x _ => (hφ x).continuousAt.continuousWithinAt
    · exact fun x _ => (hφ x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hRx : R ≤ x := le_of_lt (Set.mem_Ioi.mp hx)
      rw [(hφ x).deriv]
      have hk : 0 ≤ D2 x - lam ^ 2 * D x := by linarith [hsub x hRx]
      have he := Real.exp_pos (-lam * x)
      have hid : Real.exp (-lam * x) * (-lam) * (D1 x + lam * D x)
          + Real.exp (-lam * x) * (D2 x + lam * D1 x)
          = Real.exp (-lam * x) * (D2 x - lam ^ 2 * D x) := by ring
      rw [hid]
      exact mul_nonneg he.le hk
  -- Step 2: `D' + λD ≤ 0` on `[R, ∞)`.
  have hψnp : ∀ η1, R ≤ η1 → D1 η1 + lam * D η1 ≤ 0 := by
    intro η1 hη1
    by_contra hpos
    push_neg at hpos
    obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = Real.exp (-lam * η1) * (D1 η1 + lam * D η1) :=
      ⟨_, rfl⟩
    have ha : 0 < a := by rw [ha_def]; exact mul_pos (Real.exp_pos _) hpos
    -- `ψ(η) ≥ a e^{λη}` for `η ≥ η1`.
    have hgrow : ∀ η, η1 ≤ η → a * Real.exp (lam * η) ≤ D1 η + lam * D η := by
      intro η hη
      have hmono : Real.exp (-lam * η1) * (D1 η1 + lam * D η1)
          ≤ Real.exp (-lam * η) * (D1 η + lam * D η) :=
        hφmono (Set.mem_Ici.mpr hη1) (Set.mem_Ici.mpr (le_trans hη1 hη)) hη
      have ha_le : a ≤ Real.exp (-lam * η) * (D1 η + lam * D η) := by
        rw [ha_def]; exact hmono
      have hexp : Real.exp (lam * η) * Real.exp (-lam * η) = 1 := by
        rw [← Real.exp_add, show lam * η + -lam * η = 0 by ring, Real.exp_zero]
      have hψeq : D1 η + lam * D η
          = Real.exp (lam * η) * (Real.exp (-lam * η) * (D1 η + lam * D η)) := by
        rw [← mul_assoc, hexp, one_mul]
      rw [hψeq, mul_comm a]
      exact mul_le_mul_of_nonneg_left ha_le (Real.exp_pos _).le
    -- `D' ≥ a e^{λη} - λ M` for `η ≥ η1`.
    have hD1lb : ∀ η, η1 ≤ η → a * Real.exp (lam * η) - lam * M ≤ D1 η := by
      intro η hη
      have h1 := hgrow η hη
      have h2 := hbd η (le_trans hη1 hη)
      have h3 := mul_le_mul_of_nonneg_left h2 hlam.le
      linarith
    -- `H η = D η - (a/λ) e^{λη} + λ M η` is nondecreasing on `[η1, ∞)`.
    have hH : ∀ y, HasDerivAt (fun y => D y - a / lam * Real.exp (lam * y) + lam * M * y)
        (D1 y - a / lam * (Real.exp (lam * y) * lam) + lam * M * 1) y := by
      intro y
      have hE : HasDerivAt (fun y => Real.exp (lam * y)) (Real.exp (lam * y) * lam) y := by
        simpa using ((hasDerivAt_id' y).const_mul lam).exp
      exact ((hD y).sub (hE.const_mul (a / lam))).add ((hasDerivAt_id' y).const_mul (lam * M))
    have hHmono : MonotoneOn (fun y => D y - a / lam * Real.exp (lam * y) + lam * M * y)
        (Ici η1) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici η1)
      · exact fun x _ => (hH x).continuousAt.continuousWithinAt
      · exact fun x _ => (hH x).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Ici] at hx
        have hx1 : η1 ≤ x := le_of_lt (Set.mem_Ioi.mp hx)
        rw [(hH x).deriv]
        have h1 := hD1lb x hx1
        have h2 : a / lam * (Real.exp (lam * x) * lam) = a * Real.exp (lam * x) := by
          field_simp
        rw [h2]
        linarith
    -- Lower bound `D t ≥ K + (a/λ) e^{λt} - λ M t` for `t ≥ η1`.
    obtain ⟨K, hK⟩ : ∃ K : ℝ, K = D η1 - a / lam * Real.exp (lam * η1) + lam * M * η1 :=
      ⟨_, rfl⟩
    have hDlb : ∀ t, η1 ≤ t → K + a / lam * Real.exp (lam * t) - lam * M * t ≤ D t := by
      intro t ht
      have h : D η1 - a / lam * Real.exp (lam * η1) + lam * M * η1
          ≤ D t - a / lam * Real.exp (lam * t) + lam * M * t :=
        hHmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
      rw [hK]
      linarith
    -- Quadratic lower bound on the exponential.
    have hq : ∀ t, 0 ≤ t → a * lam * t ^ 2 / 2 ≤ a / lam * Real.exp (lam * t) := by
      intro t ht
      have h1 := Real.quadratic_le_exp_of_nonneg (show 0 ≤ lam * t from mul_nonneg hlam.le ht)
      have h2 : a * lam * t ^ 2 / 2 = a / lam * ((lam * t) ^ 2 / 2) := by
        field_simp
      rw [h2]
      apply mul_le_mul_of_nonneg_left _ (div_nonneg ha.le hlam.le)
      nlinarith [mul_nonneg hlam.le ht]
    -- Choose a point `t ≥ η1` where `D t` exceeds `M`: contradiction.
    obtain ⟨P, hP⟩ : ∃ P : ℝ, P = |lam * M| + |K - M| + 1 := ⟨_, rfl⟩
    obtain ⟨S, hS⟩ : ∃ S : ℝ, S = 2 * P / (a * lam) := ⟨_, rfl⟩
    have hS0 : 0 ≤ S := by
      rw [hS, hP]; positivity
    have haS : a * lam * S = 2 * P := by
      rw [hS]; field_simp
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = |η1| + S + 1 := ⟨_, rfl⟩
    have ht1 : η1 ≤ t := by rw [ht]; linarith [le_abs_self η1]
    have ht2 : 1 ≤ t := by rw [ht]; linarith [abs_nonneg η1]
    have htS : S ≤ t := by rw [ht]; linarith [abs_nonneg η1]
    have ht0 : 0 ≤ t := by linarith
    have hsq : t * P ≤ a * lam * t ^ 2 / 2 := by
      have h1 : t * S ≤ t * t := mul_le_mul_of_nonneg_left htS ht0
      have h2 : a * lam * (t * S) ≤ a * lam * (t * t) :=
        mul_le_mul_of_nonneg_left h1 (mul_pos ha hlam).le
      have h3 : a * lam * (t * S) = t * (2 * P) := by rw [← haS]; ring
      nlinarith
    have hfin : K + t * P - lam * M * t ≤ D t := by
      have := hq t ht0
      have := hDlb t ht1
      linarith
    have hPt : K + t * (|K - M| + 1) ≤ D t := by
      have hnn : 0 ≤ t * (|lam * M| - lam * M) :=
        mul_nonneg ht0 (sub_nonneg.mpr (le_abs_self _))
      rw [hP] at hfin
      nlinarith
    have hbt : D t ≤ M := hbd t (le_trans hη1 ht1)
    have hKM : M - K ≤ |K - M| := by
      rw [abs_sub_comm]; exact le_abs_self _
    have hstep : K + (|K - M| + 1) ≤ K + t * (|K - M| + 1) := by
      have := mul_nonneg (sub_nonneg.mpr ht2) (by positivity : (0 : ℝ) ≤ |K - M| + 1)
      nlinarith
    linarith
  -- Step 3: `e^{λη} D` is nonincreasing on `[R, ∞)`, so `D ≤ 0`.
  have hΨ : ∀ x, HasDerivAt (fun y => Real.exp (lam * y) * D y)
      (Real.exp (lam * x) * (D1 x + lam * D x)) x := by
    intro x
    have hE : HasDerivAt (fun y => Real.exp (lam * y)) (Real.exp (lam * x) * lam) x := by
      simpa using ((hasDerivAt_id' x).const_mul lam).exp
    have h := hE.mul (hD x)
    have hval : Real.exp (lam * x) * lam * D x + Real.exp (lam * x) * D1 x
        = Real.exp (lam * x) * (D1 x + lam * D x) := by ring
    rw [hval] at h
    exact h
  have hanti : AntitoneOn (fun y => Real.exp (lam * y) * D y) (Ici R) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici R)
    · exact fun x _ => (hΨ x).continuousAt.continuousWithinAt
    · exact fun x _ => (hΨ x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx1 : R ≤ x := le_of_lt (Set.mem_Ioi.mp hx)
      rw [(hΨ x).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
        (by linarith [hψnp x hx1])
  intro η hη
  have h1 : Real.exp (lam * η) * D η ≤ Real.exp (lam * R) * D R :=
    hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hη) hη
  have h2 : Real.exp (lam * R) * D R ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hR
  by_contra h
  push_neg at h
  have := mul_pos (Real.exp_pos (lam * η)) h
  linarith

end UnforcedLeray.Short.PartI.LerayPressureGauge
