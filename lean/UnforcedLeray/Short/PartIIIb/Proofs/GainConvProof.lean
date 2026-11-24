import UnforcedLeray.Short.PartIIIb.Tasks
import UnforcedLeray.Short.PartIIIb.Proofs.PolyExp
import UnforcedLeray.Short.PartIIIb.Proofs.AstarExact

/-!
# Proof of `T_gain` (target `gainConvProof`)

Source: `the November 2 reference manuscript`, lines 5960-5972.

Assume `ScalarGainLimit` (uniform convergence of the signed unit response `unitResp` to
`e^{-z}` on `[-1,1]`) and `FlatLimit` (lines 4821-4845, the bound
`|Λ(a_μ) - unitResp| ≤ C A_* ν⁻¹^k e^{-b/ν}` for `n ≥ N`, `z ∈ [-1,1]`).

* `A_* = Astar = e^{-z}/(2‖𝒞(σ₀)‖)` by `astarExact` (for `0 < ν < 1`), so
  `0 ≤ A_* ≤ e/(2‖𝒞(σ₀)‖)` on `[-1,1]`.
* `ν⁻¹^k e^{-b/ν} → 0` by `polyExp`, hence the flat error is uniformly small.
* Triangle inequality: `dist(e^{-z}, Λ(a_μ)) ≤ dist(e^{-z}, unitResp) + |Λ(a_μ) - unitResp|`,
  each summand `< ε/2` for all large `n`, uniformly in `z`.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set

namespace UnforcedLeray.Short.PartIIIb

/-- Absolute-value bound: `x ≤ C a p q` with `0 ≤ a ≤ A`, `0 ≤ p`, `0 ≤ q` gives
`x ≤ |C| A p q`. -/
theorem gain_abs_bound (x C a A p q : ℝ) (hx : x ≤ C * a * p * q) (ha0 : 0 ≤ a) (haA : a ≤ A)
    (hp : 0 ≤ p) (hq : 0 ≤ q) : x ≤ |C| * A * p * q := by
  have hpq : 0 ≤ a * p * q := mul_nonneg (mul_nonneg ha0 hp) hq
  have h1 : C * a * p * q ≤ |C| * a * p * q := by
    have h := mul_le_mul_of_nonneg_right (le_abs_self C) hpq
    calc C * a * p * q = C * (a * p * q) := by ring
      _ ≤ |C| * (a * p * q) := h
      _ = |C| * a * p * q := by ring
  have h2 : |C| * a * p * q ≤ |C| * A * p * q := by
    have h := mul_le_mul_of_nonneg_left haA (abs_nonneg C)
    have hpq' : 0 ≤ p * q := mul_nonneg hp hq
    calc |C| * a * p * q = (|C| * a) * (p * q) := by ring
      _ ≤ (|C| * A) * (p * q) := mul_le_mul_of_nonneg_right h hpq'
      _ = |C| * A * p * q := by ring
  linarith

theorem gainConvProof : UnforcedLeray.Short.PartIIIb.T_gain := by
  unfold T_gain
  intro hScalar S lam κ ell J σ₀ a_s hlam hlamim hell hJc hσ hCne hν0 hνlim hphase hFL
  unfold ScalarGainLimit at hScalar
  unfold FlatLimit at hFL
  obtain ⟨ωcan, C, k, γ', bb, N, -, -, -, hbb, hN⟩ := hFL
  have hU := Metric.tendstoUniformlyOn_iff.1
    (hScalar lam κ ell J σ₀ hlam hlamim hell hJc hσ hCne S.ν hν0 hνlim hphase)
  -- polynomial times exponential decay in `ν⁻¹`
  have hPE := UnforcedLeray.Short.PartIIIb.polyExp
  unfold T_polyExp at hPE
  have hg : Tendsto (fun n => (S.ν n)⁻¹ ^ k * Real.exp (-bb / S.ν n)) atTop (𝓝 0) :=
    (hPE k bb S.ν hbb hν0 hνlim).1
  have hnorm : 0 < 2 * ‖mellinC lam ell J (σ₀ : ℂ)‖ :=
    mul_pos two_pos (norm_pos_iff.2 hCne)
  have hν1 : ∀ᶠ n : ℕ in atTop, S.ν n < 1 :=
    hνlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hASTAR := UnforcedLeray.Short.PartIIIb.astarExact
  unfold T_astarExact at hASTAR
  unfold GainConv
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hT : Tendsto (fun n => |C| * (Real.exp 1 / (2 * ‖mellinC lam ell J (σ₀ : ℂ)‖)) *
      ((S.ν n)⁻¹ ^ k * Real.exp (-bb / S.ν n))) atTop (𝓝 0) := by
    have h := hg.const_mul (|C| * (Real.exp 1 / (2 * ‖mellinC lam ell J (σ₀ : ℂ)‖)))
    rw [mul_zero] at h
    exact h
  have hsmall : ∀ᶠ n : ℕ in atTop, |C| * (Real.exp 1 / (2 * ‖mellinC lam ell J (σ₀ : ℂ)‖)) *
      ((S.ν n)⁻¹ ^ k * Real.exp (-bb / S.ν n)) < ε / 2 :=
    hT.eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [hU (ε / 2) (half_pos hε), hsmall, eventually_ge_atTop N, hν1]
    with n hUn hsn hnN hν1n
  intro z hz
  show dist (Real.exp (-z)) ((S.ops n z).Lam (S.ops n z).aMu) < ε
  have hUz : dist (Real.exp (-z)) (unitResp lam κ (mellinC lam ell J)
      (epsCube lam.re κ σ₀ (mellinC lam ell J (σ₀ : ℂ)) (S.ν n)) (S.ν n)
      (muWin σ₀ (S.ν n) z)) < ε / 2 := hUn z hz
  have hD := (hN n hnN z hz).2.2.2
  have hAid : Astar lam κ (mellinC lam ell J (σ₀ : ℂ)) σ₀ (S.ν n) z =
      Real.exp (-z) / (2 * ‖mellinC lam ell J (σ₀ : ℂ)‖) :=
    hASTAR lam κ (mellinC lam ell J (σ₀ : ℂ)) σ₀ (S.ν n) z hCne (hν0 n) hν1n
  have hA0 : 0 ≤ Astar lam κ (mellinC lam ell J (σ₀ : ℂ)) σ₀ (S.ν n) z := by
    rw [hAid]
    positivity
  have hA1 : Astar lam κ (mellinC lam ell J (σ₀ : ℂ)) σ₀ (S.ν n) z ≤
      Real.exp 1 / (2 * ‖mellinC lam ell J (σ₀ : ℂ)‖) := by
    rw [hAid]
    exact div_le_div_of_nonneg_right (Real.exp_le_exp.2 (by linarith [hz.1])) hnorm.le
  have hbound := gain_abs_bound _ _ _ _ _ _ hD hA0 hA1
    (pow_nonneg (inv_nonneg.2 (hν0 n).le) k) (Real.exp_pos _).le
  have htri := dist_triangle (Real.exp (-z))
    (unitResp lam κ (mellinC lam ell J)
      (epsCube lam.re κ σ₀ (mellinC lam ell J (σ₀ : ℂ)) (S.ν n)) (S.ν n)
      (muWin σ₀ (S.ν n) z))
    ((S.ops n z).Lam (S.ops n z).aMu)
  have hdUL : dist (unitResp lam κ (mellinC lam ell J)
      (epsCube lam.re κ σ₀ (mellinC lam ell J (σ₀ : ℂ)) (S.ν n)) (S.ν n)
      (muWin σ₀ (S.ν n) z)) ((S.ops n z).Lam (S.ops n z).aMu) =
      |(S.ops n z).Lam (S.ops n z).aMu - unitResp lam κ (mellinC lam ell J)
        (epsCube lam.re κ σ₀ (mellinC lam ell J (σ₀ : ℂ)) (S.ν n)) (S.ν n)
        (muWin σ₀ (S.ν n) z)| := by
    rw [Real.dist_eq, abs_sub_comm]
  linarith

end UnforcedLeray.Short.PartIIIb
