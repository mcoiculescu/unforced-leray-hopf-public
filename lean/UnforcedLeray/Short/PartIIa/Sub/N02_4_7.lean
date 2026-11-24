import UnforcedLeray.Short.PartIIa.Sub.N02_4_4

/-!
# Part II-a, task `PartII-a:N02/4/7` (`nzModeBounds`): decomposition into step Props

Source of record: `the November 2 reference manuscript`, lines 1722-1727 (inverse
`q`-derivative costs `c/(2π)`; one `η`-moment costs a fixed power; all projection operations commute
with `S`).  Compiled helpers already available (Tasks/N02LerayComparison/NonzeroMode/ModeBounds/):
`nzmb_modeEq_iter` (`S^n` commutes with `NzModeEq`), `nzmb_iter_fderiv`, `nzmb_slice_energy`,
`nzmb_slice_pair0/1`, `nzmb_norm_nzS2_le`.  The assembly of `NzModeBounds` from the Props below is
the original task.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

/-- Band preservation of `S = s ∂_s`: both the `s`-band and the box support survive (outside the closed
support `g` vanishes on an open set, so `fderiv g = 0` there). -/
def NzmbBand : Prop :=
  (∀ a : ℝ × ℝ → ℂ, ContDiff ℝ ∞ a → NzBand2 a → NzBand2 (nzS2 a)) ∧
  (∀ φ : ℝ × ℝ → ℂ, ContDiff ℝ ∞ φ → (∃ s0 s1 : ℝ, 0 < s0 ∧ ∀ x : ℝ × ℝ, φ x ≠ 0 → x.1 ∈ Icc s0 s1) →
    ∃ s0 s1 : ℝ, 0 < s0 ∧ ∀ x : ℝ × ℝ, nzS2 φ x ≠ 0 → x.1 ∈ Icc s0 s1)

/-- Weighted integrability: an `s`-band supported function with exponential `η`-decay has
`(|η|^j)² ‖g‖² s^{-3/2}` integrable on `Ioi 0 × ℝ`. -/
def NzmbIntegrableWeight : Prop :=
  ∀ (g : ℝ × ℝ → ℂ), ContDiff ℝ ∞ g → ∀ (s0 s1 κ C : ℝ), 0 < s0 → 0 < κ →
    (∀ x, g x ≠ 0 → x.1 ∈ Icc s0 s1) → (∀ x, ‖g x‖ ≤ C * Real.exp (-κ * |x.2|)) → ∀ j : ℕ,
    Integrable (fun x : ℝ × ℝ => (|x.2| ^ j) ^ 2 * ‖g x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)))
      (volume.restrict (Ioi 0 ×ˢ univ))

/-- Weighted energy identity (the `j = 0` step, from `nzmb_slice_energy` for each `s`, then Fubini
`integral_prod` on `Ioi 0 × ℝ`): for smooth band-supported exponentially decaying `G1, G2`
(together with `∂_η G1, ∂_η G2`) solving `NzModeEq k A B G1 G2`,
`∫ (k²‖G1‖² + ‖∂_η G1‖² + k²‖G2‖² + ‖∂_η G2‖²) s^{-3/2} = ∫ (‖A‖² + ‖B‖²) s^{-3/2}`
over `Ioi 0 × ℝ`. -/
def NzmbWeightedEnergy : Prop :=
  ∀ (k : ℝ) (A B G1 G2 : ℝ × ℝ → ℂ), ContDiff ℝ ∞ G1 → ContDiff ℝ ∞ G2 → NzModeEq k A B G1 G2 →
    (∃ s0 s1 : ℝ, 0 < s0 ∧ ∀ x : ℝ × ℝ, (G1 x ≠ 0 ∨ G2 x ≠ 0) → x.1 ∈ Icc s0 s1) →
    (∃ κ C : ℝ, 0 < κ ∧ ∀ x : ℝ × ℝ,
      ‖G1 x‖ ≤ C * Real.exp (-κ * |x.2|) ∧ ‖fderiv ℝ G1 x (0, 1)‖ ≤ C * Real.exp (-κ * |x.2|) ∧
      ‖G2 x‖ ≤ C * Real.exp (-κ * |x.2|) ∧ ‖fderiv ℝ G2 x (0, 1)‖ ≤ C * Real.exp (-κ * |x.2|)) →
    ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ,
        (k ^ 2 * ‖G1 x‖ ^ 2 + ‖fderiv ℝ G1 x (0, 1)‖ ^ 2 + k ^ 2 * ‖G2 x‖ ^ 2 +
          ‖fderiv ℝ G2 x (0, 1)‖ ^ 2) * x.1 ^ (-(3 / 2 : ℝ)) =
      ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, (‖A x‖ ^ 2 + ‖B x‖ ^ 2) * x.1 ^ (-(3 / 2 : ℝ))

/-- Product rule in `η` and commutation of `S` with multiplication by `η`:
`∂_η(η g) = η ∂_η g + g`, `nzS2 (η g) = η nzS2 g` (since `∂_s η = 0`), and the iterate version. -/
def NzmbEtaMul : Prop :=
  ∀ g : ℝ × ℝ → ℂ, ContDiff ℝ ∞ g → ∀ x : ℝ × ℝ,
    fderiv ℝ (fun y : ℝ × ℝ => (y.2 : ℂ) * g y) x (0, 1) = (x.2 : ℂ) * fderiv ℝ g x (0, 1) + g x ∧
    nzS2 (fun y : ℝ × ℝ => (y.2 : ℂ) * g y) x = (x.2 : ℂ) * nzS2 g x ∧
    ∀ n : ℕ, (nzS2^[n]) (fun y : ℝ × ℝ => (y.2 : ℂ) * g y) x = (x.2 : ℂ) * (nzS2^[n] g) x

/-- The `j = 1` system: if `(φ, ψ)` solves `NzModeEq k a b φ ψ` then `(η φ, η ψ)` solves it with data
`(η a - ψ, η b + φ)` (algebra from the product rule). -/
def NzmbEtaModeEq : Prop :=
  ∀ (k : ℝ) (A B G1 G2 : ℝ × ℝ → ℂ), ContDiff ℝ ∞ G1 → ContDiff ℝ ∞ G2 → NzModeEq k A B G1 G2 →
    NzModeEq k (fun x => (x.2 : ℂ) * A x - G2 x) (fun x => (x.2 : ℂ) * B x + G1 x)
      (fun x => (x.2 : ℂ) * G1 x) (fun x => (x.2 : ℂ) * G2 x)

/-- Multiplying a slice by `t` keeps exponential decay (with `κ' = κ/2`), including the derivative
`(t G)' = G + t G'`. -/
def NzmbSliceEtaDecay : Prop :=
  ∀ (G : ℝ × ℝ → ℂ) (s κ C : ℝ), 0 < κ →
    (∀ t : ℝ, ‖G (s, t)‖ ≤ C * Real.exp (-κ * |t|) ∧
      ‖deriv (fun τ => G (s, τ)) t‖ ≤ C * Real.exp (-κ * |t|)) →
    ∃ κ' C' : ℝ, 0 < κ' ∧ ∀ t : ℝ, ‖t * G (s, t)‖ ≤ C' * Real.exp (-κ' * |t|) ∧
      ‖deriv (fun τ : ℝ => (τ : ℂ) * G (s, τ)) t‖ ≤ C' * Real.exp (-κ' * |t|)

end UnforcedLeray.Short.PartIIa
