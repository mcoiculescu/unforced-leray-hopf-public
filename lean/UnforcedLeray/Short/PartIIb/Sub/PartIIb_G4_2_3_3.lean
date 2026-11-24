import UnforcedLeray.Short.PartIIb.Sub.G4_2_3

/-!


Source: `the November 2 reference manuscript` lines 2349-2358.
Periodizing a smooth `G` whose iterated derivatives are bounded by `C_j e^{-κ_j |x|²}`:
three analytic leaves (uniform lattice Gaussian sum; Gaussian-in-`x₂` comparison with
`e^{-κ|x₂|/c}`; termwise differentiation of the `ℤ`-indexed series) and the assembly
`perGaussian_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- **Leaf `G4/2/3/3/1`** (SP 2349-2358): uniform lattice Gaussian sum. For `κ > 0` there is `S`
with `Σ_{k∈ℤ} e^{-κ(x₁+kc)²} ≤ S` for all `c ≥ 1`, `x₁ ∈ ℝ`, and the series is summable.
(For each `k` with `|x₁+kc| ≥ 1` compare with the nearest-lattice index; or compare with
`Σ_k e^{-κ (k-k₀)²/…}` using `|(k-k₀)c| ≥ |k-k₀|` and `|x₁+kc| ≥ |k-k₀|c - |x₁+k₀c|`.) -/
def LatticeGaussSum : Prop :=
  ∀ κ : ℝ, 0 < κ → ∃ S : ℝ, ∀ c : ℝ, 1 ≤ c → ∀ x₁ : ℝ,
    Summable (fun k : ℤ => Real.exp (-(κ * (x₁ + k * c) ^ 2))) ∧
      ∑' k : ℤ, Real.exp (-(κ * (x₁ + k * c) ^ 2)) ≤ S

/-- **Leaf `G4/2/3/3/2`** (SP 2349-2358): `e^{-κ x₂²} ≤ K e^{-κ|x₂|/c}` for `c ≥ 1`, with
`K = e^{κ/4}`: pointwise `x₂² - |x₂|/c ≥ x₂² - |x₂| ≥ -1/4`. -/
def GaussStripLe : Prop :=
  ∀ κ : ℝ, 0 < κ → ∃ K : ℝ, ∀ c : ℝ, 1 ≤ c → ∀ x₂ : ℝ,
    Real.exp (-(κ * x₂ ^ 2)) ≤ K * Real.exp (-(κ * |x₂| / c))

/-- **Leaf `G4/2/3/3/3`** (SP 2349-2358): termwise differentiation. If `G` is smooth with
`‖D^j G(x)‖ ≤ C_j e^{-κ_j|x|²}` for all `j`, then for each `c ≥ 1` the periodization `perC c G`
is `C^∞`, and its `j`-th iterated derivative at `x` is bounded by `Σ_k ‖D^j G(x₁+kc, x₂)‖`
(a summable series). Use `contDiff_tsum`-type results on the pieces
`x ↦ G(x₁ + kc, x₂)` (`iteratedFDeriv_comp_add_right`), after localizing in `x₁` (the bound
`e^{-κ(x₁+kc)²}` is uniform for `x₁` in a bounded interval and summable in `k`). -/
def PerDerivTsum : Prop :=
  ∀ G : ℝ × ℝ → ℂ, ContDiff ℝ ∞ G →
    (∀ j : ℕ, ∃ (C κ : ℝ), 0 < κ ∧ ∀ x : ℝ × ℝ,
      ‖iteratedFDeriv ℝ j G x‖ ≤ C * Real.exp (-(κ * (x.1 ^ 2 + x.2 ^ 2)))) →
    ∀ c : ℝ, 1 ≤ c → ContDiff ℝ ∞ (perC c G) ∧
      ∀ (j : ℕ) (x : ℝ × ℝ),
        Summable (fun k : ℤ => ‖iteratedFDeriv ℝ j G (x.1 + k * c, x.2)‖) ∧
        ‖iteratedFDeriv ℝ j (perC c G) x‖ ≤ ∑' k : ℤ, ‖iteratedFDeriv ℝ j G (x.1 + k * c, x.2)‖

theorem perGaussian_of (h1 : LatticeGaussSum) (h2 : GaussStripLe) (h3 : PerDerivTsum) :
    PerGaussian := by
  intro G hG hbd j
  obtain ⟨C, κ, hκ, hCj⟩ := hbd j
  obtain ⟨S, hS⟩ := h1 κ hκ
  obtain ⟨K, hK⟩ := h2 κ hκ
  have hC : 0 ≤ C := by
    have h0 := hCj 0
    have hn : 0 ≤ ‖iteratedFDeriv ℝ j G 0‖ := norm_nonneg _
    have hp : 0 < Real.exp (-(κ * ((0 : ℝ × ℝ).1 ^ 2 + (0 : ℝ × ℝ).2 ^ 2))) := Real.exp_pos _
    by_contra hneg
    push_neg at hneg
    nlinarith [mul_neg_of_neg_of_pos hneg hp]
  refine ⟨max (C * S * K) 1, κ, 0, lt_of_lt_of_le one_pos (le_max_right _ _), hκ, fun c hc => ?_⟩
  obtain ⟨hsm, hder⟩ := h3 G hG hbd c hc
  refine ⟨fun x => ?_, hsm, fun x => ?_⟩
  · have := (hder 0 x).1
    refine Summable.of_norm ?_
    simpa using this
  · obtain ⟨hsum, hle⟩ := hder j x
    have hsumE : Summable (fun k : ℤ => C * Real.exp (-(κ * (x.2 ^ 2))) *
        Real.exp (-(κ * (x.1 + k * c) ^ 2))) :=
      ((hS c hc x.1).1).mul_left _
    have hpt : ∀ k : ℤ, ‖iteratedFDeriv ℝ j G (x.1 + k * c, x.2)‖ ≤
        C * Real.exp (-(κ * (x.2 ^ 2))) * Real.exp (-(κ * (x.1 + k * c) ^ 2)) := by
      intro k
      refine (hCj _).trans (le_of_eq ?_)
      simp only
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    have h1' : ∑' k : ℤ, ‖iteratedFDeriv ℝ j G (x.1 + k * c, x.2)‖ ≤
        C * Real.exp (-(κ * (x.2 ^ 2))) * S := by
      calc _ ≤ ∑' k : ℤ, C * Real.exp (-(κ * (x.2 ^ 2))) *
              Real.exp (-(κ * (x.1 + k * c) ^ 2)) := hsum.tsum_le_tsum hpt hsumE
        _ = C * Real.exp (-(κ * (x.2 ^ 2))) * ∑' k : ℤ, Real.exp (-(κ * (x.1 + k * c) ^ 2)) :=
            tsum_mul_left
        _ ≤ C * Real.exp (-(κ * (x.2 ^ 2))) * S :=
            mul_le_mul_of_nonneg_left (hS c hc x.1).2 (by positivity)
    calc ‖iteratedFDeriv ℝ j (perC c G) x‖ ≤ _ := hle
      _ ≤ C * Real.exp (-(κ * (x.2 ^ 2))) * S := h1'
      _ = C * S * Real.exp (-(κ * (x.2 ^ 2))) := by ring
      _ ≤ C * S * (K * Real.exp (-(κ * |x.2| / c))) :=
          mul_le_mul_of_nonneg_left (hK c hc x.2)
            (mul_nonneg hC (by
              by_contra hneg
              push_neg at hneg
              have := (hS c hc 0).2
              have hn : 0 ≤ ∑' k : ℤ, Real.exp (-(κ * ((0 : ℝ) + k * c) ^ 2)) :=
                tsum_nonneg fun k => (Real.exp_pos _).le
              linarith))
      _ = C * S * K * Real.exp (-(κ * |x.2| / c)) := by ring
      _ ≤ max (C * S * K) 1 * (c ^ 0) * Real.exp (-(κ * |x.2| / c)) := by
          rw [pow_zero, mul_one]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le

end UnforcedLeray.Short.IIb
