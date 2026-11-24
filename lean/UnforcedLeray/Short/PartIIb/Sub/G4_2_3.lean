import UnforcedLeray.Short.PartIIb.Sub.G4_2

/-!
# Part II-b, task `PartII-b:G4/2/3` (`PeriodizeCoreCut`): decomposition

Source of record: `the November 2 reference manuscript`, lines 2349-2358.

Write `F = G + Hc`, where `Hc = (1-χ) M (x₁ - i x₂)^{-2}` is the harmonic part with the pole cut
out (smooth, equal to `M (x₁ - i x₂)^{-2}` for `|x| > ρ`) and `G = F - Hc` is smooth with Gaussian
bounds on all of `ℝ²` (inside the ball by compactness, outside by hypothesis). Periodize each
(`PerGaussian`; `PerHarmonicCut`, via `sumInvSqShift`) and add (`perBoundAt_add`).

Leaves: `CutExists`, `CoreGaussian`, `PerGaussian`, `PerHarmonicCut`.
Proved here: `perBoundAt_add`, `periodizeCoreCut_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- The `c`-periodization `x ↦ Σ_k F(x₁ + kc, x₂)`. -/
def perC (c : ℝ) (F : ℝ × ℝ → ℂ) (x : ℝ × ℝ) : ℂ := ∑' k : ℤ, F (x.1 + k * c, x.2)

/-- Summable, smooth periodization with the `C c^N e^{-κ|x₂|/c}` bound on the `j`-th derivative. -/
def PerBoundAt (j : ℕ) (F : ℝ × ℝ → ℂ) : Prop :=
  ∃ (C κ : ℝ) (N : ℕ), 0 < C ∧ 0 < κ ∧ ∀ c : ℝ, 1 ≤ c →
    (∀ x : ℝ × ℝ, Summable (fun k : ℤ => F (x.1 + k * c, x.2))) ∧
    ContDiff ℝ ∞ (perC c F) ∧
    ∀ x : ℝ × ℝ, ‖iteratedFDeriv ℝ j (perC c F) x‖ ≤ C * c ^ N * Real.exp (-(κ * |x.2| / c))

/-- **Leaf `PartII-b:G4/2/3/1`** (smooth cut harmonic part; SP 2349-2352). For `ρ > 0` and `M`
there is a smooth `Hc` equal to `M (x₁ - i x₂)^{-2}` for `|x| > ρ` (take `(1-χ) M (x₁-ix₂)^{-2}`
with `χ` a smooth bump equal to `1` near `0` supported in the ball of radius `ρ`). -/
def CutExists : Prop :=
  ∀ (ρ : ℝ) (M : ℂ), 0 < ρ → ∃ Hc : ℝ × ℝ → ℂ, ContDiff ℝ ∞ Hc ∧
    ∀ y : ℝ × ℝ, ρ ^ 2 < y.1 ^ 2 + y.2 ^ 2 →
      Hc y = M * (((y.1 : ℂ) - (y.2 : ℂ) * Complex.I) ^ (-2 : ℤ))

/-- **Leaf `PartII-b:G4/2/3/2`** (Gaussian bound on the whole plane). If `F`, `Hc` are smooth, `Hc`
equals the harmonic part outside the ball of radius `ρ`, and `F - harmonic` has Gaussian derivative
bounds outside it, then `F - Hc` has Gaussian derivative bounds on all of `ℝ²` (inside the closed
ball `iteratedFDeriv` is continuous, hence bounded). -/
def CoreGaussian : Prop :=
  ∀ (F Hc : ℝ × ℝ → ℂ) (ρ : ℝ) (M : ℂ), ContDiff ℝ ∞ F → ContDiff ℝ ∞ Hc → 0 < ρ →
    (∀ y : ℝ × ℝ, ρ ^ 2 < y.1 ^ 2 + y.2 ^ 2 →
      Hc y = M * (((y.1 : ℂ) - (y.2 : ℂ) * Complex.I) ^ (-2 : ℤ))) →
    (∀ j : ℕ, ∃ (C κ : ℝ), 0 < κ ∧ ∀ x : ℝ × ℝ, ρ ^ 2 < x.1 ^ 2 + x.2 ^ 2 →
        ‖iteratedFDeriv ℝ j (fun y : ℝ × ℝ => F y -
            M * (((y.1 : ℂ) - (y.2 : ℂ) * Complex.I) ^ (-2 : ℤ))) x‖ ≤
          C * Real.exp (-(κ * (x.1 ^ 2 + x.2 ^ 2)))) →
    ∀ j : ℕ, ∃ (C κ : ℝ), 0 < κ ∧ ∀ x : ℝ × ℝ,
      ‖iteratedFDeriv ℝ j (fun y => F y - Hc y) x‖ ≤ C * Real.exp (-(κ * (x.1 ^ 2 + x.2 ^ 2)))

/-- **Leaf `PartII-b:G4/2/3/3`** (periodizing a globally Gaussian-bounded smooth function; SP
2349-2358): termwise differentiation with the uniform bound `Σ_k e^{-κ(x₁+kc)²} ≤ C`, and the
decay `e^{-κ|x₂|²} ≤ e^{-κ|x₂|/c}` for `c ≥ 1`. -/
def PerGaussian : Prop :=
  ∀ G : ℝ × ℝ → ℂ, ContDiff ℝ ∞ G →
    (∀ j : ℕ, ∃ (C κ : ℝ), 0 < κ ∧ ∀ x : ℝ × ℝ,
      ‖iteratedFDeriv ℝ j G x‖ ≤ C * Real.exp (-(κ * (x.1 ^ 2 + x.2 ^ 2)))) →
    ∀ j : ℕ, PerBoundAt j G

/-- **Leaf `PartII-b:G4/2/3/4`** (periodizing the cut harmonic part, via `sumInvSqShift`,
SP 2349-2358): `Σ_k (z + kc)^{-2} = (π/c)² csc²(π z/c)` has exponential decay `e^{-2π|x₂|/c}`, and
the difference with the periodization of `Hc` is a finite sum of smooth core terms. -/
def PerHarmonicCut : Prop :=
  ∀ (Hc : ℝ × ℝ → ℂ) (ρ : ℝ) (M : ℂ), ContDiff ℝ ∞ Hc → 0 < ρ →
    (∀ y : ℝ × ℝ, ρ ^ 2 < y.1 ^ 2 + y.2 ^ 2 →
      Hc y = M * (((y.1 : ℂ) - (y.2 : ℂ) * Complex.I) ^ (-2 : ℤ))) →
    ∀ j : ℕ, PerBoundAt j Hc

theorem perBoundAt_add {j : ℕ} {G H : ℝ × ℝ → ℂ} (hG : PerBoundAt j G) (hH : PerBoundAt j H) :
    PerBoundAt j (fun y => G y + H y) := by
  obtain ⟨C₁, κ₁, N₁, hC₁, hκ₁, h₁⟩ := hG
  obtain ⟨C₂, κ₂, N₂, hC₂, hκ₂, h₂⟩ := hH
  refine ⟨C₁ + C₂, min κ₁ κ₂, max N₁ N₂, add_pos hC₁ hC₂, lt_min hκ₁ hκ₂, fun c hc => ?_⟩
  obtain ⟨s₁, d₁, b₁⟩ := h₁ c hc
  obtain ⟨s₂, d₂, b₂⟩ := h₂ c hc
  have hsum : perC c (fun y => G y + H y) = fun x => perC c G x + perC c H x := by
    funext x
    unfold perC
    exact (s₁ x).tsum_add (s₂ x)
  have hsm : ContDiff ℝ ∞ (perC c (fun y => G y + H y)) := by
    rw [hsum]; exact d₁.add d₂
  refine ⟨fun x => (s₁ x).add (s₂ x), hsm, fun x => ?_⟩
  have hit : iteratedFDeriv ℝ j (perC c (fun y => G y + H y)) x =
      iteratedFDeriv ℝ j (perC c G) x + iteratedFDeriv ℝ j (perC c H) x := by
    rw [hsum]
    have e1 : ContDiffAt ℝ (j : WithTop ℕ∞) (perC c G) x :=
      (d₁.of_le (by exact_mod_cast le_top)).contDiffAt
    have e2 : ContDiffAt ℝ (j : WithTop ℕ∞) (perC c H) x :=
      (d₂.of_le (by exact_mod_cast le_top)).contDiffAt
    exact iteratedFDeriv_add_apply e1 e2
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc
  have ha : 0 ≤ |x.2| / c := div_nonneg (abs_nonneg _) hc0.le
  have e1 : Real.exp (-(κ₁ * |x.2| / c)) ≤ Real.exp (-(min κ₁ κ₂ * |x.2| / c)) := by
    apply Real.exp_le_exp.2
    have : min κ₁ κ₂ * (|x.2| / c) ≤ κ₁ * (|x.2| / c) :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) ha
    rw [neg_le_neg_iff]
    calc min κ₁ κ₂ * |x.2| / c = min κ₁ κ₂ * (|x.2| / c) := by ring
      _ ≤ κ₁ * (|x.2| / c) := this
      _ = κ₁ * |x.2| / c := by ring
  have e2 : Real.exp (-(κ₂ * |x.2| / c)) ≤ Real.exp (-(min κ₁ κ₂ * |x.2| / c)) := by
    apply Real.exp_le_exp.2
    have : min κ₁ κ₂ * (|x.2| / c) ≤ κ₂ * (|x.2| / c) :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) ha
    rw [neg_le_neg_iff]
    calc min κ₁ κ₂ * |x.2| / c = min κ₁ κ₂ * (|x.2| / c) := by ring
      _ ≤ κ₂ * (|x.2| / c) := this
      _ = κ₂ * |x.2| / c := by ring
  have p1 : c ^ N₁ ≤ c ^ (max N₁ N₂) := pow_le_pow_right₀ hc (le_max_left _ _)
  have p2 : c ^ N₂ ≤ c ^ (max N₁ N₂) := pow_le_pow_right₀ hc (le_max_right _ _)
  rw [hit]
  calc ‖iteratedFDeriv ℝ j (perC c G) x + iteratedFDeriv ℝ j (perC c H) x‖
      ≤ ‖iteratedFDeriv ℝ j (perC c G) x‖ + ‖iteratedFDeriv ℝ j (perC c H) x‖ := norm_add_le _ _
    _ ≤ C₁ * c ^ N₁ * Real.exp (-(κ₁ * |x.2| / c)) +
          C₂ * c ^ N₂ * Real.exp (-(κ₂ * |x.2| / c)) := add_le_add (b₁ x) (b₂ x)
    _ ≤ C₁ * c ^ (max N₁ N₂) * Real.exp (-(min κ₁ κ₂ * |x.2| / c)) +
          C₂ * c ^ (max N₁ N₂) * Real.exp (-(min κ₁ κ₂ * |x.2| / c)) := by
        gcongr
    _ = (C₁ + C₂) * c ^ (max N₁ N₂) * Real.exp (-(min κ₁ κ₂ * |x.2| / c)) := by ring

theorem periodizeCoreCut_of (h0 : CutExists) (h1 : CoreGaussian) (h2 : PerGaussian)
    (h3 : PerHarmonicCut) : PeriodizeCoreCut := by
  intro F ρ M hF hρ hbd j
  obtain ⟨Hc, hHc, hHeq⟩ := h0 ρ M hρ
  have hG : ContDiff ℝ ∞ (fun y => F y - Hc y) := hF.sub hHc
  have hGb := h1 F Hc ρ M hF hHc hρ hHeq hbd
  have hPG := h2 (fun y => F y - Hc y) hG hGb j
  have hPH := h3 Hc ρ M hHc hρ hHeq j
  have hadd := perBoundAt_add hPG hPH
  have hFe : (fun y => (F y - Hc y) + Hc y) = F := by funext y; ring
  rw [hFe] at hadd
  obtain ⟨C, κ, N, hC, hκ, h⟩ := hadd
  refine ⟨C, κ, N, hC, hκ, fun c hc => ?_⟩
  obtain ⟨_, hd, hb⟩ := h c hc
  exact ⟨hd, hb⟩

end UnforcedLeray.Short.IIb
