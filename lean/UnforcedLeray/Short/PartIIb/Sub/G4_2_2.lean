import UnforcedLeray.Short.PartIIb.Sub.G4_2

/-!
# Part II-b, task `PartII-b:G4/2/2` (`PlanarStreamQuadSplit`): decomposition

Source of record: `the November 2 reference manuscript`, lines 2349-2352 (the
planar eigenstream is the harmonic quadrupole `M (x₁ - i x₂)^{-2}`, `M = -¼ ∫₀^∞ s³ q`, plus a
Gaussian remainder outside a core).

With `R q = greenInverse q`, `greenRem q r = R q (r) - M r⁻²` the target is the radial remainder
(`greenRem`) times the angular factor `e^{2iϑ}`. Leaves:

* `EigenGaussDecay` (ODE bootstrap from the eigen equation, `Re λ > 0`, `q ∈ X_G`): all radial
  derivatives of `q` are bounded by `C e^{-κ r²}` on `[1, ∞)`;
* `GreenRemDecay`: the same for `greenRem q` (`-¼[-r⁻² ∫_r^∞ s³ q + r² ∫_r^∞ s⁻¹ q]`);
* `GreenRemSmooth`: `greenRem q` is smooth on `(0, ∞)`;
* `RadialAngularDecay`: Gaussian decay of all radial derivatives on `[1,∞)` transfers to
  `x ↦ g(|x|) e^{2iϑ}` on `|x| > 1` (chain rule / Faà di Bruno).

Proved here: `planarStream_sub_harmonic` (algebra) and `planarStreamQuadSplit_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Blueprint

/-- The radial remainder `R q (r) + ¼ (∫₀^∞ s³ q) r⁻²` (`M = -¼ quadrupole q`). -/
def greenRem (q : Planar.Profile) (r : ℝ) : ℂ :=
  Planar.greenInverse q r - (-(1 / 4 : ℂ) * Planar.quadrupole q) * (((r : ℂ) ^ 2)⁻¹)

/-- **Leaf `PartII-b:G4/2/2/1`** (Gaussian decay of the eigenprofile and all its radial
derivatives; ODE bootstrap using `q = 2ik/(λ+2iΩ) · R q`, `Re λ > 0`, `q ∈ X_G`). -/
def EigenGaussDecay : Prop :=
  ∀ (lam : ℂ) (q : Planar.Profile), Planar.IsGrowingEigenpair lam q →
    ∀ j : ℕ, ∃ (C κ : ℝ), 0 < κ ∧ ∀ r : ℝ, 1 ≤ r →
      ‖iteratedDeriv j q r‖ ≤ C * Real.exp (-(κ * r ^ 2))

/-- **Leaf `PartII-b:G4/2/2/2`** (tails): Gaussian decay of `q` and its derivatives gives Gaussian
decay of all derivatives of `greenRem q` on `[1, ∞)`. -/
def GreenRemDecay : Prop :=
  ∀ (lam : ℂ) (q : Planar.Profile), Planar.IsGrowingEigenpair lam q →
    (∀ j : ℕ, ∃ (C κ : ℝ), 0 < κ ∧ ∀ r : ℝ, 1 ≤ r →
      ‖iteratedDeriv j q r‖ ≤ C * Real.exp (-(κ * r ^ 2))) →
    ∀ j : ℕ, ∃ (C κ : ℝ), 0 < κ ∧ ∀ r : ℝ, 1 ≤ r →
      ‖iteratedDeriv j (greenRem q) r‖ ≤ C * Real.exp (-(κ * r ^ 2))

/-- **Leaf `PartII-b:G4/2/2/3`**: `greenRem q` is smooth on `(0, ∞)` for an eigenprofile. -/
def GreenRemSmooth : Prop :=
  ∀ (lam : ℂ) (q : Planar.Profile), Planar.IsGrowingEigenpair lam q →
    ContDiffOn ℝ ∞ (greenRem q) (Ioi 0)

/-- **Leaf `PartII-b:G4/2/2/4`** (radial times angular, chain rule): if `g` is smooth on `(0,∞)`
and all its derivatives are Gaussian bounded on `[1,∞)`, then all Fréchet derivatives of
`x ↦ g(|x|) e^{2iϑ}` are Gaussian bounded on `|x| > 1`. -/
def RadialAngularDecay : Prop :=
  ∀ g : ℝ → ℂ, ContDiffOn ℝ ∞ g (Ioi 0) →
    (∀ j : ℕ, ∃ (C κ : ℝ), 0 < κ ∧ ∀ r : ℝ, 1 ≤ r →
      ‖iteratedDeriv j g r‖ ≤ C * Real.exp (-(κ * r ^ 2))) →
    ∀ j : ℕ, ∃ (C κ : ℝ), 0 < κ ∧ ∀ x : ℝ × ℝ, 1 < x.1 ^ 2 + x.2 ^ 2 →
      ‖iteratedFDeriv ℝ j (fun y : ℝ × ℝ =>
          g (Real.sqrt (y.1 ^ 2 + y.2 ^ 2)) * angularTwo y) x‖ ≤
        C * Real.exp (-(κ * (x.1 ^ 2 + x.2 ^ 2)))

theorem planarStream_sub_harmonic (q : Planar.Profile) (y : ℝ × ℝ) (hy : y ≠ 0) :
    planarStream q y - (-(1 / 4 : ℂ) * Planar.quadrupole q) *
        (((y.1 : ℂ) - (y.2 : ℂ) * Complex.I) ^ (-2 : ℤ)) =
      greenRem q (Real.sqrt (y.1 ^ 2 + y.2 ^ 2)) * angularTwo y := by
  have hs : 0 < y.1 ^ 2 + y.2 ^ 2 := by
    rcases y with ⟨a, b⟩
    by_contra h
    have h1 : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    have h2 : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    exact hy (by simp [h1, h2])
  have hsq : ((Real.sqrt (y.1 ^ 2 + y.2 ^ 2) : ℝ) : ℂ) ^ 2 = ((y.1 ^ 2 + y.2 ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hs.le]
  have hsc : ((y.1 ^ 2 + y.2 ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hfac : ((y.1 : ℂ) - (y.2 : ℂ) * Complex.I) * ((y.1 : ℂ) + (y.2 : ℂ) * Complex.I) =
      ((y.1 ^ 2 + y.2 ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have hne : ((y.1 : ℂ) - (y.2 : ℂ) * Complex.I) ≠ 0 := by
    intro h
    apply hsc
    rw [← hfac, h, zero_mul]
  unfold planarStream greenRem angularTwo
  rw [hsq, zpow_neg, zpow_two]
  field_simp
  rw [← hfac]
  ring

theorem planarStreamQuadSplit_of (h1 : EigenGaussDecay) (h2 : GreenRemDecay)
    (h3 : GreenRemSmooth) (h4 : RadialAngularDecay) : PlanarStreamQuadSplit := by
  intro lam q hq
  refine ⟨1, -(1 / 4 : ℂ) * Planar.quadrupole q, one_pos, fun j => ?_⟩
  obtain ⟨C, κ, hκ, hC⟩ := h4 (greenRem q) (h3 lam q hq) (h2 lam q hq (h1 lam q hq)) j
  refine ⟨C, κ, hκ, fun x hx => ?_⟩
  have hopen : IsOpen {y : ℝ × ℝ | y ≠ 0} := isOpen_ne
  have hx0 : x ≠ 0 := by
    rintro rfl
    norm_num at hx
  have heq : (fun y : ℝ × ℝ => planarStream q y -
        (-(1 / 4 : ℂ) * Planar.quadrupole q) *
          (((y.1 : ℂ) - (y.2 : ℂ) * Complex.I) ^ (-2 : ℤ))) =ᶠ[𝓝 x]
      (fun y : ℝ × ℝ => greenRem q (Real.sqrt (y.1 ^ 2 + y.2 ^ 2)) * angularTwo y) := by
    filter_upwards [hopen.mem_nhds hx0] with y hy
    exact planarStream_sub_harmonic q y hy
  rw [(heq.iteratedFDeriv ℝ j).self_of_nhds]
  exact hC x (by simpa using hx)

end UnforcedLeray.Short.IIb
