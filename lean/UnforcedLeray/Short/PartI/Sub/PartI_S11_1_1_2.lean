import UnforcedLeray.Short.PartI.Sub.PartI_S11_1_1

/-!
# Part I, task `PartI:S11/1/1/2` (decomposition): `SecStreamPsi`

Source of record: `the November 2 reference manuscript`,
lines 841-889 (sector decomposition of `A_E`, stream function `Ψ = (Δ_{|m|}⁻¹φ)(|y|)(y/|y|)^m`).

Idea: `g = greenN n φ` (`n = |m|`) is smooth on `(0,∞)`, solves `g'' + g'/r - n²g/r² = φ`, equals
`c r^n` on `(0,a)` and `c' r^{-n}` on `(b,∞)` where `tsupport φ ⊆ [a,b]`.  Hence `Ψ` is smooth off
`0` (profile smooth), near `0` it is the harmonic polynomial `c y^m` / `c ȳ^{|m|}`, the Laplacian
off `0` is the polar formula, and outside radius `b` it decays like `|y|^{-n}`.

Leaves (all true source facts, stated for the concrete objects):
`SecGreenSmooth`, `SecGreenInner`, `SecGreenOuter`, `SecGreenODE`, `SecSectorSmooth`,
`SecSectorLap`, `SecOrigin`, `SecOuterDecay`.  `secStreamPsi_of` assembles `SecStreamPsi`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray UnforcedLeray.Planar.NUE

/-- **Leaf** (lines 841-889): `greenN n φ` is smooth on `(0,∞)` for `n ≥ 1` and `φ` smooth with
compact support in `(0,∞)`.  Via `greenN n φ r = -(1/(2n)) (r^{-n}∫_0^r s^{n+1}φ - r^n ∫_r^∞ s^{1-n}φ)`
(`Planar.greenN_eq_Psi`, `B0011.Psi`) and the fundamental theorem of calculus, repeatedly. -/
def SecGreenSmooth : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ φ : ℝ → ℂ, SmoothCptFun φ → ContDiffOn ℝ ∞ (Planar.greenN n φ) (Ioi 0)

/-- **Leaf** (lines 841-889): if `φ` vanishes on `(0,a]` (`a > 0`), then `greenN n φ r = c r^n` on
`(0,a)`, for a constant `c` (namely `c = (1/(2n)) ∫_0^∞ s^{1-n} φ(s) ds`, as the first integral
in the closed form vanishes). -/
def SecGreenInner : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ φ : ℝ → ℂ, SmoothCptFun φ → ∀ a : ℝ, 0 < a → (∀ r, r ≤ a → φ r = 0) →
    ∃ c : ℂ, ∀ r : ℝ, 0 < r → r < a → Planar.greenN n φ r = c * (r : ℂ) ^ n

/-- **Leaf** (lines 841-889): if `φ` vanishes on `[b,∞)`, then `greenN n φ r = c' r^{-n}` for
`r > b` (`c' = -(1/(2n)) ∫_0^∞ s^{n+1}φ(s) ds`). -/
def SecGreenOuter : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ φ : ℝ → ℂ, SmoothCptFun φ → ∀ b : ℝ, (∀ r, b ≤ r → φ r = 0) →
    ∃ c' : ℂ, ∀ r : ℝ, b < r → Planar.greenN n φ r = c' * ((r : ℂ) ^ n)⁻¹

/-- **Leaf** (lines 841-889): the radial Poisson equation pointwise,
`g'' + g'/r - n²g/r² = φ` on `(0,∞)` for `g = greenN n φ` (from `Planar.isRadialPoissonSol_greenN`
and `SecGreenSmooth`: the integrated identity differentiates, `deriv g = ψ'`). -/
def SecGreenODE : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ φ : ℝ → ℂ, SmoothCptFun φ → ∀ r : ℝ, 0 < r →
    deriv (deriv (Planar.greenN n φ)) r + deriv (Planar.greenN n φ) r / (r : ℂ) -
      (n : ℂ) ^ 2 * Planar.greenN n φ r / (r : ℂ) ^ 2 = φ r

/-- **Leaf** (general-order version of `contDiffAt_ofProfile_two`, `PartI_S05_1_1.lean`): the sector
function of a profile smooth on `(0,∞)` is smooth off the origin.
`ofProfile m ψ z = ψ ‖z‖ * (z * ‖z‖⁻¹)^m` (zpow of a smooth nonvanishing function). -/
def SecSectorSmooth : Prop :=
  ∀ (m : ℤ) (ψ : ℝ → ℂ), ContDiffOn ℝ ∞ ψ (Ioi 0) → ∀ y : ℂ, y ≠ 0 →
    ContDiffAt ℝ ∞ (Ang.ofProfile m ψ) y

/-- **Leaf** (general-order version of `PolarLaplacianCore`, `PartI_S05_1_1.lean`, lines 788-803):
for `y ≠ 0` and `ψ` smooth on `(0,∞)`,
`Δ(ofProfile m ψ)(y) = ofProfile m (ψ'' + ψ'/r - m²ψ/r²)(y)`, with `Δ` the sum of the two pure
second iterated derivatives. -/
def SecSectorLap : Prop :=
  ∀ (m : ℤ) (ψ : ℝ → ℂ), ContDiffOn ℝ ∞ ψ (Ioi 0) → ∀ y : ℂ, y ≠ 0 →
    iteratedFDeriv ℝ 2 (Ang.ofProfile m ψ) y ![1, 1] +
        iteratedFDeriv ℝ 2 (Ang.ofProfile m ψ) y ![Complex.I, Complex.I] =
      Ang.ofProfile m (fun r => deriv (deriv ψ) r + deriv ψ r / (r : ℂ) -
        (m : ℂ) ^ 2 * ψ r / (r : ℂ) ^ 2) y

/-- **Leaf** (lines 841-889, behaviour at the origin): for `m ≠ 0`, `n = |m|`, the sector function of
`c r^n` is `c y^n` (`m > 0`) or `c ȳ^n` (`m < 0`), hence smooth on all of `ℂ` and harmonic. -/
def SecOrigin : Prop :=
  ∀ (m : ℤ) (c : ℂ), m ≠ 0 →
    ContDiff ℝ ∞ (Ang.ofProfile m (fun r : ℝ => c * (r : ℂ) ^ m.natAbs)) ∧
    ∀ y : ℂ, iteratedFDeriv ℝ 2 (Ang.ofProfile m (fun r : ℝ => c * (r : ℂ) ^ m.natAbs)) y ![1, 1] +
        iteratedFDeriv ℝ 2 (Ang.ofProfile m (fun r : ℝ => c * (r : ℂ) ^ m.natAbs)) y
          ![Complex.I, Complex.I] = 0

/-- **Leaf** (lines 841-889, decay): if `ψ` is smooth on `(0,∞)` and `ψ r = c' r^{-n}` for `r > b`
(`n = |m| ≥ 1`), then `∇(ofProfile m ψ) → 0` at infinity (it is `O(|y|^{-n-1})`, since there
`ofProfile m ψ = c' y^{-n}(y/|y|)^m`-type, an explicit rational expression in `y, ȳ`). -/
def SecOuterDecay : Prop :=
  ∀ (m : ℤ) (ψ : ℝ → ℂ) (b : ℝ) (c' : ℂ), m ≠ 0 → ContDiffOn ℝ ∞ ψ (Ioi 0) →
    (∀ r : ℝ, b < r → ψ r = c' * ((r : ℂ) ^ m.natAbs)⁻¹) →
    Tendsto (fderiv ℝ (Ang.ofProfile m ψ)) (cocompact ℂ) (𝓝 0)

/-- `ofProfile m` at the origin vanishes for `m ≠ 0`. -/
theorem ofProfile_zero_pt (m : ℤ) (hm : m ≠ 0) (h : ℝ → ℂ) : Ang.ofProfile m h 0 = 0 := by
  simp [Ang.ofProfile, Ang.angPhase, zero_zpow m hm]

/-- `ofProfile m` only sees the profile on the radii. -/
theorem ofProfile_congr_norm (m : ℤ) (g h : ℝ → ℂ) (y : ℂ) (hy : g ‖y‖ = h ‖y‖) :
    Ang.ofProfile m g y = Ang.ofProfile m h y := by
  simp [Ang.ofProfile, hy]

/-- A smooth compactly supported profile in `(0,∞)` vanishes below some `a > 0` and above some `b`. -/
theorem smoothCpt_bounds {φ : ℝ → ℂ} (h : SmoothCptFun φ) :
    ∃ a b : ℝ, 0 < a ∧ (∀ r, r ≤ a → φ r = 0) ∧ (∀ r, b ≤ r → φ r = 0) := by
  obtain ⟨-, hc, hts⟩ := h
  have hK : IsCompact (tsupport φ) := hc
  obtain ⟨B, hB⟩ := hK.bddAbove
  have hKi : IsCompact ((fun x : ℝ => x⁻¹) '' tsupport φ) :=
    hK.image_of_continuousOn (fun x hx => (continuousAt_inv₀ (ne_of_gt (hts hx))).continuousWithinAt)
  obtain ⟨M, hM⟩ := hKi.bddAbove
  refine ⟨(|M| + 1)⁻¹, B + 1, by positivity, fun r hr => ?_, fun r hr => ?_⟩
  · apply image_eq_zero_of_notMem_tsupport
    intro hrK
    have h1 : r⁻¹ ≤ M := hM ⟨r, hrK, rfl⟩
    have h0 : 0 < r := hts hrK
    have : |M| + 1 ≤ r⁻¹ := by
      have := (inv_le_inv₀ (by positivity) h0).2 hr
      simpa using this
    have := le_abs_self M
    linarith
  · apply image_eq_zero_of_notMem_tsupport
    intro hrK
    have := hB hrK
    linarith

/-- **Assembly.** `SecStreamPsi` from the eight leaves. -/
theorem secStreamPsi_of (hS : SecGreenSmooth) (hI : SecGreenInner) (hO : SecGreenOuter)
    (hD : SecGreenODE) (hSS : SecSectorSmooth) (hSL : SecSectorLap) (hOr : SecOrigin)
    (hOD : SecOuterDecay) : SecStreamPsi := by
  intro m φ hφ hm
  have hn : 1 ≤ m.natAbs := Int.natAbs_pos.2 hm
  set g := Planar.greenN m.natAbs φ with hg
  have hgs : ContDiffOn ℝ ∞ g (Ioi 0) := hS m.natAbs hn φ hφ
  obtain ⟨a, b, ha, hφa, hφb⟩ := smoothCpt_bounds hφ
  obtain ⟨c, hc⟩ := hI m.natAbs hn φ hφ a ha hφa
  obtain ⟨c', hc'⟩ := hO m.natAbs hn φ hφ b hφb
  -- near the origin, `Ψ` agrees with the harmonic sector function of `c r^n`
  have hev : Ang.ofProfile m (fun r : ℝ => c * (r : ℂ) ^ m.natAbs) =ᶠ[𝓝 (0 : ℂ)] Ang.ofProfile m g := by
    have hball : Metric.ball (0 : ℂ) a ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds _ ha
    filter_upwards [hball] with z hz
    have hz' : ‖z‖ < a := by simpa using hz
    by_cases hz0 : z = 0
    · subst hz0
      rw [ofProfile_zero_pt m hm, ofProfile_zero_pt m hm]
    · exact ofProfile_congr_norm m _ _ z (hc ‖z‖ (norm_pos_iff.2 hz0) hz').symm
  obtain ⟨hOs, hOl⟩ := hOr m c hm
  refine ⟨?_, ?_, ?_⟩
  · refine contDiff_iff_contDiffAt.2 fun y => ?_
    by_cases hy : y = 0
    · subst hy
      exact hOs.contDiffAt.congr_of_eventuallyEq hev.symm
    · exact hSS m g hgs y hy
  · intro y
    by_cases hy : y = 0
    · subst hy
      have h2 := hev.iteratedFDeriv (𝕜 := ℝ) 2
      have e := h2.self_of_nhds
      rw [← e, hOl 0, ofProfile_zero_pt m hm]
    · rw [hSL m g hgs y hy]
      apply ofProfile_congr_norm
      have hpos : 0 < ‖y‖ := norm_pos_iff.2 hy
      have := hD m.natAbs hn φ hφ ‖y‖ hpos
      have hsq : ((m.natAbs : ℕ) : ℂ) ^ 2 = (m : ℂ) ^ 2 := by
        have h1 : ((|m| : ℤ) : ℂ) ^ 2 = (m : ℂ) ^ 2 := by exact_mod_cast sq_abs m
        rw [← Int.cast_natCast, Int.natCast_natAbs]
        exact h1
      rw [← hsq]
      exact this
  · exact hOD m g b c' hm hgs hc'

end UnforcedLeray.Short.PartI
