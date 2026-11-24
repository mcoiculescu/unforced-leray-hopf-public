import UnforcedLeray.Short.PartIIb.Sub.G4_2

/-!
# Part II-b, task `PartII-b:G4/2/1` (`PlanarStreamSmooth`): decomposition into leaves

Source: `the November 2 reference manuscript` lines 2347-2352 (the Gaussian
angular-two eigenstream; smooth eigenstream core).  `planarStream q x = greenInverse q (|x|) ·
(x₁+ix₂)²/|x|²`, so smoothness at the origin reduces to `greenInverse q r = r² p(r²)` with `p`
smooth, which comes from the eigen equation `q = a · greenInverse q`,
`a(r) = 2iK(r)/(λ+2iΩ(r))`, `Ω = e^{-r²/4}`, `K = (r²/4-2)e^{-r²/4}` (entire in `r²`,
denominator nonzero since `Re λ > 0`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Blueprint

/-- **Leaf `G4/2/1/a`** (bootstrap at the origin; SP 2347-2352): for a growing eigenpair the Green
inverse is `O(r²)` at `0`.  From `MemXG` (Cauchy-Schwarz against `∫_0 s r⁻² ... `) one gets
`greenInverse q = O(r)`, then `q = a · greenInverse q = O(r)` with `a` bounded, and a second pass
of the two integrals in `greenInverse` gives `O(r²)`. -/
def GreenInverseOrderTwo : Prop :=
  ∀ (lam : ℂ) (q : Planar.Profile), Planar.IsGrowingEigenpair lam q →
    ∃ C : ℝ, ∀ r : ℝ, 0 < r → r ≤ 1 → ‖Planar.greenInverse q r‖ ≤ C * r ^ 2

/-- **Leaf `G4/2/1/b`** (regular index-2 root at `r = 0`, Frobenius-type regularity; SP 2347-2352):
under the `O(r²)` bound, the Green inverse of a growing eigenprofile is `r² p(r²)` with `p`
smooth on `ℝ`.  Route: with `G = greenInverse q`, `G'' + G'/r - 4G/r² = a(r²) G`, `a` entire in
`r²`; substituting `G = r² g(r²)` turns the integral formula into
`g(u) = -¼[∫₀¹ t³ a g(u t²)... + ½∫_u^1 ... + K]`, and one bootstraps `g ∈ C^k → g ∈ C^{k+1}` by
differentiating under the integral; extend `p` smoothly past `u = 0`. -/
def GreenInverseSqSmooth : Prop :=
  ∀ (lam : ℂ) (q : Planar.Profile), Planar.IsGrowingEigenpair lam q →
    (∃ C : ℝ, ∀ r : ℝ, 0 < r → r ≤ 1 → ‖Planar.greenInverse q r‖ ≤ C * r ^ 2) →
    ∃ p : ℝ → ℂ, ContDiff ℝ ∞ p ∧
      ∀ r : ℝ, 0 < r → Planar.greenInverse q r = (r : ℂ) ^ 2 * p (r ^ 2)

/-- Assembly: `planarStream q x = (x₁+ix₂)² p(|x|²)` for all `x` (including `0`, where both sides
vanish because `angularTwo 0 = 0` in Lean). -/
theorem planarStreamSmooth_of (h1 : GreenInverseOrderTwo) (h2 : GreenInverseSqSmooth) :
    PlanarStreamSmooth := by
  intro lam q h
  obtain ⟨p, hp, hG⟩ := h2 lam q h (h1 lam q h)
  have heq : planarStream q = fun x : ℝ × ℝ =>
      (((x.1 : ℂ) + (x.2 : ℂ) * Complex.I) ^ 2) * p (x.1 ^ 2 + x.2 ^ 2) := by
    funext x
    by_cases hx : x.1 ^ 2 + x.2 ^ 2 = 0
    · have h1' : x.1 = 0 := by nlinarith [sq_nonneg x.1, sq_nonneg x.2]
      have h2' : x.2 = 0 := by nlinarith [sq_nonneg x.1, sq_nonneg x.2]
      simp [planarStream, angularTwo, h1', h2']
    · have hpos : 0 < x.1 ^ 2 + x.2 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hx)
      have hr : 0 < Real.sqrt (x.1 ^ 2 + x.2 ^ 2) := Real.sqrt_pos.2 hpos
      have hsq : Real.sqrt (x.1 ^ 2 + x.2 ^ 2) ^ 2 = x.1 ^ 2 + x.2 ^ 2 := Real.sq_sqrt hpos.le
      unfold planarStream angularTwo
      rw [hG _ hr, hsq]
      have hne : ((x.1 ^ 2 + x.2 ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx
      have hc : ((Real.sqrt (x.1 ^ 2 + x.2 ^ 2) : ℝ) : ℂ) ^ 2 = ((x.1 ^ 2 + x.2 ^ 2 : ℝ) : ℂ) := by
        exact_mod_cast hsq
      rw [hc]
      push_cast at hne ⊢
      field_simp
  rw [heq]
  have h1c : ContDiff ℝ ∞ (fun x : ℝ × ℝ => (x.1 : ℂ)) := Complex.ofRealCLM.contDiff.comp contDiff_fst
  have h2c : ContDiff ℝ ∞ (fun x : ℝ × ℝ => (x.2 : ℂ)) := Complex.ofRealCLM.contDiff.comp contDiff_snd
  have hs : ContDiff ℝ ∞ (fun x : ℝ × ℝ => x.1 ^ 2 + x.2 ^ 2) :=
    (contDiff_fst.pow 2).add (contDiff_snd.pow 2)
  exact ((h1c.add (h2c.mul contDiff_const)).pow 2).mul (hp.comp hs)

end UnforcedLeray.Short.IIb
