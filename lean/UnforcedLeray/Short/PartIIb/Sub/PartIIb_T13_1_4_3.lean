import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_4
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# Part II-b, task `PartII-b:T13/1/4/3` (`chmMollify`): decomposition

Source: `the November 2 reference manuscript` (SP) lines 1933-1935 (smooth periodic
approximation before the cell-cutoff argument) and 1377-1424.

`w n = u ⋆ ρ_n` with `ρ_n` a normalized smooth bump of radius `1/(n+2)` on `Coord`. Leaves:
`ChmMollNice` (smooth, periodic, all derivatives in `L^r(cylMeas c)`), `ChmMollEq` (the weak
equation transfers to the convolution), `ChmMollConv` (convergence in `L^r(cylMeas c)`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

/-- The mollifier `ρ_n`: a normalized (`∫ ρ_n = 1`) smooth bump supported in the ball of radius
`1/(n+2)` about `0` in `Coord`. -/
def chmRho (n : ℕ) : Coord → ℝ :=
  (⟨1 / (2 * ((n : ℝ) + 2)), 1 / ((n : ℝ) + 2), by positivity,
      by rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]⟩ :
    ContDiffBump (0 : Coord)).normed volume

/-- Convolution of a complex function on `Coord` with a real kernel: `∫ ρ(y) u(x - y) dy`. -/
def chmConv (ρ : Coord → ℝ) (u : Coord → ℂ) (x : Coord) : ℂ := ∫ y, (ρ y : ℂ) * u (x - y)

/-- **Sub-lemma 1 (regularity).** For `q`-periodic measurable `u ∈ L^r(cylMeas c)` the mollified
`chmConv (chmRho n) u` is smooth, `q`-periodic and it and all its first and second partial
derivatives (`cdv j` is `∂_j (chmConv ρ u) = chmConv (∂_j ρ) u`) lie in `L^r(cylMeas c)`
(Young/Minkowski over the cell; `cylMeas c` is translation invariant in `s`, `η`). -/
def ChmMollNice : Prop :=
  ∀ r : ℝ, 1 < r → ∀ c : ℝ, 0 < c → ∀ u : Coord → ℂ, QPeriodicS c u →
    AEStronglyMeasurable u volume → cylNorm c r u < ⊤ →
    ∀ n : ℕ, ChmNice c r (chmConv (chmRho n) u)

/-- **Sub-lemma 2 (equation transfer).** If `(∂_s - νΔ_{q,η}) u = f` in distributions with `u, f`
`q`-periodic measurable in `L^r(cylMeas c)`, then `chmRhs ν (chmConv ρ_n u) = chmConv ρ_n f`
pointwise (test function `y ↦ ρ_n(x - y)`; `cylHeatT` commutes with translation). -/
def ChmMollEq : Prop :=
  ∀ r : ℝ, 1 < r → ∀ c ν : ℝ, 0 < c → 0 < ν → ∀ u f : Coord → ℂ,
    QPeriodicS c u → QPeriodicS c f → AEStronglyMeasurable u volume →
    AEStronglyMeasurable f volume → cylNorm c r u < ⊤ → cylNorm c r f < ⊤ →
    IsCylHeat ν u f → ∀ n : ℕ, chmRhs ν (chmConv (chmRho n) u) = chmConv (chmRho n) f

/-- **Sub-lemma 3 (convergence).** For `q`-periodic measurable `g ∈ L^r(cylMeas c)`,
`chmConv (chmRho n) g → g` in `L^r(cylMeas c)` (continuity of translation for periodic `L^r`
functions in the cylinder measure, with `∫ ρ_n = 1`). -/
def ChmMollConv : Prop :=
  ∀ r : ℝ, 1 < r → ∀ c : ℝ, 0 < c → ∀ g : Coord → ℂ, QPeriodicS c g →
    AEStronglyMeasurable g volume → cylNorm c r g < ⊤ →
    Tendsto (fun n : ℕ => cylNorm c r (fun x => chmConv (chmRho n) g x - g x)) atTop (𝓝 0)

theorem chmMollify_of (h1 : ChmMollNice) (h2 : ChmMollEq) (h3 : ChmMollConv) : ChmMollify := by
  intro r hr c ν hc hν u f hup hfp hum hfm hun hfn hheat
  refine ⟨fun n => chmConv (chmRho n) u, ?_, ?_, ?_, ?_⟩
  · exact fun n => h1 r hr c hc u hup hum hun n
  · intro n
    rw [h2 r hr c ν hc hν u f hup hfp hum hfm hun hfn hheat n]
    exact h1 r hr c hc f hfp hfm hfn n
  · exact h3 r hr c hc u hup hum hun
  · have : ∀ n : ℕ, (fun x => chmRhs ν (chmConv (chmRho n) u) x - f x) =
        fun x => chmConv (chmRho n) f x - f x := fun n => by
      rw [h2 r hr c ν hc hν u f hup hfp hum hfm hun hfn hheat n]
    simp_rw [this]
    exact h3 r hr c hc f hfp hfm hfn

end UnforcedLeray.Short.IIb
