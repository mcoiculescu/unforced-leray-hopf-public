import UnforcedLeray.Short.PartIIa.Calc.BaseJets
import UnforcedLeray.Short.PartIIa.Sub.R02
import UnforcedLeray.Short.PartIIa.Sub.R02_2

/-!
# Part II-a, base jets: the mean remainder `R₀` has words of size `s^{-(3/2+b/2)}` (`RemWords`)

Target: `UnforcedLeray.Short.PartIIa.Jet.B2.remWords32_of : WordsW (3 / 2) remFam0`
(task `PartII-a:R02/10/1`).

Source of record: `the November 2 reference manuscript`, lines 447-459
(`sct:expansion` with `N = 0`, `p = ∞`: `S = a₀ G_{νs} + R₀`), lines 1267-1272 (the heat identity
and the fact that an `η` derivative gains `s^{-1/2}`).

The three conjuncts of `WordsW (3/2) remFam0`:
* smoothness: `remFam0 = meanFam - a₀ · heatProfile` on `s > 0`, with `meanFam` smooth
  (`MeanSmoothQ`) and `heatProfile` smooth (`HeatWords`);
* `∂_q remFam0 = 0`: `remFam0 ν c tr` is constant along the direction `eqDir`;
* the words `K^ℓ ∂_η^b R₀` have size `s^{-(3/2 + b/2)}`, read off from `LateMeanRemainder` with
  `N = 0` (the exponent `-(b + 2·0 + 3)/2 = -(3/2 + b/2)` is exact, no weakening).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.Jet.B2

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0188 UnforcedLeray.B0190
open UnforcedLeray.Short.PartI (IsBUCTrain meanRemainder meanCoeff)

/-- The profile `y ↦ R₀(y.2.2, y.2.1)` is invariant under translation along `eqDir`. -/
theorem remQ_const (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (x : ProfilePoint) (t : ℝ) :
    remFam0 ν c tr (x + t • eqDir) = remFam0 ν c tr x := by
  have e : (x + t • eqDir).2 = x.2 := by simp [eqDir]
  show meanRemainder tr 0 (x + t • eqDir).2.2 (x + t • eqDir).2.1 =
    meanRemainder tr 0 x.2.2 x.2.1
  rw [e]

/-- A differentiable function that is constant along a line has zero derivative along it. -/
theorem remQ_fderiv_zero {g : ProfilePoint → ℝ} {x v : ProfilePoint}
    (hg : DifferentiableAt ℝ g x) (hc : ∀ t : ℝ, g (x + t • v) = g x) :
    fderiv ℝ g x v = 0 := by
  have hl : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
    simpa using h
  have hcomp := HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hg.hasFDerivAt hl (by simp)
  have hconst : (g ∘ fun t : ℝ => x + t • v) = fun _ => g x := funext fun t => hc t
  rw [hconst] at hcomp
  exact hcomp.unique (hasDerivAt_const (0 : ℝ) (g x))

/-- The remainder is smooth for `s > 0`: `R₀ = S - a₀ G_{νs}` (`meanFam_eq`). -/
theorem remFam0_smooth (hS : MeanSmoothQ) (hH : HeatWords) : JSmooth remFam0 := by
  intro ν c hν hc tr htr
  have e : remFam0 ν c tr = fun x => meanFam ν c tr x - meanCoeff tr 0 * heatProfile ν x := by
    funext x
    have := meanFam_eq ν c tr x
    linarith
  rw [e]
  exact (hS.1 ν c hν hc tr htr).sub (contDiffOn_const.mul (hH ν hν).1)

/-- **Mean remainder words** (`sct:expansion`, lines 447-459 with `N = 0`, `p = ∞`; line 1267-1272
for the `η`-derivative gain): `WordsW (3/2) remFam0`. -/
theorem remWords32_of (h : LateIngredients) (hS : MeanSmoothQ) (hH : HeatWords) :
    WordsW (3 / 2) remFam0 := by
  have hJ := remFam0_smooth hS hH
  refine ⟨hJ, ?_, ?_⟩
  · intro ν c hν hc tr htr x hx
    have hdiff : DifferentiableAt ℝ (remFam0 ν c tr) x :=
      ((hJ ν c hν hc tr htr).contDiffAt (isOpen_late.mem_nhds hx)).differentiableAt (by simp)
    exact remQ_fderiv_zero hdiff (fun t => remQ_const ν c tr x t)
  · intro ℓ b ρ m hρ
    obtain ⟨C, M, ν₀, hν₀, H⟩ := h.remainder ρ 0 m b ℓ hρ
    refine ⟨C, M, ν₀, hν₀, fun ν hν hle tr htr x hx => ?_⟩
    have hb := H ν hν hle tr htr x hx
    have e : -((3 : ℝ) / 2 + (b : ℝ) / 2) = -(((b : ℝ) + 2 * ((0 : ℕ) : ℝ) + 3) / 2) := by
      push_cast
      ring
    show (1 + x.2.1 ^ 2 / x.2.2) ^ m *
        |(ageOperator^[ℓ] (partialEta^[b] (trainProfile fun s z => meanRemainder tr 0 s z.2))) x| ≤
      polyConst C M ν (ν ^ (-ρ)) * x.2.2 ^ (-((3 : ℝ) / 2 + (b : ℝ) / 2))
    rw [e]
    exact hb

end UnforcedLeray.Short.PartIIa.Jet.B2
