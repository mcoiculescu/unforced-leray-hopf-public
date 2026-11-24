import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.FlatGraphOrg
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_5

/-!
# Part II-b, task `PartII-b:T13/1/4` (`CylHeatMaxReg`): decomposition

Source of record: `the November 2 reference manuscript` (SP) lines 1933-1935 ("applying
the Euclidean estimate to a cutoff of `N` repeated cells, dividing its `r`-th power by `N`, and
letting `N → ∞`. There is no period loss."), and the Euclidean estimate `free:heat-estimate`,
SP 1377-1424 (`UnforcedLeray.Parabolic.heat_maximal_regularity`, `Lib/ParabolicB.lean:158`).

Proof: (1) `ChmEuclid`, the Euclidean estimate on `Coord = ℝ × (ℝ × ℝ)` for complex functions;
(2) `ChmPeriodic`, the a priori estimate for smooth `q`-periodic `u` with constant independent of
`c` and `ν` (cutoff of `N` cells, divide by `N`, `N → ∞`); (3) `ChmMollify`, smooth periodic
approximation of `(u, f)` compatible with the equation; (4) `ChmLimit`, passage to the limit.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

/-- The conclusion of `CylHeatMaxReg` for given data and constant `C`. -/
def ChmConclusion (c r ν C : ℝ) (u f : Coord → ℂ) : Prop :=
  ∃ (Dt : Coord → ℂ) (D2 : Fin 2 → Fin 2 → Coord → ℂ),
      (QPeriodicS c Dt ∧ AEStronglyMeasurable Dt volume) ∧
      (∀ i j, QPeriodicS c (D2 i j) ∧ AEStronglyMeasurable (D2 i j) volume) ∧
      (∀ φ, IsSTTestCoord φ → ∫ x, u x * (cpd 0 φ x : ℂ) = -∫ x, Dt x * (φ x : ℂ)) ∧
      (∀ (i j : Fin 2) (φ : Coord → ℝ), IsSTTestCoord φ →
        ∫ x, u x * (cpd i.succ (fun y => cpd j.succ φ y) x : ℂ) = ∫ x, D2 i j x * (φ x : ℂ)) ∧
      eLpNorm Dt (ENNReal.ofReal r) (cylMeas c) ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal r) (cylMeas c) ∧
      ∀ i j, eLpNorm (fun x => (ν : ℂ) * D2 i j x) (ENNReal.ofReal r) (cylMeas c) ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal r) (cylMeas c)

/-- **Leaf 1 (Euclidean estimate on `Coord`, SP 1377-1424).** For `1 < r` there is `C = C_r` such
that for `ν > 0` and complex `u, F ∈ L^r(volume)` (on all of `ℝ × ℝ²`) with `(∂_s - νΔ_{q,η}) u = F`
in distributions, `∂_s u` and `∂_i∂_j u` exist weakly, are measurable, and
`‖∂_s u‖_r, ‖ν ∂_i∂_j u‖_r ≤ C ‖F‖_r`. (Transport of `Parabolic.heat_maximal_regularity` for
`d = 2` along the measure-preserving isometry `ℝ × ℝ ≃ EuclideanSpace ℝ (Fin 2)`, applied to real
and imaginary parts.) -/
def ChmEuclid : Prop :=
  ∀ r : ℝ, 1 < r → ∃ C : ℝ, 0 < C ∧ ∀ ν : ℝ, 0 < ν → ∀ u F : Coord → ℂ,
    AEStronglyMeasurable u volume → AEStronglyMeasurable F volume →
    eLpNorm u (ENNReal.ofReal r) volume < ⊤ → eLpNorm F (ENNReal.ofReal r) volume < ⊤ →
    IsCylHeat ν u F →
    ∃ (Dt : Coord → ℂ) (D2 : Fin 2 → Fin 2 → Coord → ℂ),
      AEStronglyMeasurable Dt volume ∧ (∀ i j, AEStronglyMeasurable (D2 i j) volume) ∧
      (∀ φ, IsSTTestCoord φ → ∫ x, u x * (cpd 0 φ x : ℂ) = -∫ x, Dt x * (φ x : ℂ)) ∧
      (∀ (i j : Fin 2) (φ : Coord → ℝ), IsSTTestCoord φ →
        ∫ x, u x * (cpd i.succ (fun y => cpd j.succ φ y) x : ℂ) = ∫ x, D2 i j x * (φ x : ℂ)) ∧
      eLpNorm Dt (ENNReal.ofReal r) volume ≤ ENNReal.ofReal C * eLpNorm F (ENNReal.ofReal r) volume ∧
      ∀ i j, eLpNorm (fun x => (ν : ℂ) * D2 i j x) (ENNReal.ofReal r) volume ≤
        ENNReal.ofReal C * eLpNorm F (ENNReal.ofReal r) volume

/-- A smooth `q`-periodic function with `w`, its first and its second partial derivatives (all
three directions `s, q, η`) in `L^r(cylMeas c)`. -/
structure ChmNice (c r : ℝ) (w : Coord → ℂ) : Prop where
  smooth : ContDiff ℝ ∞ w
  periodic : ∀ x, w (qShift c x) = w x
  mem0 : cylNorm c r w < ⊤
  mem1 : ∀ j : Fin 3, cylNorm c r (cdv j w) < ⊤
  mem2 : ∀ j k : Fin 3, cylNorm c r (cdv j (cdv k w)) < ⊤

/-- The classical right-hand side `∂_s w - ν(∂_q² + ∂_η²) w`. -/
def chmRhs (ν : ℝ) (w : Coord → ℂ) (x : Coord) : ℂ :=
  cdv 0 w x - (ν : ℂ) * (cdv 1 (cdv 1 w) x + cdv 2 (cdv 2 w) x)

/-- The a priori inequality for nice functions with constant `C` (at `c`, `ν`). -/
def ChmAprioriAt (c r C ν : ℝ) : Prop :=
  ∀ w : Coord → ℂ, ChmNice c r w →
    cylNorm c r (cdv 0 w) ≤ ENNReal.ofReal C * cylNorm c r (chmRhs ν w) ∧
    ∀ i j : Fin 2, cylNorm c r (fun x => (ν : ℂ) * cdv i.succ (cdv j.succ w) x) ≤
      ENNReal.ofReal C * cylNorm c r (chmRhs ν w)

/-- **Leaf 2 (a priori estimate for smooth periodic functions, SP 1933-1935).** Constant
independent of `c` and `ν` ("no period loss"). Proof from `ChmEuclid`: with `ζ_N(q)` equal to `1`
on `N` cells and with transitions inside one cell on each side, `ζ_N w` solves the heat equation
with right-hand side `ζ_N f - ν(2 ∂_qζ_N ∂_q w + ∂_q²ζ_N w)`, the commutator living on two cells;
by periodicity the left side is `≥ N` times the cell norm (`dq/c` normalization); divide the
`r`-th powers by `N` and let `N → ∞`. -/
def ChmPeriodic : Prop :=
  ∀ r : ℝ, 1 < r → ∃ C : ℝ, 0 < C ∧ ∀ c ν : ℝ, 0 < c → 0 < ν → ChmAprioriAt c r C ν

/-- Smooth periodic approximants of `(u, f)` compatible with the equation. -/
def ChmApprox (c r ν : ℝ) (u f : Coord → ℂ) (w : ℕ → Coord → ℂ) : Prop :=
  (∀ n, ChmNice c r (w n)) ∧ (∀ n, ChmNice c r (chmRhs ν (w n))) ∧
  Tendsto (fun n => cylNorm c r (fun x => w n x - u x)) atTop (𝓝 0) ∧
  Tendsto (fun n => cylNorm c r (fun x => chmRhs ν (w n) x - f x)) atTop (𝓝 0)

/-- **Leaf 3 (mollification).** For `q`-periodic measurable `u, f ∈ L^r(cylMeas c)` with
`(∂_s - νΔ)u = f` in distributions, `w n = u ⋆ ρ_{1/n}` (smooth mollifier in `(s, q, η)`) is smooth,
`q`-periodic, every derivative lies in `L^r(cylMeas c)` (Young), `chmRhs ν (w n) = f ⋆ ρ_{1/n}` (the
weak equation), and `w n → u`, `chmRhs ν (w n) → f` in `L^r(cylMeas c)` (continuity of translation
for periodic `L^r` functions; `cylMeas c` is translation invariant in `s`, `η`). -/
def ChmMollify : Prop :=
  ∀ r : ℝ, 1 < r → ∀ c ν : ℝ, 0 < c → 0 < ν → ∀ u f : Coord → ℂ,
    QPeriodicS c u → QPeriodicS c f → AEStronglyMeasurable u volume →
    AEStronglyMeasurable f volume → cylNorm c r u < ⊤ → cylNorm c r f < ⊤ →
    IsCylHeat ν u f → ∃ w : ℕ → Coord → ℂ, ChmApprox c r ν u f w

/-- **Leaf 4 (limit).** If the a priori inequality holds with constant `C` and nice `w n`
approximate `(u, f)`, then `∂_s w n` and `ν ∂_i∂_j w n` are Cauchy in `L^r(cylMeas c)` (apply the
inequality to `w n - w m`, using linearity of `chmRhs`); the limits `Dt, D2` are `q`-periodic
(a.e. limits of a subsequence of periodic functions) and measurable, satisfy the weak identities
(integrate by parts against `φ`; the pairing with a compactly supported `φ` is controlled by
finitely many cells and Hölder, using periodicity) and inherit the bounds (norms converge,
`chmRhs ν (w n) → f`). -/
def ChmLimit : Prop :=
  ∀ r : ℝ, 1 < r → ∀ c C ν : ℝ, 0 < c → 0 < C → 0 < ν → ChmAprioriAt c r C ν →
    ∀ u f : Coord → ℂ, QPeriodicS c u → AEStronglyMeasurable u volume →
    AEStronglyMeasurable f volume →
    ∀ w : ℕ → Coord → ℂ, ChmApprox c r ν u f w → ChmConclusion c r ν C u f

/-- **Reduction.** `CylHeatMaxReg` from the a priori estimate, mollification and the limit. -/
theorem cylHeatMaxReg_of (hP : ChmPeriodic) (hM : ChmMollify) (hL : ChmLimit) :
    CylHeatMaxReg := by
  intro r hr
  obtain ⟨C, hC, hA⟩ := hP r hr
  refine ⟨C, hC, fun ν c hν hc u f hup hfp hum hfm hun hfn hheat => ?_⟩
  obtain ⟨w, hw⟩ := hM r hr c ν hc hν u f hup hfp hum hfm hun hfn hheat
  exact hL r hr c C ν hc hC hν (hA c ν hc hν) u f hup hum hfm w hw

end UnforcedLeray.Short.IIb
