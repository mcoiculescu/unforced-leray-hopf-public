import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T08_2

/-!
# Part II-b, task `PartII-b:T08/2/3` (`DriftMollApprox`): mollification in `(log s, q, η)`

Source of record: `the November 2 reference manuscript`, lines 1898-1915
(`H_r = L^r(s^{r/2-5/2} ds dq/c dη)`, `S = s∂_s`).  On a compact window `s ∈ [s₀, s₁] ⊂ (0,∞)`
the weight is bounded above and below, and `u = log s` turns `S` into `∂_u`.  Mollify the profile
in the chart `(u, q, η)` with a fixed product-free bump kernel of radius `1/(n+2)`; the
mollification commutes with `S = ∂_u`, preserves `c`-periodicity in `q` (convolution of an
a.e.-periodic function), is smooth, and has support in a slightly enlarged window.  Convergence in
`H_r` is strong continuity of translations in `L^r` (`1 < r < ∞`).

`mollP n f` is the concrete mollification.  `driftMollApprox_of` proves `DriftMollApprox` from the
four leaves `DriftMollNice`, `MollInHr`, `MollWeak`, `MollConverge`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Convolution

namespace UnforcedLeray.Short.IIb

/-- Pull a profile back to logarithmic coordinates `(u, q, η) = (log s, q, η)`:
`f(e^u, q, η)`. -/
def logPull (f : CProf) : CProf := fun x => f (Real.exp x.1, x.2)

/-- Push a profile in `(u, q, η)` forward to the chart `(s, q, η)`; zero for `s ≤ 0`. -/
def expPush (F : CProf) : CProf := fun x => if 0 < x.1 then F (Real.log x.1, x.2) else 0

/-- The mollifying kernel of radius `1/(n+2)` on the chart `(u, q, η)`: a smooth, nonnegative,
compactly supported bump of integral `1` supported in the ball of radius `1/(n+2) ≤ 1/2`.  Its
existence is `ContDiffBump.normed` (Mathlib); only these properties are used downstream, see
`IsMollKer`. -/
def mollKer (n : ℕ) : Coord → ℝ :=
  fun x => (⟨1 / (2 * ((n : ℝ) + 2)), 1 / ((n : ℝ) + 2), by positivity,
    by rw [one_div, one_div]; apply inv_strictAnti₀ <;> [positivity; linarith]⟩ :
      ContDiffBump (0 : ℝ)).normed volume x.1 *
    ((⟨1 / (2 * ((n : ℝ) + 2)), 1 / ((n : ℝ) + 2), by positivity,
    by rw [one_div, one_div]; apply inv_strictAnti₀ <;> [positivity; linarith]⟩ :
      ContDiffBump (0 : ℝ)).normed volume x.2.1 *
    (⟨1 / (2 * ((n : ℝ) + 2)), 1 / ((n : ℝ) + 2), by positivity,
    by rw [one_div, one_div]; apply inv_strictAnti₀ <;> [positivity; linarith]⟩ :
      ContDiffBump (0 : ℝ)).normed volume x.2.2)

/-- The `n`-th mollification of a profile: convolve `f(e^u, q, η)` with `mollKer n` in
`(u, q, η)` and push back to `(s, q, η)`. -/
def mollP (n : ℕ) (f : CProf) : CProf :=
  expPush (mollKer n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] logPull f)

/-- **Leaf 1** (smoothness, periodicity, support; SP 1912-1915).  `ρ_n * (b∘exp)` is smooth
(`HasCompactSupport.contDiff_convolution_left`, `b∘exp` locally integrable on the window), it is
`c`-periodic in `q` everywhere (translate the integration variable, using a.e. periodicity of `b`),
and vanishes for `s < s₀/2`... precisely for `u < log s₀ - 1/2`, `u > log s₁ + 1/2`, `|η| > L+1`;
`expPush` of it is smooth on `Coord` because it vanishes for `s < s₀ e^{-1/2}`. -/
def DriftMollNice : Prop :=
  ∀ (c r : ℝ) (b Sb : CProf), 0 < c → 1 < r → DriftPairSE c r b Sb →
    ∀ n : ℕ, NiceProf c (mollP n b)

/-- **Leaf 2** (`H_r` membership; SP 1898-1903).  For `f` in `H_r` supported in a window, `mollP n f`
is `c`-periodic a.e., measurable (continuous) and has finite `H_r` norm: on the window the weight
`s^{r/2-5/2}` is bounded above/below, the change of variable `u = log s` identifies `H_r` with
`L^r(du dq dη)` there, and Young's inequality `‖ρ * F‖_r ≤ ‖ρ‖_1 ‖F‖_r` applies. -/
def MollInHr : Prop :=
  ∀ (c r : ℝ) (b Sb : CProf), 0 < c → 1 < r → DriftPairSE c r b Sb →
    ∀ n : ℕ, InHr c r (mollP n b) ∧ InHr c r (mollP n Sb)

/-- **Leaf 3** (commutation with `S`; SP 1912-1915).  Convolution in `u` commutes with
`S = s∂_s = ∂_u`: if `S b = Sb` weakly then `S (mollP n b) = mollP n Sb` weakly (Fubini, with the
weak identity applied to the translate of the test function; the reflected mollified test is a
coordinate test supported in `s > 0` because of the window). -/
def MollWeak : Prop :=
  ∀ (c r : ℝ) (b Sb : CProf), 0 < c → 1 < r → DriftPairSE c r b Sb →
    ∀ n : ℕ, HasWeakVec vS dZero (mollP n b) (mollP n Sb)

/-- **Leaf 4** (convergence in `H_r`; SP 1912-1915).  Approximate identity in `L^r`
(`1 < r < ∞`) in the chart `(u, q, η)`, transported to `H_r` by the bounded weight on the window. -/
def MollConverge : Prop :=
  ∀ (c r : ℝ) (b Sb : CProf), 0 < c → 1 < r → DriftPairSE c r b Sb →
    Tendsto (fun n : ℕ => hNorm c r (fun x => mollP n b x - b x)) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => hNorm c r (fun x => mollP n Sb x - Sb x)) atTop (𝓝 0)

/-- **`DriftMollApprox` from the four leaves.** -/
theorem driftMollApprox_of (h1 : DriftMollNice) (h2 : MollInHr) (h3 : MollWeak) (h4 : MollConverge) :
    DriftMollApprox := by
  intro c r b Sb hc hr hp ε hε
  obtain ⟨hb, hSb⟩ := h4 c r b Sb hc hr hp
  have hε' : (0 : ℝ≥0∞) < ENNReal.ofReal ε := ENNReal.ofReal_pos.2 hε
  obtain ⟨n, hn1, hn2⟩ := ((hb.eventually (gt_mem_nhds hε')).and
    (hSb.eventually (gt_mem_nhds hε'))).exists
  exact ⟨mollP n b, mollP n Sb, h1 c r b Sb hc hr hp n,
    ⟨(h2 c r b Sb hc hr hp n).1, (h2 c r b Sb hc hr hp n).2, h3 c r b Sb hc hr hp n⟩, hn1, hn2⟩

end UnforcedLeray.Short.IIb
