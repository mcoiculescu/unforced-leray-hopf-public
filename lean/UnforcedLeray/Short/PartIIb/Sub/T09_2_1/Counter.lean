import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T09_2_1
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T09_1
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
# Part II-b, `PartII-b:T09R/1`: the counterexample to Lemma A (`DivSqrtSb`, old `T09/2/1/1`)

Source of record: `the November 2 reference manuscript`, lines 1651-1653
(`Q_ε = ∂_q - ε(K+1)`, `K = 2S + η∂_η`), 1898-1903 (`H_r = L^r(s^{r/2-5/2} ds dq/c dη)`) and
1912-1918 (graph class of `bg:profile-graph`: `b, √s Q_ε b, √s ∂_η b ∈ H_r`, never `√s b`).

`F(s, η) = s^{-1/2} h(η/√s)` satisfies `(K+1)F = 0` (`2s∂_sF = -F - η∂_ηF`), so for
`b = θ(s) F e_r` (`θ = 0` on `s ≤ 1/2`, `θ = 1` on `s ≥ 1`, `h` a bump, `= 1` on `[-1,1]`, `0` off
`(-2,2)`; `q`-independent, so `c`-periodic for every `c`):
* `Q_ε b = -2ε s θ'(s) F e_r`, supported in `1/2 ≤ s ≤ 1`, `|η| ≤ 2`;
* `∂_η b = θ s⁻¹ h'(η/√s) e_r`;
* `‖b‖^r_{H_r} ≤ ∫_{s ≥ 1/2, |η| ≤ 2√s} s^{-5/2} = 4 ∫_{1/2}^∞ s^{-2} ds < ∞`, the same for
  `√s ∂_η b`, and `√s Q_ε b` is bounded with compact support;
* `‖√s b‖^r_{H_r} ≥ ∫_{s ≥ 1, |η| ≤ √s} s^{r/2-5/2} = 2 ∫_1^∞ s^{r/2-2} ds = ∞` for `r ≥ 2`.

Hence the graph triple `(b, Q_ε b, ∂_η b)` has `DivData` for every `c > 0`, `ε`, `r > 2`, while
`√s b ∉ H_r`: `DivSqrtSb` is false (and fails on the source range, `r = 23/8`).

Leaves (ids `PartII-b:T09R/1/k`): `CxSmooth`, `WeakOfSmooth`, `CxQFormula`, `CxEFormula`,
`CxRegion`, `CxInHrB`, `CxInHrQ`, `CxInHrE`, `CxNotSqrt`.
Proved here: `cxDivData_of`, `cx_fails_of`, `divSqrtSb_false_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

namespace DivCounter

/-- `θ(s) = smoothTransition(2s - 1)`: `0` for `s ≤ 1/2`, `1` for `s ≥ 1`, monotone, smooth. -/
def cxTheta (s : ℝ) : ℝ := Real.smoothTransition (2 * s - 1)

/-- The bump `h`: `h = 1` on `[-1, 1]`, `h = 0` off `(-2, 2)`, `0 ≤ h ≤ 1`, smooth. -/
def cxH : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The self-similar profile `F(s, η) = s^{-1/2} h(η/√s)` (`(K+1)F = 0` on `s > 0`; junk for
`s ≤ 0`, where it is multiplied by `θ = 0`). -/
def cxF (x : Coord) : ℝ := (Real.sqrt x.1)⁻¹ * cxH (x.2.2 / Real.sqrt x.1)

/-- The counterexample `b = θ(s) s^{-1/2} h(η/√s) e_r` (radial component only). -/
def cxB : CProf := fun x => EuclideanSpace.single 0 ((cxTheta x.1 * cxF x : ℝ) : ℂ)

/-- Its classical `Q_ε b` (`classOp` of `Sub/PartIIb_T09_1.lean`). -/
def cxQ (ε : ℝ) : CProf := classOp (vQ ε) (dQ ε) cxB

/-- Its classical `∂_η b`. -/
def cxE : CProf := classOp vEta dZero cxB

/-! ## Leaves -/

/-- **Leaf `T09R/1/1`**: `cxB` is smooth on all of `Coord`.  Proof: `contDiff_iff_contDiffAt`;
at `x` with `x.1 < 1/2`, `cxB` vanishes on the open set `{y | y.1 < 1/2}` (`cxTheta y.1 = 0`,
`Real.smoothTransition.zero_of_nonpos`), so `ContDiffAt` of `0` (`ContDiffAt.congr_of_eventuallyEq`);
at `x` with `1/4 < x.1`, `Real.sqrt` is smooth near `x.1 > 0` and nonzero, so `cxF` is smooth
near `x` (`ContDiffAt.inv`, `.div`, `cxH.contDiff`), times `Real.smoothTransition.contDiff`, then
`Complex.ofRealCLM` and `EuclideanSpace.single 0` (a continuous linear map). -/
def CxSmooth : Prop := ContDiff ℝ ∞ cxB

/-- **Leaf `T09R/1/2`** (classical derivatives are weak derivatives): for smooth `b` and
smooth coefficients, `HasWeakVec v d b (classOp v d b)`.  Proof, per component `i` and test `φ`:
both integrands are continuous with compact support (`φ`, hence `coordTranspose v d φ`, has
compact support); `∫ (Σ_j v_j ∂_j b_i + d b_i) φ = ∫ b_i (-Σ_j ∂_j(v_j φ) + d φ)` is, for each
`j`, `integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable` with `f = v_j φ` (smooth, compact
support), `g = b_i`, direction `cdir j` (pattern: `DriftWeakSHelp.ibp_test`,
`Tasks/DriftNvC/Smooth/WeakS.lean`); `fderiv` of the component `b_i` is the component of
`fderiv b` (`EuclideanSpace.proj i` is a continuous linear map). -/
def WeakOfSmooth : Prop :=
  ∀ (v : Coord → Fin 3 → ℝ) (d : Coord → ℝ) (b : CProf),
    (∀ j, ContDiff ℝ ∞ (fun x => v x j)) → ContDiff ℝ ∞ d → ContDiff ℝ ∞ b →
    HasWeakVec v d b (classOp v d b)

/-- **Leaf `T09R/1/3`** (`(K+1)F = 0`, SP 1651-1653): the classical `Q_ε b` is
`-2ε s θ'(s) F e_r`.  Proof: for `x.1 < 1/2` both sides vanish (`cxB = 0` near `x`, so
`fderiv cxB x = 0` and `cxB x = 0`; `deriv cxTheta x.1 = 0`); for `x.1 > 1/4` write
`cxB = θ(s) F e_r`, product rule, `∂_q F = 0`, and
`-2ε s ∂_s F - ε η ∂_η F - ε F = 0` (`∂_s F = -½ s^{-3/2} h(y) - ½ η s^{-2} h'(y)`,
`∂_η F = s⁻¹ h'(y)`, `y = η/√s`); `classOp (vQ ε) (dQ ε)` reads
`(-2εs)∂_s + ∂_q + (-εη)∂_η - ε`. -/
def CxQFormula : Prop :=
  ∀ (ε : ℝ) (x : Coord), cxQ ε x =
    EuclideanSpace.single 0 ((-2 * ε * x.1 * deriv cxTheta x.1 * cxF x : ℝ) : ℂ)

/-- **Leaf `T09R/1/4`**: the classical `∂_η b = θ(s) s^{-1/2} s^{-1/2} h'(η/√s) e_r`
(`classOp vEta dZero b = fderiv b · (cdir 2)`; both sides vanish for `x.1 < 1/2`). -/
def CxEFormula : Prop :=
  ∀ x : Coord, cxE x = EuclideanSpace.single 0
    ((cxTheta x.1 * ((Real.sqrt x.1)⁻¹ * (Real.sqrt x.1)⁻¹ *
      deriv (fun y : ℝ => cxH y) (x.2.2 / Real.sqrt x.1)) : ℝ) : ℂ)

/-- **Leaf `T09R/1/5`** (Tonelli on the age-weighted cell, the norm computations' engine):
for `w` depending on `s` only, the age measure of the parabolic region `|η| ≤ k√s` is
`2k√s ds`.  Proof: `Axi.ageμ c α = (vol|_{s>0}).withDensity (s^α) ⊗ Cyl.avgμ c`
(`Lib/AxisymmetricB/Lift.lean`), `lintegral_prod` (measurable integrand, the region is closed),
`lintegral_withDensity_eq_lintegral_mul`, and for fixed `s` the inner integral is
`w s · Cyl.avgμ c (univ ×ˢ Icc (-k√s) (k√s)) = w s · ofReal (2k√s)` (`Cyl.avgμ_univ_prod`,
`Real.volume_Icc`). -/
def CxRegion : Prop :=
  ∀ (c α k : ℝ) (w : ℝ → ℝ≥0∞), 0 < c → 0 ≤ k → Measurable w →
    ∫⁻ x, {x : Coord | |x.2.2| ≤ k * Real.sqrt x.1}.indicator (fun x => w x.1) x
        ∂(Axi.ageμ c α) =
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ α) * ENNReal.ofReal (2 * k * Real.sqrt s) * w s

/-- **Leaf `T09R/1/6`**: `b ∈ H_r` for every `c > 0`, `r > 0`.  Proof: `q`-independent hence
periodic, continuous hence measurable; `‖cxB x‖ ≤ s^{-1/2}` on `{s ≥ 1/2, |η| ≤ 2√s}` and `0` off
it (`θ = 0` for `s ≤ 1/2`, `h = 0` for `|y| ≥ 2`, `0 ≤ θ, h ≤ 1`), so
`∫ ‖b‖^r dhMeas ≤ ∫ 1_{region}·1_{s≥1/2} s^{-r/2} dageμ c (r/2-5/2)`, which by `CxRegion` is
`4 ∫_{1/2}^∞ s^{-2} ds < ∞` (`integrableOn_Ioi_rpow_of_lt`, `s^{r/2-5/2} s^{-r/2} √s = s^{-2}`). -/
def CxInHrB : Prop := ∀ (c r : ℝ), 0 < c → 0 < r → InHr c r cxB

/-- **Leaf `T09R/1/7`**: `√s Q_ε b ∈ H_r`.  Proof: by `CxQFormula`, `‖√s Q_ε b‖ =
2|ε| s θ'(s) h(η/√s) ≤ 2|ε| sup|θ'|`, zero unless `1/2 ≤ s ≤ 1`, `|η| ≤ 2`
(`θ` is constant off `[1/2, 1]`); bounded on the window
`Icc (1/2) 1 ×ˢ univ ×ˢ Icc (-2) 2`, whose measure is finite
(`NiceInHrHelp.ageμ_window_lt_top`, `Tasks/DriftNvC/Approx/Moll/InHr/NiceInHr.lean`). -/
def CxInHrQ : Prop := ∀ (c r ε : ℝ), 0 < c → 0 < r → InHr c r (sqrtS (cxQ ε))

/-- **Leaf `T09R/1/8`**: `√s ∂_η b ∈ H_r`.  Proof: by `CxEFormula`,
`‖√s ∂_η b‖ ≤ sup|h'| · s^{-1/2}` on `{s ≥ 1/2, |η| ≤ 2√s}` and `0` off it; then as `CxInHrB`. -/
def CxInHrE : Prop := ∀ (c r : ℝ), 0 < c → 0 < r → InHr c r (sqrtS cxE)

/-- **Leaf `T09R/1/9`**: `√s b ∉ H_r` for `r ≥ 2`.  Proof: `‖√s b‖ = θ(s) h(η/√s) = 1` on
`{s ≥ 1, |η| ≤ √s}`, so `∫ ‖√s b‖^r dhMeas ≥ ∫ 1_{|η| ≤ √s} 1_{s ≥ 1} dageμ c (r/2-5/2)
= 2 ∫_1^∞ s^{r/2-2} ds = ∞` (`CxRegion`; `r/2 - 2 ≥ -1`, `not_integrableOn_Ioi_rpow` /
`lintegral` of `s^γ`, `γ ≥ -1`, over `Ioi 1` is `⊤`); finiteness of `hNorm` would contradict
this (`eLpNorm_eq_lintegral_rpow_enorm_toReal`). -/
def CxNotSqrt : Prop := ∀ (c r : ℝ), 0 < c → 2 ≤ r → ¬ InHr c r (sqrtS cxB)

/-! ## Assembly -/

theorem vQ_contDiff (ε : ℝ) : ∀ j : Fin 3, ContDiff ℝ ∞ (fun x : Coord => vQ ε x j) := by
  intro j
  fin_cases j <;> simp [vQ] <;> fun_prop

theorem vEta_contDiff : ∀ j : Fin 3, ContDiff ℝ ∞ (fun x : Coord => vEta x j) := by
  intro j
  fin_cases j <;> simp [vEta] <;> exact contDiff_const

/-- The counterexample triple is in the graph class for every `c > 0`, `ε`, `r > 0`. -/
theorem cxDivData_of (h1 : CxSmooth) (h2 : WeakOfSmooth) (h3 : CxInHrB) (h4 : CxInHrQ)
    (h5 : CxInHrE) {c r : ℝ} (ε : ℝ) (hc : 0 < c) (hr : 0 < r) :
    DivData c r ε cxB (cxQ ε) cxE :=
  { inHr := h3 c r hc hr
    weakQ := h2 (vQ ε) (dQ ε) cxB (vQ_contDiff ε) (by unfold dQ; exact contDiff_const) h1
    weakE := h2 vEta dZero cxB vEta_contDiff (by unfold dZero; exact contDiff_const) h1
    inQ := h4 c r ε hc hr
    inE := h5 c r hc hr }

/-- **Lemma A fails at every point of its range**: for every `c > 0`, `ε`, `r > 2` the triple
`(cxB, cxQ ε, cxE)` has `DivData` and `√s cxB ∉ H_r`. -/
theorem cx_fails_of (h1 : CxSmooth) (h2 : WeakOfSmooth) (h3 : CxInHrB) (h4 : CxInHrQ)
    (h5 : CxInHrE) (h6 : CxNotSqrt) {c r : ℝ} (ε : ℝ) (hc : 0 < c) (hr : 2 < r) :
    DivData c r ε cxB (cxQ ε) cxE ∧ ¬ InHr c r (sqrtS cxB) :=
  ⟨cxDivData_of h1 h2 h3 h4 h5 ε hc (by linarith), h6 c r hc hr.le⟩

/-- **Refutation of Lemma A** (`DivSqrtSb`, old `T09/2/1/1`). -/
theorem divSqrtSb_false_of (h1 : CxSmooth) (h2 : WeakOfSmooth) (h3 : CxInHrB) (h4 : CxInHrQ)
    (h5 : CxInHrE) (h6 : CxNotSqrt) : ¬ DivSqrtSb := by
  intro h
  have hr : (2 : ℝ) < 23 / 8 := by norm_num
  obtain ⟨hd, hn⟩ := cx_fails_of h1 h2 h3 h4 h5 h6 1 one_pos hr
  exact hn (h 1 (23 / 8) 1 cxB (cxQ 1) cxE one_pos one_pos hr hd)

end DivCounter

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.DivCounter.divSqrtSb_false_of
