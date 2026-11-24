import UnforcedLeray.Cons.C01ReferenceChoice.Quadrupole
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Step C1, part G4: convergence, holomorphy and a nonzero value of the Mellin coupling `𝓙`

`paper/main.tex`, Theorem G4 (`thm:ref-planar-couplings`, lines 754–785, blueprint B0085):
`𝓙(μ) = ∫₀^∞ θ^{μ+1/2}𝔐(V_can(θ))dθ` (`eq:st18-t00017`) "is holomorphic on `Re μ > -3/2` and
is not identically zero", "Thus one may choose a real `μ₀ ∈ (1/16,1/8)` with
`𝓛(μ₀)𝓙(μ₀) ≠ 0`" (lines 781–783; used at lines 13608–13617, unit B0882).

This file derives the convergence (the clause `mellin_integrable` of `IsPlanarReference`), the
holomorphy, the continuity of `𝓙` at every `μ > -3/2`, and the choice of a real point with
`𝓙(μ) ≠ 0` in any interval, from:
* the X_G facts of G3b (`eq:st18-t00013`, lines 735–752) on a curve `V`: `V(θ) ∈ X_G`,
  bounded in `X_G` near zero, `‖e^{λθ}θ^κV(θ) - q‖_{X_G} ≤ C/θ` for large `θ` (the clauses of
  `Blueprint.Planar.IsCanonicalBranch`), and continuity of `Q(θ) = 𝔐(V(θ))` on `(0, ∞)`
  (used by the manuscript at line 2006, "Continuity then contradicts ..."; it follows from the
  continuity of `θ ↦ V(θ)` in `X_G`, `IsXGContinuous`, by `continuousOn_quadCurve`);
* for the choice of a real point, the nonvanishing of the complex `𝓙` somewhere on
  `Re μ > -3/2` (G4), itself proved below from `𝔐(q) ≠ 0`.

The proof writes `𝓙(μ) = mellin(𝔐 ∘ V)(μ + 3/2)` and applies Mathlib's
`mellinConvergent_of_isBigO_rpow_exp` and `mellin_differentiableAt_of_isBigO_rpow_exp`: `𝔐∘V` is
continuous on `(0,∞)` (`𝔐` is bounded on `X_G`, `Quadrupole.lean`), bounded near `0`, and
`O(e^{-γθ/2})` at infinity. The identity theorem for the holomorphic `mellin(𝔐∘V)` on the
connected half-plane `Re s > 0` then gives a real zero-free point in every interval.

Finally, `𝓙 ≢ 0` itself (unit B0132) is proved from `𝔐(q) ≠ 0`: if `𝓙` vanished on the
half-plane, Mathlib's Mellin inversion (`mellinInv_mellin_eq`) would give `𝔐(V(θ)) = 0` for all
`θ > 0`, contradicting `e^{λθ}θ^κ𝔐(V(θ)) → 𝔐(q)` (`eq:st18-t00111`).

Main declarations (namespace `UnforcedLeray.Cons.C01`): `IsXGContinuous`, `mellinJC`,
`quadCurve`, `CurveFacts`, `mellinJ_eq_mellin`, `mellinJC_eq_mellin`,
**`mellinConvergent_quadCurve`**, **`differentiableAt_mellin_quadCurve`**,
**`integrableOn_mellinJ_integrand`**, **`continuousAt_mellinJ`**,
**`exists_mem_Ioo_mellinJ_ne_zero`**, `quadCurve_eq_zero_of_mellin_eq_zero`,
**`exists_mellinJC_ne_zero`**.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Asymptotics
open scoped Topology

namespace UnforcedLeray.Cons.C01

open Blueprint.Planar

/-- `θ ↦ V(θ)` is continuous into `X_G` on `(0, ∞)` (the X_G-valued reading of G3b's "smooth at
every positive `θ`", `paper/main.tex` line 745). -/
def IsXGContinuous (V : ℝ → Profile) : Prop :=
  ∀ θ₀ : ℝ, 0 < θ₀ → Tendsto (fun θ => gaussianNorm (fun r => V θ r - V θ₀ r)) (𝓝 θ₀) (𝓝 0)

/-- `𝓙` at a complex exponent, `𝓙(μ) = ∫₀^∞ θ^{μ+1/2}𝔐(V(θ))dθ` (`eq:st18-t00017`), with the
principal power of the positive real `θ`. Lean's integral is `0` when the integrand is not
integrable, so `mellinJC V μ ≠ 0` implies convergence at `μ`. -/
def mellinJC (V : ℝ → Profile) (μ : ℂ) : ℂ :=
  ∫ θ in Ioi (0 : ℝ), (θ : ℂ) ^ (μ + 1 / 2) * quadrupole (V θ)

/-- The quadrupole curve `θ ↦ 𝔐(V(θ))`. -/
def quadCurve (V : ℝ → Profile) (θ : ℝ) : ℂ := quadrupole (V θ)

/-- `𝓙(μ) = mellin(𝔐∘V)(μ + 3/2)` at complex `μ` (no convergence needed). -/
theorem mellinJC_eq_mellin (V : ℝ → Profile) (μ : ℂ) :
    mellinJC V μ = mellin (quadCurve V) (μ + 3 / 2) := by
  unfold mellinJC mellin quadCurve
  refine setIntegral_congr_fun measurableSet_Ioi fun θ _ => ?_
  simp only [smul_eq_mul]
  congr 2
  ring

/-- The blueprint's real `𝓙` (`PlanarData.mellinJ`) is `mellin(𝔐∘V_can)(μ + 3/2)` at every real
`μ` (no convergence needed). -/
theorem mellinJ_eq_mellin (P : PlanarData) (μ : ℝ) :
    P.mellinJ μ = mellin (quadCurve P.canonical) ((μ : ℂ) + 3 / 2) := by
  unfold PlanarData.mellinJ mellin quadCurve
  refine setIntegral_congr_fun measurableSet_Ioi fun θ hθ => ?_
  simp only [smul_eq_mul]
  rw [Complex.ofReal_cpow (le_of_lt hθ)]
  congr 2
  push_cast
  ring

/-! ## Bounds on the quadrupole curve -/

section Curve

variable {V : ℝ → Profile} (hmem : ∀ θ : ℝ, 0 < θ → MemXG (V θ))
include hmem

/-- `θ ↦ 𝔐(V(θ))` is continuous on `(0, ∞)`. -/
theorem continuousOn_quadCurve (hcont : IsXGContinuous V) :
    ContinuousOn (quadCurve V) (Ioi 0) := by
  intro θ₀ hθ₀
  have hθ₀' : (0 : ℝ) < θ₀ := hθ₀
  refine ContinuousAt.continuousWithinAt ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun θ => quadrupoleBound * gaussianNorm (fun r => V θ r - V θ₀ r))
      (𝓝 θ₀) (𝓝 0) := by
    simpa using (hcont θ₀ hθ₀').const_mul quadrupoleBound
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [Ioi_mem_nhds hθ₀'] with θ hθ
  have hθ' : (0 : ℝ) < θ := hθ
  unfold quadCurve
  rw [← quadrupole_sub (hmem θ hθ') (hmem θ₀ hθ₀')]
  exact norm_quadrupole_le (MemXG.sub (hmem θ hθ') (hmem θ₀ hθ₀'))

/-- `𝔐(V(θ))` is bounded on `(0, 1]` when `V` is bounded in `X_G` there. -/
theorem quadCurve_bounded_near_zero
    (hbdd : ∃ C : ℝ, ∀ θ : ℝ, 0 < θ → θ ≤ 1 → gaussianNorm (V θ) ≤ C) :
    ∃ C : ℝ, ∀ θ : ℝ, 0 < θ → θ ≤ 1 → ‖quadCurve V θ‖ ≤ C := by
  obtain ⟨C, hC⟩ := hbdd
  exact ⟨quadrupoleBound * C, fun θ h0 h1 =>
    (norm_quadrupole_le (hmem θ h0)).trans
      (mul_le_mul_of_nonneg_left (hC θ h0 h1) quadrupoleBound_pos.le)⟩

/-- At infinity, `‖𝔐(V(θ))‖ ≤ C e^{-γθ}θ^{-Re κ}` from `‖e^{λθ}θ^κV(θ) - q‖_{X_G} ≤ C/θ`. -/
theorem quadCurve_bound_atTop {lam κ : ℂ} {q : Profile} (hq : MemXG q)
    (hasym : ∃ C θ₁ : ℝ, 0 < θ₁ ∧ ∀ θ : ℝ, θ₁ ≤ θ →
      gaussianNorm (fun r => Complex.exp (lam * θ) * (θ : ℂ) ^ κ * V θ r - q r) ≤ C / θ) :
    ∃ C θ₁ : ℝ, 0 ≤ C ∧ 0 < θ₁ ∧ ∀ θ : ℝ, θ₁ ≤ θ →
      ‖quadCurve V θ‖ ≤ C * (Real.exp (-(lam.re * θ)) * θ ^ (-κ.re)) := by
  obtain ⟨C, θ₁, hθ₁, hC⟩ := hasym
  refine ⟨‖quadrupole q‖ + quadrupoleBound * |C| / θ₁, θ₁, by
    have := quadrupoleBound_pos; positivity, hθ₁, fun θ hθ => ?_⟩
  have hθ0 : 0 < θ := lt_of_lt_of_le hθ₁ hθ
  set a : ℂ := Complex.exp (lam * θ) * (θ : ℂ) ^ κ with ha
  have hmemD : MemXG (fun r => a * V θ r - q r) := MemXG.sub (MemXG.const_mul a (hmem θ hθ0)) hq
  have hD : quadrupole (fun r => a * V θ r - q r) = a * quadCurve V θ - quadrupole q := by
    rw [quadrupole_sub (MemXG.const_mul a (hmem θ hθ0)) hq, quadrupole_const_mul]
    rfl
  have h1 : ‖a * quadCurve V θ - quadrupole q‖ ≤ quadrupoleBound * (C / θ) := by
    rw [← hD]
    exact (norm_quadrupole_le hmemD).trans
      (mul_le_mul_of_nonneg_left (hC θ hθ) quadrupoleBound_pos.le)
  have h2 : quadrupoleBound * (C / θ) ≤ quadrupoleBound * |C| / θ₁ := by
    rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ quadrupoleBound_pos.le
    calc C / θ ≤ |C| / θ := div_le_div_of_nonneg_right (le_abs_self C) hθ0.le
      _ ≤ |C| / θ₁ := div_le_div_of_nonneg_left (abs_nonneg C) hθ₁ hθ
  have h3 : ‖a * quadCurve V θ‖ ≤ ‖quadrupole q‖ + quadrupoleBound * |C| / θ₁ := by
    have := norm_le_insert' (a * quadCurve V θ) (quadrupole q)
    linarith [norm_sub_rev (a * quadCurve V θ) (quadrupole q)]
  have hna : ‖a‖ = Real.exp (lam.re * θ) * θ ^ κ.re := by
    rw [ha, norm_mul, Complex.norm_exp, Complex.norm_cpow_eq_rpow_re_of_pos hθ0]
    congr 2
    simp [Complex.mul_re]
  have hapos : 0 < ‖a‖ := by rw [hna]; positivity
  rw [norm_mul] at h3
  have h4 : ‖quadCurve V θ‖ ≤ (‖quadrupole q‖ + quadrupoleBound * |C| / θ₁) / ‖a‖ := by
    rw [le_div_iff₀ hapos]
    linarith
  refine h4.trans (le_of_eq ?_)
  rw [hna, Real.exp_neg, Real.rpow_neg hθ0.le]
  field_simp

/-- `𝔐∘V = O(e^{-γθ/2})` at infinity. -/
theorem quadCurve_isBigO_atTop {lam κ : ℂ} (hlam : 0 < lam.re) {q : Profile} (hq : MemXG q)
    (hasym : ∃ C θ₁ : ℝ, 0 < θ₁ ∧ ∀ θ : ℝ, θ₁ ≤ θ →
      gaussianNorm (fun r => Complex.exp (lam * θ) * (θ : ℂ) ^ κ * V θ r - q r) ≤ C / θ) :
    quadCurve V =O[atTop] fun θ => Real.exp (-(lam.re / 2) * θ) := by
  obtain ⟨C, θ₁, hC0, hθ₁, hC⟩ := quadCurve_bound_atTop hmem hq hasym
  have hlo := (isLittleO_rpow_exp_pos_mul_atTop (-κ.re) (half_pos hlam)).bound one_pos
  refine IsBigO.of_bound C ?_
  filter_upwards [hlo, eventually_ge_atTop θ₁] with θ hθ hθ₁'
  have hθ0 : 0 < θ := lt_of_lt_of_le hθ₁ hθ₁'
  have hp : θ ^ (-κ.re) ≤ Real.exp (lam.re / 2 * θ) := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hθ0 _),
      abs_of_pos (Real.exp_pos _), one_mul] at hθ
    exact hθ
  rw [Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _)]
  refine (hC θ hθ₁').trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hC0
  calc Real.exp (-(lam.re * θ)) * θ ^ (-κ.re)
      ≤ Real.exp (-(lam.re * θ)) * Real.exp (lam.re / 2 * θ) :=
        mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le
    _ = Real.exp (-(lam.re / 2) * θ) := by
        rw [← Real.exp_add]
        ring_nf

/-- `𝔐∘V = O(1) = O(θ^{-0})` at `0⁺`. -/
theorem quadCurve_isBigO_nhdsGT_zero
    (hbdd : ∃ C : ℝ, ∀ θ : ℝ, 0 < θ → θ ≤ 1 → gaussianNorm (V θ) ≤ C) :
    quadCurve V =O[𝓝[>] 0] fun θ : ℝ => θ ^ (-(0 : ℝ)) := by
  obtain ⟨C, hC⟩ := quadCurve_bounded_near_zero hmem hbdd
  refine IsBigO.of_bound C ?_
  filter_upwards [Ioc_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with θ hθ
  rw [neg_zero, Real.rpow_zero, norm_one, mul_one]
  exact hC θ hθ.1 hθ.2

end Curve

/-! ## Convergence and holomorphy of `𝓙` -/

section Mellin

variable {V : ℝ → Profile} {lam κ : ℂ} {q : Profile}

/-- The hypotheses of this file on a curve `V`: the X_G clauses of G3b and continuity of
`θ ↦ 𝔐(V(θ))` on `(0, ∞)`. -/
structure CurveFacts (V : ℝ → Profile) (lam κ : ℂ) (q : Profile) : Prop where
  re_pos : 0 < lam.re
  memXG_q : MemXG q
  memXG : ∀ θ : ℝ, 0 < θ → MemXG (V θ)
  continuous : ContinuousOn (quadCurve V) (Ioi 0)
  bounded_near_zero : ∃ C : ℝ, ∀ θ : ℝ, 0 < θ → θ ≤ 1 → gaussianNorm (V θ) ≤ C
  asymptotic : ∃ C θ₁ : ℝ, 0 < θ₁ ∧ ∀ θ : ℝ, θ₁ ≤ θ →
    gaussianNorm (fun r => Complex.exp (lam * θ) * (θ : ℂ) ^ κ * V θ r - q r) ≤ C / θ

/-- The Mellin integral of `𝔐∘V` converges on `Re s > 0`. -/
theorem mellinConvergent_quadCurve (h : CurveFacts V lam κ q) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (quadCurve V) s :=
  mellinConvergent_of_isBigO_rpow_exp (half_pos h.re_pos)
    (h.continuous.locallyIntegrableOn measurableSet_Ioi)
    (quadCurve_isBigO_atTop h.memXG h.re_pos h.memXG_q h.asymptotic)
    (quadCurve_isBigO_nhdsGT_zero h.memXG h.bounded_near_zero) hs

/-- The Mellin transform of `𝔐∘V` is holomorphic on `Re s > 0` (G4: `𝓙` is holomorphic on
`Re μ > -3/2`). -/
theorem differentiableAt_mellin_quadCurve (h : CurveFacts V lam κ q) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (mellin (quadCurve V)) s :=
  mellin_differentiableAt_of_isBigO_rpow_exp (half_pos h.re_pos)
    (h.continuous.locallyIntegrableOn measurableSet_Ioi)
    (quadCurve_isBigO_atTop h.memXG h.re_pos h.memXG_q h.asymptotic)
    (quadCurve_isBigO_nhdsGT_zero h.memXG h.bounded_near_zero) hs

/-- **The clause `mellin_integrable`**: the integrand of `𝓙(μ)` is integrable for `μ > -3/2`. -/
theorem integrableOn_mellinJ_integrand (h : CurveFacts V lam κ q) {μ : ℝ} (hμ : -(3 / 2) < μ) :
    IntegrableOn (fun θ : ℝ => ((θ ^ (μ + 1 / 2) : ℝ) : ℂ) * quadrupole (V θ)) (Ioi 0) := by
  have hs : 0 < ((μ : ℂ) + 3 / 2).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    norm_num
    linarith
  have hc := mellinConvergent_quadCurve h hs
  refine IntegrableOn.congr_fun hc (fun θ hθ => ?_) measurableSet_Ioi
  simp only [smul_eq_mul, quadCurve]
  rw [Complex.ofReal_cpow (le_of_lt hθ)]
  congr 2
  push_cast
  ring

/-- **Continuity of `𝓙`** at every real `μ > -3/2`. -/
theorem continuousAt_mellinJ {P : PlanarData} (h : CurveFacts P.canonical lam κ q) {μ : ℝ}
    (hμ : -(3 / 2) < μ) : ContinuousAt P.mellinJ μ := by
  have he : P.mellinJ = fun x : ℝ => mellin (quadCurve P.canonical) ((x : ℂ) + 3 / 2) :=
    funext (mellinJ_eq_mellin P)
  rw [he]
  have hs : 0 < ((μ : ℂ) + 3 / 2).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    norm_num
    linarith
  exact ContinuousAt.comp (g := mellin (quadCurve P.canonical))
    (differentiableAt_mellin_quadCurve h hs).continuousAt
    (Complex.continuous_ofReal.add continuous_const).continuousAt

/-- **A real point with `𝓙 ≠ 0` in every interval** (`paper/main.tex` lines 781–783): if the
complex `𝓙` does not vanish identically on `Re μ > -3/2` (G4), then every interval
`(a, b) ⊂ (-3/2, ∞)` contains a real `μ` with `𝓙(μ) ≠ 0`, by the identity theorem. -/
theorem exists_mem_Ioo_mellinJ_ne_zero {P : PlanarData} (h : CurveFacts P.canonical lam κ q)
    (hJ : ∃ μ : ℂ, -(3 / 2) < μ.re ∧ mellinJC P.canonical μ ≠ 0) {a b : ℝ} (hab : a < b)
    (ha : -(3 / 2) < a) : ∃ σ ∈ Ioo a b, P.mellinJ σ ≠ 0 := by
  by_contra hcon
  simp only [not_exists, not_and, ne_eq, not_not] at hcon
  obtain ⟨μ, hμ, hne⟩ := hJ
  set g : ℂ → ℂ := mellin (quadCurve P.canonical) with hg
  set U : Set ℂ := {s : ℂ | 0 < s.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have hgd : DifferentiableOn ℂ g U := fun s hs =>
    (differentiableAt_mellin_quadCurve h hs).differentiableWithinAt
  have hga : AnalyticOnNhd ℂ g U := hgd.analyticOnNhd hUo
  set m : ℝ := (a + b) / 2 with hm
  set d : ℝ := (b - a) / 4 with hd
  have hd0 : 0 < d := by rw [hd]; linarith
  set z₀ : ℂ := (m : ℂ) + 3 / 2 with hz₀
  have hz₀U : z₀ ∈ U := by
    show 0 < z₀.re
    simp only [hz₀, Complex.add_re, Complex.ofReal_re]
    norm_num
    linarith
  set σ : ℕ → ℝ := fun n => m + d * (1 / ((n : ℝ) + 1)) with hσ
  have hσmem : ∀ n : ℕ, σ n ∈ Ioo a b := by
    intro n
    have hn : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hn1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    constructor
    · simp only [hσ, hm]; nlinarith
    · simp only [hσ, hm]; nlinarith
  have hσlim : Tendsto σ atTop (𝓝 m) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul d
    simpa [hσ] using (tendsto_const_nhds (x := m)).add this
  set u : ℕ → ℂ := fun n => (σ n : ℂ) + 3 / 2 with hu
  have hulim : Tendsto u atTop (𝓝[≠] z₀) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
    · exact ((Complex.continuous_ofReal.tendsto m).comp hσlim).add_const _
    · simp only [mem_compl_iff, mem_singleton_iff, hu, hz₀]
      intro heq
      have h1 : (σ n : ℂ) = m := by linear_combination heq
      have h2 : σ n = m := by exact_mod_cast h1
      have h3 : 0 < d * (1 / ((n : ℝ) + 1)) := by positivity
      simp only [hσ] at h2
      linarith
  have hfreq : ∃ᶠ z in 𝓝[≠] z₀, g z = 0 := by
    refine hulim.frequently (Frequently.of_forall fun n => ?_)
    simp only [hu, hg]
    rw [← mellinJ_eq_mellin]
    exact hcon (σ n) (hσmem n)
  have hzero := hga.eqOn_zero_of_preconnected_of_frequently_eq_zero hUc hz₀U hfreq
  apply hne
  rw [mellinJC_eq_mellin]
  have hmem : μ + 3 / 2 ∈ U := by
    show 0 < (μ + 3 / 2).re
    simp only [Complex.add_re]
    norm_num
    linarith
  exact hzero hmem

/-- **Mellin uniqueness** (the Fourier injectivity step of `paper/main.tex` lines 1996–2007,
cited there from Grafakos, Prop. 2.3.22(10)): if `mellin(𝔐∘V)` vanishes on the vertical line
`Re s = 1`, then `𝔐(V(x)) = 0` for every `x > 0`. Proof: Mathlib's Mellin inversion
`mellinInv_mellin_eq` at the continuity point `x`. -/
theorem quadCurve_eq_zero_of_mellin_eq_zero (h : CurveFacts V lam κ q)
    (h0 : ∀ y : ℝ, mellin (quadCurve V) (((1 : ℝ) : ℂ) + (y : ℂ) * Complex.I) = 0) {x : ℝ}
    (hx : 0 < x) : quadCurve V x = 0 := by
  have hconv : MellinConvergent (quadCurve V) ((1 : ℝ) : ℂ) :=
    mellinConvergent_quadCurve h (by simp)
  have hvert : Complex.VerticalIntegrable (mellin (quadCurve V)) 1 := by
    unfold Complex.VerticalIntegrable
    simp only [h0]
    exact integrable_zero _ _ _
  have hcont : ContinuousAt (quadCurve V) x :=
    h.continuous.continuousAt (Ioi_mem_nhds hx)
  have h0' : ∀ y : ℝ, mellin (quadCurve V) (1 + (y : ℂ) * Complex.I) = 0 := fun y => by
    simpa using h0 y
  rw [← mellinInv_mellin_eq 1 (quadCurve V) hx hconv hvert hcont]
  unfold mellinInv
  simp [h0']

/-- **`𝓙` is not identically zero** (G4, `paper/main.tex` lines 1985–2007, unit B0132): if
`𝔐(q) ≠ 0`, the complex `𝓙` of a curve with the G3b clauses is nonzero somewhere on
`Re μ > -3/2`. If it vanished there, Mellin uniqueness would give `𝔐(V(θ)) = 0` for all
`θ > 0`, and the asymptotic `e^{λθ}θ^κ𝔐(V(θ)) = 𝔐(q) + O(θ⁻¹)` (`eq:st18-t00111`) would force
`𝔐(q) = 0`. -/
theorem exists_mellinJC_ne_zero (h : CurveFacts V lam κ q) (hq : quadrupole q ≠ 0) :
    ∃ μ : ℂ, -(3 / 2) < μ.re ∧ mellinJC V μ ≠ 0 := by
  by_contra hcon
  simp only [not_exists, not_and, ne_eq, not_not] at hcon
  have h0 : ∀ y : ℝ, mellin (quadCurve V) (((1 : ℝ) : ℂ) + (y : ℂ) * Complex.I) = 0 := by
    intro y
    have hre : -(3 / 2) < (((1 : ℝ) : ℂ) + (y : ℂ) * Complex.I - 3 / 2).re := by
      simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
      norm_num
    have := hcon _ hre
    rw [mellinJC_eq_mellin] at this
    rwa [sub_add_cancel] at this
  have hz : ∀ θ : ℝ, 0 < θ → quadrupole (V θ) = 0 := fun θ hθ =>
    quadCurve_eq_zero_of_mellin_eq_zero h h0 hθ
  obtain ⟨C, θ₁, hθ₁, hC⟩ := h.asymptotic
  apply hq
  have hbound : ∀ θ : ℝ, θ₁ ≤ θ → ‖quadrupole q‖ ≤ quadrupoleBound * (C / θ) := by
    intro θ hθ
    have hθ0 : 0 < θ := lt_of_lt_of_le hθ₁ hθ
    set a : ℂ := Complex.exp (lam * θ) * (θ : ℂ) ^ κ
    have hmemD : MemXG (fun r => a * V θ r - q r) :=
      MemXG.sub (MemXG.const_mul a (h.memXG θ hθ0)) h.memXG_q
    have hD : quadrupole (fun r => a * V θ r - q r) = -quadrupole q := by
      rw [quadrupole_sub (MemXG.const_mul a (h.memXG θ hθ0)) h.memXG_q, quadrupole_const_mul,
        hz θ hθ0]
      ring
    have := (norm_quadrupole_le hmemD).trans
      (mul_le_mul_of_nonneg_left (hC θ hθ) quadrupoleBound_pos.le)
    rwa [hD, norm_neg] at this
  have hlim : Tendsto (fun θ : ℝ => quadrupoleBound * (C / θ)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.div_atTop tendsto_id).const_mul quadrupoleBound
  have hle : ‖quadrupole q‖ ≤ 0 :=
    ge_of_tendsto hlim ((eventually_ge_atTop θ₁).mono fun θ hθ => hbound θ hθ)
  exact norm_le_zero_iff.mp hle

end Mellin

end UnforcedLeray.Cons.C01
