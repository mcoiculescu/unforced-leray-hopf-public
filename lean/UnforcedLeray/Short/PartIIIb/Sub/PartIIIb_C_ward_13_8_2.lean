import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_8
import UnforcedLeray.Analysis.LerayProjection.GradientClosure

/-!
# `PartIII-b:C/ward/13/8/2`: decomposition of `BgPresGradClosure`

Source of record `the November 2 reference manuscript`:
117-118 (the pressure is a gradient in `L²`), 2641-2642 (`p_U` recovers the discarded gradient part),
4138-4141 (exact profile equation), 5245-5246.

`BgPresGradClosure` follows from `GradL2Closure`: a smooth `p` on `ℝ³` with `∇p ∈ L²` has
`∇p` in the `L²` closure of compactly supported test gradients (hence `𝐏 ∇p = 0`).  The proof of
`GradL2Closure` is the cutoff argument `χ_R (p - c) → ∇p` with the Deny–Lions constant `c`
(`R⁻²∫_{R ≤ |y| ≤ 2R} |p - c|² → 0`), which in turn comes from an annular Poincaré inequality and a
dyadic summation.  Only the first reduction is proved here; the remaining Props are the open lemmas.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **A smooth scalar with `L²` gradient has its gradient in the compact-test gradient closure**
(source 117-118, 2641-2642). -/
def GradL2Closure : Prop :=
  ∀ p : UnforcedLeray.Space → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p →
    MemLp (physGrad p) 2 volume →
      UnforcedLeray.toL2 (physGrad p) ∈ UnforcedLeray.Leray.gradientClosure

/-- **Cutoff family** `χ_R(y) = χ(y/R)`: smooth, `0 ≤ χ_R ≤ 1`, `χ_R = 1` on `|y| ≤ R`,
`χ_R = 0` on `|y| ≥ 2R`, `‖∇χ_R‖ ≤ C / R`. -/
def CutoffFamily : Prop :=
  ∃ (χ : ℝ → UnforcedLeray.Space → ℝ) (C : ℝ), ∀ R : ℝ, 0 < R →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (χ R) ∧ (∀ y, 0 ≤ χ R y ∧ χ R y ≤ 1) ∧
    (∀ y, ‖y‖ ≤ R → χ R y = 1) ∧ (∀ y, 2 * R ≤ ‖y‖ → χ R y = 0) ∧
    (∀ y, ‖fderiv ℝ (χ R) y‖ ≤ C / R)

/-- **Deny–Lions constant**: a smooth `p` on `ℝ³` with `∇p ∈ L²` is asymptotically constant in the
annular `L²` sense: some `c` has `R⁻² ∫_{R ≤ |y| ≤ 2R} (p - c)² → 0`. -/
def DenyLionsConst : Prop :=
  ∀ p : UnforcedLeray.Space → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p →
    MemLp (physGrad p) 2 volume →
      ∃ c : ℝ, Tendsto
        (fun R : ℝ => (1 / R ^ 2) * ∫ y in {y : UnforcedLeray.Space | R ≤ ‖y‖ ∧ ‖y‖ ≤ 2 * R},
          (p y - c) ^ 2) atTop (𝓝 0)

/-- **Annular Poincaré inequality** (scale-invariant, constant independent of `R`): on
`A_R = {R ≤ |y| ≤ 4R} ⊂ ℝ³` every `C¹` function is `L²`-close to a constant `m`:
`∫_{A_R} (p - m)² ≤ C R² ∫_{A_R} |∇p|²`. -/
def AnnularPoincare : Prop :=
  ∃ C : ℝ, ∀ p : UnforcedLeray.Space → ℝ, ContDiff ℝ 1 p → ∀ R : ℝ, 0 < R →
    ∃ m : ℝ, ∫ y in {y : UnforcedLeray.Space | R ≤ ‖y‖ ∧ ‖y‖ ≤ 4 * R}, (p y - m) ^ 2 ≤
      C * R ^ 2 * ∫ y in {y : UnforcedLeray.Space | R ≤ ‖y‖ ∧ ‖y‖ ≤ 4 * R}, ‖physGrad p y‖ ^ 2

/-- **Dyadic drift lemma** (pure real analysis): if `E_k → 0` and `|m_{k+1} - m_k| ≤ K 2^{-k/2} √E_k`
then `m_k → c` with `2^{k/2} |m_k - c| → 0`. -/
def DyadicDrift : Prop :=
  ∀ (m E : ℕ → ℝ) (K : ℝ), (∀ k, 0 ≤ E k) → Tendsto E atTop (𝓝 0) →
    (∀ k, |m (k + 1) - m k| ≤ K * (2 : ℝ) ^ (-(k : ℝ) / 2) * Real.sqrt (E k)) →
      ∃ c : ℝ, Tendsto (fun k : ℕ => (2 : ℝ) ^ ((k : ℝ) / 2) * |m k - c|) atTop (𝓝 0)

/-- **`BgPresGradClosure` from `GradL2Closure`**: the exact profile pressure `pres τ` is smooth
(`IsExactProfile.smoothP`), so `∇ pres τ ∈ L²` gives `∇ pres τ` in the gradient closure and
`Leray.projection_of_mem_gradientClosure` finishes. -/
theorem bgPresGradClosure_proved_of (h : GradL2Closure) : BgPresGradClosure := by
  intro Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  refine ⟨1, one_pos, fun p d hreg hν hS hq' V rb pres hb hU τ hG => ?_⟩
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pres τ) :=
    hU.smoothP.comp (contDiff_const.prodMk contDiff_id)
  exact UnforcedLeray.Leray.projection_of_mem_gradientClosure (h _ hsm hG)

end UnforcedLeray.Short.PartIIIb.Concrete
