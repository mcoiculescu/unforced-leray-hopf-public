import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Dyn.Defs
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# `PartIII-a:T21/2/7/2/1/1/5/18/1/11`: the energy derivative (`EnergyDerivAbs`)

Source of record: `the November 2 reference manuscript`, lines 3060-3071.

Per word `w`, the difference quotients of `f r = adjSpatial w (F r)` converge in `X_{-m,c}` to
`f' r`. Writing `P r`, `Q r` for the `Lp ℂ 2 (cellMeasure c (-m))` elements of `f r`, `f' r`, the
path `r ↦ P r` is differentiable in `Lp` with derivative `Q r`, so `‖P r‖²` has derivative
`2 * ⟪P r, Q r⟫_ℝ`, and `⟪P r, Q r⟫_ℝ = re ∫ conj (P a) * Q a = ipX c m (f r) (f' r)`.
Summing over `wordsLE j` gives `energyRate`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.IIIa

/-- The per-word derivative of `‖f r‖²_X` along an `X`-differentiable path. -/
theorem energyDerivAbs_word {c m : ℝ} {I : Set ℝ} (hI : IsOpen I) {f f' : ℝ → ℝ × ℝ → ℂ}
    (hf : ∀ r ∈ I, MemLp (f r) 2 (B0579.cellMeasure c (-m)) ∧
      MemLp (f' r) 2 (B0579.cellMeasure c (-m)))
    (hd : HasXDerivOn c m I f f') {r : ℝ} (hr : r ∈ I) :
    HasDerivAt (fun r' => (xNorm c (-m) (f r')).toReal ^ 2) (2 * ipX c m (f r) (f' r)) r := by
  classical
  set μ := B0579.cellMeasure c (-m) with hμ
  have hrI : r ∈ I := hr
  let P : ℝ → Lp ℂ 2 μ := fun r' => if h : r' ∈ I then (hf r' h).1.toLp (f r') else 0
  let Q : ℝ → Lp ℂ 2 μ := fun r' => if h : r' ∈ I then (hf r' h).2.toLp (f' r') else 0
  have hP : ∀ r' (h : r' ∈ I), P r' = (hf r' h).1.toLp (f r') := fun r' h => by
    simp only [P, dif_pos h]
  have hQ : ∀ r' (h : r' ∈ I), Q r' = (hf r' h).2.toLp (f' r') := fun r' h => by
    simp only [Q, dif_pos h]
  have hPae : ∀ r' (h : r' ∈ I), P r' =ᵐ[μ] f r' := fun r' h => by
    rw [hP r' h]; exact MemLp.coeFn_toLp _
  have hQae : ∀ r' (h : r' ∈ I), Q r' =ᵐ[μ] f' r' := fun r' h => by
    rw [hQ r' h]; exact MemLp.coeFn_toLp _
  -- the slope quotients have the norm of the `X`-difference quotient
  have hslope : ∀ r' ∈ I \ {r},
      ‖slope P r r' - Q r‖ =
        (xNorm c (-m) (fun x => (((r' - r)⁻¹ : ℝ) : ℂ) * (f r' x - f r x) - f' r x)).toReal := by
    intro r' hr'
    have hr'I : r' ∈ I := hr'.1
    have hae : (⇑(((r' - r)⁻¹ : ℝ) • (P r' - P r) - Q r) : ℝ × ℝ → ℂ) =ᵐ[μ]
        (fun x => (((r' - r)⁻¹ : ℝ) : ℂ) * (f r' x - f r x) - f' r x) := by
      filter_upwards [Lp.coeFn_sub (((r' - r)⁻¹ : ℝ) • (P r' - P r)) (Q r),
        Lp.coeFn_smul ((r' - r)⁻¹ : ℝ) (P r' - P r), Lp.coeFn_sub (P r') (P r),
        hPae r' hr'I, hPae r hrI, hQae r hrI] with x h1 h2 h3 h4 h5 h6
      simp only [h1, h2, h3, h4, h5, h6, Pi.sub_apply, Pi.smul_apply, Complex.real_smul]
    rw [slope_def_module, Lp.norm_def, eLpNorm_congr_ae hae]
    rfl
  have htend : Tendsto (fun r' => ‖slope P r r' - Q r‖) (𝓝[I \ {r}] r) (𝓝 0) := by
    have h1 := (ENNReal.tendsto_toReal (show (0 : ℝ≥0∞) ≠ ⊤ from ENNReal.zero_ne_top)).comp (hd r hr)
    rw [ENNReal.toReal_zero] at h1
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r' hr'
    exact (hslope r' hr').symm
  have hPd : HasDerivWithinAt P (Q r) I r := by
    rw [hasDerivWithinAt_iff_tendsto_slope, tendsto_iff_norm_sub_tendsto_zero]
    exact htend
  have hPdAt : HasDerivAt P (Q r) r := hPd.hasDerivAt (hI.mem_nhds hr)
  -- the real inner product structure of `Lp ℂ 2 μ` (`re` of the complex one)
  letI : InnerProductSpace ℝ (Lp ℂ 2 μ) := InnerProductSpace.rclikeToReal ℂ (Lp ℂ 2 μ)
  have hsq := hPdAt.norm_sq
  have hfeq : (fun r' => (xNorm c (-m) (f r')).toReal ^ 2) =ᶠ[𝓝 r] (fun r' => ‖P r'‖ ^ 2) := by
    filter_upwards [hI.mem_nhds hr] with r' hr'
    have : ‖P r'‖ = (xNorm c (-m) (f r')).toReal := by
      rw [Lp.norm_def]
      exact congrArg ENNReal.toReal (eLpNorm_congr_ae (hPae r' hr'))
    rw [this]
  have hinner : RCLike.re (inner ℂ (P r) (Q r)) = ipX c m (f r) (f' r) := by
    have key : ∫ a, inner ℂ (P r a) (Q r a) ∂μ =
        starRingEnd ℂ (∫ a, f r a * (starRingEnd ℂ) (f' r a) ∂μ) := by
      rw [← integral_conj]
      apply integral_congr_ae
      filter_upwards [hPae r hrI, hQae r hrI] with a h1 h2
      rw [RCLike.inner_apply', h1, h2, map_mul, Complex.conj_conj]
    rw [L2.inner_def, key]
    unfold ipX
    simp
    rfl
  have hd2 := hsq.congr_of_eventuallyEq hfeq
  refine hd2.congr_deriv ?_
  exact congrArg (fun t => 2 * t) ((real_inner_eq_re_inner ℂ (P r) (Q r)).trans hinner)

/-- **`EnergyDerivAbs`** (SP 3060-3071): the energies `cellEnergy c m j` have derivative
`energyRate c m j (F r) (F' r)` on `(a, b)`. -/
theorem energyDerivAbs : UnforcedLeray.Short.IIIa.EnergyDerivAbs := by
  intro c m j F F' a b _ hmem hd r hr
  unfold cellEnergy energyRate
  refine HasDerivAt.fun_sum (fun w _ => ?_)
  exact energyDerivAbs_word isOpen_Ioo (fun r' hr' => hmem r' hr' w) (hd w) hr

end UnforcedLeray.Short.IIIa
