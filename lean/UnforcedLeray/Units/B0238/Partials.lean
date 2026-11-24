import UnforcedLeray.Units.B0140
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# B0238 helpers: classical partials of `C¹` cylinder fields

Helper module of blueprint unit **B0238** (`unlabeled:4127`, `paper/main.tex` lines 4125–4134).
The classical partials `Cyl.partialQ`, `Cyl.partialEta` (one-variable `deriv` of slices) of a
`C¹` function are the Fréchet derivative applied to `(1,0)` and `(0,1)`; hence they are genuine
derivatives (no junk value of `deriv`) and continuous. Consequences used by the unit:
* `continuous_curl`: the vorticity of a `C¹` field is continuous;
* `curl_neg_of_odd`: the vorticity of a centrally odd field is centrally even (tex 4131–4133,
  2188–2191), with no regularity hypothesis;
* `hasDerivAt_intervalIntegral_slice`: differentiation of `η ↦ ∫_a^b G(q,η) dq` under the
  integral sign for a continuous `G` with a continuous classical `η`-partial.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.B0238

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec toVec)

section Slices

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The `q`-slice of a differentiable function has derivative `Dg(z)(1,0)`. -/
theorem hasDerivAt_slice_q {g : Plane → F} {z : Plane} (hg : DifferentiableAt ℝ g z) :
    HasDerivAt (fun t : ℝ => g (t, z.2)) (fderiv ℝ g z (1, 0)) z.1 := by
  have h1 : HasDerivAt (fun t : ℝ => ((t, z.2) : Plane)) ((1 : ℝ), (0 : ℝ)) z.1 :=
    (hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2)
  have h2 : HasFDerivAt g (fderiv ℝ g z) (z.1, z.2) := hg.hasFDerivAt
  exact h2.comp_hasDerivAt z.1 h1

/-- The `η`-slice of a differentiable function has derivative `Dg(z)(0,1)`. -/
theorem hasDerivAt_slice_eta {g : Plane → F} {z : Plane} (hg : DifferentiableAt ℝ g z) :
    HasDerivAt (fun t : ℝ => g (z.1, t)) (fderiv ℝ g z (0, 1)) z.2 := by
  have h1 : HasDerivAt (fun t : ℝ => ((z.1, t) : Plane)) ((0 : ℝ), (1 : ℝ)) z.2 :=
    (hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2)
  have h2 : HasFDerivAt g (fderiv ℝ g z) (z.1, z.2) := hg.hasFDerivAt
  exact h2.comp_hasDerivAt z.2 h1

theorem partialQ_eq_fderiv {g : Plane → F} {z : Plane} (hg : DifferentiableAt ℝ g z) :
    Cyl.partialQ g z = fderiv ℝ g z (1, 0) :=
  (hasDerivAt_slice_q hg).deriv

theorem partialEta_eq_fderiv {g : Plane → F} {z : Plane} (hg : DifferentiableAt ℝ g z) :
    Cyl.partialEta g z = fderiv ℝ g z (0, 1) :=
  (hasDerivAt_slice_eta hg).deriv

/-- The Fréchet derivative of a `C¹` function in a fixed direction is continuous. -/
theorem continuous_fderiv_apply {g : Plane → F} (hg : ContDiff ℝ 1 g) (w : Plane) :
    Continuous (fun z => fderiv ℝ g z w) :=
  (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const

end Slices

/-! ### Components and vorticity of `C¹` fields -/

/-- A component of a `C^n` meridional field is `C^n`. -/
theorem contDiff_comp_apply {n : WithTop ℕ∞} {v : Plane → Vec} (hv : ContDiff ℝ n v)
    (k : Fin 2) : ContDiff ℝ n (fun w => v w k) :=
  (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.comp hv

/-- The vorticity `∂_q v₂ - ∂_η v₁` of a `C¹` field, in Fréchet form. -/
theorem curl_eq_fderiv {v : Plane → Vec} (hv : ContDiff ℝ 1 v) (z : Plane) :
    Cyl.curl v z = fderiv ℝ (fun w => v w 1) z (1, 0) - fderiv ℝ (fun w => v w 0) z (0, 1) := by
  rw [Cyl.curl, partialQ_eq_fderiv ((contDiff_comp_apply hv 1).differentiable one_ne_zero z),
    partialEta_eq_fderiv ((contDiff_comp_apply hv 0).differentiable one_ne_zero z)]

/-- The vorticity of a `C¹` field is continuous. -/
theorem continuous_curl {v : Plane → Vec} (hv : ContDiff ℝ 1 v) : Continuous (Cyl.curl v) := by
  have h : Cyl.curl v = fun z =>
      fderiv ℝ (fun w => v w 1) z (1, 0) - fderiv ℝ (fun w => v w 0) z (0, 1) :=
    funext (curl_eq_fderiv hv)
  rw [h]
  exact (continuous_fderiv_apply (contDiff_comp_apply hv 1) _).sub
    (continuous_fderiv_apply (contDiff_comp_apply hv 0) _)

/-- **The vorticity of a centrally odd field is centrally even** (tex 2188–2191, 4131–4133):
if `v(-z) = -v(z)` then `curl v(-z) = curl v(z)`. No regularity is needed: the classical
partials of `t ↦ -g(-t)` are computed by `deriv_comp_neg`. -/
theorem curl_neg_of_odd {v : Plane → Vec} (hodd : ∀ z, v (-z) = -v z) (z : Plane) :
    Cyl.curl v (-z) = Cyl.curl v z := by
  have h1 : (fun t : ℝ => v (t, (-z).2) 1) = fun t => -(fun t' : ℝ => v (t', z.2) 1) (-t) := by
    funext t
    have := hodd (-t, z.2)
    rw [Prod.neg_mk, neg_neg] at this
    simp only [Prod.snd_neg, this, PiLp.neg_apply]
  have h0 : (fun t : ℝ => v ((-z).1, t) 0) = fun t => -(fun t' : ℝ => v (z.1, t') 0) (-t) := by
    funext t
    have := hodd (z.1, -t)
    rw [Prod.neg_mk, neg_neg] at this
    simp only [Prod.fst_neg, this, PiLp.neg_apply]
  rw [Cyl.curl, Cyl.partialQ, Cyl.partialEta, h1, h0]
  rw [show (fun t : ℝ => -(fun t' : ℝ => v (t', z.2) 1) (-t)) =
      -(fun t => (fun t' : ℝ => v (t', z.2) 1) (-t)) from rfl,
    show (fun t : ℝ => -(fun t' : ℝ => v (z.1, t') 0) (-t)) =
      -(fun t => (fun t' : ℝ => v (z.1, t') 0) (-t)) from rfl,
    deriv.neg, deriv.neg, deriv_comp_neg (f := fun t' : ℝ => v (t', z.2) 1),
    deriv_comp_neg (f := fun t' : ℝ => v (z.1, t') 0)]
  simp only [Prod.fst_neg, Prod.snd_neg, neg_neg, Cyl.curl, Cyl.partialQ, Cyl.partialEta]

/-! ### Differentiation under the interval integral -/

/-- `d/dη ∫_a^b G(q,η) dq = ∫_a^b ∂_η G(q,η) dq` for continuous `G` with a continuous classical
`η`-partial `G'`. -/
theorem hasDerivAt_intervalIntegral_slice {G G' : Plane → ℝ} (hG : Continuous G)
    (hG' : Continuous G') (hd : ∀ z : Plane, HasDerivAt (fun t => G (z.1, t)) (G' z) z.2)
    (a b η₀ : ℝ) :
    HasDerivAt (fun η => ∫ q in a..b, G (q, η)) (∫ q in a..b, G' (q, η₀)) η₀ := by
  obtain ⟨B, hB⟩ := (isCompact_uIcc.prod (isCompact_Icc (a := η₀ - 1) (b := η₀ + 1))).exists_bound_of_continuousOn
    hG'.continuousOn
  have hball : Metric.ball η₀ 1 ∈ 𝓝 η₀ := Metric.ball_mem_nhds η₀ one_pos
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => B)
    (F := fun η q => G (q, η)) (F' := fun η q => G' (q, η)) hball ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Eventually.of_forall fun η =>
      (hG.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  · exact (hG.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
  · exact (hG'.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  · refine Eventually.of_forall fun t ht x hx => hB (t, x) ⟨uIoc_subset_uIcc ht, ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx
    exact ⟨by linarith, by linarith⟩
  · exact intervalIntegrable_const
  · exact Eventually.of_forall fun t _ x _ => hd (t, x)

end UnforcedLeray.B0238
