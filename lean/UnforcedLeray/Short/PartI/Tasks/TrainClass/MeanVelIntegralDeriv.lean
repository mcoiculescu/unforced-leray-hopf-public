import UnforcedLeray.Short.PartI.Sub.T01Class
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.HmeanContDiff
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.MeanMomentumU
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Part I, task `PartI:TC/5`: age derivative of the integral of the mean velocity

Source of record: `the November 2 reference manuscript`, lines 397-404 (eq.
`sct:mean`: `S_s - ν S_ηη = g := \overline{v₁v₂}`, `\bar v₁ = -S_η`, `\bar v₂ = 0`).

The statement `MeanVelIntegralDeriv` is defined in `Short/PartI/Sub/T01Class.lean`. Notation:
`u(r,η) = meanVel1 tr r η = \bar v₁`, `g(r,η) = meanStress tr r η`.

Route.
* `u` and `g` are jointly `C^∞` on `(0,∞) × ℝ` (`hmeanContDiff` applied to `v₁` and `v₁v₂`, with
  the coordinates of the smooth train velocity).
* Differentiation under the integral over `[0,R]` (`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`,
  neighbourhood `Ioo (s/2) (2s)`, bound the maximum of `|∂_r u|` over the compact box
  `[s/2,2s] × [min 0 R, max 0 R]`):
  `d/dr ∫₀^R u(r,t) dt = ∫₀^R ∂_r u(s,t) dt` at `r = s`.
* The averaged momentum equation (`trainMeanMomentumU`) gives, for every `t`,
  `∂_r u(s,t) = ν ∂_t² u(s,t) - ∂_t g(s,t)`.
* The fundamental theorem of calculus in `t` (applied to `∂_t u(s,·)` and `g(s,·)`) turns the
  integral into `ν (∂_t u(s,R) - ∂_t u(s,0)) - (g(s,R) - g(s,0))`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-! ### Smoothness of the velocity coordinates -/

/-- The `j`-th coordinate of the train velocity is `C^∞` on `(0, ∞) × Plane`. -/
private theorem mvi_velCoord {ν c : ℝ} (tr : B0140.TrainSol ν c) (j : Fin 2) :
    ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => tr.v x.1 x.2 j) (Ioi 0 ×ˢ univ) :=
  (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp_contDiffOn
    (tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self (subset_refl _)))

/-- The product of the two velocity coordinates is `C^∞` on `(0, ∞) × Plane`. -/
private theorem mvi_velProd {ν c : ℝ} (tr : B0140.TrainSol ν c) :
    ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => tr.v x.1 x.2 0 * tr.v x.1 x.2 1) (Ioi 0 ×ˢ univ) :=
  (mvi_velCoord tr 0).mul (mvi_velCoord tr 1)

/-! ### Partial derivatives in the age variable of a function on `ℝ × ℝ` -/

/-- A function `f` that is `C^∞` on `(0,∞) × ℝ` is differentiable at every point with `0 < x`. -/
private theorem mvi_differentiableAt {f : ℝ × ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (Ioi 0 ×ˢ univ))
    {x t : ℝ} (hx : 0 < x) : DifferentiableAt ℝ f (x, t) := by
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hmem : ((x, t) : ℝ × ℝ) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) := ⟨hx, mem_univ t⟩
  exact (hf.contDiffAt (hopen.mem_nhds hmem)).differentiableAt (by simp)

/-- The derivative in the first variable of `f(·, t)` at `x` is the partial `fderiv` at `(x, t)`. -/
private theorem mvi_hasDerivAt_fst {f : ℝ × ℝ → ℝ} {x t : ℝ} (hf : DifferentiableAt ℝ f (x, t)) :
    HasDerivAt (fun r => f (r, t)) (fderiv ℝ f (x, t) (1, 0)) x := by
  have hpath : HasDerivAt (fun r : ℝ => ((r, t) : ℝ × ℝ)) ((1, 0) : ℝ × ℝ) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x t)
  exact hf.hasFDerivAt.comp_hasDerivAt x hpath

/-- The map `(x, t) ↦ ∂_x f(x, t)` is continuous on `(0,∞) × ℝ` when `f` is `C^∞` there. -/
private theorem mvi_continuousOn_fderiv {f : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioi 0 ×ˢ univ)) :
    ContinuousOn (fun x : ℝ × ℝ => fderiv ℝ f x (1, 0)) (Ioi 0 ×ˢ univ) := by
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hfd : ContinuousOn (fderiv ℝ f) (Ioi 0 ×ˢ univ) :=
    hf.continuousOn_fderiv_of_isOpen hopen (by simp)
  exact hfd.clm_apply continuousOn_const

/-- Differentiation under the integral over `[0,R]` in the age variable, for a function `f`
that is `C^∞` on `(0,∞) × ℝ`, at every `s > 0`. -/
private theorem mvi_integral_hasDerivAt {f : ℝ × ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (Ioi 0 ×ˢ univ))
    {s : ℝ} (hs : 0 < s) (R : ℝ) :
    HasDerivAt (fun r : ℝ => ∫ t in (0 : ℝ)..R, f (r, t))
      (∫ t in (0 : ℝ)..R, fderiv ℝ f (s, t) (1, 0)) s := by
  have hD : ContinuousOn (fun x : ℝ × ℝ => fderiv ℝ f x (1, 0)) (Ioi 0 ×ˢ univ) :=
    mvi_continuousOn_fderiv hf
  have hK : IsCompact (Icc (s / 2) (2 * s) ×ˢ uIcc (0 : ℝ) R) :=
    isCompact_Icc.prod isCompact_uIcc
  have hKsub : Icc (s / 2) (2 * s) ×ˢ uIcc (0 : ℝ) R ⊆ Ioi 0 ×ˢ univ := by
    intro x hx
    exact ⟨lt_of_lt_of_le (by linarith) hx.1.1, mem_univ _⟩
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hD.mono hKsub)
  have hnhds : Ioo (s / 2) (2 * s) ∈ 𝓝 s := Ioo_mem_nhds (by linarith) (by linarith)
  have hmeas : ∀ᶠ x in 𝓝 s,
      AEStronglyMeasurable (fun t => f (x, t)) ((volume : Measure ℝ).restrict (uIoc (0 : ℝ) R)) := by
    filter_upwards [Ioi_mem_nhds hs] with x hx
    exact (t01_contDiff_slice hf (Set.mem_Ioi.1 hx)).continuous.aestronglyMeasurable
  have hFint : IntervalIntegrable (fun t => f (s, t)) (volume : Measure ℝ) 0 R :=
    (t01_contDiff_slice hf hs).continuous.intervalIntegrable _ _
  have hcontT : Continuous (fun t : ℝ => fderiv ℝ f (s, t) (1, 0)) := by
    have hpt : Continuous (fun t : ℝ => ((s, t) : ℝ × ℝ)) := continuous_const.prodMk continuous_id
    have hmaps : MapsTo (fun t : ℝ => ((s, t) : ℝ × ℝ)) univ (Ioi 0 ×ˢ univ) := by
      intro t _
      exact ⟨hs, mem_univ t⟩
    exact continuousOn_univ.1 (hD.comp hpt.continuousOn hmaps)
  have hbnd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ uIoc (0 : ℝ) R → ∀ x ∈ Ioo (s / 2) (2 * s),
      ‖fderiv ℝ f (x, t) (1, 0)‖ ≤ M := by
    refine ae_of_all _ (fun t ht x hx => ?_)
    exact hM (x, t) ⟨⟨le_of_lt hx.1, le_of_lt hx.2⟩, uIoc_subset_uIcc ht⟩
  have hdiffs : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ uIoc (0 : ℝ) R → ∀ x ∈ Ioo (s / 2) (2 * s),
      HasDerivAt (fun x => f (x, t)) (fderiv ℝ f (x, t) (1, 0)) x := by
    refine ae_of_all _ (fun t _ x hx => ?_)
    have hx0 : 0 < x := by linarith [hx.1]
    exact mvi_hasDerivAt_fst (mvi_differentiableAt hf hx0)
  have hres := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun r t => f (r, t)) (F' := fun r t => fderiv ℝ f (r, t) (1, 0))
    (bound := fun _ => M) hnhds hmeas hFint hcontT.aestronglyMeasurable
    hbnd (continuous_const.intervalIntegrable _ _) hdiffs
  exact hres.2

/-! ### Fundamental theorem of calculus in the age-integrated variable -/

/-- The integral of the derivative of a `C^∞` function over `[0,R]`. -/
private theorem mvi_ftc_of_contDiff {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (R : ℝ) :
    ∫ t in (0 : ℝ)..R, deriv g t = g R - g 0 := by
  have hd := contDiff_infty_iff_deriv.1 hg
  exact intervalIntegral.integral_deriv_eq_sub (fun x _ => hd.1 x)
    (hd.2.continuous.intervalIntegrable _ _)

/-- The integral of the second derivative of a `C^∞` function over `[0,R]`. -/
private theorem mvi_ftc_deriv_of_contDiff {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (R : ℝ) :
    ∫ t in (0 : ℝ)..R, deriv (deriv u) t = deriv u R - deriv u 0 :=
  mvi_ftc_of_contDiff (contDiff_infty_iff_deriv.1 hu).2 R

/-! ### `PartI:TC/5` -/

/-- **`PartI:TC/5`. Age derivative of the integral of the mean velocity** (any train; lines
397-404): for `s > 0` and every `R`, the function `r ↦ ∫₀^R u(r,t) dt` has at `r = s` the derivative
`ν (∂_η u(s,R) - ∂_η u(s,0)) - (g(s,R) - g(s,0))`. -/
theorem meanVelIntegralDeriv : MeanVelIntegralDeriv := by
  intro ν c hν hc tr s hs R
  have hU : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanVel1 tr x.1 x.2) (Ioi 0 ×ˢ univ) :=
    hmeanContDiff c hc (fun r z => tr.v r z 0) (mvi_velCoord tr 0)
  have hG : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanStress tr x.1 x.2) (Ioi 0 ×ˢ univ) :=
    hmeanContDiff c hc (fun r z => tr.v r z 0 * tr.v r z 1) (mvi_velProd tr)
  have hUs : ContDiff ℝ ∞ (fun e : ℝ => meanVel1 tr s e) :=
    t01_contDiff_slice hU hs
  have hGs : ContDiff ℝ ∞ (fun e : ℝ => meanStress tr s e) :=
    t01_contDiff_slice hG hs
  -- differentiation under the integral
  have hI : HasDerivAt (fun r : ℝ => ∫ t in (0 : ℝ)..R, meanVel1 tr r t)
      (∫ t in (0 : ℝ)..R, fderiv ℝ (fun x : ℝ × ℝ => meanVel1 tr x.1 x.2) (s, t) (1, 0)) s :=
    mvi_integral_hasDerivAt hU hs R
  -- pointwise identity from the averaged momentum equation
  have hpt : ∀ t : ℝ, fderiv ℝ (fun x : ℝ × ℝ => meanVel1 tr x.1 x.2) (s, t) (1, 0) =
      ν * deriv (deriv (fun e => meanVel1 tr s e)) t - deriv (fun e => meanStress tr s e) t := by
    intro t
    have hdiff : DifferentiableAt ℝ (fun x : ℝ × ℝ => meanVel1 tr x.1 x.2) (s, t) :=
      mvi_differentiableAt hU hs
    have hL : fderiv ℝ (fun x : ℝ × ℝ => meanVel1 tr x.1 x.2) (s, t) (1, 0) =
        deriv (fun r => meanVel1 tr r t) s := ((mvi_hasDerivAt_fst hdiff).deriv).symm
    have hmom : deriv (fun r => meanVel1 tr r t) s + deriv (fun e => meanStress tr s e) t =
        ν * deriv (deriv (fun e => meanVel1 tr s e)) t :=
      trainMeanMomentumU ν c hν hc tr s hs t
    rw [hL]
    linear_combination hmom
  -- regularity of the slices at age `s`
  have hdU : ContDiff ℝ ∞ (deriv (fun e => meanVel1 tr s e)) :=
    (contDiff_infty_iff_deriv.1 hUs).2
  have hddU : ContDiff ℝ ∞ (deriv (deriv (fun e => meanVel1 tr s e))) :=
    (contDiff_infty_iff_deriv.1 hdU).2
  have hdG : ContDiff ℝ ∞ (deriv (fun e => meanStress tr s e)) :=
    (contDiff_infty_iff_deriv.1 hGs).2
  have hA : IntervalIntegrable (fun t => ν * deriv (deriv (fun e => meanVel1 tr s e)) t)
      (volume : Measure ℝ) 0 R :=
    (continuous_const.mul hddU.continuous).intervalIntegrable _ _
  have hB : IntervalIntegrable (fun t => deriv (fun e => meanStress tr s e) t)
      (volume : Measure ℝ) 0 R :=
    hdG.continuous.intervalIntegrable _ _
  have hval : ∫ t in (0 : ℝ)..R, fderiv ℝ (fun x : ℝ × ℝ => meanVel1 tr x.1 x.2) (s, t) (1, 0) =
      ν * (deriv (fun e => meanVel1 tr s e) R - deriv (fun e => meanVel1 tr s e) 0) -
        (meanStress tr s R - meanStress tr s 0) := by
    simp only [hpt]
    rw [intervalIntegral.integral_sub hA hB, intervalIntegral.integral_const_mul,
      mvi_ftc_deriv_of_contDiff hUs R, mvi_ftc_of_contDiff hGs R]
  exact hI.congr_deriv hval

end UnforcedLeray.Short.PartI
