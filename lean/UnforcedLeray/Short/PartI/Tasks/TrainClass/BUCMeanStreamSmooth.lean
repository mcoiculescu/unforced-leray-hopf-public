import UnforcedLeray.Short.PartI.Sub.T01Class
import UnforcedLeray.Short.PartI.Tasks.TrainClass.MeanStreamIncrement
import UnforcedLeray.Short.PartI.Tasks.TrainClass.BUCMeanVelDecay
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.TrainMeanV1
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.HmeanContDiff
import UnforcedLeray.Short.PartI.Tasks.TrainClass.BUCMeanStreamSmooth.Helpers

/-!
# Part I, task `PartI:TC/8`: the mean stream is jointly smooth (BUC train)

Source of record: `the November 2 reference manuscript`, lines 397-404.
The Prop `BUCMeanStreamSmooth` is defined in `Short/PartI/Sub/T01Class.lean`.

Route, for `s > 0`, `e ∈ ℝ`, with `U = \bar v₁` and `a(s) = S(s,0)`:
* `a` is `C^∞` on `(0,∞)`: by `meanStreamIncrement` and the FTC, `a' = g(·,0) - ν ∂_η U(·,0)`,
  which is `C^∞` on `(0,∞)` (`hmeanContDiff`, and `fderiv` of the jointly smooth `U`).
* `S(s,e) = a(s) - ∫₀^e U(s,t) dt` (`bucVel_S_deriv`, the FTC).
* `∫₀^e U(s,t) dt = e ∫₀^1 U(s, eτ) dτ`, and `(σ,e) ↦ ∫_{(0,1]} U(e^σ, eτ) dτ` is `C^∞` on
  `ℝ²` (`bucSm_kernel`); composing with `(s,e) ↦ (log s, e)` gives the claim.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-- **`PartI:TC/8`. The mean stream is jointly smooth** (BUC train; lines 397-404). -/
theorem bucMeanStreamSmooth : BUCMeanStreamSmooth := by
  intro ν c hν hc tr hb
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  -- joint smoothness of the velocity components on `(0,∞) × ℝ²`
  have hvs : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2) (Ioi 0 ×ˢ univ) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self subset_rfl)
  have hproj0 : ContDiff ℝ ∞ (fun f : Fin 2 → ℝ => f 0) := by fun_prop
  have hproj1 : ContDiff ℝ ∞ (fun f : Fin 2 → ℝ => f 1) := by fun_prop
  have hv0 : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => (tr.v x.1 x.2).ofLp 0) (Ioi 0 ×ˢ univ) :=
    (hproj0.comp (PiLp.contDiff_ofLp (p := 2) (𝕜 := ℝ) (n := ∞))).comp_contDiffOn hvs
  have hv1 : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => (tr.v x.1 x.2).ofLp 1) (Ioi 0 ×ˢ univ) :=
    (hproj1.comp (PiLp.contDiff_ofLp (p := 2) (𝕜 := ℝ) (n := ∞))).comp_contDiffOn hvs
  -- joint smoothness of `U = \bar v₁` and `g = \overline{v₁ v₂}`
  have hUsm : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanVel1 tr x.1 x.2) (Ioi 0 ×ˢ univ) :=
    hmeanContDiff c hc (fun s z => tr.v s z 0) hv0
  have hGsm : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanStress tr x.1 x.2) (Ioi 0 ×ˢ univ) :=
    hmeanContDiff c hc (fun s z => tr.v s z 0 * tr.v s z 1) (hv0.mul hv1)
  -- the two functions of `r` appearing in `a'(r)`
  have hgs : ContDiffOn ℝ ∞ (fun r : ℝ => meanStress tr r 0) (Ioi 0) :=
    hGsm.comp (contDiffOn_id.prodMk contDiffOn_const) (fun r hr => ⟨hr, mem_univ _⟩)
  have hWd : ContDiffOn ℝ ∞ (fderiv ℝ (fun x : ℝ × ℝ => meanVel1 tr x.1 x.2)) (Ioi 0 ×ˢ univ) :=
    hUsm.fderiv_of_isOpen hopen (by simp)
  have hpair : ContDiffOn ℝ ∞ (fun r : ℝ => ((r, (0 : ℝ)) : ℝ × ℝ)) (Ioi 0) :=
    contDiffOn_id.prodMk contDiffOn_const
  have hWr : ContDiffOn ℝ ∞
      (fun r : ℝ => fderiv ℝ (fun x : ℝ × ℝ => meanVel1 tr x.1 x.2) ((r, (0 : ℝ)) : ℝ × ℝ))
      (Ioi 0) :=
    hWd.comp hpair (fun r hr => ⟨hr, mem_univ _⟩)
  have hdv : ContDiffOn ℝ ∞ (fun r : ℝ => deriv (meanVel1 tr r) 0) (Ioi 0) := by
    have h1 : ContDiffOn ℝ ∞
        (fun r : ℝ => fderiv ℝ (fun x : ℝ × ℝ => meanVel1 tr x.1 x.2) ((r, (0 : ℝ)) : ℝ × ℝ)
          ((0 : ℝ), (1 : ℝ))) (Ioi 0) :=
      hWr.clm_apply contDiffOn_const
    exact h1.congr fun r hr => bucSm_deriv_eq tr hUsm r hr
  have hFsm : ContDiffOn ℝ ∞
      (fun r : ℝ => meanStress tr r 0 - ν * deriv (meanVel1 tr r) 0) (Ioi 0) :=
    hgs.sub (contDiffOn_const.mul hdv)
  have hFc : ContinuousOn (fun r : ℝ => meanStress tr r 0 - ν * deriv (meanVel1 tr r) 0)
      (Ioi 0) := hFsm.continuousOn
  -- Step A: `S(·,0)` has derivative `g(r,0) - ν ∂_η U(r,0)` for `r > 0`
  have hderivA : ∀ r : ℝ, 0 < r → HasDerivAt (fun x : ℝ => meanStream tr x 0)
      (meanStress tr r 0 - ν * deriv (meanVel1 tr r) 0) r := by
    intro r hr
    have hsub : uIcc r r ⊆ Ioi 0 := by
      rw [uIcc_self]
      exact singleton_subset_iff.2 hr
    have hint : IntervalIntegrable
        (fun t : ℝ => meanStress tr t 0 - ν * deriv (meanVel1 tr t) 0) volume r r :=
      (hFc.mono hsub).intervalIntegrable
    have hFTC := intervalIntegral.integral_hasDerivAt_right hint
      (hFc.stronglyMeasurableAtFilter isOpen_Ioi r hr) (hFc.continuousAt (Ioi_mem_nhds hr))
    have hev : (fun x : ℝ => meanStream tr x 0) =ᶠ[𝓝 r]
        (fun x : ℝ => meanStream tr r 0 +
          ∫ t in r..x, (meanStress tr t 0 - ν * deriv (meanVel1 tr t) 0)) := by
      filter_upwards [Ioi_mem_nhds hr] with x hx
      have := meanStreamIncrement ν c hν hc tr hb r x hr hx
      linarith
    exact (hFTC.const_add (meanStream tr r 0)).congr_of_eventuallyEq hev
  have hSa : ContDiffOn ℝ ∞ (fun r : ℝ => meanStream tr r 0) (Ioi 0) := by
    rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun r hr => (hderivA r hr).differentiableAt.differentiableWithinAt, ?_⟩
    exact hFsm.congr fun r hr => (hderivA r hr).deriv
  -- Step B: `S(s,e) = S(s,0) - ∫₀^e U(s,t) dt`
  have hB : ∀ s : ℝ, 0 < s → ∀ e : ℝ,
      meanStream tr s e = meanStream tr s 0 - ∫ t in (0 : ℝ)..e, meanVel1 tr s t := by
    intro s hs e
    have hcontU : ContinuousOn (fun t : ℝ => meanVel1 tr s t) univ :=
      hUsm.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun t _ => (⟨hs, mem_univ t⟩ : (s, t) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)))
    have hderiv : ∀ x ∈ uIcc (0 : ℝ) e,
        HasDerivAt (fun y : ℝ => meanStream tr s y) ((fun x => -meanVel1 tr s x) x) x :=
      fun x _ => bucVel_S_deriv tr hs.le x
    have hint : IntervalIntegrable (fun x => -meanVel1 tr s x) volume 0 e :=
      ContinuousOn.intervalIntegrable (hcontU.neg.mono (subset_univ _))
    have key := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    rw [intervalIntegral.integral_neg] at key
    linarith
  -- Step C: `∫₀^e U(s,t) dt = e ∫₀^1 U(s, e x) dx`
  have hC : ∀ s e : ℝ, ∫ t in (0 : ℝ)..e, meanVel1 tr s t =
      e * ∫ x in (0 : ℝ)..1, meanVel1 tr s (e * x) := by
    intro s e
    have h : e • ∫ x in (0 : ℝ)..1, meanVel1 tr s (e * x) =
        ∫ x in e * 0..e * 1, meanVel1 tr s x :=
      intervalIntegral.smul_integral_comp_mul_left _ e
    rw [mul_zero, mul_one, smul_eq_mul] at h
    exact h.symm
  -- Step D: the parametric integral is `C^∞` in `(σ, e)`
  have hmap : ContDiff ℝ ∞
      (fun x : ℝ × (ℝ × ℝ) => ((Real.exp x.2.1, x.2.2 * x.1) : ℝ × ℝ)) := by
    fun_prop
  have hHsm : ContDiff ℝ ∞
      (fun x : ℝ × (ℝ × ℝ) => meanVel1 tr (Real.exp x.2.1) (x.2.2 * x.1)) :=
    hUsm.comp_contDiff hmap (fun x => ⟨Real.exp_pos _, mem_univ _⟩)
  have hKf : ContDiffOn ℝ ∞
      (fun y : ℝ × ℝ => ∫ τ, meanVel1 tr (Real.exp y.1) (y.2 * τ)
        ∂(volume.restrict (Ioc (0 : ℝ) 1))) univ :=
    bucSm_kernel hHsm
  have hlog : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => ((Real.log x.1, x.2) : ℝ × ℝ))
      (Ioi 0 ×ˢ univ) := by
    refine ContDiffOn.prodMk ?_ contDiffOn_snd
    exact Real.contDiffOn_log.comp contDiffOn_fst (fun x hx => (Set.mem_Ioi.1 hx.1).ne')
  have hKc := hKf.comp hlog (fun x _ => mem_univ _)
  have hA := hSa.comp contDiffOn_fst (fun x (hx : x ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) => hx.1)
  have hfin := hA.sub (contDiffOn_snd.mul hKc)
  -- the identity `S(s,e) = a(s) - e · K(log s, e)` on `(0,∞) × ℝ`
  refine hfin.congr fun x (hx : x ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) => ?_
  have hEx : ∫ t in (0 : ℝ)..x.2, meanVel1 tr x.1 t =
      x.2 * ∫ τ, meanVel1 tr (Real.exp (Real.log x.1)) (x.2 * τ)
        ∂(volume.restrict (Ioc (0 : ℝ) 1)) := by
    rw [hC x.1 x.2, intervalIntegral.integral_of_le zero_le_one, Real.exp_log hx.1]
  show meanStream tr x.1 x.2 = meanStream tr x.1 0 -
    x.2 * ∫ τ, meanVel1 tr (Real.exp (Real.log x.1)) (x.2 * τ)
      ∂(volume.restrict (Ioc (0 : ℝ) 1))
  rw [hB x.1 hx.1 x.2, hEx]

end UnforcedLeray.Short.PartI
