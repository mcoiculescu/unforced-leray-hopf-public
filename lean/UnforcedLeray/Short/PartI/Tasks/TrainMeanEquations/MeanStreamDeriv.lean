import UnforcedLeray.Short.PartI.Sub.T01Class
import UnforcedLeray.Short.PartI.Tasks.TrainClass.MeanStreamIncrement
import UnforcedLeray.Short.PartI.Tasks.TrainClass.MeanVelIntegralDeriv

/-!
# Part I, task `PartI:T01/2`: the age derivative of the mean stream

Source of record: `the November 2 reference manuscript`, lines 397-404
(eq. `sct:mean`). The Prop `TrainMeanStreamDeriv` is defined in `Short/PartI/Sub/T01.lean`.

Route. Write `a(r) = S(r,0)`. By `MeanStreamIncrement` (`a(r) - a(s) = ∫_s^r F`, with
`F(x) = g(x,0) - ν ∂_η u(x,0)`), `F` continuous on `(0,∞)` and the FTC, `a` has derivative `F(s)`
at `s > 0`. By `msi_stream_split`, `S(r,η) = a(r) - ∫_0^η u(r,t) dt` near `r = s`, and
`MeanVelIntegralDeriv` gives the derivative of the integral term. Subtracting yields
`S_s(s,η) = g(s,η) - ν ∂_η u(s,η)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-! ### Joint smoothness of the mean velocity and mean stress on `(0,∞) × ℝ` -/

/-- The `j`-th coordinate of the train velocity is `C^∞` on `(0, ∞) × Plane`. -/
private theorem msd_velCoord {ν c : ℝ} (tr : B0140.TrainSol ν c) (j : Fin 2) :
    ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => tr.v x.1 x.2 j) (Ioi 0 ×ˢ univ) :=
  (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp_contDiffOn
    (tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self (subset_refl _)))

/-- The product of the two velocity coordinates is `C^∞` on `(0, ∞) × Plane`. -/
private theorem msd_velProd {ν c : ℝ} (tr : B0140.TrainSol ν c) :
    ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => tr.v x.1 x.2 0 * tr.v x.1 x.2 1) (Ioi 0 ×ˢ univ) :=
  (msd_velCoord tr 0).mul (msd_velCoord tr 1)

private theorem msd_hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ

private theorem msd_meanVel1_contDiff {ν c : ℝ} (hc : 0 < c) (tr : B0140.TrainSol ν c) :
    ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanVel1 tr x.1 x.2) (Ioi 0 ×ˢ univ) :=
  hmeanContDiff c hc (fun r z => tr.v r z 0) (msd_velCoord tr 0)

private theorem msd_meanStress_contDiff {ν c : ℝ} (hc : 0 < c) (tr : B0140.TrainSol ν c) :
    ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanStress tr x.1 x.2) (Ioi 0 ×ˢ univ) :=
  hmeanContDiff c hc (fun r z => tr.v r z 0 * tr.v r z 1) (msd_velProd tr)

/-! ### Continuity of the integrand `F(r) = g(r,0) - ν ∂_η u(r,0)` on `(0,∞)` -/

/-- The η-derivative of `meanVel1` at `0` is the directional derivative of the joint function. -/
private theorem msd_deriv_eq {ν c : ℝ} (hc : 0 < c) (tr : B0140.TrainSol ν c) {r : ℝ} (hr : 0 < r) :
    deriv (meanVel1 tr r) 0 = fderiv ℝ (fun x : ℝ × ℝ => meanVel1 tr x.1 x.2) (r, 0) (0, 1) := by
  have hdiff : DifferentiableAt ℝ (fun x : ℝ × ℝ => meanVel1 tr x.1 x.2) (r, 0) :=
    ((msd_meanVel1_contDiff hc tr).contDiffAt (msd_hopen.mem_nhds ⟨Set.mem_Ioi.2 hr, mem_univ _⟩)).differentiableAt
      (by simp)
  have hpath : HasDerivAt (fun e : ℝ => ((r, e) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) 0 :=
    (hasDerivAt_const (0 : ℝ) r).prodMk (hasDerivAt_id (0 : ℝ))
  have h := hdiff.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hpath
  exact h.deriv

/-- Continuity in `r` of the η-derivative of `meanVel1` at `0`, for `r > 0`. -/
private theorem msd_fderiv_dir_continuousAt {ν c : ℝ} (hc : 0 < c) (tr : B0140.TrainSol ν c)
    {r : ℝ} (hr : 0 < r) :
    ContinuousAt (fun x : ℝ => fderiv ℝ (fun y : ℝ × ℝ => meanVel1 tr y.1 y.2) (x, 0) (0, 1)) r := by
  have hUa : ContDiffAt ℝ ∞ (fun y : ℝ × ℝ => meanVel1 tr y.1 y.2) (r, 0) :=
    (msd_meanVel1_contDiff hc tr).contDiffAt (msd_hopen.mem_nhds ⟨Set.mem_Ioi.2 hr, mem_univ _⟩)
  have hfd : ContinuousAt (fderiv ℝ (fun y : ℝ × ℝ => meanVel1 tr y.1 y.2)) (r, 0) :=
    (hUa.fderiv_right (m := 0) (by simp)).continuousAt
  have hdir : ContinuousAt
      (fun y : ℝ × ℝ => fderiv ℝ (fun z : ℝ × ℝ => meanVel1 tr z.1 z.2) y (0, 1)) (r, 0) :=
    hfd.clm_apply continuousAt_const
  have hpath : ContinuousAt (fun x : ℝ => ((x, (0 : ℝ)) : ℝ × ℝ)) r :=
    continuousAt_id.prodMk continuousAt_const
  exact ContinuousAt.comp (f := fun x : ℝ => ((x, (0 : ℝ)) : ℝ × ℝ)) hdir hpath

/-- The integrand `F(r) = g(r,0) - ν ∂_η u(r,0)` of `MeanStreamIncrement` is continuous at `r > 0`. -/
private theorem msd_F_continuousAt {ν c : ℝ} (hc : 0 < c) (tr : B0140.TrainSol ν c)
    {r : ℝ} (hr : 0 < r) :
    ContinuousAt (fun x : ℝ => meanStress tr x 0 - ν * deriv (meanVel1 tr x) 0) r := by
  have hG : ContinuousAt (fun x : ℝ => meanStress tr x 0) r := by
    have hGa : ContinuousAt (fun y : ℝ × ℝ => meanStress tr y.1 y.2) (r, 0) :=
      ((msd_meanStress_contDiff hc tr).contDiffAt (msd_hopen.mem_nhds ⟨Set.mem_Ioi.2 hr, mem_univ _⟩)).continuousAt
    have hpath : ContinuousAt (fun x : ℝ => ((x, (0 : ℝ)) : ℝ × ℝ)) r :=
      continuousAt_id.prodMk continuousAt_const
    exact ContinuousAt.comp (f := fun x : ℝ => ((x, (0 : ℝ)) : ℝ × ℝ)) hGa hpath
  have hD : ContinuousAt (fun x : ℝ => deriv (meanVel1 tr x) 0) r :=
    (msd_fderiv_dir_continuousAt hc tr hr).congr (by
      filter_upwards [Ioi_mem_nhds hr] with x hx
      exact (msd_deriv_eq hc tr (Set.mem_Ioi.1 hx)).symm)
  exact hG.sub (hD.const_mul ν)

/-! ### `PartI:T01/2`: the age derivative of the mean stream -/

/-- **`PartI:T01/2`, `TrainMeanStreamDeriv`** (source lines 397-404): for a BUC train, `s > 0`
and every `η`, `S_s(s,η) = g(s,η) - ν ∂_η \bar v₁(s,η)`. -/
theorem trainMeanStreamDeriv : TrainMeanStreamDeriv := by
  intro ν c hν hc tr hb s hs η
  -- the integrand of `MeanStreamIncrement` is continuous on `(0,∞)`
  have hFon : ContinuousOn (fun x : ℝ => meanStress tr x 0 - ν * deriv (meanVel1 tr x) 0) (Ioi 0) :=
    fun r hr => (msd_F_continuousAt hc tr (Set.mem_Ioi.1 hr)).continuousWithinAt
  have hint : IntervalIntegrable
      (fun x : ℝ => meanStress tr x 0 - ν * deriv (meanVel1 tr x) 0) volume s s :=
    ContinuousOn.intervalIntegrable (by
      rw [uIcc_self]
      exact continuousOn_singleton _ _)
  have hmeas : StronglyMeasurableAtFilter
      (fun x : ℝ => meanStress tr x 0 - ν * deriv (meanVel1 tr x) 0) (𝓝 s) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hFon s hs
  -- derivative of `a(r) = S(r,0)` at `s`
  have hI : HasDerivAt (fun r : ℝ => ∫ x in s..r, (meanStress tr x 0 - ν * deriv (meanVel1 tr x) 0))
      (meanStress tr s 0 - ν * deriv (meanVel1 tr s) 0) s :=
    intervalIntegral.integral_hasDerivAt_right hint hmeas (msd_F_continuousAt hc tr hs)
  have hA : HasDerivAt (fun r : ℝ => meanStream tr r 0)
      (meanStress tr s 0 - ν * deriv (meanVel1 tr s) 0) s := by
    refine (hI.const_add (meanStream tr s 0)).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hs] with r hr
    have h := meanStreamIncrement ν c hν hc tr hb s r hs (Set.mem_Ioi.1 hr)
    show meanStream tr r 0 = meanStream tr s 0 +
      ∫ x in s..r, (meanStress tr x 0 - ν * deriv (meanVel1 tr x) 0)
    linarith
  -- `S(r,η) = S(r,0) - ∫_0^η u(r,t) dt` near `r = s`
  have hpt : (fun r : ℝ => meanStream tr r η) =ᶠ[𝓝 s]
      (fun r : ℝ => meanStream tr r 0 - ∫ t in (0 : ℝ)..η, meanVel1 tr r t) := by
    filter_upwards [Ioi_mem_nhds hs] with r hr
    have h := msi_stream_split tr (Set.mem_Ioi.1 hr).le η
    show meanStream tr r η = meanStream tr r 0 - ∫ t in (0 : ℝ)..η, meanVel1 tr r t
    linarith
  have hB := hA.sub (meanVelIntegralDeriv ν c hν hc tr s hs η)
  have hD : HasDerivAt (fun r : ℝ => meanStream tr r η)
      ((meanStress tr s 0 - ν * deriv (meanVel1 tr s) 0) -
        (ν * (deriv (meanVel1 tr s) η - deriv (meanVel1 tr s) 0) -
          (meanStress tr s η - meanStress tr s 0))) s :=
    hB.congr_of_eventuallyEq hpt
  rw [hD.deriv]
  have e : deriv (fun e => hmean c (fun z => tr.v s z 0) e) η = deriv (meanVel1 tr s) η := rfl
  rw [e]
  ring

end UnforcedLeray.Short.PartI
