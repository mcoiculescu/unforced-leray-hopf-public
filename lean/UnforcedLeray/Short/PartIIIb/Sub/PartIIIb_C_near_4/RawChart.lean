import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_4
import UnforcedLeray.Short.PartIIIa.Sub.T23_1_org.Bridge

/-!
# `PartIII-b:C/near/4/2`: the chart coefficient of the raw lift is measurable

Source of record: `the November 2 reference manuscript` lines 397, 2200-2201.
For the train `p.train` the raw chart coefficient equals `rawProfile` on `s > 0`
(`IIIa.chartCoeff_raw`) and vanishes on `s ≤ 0` (`(√s)⁻¹ = 0`). On the open set
`U = (0,∞) × ℝ²` the profile is continuous, because `v` is continuous there and the two
one-variable derivatives in `raisedStream` are the components of `fderiv` of the smooth stream.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Short.IIIa

/-- The chart coefficient vanishes for `s ≤ 0`. -/
theorem chartCoeff_zero_of_le_raw (R : ℝ)
    (V : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    {pt : ℝ × (ℝ × ℝ)} (h : pt.1 ≤ 0) : chartCoeff R V pt = 0 := by
  unfold chartCoeff
  rw [Real.sqrt_eq_zero'.2 h, inv_zero, zero_smul]

/-- The raised stream is the partial-derivative expression of the smooth stream. -/
theorem raisedStream_eq_fderiv (ψ : ℝ → ℝ × ℝ → ℝ) (Ψ : ℝ × (ℝ × ℝ) → ℝ)
    (hΨ : ∀ x : ℝ × (ℝ × ℝ), Ψ x = ψ x.1 x.2) {s ξ η : ℝ}
    (hd : DifferentiableAt ℝ Ψ (s, (ξ, η))) :
    UnforcedLeray.Cons.C03.raisedStream ψ s ξ η =
      Ψ (s, (ξ, η)) - (η * fderiv ℝ Ψ (s, (ξ, η)) (0, (0, 1)) +
        2 * s * fderiv ℝ Ψ (s, (ξ, η)) (1, (0, 0))) := by
  have h1 : HasDerivAt (fun t : ℝ => ((s, (ξ, t)) : ℝ × (ℝ × ℝ)))
      ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) η :=
    (hasDerivAt_const η s).prodMk ((hasDerivAt_const η ξ).prodMk (hasDerivAt_id η))
  have h2 : HasDerivAt (fun t : ℝ => ((t, (ξ, η)) : ℝ × (ℝ × ℝ)))
      ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s (ξ, η))
  have hA : HasDerivAt (fun t : ℝ => Ψ (s, (ξ, t))) (fderiv ℝ Ψ (s, (ξ, η)) (0, (0, 1))) η :=
    hd.hasFDerivAt.comp_hasDerivAt η h1
  have hB : HasDerivAt (fun t : ℝ => Ψ (t, (ξ, η))) (fderiv ℝ Ψ (s, (ξ, η)) (1, (0, 0))) s :=
    hd.hasFDerivAt.comp_hasDerivAt s h2
  have hA' : deriv (fun t => ψ s (ξ, t)) η = fderiv ℝ Ψ (s, (ξ, η)) (0, (0, 1)) := by
    rw [← hA.deriv]
    congr 1
    funext t
    exact (hΨ (s, (ξ, t))).symm
  have hB' : deriv (fun t => ψ t (ξ, η)) s = fderiv ℝ Ψ (s, (ξ, η)) (1, (0, 0)) := by
    rw [← hB.deriv]
    congr 1
    funext t
    exact (hΨ (t, (ξ, η))).symm
  unfold UnforcedLeray.Cons.C03.raisedStream
  rw [hA', hB', hΨ (s, (ξ, η))]

/-- The raw profile is continuous on `U = (0,∞) × ℝ²`. -/
theorem rawProfile_continuousOn_U (p : Params)
    (hΨ : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => p.train.ψ x.1 x.2) (Ioi 0 ×ˢ univ)) :
    ContinuousOn
      (fun pt : ℝ × (ℝ × ℝ) => UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ pt)
      (Ioi 0 ×ˢ univ) := by
  set U : Set (ℝ × (ℝ × ℝ)) := Ioi 0 ×ˢ univ with hUdef
  set Ψ : ℝ × (ℝ × ℝ) → ℝ := fun x => p.train.ψ x.1 x.2 with hΨdef
  have hU : IsOpen U := isOpen_Ioi.prod isOpen_univ
  have hdiff : ∀ x ∈ U, DifferentiableAt ℝ Ψ x := fun x hx =>
    (hΨ.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)
  have hΨc : ContinuousOn Ψ U := hΨ.continuousOn
  have hD : ContinuousOn (fun x => fderiv ℝ Ψ x) U :=
    hΨ.continuousOn_fderiv_of_isOpen hU (by simp)
  have hD1 : ContinuousOn (fun x => fderiv ℝ Ψ x (0, (0, 1))) U :=
    hD.clm_apply continuousOn_const
  have hD2 : ContinuousOn (fun x => fderiv ℝ Ψ x (1, (0, 0))) U :=
    hD.clm_apply continuousOn_const
  have e : ContinuousOn (fun x : ℝ × (ℝ × ℝ) =>
      Ψ x - (x.2.2 * fderiv ℝ Ψ x (0, (0, 1)) + 2 * x.1 * fderiv ℝ Ψ x (1, (0, 0)))) U :=
    hΨc.sub ((continuous_snd.snd.continuousOn.mul hD1).add
      ((continuous_const.mul continuous_fst).continuousOn.mul hD2))
  have hraw : ContinuousOn (fun x : ℝ × (ℝ × ℝ) =>
      UnforcedLeray.Cons.C03.raisedStream p.train.ψ x.1 x.2.1 x.2.2) U := by
    refine e.congr (fun x hx => ?_)
    exact raisedStream_eq_fderiv p.train.ψ Ψ (fun _ => rfl) (hdiff x hx)
  have hv : ContinuousOn (fun x : ℝ × (ℝ × ℝ) => p.train.v x.1 x.2) U :=
    (p.train.isTrain.smooth_v.continuousOn).mono
      (prod_mono Ioi_subset_Ici_self (subset_refl _))
  unfold UnforcedLeray.Cons.C03.rawProfile
  exact hv.add ((continuousOn_const.mul hraw).smul continuousOn_const)

/-- **`PartIII-b:C/near/4/2`: the raw chart coefficient is measurable** (source 397, 2200-2201). -/
theorem rawChartMeasurable_of : RawChartMeasurable := by
  classical
  intro p hΨ
  have hU : MeasurableSet (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    (isOpen_Ioi.prod isOpen_univ).measurableSet
  have heq : chartCoeff p.R p.raw = (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))).piecewise
      (fun pt : ℝ × (ℝ × ℝ) => UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ pt)
      (fun _ => (0 : EuclideanSpace ℝ (Fin 2))) := by
    funext pt
    by_cases h : pt ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))
    · rw [Set.piecewise_eq_of_mem _ _ _ h]
      exact chartCoeff_raw p (mem_prod.1 h).1
    · rw [Set.piecewise_eq_of_notMem _ _ _ h]
      apply chartCoeff_zero_of_le_raw
      by_contra hc
      exact h (mk_mem_prod (not_le.1 hc) (mem_univ _))
  rw [heq]
  exact ContinuousOn.measurable_piecewise (rawProfile_continuousOn_U p hΨ) continuousOn_const hU

end UnforcedLeray.Short.PartIIIb.NearInst
