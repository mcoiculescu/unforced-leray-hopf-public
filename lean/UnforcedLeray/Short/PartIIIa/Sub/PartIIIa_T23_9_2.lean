import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T23_9
import UnforcedLeray.Short.PartIIIa.Sub.T23_1_org.Bridge

/-!
# `PartIII-a:T23/9/2` (`ChartSliceMeasurable`): decomposition

Source of record: `the November 2 reference manuscript`, lines 2703-2711.

The raw half (`chartSliceRaw`) is proved.  The inlet half is `ringStreamProfile` of
`ageCutoff · frozenStream i`, where `frozenStream i` is `±2 Re/Im` of `periodicStream p.mode p.c`
(`p.mode` an arbitrary planar profile, nothing in `BgRegime` constrains it).  Measurability of
`periodicStream` for every `f : ℝ → ℂ` rests on two general measure-theory leaves:

* `GreenInverseMeasurable` : `r ↦ greenInverse f r` is Borel for *every* `f : ℝ → ℂ` (the interval
  integrals are Lebesgue integrals, equal to `0` when not integrable);
* `ZTsumMeasurable` : the `ℤ`-indexed `tsum` of measurable `ℂ`-valued functions is measurable
  (the summable set is measurable; on it the sum is the limit of the partial sums, off it `0`).

`chartSliceMeasurable_of` assembles the target from them.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa.T23_9_Sub

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Cons.C03 UnforcedLeray.Short.IIb

/-- **Leaf `T23/9/2/1`**: `r ↦ greenInverse f r` is measurable for every profile `f`. -/
def GreenInverseMeasurable : Prop :=
  ∀ f : UnforcedLeray.Blueprint.Planar.Profile, Measurable (UnforcedLeray.Blueprint.Planar.greenInverse f)

/-- **Leaf `T23/9/2/2`**: a `ℤ`-indexed `tsum` of measurable complex functions on the plane is
measurable (no summability assumption: off the measurable summable set the `tsum` is `0`). -/
def ZTsumMeasurable : Prop :=
  ∀ F : ℤ → ℝ × ℝ → ℂ, (∀ k, Measurable (F k)) → Measurable (fun x => ∑' k : ℤ, F k x)

/-- Raw-lift half of `ChartSliceMeasurable`: for `s > 0` the chart coefficient of the raw lift is
Borel measurable in `(ξ, η)`. -/
theorem chartSliceRaw (p : Params) (d dm dp : ℝ) (hreg : BgRegime p d dm dp)
    (s : ℝ) (hs : 0 < s) :
    Measurable (fun x : ℝ × ℝ => chartCoeff p.R p.raw (s, x)) := by
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hΨs : ContDiffOn ℝ ∞ (fun y : ℝ × (ℝ × ℝ) => p.train.ψ y.1 y.2) (Ioi 0 ×ˢ univ) :=
    hreg.train_stream_smooth
  have hdiff : ∀ y : ℝ × (ℝ × ℝ), 0 < y.1 →
      DifferentiableAt ℝ (fun y : ℝ × (ℝ × ℝ) => p.train.ψ y.1 y.2) y := by
    intro y hy
    have hmem : y ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) := ⟨mem_Ioi.2 hy, mem_univ _⟩
    exact (hΨs.contDiffAt (hU.mem_nhds hmem)).differentiableAt (by simp)
  have hcont : Continuous (fun x : ℝ × ℝ => p.train.ψ s x) := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    have h1 := (hdiff (s, x) hs).continuousAt
    exact h1.comp (f := fun x : ℝ × ℝ => (s, x)) (continuous_const.prodMk continuous_id).continuousAt
  have hvc : ContinuousOn (fun y : ℝ × (ℝ × ℝ) => p.train.v y.1 y.2) (Ici 0 ×ˢ univ) :=
    p.train.isTrain.smooth_v.continuousOn
  have hvcont : Continuous (fun x : ℝ × ℝ => p.train.v s x) :=
    hvc.comp_continuous (continuous_const.prodMk continuous_id)
      (fun x => (⟨le_of_lt hs, mem_univ _⟩ : (s, x) ∈ Ici (0 : ℝ) ×ˢ univ))
  -- partial derivatives of the stream as fderivs
  have hη : ∀ x : ℝ × ℝ, deriv (fun t : ℝ => p.train.ψ s (x.1, t)) x.2 =
      fderiv ℝ (fun y : ℝ × (ℝ × ℝ) => p.train.ψ y.1 y.2) (s, x) (0, (0, 1)) := by
    intro x
    have hd : HasDerivAt (fun t : ℝ => ((s, (x.1, t)) : ℝ × (ℝ × ℝ)))
        ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) x.2 :=
      (hasDerivAt_const x.2 s).prodMk ((hasDerivAt_const x.2 x.1).prodMk (hasDerivAt_id' x.2))
    have hF := (hdiff (s, x) hs).hasFDerivAt
    exact (hF.comp_hasDerivAt x.2 hd).deriv
  have hs' : ∀ x : ℝ × ℝ, deriv (fun t : ℝ => p.train.ψ t (x.1, x.2)) s =
      fderiv ℝ (fun y : ℝ × (ℝ × ℝ) => p.train.ψ y.1 y.2) (s, x) (1, (0, 0)) := by
    intro x
    have hd : HasDerivAt (fun t : ℝ => ((t, x) : ℝ × (ℝ × ℝ)))
        ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) s :=
      (hasDerivAt_id' s).prodMk (hasDerivAt_const s x)
    have hF := (hdiff (s, x) hs).hasFDerivAt
    exact (hF.comp_hasDerivAt s hd).deriv
  have hEta : Measurable fun x : ℝ × ℝ =>
      fderiv ℝ (fun y : ℝ × (ℝ × ℝ) => p.train.ψ y.1 y.2) (s, x) (0, (0, 1)) :=
    (measurable_fderiv_apply_const ℝ (fun y : ℝ × (ℝ × ℝ) => p.train.ψ y.1 y.2)
      ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))).comp (measurable_const.prodMk measurable_id)
  have hSt : Measurable fun x : ℝ × ℝ =>
      fderiv ℝ (fun y : ℝ × (ℝ × ℝ) => p.train.ψ y.1 y.2) (s, x) (1, (0, 0)) :=
    (measurable_fderiv_apply_const ℝ (fun y : ℝ × (ℝ × ℝ) => p.train.ψ y.1 y.2)
      ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))).comp (measurable_const.prodMk measurable_id)
  have hRS : Measurable fun x : ℝ × ℝ => raisedStream p.train.ψ s x.1 x.2 := by
    have e : (fun x : ℝ × ℝ => raisedStream p.train.ψ s x.1 x.2) = fun x : ℝ × ℝ =>
        p.train.ψ s x - (x.2 *
          fderiv ℝ (fun y : ℝ × (ℝ × ℝ) => p.train.ψ y.1 y.2) (s, x) (0, (0, 1)) +
          2 * s * fderiv ℝ (fun y : ℝ × (ℝ × ℝ) => p.train.ψ y.1 y.2) (s, x) (1, (0, 0))) := by
      funext x
      unfold raisedStream
      rw [hη x, hs' x]
    rw [e]
    exact hcont.measurable.sub ((measurable_snd.mul hEta).add (hSt.const_mul (2 * s)))
  have hRaw : Measurable fun x : ℝ × ℝ => p.train.v s x +
      (p.ε * raisedStream p.train.ψ s x.1 x.2) • (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) :=
    hvcont.measurable.add ((hRS.const_mul p.ε).smul_const _)
  have e2 : (fun x : ℝ × ℝ => chartCoeff p.R p.raw (s, x)) =
      fun x : ℝ × ℝ => rawProfile p.ε p.train.v p.train.ψ (s, x) := by
    funext x
    exact chartCoeff_raw p (pt := (s, x)) hs
  rw [e2]
  exact hRaw


theorem measurable_periodicStream (h1 : GreenInverseMeasurable) (h2 : ZTsumMeasurable)
    (f : UnforcedLeray.Blueprint.Planar.Profile) (c : ℝ) :
    Measurable (fun x : ℝ × ℝ => UnforcedLeray.Blueprint.periodicStream f c x) := by
  unfold UnforcedLeray.Blueprint.periodicStream
  refine h2 _ (fun k => ?_)
  unfold UnforcedLeray.Blueprint.planarStream UnforcedLeray.Blueprint.angularTwo
  have hg := h1 f
  have hsh : Measurable (fun x : ℝ × ℝ => ((x.1 + k * c, x.2) : ℝ × ℝ)) := by fun_prop
  have hn : Measurable (fun y : ℝ × ℝ => Real.sqrt (y.1 ^ 2 + y.2 ^ 2)) := by fun_prop
  have hA : Measurable (fun y : ℝ × ℝ =>
      ((y.1 : ℂ) + (y.2 : ℂ) * Complex.I) ^ 2 / ((y.1 ^ 2 + y.2 ^ 2 : ℝ) : ℂ)) := by fun_prop
  exact ((hg.comp hn).mul hA).comp hsh

theorem chartSliceMeasurable_of (h1 : GreenInverseMeasurable) (h2 : ZTsumMeasurable)
    (p : Params) (d dm dp : ℝ) (hreg : BgRegime p d dm dp) (s : ℝ) (hs : 0 < s) :
    Measurable (fun x : ℝ × ℝ => chartCoeff p.R p.raw (s, x)) ∧
    ∀ i : Fin 2, Measurable (fun x : ℝ × ℝ => chartCoeff p.R (p.inlet i) (s, x)) := by
  refine ⟨chartSliceRaw p d dm dp hreg s hs, fun i => ?_⟩
  have hP := measurable_periodicStream h1 h2 p.mode p.c
  have hF : Measurable (p.frozenStream i) := by
    fin_cases i
    · exact (Complex.measurable_re.comp hP).const_mul 2
    · exact (Complex.measurable_im.comp hP).const_mul (-2)
  have hC : Measurable (p.cutStream i) :=
    ((contDiff_ageCutoff p.H (n := 0)).continuous.measurable.comp measurable_fst).mul
      (hF.comp measurable_snd)
  have e : (fun x : ℝ × ℝ => chartCoeff p.R (p.inlet i) (s, x)) =
      fun x : ℝ × ℝ => p.inletProfile i (s, x) := by
    funext x
    exact chartCoeff_Nv p.R_pos _ hs
  rw [e]
  have hs0 : Measurable (fun x : ℝ × ℝ => ((s, x) : ℝ × (ℝ × ℝ))) :=
    measurable_const.prodMk measurable_id
  have hdE : Measurable (fun m : ℝ × (ℝ × ℝ) => dEta (p.cutStream i) m) :=
    measurable_fderiv_apply_const ℝ (p.cutStream i) _
  have hdQ : Measurable (fun m : ℝ × (ℝ × ℝ) => dQ (p.cutStream i) m) :=
    measurable_fderiv_apply_const ℝ (p.cutStream i) _
  have hdS : Measurable (fun m : ℝ × (ℝ × ℝ) => dS (p.cutStream i) m) :=
    measurable_fderiv_apply_const ℝ (p.cutStream i) _
  have hm : Measurable (fun m : ℝ × (ℝ × ℝ) => p.inletProfile i m) := by
    unfold Params.inletProfile ringStreamProfile
    refine (hdE.neg.smul_const _).add ?_
    refine (hdQ.add (measurable_const.mul ?_)).smul_const _
    exact (hC.sub ((measurable_const.mul measurable_fst).mul hdS)).sub (measurable_snd.snd.mul hdE)
  exact hm.comp hs0

end UnforcedLeray.Short.IIIa.T23_9_Sub
