import UnforcedLeray.Short.PartI.Sub.T01Class
import UnforcedLeray.Short.PartI.Tasks.TrainClass.MeanStreamDecay
import UnforcedLeray.Short.PartI.Tasks.TrainClass.BUCMeanVelDecay
import UnforcedLeray.Short.PartI.Tasks.TrainClass.BUCMeanStressDecay
import UnforcedLeray.Short.PartI.Tasks.TrainClass.MeanVelIntegralDeriv
import UnforcedLeray.Short.PartI.Tasks.TrainClass.MeanStreamIncrement.Helpers

/-!
# Part I, task `PartI:TC/6`: increment of the mean stream at the origin

Source of record: `the November 2 reference manuscript`, lines 397-404.
The Prop `MeanStreamIncrement` is defined in `Short/PartI/Sub/T01Class.lean`.

Route, for `s₁, s₂ > 0`:
* `msi_stream_split`: `S(s,0) = S(s,R) + ∫₀^R u(s,t) dt` for every `R`;
* `meanVelIntegralDeriv`: `r ↦ ∫₀^R u(r,t) dt` has derivative `D R r` at `r > 0`; the FTC on
  `[s₁,s₂]` gives `∫_{s₁}^{s₂} D R = I(s₂,R) - I(s₁,R)`, so
  `S(s₂,0) - S(s₁,0) = ∫_{s₁}^{s₂} D R + (S(s₂,R) - S(s₁,R))` for every `R`;
* as `R → ∞`, `S(·,R) → 0` (`meanStreamDecay`), `D R r → g(r,0) - ν ∂_η u(r,0)` pointwise
  (`bucMeanVelDecay`, `bucMeanStressDecay`) and `|D R r| ≤ ν·2M₁ + 2M₀²` (dominated convergence).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-- **`PartI:TC/6`. Increment of the mean stream at the origin** (BUC train; lines 397-404). -/
theorem meanStreamIncrement : MeanStreamIncrement := by
  intro ν c hν hc tr hb s₁ s₂ hs₁ hs₂
  -- positivity and the common upper age `max s₁ s₂`
  have hpos : ∀ r ∈ uIcc s₁ s₂, 0 < r ∧ r ≤ max s₁ s₂ := by
    intro r hr
    rcases Set.mem_uIcc.1 hr with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by linarith, le_trans h2 (le_max_right _ _)⟩
    · exact ⟨by linarith, le_trans h2 (le_max_left _ _)⟩
  have hS0 : 0 ≤ max s₁ s₂ := le_trans hs₁.le (le_max_left _ _)
  obtain ⟨M0, hM0⟩ := hb.sup_bound hS0
  obtain ⟨M1, hM1⟩ := hb.deriv_bound hS0 1
  -- the uniform bound on the integrand `D R r`
  set Bd : ℝ := ν * (2 * M1) + 2 * (M0 * M0) with hBd
  have hDbd : ∀ R : ℝ, ∀ r ∈ uIcc s₁ s₂,
      |ν * (deriv (meanVel1 tr r) R - deriv (meanVel1 tr r) 0) -
        (meanStress tr r R - meanStress tr r 0)| ≤ Bd := by
    intro R r hr
    obtain ⟨hr0, hrS⟩ := hpos r hr
    have hM1r : ∀ z : Plane, ‖iteratedFDeriv ℝ 1 (tr.v r) z‖ ≤ M1 :=
      fun z => hM1 r ⟨hr0.le, hrS⟩ z
    have hM0r : ∀ z : Plane, ‖tr.v r z‖ ≤ M0 := fun z => hM0 r ⟨hr0.le, hrS⟩ z
    have hu1 := msi_deriv_meanVel1_bound hc tr hr0.le hM1r R
    have hu0 := msi_deriv_meanVel1_bound hc tr hr0.le hM1r 0
    have hg1 := msi_meanStress_bound hc tr hM0r R
    have hg0 := msi_meanStress_bound hc tr hM0r 0
    have hX : |deriv (meanVel1 tr r) R - deriv (meanVel1 tr r) 0| ≤ 2 * M1 := by
      have h1 := abs_le.1 hu1
      have h2 := abs_le.1 hu0
      rw [abs_le]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    have hY : |meanStress tr r R - meanStress tr r 0| ≤ 2 * (M0 * M0) := by
      have h1 := abs_le.1 hg1
      have h2 := abs_le.1 hg0
      rw [abs_le]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    have hX' := abs_le.1 hX
    have hY' := abs_le.1 hY
    have hνX1 : ν * (-(2 * M1)) ≤ ν * (deriv (meanVel1 tr r) R - deriv (meanVel1 tr r) 0) :=
      mul_le_mul_of_nonneg_left hX'.1 hν.le
    have hνX2 : ν * (deriv (meanVel1 tr r) R - deriv (meanVel1 tr r) 0) ≤ ν * (2 * M1) :=
      mul_le_mul_of_nonneg_left hX'.2 hν.le
    rw [abs_le, hBd]
    constructor <;> linarith [hY'.1, hY'.2]
  -- the derivative of `r ↦ ∫₀^R u(r,t) dt`
  have hDeriv : ∀ R : ℝ, ∀ r ∈ uIcc s₁ s₂, HasDerivAt
      (fun x : ℝ => ∫ t in (0 : ℝ)..R, meanVel1 tr x t)
      (ν * (deriv (meanVel1 tr r) R - deriv (meanVel1 tr r) 0) -
        (meanStress tr r R - meanStress tr r 0)) r := by
    intro R r hr
    exact meanVelIntegralDeriv ν c hν hc tr r (hpos r hr).1 R
  -- the derivative as a function of `r`
  have hGeq : ∀ R : ℝ, ∀ r ∈ uIcc s₁ s₂,
      deriv (fun x : ℝ => ∫ t in (0 : ℝ)..R, meanVel1 tr x t) r =
        ν * (deriv (meanVel1 tr r) R - deriv (meanVel1 tr r) 0) -
          (meanStress tr r R - meanStress tr r 0) :=
    fun R r hr => (hDeriv R r hr).deriv
  -- fundamental theorem of calculus in `r` on `[s₁, s₂]`
  have hFTC : ∀ R : ℝ, (∫ r in s₁..s₂,
      deriv (fun x : ℝ => ∫ t in (0 : ℝ)..R, meanVel1 tr x t) r) =
        (∫ t in (0 : ℝ)..R, meanVel1 tr s₂ t) - (∫ t in (0 : ℝ)..R, meanVel1 tr s₁ t) := by
    intro R
    have hint : IntervalIntegrable
        (fun r => deriv (fun x : ℝ => ∫ t in (0 : ℝ)..R, meanVel1 tr x t) r) volume s₁ s₂ := by
      rw [intervalIntegrable_iff]
      refine Measure.integrableOn_of_bounded (M := Bd) ?_
        (measurable_deriv (fun x : ℝ => ∫ t in (0 : ℝ)..R, meanVel1 tr x t)).aestronglyMeasurable
        ?_
      · rw [Set.uIoc, Real.volume_Ioc]
        exact ENNReal.ofReal_ne_top
      · refine (ae_restrict_mem measurableSet_uIoc).mono fun x hx => ?_
        rw [Real.norm_eq_abs, hGeq R x (Set.uIoc_subset_uIcc hx)]
        exact hDbd R x (Set.uIoc_subset_uIcc hx)
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => (hDeriv R x hx).congr_deriv (hGeq R x hx).symm) hint
  -- pointwise limit of the integrand as `R → ∞`
  have hlimD : ∀ r : ℝ, 0 < r → Tendsto
      (fun R : ℝ => ν * (deriv (meanVel1 tr r) R - deriv (meanVel1 tr r) 0) -
        (meanStress tr r R - meanStress tr r 0)) atTop
      (𝓝 (meanStress tr r 0 - ν * deriv (meanVel1 tr r) 0)) := by
    intro r hr
    have h1 := (bucMeanVelDecay ν c hν hc tr hb r hr.le).2
    have h2 := bucMeanStressDecay ν c hν hc tr hb r hr.le
    have h := ((h1.sub_const (deriv (meanVel1 tr r) 0)).const_mul ν).sub
      (h2.sub_const (meanStress tr r 0))
    have e : ν * (0 - deriv (meanVel1 tr r) 0) - (0 - meanStress tr r 0) =
        meanStress tr r 0 - ν * deriv (meanVel1 tr r) 0 := by ring
    rw [e] at h
    exact h
  -- dominated convergence on `[s₁, s₂]` as `R → ∞`
  have hDCT : Tendsto (fun R : ℝ => ∫ r in s₁..s₂,
      deriv (fun x : ℝ => ∫ t in (0 : ℝ)..R, meanVel1 tr x t) r) atTop
      (𝓝 (∫ r in s₁..s₂, (meanStress tr r 0 - ν * deriv (meanVel1 tr r) 0))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => Bd)
      (Filter.Eventually.of_forall fun R => ?_) (Filter.Eventually.of_forall fun R => ?_)
      intervalIntegrable_const (ae_of_all _ fun x hx => ?_)
    · exact (measurable_deriv (fun x : ℝ => ∫ t in (0 : ℝ)..R, meanVel1 tr x t)).aestronglyMeasurable
    · refine ae_of_all _ fun x hx => ?_
      rw [Real.norm_eq_abs, hGeq R x (Set.uIoc_subset_uIcc hx)]
      exact hDbd R x (Set.uIoc_subset_uIcc hx)
    · have hxI : x ∈ uIcc s₁ s₂ := Set.uIoc_subset_uIcc hx
      have hx0 : 0 < x := (hpos x hxI).1
      have h := hlimD x hx0
      exact Tendsto.congr (fun R => (hGeq R x hxI).symm) h
  -- assembling: the increment equals the limit of a constant family
  have hconst : ∀ R : ℝ, (∫ r in s₁..s₂,
      deriv (fun x : ℝ => ∫ t in (0 : ℝ)..R, meanVel1 tr x t) r) +
        (meanStream tr s₂ R - meanStream tr s₁ R) =
        meanStream tr s₂ 0 - meanStream tr s₁ 0 := by
    intro R
    rw [hFTC R]
    have e2 := msi_stream_split tr hs₂.le R
    have e1 := msi_stream_split tr hs₁.le R
    linarith
  have hlim2 : Tendsto (fun R : ℝ => (∫ r in s₁..s₂,
      deriv (fun x : ℝ => ∫ t in (0 : ℝ)..R, meanVel1 tr x t) r) +
        (meanStream tr s₂ R - meanStream tr s₁ R)) atTop
      (𝓝 ((∫ r in s₁..s₂, (meanStress tr r 0 - ν * deriv (meanVel1 tr r) 0)) + (0 - 0))) :=
    hDCT.add ((meanStreamDecay ν c hν hc tr s₂ hs₂.le).sub
      (meanStreamDecay ν c hν hc tr s₁ hs₁.le))
  have h3 : Tendsto (fun _ : ℝ => meanStream tr s₂ 0 - meanStream tr s₁ 0) atTop
      (𝓝 ((∫ r in s₁..s₂, (meanStress tr r 0 - ν * deriv (meanVel1 tr r) 0)) + (0 - 0))) :=
    Tendsto.congr hconst hlim2
  have key := tendsto_nhds_unique tendsto_const_nhds h3
  linarith

end UnforcedLeray.Short.PartI
