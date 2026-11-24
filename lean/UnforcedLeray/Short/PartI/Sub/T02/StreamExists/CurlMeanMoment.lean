import UnforcedLeray.Short.PartI.Sub.T02_5
import UnforcedLeray.Lib.Cylinder.IBP

/-!
# Part I, task `PartI:T02/5`: `CurlMeanMoment` (the vorticity mean has finite first moment)

Source of record: `the November 2 reference manuscript`, lines 261-288 (zero
integral vorticity in `L¹` with first moment). The statement is `CurlMeanMoment` from
`Short/PartI/Sub/T02_5.lean`.

Route. For a fixed slice `w` and every `t`, `|m(t)| ≤ ∫₀^c |curl w(q, t)| dq`, where
`m(t) = ∫₀^c curl w(q, t) dq`. The integrand is `c`-periodic in `q`, so this integral equals the
integral over the centred interval `[-c/2, c/2)`. Fubini on the cell (`Cyl.volume_restrict_cell`)
and `Integrable.integral_prod_right` turn the moment `∫_cell (1 + |η|) |curl w| < ∞` into
integrability of `η ↦ (1 + |η|) ∫_{[-c/2,c/2)} |curl w(q, η)| dq`. The function `t ↦ (1 + |t|) m(t)`
is continuous, hence measurable, and it is dominated by that integrable function.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)

/-- **Lemma `CurlMeanMoment`**: `∫_ℝ (1 + |t|) |m(t)| dt < ∞`. -/
theorem curlMeanMoment : CurlMeanMoment := by
  intro c w hs
  have hc : 0 < c := hs.pos
  -- periodicity of the vorticity in `q`
  have hP1 : Cyl.IsPeriodic c (fun u : Plane => w u 1) := fun z => by
    show w (z.1 + c, z.2) 1 = w z 1
    rw [hs.periodic z]
  have hP0 : Cyl.IsPeriodic c (fun u : Plane => w u 0) := fun z => by
    show w (z.1 + c, z.2) 0 = w z 0
    rw [hs.periodic z]
  have hcurlP : Cyl.IsPeriodic c (Cyl.curl w) := fun z => by
    show Cyl.partialQ (fun u => w u 1) (z.1 + c, z.2)
        - Cyl.partialEta (fun u => w u 0) (z.1 + c, z.2)
      = Cyl.partialQ (fun u => w u 1) z - Cyl.partialEta (fun u => w u 0) z
    rw [hP1.partialQ z, hP0.partialEta z]
  -- continuity of the vorticity
  have hC1 : ContDiff ℝ 1 (fun u : Plane => w u 1) :=
    ((EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp
      hs.smooth).of_le (by simp)
  have hC0 : ContDiff ℝ 1 (fun u : Plane => w u 0) :=
    ((EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp
      hs.smooth).of_le (by simp)
  have hcurlC : Continuous (Cyl.curl w) :=
    (Cyl.C1_partial_of_contDiff hC1).1.sub (Cyl.C1_partial_of_contDiff hC0).2
  have hunc : Continuous (fun p : ℝ × ℝ => Cyl.curl w (p.2, p.1)) :=
    hcurlC.comp (continuous_snd.prodMk continuous_fst)
  -- continuity of `m(t) = ∫₀^c curl w(q, t) dq`
  have hmcont : Continuous (fun t : ℝ => sliceCurlMean c w t) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun t q : ℝ => Cyl.curl w (q, t)) hunc 0 c
  -- `|m(t)| ≤ ∫ |curl w(·, t)|` over the centred cell interval
  have hA : ∀ t : ℝ,
      |sliceCurlMean c w t| ≤ ∫ q in Ico (-c / 2) (c / 2), |Cyl.curl w (q, t)| := by
    intro t
    have hper : Function.Periodic (fun q : ℝ => |Cyl.curl w (q, t)|) c := fun q => by
      show |Cyl.curl w (q + c, t)| = |Cyl.curl w (q, t)|
      have h : Cyl.curl w (q + c, t) = Cyl.curl w (q, t) := hcurlP (q, t)
      rw [h]
    have h1 : |sliceCurlMean c w t| ≤ ∫ q in (0 : ℝ)..c, |Cyl.curl w (q, t)| := by
      have h : ‖∫ q in (0 : ℝ)..c, Cyl.curl w (q, t)‖
          ≤ ∫ q in (0 : ℝ)..c, ‖Cyl.curl w (q, t)‖ :=
        intervalIntegral.norm_integral_le_integral_norm hc.le
      simp only [Real.norm_eq_abs] at h
      exact h
    have h2 : ∫ q in (0 : ℝ)..c, |Cyl.curl w (q, t)|
        = ∫ q in (-c / 2)..(c / 2), |Cyl.curl w (q, t)| := by
      have h := hper.intervalIntegral_add_eq (-c / 2) 0
      rw [zero_add, show -c / 2 + c = c / 2 by ring] at h
      exact h.symm
    have h3 : ∫ q in (-c / 2)..(c / 2), |Cyl.curl w (q, t)|
        = ∫ q in Ico (-c / 2) (c / 2), |Cyl.curl w (q, t)| := by
      rw [intervalIntegral.integral_of_le (show -c / 2 ≤ c / 2 by linarith)]
      exact integral_Ico_eq_integral_Ioc.symm
    rw [h2, h3] at h1
    exact h1
  -- Fubini on the cell: `η ↦ ∫_{[-c/2,c/2)} (1 + |η|) |curl w(q, η)| dq` is integrable
  have hprod : Integrable (fun z : Plane => (1 + |z.2|) * |Cyl.curl w z|)
      (((volume : Measure ℝ).restrict (Ico (-c / 2) (c / 2))).prod (volume : Measure ℝ)) := by
    rw [← Cyl.volume_restrict_cell c]
    exact hs.moment
  have hH := hprod.integral_prod_right
  have hH' : Integrable
      (fun η : ℝ => (1 + |η|) * ∫ q in Ico (-c / 2) (c / 2), |Cyl.curl w (q, η)|) := by
    refine hH.congr (ae_of_all _ fun η => ?_)
    show ∫ x in Ico (-c / 2) (c / 2), (1 + |η|) * |Cyl.curl w (x, η)|
      = (1 + |η|) * ∫ q in Ico (-c / 2) (c / 2), |Cyl.curl w (q, η)|
    rw [integral_const_mul]
  -- domination of `(1 + |t|) |m(t)|`
  have hcont : Continuous (fun t : ℝ => (1 + |t|) * |sliceCurlMean c w t|) := by
    have h1 : Continuous (fun t : ℝ => |sliceCurlMean c w t|) := continuous_abs.comp hmcont
    exact (continuous_const.add continuous_abs).mul h1
  refine Integrable.mono' hH' hcont.aestronglyMeasurable (ae_of_all _ fun t => ?_)
  show ‖(1 + |t|) * |sliceCurlMean c w t|‖
    ≤ (1 + |t|) * ∫ q in Ico (-c / 2) (c / 2), |Cyl.curl w (q, t)|
  rw [Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (hA t) (by positivity)

end UnforcedLeray.Short.PartI
