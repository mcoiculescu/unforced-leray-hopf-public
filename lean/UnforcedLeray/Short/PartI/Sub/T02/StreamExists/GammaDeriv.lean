import UnforcedLeray.Short.PartI.Sub.T02_5
import UnforcedLeray.Lib.Cylinder.IBP

/-!
# Part I, task `PartI:T02/5`: `GammaDeriv` (the circulation profile has derivative `-m`)

Source of record: `the November 2 reference manuscript`, lines 261-288 (zero
circulation). The statement is `GammaDeriv` from `Short/PartI/Sub/T02_5.lean`.

Route. `Γ(η) = ∫₀^c w₁(q, η) dq`. The black box `HasDerivAtEtaIntervalIntegral`, applied to
`f = fun z => w z 0`, gives `Γ'(η) = ∫₀^c ∂_η w₁(q, η) dq`. Since `curl w = ∂_q w₂ - ∂_η w₁`,
`m(η) = ∫₀^c ∂_q w₂ dq - ∫₀^c ∂_η w₁ dq`. The first integral is `w₂(c, η) - w₂(0, η) = 0` by the
fundamental theorem of calculus in `q` and periodicity. Hence `Γ'(η) = -m(η)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)

/-- **Lemma `GammaDeriv`**: `Γ' = -m`, where `m` is the `q`-integral of the vorticity. -/
theorem gammaDeriv (hD : HasDerivAtEtaIntervalIntegral) : GammaDeriv := by
  intro c w hs η
  -- the two components of `w` are smooth
  have hw0 : ContDiff ℝ ∞ (fun z : Plane => w z 0) := by
    change ContDiff ℝ ∞ ((EuclideanSpace.proj 0 : Vec →L[ℝ] ℝ) ∘ w)
    exact (EuclideanSpace.proj 0 : Vec →L[ℝ] ℝ).contDiff.comp hs.smooth
  have hw1 : ContDiff ℝ ∞ (fun z : Plane => w z 1) := by
    change ContDiff ℝ ∞ ((EuclideanSpace.proj 1 : Vec →L[ℝ] ℝ) ∘ w)
    exact (EuclideanSpace.proj 1 : Vec →L[ℝ] ℝ).contDiff.comp hs.smooth
  have hd1 : Differentiable ℝ (fun z : Plane => w z 1) := hw1.differentiable (by simp)
  have hC1 : ContDiff ℝ 1 (fun z : Plane => w z 0) := hw0.of_le (by norm_num)
  -- Step 1: differentiation under the integral sign (black box `hD`)
  have hGam : HasDerivAt (sliceGamma c w)
      (∫ q in (0 : ℝ)..c, Cyl.partialEta (fun z : Plane => w z 0) (q, η)) η :=
    hD (fun z : Plane => w z 0) hC1 0 c η
  -- Step 2: continuity of the two integrands of `curl`
  have hdq1 : ContDiff ℝ (0 + 1 : WithTop ℕ∞) (fun z : Plane => w z 1) := by
    rw [zero_add]; exact hw1.of_le (by norm_num)
  have hdE0 : ContDiff ℝ (0 + 1 : WithTop ℕ∞) (fun z : Plane => w z 0) := by
    rw [zero_add]; exact hw0.of_le (by norm_num)
  have hQ1 : Continuous (fun q : ℝ => Cyl.partialQ (fun z : Plane => w z 1) (q, η)) :=
    (Cyl.contDiff_partialQ (n := (0 : WithTop ℕ∞)) hdq1).continuous.comp
      (continuous_id.prodMk continuous_const : Continuous fun q : ℝ => (q, η))
  have hE0 : Continuous (fun q : ℝ => Cyl.partialEta (fun z : Plane => w z 0) (q, η)) :=
    (Cyl.contDiff_partialEta (n := (0 : WithTop ℕ∞)) hdE0).continuous.comp
      (continuous_id.prodMk continuous_const : Continuous fun q : ℝ => (q, η))
  -- Step 3: `∫₀^c ∂_q w₂ dq = w₂(c, η) - w₂(0, η) = 0` (FTC in `q` and periodicity)
  have hper : w (c, η) = w (0, η) := by
    simpa using hs.periodic (0, η)
  have hper1 : w (c, η) 1 = w (0, η) 1 := by
    rw [hper]
  have hA : ∫ q in (0 : ℝ)..c, Cyl.partialQ (fun z : Plane => w z 1) (q, η) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => Cyl.hasDerivAt_sliceQ hd1 x η) (hQ1.intervalIntegrable 0 c)]
    show w (c, η) 1 - w (0, η) 1 = 0
    rw [hper1, sub_self]
  -- Step 4: split the `q`-integral of the curl
  have hsc : sliceCurlMean c w η =
      (∫ q in (0 : ℝ)..c, Cyl.partialQ (fun z : Plane => w z 1) (q, η)) -
        ∫ q in (0 : ℝ)..c, Cyl.partialEta (fun z : Plane => w z 0) (q, η) := by
    unfold sliceCurlMean
    exact intervalIntegral.integral_sub (hQ1.intervalIntegrable 0 c) (hE0.intervalIntegrable 0 c)
  -- Step 5: `-m = ∫₀^c ∂_η w₁ dq`
  have hfinal : -sliceCurlMean c w η =
      ∫ q in (0 : ℝ)..c, Cyl.partialEta (fun z : Plane => w z 0) (q, η) := by
    rw [hsc, hA, zero_sub, neg_neg]
  rw [hfinal]
  exact hGam

end UnforcedLeray.Short.PartI
