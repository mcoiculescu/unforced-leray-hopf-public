import UnforcedLeray.Short.PartI.Sub.T02_5
import UnforcedLeray.Lib.Cylinder.IBP

/-!
# Part I, task `PartI:T02/5`: `MeanPrimDeriv` (the mean of the primitive has derivative `-Γ/c + w₁(0, ·)`)

Source of record: `the November 2 reference manuscript`, lines 261-288 (zero
circulation). The statement is `MeanPrimDeriv` from `Short/PartI/Sub/T02_5.lean`.

Route. `V(q, η) = slicePrim w q η = ∫₀^q w₂(s, η) ds` and `V̄(η) = c⁻¹ ∫₀^c V(q, η) dq`.
* The black box `ContDiffPrimitiveQ`, applied to `f = fun z => w z 1`, makes `V` jointly `C¹`.
* The black box `HasDerivAtEtaIntervalIntegral`, applied to `f = fun z => w z 1` on `[0, q]`,
  gives `∂_η V(q, η) = ∫₀^q ∂_η w₂(s, η) ds`. Divergence freeness gives
  `∂_η w₂ = -∂_q w₁`, and the fundamental theorem of calculus in `q` gives
  `∂_η V(q, η) = -(w₁(q, η) - w₁(0, η))`.
* The black box `HasDerivAtEtaIntervalIntegral`, applied to the `C¹` function `V` on `[0, c]`,
  differentiates `η ↦ ∫₀^c V(q, η) dq`; the integrand is `-(w₁(q, η) - w₁(0, η))`, whose integral
  is `-Γ(η) + c w₁(0, η)`. Multiplying by `c⁻¹` gives the claim.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)

/-- **Lemma `MeanPrimDeriv`**: `V̄' = -Γ/c + w₁(0, η)`. -/
theorem meanPrimDeriv (hD : HasDerivAtEtaIntervalIntegral) (hE : ContDiffPrimitiveQ) :
    MeanPrimDeriv := by
  intro c w hs η
  -- the components of `w` are smooth
  have hw0 : ContDiff ℝ ∞ (fun z : Plane => w z 0) := by
    change ContDiff ℝ ∞ ((EuclideanSpace.proj 0 : Vec →L[ℝ] ℝ) ∘ w)
    exact (EuclideanSpace.proj 0 : Vec →L[ℝ] ℝ).contDiff.comp hs.smooth
  have hw1 : ContDiff ℝ ∞ (fun z : Plane => w z 1) := by
    change ContDiff ℝ ∞ ((EuclideanSpace.proj 1 : Vec →L[ℝ] ℝ) ∘ w)
    exact (EuclideanSpace.proj 1 : Vec →L[ℝ] ℝ).contDiff.comp hs.smooth
  have hd0 : Differentiable ℝ (fun z : Plane => w z 0) := hw0.differentiable (by simp)
  have hC1 : ContDiff ℝ 1 (fun z : Plane => w z 1) := hw1.of_le (by norm_num)
  have hdq0 : ContDiff ℝ (0 + 1 : WithTop ℕ∞) (fun z : Plane => w z 0) := by
    rw [zero_add]; exact hw0.of_le (by norm_num)
  -- Step 1: `V` is jointly `C¹` (black box `ContDiffPrimitiveQ`)
  have hV : ContDiff ℝ 1 (fun z : Plane => slicePrim w z.1 z.2) :=
    hE (fun z : Plane => w z 1) hC1
  -- Step 2: `∂_η w₂ = -∂_q w₁` (divergence free)
  have hEta_eq : ∀ s : ℝ, Cyl.partialEta (fun z : Plane => w z 1) (s, η) =
      -Cyl.partialQ (fun z : Plane => w z 0) (s, η) := by
    intro s
    have h := hs.div (s, η)
    unfold Cyl.divergence at h
    linarith
  -- Step 3: FTC in `q` for `∂_q w₁`
  have hQ0 : Continuous (fun s : ℝ => Cyl.partialQ (fun z : Plane => w z 0) (s, η)) :=
    (Cyl.contDiff_partialQ (n := (0 : WithTop ℕ∞)) hdq0).continuous.comp
      (continuous_id.prodMk continuous_const : Continuous fun s : ℝ => (s, η))
  have hFTC : ∀ q : ℝ, ∫ s in (0 : ℝ)..q, Cyl.partialQ (fun z : Plane => w z 0) (s, η) =
      w (q, η) 0 - w (0, η) 0 := by
    intro q
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => Cyl.hasDerivAt_sliceQ hd0 x η) (hQ0.intervalIntegrable 0 q)
  -- Step 4: `∂_η V(q, η) = ∫₀^q ∂_η w₂ ds = -(w₁(q, η) - w₁(0, η))`
  have hI : ∀ q : ℝ, ∫ s in (0 : ℝ)..q, Cyl.partialEta (fun z : Plane => w z 1) (s, η) =
      -(w (q, η) 0 - w (0, η) 0) := by
    intro q
    simp only [hEta_eq]
    rw [intervalIntegral.integral_neg, hFTC q]
  have hPrimEta : ∀ q : ℝ,
      HasDerivAt (fun x : ℝ => slicePrim w q x) (-(w (q, η) 0 - w (0, η) 0)) η := by
    intro q
    have h := hD (fun z : Plane => w z 1) hC1 0 q η
    rw [hI q] at h
    exact h
  -- Step 5: the `η`-partial derivative of the jointly `C¹` function `V`
  have hVEta : ∀ q : ℝ, Cyl.partialEta (fun z : Plane => slicePrim w z.1 z.2) (q, η) =
      -(w (q, η) 0 - w (0, η) 0) := by
    intro q
    show deriv (fun x : ℝ => slicePrim w q x) η = -(w (q, η) 0 - w (0, η) 0)
    exact (hPrimEta q).deriv
  -- Step 6: the integrand of the `q`-mean, integrated
  have hint : ∫ q in (0 : ℝ)..c, Cyl.partialEta (fun z : Plane => slicePrim w z.1 z.2) (q, η) =
      ∫ q in (0 : ℝ)..c, -(w (q, η) 0 - w (0, η) 0) :=
    intervalIntegral.integral_congr (fun q _ => hVEta q)
  have hGc : Continuous (fun q : ℝ => w (q, η) 0) :=
    hw0.continuous.comp (continuous_id.prodMk continuous_const : Continuous fun q : ℝ => (q, η))
  have hsplit : ∫ q in (0 : ℝ)..c, (w (q, η) 0 - w (0, η) 0) =
      (∫ q in (0 : ℝ)..c, w (q, η) 0) - ∫ q in (0 : ℝ)..c, w (0, η) 0 :=
    intervalIntegral.integral_sub (hGc.intervalIntegrable 0 c)
      (continuous_const.intervalIntegrable 0 c)
  have hGamma : sliceGamma c w η = ∫ q in (0 : ℝ)..c, w (q, η) 0 := rfl
  have hint2 : ∫ q in (0 : ℝ)..c, -(w (q, η) 0 - w (0, η) 0) =
      -sliceGamma c w η + c * w (0, η) 0 := by
    rw [intervalIntegral.integral_neg, hsplit, intervalIntegral.integral_const, sub_zero,
      smul_eq_mul, hGamma]
    ring
  -- Step 7: differentiate `η ↦ ∫₀^c V(q, η) dq` (black box `HasDerivAtEtaIntervalIntegral`)
  have hbar : HasDerivAt (fun x : ℝ => ∫ q in (0 : ℝ)..c, slicePrim w q x)
      (-sliceGamma c w η + c * w (0, η) 0) η := by
    have h := hD (fun z : Plane => slicePrim w z.1 z.2) hV 0 c η
    rw [hint, hint2] at h
    exact h
  -- Step 8: multiply by `c⁻¹`
  have hc : c ≠ 0 := hs.pos.ne'
  have heq : c⁻¹ * (-sliceGamma c w η + c * w (0, η) 0) =
      -sliceGamma c w η / c + w (0, η) 0 := by
    calc c⁻¹ * (-sliceGamma c w η + c * w (0, η) 0)
        = -sliceGamma c w η / c + c⁻¹ * c * w (0, η) 0 := by ring
      _ = -sliceGamma c w η / c + w (0, η) 0 := by rw [inv_mul_cancel₀ hc, one_mul]
  have key := hbar.const_mul c⁻¹
  rw [heq] at key
  exact key

end UnforcedLeray.Short.PartI
