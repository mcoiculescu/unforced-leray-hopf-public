import UnforcedLeray.Short.PartI.Sub.T02_5

/-!
# Part I, task `PartI:T02/5`: `PsiGradient` (the candidate stream has gradient `w`)

Source of record: `the November 2 reference manuscript`, lines 261-288.

Target: `psiGradient` proves the leaf `PsiGradient` (`Short/PartI/Sub/T02_5.lean`) from the three
black boxes `HasDerivAtEtaIntervalIntegral`, `ContDiffPrimitiveQ` and `MeanPrimDeriv`.

For a slice `w` and `g` with `g' = -Γ/c`, put `ψ = V - V̄ + g` (`slicePsi c w g`), where
`V(q, η) = ∫₀^q w₂(s, η) ds`. Then

* `∂_q ψ = w₂`, by the fundamental theorem of calculus in `q`; the other two terms do not depend
  on `q`;
* `∂_η V(q, η) = -(w₁(q, η) - w₁(0, η))`, from `div w = 0` (so `∂_η w₂ = -∂_q w₁`) and the
  fundamental theorem of calculus in `s` along `[0, q]`;
* hence `∂_η ψ = -(w₁(q, η) - w₁(0, η)) - (-Γ/c + w₁(0, η)) + (-Γ/c) = -w₁(q, η)`, using
  `V̄' = -Γ/c + w₁(0, η)` (`MeanPrimDeriv`) and `g' = -Γ/c`;
* so `perpendicularGradient ψ z = (w₁ z, w₂ z)` and `w z = toVec (perpendicularGradient ψ z)`
  (`Train.eq_toVec`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.GaussianVortex (perpendicularGradient)
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)

/-- **`PartI:T02/5`, leaf `PsiGradient`** (source lines 261-288): for every `g` with `g' = -Γ/c`, the
candidate stream `ψ = V - V̄ + g` is differentiable and its perpendicular gradient is the slice `w`. -/
theorem psiGradient (hD : HasDerivAtEtaIntervalIntegral) (hE : ContDiffPrimitiveQ)
    (h11 : MeanPrimDeriv) : PsiGradient := by
  unfold PsiGradient
  intro c w hs g hg
  -- regularity of the components of `w`, and of the paths `q ↦ (q, η)`
  have hw1 : ContDiff ℝ 1 w := hs.smooth.of_le (by simp)
  have hw0 : ContDiff ℝ 1 (fun p : Plane => w p 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hw1
  have hw2 : ContDiff ℝ 1 (fun p : Plane => w p 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hw1
  have hpath : ∀ η : ℝ, ContDiff ℝ 1 (fun t : ℝ => ((t, η) : Plane)) := fun η =>
    contDiff_id.prodMk contDiff_const
  have hcont : ∀ η : ℝ, Continuous (fun s : ℝ => w (s, η) 1) := fun η =>
    hw2.continuous.comp (hpath η).continuous
  have hc0 : ∀ η : ℝ, ContDiff ℝ 1 (fun t : ℝ => w (t, η) 0) := fun η =>
    hw0.comp (hpath η)
  -- the primitive `V(q, η) = ∫₀^q w₂(s, η) ds` is `C¹` (hE)
  have hV : ContDiff ℝ 1 (fun z : Plane => slicePrim w z.1 z.2) :=
    hE (fun p : Plane => w p 1) hw2
  -- `V̄` (from `MeanPrimDeriv`) and `g` are differentiable in `η`
  have hVbar : ∀ η : ℝ, HasDerivAt (sliceMeanPrim c w) (-sliceGamma c w η / c + w (0, η) 0) η :=
    fun η => h11 c w hs η
  have hVbarD : Differentiable ℝ (sliceMeanPrim c w) := fun η => (hVbar η).differentiableAt
  have hgD : Differentiable ℝ g := fun η => (hg η).differentiableAt
  -- (a) differentiability of `ψ = V - V̄ + g`
  have hDiff : Differentiable ℝ (slicePsi c w g) := by
    have h1 : Differentiable ℝ (fun z : Plane => slicePrim w z.1 z.2) :=
      hV.differentiable (by norm_num)
    have h2 : Differentiable ℝ (fun z : Plane => sliceMeanPrim c w z.2) :=
      hVbarD.comp differentiable_snd
    have h3 : Differentiable ℝ (fun z : Plane => g z.2) := hgD.comp differentiable_snd
    show Differentiable ℝ (fun z : Plane => slicePrim w z.1 z.2 - sliceMeanPrim c w z.2 + g z.2)
    exact (h1.sub h2).add h3
  -- (b) `∂_q ψ = w₂`: the fundamental theorem of calculus in `q`
  have hX : ∀ q η : ℝ, GaussianVortex.partialX (slicePsi c w g) (q, η) = w (q, η) 1 := by
    intro q η
    have hI : HasDerivAt (fun x : ℝ => ∫ s in (0 : ℝ)..x, w (s, η) 1) (w (q, η) 1) q :=
      ((hcont η).integral_hasStrictDerivAt 0 q).hasDerivAt
    have hψ : HasDerivAt (fun x : ℝ => slicePsi c w g (x, η)) (w (q, η) 1) q :=
      (hI.sub_const (sliceMeanPrim c w η)).add_const (g η)
    unfold GaussianVortex.partialX
    exact hψ.deriv
  -- (c) `∂_η V = -(w₁(q, η) - w₁(0, η))`, from `div w = 0`
  have hdivEta : ∀ s η : ℝ, Cyl.partialEta (fun p : Plane => w p 1) (s, η) =
      -deriv (fun t : ℝ => w (t, η) 0) s := by
    intro s η
    have h : Cyl.partialQ (fun p : Plane => w p 0) (s, η) +
        Cyl.partialEta (fun p : Plane => w p 1) (s, η) = 0 := hs.div (s, η)
    have h' : Cyl.partialQ (fun p : Plane => w p 0) (s, η) =
        deriv (fun t : ℝ => w (t, η) 0) s := rfl
    linarith
  have hIntEta : ∀ q η : ℝ, (∫ s in (0 : ℝ)..q, Cyl.partialEta (fun p : Plane => w p 1) (s, η)) =
      -(w (q, η) 0 - w (0, η) 0) := by
    intro q η
    have hdiff : ∀ x ∈ uIcc (0 : ℝ) q, DifferentiableAt ℝ (fun t : ℝ => w (t, η) 0) x :=
      fun x _ => (hc0 η).differentiable (by norm_num) x
    have hint : IntervalIntegrable (deriv (fun t : ℝ => w (t, η) 0)) volume 0 q :=
      ((hc0 η).continuous_deriv (by norm_num)).intervalIntegrable 0 q
    have hFTC : ∫ s in (0 : ℝ)..q, deriv (fun t : ℝ => w (t, η) 0) s =
        w (q, η) 0 - w (0, η) 0 :=
      intervalIntegral.integral_deriv_eq_sub hdiff hint
    have hcongr : (∫ s in (0 : ℝ)..q, Cyl.partialEta (fun p : Plane => w p 1) (s, η)) =
        ∫ s in (0 : ℝ)..q, -deriv (fun t : ℝ => w (t, η) 0) s :=
      intervalIntegral.integral_congr (fun s _ => hdivEta s η)
    rw [hcongr, intervalIntegral.integral_neg, hFTC]
  -- (c) `∂_η ψ = -w₁`, using `V̄' = -Γ/c + w₁(0, η)` and `g' = -Γ/c`
  have hY : ∀ q η : ℝ, GaussianVortex.partialY (slicePsi c w g) (q, η) = -w (q, η) 0 := by
    intro q η
    have hdV : HasDerivAt (fun y : ℝ => ∫ s in (0 : ℝ)..q, w (s, y) 1)
        (∫ s in (0 : ℝ)..q, Cyl.partialEta (fun p : Plane => w p 1) (s, η)) η :=
      hD (fun p : Plane => w p 1) hw2 0 q η
    rw [hIntEta q η] at hdV
    have hTot : HasDerivAt (fun y : ℝ => slicePsi c w g (q, y))
        (-(w (q, η) 0 - w (0, η) 0) - (-sliceGamma c w η / c + w (0, η) 0) +
          -sliceGamma c w η / c) η :=
      (hdV.sub (hVbar η)).add (hg η)
    show deriv (fun y : ℝ => slicePsi c w g (q, y)) η = -w (q, η) 0
    rw [hTot.deriv]
    ring
  -- (d) `∇^⊥ψ = w`
  refine ⟨hDiff, fun z => ?_⟩
  obtain ⟨q, η⟩ := z
  have hpg : perpendicularGradient (slicePsi c w g) (q, η) = (w (q, η) 0, w (q, η) 1) := by
    unfold perpendicularGradient
    rw [hX q η, hY q η, neg_neg]
  rw [hpg]
  exact Train.eq_toVec (w (q, η))

end UnforcedLeray.Short.PartI
