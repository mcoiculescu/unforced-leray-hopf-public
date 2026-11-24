import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.Bootstrap.Ops

/-!
# Spine: integration and differentiation through `(I - D)^s` (helper of `Regularity/Bootstrap.lean`)

Two facts used by the time bootstrap:
* `integral_IDpow`: a Bochner integral of a curve whose `(I - D)^s`-image is continuous commutes with
  `(I - D)^s` (the coefficients commute with the integral, and Parseval/Bessel gives the domain);
* `hasDerivAt_IDpow`: if `V' = G` in `XG` and `(I - D)^s G = W` is continuous on `(0, ∞)`, then
  `θ ↦ (I - D)^s V θ` has derivative `W θ` on `(0, ∞)`.

No `sorry`, `admit`, `axiom` or `native_decide`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter intervalIntegral
open scoped ContDiff Topology InnerProductSpace ComplexConjugate

namespace UnforcedLeray.Short.Spine.BootCalc

open UnforcedLeray.B0010 UnforcedLeray.B0123 UnforcedLeray.B0094
open UnforcedLeray.Short.Spine.BootOps

theorem integral_IDpow (s : ℝ) (g h : ℝ → XG) (a b : ℝ)
    (hg : ContinuousOn g (uIcc a b)) (hh : ContinuousOn h (uIcc a b))
    (hgh : ∀ t ∈ uIcc a b, ∃ ht : g t ∈ (IDpow s).domain, IDpow s ⟨g t, ht⟩ = h t) :
    ∃ hI : (∫ t in a..b, g t) ∈ (IDpow s).domain,
      IDpow s ⟨∫ t in a..b, g t, hI⟩ = ∫ t in a..b, h t := by
  have hcoefG : ∀ n : ℕ, ∫ t in a..b, ⟪oscBasis n, g t⟫_ℂ = ⟪oscBasis n, ∫ t in a..b, g t⟫_ℂ := by
    intro n
    have := ContinuousLinearMap.intervalIntegral_comp_comm (innerSL ℂ (oscBasis n))
      (ContinuousOn.intervalIntegrable (μ := volume) hg)
    simpa only [coe_innerSL_apply] using this
  have hcoefH : ∀ n : ℕ, ∫ t in a..b, ⟪oscBasis n, h t⟫_ℂ = ⟪oscBasis n, ∫ t in a..b, h t⟫_ℂ := by
    intro n
    have := ContinuousLinearMap.intervalIntegral_comp_comm (innerSL ℂ (oscBasis n))
      (ContinuousOn.intervalIntegrable (μ := volume) hh)
    simpa only [coe_innerSL_apply] using this
  have hmul : ∀ n : ℕ, ∫ t in a..b, ⟪oscBasis n, h t⟫_ℂ
      = idMult s n * ∫ t in a..b, ⟪oscBasis n, g t⟫_ℂ := by
    intro n
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    obtain ⟨ht', hEq⟩ := hgh t ht
    show ⟪oscBasis n, h t⟫_ℂ = idMult s n * ⟪oscBasis n, g t⟫_ℂ
    rw [← hEq]
    exact inner_IDpow s ⟨g t, ht'⟩ n
  have hcoef : ∀ n : ℕ, ⟪oscBasis n, ∫ t in a..b, h t⟫_ℂ
      = idMult s n * ⟪oscBasis n, ∫ t in a..b, g t⟫_ℂ := by
    intro n
    rw [← hcoefH n, hmul n, hcoefG n]
  have hsum : Summable (fun n : ℕ => ‖idMult s n‖ ^ 2 * ‖⟪oscBasis n, ∫ t in a..b, g t⟫_ℂ‖ ^ 2) := by
    refine (hasSum_norm_inner_sq oscBasis (∫ t in a..b, h t)).summable.congr (fun n => ?_)
    rw [hcoef n, norm_mul]
    ring
  have hI : (∫ t in a..b, g t) ∈ (IDpow s).domain :=
    (mem_mulOp_domain_iff_summable oscBasis (idMult s) _).2 hsum
  refine ⟨hI, ?_⟩
  apply ext_inner_basis oscBasis
  intro n
  rw [inner_IDpow]
  exact (hcoef n).symm

theorem hasDerivAt_IDpow (s : ℝ) (V G W U : ℝ → XG) (θ0 : ℝ) (hθ : 0 < θ0)
    (hV : ∀ t, 0 < t → HasDerivAt V (G t) t)
    (hGc : ContinuousOn G (Ioi 0)) (hWc : ContinuousOn W (Ioi 0))
    (hGW : ∀ t, 0 < t → ∃ ht : G t ∈ (IDpow s).domain, IDpow s ⟨G t, ht⟩ = W t)
    (hUV : ∀ t, 0 < t → ∃ ht : V t ∈ (IDpow s).domain, IDpow s ⟨V t, ht⟩ = U t) :
    HasDerivAt U (W θ0) θ0 := by
  have hsub : ∀ u : ℝ, 0 < u → uIcc θ0 u ⊆ Ioi 0 := by
    intro u hu t ht
    rcases Set.mem_uIcc.1 ht with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact lt_of_lt_of_le hθ h1
    · exact lt_of_lt_of_le hu h1
  have key : ∀ u : ℝ, 0 < u → U u = U θ0 + ∫ t in θ0..u, W t := by
    intro u hu
    obtain ⟨hu', eu⟩ := hUV u hu
    obtain ⟨hθ', eθ⟩ := hUV θ0 hθ
    have hS := hsub u hu
    have hFTC : ∫ t in θ0..u, G t = V u - V θ0 := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro x hx
        exact hV x (hS hx)
      · exact ContinuousOn.intervalIntegrable (hGc.mono hS)
    obtain ⟨hI, eI⟩ := integral_IDpow s G W θ0 u (hGc.mono hS) (hWc.mono hS)
      (fun t ht => hGW t (hS ht))
    have hd : V u - V θ0 ∈ (IDpow s).domain := Submodule.sub_mem _ hu' hθ'
    have hsub' : IDpow s ⟨V u - V θ0, hd⟩ = IDpow s ⟨V u, hu'⟩ - IDpow s ⟨V θ0, hθ'⟩ :=
      LinearPMap.map_sub (IDpow s) ⟨V u, hu'⟩ ⟨V θ0, hθ'⟩
    have hcongr : IDpow s ⟨V u - V θ0, hd⟩ = IDpow s ⟨∫ t in θ0..u, G t, hI⟩ :=
      IDpow_congr_val _ _ hFTC.symm
    have hfin : IDpow s ⟨V u, hu'⟩ - IDpow s ⟨V θ0, hθ'⟩ = ∫ t in θ0..u, W t :=
      hsub'.symm.trans (hcongr.trans eI)
    rw [← eu, ← eθ, ← hfin]
    abel
  have hW0 : ContinuousAt W θ0 := hWc.continuousAt (Ioi_mem_nhds hθ)
  have hmeas : StronglyMeasurableAtFilter W (𝓝 θ0) :=
    hWc.stronglyMeasurableAtFilter isOpen_Ioi θ0 hθ
  have hint : IntervalIntegrable W volume θ0 θ0 :=
    ContinuousOn.intervalIntegrable (hWc.mono (hsub θ0 hθ))
  have hd := intervalIntegral.integral_hasDerivAt_right hint hmeas hW0
  have h2 := hd.const_add (U θ0)
  exact h2.congr_of_eventuallyEq (Filter.eventually_of_mem (Ioi_mem_nhds hθ) (fun u hu => key u hu))

end UnforcedLeray.Short.Spine.BootCalc
