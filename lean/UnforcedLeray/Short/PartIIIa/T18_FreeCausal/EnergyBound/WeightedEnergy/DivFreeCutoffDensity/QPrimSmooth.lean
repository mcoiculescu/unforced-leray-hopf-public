import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_1

/-!
# Part III-a, task `PartIII-a:T18/3/1/1/1`: smoothness of `q`-primitives and `q`-integrals

Target (`Sub/T18_3_1_1.lean`): `DfcQPrimSmooth`. Source of record:
`the November 2 reference manuscript`, lines 3541-3552 (density of
divergence-free fields; the calculus fact used there is smoothness of the `q`-primitive
`dfcQPrim c f` and of the `q`-integral `dfcQInt c f` of a smooth field).

## Mathematics

For `x = (q, η)` put `d = q + c/2`. The affine substitution `t = d s - c/2` (Mathlib
`intervalIntegral.smul_integral_comp_mul_add`, no nondegeneracy hypothesis needed) gives

  `∫_{-c/2}^{q} f(t, η) dt = d · ∫_0^1 f(d s - c/2, η) ds`.

The right side is a parametric integral over the FIXED interval `[0,1]` whose integrand
`(s, x) ↦ f(((x.1 + c/2) s - c/2), x.2)` is smooth jointly in `(s, x)`. Smoothness in `x` of
any finite order follows from differentiation under the integral sign over a compact interval,
proved here by induction on the order (`DfcQPrimSmoothAux.ipsContDiff`; the same argument as
`Short/PartII-a/Tasks/N02LerayComparison/ModeSplit/IntervalParamSmooth.lean`, copied so that this
file does not depend on another draft). Then `dfcQInt c f η = dfcQPrim c f (c/2, η)` holds by
definition, and it is a composition with the smooth map `η ↦ (c/2, η)`.

The hypothesis `0 < c` is not used.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace UnforcedLeray.Short.IIIa

namespace DfcQPrimSmoothAux

/-- First derivative under the `q`-integral over `[a, b]`, for a `C¹` integrand. -/
theorem ipsHasFDeriv (P V : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (a b : ℝ)
    (H : P × ℝ → V) (hH : ContDiff ℝ 1 H) (x₀ : P) :
    HasFDerivAt (fun x : P => ∫ q in a..b, H (x, q))
      (∫ q in a..b, (fderiv ℝ H (x₀, q)).comp (ContinuousLinearMap.inl ℝ P ℝ)) x₀ := by
  have hHc : Continuous H := hH.continuous
  have hfd : Continuous (fderiv ℝ H) := hH.continuous_fderiv (by norm_num)
  have hΦc : Continuous (fun z : P × ℝ => (fderiv ℝ H z).comp (ContinuousLinearMap.inl ℝ P ℝ)) :=
    hfd.clm_comp continuous_const
  have hcont₀ : Continuous
      (fun y : ℝ => (fderiv ℝ H (x₀, y)).comp (ContinuousLinearMap.inl ℝ P ℝ)) :=
    hΦc.comp (by fun_prop : Continuous fun y : ℝ => (x₀, y))
  obtain ⟨C, hC⟩ := isCompact_uIcc.exists_bound_of_continuousOn hcont₀.continuousOn
  have hev : ∀ᶠ x in nhds x₀, ∀ y ∈ Set.uIcc a b,
      ‖(fderiv ℝ H (x, y)).comp (ContinuousLinearMap.inl ℝ P ℝ)‖ < C + 1 := by
    refine isCompact_uIcc.eventually_forall_of_forall_eventually
      (P := fun x y => ‖(fderiv ℝ H (x, y)).comp (ContinuousLinearMap.inl ℝ P ℝ)‖ < C + 1) ?_
    intro y hy
    have hb : ‖(fderiv ℝ H (x₀, y)).comp (ContinuousLinearMap.inl ℝ P ℝ)‖ ≤ C := hC y hy
    have hlt : ‖(fderiv ℝ H (x₀, y)).comp (ContinuousLinearMap.inl ℝ P ℝ)‖ < C + 1 := by
      linarith
    exact (hΦc.norm.continuousAt).eventually_lt continuousAt_const hlt
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := MeasureTheory.volume)
    (F := fun x q => H (x, q))
    (F' := fun x q => (fderiv ℝ H (x, q)).comp (ContinuousLinearMap.inl ℝ P ℝ))
    (bound := fun _ => C + 1)
    (s := {x : P | ∀ y ∈ Set.uIcc a b,
      ‖(fderiv ℝ H (x, y)).comp (ContinuousLinearMap.inl ℝ P ℝ)‖ < C + 1})
    hev ?_ ?_ ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun x =>
      (by fun_prop : Continuous fun q : ℝ => H (x, q)).aestronglyMeasurable
  · exact (by fun_prop : Continuous fun q : ℝ => H (x₀, q)).intervalIntegrable a b
  · exact hcont₀.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun t ht x hx => ?_
    have h1 : ∀ y ∈ Set.uIcc a b,
        ‖(fderiv ℝ H (x, y)).comp (ContinuousLinearMap.inl ℝ P ℝ)‖ < C + 1 := hx
    exact (h1 t (Set.uIoc_subset_uIcc ht)).le
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall fun t _ x _ => ?_
    have hdiff : DifferentiableAt ℝ H (x, t) := (hH.differentiable one_ne_zero) (x, t)
    have hpair : HasFDerivAt (fun x' : P => (x', t)) (ContinuousLinearMap.inl ℝ P ℝ) x :=
      hasFDerivAt_prodMk_left x t
    exact hdiff.hasFDerivAt.comp x hpair

/-- Smoothness of `x ↦ ∫_a^b H(x, q) dq` in every finite order, for a complete codomain. -/
theorem ipsContDiff (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] (a b : ℝ) :
    ∀ n : ℕ, ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
      (H : P × ℝ → V), ContDiff ℝ n H → ContDiff ℝ n (fun x : P => ∫ q in a..b, H (x, q)) := by
  intro n
  induction n with
  | zero =>
    intro V _ _ _ H hH
    rw [Nat.cast_zero, contDiff_zero] at hH ⊢
    have hHu : Continuous (Function.uncurry fun (x : P) (t : ℝ) => H (x, t)) := hH
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hHu a b
  | succ n ih =>
    intro V _ _ _ H hH
    have hH1 : ContDiff ℝ 1 H := hH.of_le (by exact_mod_cast Nat.le_add_left 1 n)
    have hfd : ContDiff ℝ n (fderiv ℝ H) := hH.fderiv_right (by norm_num)
    have hH' : ContDiff ℝ n
        (fun z : P × ℝ => (fderiv ℝ H z).comp (ContinuousLinearMap.inl ℝ P ℝ)) :=
      hfd.clm_comp contDiff_const
    refine contDiff_succ_iff_hasFDerivAt.2
      ⟨fun x : P => ∫ q in a..b, (fderiv ℝ H (x, q)).comp (ContinuousLinearMap.inl ℝ P ℝ),
        ih (P →L[ℝ] V) (fun z : P × ℝ => (fderiv ℝ H z).comp (ContinuousLinearMap.inl ℝ P ℝ)) hH',
        fun x => ipsHasFDeriv P V a b H hH1 x⟩

end DfcQPrimSmoothAux

/-- Substitution: `dfcQPrim c f (q, η) = (q + c/2) ∫_0^1 f((q + c/2) s - c/2, η) ds`. -/
theorem dfcQPrim_eq_mul (c : ℝ) (f : ℝ × ℝ → ℝ) (x : ℝ × ℝ) :
    dfcQPrim c f x = (x.1 + c / 2) * ∫ s in (0:ℝ)..1, f ((x.1 + c / 2) * s + -(c / 2), x.2) := by
  have h := intervalIntegral.smul_integral_comp_mul_add (a := (0:ℝ)) (b := (1:ℝ))
    (f := fun t => f (t, x.2)) (x.1 + c / 2) (-(c / 2))
  have e0 : (x.1 + c / 2) * 0 + -(c / 2) = -(c / 2) := by ring
  have e1 : (x.1 + c / 2) * 1 + -(c / 2) = x.1 := by ring
  rw [e0, e1, smul_eq_mul] at h
  unfold dfcQPrim
  exact h.symm

/-- The parametric integral over `[0,1]` in the substituted form is smooth in `(q, η)`. -/
theorem paramIntegral_contDiff (c : ℝ) (f : ℝ × ℝ → ℝ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun x : ℝ × ℝ => ∫ s in (0:ℝ)..1, f ((x.1 + c / 2) * s + -(c / 2), x.2)) := by
  have hmap : ContDiff ℝ ∞
      (fun z : (ℝ × ℝ) × ℝ => ((z.1.1 + c / 2) * z.2 + -(c / 2), z.1.2)) := by
    fun_prop
  have hH : ContDiff ℝ ∞
      (fun z : (ℝ × ℝ) × ℝ => f ((z.1.1 + c / 2) * z.2 + -(c / 2), z.1.2)) :=
    hf.comp hmap
  exact contDiff_infty.2 fun n =>
    DfcQPrimSmoothAux.ipsContDiff (ℝ × ℝ) 0 1 n ℝ _ (contDiff_infty.1 hH n)

/-- Target: `DfcQPrimSmooth` (`Sub/T18_3_1_1.lean`). Smoothness of the `q`-primitive
`dfcQPrim c f` and of the `q`-integral `dfcQInt c f` for smooth `f`. -/
theorem dfcQPrimSmooth : UnforcedLeray.Short.IIIa.DfcQPrimSmooth := by
  unfold DfcQPrimSmooth
  intro c _hc f hf
  have hI := paramIntegral_contDiff c f hf
  have hfun : dfcQPrim c f = fun x : ℝ × ℝ =>
      (x.1 + c / 2) * ∫ s in (0:ℝ)..1, f ((x.1 + c / 2) * s + -(c / 2), x.2) :=
    funext fun x => dfcQPrim_eq_mul c f x
  have hQ : ContDiff ℝ ∞ (dfcQPrim c f) := by
    rw [hfun]
    exact (by fun_prop : ContDiff ℝ ∞ (fun x : ℝ × ℝ => x.1 + c / 2)).mul hI
  refine ⟨hQ, ?_⟩
  have hcomp : ContDiff ℝ ∞ (fun η : ℝ => (c / 2, η)) :=
    contDiff_const.prodMk contDiff_id
  have hdef : dfcQInt c f = fun η => dfcQPrim c f (c / 2, η) := rfl
  rw [hdef]
  exact hQ.comp hcomp

end UnforcedLeray.Short.IIIa
