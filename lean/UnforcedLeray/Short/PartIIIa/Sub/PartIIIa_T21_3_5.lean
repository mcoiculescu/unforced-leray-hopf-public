import UnforcedLeray.Short.PartIIIa.Sub.T21_3_Strip

/-!
# Part III-a, `PartIII-a:T21/3/5`: the flux identity from five analytic facts

Source of record: `the November 2 reference manuscript`, lines 2819-2836.

Key observation (no decay of `∇E` is needed): a cylinder test `φ` vanishes for `|η|` large, hence so
does `E φ`, and `E = Ec tr r` is smooth and `c`-periodic, so `E φ` is again a cylinder test.  The
`div u = 0` clause of `IsBiotSavart` (stated for cylinder tests) therefore applies to `Eφ` directly:
`∫ (u·∇E) φ = - ∫ E (u·∇φ)`.  All integrability claims are on the cell, where the integrands are
`L²` times continuous with `η`-compact support.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.Short.IIIa
open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

section Flux

variable {ν c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)

/-- Lemma `/1`: the train vorticity `E = Ec tr r` (`r ≥ 0`) is smooth and `c`-periodic in `q`
(`tr.v` smooth and periodic, `E = curl v`; SP 2819-2836, B0238 `contDiff_Vc`, periodicity of the
train). -/
def EcSmoothPeriodic (tr : UnforcedLeray.B0140.TrainSol ν c) : Prop :=
  ∀ r : ℝ, 0 ≤ r → ContDiff ℝ ∞ (UnforcedLeray.B0238.Ec tr r) ∧
    ∀ x : ℝ × ℝ, UnforcedLeray.B0238.Ec tr r (x.1 + c, x.2) = UnforcedLeray.B0238.Ec tr r x

/-- Lemma `/2`: the `ω`-terms of the flow integrand are integrable on the cell: `ω ∈ L²(cell)`
(weight `≥ 1`), and `Δφ`, `v·∇φ` are continuous with `η`-compact support. -/
def FluxIntOmega (tr : UnforcedLeray.B0140.TrainSol ν c) : Prop :=
  ∀ r : ℝ, 0 ≤ r → ∀ w : ActualVorticity (c := c) (m := m) hm, ∀ φ : ℝ × ℝ → ℝ,
    UnforcedLeray.B0579.IsCylTest c φ →
      IntegrableOn (fun x => cplx (vortFn hm w) x * (lapP φ x : ℂ)) (UnforcedLeray.B0579.cell c) ∧
      IntegrableOn (fun x => cplx (vortFn hm w) x *
        ((tr.v r x 0 * UnforcedLeray.B0579.pd 0 φ x + tr.v r x 1 * UnforcedLeray.B0579.pd 1 φ x : ℝ) : ℂ))
        (UnforcedLeray.B0579.cell c)

/-- Lemma `/3`: the `u`-terms are integrable on the cell: `u = stripVel w ∈ L²(cell)`
(`BiotSavartField`), `∇E φ` and `E ∇φ` continuous with `η`-compact support. -/
def FluxIntVel (tr : UnforcedLeray.B0140.TrainSol ν c) : Prop :=
  BiotSavartField (c := c) (m := m) hm →
  ∀ r : ℝ, 0 ≤ r → ∀ w : ActualVorticity (c := c) (m := m) hm, ∀ φ : ℝ × ℝ → ℝ,
    UnforcedLeray.B0579.IsCylTest c φ →
      IntegrableOn (fun x => (stripVel hm w x 0 * (UnforcedLeray.B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x : ℂ) +
          stripVel hm w x 1 * (UnforcedLeray.B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℂ)) * (φ x : ℂ))
        (UnforcedLeray.B0579.cell c) ∧
      IntegrableOn (fun x => (UnforcedLeray.B0238.Ec tr r x : ℂ) *
          (stripVel hm w x 0 * (UnforcedLeray.B0579.pd 0 φ x : ℂ) +
            stripVel hm w x 1 * (UnforcedLeray.B0579.pd 1 φ x : ℂ))) (UnforcedLeray.B0579.cell c)

/-- Lemma `/4`: the components of the physical flux `B(r) w = v ω + E K_c ω` (`actualTrainFluxB`,
`physicalFlux`, `r ≥ 0`) satisfy, a.e. on the cell,
`fluxFn_0 ∂_qφ + fluxFn_1 ∂_ηφ = ω (v·∇φ) + E (u·∇φ)` (complex coerced). -/
def FluxFnAe (tr : UnforcedLeray.B0140.TrainSol ν c)
    (P : ActualTrainFluxPath (c := c) (m := m) hm (ν := ν) tr) : Prop :=
  ∀ r : ℝ, 0 ≤ r → ∀ w : ActualVorticity (c := c) (m := m) hm, ∀ φ : ℝ × ℝ → ℝ,
    UnforcedLeray.B0579.IsCylTest c φ →
      (fun x => ((fluxFn (actualTrainFluxB hm P r w) 0 x * UnforcedLeray.B0579.pd 0 φ x +
          fluxFn (actualTrainFluxB hm P r w) 1 x * UnforcedLeray.B0579.pd 1 φ x : ℝ) : ℂ)) =ᵐ[volume.restrict
          (UnforcedLeray.B0579.cell c)]
        fun x => cplx (vortFn hm w) x *
            ((tr.v r x 0 * UnforcedLeray.B0579.pd 0 φ x + tr.v r x 1 * UnforcedLeray.B0579.pd 1 φ x : ℝ) : ℂ) +
          (UnforcedLeray.B0238.Ec tr r x : ℂ) *
            (stripVel hm w x 0 * (UnforcedLeray.B0579.pd 0 φ x : ℂ) +
              stripVel hm w x 1 * (UnforcedLeray.B0579.pd 1 φ x : ℂ))

/-- Product rule for the planar partials. -/
theorem pd_mul_of_diff (j : Fin 2) {f g : ℝ × ℝ → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (x : ℝ × ℝ) :
    UnforcedLeray.B0579.pd j (fun y => f y * g y) x =
      UnforcedLeray.B0579.pd j f x * g x + f x * UnforcedLeray.B0579.pd j g x := by
  unfold UnforcedLeray.B0579.pd
  rw [fderiv_fun_mul (hf x) (hg x)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- The product of a smooth periodic function with a cylinder test is a cylinder test. -/
theorem isCylTest_mul_of {E φ : ℝ × ℝ → ℝ} (hE : ContDiff ℝ ∞ E)
    (hEp : ∀ x : ℝ × ℝ, E (x.1 + c, x.2) = E x) (hφ : UnforcedLeray.B0579.IsCylTest c φ) :
    UnforcedLeray.B0579.IsCylTest c (fun x => E x * φ x) where
  smooth := hE.mul hφ.smooth
  periodic x := by simp only [hEp x, hφ.periodic x]
  band := by
    obtain ⟨R, hR⟩ := hφ.band
    exact ⟨R, fun x hx => by simp [hR x hx]⟩

/-- Conditional flux identity. -/
theorem fluxIdentity_of {ν : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    (P : ActualTrainFluxPath (c := c) (m := m) hm (ν := ν) tr)
    (h1 : EcSmoothPeriodic (c := c) tr) (h2 : FluxIntOmega (m := m) hm tr)
    (h3 : FluxIntVel (m := m) hm tr) (h4 : FluxFnAe hm tr P)
    (hBS : BiotSavartField (c := c) (m := m) hm) : FluxIdentity hm tr P := by
  intro r hr w φ hφ
  obtain ⟨hE, hEp⟩ := h1 r hr
  have hψ := isCylTest_mul_of hE hEp hφ
  have hdiv := (hBS w).2.1 _ hψ
  have hEd : Differentiable ℝ (UnforcedLeray.B0238.Ec tr r) := hE.differentiable (by simp)
  have hφd : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
  obtain ⟨hA1, hA2⟩ := h2 r hr w φ hφ
  obtain ⟨hB1, hB2⟩ := h3 hBS r hr w φ hφ
  have hdiv' : ∫ x in UnforcedLeray.B0579.cell c,
      ((stripVel hm w x 0 * (UnforcedLeray.B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x : ℂ) +
          stripVel hm w x 1 * (UnforcedLeray.B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℂ)) * (φ x : ℂ)
        + (UnforcedLeray.B0238.Ec tr r x : ℂ) *
          (stripVel hm w x 0 * (UnforcedLeray.B0579.pd 0 φ x : ℂ) +
            stripVel hm w x 1 * (UnforcedLeray.B0579.pd 1 φ x : ℂ))) = 0 := by
    rw [← hdiv]
    apply integral_congr_ae
    refine Filter.Eventually.of_forall (fun x => ?_)
    show _ = stripVel hm w x 0 * ((UnforcedLeray.B0579.pd 0 (fun y => UnforcedLeray.B0238.Ec tr r y * φ y) x : ℝ) : ℂ) + _
    rw [pd_mul_of_diff 0 hEd hφd, pd_mul_of_diff 1 hEd hφd]
    push_cast
    ring
  rw [integral_add hB1 hB2] at hdiv'
  have hfi : flowIntegrand tr (cplx (vortFn hm w)) (stripVel hm w) r φ = fun x =>
      ((ν : ℂ) * (cplx (vortFn hm w) x * (lapP φ x : ℂ)) +
        cplx (vortFn hm w) x *
          ((tr.v r x 0 * UnforcedLeray.B0579.pd 0 φ x + tr.v r x 1 * UnforcedLeray.B0579.pd 1 φ x : ℝ) : ℂ)) -
      (stripVel hm w x 0 * (UnforcedLeray.B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x : ℂ) +
          stripVel hm w x 1 * (UnforcedLeray.B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℂ)) * (φ x : ℂ) := by
    funext x
    unfold flowIntegrand
    push_cast
    ring
  have hAA : IntegrableOn (fun x => (ν : ℂ) * (cplx (vortFn hm w) x * (lapP φ x : ℂ)) +
        cplx (vortFn hm w) x *
          ((tr.v r x 0 * UnforcedLeray.B0579.pd 0 φ x + tr.v r x 1 * UnforcedLeray.B0579.pd 1 φ x : ℝ) : ℂ))
      (UnforcedLeray.B0579.cell c) := (hA1.const_mul (ν : ℂ)).add hA2
  constructor
  · rw [hfi]
    exact hAA.sub hB1
  · rw [hfi, integral_sub hAA hB1,
      integral_add (hA1.const_mul (ν : ℂ)) hA2, integral_const_mul]
    have hB : ∫ x in UnforcedLeray.B0579.cell c,
        (stripVel hm w x 0 * (UnforcedLeray.B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x : ℂ) +
          stripVel hm w x 1 * (UnforcedLeray.B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℂ)) * (φ x : ℂ)
        = -∫ x in UnforcedLeray.B0579.cell c, (UnforcedLeray.B0238.Ec tr r x : ℂ) *
          (stripVel hm w x 0 * (UnforcedLeray.B0579.pd 0 φ x : ℂ) +
            stripVel hm w x 1 * (UnforcedLeray.B0579.pd 1 φ x : ℂ)) :=
      eq_neg_of_add_eq_zero_left hdiv'
    rw [hB]
    have e1 : ∫ x in UnforcedLeray.B0579.cell c, cplx (vortFn hm w) x * (lapP φ x : ℂ) =
        ((∫ x in UnforcedLeray.B0579.cell c, vortFn hm w x * lapP φ x : ℝ) : ℂ) := by
      have h : ∀ x, cplx (vortFn hm w) x * (lapP φ x : ℂ) = ((vortFn hm w x * lapP φ x : ℝ) : ℂ) :=
        fun x => by simp [cplx]
      simp only [h]
      exact integral_complex_ofReal
    have e2 : ∫ x in UnforcedLeray.B0579.cell c,
        ((fluxFn (actualTrainFluxB hm P r w) 0 x * UnforcedLeray.B0579.pd 0 φ x +
          fluxFn (actualTrainFluxB hm P r w) 1 x * UnforcedLeray.B0579.pd 1 φ x : ℝ) : ℂ) =
        ((∫ x in UnforcedLeray.B0579.cell c,
          (fluxFn (actualTrainFluxB hm P r w) 0 x * UnforcedLeray.B0579.pd 0 φ x +
          fluxFn (actualTrainFluxB hm P r w) 1 x * UnforcedLeray.B0579.pd 1 φ x) : ℝ) : ℂ) :=
      integral_complex_ofReal
    rw [Complex.ofReal_add, Complex.ofReal_mul, ← e1, ← e2,
      integral_congr_ae (h4 r hr w φ hφ), integral_add hA2 hB2]
    ring

end Flux

end UnforcedLeray.Short.IIIa.Exist
