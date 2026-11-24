import UnforcedLeray.Cons.L2.CanonicalBranch.Evolution

/-!
# Small-diffusion free-family convergence for the canonical complement

This is the first free-family input to the compact-Duhamel route for B0112. It is independent of
the reference adjoint and uses only the explicit Gaussian semigroup `expD`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology InnerProductSpace

namespace UnforcedLeray.Cons.G3b

open UnforcedLeray.B0010 UnforcedLeray.B0094 UnforcedLeray.B0123 UnforcedLeray.Evolution

/-- The free propagator for a nonnegative diffusion coefficient `β`. -/
def freeDiffusion (β : ℝ → ℝ) (t s : ℝ) : XG →L[ℂ] XG :=
  expD (∫ τ in s..t, β τ)

/-- A uniform pointwise bound on `β` makes its integrated diffusion small on a fixed block. -/
theorem integral_beta_small_block {β : ℝ → ℝ} {s t B δ : ℝ}
    (hst : s ≤ t) (hspan : t - s ≤ B)
    (hβi : IntervalIntegrable β volume s t)
    (hβ0 : ∀ τ, 0 ≤ β τ) (hβδ : ∀ τ, β τ ≤ δ) (hδ : 0 ≤ δ) :
    0 ≤ (∫ τ in s..t, β τ) ∧ (∫ τ in s..t, β τ) ≤ δ * B := by
  constructor
  · exact intervalIntegral.integral_nonneg hst (fun τ _ => hβ0 τ)
  · have hmono := intervalIntegral.integral_mono_on hst hβi intervalIntegrable_const
      (fun τ _ => hβδ τ)
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    calc
      (∫ τ in s..t, β τ) ≤ (t - s) * δ := hmono
      _ ≤ B * δ := mul_le_mul_of_nonneg_right hspan hδ
      _ = δ * B := mul_comm _ _

/-- Strong continuity at zero, with an explicit neighborhood that can be used uniformly over
all coefficients `β`. -/
theorem expD_apply_close_of_small_parameter (x : XG) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ a : ℝ, |a| < η → ‖expD a x - x‖ < ε := by
  have hcont : ContinuousAt (fun a : ℝ => expD a x) 0 :=
    (continuous_expD_apply x).continuousAt
  have hev : ∀ᶠ a : ℝ in 𝓝 0, expD a x ∈ Metric.ball (expD 0 x) ε :=
    hcont (Metric.ball_mem_nhds _ hε)
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨η, hη, hball⟩ := hev
  refine ⟨η, hη, fun a ha => ?_⟩
  have haBall : dist a (0 : ℝ) < η := by
    simpa [Real.dist_eq] using ha
  have hdist := hball haBall
  rw [Metric.mem_ball, dist_eq_norm] at hdist
  simpa [B0123.expD_zero] using hdist

/-- As `‖β‖∞ → 0`, the concrete free Gaussian propagators converge strongly to the identity,
uniformly over all endpoints in a block of length at most `B` and all coefficients in the same
pointwise envelope. -/
theorem freeDiffusion_uniform_strong_small {B : ℝ} (hB : 0 < B) (x : XG) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (β : ℝ → ℝ) (s t : ℝ),
      s ≤ t → t - s ≤ B → IntervalIntegrable β volume s t →
      (∀ τ, 0 ≤ β τ) → (∀ τ, β τ ≤ δ) →
      ‖freeDiffusion β t s x - x‖ < ε := by
  obtain ⟨η, hη, hclose⟩ := expD_apply_close_of_small_parameter x hε
  let δ : ℝ := η / (2 * B)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, fun β s t hst hspan hβi hβ0 hβδ => ?_⟩
  have hα := integral_beta_small_block hst hspan hβi hβ0 hβδ hδ.le
  have hαsmall : |(∫ τ in s..t, β τ)| < η := by
    rw [abs_of_nonneg hα.1]
    calc
      (∫ τ in s..t, β τ) ≤ δ * B := hα.2
      _ = η / 2 := by dsimp [δ]; field_simp
      _ < η := by linarith
  simpa [freeDiffusion] using hclose (∫ τ in s..t, β τ) hαsmall

/-- The concrete measurable-coefficient Gaussian diffusion defines a contraction evolution
family on any fixed block. The hypotheses retain the interval integrability needed by the
evolution law and the endpoint continuity needed by the Dyson construction. -/
def freeDiffusionFamily {a b : ℝ} (β : ℝ → ℝ)
    (hβi : ∀ s t, IntervalIntegrable β volume s t)
    (hβ0 : ∀ τ, 0 ≤ β τ) (M : ℝ) (hβM : ∀ τ, |β τ| ≤ M) :
    EvolutionFamily XG a b where
  U := fun t s => freeDiffusion β t s
  U_diag t _ := by simp [freeDiffusion, B0123.expD_zero]
  U_comp s r t _ hsr hrt _ := by
    unfold freeDiffusion
    rw [← B0123.expD_add
      (intervalIntegral.integral_nonneg hrt fun τ _ => hβ0 τ)
      (intervalIntegral.integral_nonneg hsr fun τ _ => hβ0 τ), add_comm,
      intervalIntegral.integral_add_adjacent_intervals (hβi s r) (hβi r t)]
  U_cont x := by
    have hβbound : ∀ p ∈ Evolution.triangle a b, ∀ r ∈ Set.Ioc p.1 p.2,
        ‖β r‖ ≤ max M 0 := by
      intro p _ r _
      simpa [Real.norm_eq_abs] using (hβM r).trans (le_max_left M 0)
    have hIcont : ContinuousOn
        (fun p : ℝ × ℝ => ∫ r in p.1..p.2, β r) (Evolution.triangle a b) := by
      have hIcontC : ContinuousOn
          (fun p : ℝ × ℝ => ∫ r in p.1..p.2, (β r : ℂ)) (Evolution.triangle a b) := by
        refine Evolution.continuousOn_integral_triangle
          (Ψ := fun (_ : ℝ × ℝ) r => (β r : ℂ)) (K := max M 0) ?_ ?_ ?_
        · intro p hp
          have hβc : IntervalIntegrable (fun r => (β r : ℂ)) volume p.1 p.2 := by
            rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hp.2.1]
            exact Complex.ofRealCLM.integrable_comp (hβi p.1 p.2).1
          exact hβc.1.1
        · intro p hp r hr
          simpa [Complex.norm_real, Real.norm_eq_abs] using
            (hβM r).trans (le_max_left M 0)
        · intro p hp r hpr hrt
          exact continuousWithinAt_const
      have hRe : ContinuousOn
          (fun p : ℝ × ℝ => Complex.re (∫ r in p.1..p.2, (β r : ℂ)))
          (Evolution.triangle a b) :=
        Complex.continuous_re.comp_continuousOn hIcontC
      have heq : ∀ p ∈ Evolution.triangle a b,
          ∫ r in p.1..p.2, β r = Complex.re (∫ r in p.1..p.2, (β r : ℂ)) := by
        intro p hp
        have hβc : IntervalIntegrable (fun r => (β r : ℂ)) volume p.1 p.2 := by
          rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hp.2.1]
          exact Complex.ofRealCLM.integrable_comp (hβi p.1 p.2).1
        simpa using Complex.reCLM.intervalIntegral_comp_comm hβc
      exact hRe.congr fun p hp => heq p hp
    have hUcont := (continuous_expD_apply x).comp_continuousOn hIcont
    change ContinuousOn
      (fun p : ℝ × ℝ => expD (∫ τ in p.1..p.2, β τ) x)
      {p | a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b}
    exact hUcont
  U_bdd := ⟨1, fun s t _ _ _ => norm_expD_le _⟩

/-- The Gaussian free propagator is self-adjoint for nonnegative diffusion time. -/
theorem adjoint_expD_eq_expD {a : ℝ} (ha : 0 ≤ a) :
    ContinuousLinearMap.adjoint (expD a) = expD a := by
  apply ContinuousLinearMap.ext
  intro x
  apply B0094.ext_inner_basis B0094.oscBasis
  intro n
  obtain ⟨hn, hDn⟩ := B0094.D_oscBasis n
  have hDn' : B0094.D ⟨B0094.oscBasis n, hn⟩ =
      ((-(n : ℝ) : ℝ) : ℂ) • (B0094.oscBasis n : XG) := by
    simpa only [Complex.ofReal_neg, Complex.ofReal_natCast, Subtype.coe_mk] using hDn
  have hEig := B0123.expD_eigen ha ⟨B0094.oscBasis n, hn⟩ (-(n : ℝ)) hDn'
  rw [ContinuousLinearMap.adjoint_inner_right, hEig, inner_smul_left,
    B0123.inner_expD]
  rw [Complex.ofReal_neg] at hEig
  have hexp : Complex.exp ((a : ℂ) * ((-(n : ℝ)) : ℂ)) =
      ((Real.exp (-(a * n)) : ℝ) : ℂ) := by
    rw [show (a : ℂ) * ((-(n : ℝ)) : ℂ) = ((-(a * n) : ℝ) : ℂ) by
      push_cast
      ring,
      Complex.ofReal_exp]
  have hcoef : starRingEnd ℂ
      (Complex.exp ((a : ℂ) * ((-(n : ℝ)) : ℂ))) = B0123.expMult a n := by
    rw [hexp, Complex.conj_ofReal]
    simp [B0123.expMult, ha]
  simp only [Complex.ofReal_neg]
  rw [hcoef]

/-- The Gaussian diffusion family has a strongly continuous adjoint family because each
nonnegative-time `expD` is self-adjoint. -/
theorem freeDiffusionFamily_adjointContinuous {a b : ℝ} (β : ℝ → ℝ)
    (hβi : ∀ s t, IntervalIntegrable β volume s t)
    (hβ0 : ∀ τ, 0 ≤ β τ) (M : ℝ) (hβM : ∀ τ, |β τ| ≤ M) :
    (freeDiffusionFamily (a := a) (b := b) β hβi hβ0 M hβM).AdjointContinuous := by
  intro y
  let E : EvolutionFamily XG a b := freeDiffusionFamily (a := a) (b := b) β hβi hβ0 M hβM
  have hcont := E.U_cont y
  refine hcont.congr fun p hp => ?_
  have hself : ContinuousLinearMap.adjoint (freeDiffusion β p.2 p.1) =
      freeDiffusion β p.2 p.1 := by
    unfold freeDiffusion
    exact adjoint_expD_eq_expD
      (intervalIntegral.integral_nonneg hp.2.1 (fun τ _ => hβ0 τ))
  change (ContinuousLinearMap.adjoint (freeDiffusion β p.2 p.1)) y =
    freeDiffusion β p.2 p.1 y
  rw [hself]


/-- The adjoints of the free Gaussian propagators converge strongly to the identity with the same
uniformity as the propagators. -/
theorem adjoint_freeDiffusion_uniform_strong_small {B : ℝ} (hB : 0 < B) (y : XG) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (β : ℝ → ℝ) (s t : ℝ),
      s ≤ t → t - s ≤ B → IntervalIntegrable β volume s t →
      (∀ τ, 0 ≤ β τ) → (∀ τ, β τ ≤ δ) →
      ‖ContinuousLinearMap.adjoint (freeDiffusion β t s) y - y‖ < ε := by
  obtain ⟨δ, hδ, hsmall⟩ := freeDiffusion_uniform_strong_small hB y hε
  refine ⟨δ, hδ, fun β s t hst hspan hβi hβ0 hβδ => ?_⟩
  have hα := integral_beta_small_block hst hspan hβi hβ0 hβδ hδ.le
  have hself := adjoint_expD_eq_expD hα.1
  have hopen : ContinuousLinearMap.adjoint (freeDiffusion β t s) = freeDiffusion β t s := by
    simpa [freeDiffusion] using hself
  rw [hopen]
  exact hsmall β s t hst hspan hβi hβ0 hβδ

end UnforcedLeray.Cons.G3b
