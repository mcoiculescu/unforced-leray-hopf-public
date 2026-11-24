import UnforcedLeray.Cons.L2.CanonicalBranch.DysonConvergence

/-!
# Weak Gaussian generator on the oscillator domain

This downstream leaf begins the concrete B0115 derivation. It records the selfadjoint action of the
Gaussian diffusion family and develops the domain-level integral formula needed to test the actual
Dyson evolution against the adjoint mode.
-/

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set

namespace UnforcedLeray.Cons.G3b

open UnforcedLeray.B0010 UnforcedLeray.B0094 UnforcedLeray.B0123

private theorem integral_expMult_generator (n : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    ∫ u in (0 : ℝ)..a, B0123.expMult u n * (-(n : ℂ)) =
      B0123.expMult a n - 1 := by
  have hraw : ∫ u in (0 : ℝ)..a,
      Complex.exp (-(n : ℂ) * (u : ℂ)) * (-(n : ℂ)) =
        Complex.exp (-(n : ℂ) * (a : ℂ)) - 1 := by
    by_cases hn : (n : ℂ) = 0
    · simp [hn]
    · have hbase := integral_exp_mul_complex (a := (0 : ℝ)) (b := a)
        (c := -(n : ℂ)) (by simpa using hn)
      have hbase' : (∫ u in (0 : ℝ)..a,
          Complex.exp (-(n : ℂ) * (u : ℂ))) =
          (Complex.exp (-(n : ℂ) * (a : ℂ)) - 1) / (-(n : ℂ)) := by
        rw [hbase]
        simp
      calc
        ∫ u in (0 : ℝ)..a, Complex.exp (-(n : ℂ) * (u : ℂ)) * (-(n : ℂ)) =
            (∫ u in (0 : ℝ)..a, Complex.exp (-(n : ℂ) * (u : ℂ))) * (-(n : ℂ)) := by
              rw [intervalIntegral.integral_mul_const]
        _ = ((Complex.exp (-(n : ℂ) * (a : ℂ)) - 1) / (-(n : ℂ))) * (-(n : ℂ)) := by
              rw [hbase']
        _ = Complex.exp (-(n : ℂ) * (a : ℂ)) - 1 := by
              field_simp [hn]
  have hpoint : ∀ u ∈ uIcc (0 : ℝ) a,
      B0123.expMult u n * (-(n : ℂ)) =
        Complex.exp (-(n : ℂ) * (u : ℂ)) * (-(n : ℂ)) := by
    intro u hu
    rw [uIcc_of_le ha] at hu
    simp [B0123.expMult, max_eq_left hu.1, mul_comm]
  calc
    ∫ u in (0 : ℝ)..a, B0123.expMult u n * (-(n : ℂ)) =
        ∫ u in (0 : ℝ)..a, Complex.exp (-(n : ℂ) * (u : ℂ)) * (-(n : ℂ)) := by
      apply intervalIntegral.integral_congr
      intro u hu
      exact hpoint u hu
    _ = Complex.exp (-(n : ℂ) * (a : ℂ)) - 1 := hraw
    _ = B0123.expMult a n - 1 := by
      simp [B0123.expMult, max_eq_left ha, mul_comm]

section InnerProductLemmas

/-- The Gaussian diffusion multiplier is selfadjoint. -/
theorem expD_adjoint_eq_self {a : ℝ} (ha : 0 ≤ a) :
    ContinuousLinearMap.adjoint (B0123.expD a) = B0123.expD a := by
  apply ContinuousLinearMap.ext
  intro x
  apply B0094.ext_inner_basis
  intro n
  obtain ⟨hn, hDn⟩ := B0094.D_oscBasis n
  have hDn' : B0094.D ⟨B0094.oscBasis n, hn⟩ =
      (((-(n : ℝ)) : ℝ) : ℂ) • B0094.oscBasis n := by
    rw [hDn, Complex.ofReal_neg, Complex.ofReal_natCast]
  have hexp : Complex.exp ((a : ℂ) * (((-(n : ℝ)) : ℝ) : ℂ)) =
      (Real.exp (-(a * (n : ℝ))) : ℂ) := by
    have harg : (a : ℂ) * (((-(n : ℝ)) : ℝ) : ℂ) =
        ((-(a * (n : ℝ)) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [harg, ← Complex.ofReal_exp]
  rw [ContinuousLinearMap.adjoint_inner_right,
    B0123.expD_eigen ha ⟨B0094.oscBasis n, hn⟩ (-(n : ℝ)) hDn',
    B0123.inner_expD]
  rw [B0123.expMult_of_nonneg ha, hexp, inner_smul_left, Complex.conj_ofReal]

/-- The Gaussian semigroup satisfies the integrated generator identity on `D.domain`. -/
theorem expD_integral_generator {a : ℝ} (ha : 0 ≤ a) (z : B0094.D.domain) :
    B0123.expD a (z : XG) = (z : XG) +
      ∫ u in (0 : ℝ)..a, B0123.expD u (B0094.D z) := by
  apply B0094.ext_inner_basis
  intro n
  have hInt : IntervalIntegrable (fun u : ℝ => B0123.expD u (B0094.D z)) volume 0 a :=
    (continuous_expD_apply (B0094.D z)).continuousOn.intervalIntegrable_of_Icc ha
  have hmap : inner ℂ (B0094.oscBasis n)
      (∫ u in (0 : ℝ)..a, B0123.expD u (B0094.D z)) =
      ∫ u in (0 : ℝ)..a,
        inner ℂ (B0094.oscBasis n) (B0123.expD u (B0094.D z)) := by
    simpa only [innerSL_apply_apply] using
      ((innerSL ℂ (B0094.oscBasis n)).intervalIntegral_comp_comm hInt).symm
  have hDcoeff : inner ℂ (B0094.oscBasis n) (B0094.D z) =
      -(n : ℂ) * inner ℂ (B0094.oscBasis n) (z : XG) := B0123.inner_D z n
  rw [B0123.inner_expD, inner_add_right, hmap]
  simp_rw [B0123.inner_expD, hDcoeff]
  have hfac : ∫ u in (0 : ℝ)..a,
      B0123.expMult u n * (-(n : ℂ) * inner ℂ (B0094.oscBasis n) (z : XG)) =
        (B0123.expMult a n - 1) * inner ℂ (B0094.oscBasis n) (z : XG) := by
    calc
      ∫ u in (0 : ℝ)..a,
          B0123.expMult u n * (-(n : ℂ) * inner ℂ (B0094.oscBasis n) (z : XG)) =
        (∫ u in (0 : ℝ)..a, B0123.expMult u n * (-(n : ℂ))) *
          inner ℂ (B0094.oscBasis n) (z : XG) := by
            rw [← intervalIntegral.integral_mul_const]
            congr 1
            funext u
            ring
      _ = (B0123.expMult a n - 1) * inner ℂ (B0094.oscBasis n) (z : XG) := by
        rw [integral_expMult_generator n ha]
  calc
    B0123.expMult a n * inner ℂ (B0094.oscBasis n) (z : XG) =
        inner ℂ (B0094.oscBasis n) (z : XG) +
          (B0123.expMult a n - 1) * inner ℂ (B0094.oscBasis n) (z : XG) := by ring
    _ = inner ℂ (B0094.oscBasis n) (z : XG) +
          ∫ u in (0 : ℝ)..a,
            B0123.expMult u n * (-(n : ℂ) * inner ℂ (B0094.oscBasis n) (z : XG)) := by
      rw [hfac]

/-- The domain identity follows a continuous nonnegative diffusion clock. -/
theorem expD_integral_generator_timeChange {s t : ℝ} (hst : s ≤ t)
    (β : ℝ → ℝ) (hβ : Continuous β)
    (hβ0 : ∀ r ∈ Icc s t, 0 ≤ β r) (z : B0094.D.domain) :
    B0123.expD (∫ r in s..t, β r) (z : XG) = (z : XG) +
      ∫ r in s..t, β r • B0123.expD (∫ q in s..r, β q) (B0094.D z) := by
  let ρ : ℝ → ℝ := fun r => ∫ q in s..r, β q
  have hρder : ∀ r ∈ uIcc s t, HasDerivAt ρ (β r) r := by
    intro r hr
    change HasDerivAt (fun y => ∫ q in s..y, β q) (β r) r
    exact intervalIntegral.integral_hasDerivAt_right
      (hβ.intervalIntegrable s r)
      (hβ.stronglyMeasurableAtFilter volume (nhds r))
      (hβ.continuousAt)
  have hβcont : ContinuousOn β (uIcc s t) :=
    hβ.continuousOn.mono (subset_univ _)
  have hsubst :
      (∫ r in s..t, β r • B0123.expD (ρ r) (B0094.D z)) =
        ∫ u in ρ s..ρ t, B0123.expD u (B0094.D z) := by
    exact intervalIntegral.integral_deriv_smul_comp hρder hβcont
      (continuous_expD_apply (B0094.D z))
  have hρs : ρ s = 0 := by simp [ρ]
  have ha : 0 ≤ ρ t := by
    change 0 ≤ ∫ r in s..t, β r
    exact intervalIntegral.integral_nonneg hst (fun r hr => hβ0 r hr)
  have hbase := expD_integral_generator ha z
  have hbase' : B0123.expD (ρ t) (z : XG) = (z : XG) +
      ∫ u in ρ s..ρ t, B0123.expD u (B0094.D z) := by
    rw [hρs]
    exact hbase
  rw [← hsubst] at hbase'
  simpa [ρ] using hbase'

/-- Testing the diffusion clock against a domain vector gives the adjoint generator pairing. -/
theorem expD_timeChange_inner_generator {s t : ℝ} (hst : s ≤ t)
    (β : ℝ → ℝ) (hβ : Continuous β)
    (hβ0 : ∀ r ∈ Icc s t, 0 ≤ β r) (z : B0094.D.domain) (x : XG) :
    inner ℂ (z : XG) (B0123.expD (∫ r in s..t, β r) x) =
      inner ℂ (z : XG) x +
        ∫ r in s..t, ((β r : ℝ) : ℂ) *
          inner ℂ (B0094.D z) (B0123.expD (∫ q in s..r, β q) x) := by
  let ρ : ℝ → ℝ := fun r => ∫ q in s..r, β q
  have hρder : ∀ r ∈ uIcc s t, HasDerivAt ρ (β r) r := by
    intro r hr
    change HasDerivAt (fun y => ∫ q in s..y, β q) (β r) r
    exact intervalIntegral.integral_hasDerivAt_right
      (hβ.intervalIntegrable s r)
      (hβ.stronglyMeasurableAtFilter volume (nhds r)) hβ.continuousAt
  have hρcont : ContinuousOn ρ (Icc s t) := by
    intro r hr
    have hr' : r ∈ uIcc s t := by rw [uIcc_of_le hst]; exact hr
    exact (hρder r hr').continuousAt.continuousWithinAt
  have hPath : ContinuousOn (fun r => B0123.expD (ρ r) (B0094.D z)) (Icc s t) :=
    (continuous_expD_apply (B0094.D z)).comp_continuousOn hρcont
  have hIntegrand : ContinuousOn
      (fun r => β r • B0123.expD (ρ r) (B0094.D z)) (Icc s t) :=
    hβ.continuousOn.smul hPath
  have hInt : IntervalIntegrable
      (fun r => β r • B0123.expD (ρ r) (B0094.D z)) volume s t :=
    hIntegrand.intervalIntegrable_of_Icc hst
  have hclock_nonneg : 0 ≤ ρ t := by
    change 0 ≤ ∫ r in s..t, β r
    exact intervalIntegral.integral_nonneg hst (fun r hr => hβ0 r hr)
  have hself_t := expD_adjoint_eq_self hclock_nonneg
  have hpair : inner ℂ (z : XG) (B0123.expD (ρ t) x) =
      inner ℂ (B0123.expD (ρ t) (z : XG)) x := by
    calc
      inner ℂ (z : XG) (B0123.expD (ρ t) x) =
          inner ℂ (z : XG) ((ContinuousLinearMap.adjoint (B0123.expD (ρ t))) x) := by
            rw [hself_t]
      _ = inner ℂ (B0123.expD (ρ t) (z : XG)) x :=
            ContinuousLinearMap.adjoint_inner_right _ _ _
  have hbase := expD_integral_generator_timeChange hst β hβ hβ0 z
  calc
    inner ℂ (z : XG) (B0123.expD (ρ t) x) =
        inner ℂ (B0123.expD (ρ t) (z : XG)) x := hpair
    _ = inner ℂ (z : XG) x +
        inner ℂ (∫ r in s..t, β r • B0123.expD (ρ r) (B0094.D z)) x := by
          rw [hbase, inner_add_left]
    _ = inner ℂ (z : XG) x +
        ∫ r in s..t, ((β r : ℝ) : ℂ) *
          inner ℂ (B0094.D z) (B0123.expD (ρ r) x) := by
          have hinner := UnforcedLeray.Evolution.inner_integral_left hst hInt x
          calc
            inner ℂ (z : XG) x +
                inner ℂ (∫ r in s..t, β r • B0123.expD (ρ r) (B0094.D z)) x =
              inner ℂ (z : XG) x +
                ∫ r in s..t, inner ℂ (β r • B0123.expD (ρ r) (B0094.D z)) x :=
                  congrArg (fun w : ℂ => inner ℂ (z : XG) x + w) hinner
            _ = inner ℂ (z : XG) x +
                ∫ r in s..t, ((β r : ℝ) : ℂ) *
                  inner ℂ (B0094.D z) (B0123.expD (ρ r) x) := by
              congr 1
              apply intervalIntegral.integral_congr
              intro r hr
              rw [uIcc_of_le hst] at hr
              have hrρ : 0 ≤ ρ r := by
                change 0 ≤ ∫ q in s..r, β q
                exact intervalIntegral.integral_nonneg hr.1
                  (fun q hq => hβ0 q ⟨hq.1, hq.2.trans hr.2⟩)
              have hself_r := expD_adjoint_eq_self hrρ
              have hmap_r : B0123.expD (ρ r) =
                  ContinuousLinearMap.adjoint (B0123.expD (ρ r)) := hself_r.symm
              have hvec_r : B0123.expD (ρ r) (B0094.D z) =
                  (ContinuousLinearMap.adjoint (B0123.expD (ρ r))) (B0094.D z) :=
                congrArg (fun A : XG →L[ℂ] XG => A (B0094.D z)) hmap_r
              have hpair_r : inner ℂ
                  (B0123.expD (ρ r) (B0094.D z)) x =
                    inner ℂ (B0094.D z) (B0123.expD (ρ r) x) := by
                calc
                  inner ℂ (B0123.expD (ρ r) (B0094.D z)) x =
                      inner ℂ ((ContinuousLinearMap.adjoint (B0123.expD (ρ r)))
                    (B0094.D z)) x := by rw [hvec_r]
                  _ = inner ℂ (B0094.D z) (B0123.expD (ρ r) x) :=
                        ContinuousLinearMap.adjoint_inner_left _ _ _
              change inner ℂ (β r • B0123.expD (ρ r) (B0094.D z)) x = _
              rw [RCLike.real_smul_eq_coe_smul (K := ℂ) (β r)
                (B0123.expD (ρ r) (B0094.D z))]
              rw [inner_smul_left, hpair_r]
              simp

/-- Weak generator of the concrete Gaussian family on the one-functional core generated by a
vector in `D.domain`. -/
theorem freeDiffusionFamily_hasWeakGenerator_domain {a b : ℝ}
    (β : ℝ → ℝ) (hβ : Continuous β) (hβ0 : ∀ r, 0 ≤ β r)
    (M : ℝ) (hβM : ∀ r, |β r| ≤ M) (z : B0094.D.domain) :
    (freeDiffusionFamily (a := a) (b := b) β
      (fun s t => hβ.intervalIntegrable s t) hβ0 M hβM).HasWeakGenerator
      {innerSL ℂ (z : XG)}
      (fun t _ => ((β t : ℝ) : ℂ) • innerSL ℂ (B0094.D z)) := by
  let E := freeDiffusionFamily (a := a) (b := b) β
    (fun s t => hβ.intervalIntegrable s t) hβ0 M hβM
  let G : ℝ → (XG →L[ℂ] ℂ) → (XG →L[ℂ] ℂ) :=
    fun t _ => ((β t : ℝ) : ℂ) • innerSL ℂ (B0094.D z)
  intro ℓ hℓ s x hs t ht
  let ρ : ℝ → ℝ := fun r => ∫ q in s..r, β q
  have hℓeq : ℓ = innerSL ℂ (z : XG) := by simpa using hℓ
  subst ℓ
  have hρc : ContinuousOn ρ (Icc s b) := by
    intro r hr
    dsimp [ρ]
    exact (UnforcedLeray.Evolution.hasDerivWithinAt_integral_Icc
      (hβ.continuousOn.mono (Icc_subset_Icc le_rfl le_rfl)) hr).continuousWithinAt
  have hg : ContinuousOn
      (fun r => ((β r : ℝ) : ℂ) *
        inner ℂ (B0094.D z) (B0123.expD (ρ r) x)) (Icc s b) := by
    have hβc : ContinuousOn (fun r => ((β r : ℝ) : ℂ)) (Icc s b) :=
      (Complex.continuous_ofReal.comp hβ).continuousOn
    have hpath : ContinuousOn
        (fun r => B0123.expD (ρ r) x) (Icc s b) :=
      (continuous_expD_apply x).comp_continuousOn hρc
    exact hβc.mul ((continuousOn_const.inner hpath))
  have hEid : ∀ u ∈ Icc s b,
      inner ℂ (z : XG) (E.U u s x) = inner ℂ (z : XG) x +
        ∫ r in s..u, ((β r : ℝ) : ℂ) *
          inner ℂ (B0094.D z) (B0123.expD (ρ r) x) := by
    intro u hu
    have h := expD_timeChange_inner_generator hu.1 β hβ
      (fun r hr => hβ0 r) z x
    simpa [E, ρ, freeDiffusionFamily, freeDiffusion] using h
  have hder := UnforcedLeray.Evolution.hasDerivWithinAt_integral_Icc hg ht
  have hder' := hder.const_add (inner ℂ (z : XG) x)
  have hder'' := hder'.congr_of_mem hEid ht
  have hG : G t (innerSL ℂ (z : XG)) (E.U t s x) =
      ((β t : ℝ) : ℂ) * inner ℂ (B0094.D z) (E.U t s x) := by
    simp [G, innerSL_apply_apply]
  have htarget : G t (innerSL ℂ (z : XG)) (E.U t s x) =
      ((β t : ℝ) : ℂ) * inner ℂ (B0094.D z) (B0123.expD (ρ t) x) := by
    simpa [E, ρ, freeDiffusionFamily, freeDiffusion] using hG
  rw [htarget]
  exact hder''

end InnerProductLemmas

end UnforcedLeray.Cons.G3b
