import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3.Of
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_1.Generator
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2.ContZero

/-!
# `R0TransposeIdentity` (organizer task `PartIII-b:C/flatset/col/7/3/2`)

Source `the November 2 reference manuscript` 1650-1656 (`T₀ = (μ - A₀)⁻¹P₀`,
`A₀ = -S + νsΔ`, transpose `T₀(t)* = e^{-t/2}e^{νs(eᵗ-1)Δ}f(seᵗ)`).

Route: with `Z, AZ` the `H`-representatives of `ζ, A₀*ζ`, `V = μZ - AZ` represents
`(μ - A₀*)ζ`, and `F(t) = ⟨Z, T₀(t)g⟩` has `F'(t) = ⟨AZ, T₀(t)g⟩` for `t > 0`. Then
`⟨R₀(μ)g, V⟩ = ∫_0^∞ e^{-μt}(μF - F') dt = -∫_0^∞ (e^{-μt}F)' dt = F(0) = ⟨Z, g⟩`.

The generator identity (`NeedGenerator`), right-continuity at `0` (`NeedContZero`) and the
`H`-membership of `ζ` and `A₀*ζ` (`NeedMemLpTest`) are not yet in the library (B0224 has no
time-derivative or strong-continuity lemma for `T₀`). They are stated as explicit `Prop`s and the
target is reduced to them; see `r0TransposeIdentity_of_needs`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate InnerProductSpace

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.PartIIa (IsMeridTest)

/-- NEEDED: smooth meridional tests and their `A₀*`-images lie in `H`. -/
def NeedMemLpTest : Prop :=
  ∀ (c ν : ℝ) (ζ : Profile → MeridC), IsMeridTest c ζ →
    MemLp ζ 2 (measureH c) ∧ MemLp (A0adj ν ζ) 2 (measureH c)

/-- NEEDED: generator identity, `d/dt ⟨ζ, T₀(t)g⟩_H = ⟨A₀*ζ, T₀(t)g⟩_H` for `t > 0`. -/
def NeedGenerator : Prop :=
  ∀ (c ν : ℝ) (hc : 0 < c), 0 < ν → ∀ (g : HSpace c MeridC) (ζ : Profile → MeridC), IsMeridTest c ζ →
    ∀ t : ℝ, 0 < t →
      HasDerivAt (fun s : ℝ => pairH c (UnforcedLeray.B0224.T0 hc ν s g : Profile → MeridC) ζ)
        (pairH c (UnforcedLeray.B0224.T0 hc ν t g : Profile → MeridC) (A0adj ν ζ)) t

/-- NEEDED: right-continuity at `0` of `t ↦ ⟨ζ, T₀(t)g⟩_H` (strong continuity of `T₀`). -/
def NeedContZero : Prop :=
  ∀ (c ν : ℝ) (hc : 0 < c) (g : HSpace c MeridC) (ζ : Profile → MeridC), IsMeridTest c ζ →
    ContinuousWithinAt
      (fun s : ℝ => pairH c (UnforcedLeray.B0224.T0 hc ν s g : Profile → MeridC) ζ) (Ici 0) 0

/-- **Reduction of `R0TransposeIdentity` to the three needed facts.** -/
theorem r0TransposeIdentity_of_needs (hM : NeedMemLpTest) (hG : NeedGenerator)
    (hC : NeedContZero) : R0TransposeIdentity := by
  intro c ν μ hc hν hμ g ζ hζ
  obtain ⟨hZm, hAm⟩ := hM c ν ζ hζ
  obtain ⟨Z, hZ⟩ : ∃ Z : HSpace c MeridC, (Z : Profile → MeridC) =ᵐ[measureH c] ζ :=
    ⟨hZm.toLp ζ, hZm.coeFn_toLp⟩
  obtain ⟨AZ, hAZ⟩ : ∃ AZ : HSpace c MeridC,
      (AZ : Profile → MeridC) =ᵐ[measureH c] A0adj ν ζ :=
    ⟨hAm.toLp _, hAm.coeFn_toLp⟩
  have hμC : 0 < ((μ : ℂ)).re + 1 / 4 := by simpa using hμ
  -- `V = μZ - AZ` represents `(μ - A₀*)ζ`
  have hVae : (((μ : ℂ) • Z - AZ : HSpace c MeridC) : Profile → MeridC)
      =ᵐ[measureH c] resolventTest ν μ ζ := by
    filter_upwards [Lp.coeFn_sub ((μ : ℂ) • Z) AZ, Lp.coeFn_smul (μ : ℂ) Z, hZ, hAZ]
      with p h1 h2 h3 h4
    rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3, h4]
    simp only [resolventTest]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ) μ (ζ p)]
    rfl
  have hV : ∀ y : HSpace c MeridC, inner ℂ ((μ : ℂ) • Z - AZ) y =
      (μ : ℂ) * inner ℂ Z y - inner ℂ AZ y := by
    intro y
    rw [inner_sub_left, inner_smul_left, Complex.conj_ofReal]
  -- `⟨Z, u⟩ = pairH u ζ` and `⟨AZ, u⟩ = pairH u (A₀*ζ)`
  have hFz : ∀ t : ℝ, pairH c (UnforcedLeray.B0224.T0 hc ν t g : Profile → MeridC) ζ =
      inner ℂ Z (UnforcedLeray.B0224.T0 hc ν t g) := fun t => pairH_eq_inner _ Z hZ
  -- left side: `pairH (R0 g) (μζ - A₀*ζ) = ⟨V, R0 g⟩`
  have hpair_R : pairH c (UnforcedLeray.B0225.R0 hc ν (μ : ℂ) g : Profile → MeridC)
      (resolventTest ν μ ζ) = inner ℂ ((μ : ℂ) • Z - AZ) (UnforcedLeray.B0225.R0 hc ν (μ : ℂ) g) :=
    pairH_eq_inner _ _ hVae
  have hint : IntegrableOn
      (fun t : ℝ => Complex.exp (-((μ : ℂ) * t)) • UnforcedLeray.B0224.T0 hc ν t g) (Ioi 0) :=
    UnforcedLeray.B0225.integrableOn_lapT0 hc ν hμC g
  have hR0 : inner ℂ ((μ : ℂ) • Z - AZ) (UnforcedLeray.B0225.R0 hc ν (μ : ℂ) g) =
      ∫ t in Ioi (0 : ℝ), Complex.exp (-((μ : ℂ) * t)) *
        inner ℂ ((μ : ℂ) • Z - AZ) (UnforcedLeray.B0224.T0 hc ν t g) := by
    rw [UnforcedLeray.B0225.R0_apply hc ν hμC g, ← integral_inner hint]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [inner_smul_right]
  -- the function `F(t) = ⟨Z, T₀(t)g⟩`, its derivative and right-continuity
  have hcont : ContinuousWithinAt
      (fun t : ℝ => Complex.exp (-((μ : ℂ) * t)) * inner ℂ Z (UnforcedLeray.B0224.T0 hc ν t g))
      (Ici 0) 0 := by
    have h1 : ContinuousWithinAt
        (fun t : ℝ => inner ℂ Z (UnforcedLeray.B0224.T0 hc ν t g)) (Ici 0) 0 :=
      (hC c ν hc g ζ hζ).congr (fun t _ => (hFz t).symm) (hFz 0).symm
    exact (Continuous.continuousWithinAt (by fun_prop)).mul h1
  have hderiv : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivAt
        (fun t : ℝ => Complex.exp (-((μ : ℂ) * t)) * inner ℂ Z (UnforcedLeray.B0224.T0 hc ν t g))
        (-(Complex.exp (-((μ : ℂ) * x)) *
          inner ℂ ((μ : ℂ) • Z - AZ) (UnforcedLeray.B0224.T0 hc ν x g))) x := by
    intro x hx
    have hE : HasDerivAt (fun t : ℝ => Complex.exp (-((μ : ℂ) * t)))
        (Complex.exp (-((μ : ℂ) * x)) * (-(μ : ℂ))) x := by
      have h := (((hasDerivAt_id x).ofReal_comp).const_mul (μ : ℂ)).neg.cexp
      simpa using h
    have hF : HasDerivAt (fun t : ℝ => inner ℂ Z (UnforcedLeray.B0224.T0 hc ν t g))
        (inner ℂ AZ (UnforcedLeray.B0224.T0 hc ν x g)) x := by
      have h := hG c ν hc hν g ζ hζ x hx
      have hfun : (fun s : ℝ => pairH c (UnforcedLeray.B0224.T0 hc ν s g : Profile → MeridC) ζ) =
          fun s : ℝ => inner ℂ Z (UnforcedLeray.B0224.T0 hc ν s g) := funext hFz
      rw [hfun] at h
      rw [show pairH c (UnforcedLeray.B0224.T0 hc ν x g : Profile → MeridC) (A0adj ν ζ) =
          inner ℂ AZ (UnforcedLeray.B0224.T0 hc ν x g) from pairH_eq_inner _ AZ hAZ] at h
      exact h
    have hprod := hE.mul hF
    refine hprod.congr_deriv ?_
    rw [hV]
    ring
  -- integrability of the derivative
  have hfint : IntegrableOn
      (fun x : ℝ => -(Complex.exp (-((μ : ℂ) * x)) *
        inner ℂ ((μ : ℂ) • Z - AZ) (UnforcedLeray.B0224.T0 hc ν x g))) (Ioi 0) := by
    have hI : Integrable (fun t : ℝ => (innerSL ℂ ((μ : ℂ) • Z - AZ))
        (UnforcedLeray.B0225.lapT0 hc ν (μ : ℂ) g t)) (volume.restrict (Ioi (0 : ℝ))) :=
      ContinuousLinearMap.integrable_comp (innerSL ℂ ((μ : ℂ) • Z - AZ)) hint
    refine hI.neg.congr (Eventually.of_forall fun t => ?_)
    simp only [Pi.neg_apply, innerSL_apply_apply, UnforcedLeray.B0225.lapT0, inner_smul_right]
  -- decay at infinity
  have htend : Tendsto
      (fun t : ℝ => Complex.exp (-((μ : ℂ) * t)) * inner ℂ Z (UnforcedLeray.B0224.T0 hc ν t g))
      atTop (𝓝 0) := by
    have hexp : Tendsto (fun t : ℝ => Real.exp (-(((μ : ℂ)).re + 1 / 4) * t)) atTop (𝓝 0) := by
      have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (Tendsto.const_mul_atTop hμC (tendsto_id (x := atTop)))
      exact Tendsto.congr (fun t => by simp only [Function.comp_apply, id, neg_mul]) h2
    have hb : Tendsto (fun t : ℝ => ‖Z‖ * (‖g‖ * Real.exp (-(((μ : ℂ)).re + 1 / 4) * t)))
        atTop (𝓝 0) := by
      simpa only [mul_zero] using ((hexp.const_mul ‖g‖).const_mul ‖Z‖)
    refine squeeze_zero_norm' (Eventually.of_forall fun t => ?_) hb
    have hEq : Complex.exp (-((μ : ℂ) * t)) * inner ℂ Z (UnforcedLeray.B0224.T0 hc ν t g) =
        inner ℂ Z (UnforcedLeray.B0225.lapT0 hc ν (μ : ℂ) g t) := by
      simp only [UnforcedLeray.B0225.lapT0, inner_smul_right]
    rw [hEq]
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (UnforcedLeray.B0225.norm_lapT0_le hc ν (μ : ℂ) g t)
        (norm_nonneg _))
  -- integration by parts on `(0, ∞)`
  have hfinal := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hfint htend
  have hT0g : UnforcedLeray.B0224.T0 hc ν 0 g = g := by
    rw [UnforcedLeray.B0224.T0_zero_eq]
    rfl
  simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_mul, hT0g] at hfinal
  rw [integral_neg] at hfinal
  rw [hpair_R, hR0, pairH_eq_inner g Z hZ]
  linear_combination -hfinal

theorem r0TransposeIdentity : R0TransposeIdentity :=
  r0TransposeIdentity_of_needs (fun c ν ζ hζ => memLp_test_A0adj c ν ζ hζ)
    (fun c ν hc hν g ζ hζ t ht => t0_generator c ν hc hν g ζ hζ t ht)
    (fun c ν hc g ζ hζ => t0_contZero c ν hc g ζ hζ)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
