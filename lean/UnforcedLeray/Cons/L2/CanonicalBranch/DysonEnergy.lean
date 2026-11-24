import UnforcedLeray.Cons.L2.CanonicalBranch.DysonStability
import UnforcedLeray.Lib.EvolutionFamilies.WeakGenerator
import UnforcedLeray.Lib.BochnerTime.Basic
import UnforcedLeray.Lib.BochnerTime.Energy
import UnforcedLeray.Lib.BudgetsGronwall.VariationOfConstants
import Mathlib.Analysis.InnerProductSpace.Calculus
import UnforcedLeray.Units.B0087

/-!
# Energy estimates for the bounded Dyson approximations

This leaf develops the differential estimate for bounded approximations of the canonical first
Dyson evolution. The coefficient is allowed to be operator-norm continuous on a block; the
canonical profile `β(t)=1/(R-t)` has this property on every active compact block.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace ComplexConjugate RealInnerProductSpace

namespace UnforcedLeray.Cons.G3b

open UnforcedLeray.B0010 UnforcedLeray.Evolution UnforcedLeray.BochnerTime

private theorem continuousOn_complexCast {a b : ℝ} {β : ℝ → ℝ}
    (hβ : ContinuousOn β (Icc a b)) :
    ContinuousOn (fun r => ((β r : ℝ) : ℂ)) (Icc a b) := by
  exact Complex.continuous_ofReal.continuousOn.comp hβ
    (fun r hr => Set.mem_univ (β r))

/-- The identity evolution family on a time interval. -/
private def identityEvolutionFamily {a b : ℝ} : EvolutionFamily XG a b where
  U _ _ := 1
  U_diag _ _ := rfl
  U_comp _ _ _ _ _ _ _ := by ext x; rfl
  U_cont _ := continuousOn_const
  U_bdd := ⟨1, fun _ _ _ _ _ => ContinuousLinearMap.norm_id_le⟩

/-- On a continuous bounded coefficient, a Dyson evolution from the identity family has the
pointwise vector derivative `u'=A(t)u`. This follows from its actual left Duhamel identity. -/
theorem dyson_identity_hasDerivWithinAt {a b s t : ℝ} (A : BoundedPert XG a b)
    (hA : ContinuousOn A.A (Icc a b)) (has : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) (x : XG) :
    HasDerivWithinAt (fun r => (Evolution.dyson (identityEvolutionFamily (a := a) (b := b)) A).U r s x)
      (A.A t ((Evolution.dyson (identityEvolutionFamily (a := a) (b := b)) A).U t s x))
      (Icc s b) t := by
  let U := Evolution.dyson (identityEvolutionFamily (a := a) (b := b)) A
  have hcont : ContinuousOn (fun r => U.U r s x) (Icc s b) := U.continuousOn_fst has x
  have hUcont : ContinuousOn (fun r => A.A r (U.U r s x)) (Icc s b) :=
    (hA.mono (Icc_subset_Icc has le_rfl)).clm_apply hcont
  have hder := Evolution.hasDerivWithinAt_integral_Icc hUcont ⟨hst, ht⟩
  have hstar : ∀ τ ∈ Icc s b,
      U.U τ s x = x + ∫ r in s..τ, A.A r (U.U r s x) := by
    intro τ hτ
    change (Evolution.dyson (identityEvolutionFamily (a := a) (b := b)) A).U τ s x =
      x + ∫ r in s..τ,
        A.A r ((Evolution.dyson (identityEvolutionFamily (a := a) (b := b)) A).U r s x)
    rw [Evolution.dyson_left (identityEvolutionFamily (a := a) (b := b)) A
      ⟨has, hτ.1, hτ.2⟩ x]
    simp [identityEvolutionFamily]
    rfl
  have hder' := hder.const_add x
  exact hder'.congr_of_mem hstar ⟨hst, ht⟩

/-- A signed-rate energy estimate for a continuously differentiable complex Hilbert-valued path. -/
theorem continuousODE_norm_le_exp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (u : ℝ → E) (A : ℝ → E →L[ℂ] E) {a s T : ℝ}
    (hu : ContinuousOn u (Icc s T))
    (hODE : ∀ τ ∈ Ico s T, HasDerivWithinAt u (A τ (u τ)) (Icc s T) τ)
    (hdiss : ∀ τ ∈ Ico s T, (⟪u τ, A τ (u τ)⟫_ℂ).re ≤ a * ‖u τ‖ ^ 2)
    {t : ℝ} (ht : t ∈ Icc s T) :
    ‖u t‖ ≤ Real.exp (a * (t - s)) * ‖u s‖ := by
  letI : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
  let y : ℝ → ℝ := fun τ => ‖u τ‖ ^ 2
  have hy : ContinuousOn y (Icc s T) := hu.norm.pow 2
  have hdy : ∀ τ ∈ Ico s T,
      ∃ y', HasDerivWithinAt y y' (Ici τ) τ ∧ y' ≤ (2 * a) * y τ + (0 : ℝ) := by
    intro τ hτ
    refine ⟨2 * ⟪u τ, A τ (u τ)⟫_ℝ, ?_, ?_⟩
    · exact (hODE τ hτ).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hτ) |>.norm_sq
    · have hre : ⟪u τ, A τ (u τ)⟫_ℝ = (⟪u τ, A τ (u τ)⟫_ℂ).re :=
        real_inner_eq_re_inner (𝕜 := ℂ) _ _
      have h := hdiss τ hτ
      dsimp [y]
      rw [hre]
      nlinarith
  have hmain := UnforcedLeray.Gronwall.le_exp_mul_of_deriv_le
    (y := y) (γ := fun _ => 0) (K := 2 * a) hy continuousOn_const hdy t ht
  have hsq : ‖u t‖ ^ 2 ≤
      Real.exp ((2 * a) * (t - s)) * ‖u s‖ ^ 2 := by
    simpa [y] using hmain
  have hexp : (Real.exp (a * (t - s)) * ‖u s‖) ^ 2 =
      Real.exp ((2 * a) * (t - s)) * ‖u s‖ ^ 2 := by
    rw [mul_pow, pow_two, ← Real.exp_add]
    congr 1
    ring
  have hright : 0 ≤ Real.exp (a * (t - s)) * ‖u s‖ :=
    mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  apply (sq_le_sq₀ (norm_nonneg _) hright).mp
  rw [hexp]
  exact hsq

/-- The identity-free Dyson evolution obeys the signed energy estimate whenever its continuous
coefficient has the corresponding dissipative quadratic-form bound. -/
theorem dyson_identity_norm_le_exp {a b s t rate : ℝ} (A : BoundedPert XG a b)
    (hA : ContinuousOn A.A (Icc a b)) (has : a ≤ s) (hst : s ≤ t) (ht : t ≤ b)
    (hDiss : ∀ r ∈ Icc a b, ∀ z : XG,
      (⟪z, A.A r z⟫_ℂ).re ≤ rate * ‖z‖ ^ 2) (x : XG) :
    ‖(Evolution.dyson (identityEvolutionFamily (a := a) (b := b)) A).U t s x‖ ≤
      Real.exp (rate * (t - s)) * ‖x‖ := by
  let U := Evolution.dyson (identityEvolutionFamily (a := a) (b := b)) A
  have hu : ContinuousOn (fun r => U.U r s x) (Icc s t) :=
    (U.continuousOn_fst has x).mono (Icc_subset_Icc le_rfl ht)
  have hODE : ∀ τ ∈ Ico s t,
      HasDerivWithinAt (fun r => U.U r s x) (A.A τ (U.U τ s x)) (Icc s t) τ := by
    intro τ hτ
    have hder := dyson_identity_hasDerivWithinAt A hA has hτ.1
      ((le_of_lt hτ.2).trans ht) x
    exact hder.mono (Icc_subset_Icc le_rfl ht)
  have hDiss' : ∀ τ ∈ Ico s t,
      (⟪U.U τ s x, A.A τ (U.U τ s x)⟫_ℂ).re ≤
        rate * ‖U.U τ s x‖ ^ 2 := by
    intro τ hτ
    exact hDiss τ ⟨has.trans hτ.1, (le_of_lt hτ.2).trans ht⟩ _
  calc
    ‖U.U t s x‖ ≤ Real.exp (rate * (t - s)) * ‖U.U s s x‖ :=
      continuousODE_norm_le_exp (fun r => U.U r s x) A.A hu hODE hDiss'
        ⟨hst, le_rfl⟩
    _ = Real.exp (rate * (t - s)) * ‖x‖ := by
      rw [U.apply_diag ⟨has, hst.trans ht⟩ x]

/-- The bounded Yosida regularization of the canonical first-stage generator. -/
def boundedYosidaCoefficient (T : XG →L[ℂ] XG) (lam κ : ℂ) (β : ℝ → ℝ)
    (N : ℕ) (r : ℝ) : XG →L[ℂ] XG :=
  T - lam • (1 : XG →L[ℂ] XG) - (((β r : ℝ) : ℂ) * κ) • (1 : XG →L[ℂ] XG) +
    ((β r : ℝ) : ℂ) • PlanarSpectral.Dyosida N

set_option maxHeartbeats 500000 in
private theorem continuousOn_boundedYosidaCoefficient {a b : ℝ}
    (T : XG →L[ℂ] XG) (lam κ : ℂ) (β : ℝ → ℝ) (N : ℕ)
    (hβ : ContinuousOn β (Icc a b)) :
    ContinuousOn (fun r => boundedYosidaCoefficient T lam κ β N r) (Icc a b) := by
  have hβc := continuousOn_complexCast hβ
  have hβκ : ContinuousOn (fun r => ((β r : ℝ) : ℂ) * κ) (Icc a b) :=
    hβc.mul continuousOn_const
  have hI : ContinuousOn (fun _ : ℝ => (1 : XG →L[ℂ] XG)) (Icc a b) := continuousOn_const
  have hT : ContinuousOn (fun _ : ℝ => T) (Icc a b) := continuousOn_const
  have hlam : ContinuousOn (fun _ : ℝ => lam) (Icc a b) := continuousOn_const
  have hD : ContinuousOn (fun _ : ℝ => PlanarSpectral.Dyosida N) (Icc a b) :=
    continuousOn_const
  have hlamI : ContinuousOn (fun r => lam • (1 : XG →L[ℂ] XG)) (Icc a b) := hlam.smul hI
  have hβκI : ContinuousOn
      (fun r => (((β r : ℝ) : ℂ) * κ) • (1 : XG →L[ℂ] XG)) (Icc a b) := hβκ.smul hI
  have hβD : ContinuousOn
      (fun r => ((β r : ℝ) : ℂ) • PlanarSpectral.Dyosida N) (Icc a b) := hβc.smul hD
  change ContinuousOn
    (fun r => T - lam • (1 : XG →L[ℂ] XG) -
      (((β r : ℝ) : ℂ) * κ) • (1 : XG →L[ℂ] XG) +
      ((β r : ℝ) : ℂ) • PlanarSpectral.Dyosida N) (Icc a b)
  exact (hT.sub hlamI).sub hβκI |>.add hβD

/-- Build an actual `BoundedPert` from an operator-norm continuous coefficient on a compact
time interval. -/
def boundedPertOfContinuous {a b : ℝ} (A : ℝ → XG →L[ℂ] XG)
    (hA : ContinuousOn A (Icc a b)) : BoundedPert XG a b where
  A := A
  meas x := (hA.clm_apply continuousOn_const).aestronglyMeasurable measurableSet_Icc
  bdd := by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
    exact ⟨C, hC⟩

/-- The Yosida-regularized coefficient has the sharp energy rate when `0≤β≤δ` and the
transport generator is skew-adjoint. -/
theorem boundedYosidaCoefficient_quadratic_bound {a b δ rate : ℝ}
    (T : XG →L[ℂ] XG) (hT : ContinuousLinearMap.adjoint T = -T)
    (lam κ : ℂ) (β : ℝ → ℝ) (N : ℕ)
    (hβ0 : ∀ r ∈ Icc a b, 0 ≤ β r) (hβδ : ∀ r ∈ Icc a b, β r ≤ δ)
    (hδ : 0 ≤ δ) (hrate : rate = -lam.re + δ * |κ.re|) :
    ∀ r ∈ Icc a b, ∀ z : XG,
      (⟪z, boundedYosidaCoefficient T lam κ β N r z⟫_ℂ).re ≤ rate * ‖z‖ ^ 2 := by
  intro r hr z
  have hβr : 0 ≤ β r := hβ0 r hr
  have hβrδ : β r ≤ δ := hβδ r hr
  have hTz : (⟪z, T z⟫_ℂ).re = 0 :=
    UnforcedLeray.Infra.re_inner_apply_eq_zero_of_adjoint_eq_neg hT z
  have hDz : (⟪z, PlanarSpectral.Dyosida N z⟫_ℂ).re ≤ 0 :=
    dyosida_inner_nonpos N z
  have hself : (⟪z, z⟫_ℂ).re = ‖z‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) z
  have him : (⟪z, z⟫_ℂ).im = 0 := by
    have hs := inner_conj_symm (𝕜 := ℂ) z z
    have him' := congrArg Complex.im hs
    simp only [Complex.conj_im] at him'
    nlinarith
  have hselfC : ⟪z, z⟫_ℂ = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    apply Complex.ext
    · simpa using hself
    · simpa using him
  have hκ : -(β r * κ.re) ≤ δ * |κ.re| := by
    calc
      -(β r * κ.re) = β r * (-κ.re) := by ring
      _ ≤ β r * |κ.re| := mul_le_mul_of_nonneg_left (neg_le_abs κ.re) hβr
      _ ≤ δ * |κ.re| :=
        mul_le_mul_of_nonneg_right hβrδ (abs_nonneg _)
  have hform :
      (⟪z, boundedYosidaCoefficient T lam κ β N r z⟫_ℂ).re =
        (⟪z, T z⟫_ℂ).re - lam.re * ‖z‖ ^ 2 -
          (β r * κ.re) * ‖z‖ ^ 2 + β r * (⟪z, PlanarSpectral.Dyosida N z⟫_ℂ).re := by
    have happly : boundedYosidaCoefficient T lam κ β N r z =
        T z - lam • z - (((β r : ℝ) : ℂ) * κ) • z +
          ((β r : ℝ) : ℂ) • PlanarSpectral.Dyosida N z := rfl
    rw [happly, inner_add_right, inner_sub_right, inner_sub_right,
      inner_smul_right, inner_smul_right, inner_smul_right, hselfC]
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    ring
  rw [hrate, hform, hTz]
  have hdz : β r * (⟪z, PlanarSpectral.Dyosida N z⟫_ℂ).re ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hβr hDz
  have hn : 0 ≤ ‖z‖ ^ 2 := by positivity
  have hκn := mul_le_mul_of_nonneg_right hκ hn
  nlinarith

/-- The actual bounded Yosida Dyson approximant has the sharp signed exponential norm bound for
continuous `β` with `0≤β≤δ`. -/
theorem boundedYosidaDyson_norm_le {a b s t δ : ℝ}
    (lam κ : ℂ) (β : ℝ → ℝ) (N : ℕ)
    (hβ : ContinuousOn β (Icc a b)) (hβ0 : ∀ r ∈ Icc a b, 0 ≤ β r)
    (hβδ : ∀ r ∈ Icc a b, β r ≤ δ) (hδ : 0 ≤ δ)
    (hT : ContinuousLinearMap.adjoint UnforcedLeray.B0087.imMulOp =
      -UnforcedLeray.B0087.imMulOp)
    (has : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) (x : XG) :
    ‖(Evolution.dyson (identityEvolutionFamily (a := a) (b := b))
      (boundedPertOfContinuous
        (fun r => boundedYosidaCoefficient UnforcedLeray.B0087.imMulOp lam κ β N r)
        (continuousOn_boundedYosidaCoefficient _ _ _ _ _ hβ))).U t s x‖ ≤
      Real.exp ((-lam.re + δ * |κ.re|) * (t - s)) * ‖x‖ := by
  let A := boundedPertOfContinuous
    (fun r => boundedYosidaCoefficient UnforcedLeray.B0087.imMulOp lam κ β N r)
    (continuousOn_boundedYosidaCoefficient _ _ _ _ _ hβ)
  have hDiss : ∀ r ∈ Icc a b, ∀ z : XG,
      (⟪z, A.A r z⟫_ℂ).re ≤ (-lam.re + δ * |κ.re|) * ‖z‖ ^ 2 := by
    intro r hr z
    exact boundedYosidaCoefficient_quadratic_bound
      (T := UnforcedLeray.B0087.imMulOp) hT lam κ β N hβ0 hβδ hδ rfl r hr z
  have hA : ContinuousOn A.A (Icc a b) :=
    continuousOn_boundedYosidaCoefficient _ _ _ _ _ hβ
  exact dyson_identity_norm_le_exp A hA has hst ht hDiss x


/-- The bounded diffusion coefficient used to construct the Hermite Yosida evolution. -/
def boundedYosidaDiffusionCoefficient (β : ℝ → ℝ) (N : ℕ) (r : ℝ) : XG →L[ℂ] XG :=
  ((β r : ℝ) : ℂ) • PlanarSpectral.Dyosida N

/-- The identity family has zero weak generator on the full dual. -/
theorem identityEvolutionFamily_hasWeakGenerator {a b : ℝ} :
    (identityEvolutionFamily (a := a) (b := b)).HasWeakGenerator Set.univ
      (fun _ _ => 0) := by
  intro (ℓ : XG →L[ℂ] ℂ) hℓ s x hs t ht
  change HasDerivWithinAt (fun _ : ℝ => ℓ x) 0 (Icc s b) t
  exact (hasDerivWithinAt_const (c := ℓ x) (s := Icc s b) (x := t))

/-- The actual bounded Hermite diffusion evolution has weak generator `ℓ ∘ βD_N`. -/
theorem boundedYosidaDiffusionFamily_hasWeakGenerator {a b : ℝ}
    (β : ℝ → ℝ) (N : ℕ) (hβ : ContinuousOn β (Icc a b)) :
    (Evolution.dyson (identityEvolutionFamily (a := a) (b := b))
      (boundedPertOfContinuous (boundedYosidaDiffusionCoefficient β N)
        (by
          have hβc := continuousOn_complexCast hβ
          exact hβc.smul continuousOn_const))).HasWeakGenerator Set.univ
      (fun r ℓ => ℓ.comp (boundedYosidaDiffusionCoefficient β N r)) := by
  let A := boundedPertOfContinuous (boundedYosidaDiffusionCoefficient β N)
    (by
      have hβc := continuousOn_complexCast hβ
      exact hβc.smul continuousOn_const)
  have hbase := identityEvolutionFamily_hasWeakGenerator (a := a) (b := b)
  have hG : ∀ (ℓ : XG →L[ℂ] ℂ), ℓ ∈ Set.univ →
      ContinuousOn (fun _ : ℝ => (0 : XG →L[ℂ] ℂ)) (Icc a b) := by
    intro ℓ hℓ
    exact continuousOn_const
  have hA : ContinuousOn A.A (Icc a b) := by
    exact (by
      change ContinuousOn (boundedYosidaDiffusionCoefficient β N) (Icc a b)
      have hβc := continuousOn_complexCast hβ
      exact hβc.smul continuousOn_const)
  have h := Evolution.dyson_hasWeakGenerator
    (identityEvolutionFamily (a := a) (b := b)) A hbase hG hA
  intro (ℓ : XG →L[ℂ] ℂ) hℓ s x hs t ht
  simpa [A, boundedPertOfContinuous, zero_add] using h ℓ hℓ s x hs t ht



/-- The transport and scalar part of the bounded Yosida coefficient. -/
def boundedYosidaTransportCoefficient (T : XG →L[ℂ] XG) (lam κ : ℂ)
    (β : ℝ → ℝ) (r : ℝ) : XG →L[ℂ] XG :=
  T - lam • (1 : XG →L[ℂ] XG) - (((β r : ℝ) : ℂ) * κ) • (1 : XG →L[ℂ] XG)

private theorem continuousOn_boundedYosidaTransportCoefficient {a b : ℝ}
    (T : XG →L[ℂ] XG) (lam κ : ℂ) (β : ℝ → ℝ)
    (hβ : ContinuousOn β (Icc a b)) :
    ContinuousOn (boundedYosidaTransportCoefficient T lam κ β) (Icc a b) := by
  have hβc := continuousOn_complexCast hβ
  have hβκ : ContinuousOn (fun r => ((β r : ℝ) : ℂ) * κ) (Icc a b) :=
    hβc.mul continuousOn_const
  have hI : ContinuousOn (fun _ : ℝ => (1 : XG →L[ℂ] XG)) (Icc a b) := continuousOn_const
  have hT : ContinuousOn (fun _ : ℝ => T) (Icc a b) := continuousOn_const
  have hlam : ContinuousOn (fun _ : ℝ => lam) (Icc a b) := continuousOn_const
  have hlamI : ContinuousOn (fun r => lam • (1 : XG →L[ℂ] XG)) (Icc a b) := hlam.smul hI
  have hβκI : ContinuousOn
      (fun r => (((β r : ℝ) : ℂ) * κ) • (1 : XG →L[ℂ] XG)) (Icc a b) := hβκ.smul hI
  change ContinuousOn (fun r => T - lam • (1 : XG →L[ℂ] XG) -
    (((β r : ℝ) : ℂ) * κ) • (1 : XG →L[ℂ] XG)) (Icc a b)
  exact (hT.sub hlamI).sub hβκI

/-- The two-stage Dyson approximation, with its actual weak generator. -/
theorem boundedYosidaTransportDyson_hasWeakGenerator {a b : ℝ}
    (T : XG →L[ℂ] XG) (lam κ : ℂ) (β : ℝ → ℝ) (N : ℕ)
    (hβ : ContinuousOn β (Icc a b)) :
    (Evolution.dyson
      (Evolution.dyson (identityEvolutionFamily (a := a) (b := b))
        (boundedPertOfContinuous (boundedYosidaDiffusionCoefficient β N)
          (by
            have hβc := continuousOn_complexCast hβ
            exact hβc.smul continuousOn_const)))
      (boundedPertOfContinuous (boundedYosidaTransportCoefficient T lam κ β)
        (continuousOn_boundedYosidaTransportCoefficient T lam κ β hβ))).HasWeakGenerator
      Set.univ (fun r ℓ =>
        ℓ.comp (boundedYosidaDiffusionCoefficient β N r +
          boundedYosidaTransportCoefficient T lam κ β r)) := by
  let Aₙ := boundedPertOfContinuous (boundedYosidaDiffusionCoefficient β N)
    (by
      have hβc := continuousOn_complexCast hβ
      exact hβc.smul continuousOn_const)
  let Eₙ := Evolution.dyson (identityEvolutionFamily (a := a) (b := b)) Aₙ
  let A := boundedPertOfContinuous (boundedYosidaTransportCoefficient T lam κ β)
    (continuousOn_boundedYosidaTransportCoefficient T lam κ β hβ)
  have hE : Eₙ.HasWeakGenerator Set.univ
      (fun r ℓ => ℓ.comp (boundedYosidaDiffusionCoefficient β N r)) := by
    simpa [Eₙ, Aₙ] using boundedYosidaDiffusionFamily_hasWeakGenerator β N hβ
  have hG : ∀ (ℓ : XG →L[ℂ] ℂ), ℓ ∈ Set.univ →
      ContinuousOn (fun r => ℓ.comp (boundedYosidaDiffusionCoefficient β N r))
        (Icc a b) := by
    intro ℓ hℓ
    have hβc := continuousOn_complexCast hβ
    have hEq : (fun r => ℓ.comp (boundedYosidaDiffusionCoefficient β N r)) =
        (fun r => ((β r : ℝ) : ℂ) • (ℓ.comp (PlanarSpectral.Dyosida N))) := by
      funext r
      ext x
      simp only [boundedYosidaDiffusionCoefficient, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.smul_apply, map_smul, smul_eq_mul]
    rw [hEq]
    exact hβc.smul continuousOn_const
  have hA : ContinuousOn A.A (Icc a b) :=
    continuousOn_boundedYosidaTransportCoefficient T lam κ β hβ
  have h := Evolution.dyson_hasWeakGenerator Eₙ A hE hG hA
  intro ℓ hℓ s x hs t ht
  simpa [Eₙ, A, Aₙ, boundedPertOfContinuous, zero_add,
    ContinuousLinearMap.comp_apply] using h ℓ hℓ s x hs t ht



/-- The transport-generator term of the two-stage approximation is norm-continuous on a block. -/
theorem boundedYosidaTransportGenerator_continuous {a b : ℝ}
    (T : XG →L[ℂ] XG) (lam κ : ℂ) (β : ℝ → ℝ)
    (hβ : ContinuousOn β (Icc a b)) (ℓ : XG →L[ℂ] ℂ) :
    ContinuousOn (fun r => ℓ.comp (boundedYosidaTransportCoefficient T lam κ β r))
      (Icc a b) := by
  have hβc := continuousOn_complexCast hβ
  have hβκ : ContinuousOn (fun r => ((β r : ℝ) : ℂ) * κ) (Icc a b) :=
    hβc.mul continuousOn_const
  have hEq : (fun r => ℓ.comp (boundedYosidaTransportCoefficient T lam κ β r)) =
      (fun r => ℓ.comp T - lam • ℓ - (((β r : ℝ) : ℂ) * κ) • ℓ) := by
    funext r
    ext x
    simp [boundedYosidaTransportCoefficient, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.one_apply, smul_eq_mul]
  rw [hEq]
  have h1 : ContinuousOn (fun _ : ℝ => ℓ.comp T) (Icc a b) := continuousOn_const
  have h2 : ContinuousOn (fun _ : ℝ => lam • ℓ) (Icc a b) := continuousOn_const
  have h3 : ContinuousOn
      (fun r => (((β r : ℝ) : ℂ) * κ) • ℓ) (Icc a b) := hβκ.smul continuousOn_const
  exact (h1.sub h2).sub h3

/-- The full coefficient is the sum of its bounded diffusion and transport pieces. -/
theorem boundedYosidaCoefficient_eq_sum (T : XG →L[ℂ] XG) (lam κ : ℂ)
    (β : ℝ → ℝ) (N : ℕ) (r : ℝ) :
    boundedYosidaDiffusionCoefficient β N r +
      boundedYosidaTransportCoefficient T lam κ β r =
      boundedYosidaCoefficient T lam κ β N r := by
  ext x
  filter_upwards [] with y
  simp only [boundedYosidaDiffusionCoefficient, boundedYosidaTransportCoefficient,
    boundedYosidaCoefficient, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, smul_eq_mul]
  abel

/-- The two-stage weak generator is continuous in operator norm on every block. -/
theorem boundedYosidaTransportDyson_generator_continuous {a b : ℝ}
    (T : XG →L[ℂ] XG) (lam κ : ℂ) (β : ℝ → ℝ) (N : ℕ)
    (hβ : ContinuousOn β (Icc a b)) :
    ∀ (ℓ : XG →L[ℂ] ℂ), ℓ ∈ Set.univ →
      ContinuousOn (fun r => ℓ.comp
        (boundedYosidaDiffusionCoefficient β N r +
          boundedYosidaTransportCoefficient T lam κ β r)) (Icc a b) := by
  intro ℓ hℓ
  have hEq : (fun r => ℓ.comp
      (boundedYosidaDiffusionCoefficient β N r +
        boundedYosidaTransportCoefficient T lam κ β r)) =
      (fun r => ℓ.comp (boundedYosidaDiffusionCoefficient β N r) +
        ℓ.comp (boundedYosidaTransportCoefficient T lam κ β r)) := by
    funext r
    ext x
    simp [ContinuousLinearMap.comp_apply]
  rw [hEq]
  have hβc := continuousOn_complexCast hβ
  have hdiffEq : (fun r => ℓ.comp (boundedYosidaDiffusionCoefficient β N r)) =
      (fun r => ((β r : ℝ) : ℂ) • (ℓ.comp (PlanarSpectral.Dyosida N))) := by
    funext r
    ext x
    simp only [boundedYosidaDiffusionCoefficient, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, map_smul, smul_eq_mul]
  have hdiff : ContinuousOn
      (fun r => ℓ.comp (boundedYosidaDiffusionCoefficient β N r)) (Icc a b) := by
    rw [hdiffEq]
    exact hβc.smul continuousOn_const
  exact hdiff.add (boundedYosidaTransportGenerator_continuous T lam κ β hβ ℓ)

/-- A full-dual weak generator yields the vector mild equation and hence a pointwise vector
 derivative whenever its operator coefficient is continuous. -/
theorem weakGenerator_path_hasDerivWithinAt {a b s : ℝ}
    (U : EvolutionFamily XG a b) (C : ℝ → XG →L[ℂ] XG)
    (hU : U.HasWeakGenerator Set.univ (fun r ℓ => ℓ.comp (C r)))
    (hG : ∀ (ℓ : XG →L[ℂ] ℂ), ℓ ∈ Set.univ →
      ContinuousOn (fun r => ℓ.comp (C r)) (Icc a b))
    (hC : ContinuousOn C (Icc a b)) (has : a ≤ s) (x : XG)
    {t : ℝ} (ht : t ∈ Icc s b) :
    HasDerivWithinAt (fun r => U.U r s x) (C t (U.U t s x)) (Icc s b) t := by
  have hu : ContinuousOn (fun r => U.U r s x) (Icc s b) := U.continuousOn_fst has x
  have hg : ContinuousOn (fun r => C r (U.U r s x)) (Icc s b) :=
    (hC.mono (Icc_subset_Icc has le_rfl)).clm_apply hu
  have hweak : ∀ u ∈ Icc s b,
      U.U u s x = x + ∫ r in s..u, C r (U.U r s x) := by
    intro u hu'
    refine ext_inner_left ℂ fun z => ?_
    have hform := U.integral_form hU hG (ℓ := innerSL ℂ z) (Set.mem_univ (innerSL ℂ z))
      has hu'.1 hu'.2 x
    have hInt : IntervalIntegrable (fun r => C r (U.U r s x)) volume s u :=
      (hg.mono (Icc_subset_Icc le_rfl hu'.2)).intervalIntegrable_of_Icc hu'.1
    have hcomp := (innerSL ℂ z).intervalIntegral_comp_comm hInt
    simp only [ContinuousLinearMap.comp_apply] at hform
    rw [hcomp] at hform
    simpa only [innerSL_apply_apply, inner_add_right] using hform
  have hder := Evolution.hasDerivWithinAt_integral_Icc hg ht
  have hder' := hder.const_add x
  exact hder'.congr_of_mem hweak ht

/-- Sharp norm estimate from a continuous full-dual weak generator and its quadratic-form bound. -/
theorem weakGenerator_norm_le_exp {a b s t rate : ℝ}
    (U : EvolutionFamily XG a b) (C : ℝ → XG →L[ℂ] XG)
    (hU : U.HasWeakGenerator Set.univ (fun r ℓ => ℓ.comp (C r)))
    (hG : ∀ (ℓ : XG →L[ℂ] ℂ), ℓ ∈ Set.univ →
      ContinuousOn (fun r => ℓ.comp (C r)) (Icc a b))
    (hC : ContinuousOn C (Icc a b)) (has : a ≤ s) (hst : s ≤ t) (ht : t ≤ b)
    (hDiss : ∀ r ∈ Icc a b, ∀ z : XG,
      (⟪z, C r z⟫_ℂ).re ≤ rate * ‖z‖ ^ 2) (x : XG) :
    ‖U.U t s x‖ ≤ Real.exp (rate * (t - s)) * ‖x‖ := by
  let u : ℝ → XG := fun r => U.U r s x
  have hu : ContinuousOn u (Icc s t) :=
    (U.continuousOn_fst has x).mono (Icc_subset_Icc le_rfl ht)
  have hODE : ∀ τ ∈ Ico s t,
      HasDerivWithinAt u (C τ (u τ)) (Icc s t) τ := by
    intro τ hτ
    have hder := weakGenerator_path_hasDerivWithinAt U C hU hG hC has x
      ⟨hτ.1, (le_of_lt hτ.2).trans ht⟩
    exact hder.mono (Icc_subset_Icc le_rfl ht)
  have hDiss' : ∀ τ ∈ Ico s t,
      (⟪u τ, C τ (u τ)⟫_ℂ).re ≤ rate * ‖u τ‖ ^ 2 := by
    intro τ hτ
    exact hDiss τ ⟨has.trans hτ.1, (le_of_lt hτ.2).trans ht⟩ _
  calc
    ‖u t‖ ≤ Real.exp (rate * (t - s)) * ‖u s‖ :=
      continuousODE_norm_le_exp u C hu hODE hDiss' ⟨hst, le_rfl⟩
    _ = Real.exp (rate * (t - s)) * ‖x‖ := by simp [u, U.apply_diag ⟨has, hst.trans ht⟩]


/-- The actual two-stage bounded Yosida family obeys the sharp energy estimate. -/
theorem boundedYosidaTransportDyson_norm_le {a b s t δ : ℝ}
    (lam κ : ℂ) (β : ℝ → ℝ) (N : ℕ)
    (hβ : ContinuousOn β (Icc a b)) (hβ0 : ∀ r ∈ Icc a b, 0 ≤ β r)
    (hβδ : ∀ r ∈ Icc a b, β r ≤ δ) (hδ : 0 ≤ δ)
    (hT : ContinuousLinearMap.adjoint UnforcedLeray.B0087.imMulOp =
      -UnforcedLeray.B0087.imMulOp)
    (has : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) (x : XG) :
    ‖(Evolution.dyson
      (Evolution.dyson (identityEvolutionFamily (a := a) (b := b))
        (boundedPertOfContinuous (boundedYosidaDiffusionCoefficient β N)
          (by
            have hβc := continuousOn_complexCast hβ
            exact hβc.smul continuousOn_const)))
      (boundedPertOfContinuous (boundedYosidaTransportCoefficient
        UnforcedLeray.B0087.imMulOp lam κ β)
        (continuousOn_boundedYosidaTransportCoefficient
          UnforcedLeray.B0087.imMulOp lam κ β hβ))).U t s x‖ ≤
      Real.exp ((-lam.re + δ * |κ.re|) * (t - s)) * ‖x‖ := by
  let C := fun r => boundedYosidaDiffusionCoefficient β N r +
    boundedYosidaTransportCoefficient UnforcedLeray.B0087.imMulOp lam κ β r
  have hU := boundedYosidaTransportDyson_hasWeakGenerator
    UnforcedLeray.B0087.imMulOp lam κ β N hβ
  have hG := boundedYosidaTransportDyson_generator_continuous
    UnforcedLeray.B0087.imMulOp lam κ β N hβ
  have hDiff : ContinuousOn (boundedYosidaDiffusionCoefficient β N) (Icc a b) := by
    have hβc := continuousOn_complexCast hβ
    exact hβc.smul continuousOn_const
  have hTrans : ContinuousOn
      (boundedYosidaTransportCoefficient UnforcedLeray.B0087.imMulOp lam κ β)
      (Icc a b) :=
    continuousOn_boundedYosidaTransportCoefficient UnforcedLeray.B0087.imMulOp lam κ β hβ
  have hC : ContinuousOn C (Icc a b) := hDiff.add hTrans
  have hDiss : ∀ r ∈ Icc a b, ∀ z : XG,
      (⟪z, C r z⟫_ℂ).re ≤ (-lam.re + δ * |κ.re|) * ‖z‖ ^ 2 := by
    intro r hr z
    change (⟪z, (boundedYosidaDiffusionCoefficient β N r +
      boundedYosidaTransportCoefficient UnforcedLeray.B0087.imMulOp lam κ β r) z⟫_ℂ).re ≤ _
    rw [boundedYosidaCoefficient_eq_sum
      UnforcedLeray.B0087.imMulOp lam κ β N r]
    exact boundedYosidaCoefficient_quadratic_bound
      (T := UnforcedLeray.B0087.imMulOp) hT lam κ β N hβ0 hβδ hδ rfl r hr z
  exact weakGenerator_norm_le_exp _ C hU hG hC has hst ht hDiss x


end UnforcedLeray.Cons.G3b
