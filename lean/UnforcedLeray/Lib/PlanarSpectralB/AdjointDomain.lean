import UnforcedLeray.Lib.PlanarSpectralB.Oscillator
import UnforcedLeray.Lib.ComplexODEC
import UnforcedLeray.Blueprint.Construction.Planar

/-!
# Oscillator domain for a Gaussian-class angular-two profile

Generic bridge for the adjoint mode in the canonical construction. A smooth angular-two planar
field with polynomial-times-Gaussian bounds has an `X_G` profile in the domain of the closed
oscillator `D`; the action is the classical Gaussian operator, represented by its radial profile.
This repackages `D_classical_laguerre` with the specified profile representative rather than the
existential representative produced by the Schwartz-core proof.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace ComplexConjugate ContDiff

namespace UnforcedLeray.PlanarSpectral

open UnforcedLeray.ComplexODEC

/-- Radial Gaussian coefficient for the adjoint mode. If `φ(r)=β₀r²b(r²)`, then the normalized
adjoint profile is `r² * adjointBeta c β₀ J (r²)`, with `J` its direct-adjoint pairing. -/
def adjointBeta (c β₀ J : ℂ) (s : ℝ) : ℂ :=
  ((((4 * Real.pi)⁻¹ : ℝ) : ℂ) * conj β₀ / conj J) *
    (gaussE s * (conj (regB c s) * conj (resI c s)))

private theorem contDiff_conj_profile {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun s => conj (f s)) :=
  Complex.conjCLE.contDiff.comp hf

private theorem norm_iteratedDeriv_conj_profile {f : ℝ → ℂ} (m : ℕ) (s : ℝ) :
    ‖iteratedDeriv m (fun x => conj (f x)) s‖ = ‖iteratedDeriv m f s‖ := by
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have heq : (fun x => conj (f x)) = Complex.conjLIE ∘ f := rfl
  rw [heq]
  exact Complex.conjLIE.norm_iteratedFDeriv_comp_left f s m

private theorem derivBoundUpTo_conj_profile {w : ℝ → ℝ} {S : Set ℝ} {f : ℝ → ℂ} {k : ℕ}
    (hf : DerivBoundUpTo w S f k) :
    DerivBoundUpTo w S (fun s => conj (f s)) k := by
  intro m hm
  obtain ⟨C, N, hC, hb⟩ := hf m hm
  refine ⟨C, N, hC, fun s hs => ?_⟩
  rw [norm_iteratedDeriv_conj_profile m s]
  exact hb s hs

/-- Every radial derivative of `adjointBeta` is polynomially bounded times the Gaussian. -/
theorem derivBound_adjointBeta {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F)
    (β₀ J : ℂ) :
    DerivBound (fun s => Real.exp ((-1 / 4) * s)) (Ici 0) (adjointBeta c β₀ J) := by
  have hc := hF.im_ne_zero
  intro k
  have hreg := derivBoundUpTo_conj_profile (derivBound_regB hF k)
  have hres := derivBoundUpTo_conj_profile (derivBound_resI hc k)
  have hinner := hreg.mul (contDiff_conj_profile (contDiff_regB hc))
    (contDiff_conj_profile (contDiff_resI hc)) (fun _ _ => zero_le_one)
    (fun _ _ => zero_le_one) hres
  have hinner' : DerivBoundUpTo (fun _ => 1) (Ici 0)
      (fun s => conj (regB c s) * conj (resI c s)) k := by simpa using hinner
  have hgauss := (derivBound_gaussE k).mono_set (subset_univ (Ici 0))
  have houter := hgauss.mul contDiff_gaussE
    ((contDiff_conj_profile (contDiff_regB hc)).mul
      (contDiff_conj_profile (contDiff_resI hc)))
    (fun _ _ => (Real.exp_pos _).le) (fun _ _ => zero_le_one) hinner'
  have hscaled := houter.const_mul
    (((((4 * Real.pi)⁻¹ : ℝ) : ℂ) * conj β₀) / conj J)
  have heq : adjointBeta c β₀ J = fun s =>
      (((((4 * Real.pi)⁻¹ : ℝ) : ℂ) * conj β₀) / conj J) *
        (gaussE s * (conj (regB c s) * conj (resI c s))) := rfl
  rw [heq]
  simpa [mul_one] using hscaled

/-- Smoothness of the radial adjoint coefficient. -/
theorem contDiff_adjointBeta {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F)
    (β₀ J : ℂ) : ContDiff ℝ ∞ (adjointBeta c β₀ J) := by
  have hc := hF.im_ne_zero
  change ContDiff ℝ ∞ (fun s =>
    (((((4 * Real.pi)⁻¹ : ℝ) : ℂ) * conj β₀) / conj J) *
      (gaussE s * (conj (regB c s) * conj (resI c s))))
  exact contDiff_const.mul (contDiff_gaussE.mul
    ((contDiff_conj_profile (contDiff_regB hc)).mul
      (contDiff_conj_profile (contDiff_resI hc))))

/-- P9's angular-two estimate upgrades a radial Gaussian derivative bound to Cartesian
polynomial-times-Gaussian bounds on `ℂ`. -/
theorem norm_iteratedFDeriv_radialSq_le {β : ℝ → ℂ} (hβ : ContDiff ℝ ∞ β)
    (hb : DerivBound (fun s => Real.exp ((-1 / 4) * s)) (Ici 0) β) (k : ℕ) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ y : ℂ,
      ‖iteratedFDeriv ℝ k (fun y => y ^ 2 * β (‖y‖ ^ 2)) y‖ ≤
        C * (1 + ‖y‖) ^ N * Real.exp (-‖y‖ ^ 2 / 4) := by
  obtain ⟨C₀, N₀, hP9⟩ := Planar.norm_iteratedFDeriv_angularTwo_le k
  have hb2 : ∀ m : ℕ, ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ (m ≤ k → ∀ s ∈ Ici (0 : ℝ),
      ‖iteratedDeriv m β s‖ ≤ C * (1 + |s|) ^ N * Real.exp ((-1 / 4) * s)) := by
    intro m
    by_cases hm : m ≤ k
    · obtain ⟨C, N, hC, h⟩ := hb k m hm
      exact ⟨C, N, hC, fun _ => h⟩
    · exact ⟨0, 0, le_rfl, fun h => absurd h hm⟩
  choose Cm Nm hCm hm using hb2
  set Cs : ℝ := ∑ m ∈ Finset.range (k + 1), Cm m
  set Ns : ℕ := ∑ m ∈ Finset.range (k + 1), Nm m
  have hCs : 0 ≤ Cs := Finset.sum_nonneg fun m _ => hCm m
  refine ⟨max C₀ 0 * Cs, N₀ + 2 * Ns, mul_nonneg (le_max_right _ _) hCs, fun y => ?_⟩
  have hy0 : (0 : ℝ) ≤ ‖y‖ ^ 2 := by positivity
  have h1 : (1 : ℝ) ≤ 1 + |‖y‖ ^ 2| := one_le_one_add_abs _
  have hsq : 1 + |‖y‖ ^ 2| ≤ (1 + ‖y‖) ^ 2 := by
    rw [abs_of_nonneg hy0]
    nlinarith [norm_nonneg y]
  have hexp : Real.exp ((-1 / 4) * ‖y‖ ^ 2) = Real.exp (-‖y‖ ^ 2 / 4) := by
    congr 1
    ring
  have hsum : ∑ m ∈ Finset.range (k + 1), ‖iteratedDeriv m β (‖y‖ ^ 2)‖ ≤
      Cs * (1 + ‖y‖) ^ (2 * Ns) * Real.exp (-‖y‖ ^ 2 / 4) := by
    rw [mul_assoc, Finset.sum_mul]
    refine Finset.sum_le_sum fun m hmr => ?_
    have hmk : m ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hmr)
    refine (hm m hmk _ hy0).trans ?_
    rw [hexp, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (hCm m)
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    calc (1 + |‖y‖ ^ 2|) ^ Nm m ≤ (1 + |‖y‖ ^ 2|) ^ Ns :=
          pow_le_pow_right₀ h1 (Finset.single_le_sum (f := Nm)
            (fun _ _ => Nat.zero_le _) hmr)
      _ ≤ ((1 + ‖y‖) ^ 2) ^ Ns := pow_le_pow_left₀ (by linarith) hsq Ns
      _ = (1 + ‖y‖) ^ (2 * Ns) := by rw [← pow_mul]
  refine (hP9 β (hβ.of_le (natCast_le_infty k)) y).trans ?_
  calc C₀ * (1 + ‖y‖) ^ N₀ *
          ∑ m ∈ Finset.range (k + 1), ‖iteratedDeriv m β (‖y‖ ^ 2)‖
      ≤ max C₀ 0 * (1 + ‖y‖) ^ N₀ *
          ∑ m ∈ Finset.range (k + 1), ‖iteratedDeriv m β (‖y‖ ^ 2)‖ := by
        gcongr
        exact le_max_left _ _
      _ ≤ max C₀ 0 * (1 + ‖y‖) ^ N₀ *
          (Cs * (1 + ‖y‖) ^ (2 * Ns) * Real.exp (-‖y‖ ^ 2 / 4)) := by
        gcongr
      _ = max C₀ 0 * Cs * (1 + ‖y‖) ^ (N₀ + 2 * Ns) *
          Real.exp (-‖y‖ ^ 2 / 4) := by rw [pow_add]; ring

/-- The radial profile obtained from the manuscript's normalized adjoint formula, before the
angular factor is attached. It is definitionally the same expression used in the C1 reference
choice layer. -/
def adjointProfileFormula (c : ℂ) (F : ℝ → ℂ) (J : ℂ) (r : ℝ) : ℂ :=
  conj (modeRadial F r / ((GaussianVortex.radialOmega r : ℂ) - c)) /
    (Blueprint.Planar.gaussianWeightInv r : ℂ) / conj J

/-- Exact factorization of the normalized adjoint profile into `r²` times its Gaussian radial
coefficient, away from the measure-zero polar origin. -/
theorem adjointProfileFormula_eq_adjointBeta {c : ℂ} {F : ℝ → ℂ} {J β₀ : ℂ}
    (hβ : ∀ t, F t = β₀ * regLog c t) (hJ : J ≠ 0) {r : ℝ} (hr : 0 < r) :
    adjointProfileFormula c F J r = (r : ℂ) ^ 2 * adjointBeta c β₀ J (r ^ 2) := by
  have hrad := modeRadial_eq hβ hr
  have hΩ : GaussianVortex.radialOmega r = Real.exp (-(r ^ 2 / 4)) := rfl
  have hweight : Blueprint.Planar.gaussianWeightInv r =
      4 * Real.pi * Real.exp (r ^ 2 / 4) := rfl
  rw [adjointProfileFormula, hrad, hΩ, hweight, adjointBeta, gaussE, resI]
  simp only [map_div₀, map_mul, map_sub, map_inv₀, Complex.conj_ofReal]
  have hpi : (4 * Real.pi : ℝ) ≠ 0 := by positivity
  have hexp : Real.exp (r ^ 2 / 4) ≠ 0 := (Real.exp_pos _).ne'
  push_cast
  field_simp [hpi, hexp, hJ]
  set A : ℂ := conj β₀ * (r : ℂ) ^ 2 * conj (regB c (r ^ 2))
  set D : ℂ := Complex.exp (-(↑r ^ 2 / 4)) - conj c
  set E₁ : ℂ := Complex.exp (-(↑r ^ 2 / 4))
  set E₂ : ℂ := Complex.exp (↑r ^ 2 / 4)
  change A / D = A * E₁ * E₂ / D
  have hprod : Complex.exp (-(↑r ^ 2 / 4)) * Complex.exp (↑r ^ 2 / 4) = 1 := by
    rw [← Complex.exp_add]
    have he : -(↑r ^ 2 / 4) + ↑r ^ 2 / 4 = (0 : ℂ) := by ring
    rw [he, Complex.exp_zero]
  calc
    A / D = A * (1 / D) := by ring
    _ = A * (E₁ * E₂) * (1 / D) := by rw [hprod]; ring
    _ = A * E₁ * E₂ / D := by ring

/-- The smooth adjoint radial representative agrees with the literal normalized formula almost
everywhere for the Gaussian radial measure; the exceptional origin carries no mass. -/
theorem adjointProfileFormula_ae_eq_adjointBeta {c : ℂ} {F : ℝ → ℂ} {J β₀ : ℂ}
    (hβ : ∀ t, F t = β₀ * regLog c t) (hJ : J ≠ 0) :
    adjointProfileFormula c F J =ᵐ[B0010.xGMeasure]
      (fun r => (r : ℂ) ^ 2 * adjointBeta c β₀ J (r ^ 2)) := by
  filter_upwards [B0012.ae_xG_pos] with r hr
  exact adjointProfileFormula_eq_adjointBeta hβ hJ hr

/-- Polar angular-two profiles of the form `r² β(r²)` are the smooth Cartesian field
`(x₁ + i x₂)² β(x₁²+x₂²)`, including at the origin. -/
theorem angularTwoField_radialSq (β : ℝ → ℂ) (z : ℝ × ℝ) :
    B0010.angularTwoField (fun r => (r : ℂ) ^ 2 * β (r ^ 2)) z =
      (B0094.wz z) ^ 2 * β (B0094.sz z) := by
  by_cases hz : z = (0, 0)
  · subst z
    simp [B0010.angularTwoField, B0094.wz, B0094.sz]
  let ζ := Complex.equivRealProd.symm z
  have hr : 0 < ‖ζ‖ := norm_pos_iff.mpr (by
    intro hζ
    apply hz
    have hh := congrArg Complex.equivRealProd hζ
    simpa [ζ] using hh)
  have hnorm : Real.sqrt (z.1 ^ 2 + z.2 ^ 2) = ‖ζ‖ := by
    rw [show ζ = Complex.equivRealProd.symm z by rfl,
      Complex.equivRealProd_symm_apply, Complex.norm_def, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im,
      Complex.mul_im, zero_add]
    ring_nf
  have hre : ζ.re = z.1 := by simp [ζ]
  have him : ζ.im = z.2 := by simp [ζ]
  have hzpolar : ((‖ζ‖ * Real.cos (Complex.arg ζ),
      ‖ζ‖ * Real.sin (Complex.arg ζ)) : ℝ × ℝ) = z := by
    rw [Complex.norm_mul_cos_arg, Complex.norm_mul_sin_arg, hre, him]
  have hp := B0010.angularTwoField_polar
    (fun r => (r : ℂ) ^ 2 * β (r ^ 2)) hr (Complex.arg ζ)
  rw [hzpolar] at hp
  have hw : B0094.wz z = ζ := by simp [ζ, B0094.wz, Complex.equivRealProd_symm_apply]
  have hs : B0094.sz z = ‖ζ‖ ^ 2 := by
    rw [B0094.sz]
    rw [← hnorm]
    rw [Real.sq_sqrt (by positivity : 0 ≤ z.1 ^ 2 + z.2 ^ 2)]
  have hphase : ζ ^ 2 = ‖ζ‖ ^ 2 * Complex.exp (2 * Complex.I * Complex.arg ζ) := by
    calc
      ζ ^ 2 = (‖ζ‖ * Complex.exp (Complex.arg ζ * Complex.I)) ^ 2 := by
        exact (congrArg (fun x : ℂ => x ^ 2) (Complex.norm_mul_exp_arg_mul_I ζ)).symm
      _ = ‖ζ‖ ^ 2 * Complex.exp (2 * Complex.I * Complex.arg ζ) := by
        rw [B0094.exp_two_mul_I]
        ring
  calc
    B0010.angularTwoField (fun r => (r : ℂ) ^ 2 * β (r ^ 2)) z =
        (‖ζ‖ : ℂ) ^ 2 * β (‖ζ‖ ^ 2) *
          Complex.exp (2 * Complex.I * (Complex.arg ζ : ℂ)) := hp
    _ = (‖ζ‖ : ℂ) ^ 2 * Complex.exp (2 * Complex.I * Complex.arg ζ) *
        β (‖ζ‖ ^ 2) := by ring
    _ = ζ ^ 2 * β (‖ζ‖ ^ 2) := by rw [hphase]
    _ = B0094.wz z ^ 2 * β (B0094.sz z) := by rw [hw, hs]

/-- The Gaussian operator on the repaired angular-two profile `r² β(r²)` has the radial
coefficient `r² (4s β'' + (s+12)β' + 3β)(r²)`. This is the polar calculus bridge used to
identify the closed oscillator action with the profile operator. -/
theorem gaussianOperator_angularTwoField_radialSq {β : ℝ → ℂ}
    (hβ : ContDiff ℝ ∞ β) :
    B0093.gaussianOperator
        (B0010.angularTwoField (fun r => (r : ℂ) ^ 2 * β (r ^ 2))) =
      B0010.angularTwoField (fun r => (r : ℂ) ^ 2 *
        (4 * (r ^ 2 : ℝ) * deriv (deriv β) (r ^ 2) +
          ((r ^ 2 + 12 : ℝ) : ℂ) * deriv β (r ^ 2) + 3 * β (r ^ 2))) := by
  let β' : ℝ → ℂ := deriv β
  let β'' : ℝ → ℂ := deriv β'
  let A : ℝ → ℂ := fun s => 4 * (s : ℂ) * β'' s + ((s + 12 : ℝ) : ℂ) * β' s + 3 * β s
  have hβ1 : ∀ s, HasDerivAt β (β' s) s := by
    intro s
    exact (hβ.differentiable (by simp) s).hasDerivAt
  have hβ2 : ∀ s, HasDerivAt β' (β'' s) s := by
    intro s
    exact ((contDiff_infty_iff_deriv.mp hβ).2.differentiable (by simp) s).hasDerivAt
  have hfield (q : ℝ → ℂ) :
      B0010.angularTwoField (fun r => (r : ℂ) ^ 2 * q (r ^ 2)) = B0094.angF q := by
    funext z
    simpa [B0094.angF] using angularTwoField_radialSq q z
  rw [hfield β]
  funext z
  rw [B0094.gaussianOperator_angF β β' β'' hβ1 hβ2 z]
  calc
    B0094.wz z ^ 2 *
        (4 * (B0094.sz z : ℂ) * β'' (B0094.sz z) +
          (12 + (B0094.sz z : ℂ)) * β' (B0094.sz z) +
          3 * β (B0094.sz z)) = B0094.angF A z := by
      dsimp [B0094.angF, A, β', β'']
      congr 1
      push_cast
      ring
    _ = B0010.angularTwoField (fun r => (r : ℂ) ^ 2 * A (r ^ 2)) z :=
      congrFun (hfield A).symm z
    _ = B0010.angularTwoField (fun r => (r : ℂ) ^ 2 *
        (4 * (r ^ 2 : ℝ) * deriv (deriv β) (r ^ 2) +
          ((r ^ 2 + 12 : ℝ) : ℂ) * deriv β (r ^ 2) + 3 * β (r ^ 2))) z := by
      congr 1

/-- The repaired radial-square field has angular weight two. -/
theorem isAngularTwo_angularTwoField_radialSq (β : ℝ → ℂ) :
    B0094.IsAngularTwo (B0010.angularTwoField (fun r => (r : ℂ) ^ 2 * β (r ^ 2))) := by
  intro θ z
  rw [angularTwoField_radialSq, angularTwoField_radialSq, B0094.wz_rot, B0094.sz_rot,
    B0094.exp_two_mul_I]
  ring

private def radialSqCartesian (β : ℝ → ℂ) (y : ℂ) : ℂ :=
  y ^ 2 * β (‖y‖ ^ 2)

private theorem radialSqNorm (z : ℝ × ℝ) :
    Real.sqrt (z.1 ^ 2 + z.2 ^ 2) = ‖Complex.equivRealProdCLM.symm z‖ := by
  rw [Complex.equivRealProdCLM_symm_apply, Complex.norm_def, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im,
    Complex.mul_im, zero_add]
  ring_nf

private theorem radialSqNormL (z : ℝ × ℝ) :
    Real.sqrt (z.1 ^ 2 + z.2 ^ 2) = ‖(Complex.equivRealProdCLM.symm : (ℝ × ℝ) →L[ℝ] ℂ) z‖ := by
  exact radialSqNorm z

private theorem sz_eq_equivNormSq (z : ℝ × ℝ) :
    B0094.sz z = ‖Complex.equivRealProdCLM.symm z‖ ^ 2 := by
  rw [B0094.sz, ← radialSqNorm]
  rw [Real.sq_sqrt (by positivity : 0 ≤ z.1 ^ 2 + z.2 ^ 2)]

private theorem wz_eq_equiv (z : ℝ × ℝ) :
    B0094.wz z = Complex.equivRealProdCLM.symm z := by
  simp [B0094.wz, Complex.equivRealProdCLM_symm_apply]

private theorem angularTwoField_radialSq_eq_comp (β : ℝ → ℂ) :
    B0010.angularTwoField (fun r => (r : ℂ) ^ 2 * β (r ^ 2)) =
      fun z => radialSqCartesian β (Complex.equivRealProdCLM.symm z) := by
  funext z
  rw [angularTwoField_radialSq]
  rw [wz_eq_equiv, sz_eq_equivNormSq]
  rfl

/-- A radial Gaussian derivative bound yields the full Cartesian Gaussian class for the repaired
angular-two field. The plane/product coordinate change is included in the derivative bounds. -/
theorem gaussClass_angularTwo_of_derivBound {β : ℝ → ℂ} (hβ : ContDiff ℝ ∞ β)
    (hb : DerivBound (fun s => Real.exp ((-1 / 4) * s)) (Ici 0) β) :
    IsGaussClass (B0010.angularTwoField (fun r => (r : ℂ) ^ 2 * β (r ^ 2))) := by
  let L : (ℝ × ℝ) →L[ℝ] ℂ := Complex.equivRealProdCLM.symm
  let g : ℂ → ℂ := radialSqCartesian β
  have hg : ContDiff ℝ ∞ g := Planar.contDiff_angularTwo hβ
  have hcomp : B0010.angularTwoField (fun r => (r : ℂ) ^ 2 * β (r ^ 2)) = g ∘ L := by
    rw [angularTwoField_radialSq_eq_comp]
    rfl
  refine ⟨?_, fun n => ?_⟩
  · rw [hcomp]
    exact hg.comp L.contDiff
  · obtain ⟨C, N, hC, hbound⟩ := norm_iteratedFDeriv_radialSq_le hβ hb n
    let K : ℝ := max 1 ‖L‖
    have hK1 : 1 ≤ K := le_max_left _ _
    have hKL : ‖L‖ ≤ K := le_max_right _ _
    have hweight (z : ℝ × ℝ) : B0093.gaussianWeight z =
        (4 * Real.pi)⁻¹ * Real.exp (-‖L z‖ ^ 2 / 4) := by
      change B0093.gaussianWeight z =
        (4 * Real.pi)⁻¹ * Real.exp (-‖Complex.equivRealProdCLM.symm z‖ ^ 2 / 4)
      rw [B0093.gaussianWeight, UnforcedLeray.GaussianVortex.planarGaussian,
        UnforcedLeray.GaussianVortex.radiusSq, ← radialSqNorm]
      rw [Real.sq_sqrt (by positivity : 0 ≤ z.1 ^ 2 + z.2 ^ 2)]
      congr 1
      ring_nf
    have hderiv (z : ℝ × ℝ) :
        ‖iteratedFDeriv ℝ n (g ∘ L) z‖ ≤
          ‖iteratedFDeriv ℝ n g (L z)‖ * ‖L‖ ^ n := by
      rw [L.iteratedFDeriv_comp_right hg z (natCast_le_infty n)]
      calc
        _ ≤ ‖iteratedFDeriv ℝ n g (L z)‖ *
            ∏ _ : Fin n, ‖L‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
        _ = ‖iteratedFDeriv ℝ n g (L z)‖ * ‖L‖ ^ n := by simp
    have hpoly (z : ℝ × ℝ) : 1 + ‖L z‖ ≤ K * (1 + ‖z‖) := by
      calc
        1 + ‖L z‖ ≤ 1 + ‖L‖ * ‖z‖ := by gcongr; exact L.le_opNorm z
        _ ≤ K * (1 + ‖z‖) := by nlinarith [norm_nonneg z]
    have hpi : (4 * Real.pi : ℝ) ≠ 0 := by positivity
    refine ⟨(4 * Real.pi) * C * ‖L‖ ^ n * K ^ N, N, fun z => ?_⟩
    rw [hcomp]
    calc
      ‖iteratedFDeriv ℝ n (g ∘ L) z‖ ≤
          (C * (1 + ‖L z‖) ^ N * Real.exp (-‖L z‖ ^ 2 / 4)) * ‖L‖ ^ n := by
        exact (hderiv z).trans (mul_le_mul_of_nonneg_right (hbound (L z))
          (pow_nonneg (norm_nonneg _) _))
      _ ≤ ((4 * Real.pi) * C * ‖L‖ ^ n * K ^ N) *
          (1 + ‖z‖) ^ N * ((4 * Real.pi)⁻¹ * Real.exp (-‖L z‖ ^ 2 / 4)) := by
        calc
          _ ≤ C * (K * (1 + ‖z‖)) ^ N * Real.exp (-‖L z‖ ^ 2 / 4) * ‖L‖ ^ n := by
            have hpow : (1 + ‖L z‖) ^ N ≤ (K * (1 + ‖z‖)) ^ N :=
              pow_le_pow_left₀ (by positivity) (hpoly z) N
            gcongr
          _ = ((4 * Real.pi) * C * ‖L‖ ^ n * K ^ N) *
              (1 + ‖z‖) ^ N * ((4 * Real.pi)⁻¹ * Real.exp (-‖L z‖ ^ 2 / 4)) := by
            rw [mul_pow]
            field_simp [hpi]
      _ = ((4 * Real.pi) * C * ‖L‖ ^ n * K ^ N) *
          (1 + ‖z‖) ^ N * B0093.gaussianWeight z := by
        rw [hweight]

/-- The repaired Cartesian representative of the actual adjoint coefficient belongs to the
Gaussian class, without a Gaussian-class premise. -/
theorem gaussClass_adjointBeta {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F)
    (β₀ J : ℂ) :
    IsGaussClass (B0010.angularTwoField
      (fun r => (r : ℂ) ^ 2 * adjointBeta c β₀ J (r ^ 2))) :=
  gaussClass_angularTwo_of_derivBound (contDiff_adjointBeta hF β₀ J)
    (derivBound_adjointBeta hF β₀ J)

/-- A Gaussian-class angular-two profile has its prescribed `X_G` representative in `D.domain`.
The image under `D` is represented by the radial profile of the classical planar oscillator
`Δ + ½ y·∇ + 2`. -/
theorem exists_Ddomain_of_gaussClass_profile {f : ℝ → ℂ}
    (hf : IsGaussClass (B0010.angularTwoField f))
    (ha : B0094.IsAngularTwo (B0010.angularTwoField f))
    (hm : MemLp f 2 B0010.xGMeasure) :
    ∃ h : (hm.toLp f) ∈ B0094.D.domain, ∃ DF : B0010.XG,
      B0094.D ⟨hm.toLp f, h⟩ = DF ∧
      ∃ df : ℝ → ℂ, B0010.angularTwoField df =
          B0093.gaussianOperator (B0010.angularTwoField f) ∧
        (⇑DF : ℝ → ℂ) =ᵐ[B0010.xGMeasure] df := by
  obtain ⟨F, DF, hF, hD, hclassical, hcoeff⟩ := D_classical_laguerre hf ha
  obtain ⟨f₂, df₂, hfield, hDfield, hFae, hDFae⟩ := hclassical
  have hf₂ : f₂ =ᵐ[B0010.xGMeasure] f := by
    filter_upwards [B0012.ae_xG_pos] with r hr
    have h := congrFun hfield (r, 0)
    rw [B0010.angularTwoField_profile f₂ hr,
      B0010.angularTwoField_profile f hr] at h
    exact h
  have hrep : (hm.toLp f : B0010.XG) = F := by
    apply Lp.ext
    filter_upwards [hm.coeFn_toLp, hFae, hf₂] with r h1 h2 h3
    rw [h1, h2, h3]
  refine ⟨?_, DF, ?_, df₂, hDfield, ?_⟩
  · rw [hrep]
    exact hF
  · simpa [hrep] using hD
  · filter_upwards [hDFae] with r hr
    exact hr

/-- The closed oscillator domain transfers to any `MemLp` representative that is AE equal to a
Gaussian-class angular-two radial profile. This is the interface used for the literal adjoint
formula, whose value at the polar origin need not be the smooth representative's value. -/
theorem exists_Ddomain_of_gaussClass_profile_ae {f g : ℝ → ℂ}
    (hfg : f =ᵐ[B0010.xGMeasure] g)
    (hg : IsGaussClass (B0010.angularTwoField g))
    (ha : B0094.IsAngularTwo (B0010.angularTwoField g))
    (hmf : MemLp f 2 B0010.xGMeasure) :
    ∃ h : (hmf.toLp f) ∈ B0094.D.domain, ∃ DF : B0010.XG,
      B0094.D ⟨hmf.toLp f, h⟩ = DF ∧
      ∃ df : ℝ → ℂ, B0010.angularTwoField df =
          B0093.gaussianOperator (B0010.angularTwoField g) ∧
        (⇑DF : ℝ → ℂ) =ᵐ[B0010.xGMeasure] df := by
  have hmg : MemLp g 2 B0010.xGMeasure :=
    (MeasureTheory.memLp_congr_ae hfg).1 hmf
  obtain ⟨hG, DF, hD, df, hDfield, hDFae⟩ :=
    exists_Ddomain_of_gaussClass_profile hg ha hmg
  have hrep : (hmg.toLp g : B0010.XG) = hmf.toLp f := by
    apply Lp.ext
    filter_upwards [hmg.coeFn_toLp, hmf.coeFn_toLp, hfg] with r hg' hf' hfg'
    rw [hg', hf', hfg']
  refine ⟨?_, DF, ?_, df, hDfield, hDFae⟩
  · rw [← hrep]
    exact hG
  · simpa [hrep] using hD

/-- The actual growing vorticity profile agrees almost everywhere with the repaired Cartesian
profile `r² β(r²)`, where `β = β₀ κ_c b`. -/
theorem modeVort_ae_eq_modeBeta {c : ℂ} {F : ℝ → ℂ} {β₀ : ℂ}
    (hβ : ∀ t, F t = β₀ * regLog c t) :
    modeVort c F =ᵐ[B0010.xGMeasure]
      (fun r => (r : ℂ) ^ 2 * modeBeta c β₀ (r ^ 2)) := by
  filter_upwards [B0012.ae_xG_pos] with r hr
  have hq := modeQ_eq hβ (r : ℂ)
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  simpa [modeQ, Planar.NUE.Ang.ofProfile, Planar.NUE.Ang.angPhase,
    Real.norm_eq_abs, abs_of_pos hr, hrC] using hq

/-- The actual growing mode's closed-domain action is represented by the classical Gaussian
operator applied to its repaired Cartesian profile. -/
theorem exists_modeVort_Ddomain_action {c : ℂ} {F : ℝ → ℂ}
    (hF : WholeLineData c F) :
    ∃ β₀ : ℂ, ∃ h : (memLp_modeVort_XG hF).toLp (modeVort c F) ∈ B0094.D.domain,
      ∃ DF : B0010.XG,
        B0094.D ⟨(memLp_modeVort_XG hF).toLp (modeVort c F), h⟩ = DF ∧
        (⇑DF : ℝ → ℂ) =ᵐ[B0010.xGMeasure] (fun r => (r : ℂ) ^ 2 *
          (4 * (r ^ 2 : ℝ) * deriv (deriv (modeBeta c β₀)) (r ^ 2) +
            ((r ^ 2 + 12 : ℝ) : ℂ) * deriv (modeBeta c β₀) (r ^ 2) +
            3 * modeBeta c β₀ (r ^ 2))) := by
  obtain ⟨β₀, -, hβ⟩ := exists_mode_eq_regLog hF
  refine ⟨β₀, ?_⟩
  obtain ⟨hD, DF, hDact, df, hfield, hDFae⟩ := exists_Ddomain_of_gaussClass_profile_ae
    (modeVort_ae_eq_modeBeta (fun t => (hβ t).1))
    (gaussClass_angularTwo_of_derivBound
      (contDiff_modeBeta hF.im_ne_zero β₀) (derivBound_modeBeta hF β₀))
    (isAngularTwo_angularTwoField_radialSq (modeBeta c β₀))
    (memLp_modeVort_XG hF)
  refine ⟨hD, DF, hDact, ?_⟩
  have hgauss := gaussianOperator_angularTwoField_radialSq
    (contDiff_modeBeta hF.im_ne_zero β₀)
  have hprofile : B0010.angularTwoField df =
      B0010.angularTwoField (fun r => (r : ℂ) ^ 2 *
        (4 * (r ^ 2 : ℝ) * deriv (deriv (modeBeta c β₀)) (r ^ 2) +
          ((r ^ 2 + 12 : ℝ) : ℂ) * deriv (modeBeta c β₀) (r ^ 2) +
          3 * modeBeta c β₀ (r ^ 2))) := by
    rw [hfield, hgauss]
  filter_upwards [hDFae, B0012.ae_xG_pos] with r hdf hr
  have h := congrFun hprofile (r, 0)
  rw [B0010.angularTwoField_profile df hr,
    B0010.angularTwoField_profile (fun r => (r : ℂ) ^ 2 *
      (4 * (r ^ 2 : ℝ) * deriv (deriv (modeBeta c β₀)) (r ^ 2) +
        ((r ^ 2 + 12 : ℝ) : ℂ) * deriv (modeBeta c β₀) (r ^ 2) +
        3 * modeBeta c β₀ (r ^ 2))) hr] at h
  exact hdf.trans h

/-- The actual growing mode belongs to the closed oscillator domain; this has no Gaussian-class
premise. -/
theorem modeVort_mem_Ddomain {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F) :
    (memLp_modeVort_XG hF).toLp (modeVort c F) ∈ B0094.D.domain := by
  obtain ⟨_, hD, DF, hDact, hdf⟩ := exists_modeVort_Ddomain_action hF
  exact hD

end UnforcedLeray.PlanarSpectral
