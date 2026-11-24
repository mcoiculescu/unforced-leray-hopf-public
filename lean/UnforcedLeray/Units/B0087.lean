import UnforcedLeray.Units.B0012
import UnforcedLeray.Infra.WeaklyNullCompact
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# B0087: `L₀` is bounded on `X_G` and a compact perturbation of imaginary multiplication

Blueprint unit B0087 (`unlabeled:1424`, old ledger C04), `paper/main.tex` lines 1424--1432, in
the proof "Gaussian boundedness and the complement estimate" of `sec:st18-1584`. Dependencies:
B0010 (`eq:st18-t00005`, the space `X_G`), B0011 (`eq:st18-t00007`, the Green inverse `R`),
B0012 (`eq:st18-t00006`, the bounded generator `L₀ = -2iΩ + 2ikR`).

The manuscript says (lines 1424--1432):
* (a) "Multiplication by `-2iΩ` is bounded and skew-adjoint."
* (b) "The interaction `2ikR` is compact. Indeed, after the unitary change `f ↦ f/√G`, its
  kernel on `L²(r dr)` is `-(i/2) (k(r)/√G(r)) (min(r,s)/max(r,s))² √G(s)`. The square integral
  is bounded by a constant times `(∫|k|²G⁻¹ r dr)(∫ G s ds) < ∞`."
* (c) "Thus `L₀` is bounded and a compact perturbation of imaginary multiplication."

**Formalization** (all on B0010's `XG = L²((0,∞), G⁻¹ r dr; ℂ)`, with B0012's operators).
* (a) `imMulOp = (-2i) • omegaOp` is multiplication by the purely imaginary bounded multiplier
  `imMultiplier r = -2iΩ(r)` (`coeFn_imMulOp`, `re_imMultiplier`, `norm_imMulOp_le`), and it is
  skew-adjoint: `adjoint_imMulOp : imMulOp† = -imMulOp`, `imMulOp_mem_skewAdjoint`.
* (b) `interactionOp = (2i) • B0012.kROp` is `f ↦ 2ikRf` (`coeFn_interactionOp`) and is compact
  (`isCompactOperator_interactionOp`). The unitary change is `U : XG ≃ₗᵢ[ℂ] L2r`,
  `L2r = L²((0,∞), r dr; ℂ)`, with `U f = f/√G` (`coeFn_U`) and `U⁻¹ g = √G g`
  (`coeFn_U_symm`). The conjugated operator is the integral operator with kernel `hsKernel`
  relative to `s ds` (`conj_interactionOp_eq_kernel`, with absolutely convergent integral by
  `integrable_hsKernel_mul`), and the square integral of the kernel against `r dr ⊗ s ds` is at
  most `¼ (∫|k|²G⁻¹ r dr)(∫ G s ds)` and finite (`hsKernel_sq_lintegral_le`,
  `hsKernel_sq_lintegral_lt_top`). All integrals of nonnegative quantities are lintegrals, so no
  junk value enters.
* (c) `L0_eq : L0 = imMulOp + interactionOp`, and `L0_bounded_and_compactPerturbation`: `L₀` is
  bounded and `IsCompactPerturbationOfImagMul L0` (there is a bounded measurable purely
  imaginary multiplier whose multiplication operator differs from `L₀` by a compact operator).

**Proof route for compactness.** The manuscript deduces compactness from the Hilbert–Schmidt
property of the kernel. Hilbert–Schmidt integral operators are not in Mathlib, so compactness is
proved directly (the kernel facts are still proved as stated): by
`Infra.WeaklyNullCompact.isCompactOperator_of_forall_weaklyNull_of_norm_le_one` it suffices that
`‖kR xₙ‖ → 0` for weakly null `xₙ` with `‖xₙ‖ ≤ 1`. For `r > 0`,
`Rxₙ(r) = -¼ ⟪h_r, xₙ⟫ → 0` (B0012 `Psi_eq_pairing`, `h_r = rep r ∈ X_G`), and
`|k(r) Rxₙ(r)|² G⁻¹ r ≤ (¼‖G‖)² |k(r)|² G⁻¹ r` (B0012 `norm_R_coe_le`) is integrable since
`k ∈ X_G`; dominated convergence gives `‖kRxₙ‖² → 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace

namespace UnforcedLeray.B0087

open B0010 B0011 B0012 GaussianVortex

/-! ## (a) Multiplication by `-2iΩ` is bounded and skew-adjoint -/

/-- The purely imaginary multiplier `-2iΩ(r)` of `L₀` (tex lines 680, 1424). -/
def imMultiplier (r : ℝ) : ℂ := -2 * Complex.I * (radialOmega r : ℂ)

theorem re_imMultiplier (r : ℝ) : (imMultiplier r).re = 0 := by
  simp [imMultiplier]

theorem continuous_imMultiplier : Continuous imMultiplier := by
  unfold imMultiplier
  exact continuous_const.mul (Complex.continuous_ofReal.comp continuous_radialOmega)

theorem norm_imMultiplier_le (r : ℝ) : ‖imMultiplier r‖ ≤ 2 := by
  have h1 := radialOmega_le_one r
  have h0 := (radialOmega_pos r).le
  rw [imMultiplier, norm_mul, norm_mul, norm_neg, Complex.norm_I, Complex.norm_real,
    Real.norm_of_nonneg h0]
  norm_num
  linarith

/-- Multiplication by `-2iΩ` on `X_G` (tex line 1424). -/
def imMulOp : XG →L[ℂ] XG := (-2 * Complex.I) • omegaOp

/-- `imMulOp` is multiplication by `-2iΩ(r)`. -/
theorem coeFn_imMulOp (f : XG) :
    ⇑(imMulOp f) =ᵐ[xGMeasure] fun r => imMultiplier r * f r := by
  have e : imMulOp f = (-2 * Complex.I) • omegaOp f := rfl
  rw [e]
  filter_upwards [Lp.coeFn_smul (-2 * Complex.I) (omegaOp f), coeFn_omegaOp f] with r h1 h2
  rw [h1, Pi.smul_apply, h2, smul_eq_mul, imMultiplier]
  ring

/-- **(a), boundedness** (tex line 1424): `‖-2iΩ f‖ ≤ 2 ‖f‖`. -/
theorem norm_imMulOp_le (f : XG) : ‖imMulOp f‖ ≤ 2 * ‖f‖ := by
  have e : imMulOp f = (-2 * Complex.I) • omegaOp f := rfl
  have n1 : ‖(-2 * Complex.I)‖ = 2 := by
    rw [norm_mul, norm_neg, Complex.norm_I]; norm_num
  rw [e, norm_smul, n1]
  exact mul_le_mul_of_nonneg_left (norm_omegaOp_le f) (by norm_num)

/-- Multiplication by the real function `Ω` is symmetric on `X_G`. -/
theorem inner_omegaOp (f g : XG) : ⟪omegaOp f, g⟫_ℂ = ⟪f, omegaOp g⟫_ℂ := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_omegaOp f, coeFn_omegaOp g] with r h1 h2
  rw [h1, h2, RCLike.inner_apply', RCLike.inner_apply', map_mul, Complex.conj_ofReal]
  ring

theorem adjoint_omegaOp : ContinuousLinearMap.adjoint omegaOp = omegaOp :=
  ((ContinuousLinearMap.eq_adjoint_iff omegaOp omegaOp).2 inner_omegaOp).symm

/-- **(a), skew-adjointness** (tex line 1424): the adjoint of multiplication by `-2iΩ` on
`X_G` is its negative. -/
theorem adjoint_imMulOp : ContinuousLinearMap.adjoint imMulOp = -imMulOp := by
  refine ((ContinuousLinearMap.eq_adjoint_iff (-imMulOp) imMulOp).2 fun f g => ?_).symm
  have e1 : (-imMulOp) f = -((-2 * Complex.I) • omegaOp f) := rfl
  have e2 : imMulOp g = (-2 * Complex.I) • omegaOp g := rfl
  rw [e1, e2, inner_neg_left, inner_smul_left, inner_smul_right, inner_omegaOp]
  simp only [map_mul, map_neg, Complex.conj_I, map_ofNat]
  ring

/-- **(a), skew-adjointness**, in the star-algebra form: `imMulOp ∈ skewAdjoint`. -/
theorem imMulOp_mem_skewAdjoint : imMulOp ∈ skewAdjoint (XG →L[ℂ] XG) := by
  rw [skewAdjoint.mem_iff, ContinuousLinearMap.star_eq_adjoint, adjoint_imMulOp]

/-! ## (b) The interaction `2ikR` is compact -/

/-- The interaction `f ↦ 2ikRf` of `L₀` (tex lines 680, 1424). -/
def interactionOp : XG →L[ℂ] XG := (2 * Complex.I) • kROp

theorem coeFn_interactionOp (f : XG) :
    ⇑(interactionOp f) =ᵐ[xGMeasure] fun r => 2 * Complex.I * (radialK r : ℂ) * R (⇑f) r := by
  have e : interactionOp f = (2 * Complex.I) • kROp f := rfl
  rw [e]
  filter_upwards [Lp.coeFn_smul (2 * Complex.I) (kROp f), coeFn_kROp f] with r h1 h2
  rw [h1, Pi.smul_apply, h2, smul_eq_mul]
  ring

/-- `L₀ = -2iΩ + 2ikR` (B0012, tex line 680). -/
theorem L0_eq : L0 = imMulOp + interactionOp := rfl

/-- For a weakly null sequence, `Rxₙ(r) → 0` at every `r > 0`. -/
theorem tendsto_R_of_weaklyNull {x : ℕ → XG}
    (hx : ∀ y : XG, Tendsto (fun n => ⟪y, x n⟫_ℂ) atTop (𝓝 0)) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun n => R (⇑(x n)) r) atTop (𝓝 0) := by
  have e : ∀ n, R (⇑(x n)) r = -(1 / 4 : ℂ) * ⟪(memLp_rep hr).toLp (rep r), x n⟫_ℂ := fun n => by
    rw [R_eq_Psi (wprof_coe (x n)) hr, Psi_eq_pairing (x n) hr, pairing_eq_inner]
  simp_rw [e]
  simpa using (hx ((memLp_rep hr).toLp (rep r))).const_mul (-(1 / 4 : ℂ))

theorem continuous_xGWeight : Continuous fun r : ℝ => (radialGaussianWeight r)⁻¹ * r :=
  (continuous_radialGaussianWeight.inv₀ fun r => (radialGaussianWeight_pos r).ne').mul
    continuous_id

theorem norm_sq_kROp (f : XG) :
    ‖kROp f‖ ^ 2 =
      ∫ r in Ioi 0, ‖(radialK r : ℂ) * R (⇑f) r‖ ^ 2 * ((radialGaussianWeight r)⁻¹ * r) :=
  norm_sq_toLp (memLp_kR f)

theorem integrableOn_k_sq :
    IntegrableOn (fun r => ‖(radialK r : ℂ)‖ ^ 2 * ((radialGaussianWeight r)⁻¹ * r)) (Ioi 0) :=
  (memLp_iff_integrableOn
    (Complex.continuous_ofReal.comp continuous_radialK).aestronglyMeasurable).1 memLp_k

/-- **(b)** (tex line 1424): `f ↦ kRf` is a compact operator on `X_G`. -/
theorem isCompactOperator_kROp : IsCompactOperator kROp := by
  refine Infra.WeaklyNullCompact.isCompactOperator_of_forall_weaklyNull_of_norm_le_one kROp
    fun x hx1 hx => ?_
  set C : ℝ := 1 / 4 * ‖gaussLp‖ with hC
  have hC0 : 0 ≤ C := by positivity
  have hsq : Tendsto (fun n => ‖kROp (x n)‖ ^ 2) atTop (𝓝 0) := by
    simp_rw [norm_sq_kROp]
    have hlim := tendsto_integral_of_dominated_convergence (μ := volume.restrict (Ioi (0 : ℝ)))
      (F := fun n r => ‖(radialK r : ℂ) * R (⇑(x n)) r‖ ^ 2 * ((radialGaussianWeight r)⁻¹ * r))
      (f := fun _ => (0 : ℝ))
      (fun r => C ^ 2 * (‖(radialK r : ℂ)‖ ^ 2 * ((radialGaussianWeight r)⁻¹ * r)))
      ?_ (integrableOn_k_sq.const_mul _) ?_ ?_
    · rwa [integral_zero] at hlim
    · intro n
      exact (((Complex.continuous_ofReal.comp continuous_radialK).aestronglyMeasurable.mul
        ((continuousOn_R (x n)).aestronglyMeasurable measurableSet_Ioi)).norm.pow 2).mul
        continuous_xGWeight.aestronglyMeasurable
    · intro n
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun r hr => ?_
      have hr' : (0 : ℝ) < r := hr
      have hRC : ‖R (⇑(x n)) r‖ ≤ C :=
        (norm_R_coe_le (x n) hr').trans (mul_le_of_le_one_right hC0 (hx1 n))
      have hw0 : 0 ≤ (radialGaussianWeight r)⁻¹ * r :=
        mul_nonneg (inv_nonneg.2 (radialGaussianWeight_pos r).le) hr'.le
      have hR2 : ‖R (⇑(x n)) r‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hRC 2
      rw [Real.norm_of_nonneg (by positivity), norm_mul, mul_pow]
      calc ‖(radialK r : ℂ)‖ ^ 2 * ‖R (⇑(x n)) r‖ ^ 2 * ((radialGaussianWeight r)⁻¹ * r)
          ≤ ‖(radialK r : ℂ)‖ ^ 2 * C ^ 2 * ((radialGaussianWeight r)⁻¹ * r) := by gcongr
        _ = C ^ 2 * (‖(radialK r : ℂ)‖ ^ 2 * ((radialGaussianWeight r)⁻¹ * r)) := by ring
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun r hr => ?_
      have h := tendsto_R_of_weaklyNull hx (r := r) hr
      have h2 := (((h.const_mul (radialK r : ℂ)).norm).pow 2).mul_const
        ((radialGaussianWeight r)⁻¹ * r)
      simpa using h2
  have h := (Real.continuous_sqrt.tendsto 0).comp hsq
  simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using h

/-- **(b)** (tex line 1424): "The interaction `2ikR` is compact." -/
theorem isCompactOperator_interactionOp : IsCompactOperator interactionOp := by
  have h := isCompactOperator_kROp.smul (2 * Complex.I)
  unfold interactionOp
  rw [FunLike.coe_smul]
  exact h

/-! ## (b) The unitary change `f ↦ f/√G` onto `L²((0,∞), r dr)` -/

/-- The density `r` of `r dr` on `(0, ∞)`. -/
def rDensity (r : ℝ) : ℝ≥0 := Real.toNNReal r

theorem measurable_rDensity : Measurable rDensity := measurable_real_toNNReal

/-- The measure `r dr` on `(0, ∞)` (tex line 1425, "`L²(r dr)`"). -/
def rMeasure : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity (fun r => (rDensity r : ℝ≥0∞))

/-- `L²((0,∞), r dr; ℂ)` (tex line 1425). -/
abbrev L2r : Type := Lp ℂ 2 rMeasure

theorem rMeasure_ac : rMeasure ≪ volume.restrict (Ioi (0 : ℝ)) :=
  withDensity_absolutelyContinuous _ _

theorem restrict_ac_rMeasure : volume.restrict (Ioi (0 : ℝ)) ≪ rMeasure := by
  refine withDensity_absolutelyContinuous' measurable_rDensity.coe_nnreal_ennreal.aemeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun r hr => ?_
  simp only [rDensity, ne_eq, ENNReal.coe_eq_zero, Real.toNNReal_eq_zero, not_le]
  exact hr

theorem ae_rMeasure_pos : ∀ᵐ r ∂rMeasure, (0 : ℝ) < r :=
  rMeasure_ac.ae_le (ae_restrict_mem measurableSet_Ioi)

/-- Membership in `L²(r dr)`: `∫₀^∞ |h|² r dr < ∞`. -/
theorem memLp_r_iff {h : ℝ → ℂ} (hm : AEStronglyMeasurable h (volume.restrict (Ioi 0))) :
    MemLp h 2 rMeasure ↔ IntegrableOn (fun r => ‖h r‖ ^ 2 * r) (Ioi 0) := by
  have hm' : AEStronglyMeasurable h rMeasure := hm.mono_ac rMeasure_ac
  rw [memLp_two_iff_integrable_sq_norm hm', rMeasure,
    integrable_withDensity_iff_integrable_smul measurable_rDensity]
  refine integrableOn_congr_fun (fun r hr => ?_) measurableSet_Ioi
  have hr' : (0 : ℝ) ≤ r := le_of_lt hr
  simp only [NNReal.smul_def, rDensity, Real.coe_toNNReal _ hr', smul_eq_mul]
  ring

/-- The `L²` norm as an integral, for any measure on `ℝ`. -/
theorem norm_sq_Lp_eq_integral {μ : Measure ℝ} (F : Lp ℂ 2 μ) :
    ‖F‖ ^ 2 = ∫ x, ‖F x‖ ^ 2 ∂μ := by
  have h := (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) F).symm
  rw [L2.inner_def] at h
  have e : ∀ x, ⟪F x, F x⟫_ℂ = ((‖F x‖ ^ 2 : ℝ) : ℂ) := fun x => by
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  simp_rw [e, integral_complex_ofReal] at h
  have h' : ((‖F‖ ^ 2 : ℝ) : ℂ) = ((∫ x, ‖F x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [Complex.ofReal_pow]
    exact h
  exact Complex.ofReal_injective h'

theorem norm_sq_toLp_r {h : ℝ → ℂ} (hf : MemLp h 2 rMeasure) :
    ‖hf.toLp h‖ ^ 2 = ∫ r in Ioi 0, ‖h r‖ ^ 2 * r := by
  rw [norm_sq_Lp_eq_integral, integral_congr_ae (hf.coeFn_toLp.mono fun x hx => by
      rw [hx]), rMeasure, integral_withDensity_eq_integral_smul measurable_rDensity]
  refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  have hr' : (0 : ℝ) ≤ r := le_of_lt hr
  simp only [NNReal.smul_def, rDensity, Real.coe_toNNReal _ hr',
    smul_eq_mul]
  ring

theorem norm_sq_XG (f : XG) :
    ‖f‖ ^ 2 = ∫ r in Ioi 0, ‖f r‖ ^ 2 * ((radialGaussianWeight r)⁻¹ * r) := by
  have h := norm_sq_toLp (Lp.memLp f)
  rwa [Lp.toLp_coeFn] at h

/-- `√G(r)`. -/
def sqrtG (r : ℝ) : ℝ := Real.sqrt (radialGaussianWeight r)

theorem sqrtG_pos (r : ℝ) : 0 < sqrtG r := Real.sqrt_pos.2 (radialGaussianWeight_pos r)

theorem sqrtG_sq (r : ℝ) : sqrtG r ^ 2 = radialGaussianWeight r :=
  Real.sq_sqrt (radialGaussianWeight_pos r).le

theorem continuous_sqrtG : Continuous sqrtG := continuous_radialGaussianWeight.sqrt

theorem sqrtG_ofReal_ne_zero (r : ℝ) : (sqrtG r : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.2 (sqrtG_pos r).ne'

theorem memLp_divSqrt (f : XG) : MemLp (fun r => f r / (sqrtG r : ℂ)) 2 rMeasure := by
  have hm : AEStronglyMeasurable (fun r => f r / (sqrtG r : ℂ)) (volume.restrict (Ioi 0)) :=
    (aesm_coe f).div₀ (Complex.continuous_ofReal.comp continuous_sqrtG).aestronglyMeasurable
  refine (memLp_r_iff hm).2 ?_
  refine ((memLp_iff_integrableOn (aesm_coe f)).1 (Lp.memLp f)).congr_fun (fun r _ => ?_)
    measurableSet_Ioi
  have hG := (radialGaussianWeight_pos r).ne'
  simp only
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (sqrtG_pos r).le, div_pow, sqrtG_sq]
  field_simp

theorem memLp_mulSqrt (g : L2r) : MemLp (fun r => (sqrtG r : ℂ) * g r) 2 xGMeasure := by
  have hg : AEStronglyMeasurable (⇑g) (volume.restrict (Ioi 0)) :=
    (Lp.aestronglyMeasurable g).mono_ac restrict_ac_rMeasure
  have hm : AEStronglyMeasurable (fun r => (sqrtG r : ℂ) * g r) (volume.restrict (Ioi 0)) :=
    (Complex.continuous_ofReal.comp continuous_sqrtG).aestronglyMeasurable.mul hg
  refine (memLp_iff_integrableOn hm).2 ?_
  refine ((memLp_r_iff hg).1 (Lp.memLp g)).congr_fun (fun r _ => ?_) measurableSet_Ioi
  have hG := (radialGaussianWeight_pos r).ne'
  simp only
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sqrtG_pos r).le, mul_pow, sqrtG_sq]
  field_simp

/-- `f ↦ f/√G`, from `X_G` to `L²(r dr)`. -/
def toR (f : XG) : L2r := (memLp_divSqrt f).toLp _

/-- `g ↦ √G g`, from `L²(r dr)` to `X_G`. -/
def ofR (g : L2r) : XG := (memLp_mulSqrt g).toLp _

theorem coeFn_toR (f : XG) : ⇑(toR f) =ᵐ[rMeasure] fun r => f r / (sqrtG r : ℂ) :=
  (memLp_divSqrt f).coeFn_toLp

theorem coeFn_ofR (g : L2r) : ⇑(ofR g) =ᵐ[xGMeasure] fun r => (sqrtG r : ℂ) * g r :=
  (memLp_mulSqrt g).coeFn_toLp

theorem toR_ofR (g : L2r) : toR (ofR g) = g := by
  refine Lp.ext ?_
  filter_upwards [coeFn_toR (ofR g), rMeasure_ac.ae_le (restrict_ac.ae_le (coeFn_ofR g))]
    with r h1 h2
  rw [h1, h2]
  field_simp [sqrtG_ofReal_ne_zero r]

theorem ofR_toR (f : XG) : ofR (toR f) = f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_ofR (toR f), xG_ac.ae_le (restrict_ac_rMeasure.ae_le (coeFn_toR f))]
    with r h1 h2
  rw [h1, h2]
  field_simp [sqrtG_ofReal_ne_zero r]

theorem toR_add (f g : XG) : toR (f + g) = toR f + toR g := by
  refine Lp.ext ?_
  filter_upwards [coeFn_toR (f + g), Lp.coeFn_add (toR f) (toR g), coeFn_toR f, coeFn_toR g,
    rMeasure_ac.ae_le (restrict_ac.ae_le (Lp.coeFn_add f g))] with r h1 h2 h3 h4 h5
  rw [h1, h2, Pi.add_apply, h3, h4, h5, Pi.add_apply, add_div]

theorem toR_smul (c : ℂ) (f : XG) : toR (c • f) = c • toR f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_toR (c • f), Lp.coeFn_smul c (toR f), coeFn_toR f,
    rMeasure_ac.ae_le (restrict_ac.ae_le (Lp.coeFn_smul c f))] with r h1 h2 h3 h4
  rw [h1, h2, Pi.smul_apply, h3, h4, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_div_assoc]

theorem norm_toR (f : XG) : ‖toR f‖ = ‖f‖ := by
  have h : ‖toR f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [toR, norm_sq_toLp_r, norm_sq_XG]
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
    have hG := (radialGaussianWeight_pos r).ne'
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (sqrtG_pos r).le, div_pow, sqrtG_sq]
    field_simp
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- **The unitary change `f ↦ f/√G`** (tex line 1425) from `X_G` onto `L²((0,∞), r dr)`. -/
def U : XG ≃ₗᵢ[ℂ] L2r where
  toFun := toR
  invFun := ofR
  map_add' := toR_add
  map_smul' := toR_smul
  left_inv := ofR_toR
  right_inv := toR_ofR
  norm_map' := norm_toR

theorem coeFn_U (f : XG) : ⇑(U f) =ᵐ[rMeasure] fun r => f r / (sqrtG r : ℂ) := coeFn_toR f

theorem coeFn_U_symm (g : L2r) :
    ⇑(U.symm g) =ᵐ[xGMeasure] fun r => (sqrtG r : ℂ) * g r := coeFn_ofR g

/-! ## (b) The kernel of `2ikR` on `L²(r dr)` and its square integral -/

/-- The kernel of the conjugated interaction on `L²(r dr)` (tex lines 1425--1428):
`-(i/2) (k(r)/√G(r)) (min(r,s)/max(r,s))² √G(s)`, relative to `s ds`. -/
def hsKernel (r s : ℝ) : ℂ :=
  -(Complex.I / 2) * ((radialK r : ℂ) / (sqrtG r : ℂ)) *
    (((min r s / max r s) ^ 2 : ℝ) : ℂ) * (sqrtG s : ℂ)

theorem hsKernel_mul_eq (r s : ℝ) (z : ℂ) :
    hsKernel r s * z * (s : ℂ) = (-(Complex.I / 2) * ((radialK r : ℂ) / (sqrtG r : ℂ))) *
      ((B0011.ker 2 r s : ℂ) * ((sqrtG s : ℂ) * z)) := by
  simp only [hsKernel, B0011.ker, Complex.ofReal_mul]
  ring

/-- For `g ∈ L²(r dr)` and `r > 0`, `s ↦ K(r,s) g(s) s` is integrable on `(0, ∞)`, so the
kernel integral below is a genuine (absolutely convergent) integral. -/
theorem integrable_hsKernel_mul (g : L2r) {r : ℝ} (hr : 0 < r) :
    Integrable (fun s => hsKernel r s * g s * (s : ℂ)) (volume.restrict (Ioi 0)) := by
  have hf : ⇑(U.symm g) =ᵐ[volume.restrict (Ioi 0)] fun s => (sqrtG s : ℂ) * g s :=
    restrict_ac.ae_le (coeFn_U_symm g)
  have h := ((wprof_coe (U.symm g)).integrable_ker 2 hr.le).const_mul
    (-(Complex.I / 2) * ((radialK r : ℂ) / (sqrtG r : ℂ)))
  refine h.congr ?_
  filter_upwards [hf] with s hs
  rw [hs, hsKernel_mul_eq]

/-- **(b), kernel** (tex lines 1424--1428): after the unitary change `f ↦ f/√G`, the
interaction `2ikR` is the integral operator on `L²(r dr)` with kernel `hsKernel` relative to
`s ds`: `(U (2ikR) U⁻¹ g)(r) = ∫₀^∞ K(r,s) g(s) s ds` for a.e. `r`. -/
theorem conj_interactionOp_eq_kernel (g : L2r) :
    ⇑(U (interactionOp (U.symm g))) =ᵐ[rMeasure]
      fun r => ∫ s in Ioi 0, hsKernel r s * g s * (s : ℂ) := by
  set f := U.symm g with hfdef
  have hf : ⇑f =ᵐ[volume.restrict (Ioi 0)] fun s => (sqrtG s : ℂ) * g s :=
    restrict_ac.ae_le (coeFn_U_symm g)
  filter_upwards [coeFn_U (interactionOp f),
    rMeasure_ac.ae_le (restrict_ac.ae_le (coeFn_interactionOp f)), ae_rMeasure_pos]
    with r h1 h2 hr
  rw [h1, h2, R_eq_Psi (wprof_coe f) hr, Psi]
  have e1 : ∫ s in Ioi 0, (B0011.ker 2 r s : ℂ) * f s =
      ∫ s in Ioi 0, (B0011.ker 2 r s : ℂ) * ((sqrtG s : ℂ) * g s) :=
    integral_congr_ae (hf.mono fun s hs => by simp only; rw [hs])
  have e2 : ∫ s in Ioi 0, hsKernel r s * g s * (s : ℂ) =
      (-(Complex.I / 2) * ((radialK r : ℂ) / (sqrtG r : ℂ))) *
        ∫ s in Ioi 0, (B0011.ker 2 r s : ℂ) * ((sqrtG s : ℂ) * g s) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun s => hsKernel_mul_eq r s (g s))
  rw [e1, e2]
  ring

/-- The pointwise Hilbert–Schmidt bound `|K(r,s)|² r s ≤ ¼ (|k(r)|² G(r)⁻¹ r) (G(s) s)`, from
`(min/max)⁴ ≤ 1`. -/
theorem norm_hsKernel_sq_le {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    ‖hsKernel r s‖ ^ 2 * r * s ≤
      1 / 4 * (‖(radialK r : ℂ)‖ ^ 2 * ((radialGaussianWeight r)⁻¹ * r)) *
        (radialGaussianWeight s * s) := by
  set q : ℝ := (min r s / max r s) ^ 2 with hq
  have hmax : 0 < max r s := lt_max_of_lt_left hr
  have hm0 : 0 ≤ min r s / max r s := div_nonneg (le_min hr.le hs.le) hmax.le
  have hm1 : min r s / max r s ≤ 1 := div_le_one_of_le₀ min_le_max hmax.le
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 := pow_le_one₀ hm0 hm1
  have hq2 : q ^ 2 ≤ 1 := pow_le_one₀ hq0 hq1
  have n1 : ‖-(Complex.I / 2)‖ = 1 / 2 := by
    rw [norm_neg, norm_div, Complex.norm_I]; norm_num
  have n2 : ‖(radialK r : ℂ) / (sqrtG r : ℂ)‖ = ‖(radialK r : ℂ)‖ / sqrtG r := by
    rw [norm_div, Complex.norm_real (sqrtG r), Real.norm_of_nonneg (sqrtG_pos r).le]
  have n3 : ‖((q : ℝ) : ℂ)‖ = q := by rw [Complex.norm_real, Real.norm_of_nonneg hq0]
  have n4 : ‖(sqrtG s : ℂ)‖ = sqrtG s := by
    rw [Complex.norm_real, Real.norm_of_nonneg (sqrtG_pos s).le]
  have hk : hsKernel r s = -(Complex.I / 2) * ((radialK r : ℂ) / (sqrtG r : ℂ)) *
      ((q : ℝ) : ℂ) * (sqrtG s : ℂ) := rfl
  rw [hk, norm_mul, norm_mul, norm_mul, n1, n2, n3, n4]
  have hsr := (sqrtG_pos r).ne'
  have e : (1 / 2 * (‖(radialK r : ℂ)‖ / sqrtG r) * q * sqrtG s) ^ 2 * r * s =
      1 / 4 * (‖(radialK r : ℂ)‖ ^ 2 * ((radialGaussianWeight r)⁻¹ * r)) *
        (radialGaussianWeight s * s) * q ^ 2 := by
    rw [← sqrtG_sq r, ← sqrtG_sq s]
    field_simp
    ring
  rw [e]
  have hpos : 0 ≤ 1 / 4 * (‖(radialK r : ℂ)‖ ^ 2 * ((radialGaussianWeight r)⁻¹ * r)) *
      (radialGaussianWeight s * s) :=
    mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _)
      (mul_nonneg (inv_nonneg.2 (radialGaussianWeight_pos r).le) hr.le)))
      (mul_nonneg (radialGaussianWeight_pos s).le hs.le)
  exact mul_le_of_le_one_right hpos hq2

/-- `∫₀^∞ |k|² G⁻¹ r dr < ∞` (`k ∈ X_G`, B0012 `memLp_k`). -/
theorem lintegral_k_sq_lt_top :
    ∫⁻ r in Ioi 0, ENNReal.ofReal (‖(radialK r : ℂ)‖ ^ 2 * ((radialGaussianWeight r)⁻¹ * r))
      < ∞ :=
  integrableOn_k_sq.lintegral_lt_top

/-- `∫₀^∞ G s ds < ∞` (B0012 `memLp_gauss`). -/
theorem lintegral_gauss_lt_top :
    ∫⁻ s in Ioi 0, ENNReal.ofReal (radialGaussianWeight s * s) < ∞ := by
  have h := (memLp_iff_integrableOn (Complex.continuous_ofReal.comp
    continuous_radialGaussianWeight).aestronglyMeasurable).1 memLp_gauss
  have h' : IntegrableOn (fun s => radialGaussianWeight s * s) (Ioi 0) := by
    refine h.congr_fun (fun s _ => ?_) measurableSet_Ioi
    have hG := (radialGaussianWeight_pos s).ne'
    simp only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    field_simp
  exact h'.lintegral_lt_top

/-- **(b), square integral** (tex lines 1429--1430): the square integral of the kernel against
`r dr ⊗ s ds` is bounded by a constant times `(∫|k|²G⁻¹ r dr)(∫ G s ds)`. -/
theorem hsKernel_sq_lintegral_le :
    ∫⁻ r in Ioi 0, ∫⁻ s in Ioi 0, ENNReal.ofReal (‖hsKernel r s‖ ^ 2 * r * s) ≤
      ENNReal.ofReal (1 / 4) *
        (∫⁻ r in Ioi 0,
          ENNReal.ofReal (‖(radialK r : ℂ)‖ ^ 2 * ((radialGaussianWeight r)⁻¹ * r))) *
        ∫⁻ s in Ioi 0, ENNReal.ofReal (radialGaussianWeight s * s) := by
  set A : ℝ → ℝ := fun r => ‖(radialK r : ℂ)‖ ^ 2 * ((radialGaussianWeight r)⁻¹ * r) with hA
  set B : ℝ → ℝ := fun s => radialGaussianWeight s * s with hB
  have hB0 : ∀ s ∈ Ioi (0 : ℝ), 0 ≤ B s := fun s hs =>
    mul_nonneg (radialGaussianWeight_pos s).le (le_of_lt hs)
  calc ∫⁻ r in Ioi 0, ∫⁻ s in Ioi 0, ENNReal.ofReal (‖hsKernel r s‖ ^ 2 * r * s)
      ≤ ∫⁻ r in Ioi 0, ∫⁻ s in Ioi 0, ENNReal.ofReal (1 / 4 * A r) * ENNReal.ofReal (B s) := by
        refine setLIntegral_mono' measurableSet_Ioi fun r hr =>
          setLIntegral_mono' measurableSet_Ioi fun s hs => ?_
        have hr' : (0 : ℝ) < r := hr
        have hA0 : 0 ≤ 1 / 4 * A r := mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _)
          (mul_nonneg (inv_nonneg.2 (radialGaussianWeight_pos r).le) hr'.le))
        rw [← ENNReal.ofReal_mul hA0]
        exact ENNReal.ofReal_le_ofReal (norm_hsKernel_sq_le hr hs)
    _ = ∫⁻ r in Ioi 0, ENNReal.ofReal (1 / 4 * A r) *
          ∫⁻ s in Ioi 0, ENNReal.ofReal (B s) := by
        refine lintegral_congr fun r => ?_
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = (∫⁻ r in Ioi 0, ENNReal.ofReal (1 / 4 * A r)) *
          ∫⁻ s in Ioi 0, ENNReal.ofReal (B s) :=
        lintegral_mul_const' _ _ lintegral_gauss_lt_top.ne
    _ = ENNReal.ofReal (1 / 4) * (∫⁻ r in Ioi 0, ENNReal.ofReal (A r)) *
          ∫⁻ s in Ioi 0, ENNReal.ofReal (B s) := by
        congr 1
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun r => ?_
        rw [ENNReal.ofReal_mul (by norm_num)]

/-- **(b), finiteness** (tex line 1430): the square integral of the kernel is finite, i.e. the
conjugated interaction is an integral operator with a square-integrable (Hilbert–Schmidt)
kernel on `L²(r dr)`. -/
theorem hsKernel_sq_lintegral_lt_top :
    ∫⁻ r in Ioi 0, ∫⁻ s in Ioi 0, ENNReal.ofReal (‖hsKernel r s‖ ^ 2 * r * s) < ∞ :=
  hsKernel_sq_lintegral_le.trans_lt (ENNReal.mul_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top lintegral_k_sq_lt_top) lintegral_gauss_lt_top)

/-! ## (c) `L₀` is bounded and a compact perturbation of imaginary multiplication -/

/-- `T` is a compact perturbation of imaginary multiplication on `X_G` (tex line 1431): there
are a bounded measurable purely imaginary multiplier `m` and a bounded operator `M` acting as
multiplication by `m` such that `T - M` is compact. -/
def IsCompactPerturbationOfImagMul (T : XG →L[ℂ] XG) : Prop :=
  ∃ m : ℝ → ℂ, Measurable m ∧ (∃ C : ℝ, ∀ r, ‖m r‖ ≤ C) ∧ (∀ r, (m r).re = 0) ∧
    ∃ M : XG →L[ℂ] XG, (∀ f : XG, ⇑(M f) =ᵐ[xGMeasure] fun r => m r * f r) ∧
      IsCompactOperator (T - M)

/-- `L₀` is a compact perturbation of multiplication by the imaginary function `-2iΩ`. -/
theorem L0_isCompactPerturbationOfImagMul : IsCompactPerturbationOfImagMul L0 := by
  refine ⟨imMultiplier, continuous_imMultiplier.measurable, ⟨2, norm_imMultiplier_le⟩,
    re_imMultiplier, imMulOp, coeFn_imMulOp, ?_⟩
  rw [L0_eq, add_sub_cancel_left]
  exact isCompactOperator_interactionOp

/-- **B0087** (tex lines 1424--1432), whole statement:
(a) multiplication by `-2iΩ` is bounded and skew-adjoint on `X_G`;
(b) `2ikR` is compact; after the unitary change `U f = f/√G` onto `L²(r dr)` it is the integral
operator with kernel `hsKernel` relative to `s ds`, whose square integral is at most
`¼ (∫|k|²G⁻¹ r dr)(∫ G s ds) < ∞`;
(c) `L₀ = -2iΩ + 2ikR` is bounded on `X_G` and a compact perturbation of imaginary
multiplication. -/
theorem L0_bounded_and_compactPerturbation :
    -- (a)
    (∀ f : XG, ⇑(imMulOp f) =ᵐ[xGMeasure] fun r => imMultiplier r * f r) ∧
    (∀ f : XG, ‖imMulOp f‖ ≤ 2 * ‖f‖) ∧ ContinuousLinearMap.adjoint imMulOp = -imMulOp ∧
    -- (b)
    (∀ f : XG, ⇑(interactionOp f) =ᵐ[xGMeasure]
      fun r => 2 * Complex.I * (radialK r : ℂ) * R (⇑f) r) ∧
    IsCompactOperator interactionOp ∧
    (∀ f : XG, ⇑(U f) =ᵐ[rMeasure] fun r => f r / (sqrtG r : ℂ)) ∧
    (∀ g : L2r, ⇑(U.symm g) =ᵐ[xGMeasure] fun r => (sqrtG r : ℂ) * g r) ∧
    (∀ g : L2r, ∀ r : ℝ, 0 < r →
      Integrable (fun s => hsKernel r s * g s * (s : ℂ)) (volume.restrict (Ioi 0))) ∧
    (∀ g : L2r, ⇑(U (interactionOp (U.symm g))) =ᵐ[rMeasure]
      fun r => ∫ s in Ioi 0, hsKernel r s * g s * (s : ℂ)) ∧
    ∫⁻ r in Ioi 0, ∫⁻ s in Ioi 0, ENNReal.ofReal (‖hsKernel r s‖ ^ 2 * r * s) ≤
      ENNReal.ofReal (1 / 4) *
        (∫⁻ r in Ioi 0,
          ENNReal.ofReal (‖(radialK r : ℂ)‖ ^ 2 * ((radialGaussianWeight r)⁻¹ * r))) *
        (∫⁻ s in Ioi 0, ENNReal.ofReal (radialGaussianWeight s * s)) ∧
    ENNReal.ofReal (1 / 4) *
        (∫⁻ r in Ioi 0,
          ENNReal.ofReal (‖(radialK r : ℂ)‖ ^ 2 * ((radialGaussianWeight r)⁻¹ * r))) *
        (∫⁻ s in Ioi 0, ENNReal.ofReal (radialGaussianWeight s * s)) < ∞ ∧
    -- (c)
    (∃ C : ℝ, 0 ≤ C ∧ ∀ f : XG, ‖L0 f‖ ≤ C * ‖f‖) ∧ IsCompactPerturbationOfImagMul L0 :=
  ⟨coeFn_imMulOp, norm_imMulOp_le, adjoint_imMulOp, coeFn_interactionOp,
    isCompactOperator_interactionOp, coeFn_U, coeFn_U_symm,
    fun g _ hr => integrable_hsKernel_mul g hr,
    conj_interactionOp_eq_kernel, hsKernel_sq_lintegral_le,
    ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top lintegral_k_sq_lt_top)
      lintegral_gauss_lt_top,
    L0_bounded, L0_isCompactPerturbationOfImagMul⟩

end UnforcedLeray.B0087
