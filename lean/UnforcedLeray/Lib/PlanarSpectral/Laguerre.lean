import UnforcedLeray.Units.B0010
import UnforcedLeray.Units.B0094.Basis
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Tactic

/-!
# INF10 H1--H2: the Laguerre model of `X_G`


bypass B6 and targets H1, H2 (Level H). The manuscript diagonalizes `D = Δ + ½ y·∇ + 2` on the
Gaussian angular-two space `X_G` (`eq:st18-t00005`, tex lines 672--678, unit B0010) through the
Hermite oscillator (`eq:st18-t00067`--`eq:st18-t00068`, tex lines 1498--1515, units B0093,
B0094). Bypass B6 replaces this by the angular-two Laguerre model: with `x = r²/4` and
`f₂ = r² p(x) e^{-x}`,

  `‖f‖²_{X_G} = ∫₀^∞ |f₂|² G⁻¹ r dr = 128 π ∫₀^∞ |p(x)|² x² e^{-x} dx`.

We prove:

* **H1** `xGToLaguerre : XG ≃ₗᵢ[ℂ] Lp ℂ 2 laguerreMeasure`, where `laguerreMeasure` is
  `x² e^{-x} dx` on `(0, ∞)`. Explicitly (`coeFn_xGToLaguerre`)
  `(xGToLaguerre f)(x) = √(8π) e^x x⁻¹ f₂(2√x)`, i.e. `√(128π) p(x)` for `f₂ = r² p(r²/4) e^{-r²/4}`,
  and (`coeFn_xGToLaguerre_symm`) `(xGToLaguerre.symm g)(r) = (8π)^{-1/2} (r²/4) e^{-r²/4} g(r²/4)`.
  The proof is the substitution `x = r²/4` (Mathlib `lintegral_image_eq_lintegral_abs_deriv_mul`).
* **H2** `laguerreMono k = x^k`, `xGToLaguerre_vmono` (the image of the B0094 profile
  `r^{2+2k} e^{-r²/4}` is `√(8π) 4^{k+1} x^k`), `linearIndependent_laguerreMono`,
  `span_monomials_orthogonal_eq_bot` (completeness of the monomials, transported from the
  compiled draft `B0094.eq_zero_of_inner_prof_X_pow`: exponential moments, Weierstrass, and the
  fundamental lemma; this replaces the Laplace/Plancherel route of the scoping note), and
  `laguerreBasis : HilbertBasis ℕ ℂ (Lp ℂ 2 laguerreMeasure)`, the Gram--Schmidt
  orthonormalization of the monomials (`coe_laguerreBasis`).
-/

set_option autoImplicit false

noncomputable section
open MeasureTheory Set Filter Polynomial
open scoped ENNReal NNReal InnerProductSpace ComplexConjugate Real
namespace UnforcedLeray.PlanarSpectral
open UnforcedLeray.B0010

/-! ## The Laguerre measure `x² e^{-x} dx` on `(0, ∞)` -/

/-- The Laguerre density `x² e^{-x}` (generalized Laguerre weight with `α = 2`). -/
def laguerreDensity (x : ℝ) : ℝ≥0 := ⟨x ^ 2 * Real.exp (-x), by positivity⟩

theorem measurable_laguerreDensity : Measurable laguerreDensity :=
  (by fun_prop : Measurable fun x : ℝ => x ^ 2 * Real.exp (-x)).subtype_mk

theorem coe_laguerreDensity (x : ℝ) :
    (laguerreDensity x : ℝ≥0∞) = ENNReal.ofReal (x ^ 2 * Real.exp (-x)) :=
  (ENNReal.ofReal_eq_coe_nnreal _).symm

/-- The measure `x² e^{-x} dx` on `(0, ∞)` (scoping note §4, B6). -/
def laguerreMeasure : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity (fun x => (laguerreDensity x : ℝ≥0∞))

/-- The Laguerre space `L²((0, ∞), x² e^{-x} dx; ℂ)`. -/
abbrev LaguerreL2 : Type := Lp ℂ 2 laguerreMeasure

theorem lintegral_laguerreMeasure (G : ℝ → ℝ≥0∞) :
    ∫⁻ x, G x ∂laguerreMeasure =
      ∫⁻ x in Ioi 0, ENNReal.ofReal (x ^ 2 * Real.exp (-x)) * G x := by
  rw [laguerreMeasure, lintegral_withDensity_eq_lintegral_mul_non_measurable _
    measurable_laguerreDensity.coe_nnreal_ennreal
    (ae_of_all _ fun _ => ENNReal.coe_lt_top)]
  simp only [Pi.mul_apply, coe_laguerreDensity]

theorem lintegral_xGMeasure (G : ℝ → ℝ≥0∞) :
    ∫⁻ r, G r ∂xGMeasure =
      ∫⁻ r in Ioi 0, ENNReal.ofReal (4 * π * Real.exp (r ^ 2 / 4) * r) * G r := by
  rw [xGMeasure, lintegral_withDensity_eq_lintegral_mul_non_measurable _
    measurable_xGDensity.coe_nnreal_ennreal
    (ae_of_all _ fun _ => ENNReal.coe_lt_top)]
  simp only [Pi.mul_apply, xGDensity_eq]
  rfl

theorem ae_laguerreMeasure_pos : ∀ᵐ x ∂laguerreMeasure, 0 < x :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)

theorem ae_xGMeasure_pos : ∀ᵐ r ∂xGMeasure, 0 < r :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)

/-! ## The substitution `x = r²/4` -/

theorem sqrt_sq_div_four {r : ℝ} (hr : 0 < r) : 2 * Real.sqrt (r ^ 2 / 4) = r := by
  rw [show r ^ 2 / 4 = (r / 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  ring

theorem sq_two_sqrt_div_four {x : ℝ} (hx : 0 < x) : (2 * Real.sqrt x) ^ 2 / 4 = x := by
  rw [mul_pow, Real.sq_sqrt hx.le]
  ring

/-- `∫⁻_{(0,∞)} H(x) dx = ∫⁻_{(0,∞)} H(r²/4) (r/2) dr`, for every `H` (no measurability needed). -/
theorem lintegral_Ioi_comp_sq_div_four (H : ℝ → ℝ≥0∞) :
    ∫⁻ x in Ioi 0, H x = ∫⁻ r in Ioi 0, ENNReal.ofReal (r / 2) * H (r ^ 2 / 4) := by
  have himage : (fun r : ℝ => r ^ 2 / 4) '' Ioi 0 = Ioi 0 := by
    ext x
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact div_pos (pow_pos (show (0 : ℝ) < r from hr) 2) (by norm_num)
    · intro hx
      refine ⟨2 * Real.sqrt x, ?_, sq_two_sqrt_div_four hx⟩
      exact mul_pos two_pos (Real.sqrt_pos.mpr hx)
  have hderiv : ∀ r ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun r : ℝ => r ^ 2 / 4) (r / 2) (Ioi 0) r := by
    intro r _
    have h := (hasDerivAt_pow 2 r).div_const 4
    refine (h.congr_deriv ?_).hasDerivWithinAt
    push_cast
    ring
  have hinj : InjOn (fun r : ℝ => r ^ 2 / 4) (Ioi 0) := by
    intro r hr s hs hrs
    have h : r ^ 2 = s ^ 2 := by
      have := hrs
      simp only at this
      linarith
    exact (sq_eq_sq₀ (le_of_lt hr) (le_of_lt hs)).mp h
  conv_lhs => rw [← himage]
  rw [lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hderiv hinj H]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
  rw [abs_of_pos (half_pos (mem_Ioi.mp hr))]

/-! ## The pointwise transforms -/

/-- The factor `√(8π) e^x / x`. -/
def lagFactor (x : ℝ) : ℝ := Real.sqrt (8 * π) * Real.exp x / x

/-- The inverse factor `(r²/4) e^{-r²/4} / √(8π)`. -/
def xGFactor (r : ℝ) : ℝ := r ^ 2 / 4 * Real.exp (-(r ^ 2 / 4)) / Real.sqrt (8 * π)

/-- `X_G`-profile to Laguerre function: `f₂ ↦ √(8π) e^x x⁻¹ f₂(2√x)`. -/
def toLagFun (f : ℝ → ℂ) (x : ℝ) : ℂ := (lagFactor x : ℂ) * f (2 * Real.sqrt x)

/-- Laguerre function to `X_G`-profile: `g ↦ (8π)^{-1/2} (r²/4) e^{-r²/4} g(r²/4)`. -/
def fromLagFun (g : ℝ → ℂ) (r : ℝ) : ℂ := (xGFactor r : ℂ) * g (r ^ 2 / 4)

theorem measurable_lagFactor : Measurable lagFactor := by
  unfold lagFactor; fun_prop

theorem measurable_xGFactor : Measurable xGFactor := by
  unfold xGFactor; fun_prop

theorem stronglyMeasurable_toLagFun {f : ℝ → ℂ} (hf : StronglyMeasurable f) :
    StronglyMeasurable (toLagFun f) :=
  (Complex.measurable_ofReal.comp measurable_lagFactor).stronglyMeasurable.mul
    (hf.comp_measurable (by fun_prop))

theorem stronglyMeasurable_fromLagFun {g : ℝ → ℂ} (hg : StronglyMeasurable g) :
    StronglyMeasurable (fromLagFun g) :=
  (Complex.measurable_ofReal.comp measurable_xGFactor).stronglyMeasurable.mul
    (hg.comp_measurable (by fun_prop))

theorem enorm_ofReal_mul_sq (a : ℝ) (z : ℂ) :
    ‖(a : ℂ) * z‖ₑ ^ 2 = ENNReal.ofReal (a ^ 2) * ‖z‖ₑ ^ 2 := by
  rw [enorm_mul, mul_pow, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
    ← ENNReal.ofReal_pow (abs_nonneg a), sq_abs]

theorem toLagFun_fromLagFun (g : ℝ → ℂ) {x : ℝ} (hx : 0 < x) :
    toLagFun (fromLagFun g) x = g x := by
  have hs : 0 < Real.sqrt (8 * π) := Real.sqrt_pos.mpr (by positivity)
  simp only [toLagFun, fromLagFun, sq_two_sqrt_div_four hx, ← mul_assoc, ← Complex.ofReal_mul]
  have h : lagFactor x * xGFactor (2 * Real.sqrt x) = 1 := by
    simp only [lagFactor, xGFactor, sq_two_sqrt_div_four hx]
    rw [Real.exp_neg]
    field_simp
  rw [h, Complex.ofReal_one, one_mul]

theorem fromLagFun_toLagFun (f : ℝ → ℂ) {r : ℝ} (hr : 0 < r) :
    fromLagFun (toLagFun f) r = f r := by
  have hs : 0 < Real.sqrt (8 * π) := Real.sqrt_pos.mpr (by positivity)
  simp only [toLagFun, fromLagFun, sqrt_sq_div_four hr, ← mul_assoc, ← Complex.ofReal_mul]
  have hx : 0 < r ^ 2 / 4 := by positivity
  have h : xGFactor r * lagFactor (r ^ 2 / 4) = 1 := by
    simp only [lagFactor, xGFactor]
    rw [Real.exp_neg]
    field_simp
  rw [h, Complex.ofReal_one, one_mul]

/-! ## The two lintegral identities -/

theorem real_identity_to {r : ℝ} (hr : 0 < r) :
    r / 2 * ((r ^ 2 / 4) ^ 2 * Real.exp (-(r ^ 2 / 4))) * lagFactor (r ^ 2 / 4) ^ 2 =
      4 * π * Real.exp (r ^ 2 / 4) * r := by
  have hs : Real.sqrt (8 * π) ^ 2 = 8 * π := Real.sq_sqrt (by positivity)
  simp only [lagFactor, div_pow, mul_pow, hs, Real.exp_neg]
  field_simp
  ring

theorem real_identity_from {r : ℝ} (hr : 0 < r) :
    4 * π * Real.exp (r ^ 2 / 4) * r * xGFactor r ^ 2 =
      r / 2 * ((r ^ 2 / 4) ^ 2 * Real.exp (-(r ^ 2 / 4))) := by
  have hs : Real.sqrt (8 * π) ^ 2 = 8 * π := Real.sq_sqrt (by positivity)
  simp only [xGFactor, div_pow, mul_pow, hs, Real.exp_neg]
  field_simp
  ring

/-- `∫ |T f|² x² e^{-x} dx = ∫ |f|² G⁻¹ r dr` for every profile `f`. -/
theorem lintegral_enorm_toLagFun (f : ℝ → ℂ) :
    ∫⁻ x, ‖toLagFun f x‖ₑ ^ 2 ∂laguerreMeasure = ∫⁻ r, ‖f r‖ₑ ^ 2 ∂xGMeasure := by
  rw [lintegral_laguerreMeasure, lintegral_xGMeasure, lintegral_Ioi_comp_sq_div_four]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
  have hr : 0 < r := hr
  simp only [toLagFun, sqrt_sq_div_four hr, enorm_ofReal_mul_sq]
  rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), real_identity_to hr]

/-- `∫ |S g|² G⁻¹ r dr = ∫ |g|² x² e^{-x} dx` for every function `g`. -/
theorem lintegral_enorm_fromLagFun (g : ℝ → ℂ) :
    ∫⁻ r, ‖fromLagFun g r‖ₑ ^ 2 ∂xGMeasure = ∫⁻ x, ‖g x‖ₑ ^ 2 ∂laguerreMeasure := by
  rw [lintegral_laguerreMeasure, lintegral_xGMeasure]
  conv_rhs => rw [lintegral_Ioi_comp_sq_div_four]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
  have hr : 0 < r := hr
  simp only [fromLagFun, enorm_ofReal_mul_sq]
  rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), real_identity_from hr]

/-! ## `L²` membership and transfer of a.e. equalities -/

theorem eLpNorm_two_eq {μ : Measure ℝ} (u : ℝ → ℂ) :
    eLpNorm u 2 μ = (∫⁻ x, ‖u x‖ₑ ^ 2 ∂μ) ^ (1 / (2 : ℝ)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]

theorem eLpNorm_toLagFun (f : ℝ → ℂ) :
    eLpNorm (toLagFun f) 2 laguerreMeasure = eLpNorm f 2 xGMeasure := by
  rw [eLpNorm_two_eq, eLpNorm_two_eq, lintegral_enorm_toLagFun]

theorem eLpNorm_fromLagFun (g : ℝ → ℂ) :
    eLpNorm (fromLagFun g) 2 xGMeasure = eLpNorm g 2 laguerreMeasure := by
  rw [eLpNorm_two_eq, eLpNorm_two_eq, lintegral_enorm_fromLagFun]

theorem memLp_toLagFun (f : XG) : MemLp (toLagFun f) 2 laguerreMeasure :=
  ⟨(stronglyMeasurable_toLagFun (Lp.stronglyMeasurable f)).aestronglyMeasurable,
    by rw [eLpNorm_toLagFun]; exact Lp.eLpNorm_lt_top f⟩

theorem memLp_fromLagFun (g : LaguerreL2) : MemLp (fromLagFun g) 2 xGMeasure :=
  ⟨(stronglyMeasurable_fromLagFun (Lp.stronglyMeasurable g)).aestronglyMeasurable,
    by rw [eLpNorm_fromLagFun]; exact Lp.eLpNorm_lt_top g⟩

theorem ae_eq_of_lintegral_enorm_sub_sq_eq_zero {μ : Measure ℝ} {u v : ℝ → ℂ}
    (hu : StronglyMeasurable u) (hv : StronglyMeasurable v)
    (h : ∫⁻ x, ‖u x - v x‖ₑ ^ 2 ∂μ = 0) : u =ᵐ[μ] v := by
  have hm : Measurable fun x => ‖u x - v x‖ₑ ^ 2 :=
    ((hu.sub hv).measurable.enorm).pow_const 2
  rw [lintegral_eq_zero_iff hm] at h
  filter_upwards [h] with x hx
  simp only [Pi.zero_apply, pow_eq_zero_iff two_ne_zero, enorm_eq_zero, sub_eq_zero] at hx
  exact hx

theorem toLagFun_sub (u v : ℝ → ℂ) (x : ℝ) :
    toLagFun u x - toLagFun v x = toLagFun (u - v) x := by
  simp only [toLagFun, Pi.sub_apply, mul_sub]

theorem fromLagFun_sub (u v : ℝ → ℂ) (x : ℝ) :
    fromLagFun u x - fromLagFun v x = fromLagFun (u - v) x := by
  simp only [fromLagFun, Pi.sub_apply, mul_sub]

/-- `T` respects a.e. equality: `u = v` `X_G`-a.e. implies `T u = T v` Laguerre-a.e. -/
theorem toLagFun_congr_ae {u v : ℝ → ℂ} (hu : StronglyMeasurable u)
    (hv : StronglyMeasurable v) (h : u =ᵐ[xGMeasure] v) :
    toLagFun u =ᵐ[laguerreMeasure] toLagFun v := by
  apply ae_eq_of_lintegral_enorm_sub_sq_eq_zero (stronglyMeasurable_toLagFun hu)
    (stronglyMeasurable_toLagFun hv)
  simp_rw [toLagFun_sub]
  rw [lintegral_enorm_toLagFun]
  rw [lintegral_congr_ae (g := fun _ => 0) ?_, lintegral_zero]
  filter_upwards [h] with r hr
  simp [hr]

theorem fromLagFun_congr_ae {u v : ℝ → ℂ} (hu : StronglyMeasurable u)
    (hv : StronglyMeasurable v) (h : u =ᵐ[laguerreMeasure] v) :
    fromLagFun u =ᵐ[xGMeasure] fromLagFun v := by
  apply ae_eq_of_lintegral_enorm_sub_sq_eq_zero (stronglyMeasurable_fromLagFun hu)
    (stronglyMeasurable_fromLagFun hv)
  simp_rw [fromLagFun_sub]
  rw [lintegral_enorm_fromLagFun]
  rw [lintegral_congr_ae (g := fun _ => 0) ?_, lintegral_zero]
  filter_upwards [h] with r hr
  simp [hr]

/-! ## H1: the isometric isomorphism -/

/-- The transform `X_G → L²(x² e^{-x} dx)` as a linear map. -/
def toLagLinear : XG →ₗ[ℂ] LaguerreL2 where
  toFun f := (memLp_toLagFun f).toLp _
  map_add' f g := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    have h := toLagFun_congr_ae (Lp.stronglyMeasurable (f + g))
      ((Lp.stronglyMeasurable f).add (Lp.stronglyMeasurable g)) (Lp.coeFn_add f g)
    refine h.trans (Eventually.of_forall fun x => ?_)
    simp only [toLagFun, Pi.add_apply, mul_add]
  map_smul' c f := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    have h := toLagFun_congr_ae (Lp.stronglyMeasurable (c • f))
      ((Lp.stronglyMeasurable f).const_smul c) (Lp.coeFn_smul c f)
    refine h.trans (Eventually.of_forall fun x => ?_)
    simp only [toLagFun, Pi.smul_apply, smul_eq_mul]
    ring

theorem coeFn_toLagLinear (f : XG) : (toLagLinear f : ℝ → ℂ) =ᵐ[laguerreMeasure] toLagFun f :=
  (memLp_toLagFun f).coeFn_toLp

theorem norm_toLagLinear (f : XG) : ‖toLagLinear f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (coeFn_toLagLinear f), eLpNorm_toLagFun]

/-- The transform as a linear isometry. -/
def toLagIsometry : XG →ₗᵢ[ℂ] LaguerreL2 :=
  { toLagLinear with norm_map' := norm_toLagLinear }

theorem toLagLinear_fromLagFun (g : LaguerreL2) :
    toLagLinear ((memLp_fromLagFun g).toLp _) = g := by
  apply Lp.ext
  refine (coeFn_toLagLinear _).trans ?_
  have h := toLagFun_congr_ae (Lp.stronglyMeasurable ((memLp_fromLagFun g).toLp _))
    (stronglyMeasurable_fromLagFun (Lp.stronglyMeasurable g)) (memLp_fromLagFun g).coeFn_toLp
  refine h.trans ?_
  filter_upwards [ae_laguerreMeasure_pos] with x hx
  exact toLagFun_fromLagFun _ hx

theorem surjective_toLagIsometry : Function.Surjective toLagIsometry :=
  fun g => ⟨_, toLagLinear_fromLagFun g⟩

/-- **H1** (scoping note §5, Level H; bypass B6): the isometric isomorphism
`X_G ≅ L²((0,∞), x² e^{-x} dx)`, `f₂ ↦ √(8π) e^x x⁻¹ f₂(2√x)` (B0010, `eq:st18-t00005`,
tex lines 672--678). -/
def xGToLaguerre : XG ≃ₗᵢ[ℂ] LaguerreL2 :=
  LinearIsometryEquiv.ofSurjective toLagIsometry surjective_toLagIsometry

/-- The explicit formula `(xGToLaguerre f)(x) = √(8π) e^x x⁻¹ f₂(2√x)` (a.e.). -/
theorem coeFn_xGToLaguerre (f : XG) :
    (xGToLaguerre f : ℝ → ℂ) =ᵐ[laguerreMeasure]
      fun x => ((Real.sqrt (8 * π) * Real.exp x / x : ℝ) : ℂ) * f (2 * Real.sqrt x) :=
  coeFn_toLagLinear f

theorem xGToLaguerre_symm_eq (g : LaguerreL2) :
    xGToLaguerre.symm g = (memLp_fromLagFun g).toLp _ := by
  rw [LinearIsometryEquiv.symm_apply_eq]
  exact (toLagLinear_fromLagFun g).symm

/-- The explicit inverse `(xGToLaguerre.symm g)(r) = (8π)^{-1/2} (r²/4) e^{-r²/4} g(r²/4)` (a.e.). -/
theorem coeFn_xGToLaguerre_symm (g : LaguerreL2) :
    (xGToLaguerre.symm g : ℝ → ℂ) =ᵐ[xGMeasure]
      fun r => ((r ^ 2 / 4 * Real.exp (-(r ^ 2 / 4)) / Real.sqrt (8 * π) : ℝ) : ℂ) *
        g (r ^ 2 / 4) := by
  rw [xGToLaguerre_symm_eq]
  exact (memLp_fromLagFun g).coeFn_toLp

/-! ## H2: monomials, completeness, and the Laguerre Hilbert basis -/

/-- The scale `√(8π) 4^{k+1}` relating `r^{2+2k} e^{-r²/4}` to `x^k`. -/
def monoScale (k : ℕ) : ℝ := Real.sqrt (8 * π) * 4 ^ (k + 1)

theorem monoScale_pos (k : ℕ) : 0 < monoScale k := by
  unfold monoScale
  have := Real.sqrt_pos.mpr (show (0 : ℝ) < 8 * π by positivity)
  positivity

theorem toLagFun_profFun_X_pow (k : ℕ) {x : ℝ} (hx : 0 < x) :
    toLagFun (B0094.profFun (X ^ k)) x = (monoScale k : ℂ) * (x : ℂ) ^ k := by
  rw [toLagFun, B0094.profFun_X_pow, ← Complex.ofReal_mul, ← Complex.ofReal_pow,
    ← Complex.ofReal_mul]
  congr 1
  simp only [lagFactor, B0094.monoReal, monoScale]
  have h1 : (2 * Real.sqrt x) ^ (2 + 2 * k) = 4 ^ (k + 1) * x ^ (k + 1) := by
    rw [show 2 + 2 * k = 2 * (k + 1) by ring, pow_mul, mul_pow, Real.sq_sqrt hx.le, mul_pow]
    norm_num
  have h2 : (2 * Real.sqrt x) ^ 2 / 4 = x := sq_two_sqrt_div_four hx
  rw [h1, h2, Real.exp_neg]
  field_simp
  ring

theorem coeFn_xGToLaguerre_vmono (k : ℕ) :
    (xGToLaguerre (B0094.vmono k) : ℝ → ℂ) =ᵐ[laguerreMeasure]
      fun x => (monoScale k : ℂ) * (x : ℂ) ^ k := by
  refine (coeFn_toLagLinear (B0094.vmono k)).trans ?_
  have h := toLagFun_congr_ae (Lp.stronglyMeasurable (B0094.vmono k))
    (B0094.continuous_profFun (X ^ k)).stronglyMeasurable (B0094.coeFn_prof (X ^ k))
  refine h.trans ?_
  filter_upwards [ae_laguerreMeasure_pos] with x hx
  exact toLagFun_profFun_X_pow k hx

theorem memLp_monomial (k : ℕ) : MemLp (fun x : ℝ => (x : ℂ) ^ k) 2 laguerreMeasure := by
  refine (Lp.memLp (((monoScale k : ℂ))⁻¹ • xGToLaguerre (B0094.vmono k))).ae_eq ?_
  have hne : (monoScale k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (monoScale_pos k).ne'
  filter_upwards [Lp.coeFn_smul ((monoScale k : ℂ))⁻¹ (xGToLaguerre (B0094.vmono k)),
    coeFn_xGToLaguerre_vmono k] with x h1 h2
  rw [h1, Pi.smul_apply, h2, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-- The monomial `x^k` in `L²(x² e^{-x} dx)`. -/
def laguerreMono (k : ℕ) : LaguerreL2 := (memLp_monomial k).toLp _

theorem coeFn_laguerreMono (k : ℕ) :
    (laguerreMono k : ℝ → ℂ) =ᵐ[laguerreMeasure] fun x : ℝ => (x : ℂ) ^ k :=
  (memLp_monomial k).coeFn_toLp

/-- The B0094 profile `r^{2+2k} e^{-r²/4}` is sent to `√(8π) 4^{k+1} x^k`. -/
theorem xGToLaguerre_vmono (k : ℕ) :
    xGToLaguerre (B0094.vmono k) = (monoScale k : ℂ) • laguerreMono k := by
  apply Lp.ext
  filter_upwards [coeFn_xGToLaguerre_vmono k, Lp.coeFn_smul (monoScale k : ℂ) (laguerreMono k),
    coeFn_laguerreMono k] with x h1 h2 h3
  rw [h1, h2, Pi.smul_apply, h3, smul_eq_mul]

theorem laguerreMono_eq (k : ℕ) :
    laguerreMono k = ((monoScale k : ℂ))⁻¹ • xGToLaguerre (B0094.vmono k) := by
  have hne : (monoScale k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (monoScale_pos k).ne'
  rw [xGToLaguerre_vmono, smul_smul, inv_mul_cancel₀ hne, one_smul]

/-- The monomials are linearly independent in `L²(x² e^{-x} dx)`. -/
theorem linearIndependent_laguerreMono : LinearIndependent ℂ laguerreMono := by
  have h := B0094.linearIndependent_vmono.map' xGToLaguerre.toLinearEquiv.toLinearMap
    (LinearEquiv.ker _)
  have hu : ∀ k, (monoScale k : ℂ)⁻¹ ≠ 0 := fun k =>
    inv_ne_zero (Complex.ofReal_ne_zero.mpr (monoScale_pos k).ne')
  have h2 := h.units_smul (fun k => Units.mk0 _ (hu k))
  have e : laguerreMono =
      (fun k => Units.mk0 _ (hu k)) • (⇑xGToLaguerre.toLinearEquiv.toLinearMap ∘ B0094.vmono) := by
    funext k
    rw [Pi.smul_apply', Units.smul_mk0, laguerreMono_eq]
    rfl
  rw [e]
  exact h2

/-- Completeness of the monomials: a vector of `L²(x² e^{-x} dx)` orthogonal to every `x^k`
vanishes (scoping note §4, B6 "Completeness"; transported from `B0094.eq_zero_of_inner_prof_X_pow`). -/
theorem eq_zero_of_forall_inner_laguerreMono {g : LaguerreL2}
    (hg : ∀ k, ⟪laguerreMono k, g⟫_ℂ = 0) : g = 0 := by
  set h := xGToLaguerre.symm g with hh
  have horth : ∀ k, ⟪B0094.prof (X ^ k), h⟫_ℂ = 0 := by
    intro k
    rw [← LinearIsometryEquiv.inner_map_map xGToLaguerre, hh,
      LinearIsometryEquiv.apply_symm_apply]
    change ⟪xGToLaguerre (B0094.vmono k), g⟫_ℂ = 0
    rw [xGToLaguerre_vmono, inner_smul_left, hg k, mul_zero]
  have h0 : h = 0 := B0094.eq_zero_of_inner_prof_X_pow h horth
  rw [← xGToLaguerre.apply_symm_apply g, ← hh, h0, map_zero]

/-- **H2** completeness (scoping note §5, Level H): `(span {x^k})ᗮ = ⊥`. -/
theorem span_monomials_orthogonal_eq_bot :
    (Submodule.span ℂ (Set.range laguerreMono))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro g hg
  exact eq_zero_of_forall_inner_laguerreMono fun k =>
    Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (Set.mem_range_self k)) hg

/-- The Gram--Schmidt orthonormalization of the monomials (normalized generalized Laguerre
functions with `α = 2`, up to sign conventions). -/
def laguerreFun (n : ℕ) : LaguerreL2 := InnerProductSpace.gramSchmidtNormed ℂ laguerreMono n

theorem orthonormal_laguerreFun : Orthonormal ℂ laguerreFun :=
  InnerProductSpace.gramSchmidtNormed_orthonormal linearIndependent_laguerreMono

theorem span_laguerreFun :
    Submodule.span ℂ (Set.range laguerreFun) = Submodule.span ℂ (Set.range laguerreMono) := by
  change Submodule.span ℂ (Set.range (InnerProductSpace.gramSchmidtNormed ℂ laguerreMono)) = _
  rw [InnerProductSpace.span_gramSchmidtNormed_range, InnerProductSpace.span_gramSchmidt]

/-- **H2** (scoping note §5, Level H; bypass B6): the Laguerre Hilbert basis of
`L²((0,∞), x² e^{-x} dx)`, Gram--Schmidt of the monomials. -/
def laguerreBasis : HilbertBasis ℕ ℂ LaguerreL2 :=
  HilbertBasis.mkOfOrthogonalEqBot orthonormal_laguerreFun
    (by rw [span_laguerreFun]; exact span_monomials_orthogonal_eq_bot)

theorem coe_laguerreBasis :
    ⇑laguerreBasis = InnerProductSpace.gramSchmidtNormed ℂ laguerreMono :=
  HilbertBasis.coe_mkOfOrthogonalEqBot _ _

/-- The transported Hilbert basis of `X_G`. -/
def xGLaguerreBasis : HilbertBasis ℕ ℂ XG :=
  HilbertBasis.ofRepr (xGToLaguerre.trans laguerreBasis.repr)

theorem xGLaguerreBasis_apply (n : ℕ) :
    xGLaguerreBasis n = xGToLaguerre.symm (laguerreBasis n) :=
  rfl

end UnforcedLeray.PlanarSpectral
