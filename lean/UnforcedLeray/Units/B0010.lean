import UnforcedLeray.Analysis.GaussianVortex.RadialProfile
import UnforcedLeray.Analysis.GaussianVortex.PlanarDefs
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Tactic

/-!
# B0010: the Gaussian angular-two space `X_G` (`eq:st18-t00005`)

Blueprint unit B0010, label `eq:st18-t00005`, `paper/main.tex` lines 672--678.

The manuscript defines
`X_G = {f(r,ϑ) = f₂(r) e^{2iϑ} : ∫₀^∞ |f₂(r)|² G(r)⁻¹ r dr < ∞}`,
(lines 673--676), where `G(y) = (4π)⁻¹ e^{-|y|²/4}` is the Gaussian weight of
`eq:st18-t00002` (line 648), read as a function of `r = |y|`. Line 678 says that the pairing of
`X_G` omits the angular factor `2π` and is linear in the first variable, i.e.
`⟨f, g⟩_{X_G} = ∫₀^∞ f₂ conj(g₂) G⁻¹ r dr`. That `X_G` is a complex Hilbert space is implicit
(line 660 states it for the neighbouring spaces `H^j_M`, `𝒳_{j,M}`; the blueprint statement of
B0010 states it for `X_G`).

In Lean, the profile space is `XG = Lp ℂ 2 xGMeasure`, where `xGMeasure` is Lebesgue measure on
`(0, ∞)` with density `G(r)⁻¹ r`. We prove:
* `memLp_iff_lintegral`, `memLp_iff_integrableOn`: a measurable profile lies in `XG` iff
  `∫₀^∞ |f₂|² G⁻¹ r dr < ∞` (as a Lebesgue integral, so no Bochner junk value enters);
* `XG` is a complete complex inner product space (`XG_completeSpace`, `XG_innerProductSpace`);
* `pairing` is the manuscript's pairing, `pairing_eq_inner` identifies it with Mathlib's inner
  product with the arguments swapped (Mathlib's is linear in the second variable),
  `pairing_toLp` gives the integral formula, and `pairing_add_left`, `pairing_smul_left`,
  `pairing_conj_symm`, `pairing_self` give linearity in the first variable, Hermitian symmetry
  and `⟨f, f⟩ = ‖f‖²`;
* `angularTwoField` realizes a profile as the planar function `f₂(r) e^{2iϑ}`,
  `angularTwoField_polar` evaluates it in every polar representation, `XGSet` is the set
  of lines 674--675 as a set of planar functions, and `integral_plane_pairing` /
  `pairing_toLp_eq_planar` prove that the planar weighted pairing
  `∫_{ℝ²} f conj(g) G⁻¹ dy` equals `2π ⟨f, g⟩_{X_G}`: this is the omitted angular factor;
* `exists_ne_zero`: `XG` is not the zero space (sanity check against a degenerate measure).

The dependency B0007 (`eq:st18-t00002`) provides `GaussianVortex.radialOmega r = e^{-r²/4}` and
`GaussianVortex.planarGaussian z = e^{-|z|²/4}`; the normalized weight `G = (4π)⁻¹ e^{-|y|²/4}`
is not in the compiled library, so it is defined here from those profiles.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal ComplexConjugate Real

namespace UnforcedLeray.B0010

open GaussianVortex

/-! ## The Gaussian weight -/

/-- The Gaussian weight `G(y) = (4π)⁻¹ e^{-|y|²/4}` on the plane (`eq:st18-t00002`, tex line 648),
built from the compiled profile `planarGaussian z = e^{-|z|²/4}` (with `|z|² = radiusSq z`). -/
def gaussianWeight (z : Plane) : ℝ := (4 * π)⁻¹ * planarGaussian z

/-- The radial profile of the Gaussian weight, `G(r) = (4π)⁻¹ e^{-r²/4}`, as it is used in
the integral of tex line 675. -/
def radialGaussianWeight (r : ℝ) : ℝ := (4 * π)⁻¹ * radialOmega r

theorem gaussianWeight_eq_radial (z : Plane) :
    gaussianWeight z = radialGaussianWeight (Real.sqrt (radiusSq z)) := by
  unfold gaussianWeight radialGaussianWeight planarGaussian radialOmega
  rw [Real.sq_sqrt (by unfold radiusSq; positivity)]

theorem radialGaussianWeight_pos (r : ℝ) : 0 < radialGaussianWeight r := by
  unfold radialGaussianWeight
  exact mul_pos (by positivity) (radialOmega_pos r)

theorem radialGaussianWeight_inv (r : ℝ) :
    (radialGaussianWeight r)⁻¹ = 4 * π * Real.exp (r ^ 2 / 4) := by
  unfold radialGaussianWeight radialOmega
  rw [mul_inv, inv_inv, ← Real.exp_neg, neg_neg]

/-! ## The weighted measure `G(r)⁻¹ r dr` on `(0, ∞)` -/

/-- The density `G(r)⁻¹ r`, as a nonnegative real (it is used only on `r > 0`). -/
def xGDensity (r : ℝ) : ℝ≥0 := Real.toNNReal ((radialGaussianWeight r)⁻¹ * r)

theorem xGDensity_eq (r : ℝ) :
    xGDensity r = Real.toNNReal (4 * π * Real.exp (r ^ 2 / 4) * r) := by
  rw [xGDensity, radialGaussianWeight_inv]

theorem measurable_xGDensity : Measurable xGDensity := by
  have h : xGDensity = fun r => Real.toNNReal (4 * π * Real.exp (r ^ 2 / 4) * r) :=
    funext xGDensity_eq
  rw [h]
  fun_prop

theorem coe_xGDensity {r : ℝ} (hr : 0 < r) :
    (xGDensity r : ℝ) = (radialGaussianWeight r)⁻¹ * r :=
  Real.coe_toNNReal _ (mul_nonneg (inv_nonneg.2 (radialGaussianWeight_pos r).le) hr.le)

/-- The measure `G(r)⁻¹ r dr` on `(0, ∞)` (tex line 675). -/
def xGMeasure : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity (fun r => (xGDensity r : ℝ≥0∞))

theorem xGMeasure_apply {s : Set ℝ} (hs : MeasurableSet s) :
    xGMeasure s =
      ∫⁻ r in s ∩ Ioi 0, ENNReal.ofReal ((radialGaussianWeight r)⁻¹ * r) := by
  rw [xGMeasure, withDensity_apply _ hs, Measure.restrict_restrict hs]
  rfl

/-! ## The space `X_G` of angular-two profiles -/

/-- The Gaussian angular-two space `X_G` of tex lines 673--676, realized on its radial
profiles `f₂`: `L²((0, ∞), G(r)⁻¹ r dr; ℂ)`. -/
abbrev XG : Type := Lp ℂ 2 xGMeasure

/-- `X_G` is complete (tex lines 673--678; implicit: `X_G` is a complex Hilbert space). -/
theorem XG_completeSpace : CompleteSpace XG := inferInstance

/-- `X_G` carries its complex inner product (tex lines 673--678, implicit). -/
abbrev XG_innerProductSpace : InnerProductSpace ℂ XG := inferInstance

/-- Membership in `X_G` (tex lines 674--675): a measurable profile `f₂` defines an element of `X_G`
iff `∫₀^∞ |f₂(r)|² G(r)⁻¹ r dr < ∞`, with the integral taken as a Lebesgue integral. -/
theorem memLp_iff_lintegral {f₂ : ℝ → ℂ}
    (hf : AEStronglyMeasurable f₂ (volume.restrict (Ioi 0))) :
    MemLp f₂ 2 xGMeasure ↔
      ∫⁻ r in Ioi 0, ‖f₂ r‖ₑ ^ 2 * ENNReal.ofReal ((radialGaussianWeight r)⁻¹ * r) < ∞ := by
  have hf' : AEStronglyMeasurable f₂ xGMeasure :=
    hf.mono_ac (withDensity_absolutelyContinuous _ _)
  rw [MemLp, and_iff_right hf',
    eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top,
    xGMeasure, lintegral_withDensity_eq_lintegral_mul₀
      measurable_xGDensity.coe_nnreal_ennreal.aemeasurable
      (hf.enorm.pow_const _)]
  have h : ∀ r, ((fun r => (xGDensity r : ℝ≥0∞)) *
      fun x => ‖f₂ x‖ₑ ^ (2 : ℝ≥0∞).toReal) r =
      ‖f₂ r‖ₑ ^ 2 * ENNReal.ofReal ((radialGaussianWeight r)⁻¹ * r) := by
    intro r
    simp only [Pi.mul_apply, ENNReal.toReal_ofNat, ENNReal.rpow_two]
    rw [mul_comm]
    rfl
  rw [lintegral_congr h]

/-- Membership in `X_G` (tex lines 674--675), Bochner form: a measurable profile `f₂` lies in `X_G`
iff `r ↦ |f₂(r)|² G(r)⁻¹ r` is integrable on `(0, ∞)`. -/
theorem memLp_iff_integrableOn {f₂ : ℝ → ℂ}
    (hf : AEStronglyMeasurable f₂ (volume.restrict (Ioi 0))) :
    MemLp f₂ 2 xGMeasure ↔
      IntegrableOn (fun r => ‖f₂ r‖ ^ 2 * ((radialGaussianWeight r)⁻¹ * r)) (Ioi 0) := by
  have hf' : AEStronglyMeasurable f₂ xGMeasure :=
    hf.mono_ac (withDensity_absolutelyContinuous _ _)
  rw [memLp_two_iff_integrable_sq_norm hf', xGMeasure,
    integrable_withDensity_iff_integrable_smul measurable_xGDensity]
  refine integrableOn_congr_fun (fun r hr => ?_) measurableSet_Ioi
  simp only [NNReal.smul_def, coe_xGDensity hr, smul_eq_mul]
  ring

/-! ## The pairing -/

/-- The pairing of `X_G` (tex line 678): `⟨f, g⟩_{X_G} = ∫₀^∞ f₂ conj(g₂) G⁻¹ r dr`,
without the angular factor `2π` and linear in the first variable. -/
def pairing (f g : XG) : ℂ := ∫ r, f r * conj (g r) ∂xGMeasure

/-- The manuscript's pairing is Mathlib's `L²` inner product with its arguments swapped
(Mathlib's inner product is linear in the second variable). -/
theorem pairing_eq_inner (f g : XG) : pairing f g = inner ℂ g f := by
  rw [pairing, MeasureTheory.L2.inner_def]
  congr 1

/-- The integral formula for the pairing of two profiles (tex lines 675, 678). -/
theorem pairing_toLp {f₂ g₂ : ℝ → ℂ} (hf : MemLp f₂ 2 xGMeasure) (hg : MemLp g₂ 2 xGMeasure) :
    pairing (hf.toLp f₂) (hg.toLp g₂) =
      ∫ r in Ioi 0, f₂ r * conj (g₂ r) * (((radialGaussianWeight r)⁻¹ * r : ℝ) : ℂ) := by
  have h1 : pairing (hf.toLp f₂) (hg.toLp g₂) = ∫ r, f₂ r * conj (g₂ r) ∂xGMeasure := by
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with r hfr hgr
    rw [hfr, hgr]
  rw [h1, xGMeasure, integral_withDensity_eq_integral_smul measurable_xGDensity]
  refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
  simp only [NNReal.smul_def, coe_xGDensity hr, Complex.real_smul]
  ring

/-- The pairing is additive in the first variable (tex line 678). -/
theorem pairing_add_left (f f' g : XG) : pairing (f + f') g = pairing f g + pairing f' g := by
  simp only [pairing_eq_inner, inner_add_right]

/-- The pairing is complex-linear (not conjugate-linear) in the first variable (tex line 678). -/
theorem pairing_smul_left (c : ℂ) (f g : XG) : pairing (c • f) g = c * pairing f g := by
  simp only [pairing_eq_inner, inner_smul_right]

/-- The pairing is Hermitian. -/
theorem pairing_conj_symm (f g : XG) : conj (pairing f g) = pairing g f := by
  simp only [pairing_eq_inner, inner_conj_symm]

/-- The pairing induces the norm of `X_G`. -/
theorem pairing_self (f : XG) : pairing f f = ((‖f‖ ^ 2 : ℝ) : ℂ) := by
  rw [pairing_eq_inner, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

/-- The norm of a profile in `X_G` (tex line 675): `‖f‖² = ∫₀^∞ |f₂|² G⁻¹ r dr`. -/
theorem norm_sq_toLp {f₂ : ℝ → ℂ} (hf : MemLp f₂ 2 xGMeasure) :
    ‖hf.toLp f₂‖ ^ 2 = ∫ r in Ioi 0, ‖f₂ r‖ ^ 2 * ((radialGaussianWeight r)⁻¹ * r) := by
  apply Complex.ofReal_injective
  rw [← pairing_self, pairing_toLp, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi (fun r _ => ?_)
  rw [Complex.mul_conj']
  push_cast
  ring

/-! ## The planar realization `f(r, ϑ) = f₂(r) e^{2iϑ}` -/

/-- The planar angular-two function `f(r, ϑ) = f₂(r) e^{2iϑ}` of tex line 674, where
`(r, ϑ) = polarCoord z` are the polar coordinates of `z` (`ϑ ∈ (-π, π]`). -/
def angularTwoField (f₂ : ℝ → ℂ) (z : ℝ × ℝ) : ℂ :=
  f₂ (polarCoord z).1 * Complex.exp (2 * Complex.I * (polarCoord z).2)

/-- `angularTwoField f₂` is `f₂(r) e^{2iϑ}` in every polar representation
`z = (r cos ϑ, r sin ϑ)`, `r > 0`, `ϑ ∈ ℝ`. -/
theorem angularTwoField_polar (f₂ : ℝ → ℂ) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    angularTwoField f₂ (r * Real.cos θ, r * Real.sin θ) =
      f₂ r * Complex.exp (2 * Complex.I * θ) := by
  unfold angularTwoField
  simp only [polarCoord_apply]
  have h1 : √((r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2) = r := by
    rw [show (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 by
      linear_combination r ^ 2 * Real.sin_sq_add_cos_sq θ]
    exact Real.sqrt_sq hr.le
  have h2 : Complex.equivRealProd.symm (r * Real.cos θ, r * Real.sin θ) =
      (r : ℂ) * (Complex.cos θ + Complex.sin θ * Complex.I) := by
    rw [Complex.equivRealProd_symm_apply]
    push_cast
    ring
  rw [h1, h2]
  congr 1
  have h3 := Complex.arg_mul_cos_add_sin_mul_I_sub hr θ
  have h4 : Complex.arg ((r : ℂ) * (Complex.cos θ + Complex.sin θ * Complex.I)) =
      θ + 2 * π * (⌊(π - θ) / (2 * π)⌋ : ℤ) := by linarith
  rw [h4]
  push_cast
  rw [show 2 * Complex.I * ((θ : ℂ) + 2 * π * (⌊(π - θ) / (2 * π)⌋ : ℂ)) =
      2 * Complex.I * θ + ((2 * ⌊(π - θ) / (2 * π)⌋ : ℤ) : ℂ) * (2 * π * Complex.I) by
    push_cast; ring]
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The profile is recovered from the planar function: `f₂(r) = f(r, 0)` for `r > 0`. -/
theorem angularTwoField_profile (f₂ : ℝ → ℂ) {r : ℝ} (hr : 0 < r) :
    angularTwoField f₂ (r, 0) = f₂ r := by
  have h := angularTwoField_polar f₂ hr 0
  simpa using h

/-- The set `X_G` of tex lines 673--676, as a set of planar functions `f = f₂(r) e^{2iϑ}`:
`f₂` is measurable on `(0, ∞)` and `∫₀^∞ |f₂(r)|² G(r)⁻¹ r dr < ∞`. -/
def XGSet : Set ((ℝ × ℝ) → ℂ) :=
  {f | ∃ f₂ : ℝ → ℂ, AEStronglyMeasurable f₂ (volume.restrict (Ioi 0)) ∧
    ∫⁻ r in Ioi 0, ‖f₂ r‖ₑ ^ 2 * ENNReal.ofReal ((radialGaussianWeight r)⁻¹ * r) < ∞ ∧
    f = angularTwoField f₂}

/-- The planar functions of `XGSet` are exactly the planar realizations of the profiles of the
Hilbert space `XG`. -/
theorem mem_XGSet_iff (f : (ℝ × ℝ) → ℂ) :
    f ∈ XGSet ↔ ∃ f₂ : ℝ → ℂ, AEStronglyMeasurable f₂ (volume.restrict (Ioi 0)) ∧
      MemLp f₂ 2 xGMeasure ∧ f = angularTwoField f₂ := by
  constructor
  · rintro ⟨f₂, hm, hi, rfl⟩
    exact ⟨f₂, hm, (memLp_iff_lintegral hm).2 hi, rfl⟩
  · rintro ⟨f₂, hm, hi, rfl⟩
    exact ⟨f₂, hm, (memLp_iff_lintegral hm).1 hi, rfl⟩

/-- The planar weighted pairing of two angular-two functions equals `2π` times the radial
pairing (tex line 678: the pairing of `X_G` omits the angular factor `2π`). No
integrability is needed: both sides are the same integral in two coordinate systems. -/
theorem integral_plane_pairing (f₂ g₂ : ℝ → ℂ) :
    ∫ z : ℝ × ℝ, angularTwoField f₂ z * conj (angularTwoField g₂ z) *
        (((gaussianWeight z)⁻¹ : ℝ) : ℂ) =
      (2 * π : ℂ) *
        ∫ r in Ioi 0, f₂ r * conj (g₂ r) * (((radialGaussianWeight r)⁻¹ * r : ℝ) : ℂ) := by
  rw [← integral_comp_polarCoord_symm]
  have key : ∀ p ∈ polarCoord.target,
      p.1 • (angularTwoField f₂ (polarCoord.symm p) *
        conj (angularTwoField g₂ (polarCoord.symm p)) *
        (((gaussianWeight (polarCoord.symm p))⁻¹ : ℝ) : ℂ)) =
      (f₂ p.1 * conj (g₂ p.1) * (((radialGaussianWeight p.1)⁻¹ * p.1 : ℝ) : ℂ)) *
        (fun _ : ℝ => (1 : ℂ)) p.2 := by
    intro p hp
    have hw : gaussianWeight (polarCoord.symm p) = radialGaussianWeight p.1 := by
      have hs : (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 = p.1 ^ 2 := by
        linear_combination p.1 ^ 2 * Real.sin_sq_add_cos_sq p.2
      unfold gaussianWeight radialGaussianWeight planarGaussian radialOmega radiusSq
      simp only [polarCoord_symm_apply]
      rw [hs]
    have hE : Complex.exp (2 * Complex.I * p.2) * conj (Complex.exp (2 * Complex.I * p.2)) = 1 := by
      rw [← Complex.exp_conj, ← Complex.exp_add]
      simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
      ring_nf
      exact Complex.exp_zero
    simp only [angularTwoField, polarCoord.right_inv hp, hw, Complex.real_smul, map_mul]
    push_cast
    linear_combination
      ((p.1 : ℂ) * f₂ p.1 * conj (g₂ p.1) * ((radialGaussianWeight p.1 : ℂ))⁻¹) * hE
  rw [setIntegral_congr_fun polarCoord.open_target.measurableSet key, polarCoord_target,
    Measure.volume_eq_prod,
    setIntegral_prod_mul (μ := volume) (ν := volume)
      (fun r => f₂ r * conj (g₂ r) * (((radialGaussianWeight r)⁻¹ * r : ℝ) : ℂ))
      (fun _ : ℝ => (1 : ℂ)) (Ioi 0) (Ioo (-π) π)]
  have hI : ∫ _ in Ioo (-π) π, (1 : ℂ) = (2 * π : ℂ) := by
    simp [integral_const]
    rw [max_eq_left (by positivity)]
    push_cast
    ring
  rw [hI, mul_comm]

/-- The pairing of `X_G` is the planar Gaussian-weighted pairing divided by `2π`
(tex line 678: it omits the angular factor `2π`). -/
theorem pairing_toLp_eq_planar {f₂ g₂ : ℝ → ℂ} (hf : MemLp f₂ 2 xGMeasure)
    (hg : MemLp g₂ 2 xGMeasure) :
    pairing (hf.toLp f₂) (hg.toLp g₂) =
      (2 * π : ℂ)⁻¹ * ∫ z : ℝ × ℝ, angularTwoField f₂ z * conj (angularTwoField g₂ z) *
        (((gaussianWeight z)⁻¹ : ℝ) : ℂ) := by
  rw [integral_plane_pairing, pairing_toLp, ← mul_assoc, inv_mul_cancel₀, one_mul]
  exact mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)

/-- The norm of `X_G` is the planar Gaussian-weighted `L²` norm divided by `2π`
(tex lines 675, 678). -/
theorem norm_sq_toLp_eq_planar {f₂ : ℝ → ℂ} (hf : MemLp f₂ 2 xGMeasure) :
    ((‖hf.toLp f₂‖ ^ 2 : ℝ) : ℂ) =
      (2 * π : ℂ)⁻¹ * ∫ z : ℝ × ℝ, angularTwoField f₂ z * conj (angularTwoField f₂ z) *
        (((gaussianWeight z)⁻¹ : ℝ) : ℂ) := by
  rw [← pairing_self, pairing_toLp_eq_planar]

/-! ## Nondegeneracy -/

/-- `X_G` is not the zero space. -/
theorem exists_ne_zero : ∃ f : XG, f ≠ 0 := by
  have hs : MeasurableSet (Ioc (1 : ℝ) 2) := measurableSet_Ioc
  have hμ : xGMeasure (Ioc 1 2) =
      ∫⁻ r in Ioc (1 : ℝ) 2, ENNReal.ofReal ((radialGaussianWeight r)⁻¹ * r) := by
    have hsub : Ioc (1 : ℝ) 2 ∩ Ioi 0 = Ioc 1 2 :=
      Set.inter_eq_left.2 (fun r (hr : r ∈ Ioc (1 : ℝ) 2) => show (0 : ℝ) < r from
        lt_trans one_pos hr.1)
    rw [xGMeasure_apply hs, hsub]
  have hle : ∀ r ∈ Ioc (1 : ℝ) 2, ENNReal.ofReal ((radialGaussianWeight r)⁻¹ * r) ≤
      ENNReal.ofReal (4 * π * Real.exp 1 * 2) := by
    intro r hr
    apply ENNReal.ofReal_le_ofReal
    rw [radialGaussianWeight_inv]
    have h1 : r ^ 2 / 4 ≤ 1 := by nlinarith [hr.1, hr.2]
    have h2 : Real.exp (r ^ 2 / 4) ≤ Real.exp 1 := Real.exp_le_exp.2 h1
    have hπ := Real.pi_pos
    have h3 := Real.exp_pos (r ^ 2 / 4)
    have h4 : (0 : ℝ) ≤ 4 * π * Real.exp (r ^ 2 / 4) := by positivity
    calc 4 * π * Real.exp (r ^ 2 / 4) * r ≤ 4 * π * Real.exp (r ^ 2 / 4) * 2 :=
          mul_le_mul_of_nonneg_left hr.2 h4
      _ ≤ 4 * π * Real.exp 1 * 2 := by gcongr
  have hge : ∀ r ∈ Ioc (1 : ℝ) 2,
      (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((radialGaussianWeight r)⁻¹ * r) := by
    intro r hr
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    rw [radialGaussianWeight_inv]
    have h1 : 1 ≤ Real.exp (r ^ 2 / 4) := Real.one_le_exp (by positivity)
    have hπ : 2 ≤ π := Real.two_le_pi
    have h5 : (1 : ℝ) ≤ 4 * π * Real.exp (r ^ 2 / 4) := by nlinarith
    nlinarith [hr.1]
  have hfin : xGMeasure (Ioc 1 2) ≠ ∞ := by
    rw [hμ]
    refine ne_top_of_le_ne_top ?_ (setLIntegral_mono measurable_const hle)
    rw [setLIntegral_const, Real.volume_Ioc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hpos : xGMeasure (Ioc 1 2) ≠ 0 := by
    rw [hμ]
    refine (lt_of_lt_of_le ?_ (setLIntegral_mono' hs hge)).ne'
    rw [setLIntegral_const, Real.volume_Ioc, one_mul]
    norm_num
  refine ⟨indicatorConstLp 2 hs hfin (1 : ℂ), fun h => ?_⟩
  have hn := norm_indicatorConstLp (p := 2) (hs := hs) (hμs := hfin) (c := (1 : ℂ))
    two_ne_zero ENNReal.ofNat_ne_top
  rw [h, norm_zero] at hn
  have h1 : 0 < xGMeasure.real (Ioc 1 2) := ENNReal.toReal_pos hpos hfin
  have h2 : 0 < ‖(1 : ℂ)‖ * xGMeasure.real (Ioc 1 2) ^ (1 / (2 : ℝ≥0∞).toReal) := by
    rw [norm_one, one_mul]
    exact Real.rpow_pos_of_pos h1 _
  linarith

end UnforcedLeray.B0010
