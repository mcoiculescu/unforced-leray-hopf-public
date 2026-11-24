import UnforcedLeray.Analysis.Sturm.BirmanSchwingerOperator
import UnforcedLeray.Analysis.Sturm.EigenfunctionRegularity
import UnforcedLeray.Analysis.Sturm.NeutralCoercivity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

/-!
# INF10 S3: no two-dimensional nonpositive subspace for `B_m = I - N_m`


bypass B2 and target S3. The manuscript states at tex line 948 (blueprint unit B0029, from the
codimension-one positivity `eq:st18-t00030`, tex lines 941--947, unit B0028) that for `n > 1`
every nonpositive spectral subspace of `𝓗_n = -∂_t² + n² - W` has dimension at most one. Its
Birman--Schwinger form (tex lines 1308--1320, units B0072, B0073) transfers this to
`B_n = I - K_n` with `K_n = √v (-Δ_n)⁻¹ √v`. In logarithmic radius `t = log r`
(tex lines 820--836) `K_n` is the compiled operator `N_m = birmanSchwingerOperator hm`
(`W^{1/2} (m² - ∂²)⁻¹ W^{1/2}` on `L²(ℝ, dt)`).

We prove the statement of bypass B2 step 3 directly, without spectral theory:

* `inner_freeResolventOperator_self`: for every `g ∈ L²`, with `F = (m² - ∂²)⁻¹ g`,
  `⟪F, g⟫ = ‖F'‖² + m² ‖F‖²` (the compact-data identity extended by density).
* `eq_zero_of_nonpositive_of_trace_zero`: if `Re⟪B_m v, v⟫ ≤ 0` and `F_v = (m² - ∂²)⁻¹ W^{1/2} v`
  vanishes at the critical time `t_* = log √8`, then `v = 0` (for `m > 1`). Proof: Cauchy--Schwarz
  gives `‖F_v‖²_{H¹_m} ≤ ‖W^{1/2} F_v‖²`, i.e. `⟪F_v, 𝓗_m F_v⟫ ≤ 0`, and the compiled
  `quadraticForm_trace_zero_coercive` (`eq:st18-t00030`) then forces `F_v = 0`.
* `not_exists_two_dim_nonpositive` (S3): no `V` with `finrank V = 2` and `Re⟪B_m v, v⟫ ≤ 0` on `V`;
  the trace `v ↦ F_v(t_*)` is a linear functional, so it has a nonzero zero on `V`.
* `not_neutral_pair`: the form used by S4: two linearly independent vectors on which the
  sesquilinear form `⟪x, B_m y⟫` vanishes identically do not exist.
-/

set_option autoImplicit false

noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ComplexConjugate
namespace UnforcedLeray.Sturm
open GaussianPotential

namespace PlanarIndex

/-! ## The energy identity for every `L²` datum -/

section Energy
variable {L : ℝ} (hL : 0 < L)
include hL

/-- `∫ |(m² - ∂²)⁻¹ g|² = ‖R g‖²` for the pointwise Green convolution of an arbitrary `L²` datum. -/
theorem integral_norm_sq_freeResolvent (g : ComplexL2) :
    (∫ x, ‖freeResolvent L (g : ℝ → ℂ) x‖ ^ 2) = ‖freeResolventOperator hL g‖ ^ 2 :=
  (freeResolventC1Representative hL g).integral_norm_sq

/-- `∫ |∂(m² - ∂²)⁻¹ g|² = ‖R' g‖²` for an arbitrary `L²` datum. -/
theorem integral_norm_sq_freeResolventDeriv (g : ComplexL2) :
    (∫ x, ‖freeResolventDeriv L (g : ℝ → ℂ) x‖ ^ 2) =
      ‖freeResolventDerivativeOperator hL g‖ ^ 2 := by
  have h := (freeResolventC1Representative hL g).integral_derivative_norm_sq
  simp only [freeResolventC1Representative_value,
    deriv_freeResolvent_of_memLp hL (Lp.memLp g)] at h
  exact h

/-- The energy identity `⟪R g, g⟫ = ‖R' g‖² + L² ‖R g‖²` for every `g ∈ L²(ℝ)` (bypass B2 step 3:
`⟨N_m u, u⟩ = ‖F_u‖²_{H¹_m}`). -/
theorem inner_freeResolventOperator_self (f : ComplexL2) :
    ⟪freeResolventOperator hL f, f⟫_ℂ =
      ((‖freeResolventDerivativeOperator hL f‖ ^ 2 +
        L ^ 2 * ‖freeResolventOperator hL f‖ ^ 2 : ℝ) : ℂ) := by
  refine denseRange_compactL2_subtypeL.induction_on
    (p := fun u => ⟪freeResolventOperator hL u, u⟫_ℂ =
      ((‖freeResolventDerivativeOperator hL u‖ ^ 2 +
        L ^ 2 * ‖freeResolventOperator hL u‖ ^ 2 : ℝ) : ℂ)) f
    (isClosed_eq (by fun_prop)
      (Complex.continuous_ofReal.comp (by fun_prop))) ?_
  intro g
  change ⟪freeResolventOperator hL (g : ComplexL2), (g : ComplexL2)⟫_ℂ = _
  rw [freeResolventOperator_pairing_energy_compact hL g,
    integral_norm_sq_freeResolvent hL, integral_norm_sq_freeResolventDeriv hL]
  rfl

end Energy

/-! ## Real and imaginary parts of a `C¹` representative -/

theorem deriv_re_of_differentiable {F : ℝ → ℂ} (hF : Differentiable ℝ F) :
    deriv (fun t => (F t).re) = fun t => (deriv F t).re := by
  funext t
  exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hF t).hasDerivAt).deriv

theorem deriv_im_of_differentiable {F : ℝ → ℂ} (hF : Differentiable ℝ F) :
    deriv (fun t => (F t).im) = fun t => (deriv F t).im := by
  funext t
  exact (Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hF t).hasDerivAt).deriv

theorem integral_norm_sq_eq_re_im {F : ℝ → ℂ} (hF : MemLp F 2 volume) :
    (∫ t, ‖F t‖ ^ 2) = (∫ t, (F t).re ^ 2) + ∫ t, (F t).im ^ 2 := by
  have h : (fun t => ‖F t‖ ^ 2) = fun t => (F t).re ^ 2 + (F t).im ^ 2 := by
    funext t
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [h]
  exact integral_add hF.re.integrable_sq hF.im.integrable_sq

theorem integral_W_norm_sq_eq_re_im {F : ℝ → ℂ} (hF : MemLp F 2 volume) :
    (∫ t, Wlog t * ‖F t‖ ^ 2) =
      (∫ t, Wlog t * (F t).re ^ 2) + ∫ t, Wlog t * (F t).im ^ 2 := by
  have h : (fun t => Wlog t * ‖F t‖ ^ 2) =
      fun t => Wlog t * (F t).re ^ 2 + Wlog t * (F t).im ^ 2 := by
    funext t
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [h]
  exact integral_add (integrable_potential hF.re) (integrable_potential hF.im)

/-- The complex form of `eq:st18-t00030` (tex lines 941--947, unit B0028): for a `C¹` function
`F` with `F, F' ∈ L²` and `F(t_*) = 0`,
`(m² - 1) ∫ |F|² ≤ ∫ |F'|² + m² ∫ |F|² - ∫ W |F|²`. -/
theorem complex_trace_zero_coercive {F : ℝ → ℂ} (hF : ContDiff ℝ 1 F)
    (hF2 : MemLp F 2 volume) (hdF2 : MemLp (deriv F) 2 volume)
    (htr : F neutralCriticalTime = 0) (m : ℝ) :
    (m ^ 2 - 1) * (∫ t, ‖F t‖ ^ 2) ≤
      (∫ t, ‖deriv F t‖ ^ 2) + m ^ 2 * (∫ t, ‖F t‖ ^ 2) - ∫ t, Wlog t * ‖F t‖ ^ 2 := by
  have hd : Differentiable ℝ F := hF.differentiable one_ne_zero
  have hre := quadraticForm_trace_zero_coercive (f := fun t => (F t).re)
    (Complex.reCLM.contDiff.comp hF) hF2.re
    (by rw [deriv_re_of_differentiable hd]; exact hdF2.re)
    (by simp only [htr, Complex.zero_re]) m
  have him := quadraticForm_trace_zero_coercive (f := fun t => (F t).im)
    (Complex.imCLM.contDiff.comp hF) hF2.im
    (by rw [deriv_im_of_differentiable hd]; exact hdF2.im)
    (by simp only [htr, Complex.zero_im]) m
  have hdre : MemLp (deriv fun t => (F t).re) 2 volume := by
    rw [deriv_re_of_differentiable hd]; exact hdF2.re
  have hdim : MemLp (deriv fun t => (F t).im) 2 volume := by
    rw [deriv_im_of_differentiable hd]; exact hdF2.im
  have hre_e : quadraticForm m (fun t => (F t).re) (deriv fun t => (F t).re) =
      (∫ t, (deriv F t).re ^ 2) + m ^ 2 * (∫ t, (F t).re ^ 2) -
        ∫ t, Wlog t * (F t).re ^ 2 := by
    rw [quadraticForm_expansion (f := fun t => (F t).re) hF2.re hdre m,
      deriv_re_of_differentiable hd]
  have him_e : quadraticForm m (fun t => (F t).im) (deriv fun t => (F t).im) =
      (∫ t, (deriv F t).im ^ 2) + m ^ 2 * (∫ t, (F t).im ^ 2) -
        ∫ t, Wlog t * (F t).im ^ 2 := by
    rw [quadraticForm_expansion (f := fun t => (F t).im) hF2.im hdim m,
      deriv_im_of_differentiable hd]
  rw [integral_norm_sq_eq_re_im hF2, integral_norm_sq_eq_re_im hdF2,
    integral_W_norm_sq_eq_re_im hF2]
  linarith

/-! ## The Green profile `F_v = (m² - ∂²)⁻¹ W^{1/2} v` and its trace at `t_*` -/

section Trace
variable {m : ℝ} (hm : 0 < m)
include hm

/-- `F_v` is continuous, as the `C¹` representative of `R_m W^{1/2} v`. -/
theorem continuous_greenProfile (v : ComplexL2) :
    Continuous (freeResolvent m (complexPotentialSqrtOperator v : ℝ → ℂ)) :=
  (contDiff_one_freeResolvent_of_memLp hm (Lp.memLp _)).continuous

/-- `F_{v+w} = F_v + F_w` everywhere (continuous representatives of equal `L²` classes). -/
theorem greenProfile_add (v w : ComplexL2) :
    freeResolvent m (complexPotentialSqrtOperator (v + w) : ℝ → ℂ) =
      freeResolvent m (complexPotentialSqrtOperator v : ℝ → ℂ) +
        freeResolvent m (complexPotentialSqrtOperator w : ℝ → ℂ) := by
  refine (Continuous.ae_eq_iff_eq volume (continuous_greenProfile hm (v + w))
    ((continuous_greenProfile hm v).add (continuous_greenProfile hm w))).mp ?_
  have h0 : freeResolventOperator hm (complexPotentialSqrtOperator (v + w)) =
      freeResolventOperator hm (complexPotentialSqrtOperator v) +
        freeResolventOperator hm (complexPotentialSqrtOperator w) := by
    rw [map_add, map_add]
  have h1 := coeFn_freeResolventOperator hm (complexPotentialSqrtOperator (v + w))
  have h2 := coeFn_freeResolventOperator hm (complexPotentialSqrtOperator v)
  have h3 := coeFn_freeResolventOperator hm (complexPotentialSqrtOperator w)
  have h4 := Lp.coeFn_add (freeResolventOperator hm (complexPotentialSqrtOperator v))
    (freeResolventOperator hm (complexPotentialSqrtOperator w))
  rw [h0] at h1
  filter_upwards [h1, h2, h3, h4] with x hx1 hx2 hx3 hx4
  rw [← hx1, hx4, Pi.add_apply, hx2, hx3, Pi.add_apply]

/-- `F_{c v} = c F_v` everywhere. -/
theorem greenProfile_smul (c : ℂ) (v : ComplexL2) :
    freeResolvent m (complexPotentialSqrtOperator (c • v) : ℝ → ℂ) =
      c • freeResolvent m (complexPotentialSqrtOperator v : ℝ → ℂ) := by
  refine (Continuous.ae_eq_iff_eq volume (continuous_greenProfile hm (c • v))
    ((continuous_greenProfile hm v).const_smul c)).mp ?_
  have h0 : freeResolventOperator hm (complexPotentialSqrtOperator (c • v)) =
      c • freeResolventOperator hm (complexPotentialSqrtOperator v) := by
    rw [map_smul, map_smul]
  have h1 := coeFn_freeResolventOperator hm (complexPotentialSqrtOperator (c • v))
  have h2 := coeFn_freeResolventOperator hm (complexPotentialSqrtOperator v)
  have h4 := Lp.coeFn_smul c (freeResolventOperator hm (complexPotentialSqrtOperator v))
  rw [h0] at h1
  filter_upwards [h1, h2, h4] with x hx1 hx2 hx4
  rw [← hx1, hx4, Pi.smul_apply, hx2, Pi.smul_apply]

/-- The trace functional `v ↦ F_v(t_*)`, `t_* = log √8` (tex line 925). -/
def traceFunctional : ComplexL2 →ₗ[ℂ] ℂ where
  toFun v := freeResolvent m (complexPotentialSqrtOperator v : ℝ → ℂ) neutralCriticalTime
  map_add' v w := by rw [greenProfile_add hm v w, Pi.add_apply]
  map_smul' c v := by rw [greenProfile_smul hm c v, Pi.smul_apply]; rfl

theorem traceFunctional_apply (v : ComplexL2) :
    traceFunctional hm v =
      freeResolvent m (complexPotentialSqrtOperator v : ℝ → ℂ) neutralCriticalTime := rfl

/-- `⟪N_m v, v⟫ = ⟪R_m W^{1/2} v, W^{1/2} v⟫`. -/
theorem inner_birmanSchwingerOperator_self (v : ComplexL2) :
    ⟪birmanSchwingerOperator hm v, v⟫_ℂ =
      ⟪freeResolventOperator hm (complexPotentialSqrtOperator v),
        complexPotentialSqrtOperator v⟫_ℂ := by
  rw [birmanSchwingerOperator_apply]
  exact complexPotentialSqrtOperator_isSelfAdjoint.isSymmetric _ _

/-- `⟪N_m v, v⟫ = ‖F_v'‖² + m² ‖F_v‖²` is real and nonnegative. -/
theorem inner_birmanSchwingerOperator_self_eq (v : ComplexL2) :
    ⟪birmanSchwingerOperator hm v, v⟫_ℂ =
      ((‖freeResolventDerivativeOperator hm (complexPotentialSqrtOperator v)‖ ^ 2 +
        m ^ 2 * ‖freeResolventOperator hm (complexPotentialSqrtOperator v)‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_birmanSchwingerOperator_self hm, inner_freeResolventOperator_self hm]

/-- `Re⟪B_m v, v⟫ = ‖v‖² - Re⟪N_m v, v⟫`. -/
theorem re_inner_one_sub_birmanSchwinger (v : ComplexL2) :
    (⟪(1 - birmanSchwingerOperator hm) v, v⟫_ℂ).re =
      ‖v‖ ^ 2 - (⟪birmanSchwingerOperator hm v, v⟫_ℂ).re := by
  have h : (⟪v, v⟫_ℂ).re = ‖v‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) v
  change (⟪v - birmanSchwingerOperator hm v, v⟫_ℂ).re = _
  rw [inner_sub_left, Complex.sub_re, h]

end Trace

/-- **Key step of bypass B2** (scoping note §4, B2 step 3). If `m > 1`, `Re⟪B_m v, v⟫ ≤ 0`, and
the Green profile `F_v = (m² - ∂²)⁻¹ W^{1/2} v` vanishes at `t_* = log √8`, then `v = 0`.
This is where `eq:st18-t00030` (tex lines 941--947, unit B0028) enters. -/
theorem eq_zero_of_nonpositive_of_trace_zero {m : ℝ} (hm1 : 1 < m) (v : ComplexL2)
    (hv : (⟪(1 - birmanSchwingerOperator (by linarith : (0 : ℝ) < m)) v, v⟫_ℂ).re ≤ 0)
    (htr : traceFunctional (by linarith : (0 : ℝ) < m) v = 0) : v = 0 := by
  have hm : (0 : ℝ) < m := by linarith
  set g := complexPotentialSqrtOperator v with hg
  set Rg := freeResolventOperator hm g with hRg
  set rep := freeResolventC1Representative hm g with hrep
  set E : ℝ := ‖freeResolventDerivativeOperator hm g‖ ^ 2 + m ^ 2 * ‖Rg‖ ^ 2 with hE
  have hE0 : 0 ≤ E := by positivity
  have hNv : ⟪birmanSchwingerOperator hm v, v⟫_ℂ = (E : ℂ) :=
    inner_birmanSchwingerOperator_self_eq hm v
  -- `‖v‖² ≤ E`
  have hvE : ‖v‖ ^ 2 ≤ E := by
    have h := re_inner_one_sub_birmanSchwinger hm v
    rw [hNv, Complex.ofReal_re] at h
    linarith
  -- `E ≤ ‖W^{1/2} F‖ ‖v‖`
  have hEle : E ≤ ‖complexPotentialSqrtOperator Rg‖ * ‖v‖ := by
    have h1 : ⟪Rg, g⟫_ℂ = (E : ℂ) := by
      rw [← hNv, inner_birmanSchwingerOperator_self hm]
    have h2 : ⟪Rg, g⟫_ℂ = ⟪complexPotentialSqrtOperator Rg, v⟫_ℂ :=
      (complexPotentialSqrtOperator_isSelfAdjoint.isSymmetric Rg v).symm
    have h3 := norm_inner_le_norm (𝕜 := ℂ) (complexPotentialSqrtOperator Rg) v
    rw [← h2, h1, Complex.norm_real, Real.norm_eq_abs] at h3
    exact (le_abs_self E).trans h3
  -- hence `E ≤ ‖W^{1/2} F‖²`
  set a := ‖complexPotentialSqrtOperator Rg‖ with ha
  have ha0 : 0 ≤ a := norm_nonneg _
  have hEa : E ≤ a ^ 2 := by
    rcases hE0.eq_or_lt with h0 | hpos
    · rw [← h0]; positivity
    · have hsq : E * E ≤ a ^ 2 * E := by
        calc E * E ≤ (a * ‖v‖) * (a * ‖v‖) :=
              mul_self_le_mul_self hE0 hEle
          _ = a ^ 2 * ‖v‖ ^ 2 := by ring
          _ ≤ a ^ 2 * E := mul_le_mul_of_nonneg_left hvE (sq_nonneg a)
      exact le_of_mul_le_mul_right hsq hpos
  -- translate into integrals of the classical representative
  have hval : rep.value = freeResolvent m (g : ℝ → ℂ) := rfl
  have hI1 : (∫ t, ‖rep.value t‖ ^ 2) = ‖Rg‖ ^ 2 := rep.integral_norm_sq
  have hI2 : (∫ t, ‖deriv rep.value t‖ ^ 2) = ‖freeResolventDerivativeOperator hm g‖ ^ 2 :=
    rep.integral_derivative_norm_sq
  have hI3 : (∫ t, Wlog t * ‖rep.value t‖ ^ 2) = a ^ 2 := by
    rw [ha, norm_complexPotentialSqrtOperator_sq]
    apply integral_congr_ae
    filter_upwards [rep.value_ae] with t ht
    rw [ht]
  have hcoer := complex_trace_zero_coercive rep.contDiff rep.memLp rep.deriv_memLp
    (by rw [hval]; exact htr) m
  rw [hI1, hI2, hI3] at hcoer
  -- `(m² - 1) ‖R g‖² ≤ E - a² ≤ 0`
  have hm2 : 0 < m ^ 2 - 1 := by nlinarith
  have hR0 : ‖Rg‖ ^ 2 = 0 := by
    have : (m ^ 2 - 1) * ‖Rg‖ ^ 2 ≤ 0 := by linarith
    exact le_antisymm (nonpos_of_mul_nonpos_right this hm2) (sq_nonneg _)
  have hRg0 : Rg = 0 := by
    have : ‖Rg‖ = 0 := (pow_eq_zero_iff two_ne_zero).mp hR0
    exact norm_eq_zero.mp this
  -- then `⟪N v, v⟫ = 0`, so `‖v‖² ≤ 0`
  have hE' : E = 0 := by
    have h1 : ⟪Rg, g⟫_ℂ = (E : ℂ) := by
      rw [← hNv, inner_birmanSchwingerOperator_self hm]
    rw [hRg0, inner_zero_left] at h1
    exact_mod_cast h1.symm
  have : ‖v‖ ^ 2 ≤ 0 := hE' ▸ hvE
  exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
    (le_antisymm this (sq_nonneg _)))

/-- **S3** (scoping note §5, Level S; bypass B2 step 3; replaces the counting statement of
B0029, tex line 948, and of B0072--B0073, tex lines 1308--1320). For `m > 1` there is no
two-dimensional complex subspace `V ⊆ L²(ℝ)` on which `Re⟪(I - N_m) v, v⟫ ≤ 0`. -/
theorem _root_.UnforcedLeray.Sturm.not_exists_two_dim_nonpositive {m : ℝ} (hm : 1 < m) :
    ¬ ∃ V : Submodule ℂ ComplexL2, Module.finrank ℂ V = 2 ∧
      ∀ v ∈ V, (⟪(1 - birmanSchwingerOperator (by linarith : 0 < m)) v, v⟫_ℂ).re ≤ 0 := by
  rintro ⟨V, hV, hneg⟩
  have hm0 : (0 : ℝ) < m := by linarith
  have : FiniteDimensional ℂ V := Module.finite_of_finrank_pos (by omega)
  let φ : V →ₗ[ℂ] ℂ := (traceFunctional hm0).comp V.subtype
  have hrank := LinearMap.finrank_range_add_finrank_ker φ
  have hle : Module.finrank ℂ (LinearMap.range φ) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range φ)
    simpa using this
  have hker : 0 < Module.finrank ℂ (LinearMap.ker φ) := by omega
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Submodule.one_le_finrank_iff.mp hker)
  have hw' : traceFunctional hm0 (w : ComplexL2) = 0 := LinearMap.mem_ker.mp hw
  have hwV := hneg (w : ComplexL2) w.2
  have := eq_zero_of_nonpositive_of_trace_zero hm (w : ComplexL2) hwV hw'
  exact hw0 (Subtype.ext this)

/-- The neutral-pair form of S3 used in S4: for `m > 1`, there are no two linearly independent
vectors `x, y` on which the sesquilinear form `(u, w) ↦ ⟪u, B_m w⟫` vanishes identically. -/
theorem not_neutral_pair {m : ℝ} (hm : 1 < m) {x y : ComplexL2}
    (hxy : LinearIndependent ℂ ![x, y])
    (hxx : ⟪x, (1 - birmanSchwingerOperator (by linarith : (0 : ℝ) < m)) x⟫_ℂ = 0)
    (hxy' : ⟪x, (1 - birmanSchwingerOperator (by linarith : (0 : ℝ) < m)) y⟫_ℂ = 0)
    (hyx : ⟪y, (1 - birmanSchwingerOperator (by linarith : (0 : ℝ) < m)) x⟫_ℂ = 0)
    (hyy : ⟪y, (1 - birmanSchwingerOperator (by linarith : (0 : ℝ) < m)) y⟫_ℂ = 0) :
    False := by
  have hm0 : (0 : ℝ) < m := by linarith
  set B := (1 - birmanSchwingerOperator hm0) with hB
  have h1 : ⟪B x, x⟫_ℂ = 0 := by rw [← inner_conj_symm, hxx, map_zero]
  have h2 : ⟪B x, y⟫_ℂ = 0 := by rw [← inner_conj_symm, hyx, map_zero]
  have h3 : ⟪B y, x⟫_ℂ = 0 := by rw [← inner_conj_symm, hxy', map_zero]
  have h4 : ⟪B y, y⟫_ℂ = 0 := by rw [← inner_conj_symm, hyy, map_zero]
  apply not_exists_two_dim_nonpositive hm
  refine ⟨Submodule.span ℂ (Set.range ![x, y]), ?_, ?_⟩
  · rw [finrank_span_eq_card hxy]
    simp
  · intro v hv
    rw [Matrix.range_cons_cons_empty] at hv
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hv
    have hzero : ⟪B (a • x + b • y), a • x + b • y⟫_ℂ = 0 := by
      simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
        inner_smul_right, h1, h2, h3, h4, mul_zero, add_zero]
    rw [hzero, Complex.zero_re]

end PlanarIndex
end UnforcedLeray.Sturm
