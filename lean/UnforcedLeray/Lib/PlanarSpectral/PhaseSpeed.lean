import UnforcedLeray.Lib.PlanarSpectral.IndexLemma
import UnforcedLeray.Analysis.Sturm.NeutralProfileDefs
import UnforcedLeray.Analysis.Sturm.FreeResolventSymmetry
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# INF10 S4: the phase-speed operator `C_m = Ω - J N_m` and its neutrality consequences


bypass B2 and target S4. The manuscript's bounded phase-speed operator is
`T̃_n = a_* I + J 𝓑_n = Ω - J 𝓚_n` (`eq:st18-t00057`, tex lines 1296--1301), with
`T̃_n^* 𝓑_n = 𝓑_n T̃_n` (`eq:st18-t00058`, tex lines 1302--1306). Here
`Ω(r) = e^{-r²/4}` (`eq:st18-t00001`, tex line 639), `a_* = e^{-2}` (`eq:st18-t00002`, tex line
646), `J = Ω - a_*`, and `𝓑_n = I - 𝓚_n`. In logarithmic radius `t = log r` (tex lines 820--836)
`𝓚_n` is the compiled `N_m = birmanSchwingerOperator hm` on `L²(ℝ, dt)` and `Ω` is
multiplication by `neutralOmega t = exp(-e^{2t}/4)`.

The manuscript applies Lin--Zeng's trichotomy theorem (tex lines 1325--1349; units B0074--B0077)
and the Fredholm closed-range argument of B0096 (tex line 1518). Bypass B2 replaces both by the
index lemma S3 (`not_exists_two_dim_nonpositive`, `IndexLemma.lean`):

* `adjoint_phaseSpeedOp_comp`: `C_m^† B_m = B_m C_m` (`eq:st18-t00058`); pure algebra, since
  `Ω - J = a_*` is a real scalar.
* `inner_B_eq_zero_of_eigen`: `C_m f = c f`, `Im c ≠ 0` imply `⟪f, B_m f⟫ = 0` (B2 step 2).
* `eq_zero_of_phaseSpeed_eigen_of_three_le` (B0077, tex lines 1347--1349): no nonreal phase speed
  for `m ≥ 3`, from `‖N_m‖ ≤ 8/m² < 1`.
* `phaseSpeed_two_unique` (B0076(i), tex lines 1339--1347): the upper-half-plane phase speed at
  `m = 2` is unique and geometrically simple.
* `phaseSpeed_two_no_jordan` (B0076, "algebraic multiplicity one", tex lines 1344--1346): no
  Jordan vector.
* `bilinear_pairing_ne_zero` (B0096, tex line 1518, via B2(c)): `∫ f · B_2 f dt ≠ 0`.

Lean's inner product `⟪x, y⟫_ℂ` is conjugate-linear in `x`. The sesquilinear form of B2 is
`(x, y) ↦ ⟪x, B_m y⟫_ℂ`; the bilinear pairing `∫ f · B f` is `⟪star f, B f⟫_ℂ`
(`integral_mul_eq_inner_star`).
-/

set_option autoImplicit false

noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace InnerProduct ComplexConjugate
namespace UnforcedLeray.Sturm
open GaussianPotential

/-! ## The coefficients `Ω`, `a_*`, `J` -/

/-- The critical speed `a_* = e^{-2}` (`eq:st18-t00002`, tex line 646). -/
def aStar : ℝ := Real.exp (-2)

theorem phaseSpeed_measurable_omega : Measurable neutralOmega :=
  continuous_neutralOmega.measurable

theorem phaseSpeed_omega_pos (t : ℝ) : 0 < neutralOmega t := Real.exp_pos _

theorem phaseSpeed_norm_omega_le (t : ℝ) : ‖neutralOmega t‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_pos (phaseSpeed_omega_pos t)]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (neutralRadius_pos t).le)

/-- Multiplication by the angular velocity `Ω(e^t) = exp(-e^{2t}/4)` on `L²(ℝ, dt)`
(`eq:st18-t00001`, tex line 639, in the logarithmic radius of tex line 820). -/
def omegaOp : ComplexL2 →L[ℂ] ComplexL2 :=
  ComplexBoundedMultiplier.operator neutralOmega phaseSpeed_measurable_omega 1
    phaseSpeed_norm_omega_le

theorem coeFn_omegaOp (f : ComplexL2) :
    omegaOp f =ᵐ[volume] fun t => (neutralOmega t : ℂ) * f t :=
  ComplexBoundedMultiplier.coeFn_operator neutralOmega phaseSpeed_measurable_omega 1
    phaseSpeed_norm_omega_le f

theorem omegaOp_isSelfAdjoint : IsSelfAdjoint omegaOp :=
  ComplexBoundedMultiplier.operator_isSelfAdjoint neutralOmega phaseSpeed_measurable_omega 1
    phaseSpeed_norm_omega_le

/-- Multiplication by `J = Ω - a_*` (tex lines 1296--1301). -/
def JOp : ComplexL2 →L[ℂ] ComplexL2 :=
  omegaOp - (aStar : ℂ) • ContinuousLinearMap.id ℂ ComplexL2

theorem omegaOp_sub_JOp : omegaOp - JOp = (aStar : ℂ) • ContinuousLinearMap.id ℂ ComplexL2 := by
  rw [JOp]; abel

theorem coeFn_JOp (f : ComplexL2) :
    JOp f =ᵐ[volume] fun t => ((neutralOmega t - aStar : ℝ) : ℂ) * f t := by
  change (omegaOp f - (aStar : ℂ) • f : ComplexL2) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_sub (omegaOp f) ((aStar : ℂ) • f), coeFn_omegaOp f,
    Lp.coeFn_smul (aStar : ℂ) f] with t h1 h2 h3
  rw [h1, Pi.sub_apply, h2, h3, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem isSelfAdjoint_ofReal_smul_id (a : ℝ) :
    IsSelfAdjoint ((a : ℂ) • ContinuousLinearMap.id ℂ ComplexL2) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  simp only [ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.coe_id, LinearMap.smul_apply,
    LinearMap.id_apply, inner_smul_left, inner_smul_right, Complex.conj_ofReal]

theorem JOp_isSelfAdjoint : IsSelfAdjoint JOp :=
  omegaOp_isSelfAdjoint.sub (isSelfAdjoint_ofReal_smul_id aStar)

/-! ## The phase-speed operator -/

/-- **S4.** The bounded phase-speed operator `C_m = Ω - J N_m` (`eq:st18-t00057`, tex lines
1296--1301: `T̃_n = Ω - J 𝓚_n`). A sector-`m` Rayleigh mode with speed `c` gives `C_m f = c f` for
`f = W^{1/2} J F / (Ω - c)` (scoping note §4, B2). -/
def phaseSpeedOp {m : ℝ} (hm : 0 < m) : ComplexL2 →L[ℂ] ComplexL2 :=
  omegaOp - JOp ∘L birmanSchwingerOperator hm

/-- `C_m = a_* I + J B_m` (`eq:st18-t00057`, tex lines 1296--1301). -/
theorem phaseSpeedOp_eq {m : ℝ} (hm : 0 < m) :
    phaseSpeedOp hm = (aStar : ℂ) • ContinuousLinearMap.id ℂ ComplexL2 +
      JOp ∘L (1 - birmanSchwingerOperator hm) := by
  ext1 f
  change omegaOp f - JOp (birmanSchwingerOperator hm f) =
    (aStar : ℂ) • f + JOp (f - birmanSchwingerOperator hm f)
  rw [map_sub]
  change omegaOp f - JOp (birmanSchwingerOperator hm f) =
    (aStar : ℂ) • f + (omegaOp f - (aStar : ℂ) • f - JOp (birmanSchwingerOperator hm f))
  abel

/-- The ring identity behind `eq:st18-t00058`: with `J = Ω - a`,
`(Ω - N J)(1 - N) = (1 - N)(Ω - J N)`. -/
theorem comm_identity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (Ω N : E →L[ℂ] E) (a : ℂ) :
    (Ω - N * (Ω - a • 1)) * (1 - N) = (1 - N) * (Ω - (Ω - a • 1) * N) := by
  simp only [sub_mul, mul_sub, mul_one, one_mul, smul_mul_assoc, mul_smul_comm, mul_assoc,
    smul_sub]
  abel

/-- **S4**, `eq:st18-t00058` (tex lines 1302--1306): `C_m^† B_m = B_m C_m`. -/
theorem adjoint_phaseSpeedOp_comp {m : ℝ} (hm : 0 < m) :
    (phaseSpeedOp hm)† ∘L (1 - birmanSchwingerOperator hm) =
      (1 - birmanSchwingerOperator hm) ∘L phaseSpeedOp hm := by
  have hΩ : omegaOp† = omegaOp := ContinuousLinearMap.isSelfAdjoint_iff'.mp omegaOp_isSelfAdjoint
  have hJ : JOp† = JOp := ContinuousLinearMap.isSelfAdjoint_iff'.mp JOp_isSelfAdjoint
  have hN : (birmanSchwingerOperator hm)† = birmanSchwingerOperator hm :=
    ContinuousLinearMap.isSelfAdjoint_iff'.mp (birmanSchwingerOperator_isSelfAdjoint hm)
  have hadj : (phaseSpeedOp hm)† = omegaOp - birmanSchwingerOperator hm ∘L JOp := by
    rw [phaseSpeedOp, map_sub, ContinuousLinearMap.adjoint_comp, hΩ, hJ, hN]
  rw [hadj]
  have hJ' : JOp = omegaOp - (aStar : ℂ) • (1 : ComplexL2 →L[ℂ] ComplexL2) := rfl
  rw [phaseSpeedOp, hJ']
  exact comm_identity omegaOp (birmanSchwingerOperator hm) (aStar : ℂ)

/-! ## Neutrality -/

section Neutral
variable {m : ℝ} (hm : 0 < m)

/-- The energy operator `B_m = I - N_m` is symmetric. -/
theorem inner_B_symm (x y : ComplexL2) :
    ⟪(1 - birmanSchwingerOperator hm) x, y⟫_ℂ = ⟪x, (1 - birmanSchwingerOperator hm) y⟫_ℂ := by
  have h := (birmanSchwingerOperator_isSelfAdjoint hm).isSymmetric x y
  change ⟪x - birmanSchwingerOperator hm x, y⟫_ℂ = ⟪x, y - birmanSchwingerOperator hm y⟫_ℂ
  rw [inner_sub_left, inner_sub_right]
  change ⟪x, y⟫_ℂ - ⟪birmanSchwingerOperator hm x, y⟫_ℂ =
    ⟪x, y⟫_ℂ - ⟪x, birmanSchwingerOperator hm y⟫_ℂ
  rw [show ⟪birmanSchwingerOperator hm x, y⟫_ℂ = ⟪x, birmanSchwingerOperator hm y⟫_ℂ from h]

/-- `⟪C x, B y⟫ = ⟪x, B C y⟫`, the pairing form of `eq:st18-t00058`. -/
theorem inner_phaseSpeed_B (x y : ComplexL2) :
    ⟪phaseSpeedOp hm x, (1 - birmanSchwingerOperator hm) y⟫_ℂ =
      ⟪x, (1 - birmanSchwingerOperator hm) (phaseSpeedOp hm y)⟫_ℂ := by
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.comp_apply,
    adjoint_phaseSpeedOp_comp, ContinuousLinearMap.comp_apply]

/-- Eigenvectors with speeds `c, c'` satisfy `(c' - conj c) ⟪f, B f'⟫ = 0` (scoping note §4, B2(b)). -/
theorem inner_B_eigen {c c' : ℂ} {f f' : ComplexL2} (hf : phaseSpeedOp hm f = c • f)
    (hf' : phaseSpeedOp hm f' = c' • f') :
    (c' - conj c) * ⟪f, (1 - birmanSchwingerOperator hm) f'⟫_ℂ = 0 := by
  have h := inner_phaseSpeed_B hm f f'
  rw [hf, hf', map_smul, inner_smul_left, inner_smul_right] at h
  rw [sub_mul, h, sub_self]

/-- **B2 step 2**: `C_m f = c f` with `Im c ≠ 0` implies `⟪f, B_m f⟫ = 0`. -/
theorem inner_B_eq_zero_of_eigen {c : ℂ} (hc : c.im ≠ 0) {f : ComplexL2}
    (hf : phaseSpeedOp hm f = c • f) : ⟪f, (1 - birmanSchwingerOperator hm) f⟫_ℂ = 0 := by
  have h := inner_B_eigen hm hf hf
  have hne : c - conj c ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
    exact hc (by linarith)
  exact (mul_eq_zero.mp h).resolve_left hne

end Neutral

/-- **S4**, B0077 (tex lines 1347--1349): for `m ≥ 3` the phase-speed operator has no nonreal
eigenvalue, since `‖N_m‖ ≤ 8/m² < 1` makes `B_m` coercive. -/
theorem eq_zero_of_phaseSpeed_eigen_of_three_le {m : ℝ} (hm : 3 ≤ m) {c : ℂ} {f : ComplexL2}
    (hc : c.im ≠ 0) (h : phaseSpeedOp (by linarith : (0 : ℝ) < m) f = c • f) : f = 0 := by
  have hm0 : (0 : ℝ) < m := by linarith
  have h0 := inner_B_eq_zero_of_eigen hm0 hc h
  have hre : (⟪f, (1 - birmanSchwingerOperator hm0) f⟫_ℂ).re =
      ‖f‖ ^ 2 - (⟪f, birmanSchwingerOperator hm0 f⟫_ℂ).re := by
    have h1 : (⟪f, f⟫_ℂ).re = ‖f‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) f
    change (⟪f, f - birmanSchwingerOperator hm0 f⟫_ℂ).re = _
    rw [inner_sub_right, Complex.sub_re, h1]
  rw [h0, Complex.zero_re] at hre
  have hN : ‖birmanSchwingerOperator hm0‖ ≤ 8 / 9 := by
    have h1 := norm_birmanSchwingerOperator_le hm0
    have h9 : (9 : ℝ) ≤ m ^ 2 := by nlinarith
    calc ‖birmanSchwingerOperator hm0‖ ≤ 8 * (m ^ 2)⁻¹ := h1
      _ ≤ 8 * (9 : ℝ)⁻¹ := by gcongr
      _ = 8 / 9 := by norm_num
  have hbound : (⟪f, birmanSchwingerOperator hm0 f⟫_ℂ).re ≤ 8 / 9 * ‖f‖ ^ 2 := by
    calc (⟪f, birmanSchwingerOperator hm0 f⟫_ℂ).re ≤ ‖⟪f, birmanSchwingerOperator hm0 f⟫_ℂ‖ :=
          Complex.re_le_norm _
      _ ≤ ‖f‖ * ‖birmanSchwingerOperator hm0 f‖ := norm_inner_le_norm _ _
      _ ≤ ‖f‖ * (‖birmanSchwingerOperator hm0‖ * ‖f‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ ‖f‖ * (8 / 9 * ‖f‖) := by gcongr
      _ = 8 / 9 * ‖f‖ ^ 2 := by ring
  have : ‖f‖ ^ 2 ≤ 0 := by linarith
  exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp (le_antisymm this (sq_nonneg _)))

/-! ## Angular index two -/

theorem im_sub_conj_pos {c c' : ℂ} (hc : 0 < c.im) (hc' : 0 < c'.im) : c' - conj c ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
  linarith

/-- Geometric uniqueness at `m = 2`: two eigenvectors with upper-half-plane speeds are parallel
(scoping note §4, B2(b); B0076, tex lines 1339--1347). -/
theorem phaseSpeed_two_eigenvector_unique {c c' : ℂ} {f f' : ComplexL2}
    (hc : 0 < c.im) (hc' : 0 < c'.im)
    (hf : phaseSpeedOp (m := 2) two_pos f = c • f)
    (hf' : phaseSpeedOp (m := 2) two_pos f' = c' • f') (h0 : f ≠ 0) :
    ∃ μ : ℂ, f' = μ • f := by
  by_contra hne
  push Not at hne
  have hli : LinearIndependent ℂ ![f, f'] :=
    (LinearIndependent.pair_iff' h0).mpr fun a ha => hne a ha.symm
  have hff := inner_B_eq_zero_of_eigen (m := 2) two_pos hc.ne' hf
  have hf'f' := inner_B_eq_zero_of_eigen (m := 2) two_pos hc'.ne' hf'
  have hff' := (mul_eq_zero.mp (inner_B_eigen (m := 2) two_pos hf hf')).resolve_left
    (im_sub_conj_pos hc hc')
  have hf'f := (mul_eq_zero.mp (inner_B_eigen (m := 2) two_pos hf' hf)).resolve_left
    (im_sub_conj_pos hc' hc)
  exact PlanarIndex.not_neutral_pair (m := 2) one_lt_two hli hff hff' hf'f hf'f'

/-- **S4**, B0076(i)--(ii) (tex lines 1339--1347): at `m = 2` the upper-half-plane phase speed
is unique and geometrically simple. The hypothesis `f' ≠ 0` is needed for `c' = c` (otherwise
`f' = 0` is an eigenvector for every `c'`). -/
theorem phaseSpeed_two_unique {c c' : ℂ} {f f' : ComplexL2}
    (hc : 0 < c.im) (hc' : 0 < c'.im)
    (hf : phaseSpeedOp (m := 2) two_pos f = c • f)
    (hf' : phaseSpeedOp (m := 2) two_pos f' = c' • f') (h0 : f ≠ 0) (h0' : f' ≠ 0) :
    c' = c ∧ ∃ μ : ℂ, f' = μ • f := by
  obtain ⟨μ, hμ⟩ := phaseSpeed_two_eigenvector_unique hc hc' hf hf' h0
  refine ⟨?_, μ, hμ⟩
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    exact h0' (by rw [hμ, zero_smul])
  have h1 : phaseSpeedOp (m := 2) two_pos f' = (μ * c) • f := by
    rw [hμ, map_smul, hf, smul_smul]
  rw [hf', hμ, smul_smul] at h1
  have h2 : (c' * μ - μ * c) • f = 0 := by rw [sub_smul, h1, sub_self]
  have h3 := (smul_eq_zero.mp h2).resolve_right h0
  have h4 : μ * (c' - c) = 0 := by linear_combination h3
  exact sub_eq_zero.mp ((mul_eq_zero.mp h4).resolve_left hμ0)

/-- **S4**, B0076 (algebraic multiplicity one, tex lines 1344--1346; scoping note §4, B2(b)):
the upper-half-plane eigenvector at `m = 2` has no Jordan vector. -/
theorem phaseSpeed_two_no_jordan {c : ℂ} {f f₁ : ComplexL2} (hc : 0 < c.im) (h0 : f ≠ 0)
    (hf : phaseSpeedOp (m := 2) two_pos f = c • f) :
    phaseSpeedOp (m := 2) two_pos f₁ - c • f₁ ≠ f := by
  intro hJ
  have hf₁ : phaseSpeedOp (m := 2) two_pos f₁ = c • f₁ + f := by rw [← hJ]; abel
  set B := (1 - birmanSchwingerOperator (m := 2) two_pos) with hB
  have hne : c - conj c ≠ 0 := im_sub_conj_pos hc hc
  have hff : ⟪f, B f⟫_ℂ = 0 := inner_B_eq_zero_of_eigen (m := 2) two_pos hc.ne' hf
  -- `⟪f₁, B f⟫ = 0`
  have hf₁f : ⟪f₁, B f⟫_ℂ = 0 := by
    have h := inner_phaseSpeed_B (m := 2) two_pos f₁ f
    rw [hf₁, hf, map_smul, inner_add_left, inner_smul_left, inner_smul_right, hff,
      add_zero] at h
    have h' : (c - conj c) * ⟪f₁, B f⟫_ℂ = 0 := by rw [sub_mul, h, sub_self]
    exact (mul_eq_zero.mp h').resolve_left hne
  -- `⟪f, B f₁⟫ = 0`
  have hff₁ : ⟪f, B f₁⟫_ℂ = 0 := by
    have h := inner_phaseSpeed_B (m := 2) two_pos f f₁
    rw [hf, hf₁, map_add, map_smul, inner_add_right, inner_smul_left, inner_smul_right, hff,
      add_zero] at h
    have h' : (c - conj c) * ⟪f, B f₁⟫_ℂ = 0 := by rw [sub_mul, h, sub_self]
    exact (mul_eq_zero.mp h').resolve_left hne
  -- `⟪f₁, B f₁⟫ = 0`
  have hf₁f₁ : ⟪f₁, B f₁⟫_ℂ = 0 := by
    have h := inner_phaseSpeed_B (m := 2) two_pos f₁ f₁
    rw [hf₁, map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right, hff₁, hf₁f, add_zero, add_zero] at h
    have h' : (c - conj c) * ⟪f₁, B f₁⟫_ℂ = 0 := by rw [sub_mul, h, sub_self]
    exact (mul_eq_zero.mp h').resolve_left hne
  have hli : LinearIndependent ℂ ![f, f₁] := by
    refine (LinearIndependent.pair_iff' h0).mpr fun a ha => ?_
    apply h0
    rw [← hJ, ← ha, map_smul, hf, smul_smul, smul_smul, mul_comm, sub_self]
  exact PlanarIndex.not_neutral_pair (m := 2) one_lt_two hli hff hff₁ hf₁f hf₁f₁

/-! ## Complex conjugation commutes with the real operators -/

theorem coeFn_star_L2 (f : ComplexL2) : (star f : ComplexL2) =ᵐ[volume] fun t => conj (f t) :=
  Lp.coeFn_star f

theorem star_sub_L2 (u w : ComplexL2) : (star (u - w) : ComplexL2) = star u - star w := by
  apply Lp.ext
  filter_upwards [coeFn_star_L2 (u - w), Lp.coeFn_sub u w, Lp.coeFn_sub (star u) (star w),
    coeFn_star_L2 u, coeFn_star_L2 w] with t h1 h2 h3 h4 h5
  rw [h1, h3, h2, Pi.sub_apply, Pi.sub_apply, h4, h5, map_sub]

theorem star_smul_L2 (a : ℂ) (u : ComplexL2) : (star (a • u) : ComplexL2) = conj a • star u := by
  apply Lp.ext
  filter_upwards [coeFn_star_L2 (a • u), Lp.coeFn_smul a u, Lp.coeFn_smul (conj a) (star u),
    coeFn_star_L2 u] with t h1 h2 h3 h4
  rw [h1, h3, h2, Pi.smul_apply, Pi.smul_apply, h4, smul_eq_mul, smul_eq_mul, map_mul]

theorem star_zero_L2 : (star (0 : ComplexL2) : ComplexL2) = 0 := by
  apply Lp.ext
  filter_upwards [coeFn_star_L2 0, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with t h1 h2
  rw [h1, h2, Pi.zero_apply, map_zero]

/-- A real bounded multiplier commutes with conjugation. -/
theorem multiplier_star (w : ℝ → ℝ) (hw : Measurable w) (C : ℝ) (hbound : ∀ x, ‖w x‖ ≤ C)
    (f : ComplexL2) :
    ComplexBoundedMultiplier.operator w hw C hbound (star f) =
      star (ComplexBoundedMultiplier.operator w hw C hbound f) := by
  apply Lp.ext
  filter_upwards [ComplexBoundedMultiplier.coeFn_operator w hw C hbound (star f),
    ComplexBoundedMultiplier.coeFn_operator w hw C hbound f, coeFn_star_L2 f,
    coeFn_star_L2 (ComplexBoundedMultiplier.operator w hw C hbound f)] with t h1 h2 h3 h4
  rw [h1, h4, h3, h2, map_mul, Complex.conj_ofReal]

theorem omegaOp_star (f : ComplexL2) : omegaOp (star f) = star (omegaOp f) :=
  multiplier_star _ _ _ _ f

theorem JOp_star (f : ComplexL2) : JOp (star f) = star (JOp f) := by
  change omegaOp (star f) - (aStar : ℂ) • star f = star (omegaOp f - (aStar : ℂ) • f)
  rw [star_sub_L2, star_smul_L2, Complex.conj_ofReal, omegaOp_star]

theorem freeResolventOperator_star {L : ℝ} (hL : 0 < L) (f : ComplexL2) :
    freeResolventOperator hL (star f) = star (freeResolventOperator hL f) := by
  apply Lp.ext
  have hc : freeResolvent L ((star f : ComplexL2) : ℝ → ℂ) =
      fun x => conj (freeResolvent L (f : ℝ → ℂ) x) := by
    rw [freeResolvent_congr_ae L (coeFn_star_L2 f), freeResolvent_conj]
  filter_upwards [coeFn_freeResolventOperator hL (star f), coeFn_freeResolventOperator hL f,
    coeFn_star_L2 (freeResolventOperator hL f)] with t h1 h2 h3
  rw [h1, hc, h3, h2]

theorem birmanSchwingerOperator_star {m : ℝ} (hm : 0 < m) (f : ComplexL2) :
    birmanSchwingerOperator hm (star f) = star (birmanSchwingerOperator hm f) := by
  rw [birmanSchwingerOperator_apply, birmanSchwingerOperator_apply]
  have hS (u : ComplexL2) : complexPotentialSqrtOperator (star u) =
      star (complexPotentialSqrtOperator u) := multiplier_star _ _ _ _ u
  rw [hS, freeResolventOperator_star, hS]

theorem phaseSpeedOp_star {m : ℝ} (hm : 0 < m) (f : ComplexL2) :
    phaseSpeedOp hm (star f) = star (phaseSpeedOp hm f) := by
  change omegaOp (star f) - JOp (birmanSchwingerOperator hm (star f)) =
    star (omegaOp f - JOp (birmanSchwingerOperator hm f))
  rw [birmanSchwingerOperator_star, JOp_star, omegaOp_star, star_sub_L2]

/-- The bilinear pairing `∫ f g` is `⟪star f, g⟫_ℂ`. -/
theorem integral_mul_eq_inner_star (f g : ComplexL2) :
    (∫ t, f t * g t) = ⟪(star f : ComplexL2), g⟫_ℂ := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_star_L2 f] with t ht
  rw [RCLike.inner_apply, ht, RingHomCompTriple.comp_apply, RingHom.id_apply]
  ring

/-- **S4**, B0096 (tex line 1518) via bypass B2(c): for the upper-half-plane eigenvector at
`m = 2`, the bilinear pairing `∫ f · B_2 f dt` is nonzero. (The integrand is a product of two
`L²` functions, hence integrable, so no junk value enters.) -/
theorem bilinear_pairing_ne_zero {c : ℂ} {f : ComplexL2} (hc : 0 < c.im) (h0 : f ≠ 0)
    (hf : phaseSpeedOp (m := 2) two_pos f = c • f) :
    ∫ t, f t * ((1 - birmanSchwingerOperator (m := 2) two_pos) f) t ≠ 0 := by
  intro hint
  rw [integral_mul_eq_inner_star] at hint
  set B := (1 - birmanSchwingerOperator (m := 2) two_pos) with hB
  set g : ComplexL2 := star f with hg
  have hstar : phaseSpeedOp (m := 2) two_pos g = conj c • g := by
    rw [hg, phaseSpeedOp_star, hf, star_smul_L2]
  have hgim : (conj c).im ≠ 0 := by
    rw [Complex.conj_im]; exact neg_ne_zero.mpr hc.ne'
  have hff : ⟪f, B f⟫_ℂ = 0 := inner_B_eq_zero_of_eigen (m := 2) two_pos hc.ne' hf
  have hgg : ⟪g, B g⟫_ℂ = 0 := inner_B_eq_zero_of_eigen (m := 2) two_pos hgim hstar
  have hfg : ⟪f, B g⟫_ℂ = 0 := by
    rw [← inner_B_symm (m := 2) two_pos, ← inner_conj_symm, hint, map_zero]
  have hli : LinearIndependent ℂ ![f, g] := by
    refine (LinearIndependent.pair_iff' h0).mpr fun a ha => ?_
    -- `g = a f` forces `a = 0`, hence `f = star (star f) = star 0 = 0`
    have h1 : phaseSpeedOp (m := 2) two_pos g = (a * c) • f := by
      rw [← ha, map_smul, hf, smul_smul]
    rw [hstar, ← ha, smul_smul] at h1
    have h2 : (conj c * a - a * c) • f = 0 := by rw [sub_smul, h1, sub_self]
    have h3 := (smul_eq_zero.mp h2).resolve_right h0
    have h4 : a * (conj c - c) = 0 := by linear_combination h3
    have hne : conj c - c ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
      linarith
    have ha0 : a = 0 := (mul_eq_zero.mp h4).resolve_right hne
    apply h0
    have hg0 : g = 0 := by rw [← ha, ha0, zero_smul]
    rw [← star_star f, ← hg, hg0, star_zero_L2]
  exact PlanarIndex.not_neutral_pair (m := 2) one_lt_two hli hff hfg hint hgg

end UnforcedLeray.Sturm
