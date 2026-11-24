import UnforcedLeray.Units.B0012
import UnforcedLeray.Units.B0086

/-!
# B0090: the bounded `X_G`-adjoint of `L₀` (`eq:st18-t00064`)

Blueprint unit B0090, label `eq:st18-t00064`, `paper/main.tex` lines 1454--1461 (inside the
proof "Identification and regularity of the adjoint", section `sec:st18-1623`). Dependencies:
B0012 = `eq:st18-t00006` (the bounded generator `L₀` on `X_G`), B0011 = `eq:st18-t00007` (the
Green inverse `R`), B0086 = `eq:st18-t00062` (the pointwise Green bound, also for `R((x-2)f)`).

The manuscript says (lines 1456--1461): "Put `V = x - 2`. Since `R` is selfadjoint in unweighted
radial area and `Ω/G = 4π`, the bounded adjoint is `L₀^* h = 2iΩ [h - R(Vh)]`. All integrals are
justified by `eq:st18-t00062` and Gaussian moment bounds."

**Formalization.**
* `V r = x - 2`, `x = r²/4` (B0086 `xVar`). The two algebraic facts used: `k = VΩ`
  (`radialK_eq_V_mul_omega`, with `k` of tex line 647) and `Ω/G = 4π` (`omega_div_gauss`).
* "`R` is selfadjoint in unweighted radial area" (real symmetric kernel, Fubini):
  `integral_R_mul_symm` gives, for profiles `f, g` with `r f, r g ∈ L¹(0,∞)` (B0011 `WProf`),
  that both integrands of `∫₀^∞ (Rf) g r dr = ∫₀^∞ f (Rg) r dr` are integrable and the integrals
  agree; `integral_R_mul_conj_symm` is the sesquilinear form `∫ (Rf) conj g r = ∫ f conj(Rg) r`.
  Since the integrands are proved integrable, no Bochner junk value enters.
* `L0AdjFun h r = 2iΩ(r) [h(r) - R(Vh)(r)]` is the manuscript formula on a profile `h`.
* **`eq:st18-t00064`**: `coeFn_adjoint_L0` says that the Hilbert-space adjoint
  `ContinuousLinearMap.adjoint B0012.L0` (a bounded operator on `X_G`) is given a.e. by
  `L0AdjFun`; `adjoint_L0_toLp` is the same statement on profiles, and
  `integral_L0Fun_mul_conj` is the integral identity
  `∫₀^∞ (L₀f) conj(h) G⁻¹ r dr = ∫₀^∞ f conj(L₀^*h) G⁻¹ r dr` for profiles `f, h ∈ X_G`,
  together with the integrability of both integrands (`integrableOn_mul_conj`).
  `adjoint_L0_apply` is the operator form `L₀^* = 2i(Ω - ΩR V)`.
* "All integrals are justified by `eq:st18-t00062`": `R(Vh)` is bounded on `(0,∞)` by
  B0086 `green_bound_const` (`norm_RV_le`), so `Ω R(Vh) ∈ X_G` (`memLp_omegaRV`), and `Vh`
  satisfies `WProf` (B0086 `wprof_xm2`, a Gaussian moment bound), so Fubini applies.

**Proof (blueprint outline).** `⟨2ikRf, h⟩_{X_G} = 2i ∫ (Rf)(k/G) conj(h) r dr
= 8πi ∫ (Rf) V conj(h) r dr = 8πi ∫ f conj(R(Vh)) r dr = ⟨f, -2iΩR(Vh)⟩_{X_G}`, and
multiplication by `-2iΩ` has adjoint `2iΩ`. The Fubini argument for the symmetric kernel is
adapted from the reference formalization
`NonUniqueEuler/lean/NonUniqueEuler/H/Sec4/Adjoint/Green.lean` (`integral_green_mul_symm`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate

namespace UnforcedLeray.B0090

open B0010 B0011 B0012 GaussianVortex

/-! ## The potential `V = x - 2` and the identities `k = VΩ`, `Ω/G = 4π` -/

/-- The potential `V = x - 2`, `x = r²/4` (tex line 1456; B0086 `xVar`). -/
def V (r : ℝ) : ℝ := B0086.xVar r - 2

/-- `k = VΩ` (tex line 647: `k = (x-2)e^{-x}`; used at tex line 1456). -/
theorem radialK_eq_V_mul_omega (r : ℝ) : radialK r = V r * radialOmega r := rfl

/-- `Ω/G = 4π` (tex line 1456), with `G = (4π)⁻¹ Ω` the Gaussian of tex line 650. -/
theorem omega_div_gauss (r : ℝ) : radialOmega r / radialGaussianWeight r = 4 * Real.pi := by
  have hΩ := (radialOmega_pos r).ne'
  unfold radialGaussianWeight
  field_simp

theorem gauss_inv_mul_omega (r : ℝ) :
    (radialGaussianWeight r)⁻¹ * radialOmega r = 4 * Real.pi := by
  rw [← div_eq_inv_mul, omega_div_gauss]

/-! ## `R` is selfadjoint in unweighted radial area `r dr` -/

theorem integrable_mul_coe {g : ℝ → ℂ} (hg : WProf g) :
    Integrable (fun ρ => g ρ * (ρ : ℂ)) (volume.restrict (Ioi 0)) := by
  refine Integrable.mono' hg.int
    (hg.meas.mul Complex.continuous_ofReal.aestronglyMeasurable) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun ρ hρ => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (le_of_lt hρ), mul_comm]

/-- `WProf` is stable under complex conjugation. -/
theorem wprof_conj {g : ℝ → ℂ} (hg : WProf g) : WProf (fun s => conj (g s)) :=
  ⟨Complex.continuous_conj.comp_aestronglyMeasurable hg.meas,
    hg.int.congr (ae_of_all _ fun ρ => by simp only [Complex.norm_conj])⟩

/-- The Green kernel is real: `R(conj g) = conj(Rg)` at `r > 0`. -/
theorem R_conj {g : ℝ → ℂ} (hg : WProf g) {r : ℝ} (hr : 0 < r) :
    R (fun s => conj (g s)) r = conj (R g r) := by
  rw [R_eq_Psi (wprof_conj hg) hr, R_eq_Psi hg hr, Psi, Psi, map_mul, ← integral_conj]
  congr 1
  · have h4 : conj (4 : ℂ) = 4 := map_ofNat _ 4
    rw [map_neg, map_div₀, map_one, h4]
  · refine integral_congr_ae (ae_of_all _ fun s => ?_)
    simp only [map_mul, Complex.conj_ofReal]

/-- **`R` is selfadjoint in unweighted radial area** (tex line 1456; real symmetric kernel
`-¼ (min(r,s)/max(r,s))²`, Fubini): for profiles `f, g` with `r f, r g ∈ L¹(0, ∞)` (B0011
`WProf`), both integrands are integrable on `(0, ∞)` and
`∫₀^∞ (Rf)(r) g(r) r dr = ∫₀^∞ f(r) (Rg)(r) r dr`.
Adapted from `NonUniqueEuler/lean/NonUniqueEuler/H/Sec4/Adjoint/Green.lean`
(`integral_green_mul_symm`). -/
theorem integral_R_mul_symm {f g : ℝ → ℂ} (hf : WProf f) (hg : WProf g) :
    IntegrableOn (fun r => R f r * g r * (r : ℂ)) (Ioi 0) ∧
      IntegrableOn (fun r => f r * R g r * (r : ℂ)) (Ioi 0) ∧
      ∫ r in Ioi (0 : ℝ), R f r * g r * (r : ℂ) = ∫ r in Ioi (0 : ℝ), f r * R g r * (r : ℂ) := by
  set μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hμ
  let K : ℝ → ℝ → ℂ := fun r ρ => (((min r ρ / max r ρ) ^ 2 : ℝ) : ℂ)
  let F : ℝ → ℝ → ℂ := fun r ρ => K r ρ * ((g r * r) * (f ρ * ρ))
  have hKs : ∀ r ρ, K ρ r = K r ρ := fun r ρ => by simp only [K, min_comm, max_comm]
  have hKm : Measurable (Function.uncurry K) := by
    apply Complex.measurable_ofReal.comp
    exact ((measurable_fst.min measurable_snd).div (measurable_fst.max measurable_snd)).pow_const _
  have hKb : ∀ᵐ p ∂(μ.prod μ), ‖Function.uncurry K p‖ ≤ 1 := by
    rw [hμ, Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
    obtain ⟨h1, h2⟩ := hp
    simp only [mem_Ioi] at h1 h2
    simp only [Function.uncurry, K, Complex.norm_real, Real.norm_eq_abs]
    have hmax : 0 < max p.1 p.2 := lt_max_of_lt_left h1
    have hmin : 0 < min p.1 p.2 := lt_min h1 h2
    rw [abs_of_nonneg (by positivity)]
    apply pow_le_one₀ (by positivity)
    rw [div_le_one hmax]
    exact min_le_max
  have hint : Integrable (Function.uncurry F) (μ.prod μ) :=
    ((integrable_mul_coe hg).mul_prod (integrable_mul_coe hf)).bdd_mul
      hKm.aestronglyMeasurable hKb
  have hL : ∀ r ∈ Ioi (0 : ℝ),
      R f r * g r * (r : ℂ) = -(1 / 4 : ℂ) * ∫ ρ in Ioi 0, F r ρ := by
    intro r hr
    have e : ∫ ρ in Ioi 0, F r ρ = Psi 2 f r * (g r * r) := by
      rw [Psi, ← integral_mul_const]
      refine integral_congr_ae (ae_of_all _ fun ρ => ?_)
      simp only [F, K, B0011.ker]
      push_cast
      ring
    rw [e, R_eq_Psi hf hr]
    ring
  have hR : ∀ ρ ∈ Ioi (0 : ℝ),
      f ρ * R g ρ * (ρ : ℂ) = -(1 / 4 : ℂ) * ∫ r in Ioi 0, F r ρ := by
    intro ρ hρ
    have e : ∫ r in Ioi 0, F r ρ = Psi 2 g ρ * (f ρ * ρ) := by
      rw [Psi, ← integral_mul_const]
      refine integral_congr_ae (ae_of_all _ fun r => ?_)
      simp only [F]
      rw [← hKs r ρ]
      simp only [K, B0011.ker]
      push_cast
      ring
    rw [e, R_eq_Psi hg hρ]
    ring
  have hI1 : Integrable (fun r => ∫ ρ in Ioi 0, F r ρ) μ := hint.integral_prod_left
  have hI2 : Integrable (fun ρ => ∫ r in Ioi 0, F r ρ) μ := hint.integral_prod_right
  refine ⟨?_, ?_, ?_⟩
  · exact IntegrableOn.congr_fun (hI1.const_mul (-(1 / 4 : ℂ)))
      (fun r hr => (hL r hr).symm) measurableSet_Ioi
  · exact IntegrableOn.congr_fun (hI2.const_mul (-(1 / 4 : ℂ)))
      (fun ρ hρ => (hR ρ hρ).symm) measurableSet_Ioi
  · rw [setIntegral_congr_fun measurableSet_Ioi hL, setIntegral_congr_fun measurableSet_Ioi hR,
      integral_const_mul, integral_const_mul, integral_integral_swap hint]

/-- **`R` is selfadjoint in unweighted radial area**, sesquilinear form (tex line 1456): for
`r f, r g ∈ L¹(0, ∞)`, `∫₀^∞ (Rf) conj(g) r dr = ∫₀^∞ f conj(Rg) r dr`, both integrands being
integrable on `(0, ∞)`. -/
theorem integral_R_mul_conj_symm {f g : ℝ → ℂ} (hf : WProf f) (hg : WProf g) :
    IntegrableOn (fun r => R f r * conj (g r) * (r : ℂ)) (Ioi 0) ∧
      IntegrableOn (fun r => f r * conj (R g r) * (r : ℂ)) (Ioi 0) ∧
      ∫ r in Ioi (0 : ℝ), R f r * conj (g r) * (r : ℂ) =
        ∫ r in Ioi (0 : ℝ), f r * conj (R g r) * (r : ℂ) := by
  obtain ⟨h1, h2, h3⟩ := integral_R_mul_symm hf (wprof_conj hg)
  have e : EqOn (fun r => f r * R (fun s => conj (g s)) r * (r : ℂ))
      (fun r => f r * conj (R g r) * (r : ℂ)) (Ioi 0) := fun r hr => by
    simp only
    rw [R_conj hg hr]
  refine ⟨h1, h2.congr_fun e measurableSet_Ioi, ?_⟩
  rw [h3, setIntegral_congr_fun measurableSet_Ioi e]

/-! ## The term `ΩR(Vh)` -/

/-- `Vh` satisfies B0011's `WProf` for `h ∈ X_G` (B0086 `wprof_xm2`: Gaussian moments). -/
theorem wprof_V {h : ℝ → ℂ} (hh : MemXG h) : WProf (fun s => (V s : ℂ) * h s) :=
  B0086.wprof_xm2 hh

theorem min_le_one' {r : ℝ} (hr : 0 < r) : min r (r ^ 2)⁻¹ ≤ 1 := by
  rcases le_or_gt r 1 with h | h
  · exact (min_le_left _ _).trans h
  · refine (min_le_right _ _).trans ?_
    apply inv_le_one_of_one_le₀
    nlinarith

/-- `|R(Vh)(r)| ≤ C ‖h‖_{X_G}` on `(0, ∞)`, from `eq:st18-t00062` (B0086, tex line 1422). -/
theorem norm_RV_le (h : XG) {r : ℝ} (hr : 0 < r) :
    ‖R (fun s => (V s : ℂ) * h s) r‖ ≤ B0086.greenConst * ‖h‖ := by
  have h1 := (B0086.green_bound_const (B0086.memXG_coe h) hr).2
  rw [B0086.xGNorm_eq_norm] at h1
  have hC : 0 ≤ B0086.greenConst * ‖h‖ := mul_nonneg B0086.greenConst_nonneg (norm_nonneg _)
  calc ‖R (fun s => (V s : ℂ) * h s) r‖ ≤ B0086.greenConst * ‖h‖ * min r (r ^ 2)⁻¹ := h1
    _ ≤ B0086.greenConst * ‖h‖ * 1 := mul_le_mul_of_nonneg_left (min_le_one' hr) hC
    _ = B0086.greenConst * ‖h‖ := mul_one _

theorem continuousOn_RV (h : XG) : ContinuousOn (R fun s => (V s : ℂ) * h s) (Ioi 0) := by
  obtain ⟨ψ', hd, -, -⟩ := (wprof_V (B0012.memXG_coe h)).isDelta2Sol_R
  exact fun r hr => (hd r hr).continuousAt.continuousWithinAt

/-- `ΩR(Vh) ∈ X_G` for `h ∈ X_G`. -/
theorem memLp_omegaRV (h : XG) :
    MemLp (fun r => (radialOmega r : ℂ) * R (fun s => (V s : ℂ) * h s) r) 2 xGMeasure := by
  have hm : AEStronglyMeasurable
      (fun r => (radialOmega r : ℂ) * R (fun s => (V s : ℂ) * h s) r) xGMeasure :=
    (Complex.continuous_ofReal.comp continuous_radialOmega).aestronglyMeasurable.mul
      (((continuousOn_RV h).aestronglyMeasurable measurableSet_Ioi).mono_ac xG_ac)
  have hC : 0 ≤ 4 * Real.pi * B0086.greenConst * ‖h‖ :=
    mul_nonneg (mul_nonneg (by positivity) B0086.greenConst_nonneg) (norm_nonneg _)
  refine (memLp_gauss.const_smul (((4 * Real.pi * B0086.greenConst * ‖h‖ : ℝ)) : ℂ)).of_le hm ?_
  filter_upwards [ae_xG_pos] with r hr
  rw [Pi.smul_apply, smul_eq_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Complex.norm_real, Real.norm_of_nonneg (radialOmega_pos r).le, Real.norm_of_nonneg hC,
    Real.norm_of_nonneg (radialGaussianWeight_pos r).le]
  have hΩ : radialOmega r = 4 * Real.pi * radialGaussianWeight r := by
    have := gauss_inv_mul_omega r
    have hG := (radialGaussianWeight_pos r).ne'
    field_simp at this
    linarith
  have hb := norm_RV_le h hr
  have hG := radialGaussianWeight_pos r
  rw [hΩ]
  calc 4 * Real.pi * radialGaussianWeight r * ‖R (fun s => (V s : ℂ) * h s) r‖
      ≤ 4 * Real.pi * radialGaussianWeight r * (B0086.greenConst * ‖h‖) := by gcongr
    _ = 4 * Real.pi * B0086.greenConst * ‖h‖ * radialGaussianWeight r := by ring

/-- `ΩR(Vh)` as an element of `X_G`. -/
def omegaRV (h : XG) : XG := (memLp_omegaRV h).toLp _

theorem coeFn_omegaRV (h : XG) :
    ⇑(omegaRV h) =ᵐ[xGMeasure] fun r => (radialOmega r : ℂ) * R (fun s => (V s : ℂ) * h s) r :=
  (memLp_omegaRV h).coeFn_toLp

/-! ## The two adjoint identities -/

/-- Multiplication by the real function `Ω` is symmetric on `X_G`. -/
theorem inner_omegaOp_symm (f h : XG) : inner ℂ h (omegaOp f) = inner ℂ (omegaOp h) f := by
  rw [← pairing_eq_inner, ← pairing_eq_inner]
  unfold pairing
  apply integral_congr_ae
  filter_upwards [coeFn_omegaOp f, coeFn_omegaOp h] with r h1 h2
  rw [h1, h2, map_mul, Complex.conj_ofReal]
  ring

/-- `⟨kRf, h⟩_{X_G} = ⟨f, ΩR(Vh)⟩_{X_G}` (tex line 1456: `R` selfadjoint in `r dr`, `k = VΩ`,
`Ω/G = 4π`). -/
theorem inner_kROp (f h : XG) : inner ℂ h (kROp f) = inner ℂ (omegaRV h) f := by
  rw [← pairing_eq_inner, ← pairing_eq_inner]
  set u : ℝ → ℂ := fun s => conj ((V s : ℂ) * h s) with hu
  have hwV : WProf (fun s => (V s : ℂ) * h s) := wprof_V (B0012.memXG_coe h)
  have hwf : WProf ⇑f := B0012.wprof_coe f
  have e1 : pairing (kROp f) h =
      (4 * Real.pi : ℂ) * ∫ r in Ioi 0, R (⇑f) r * conj ((V r : ℂ) * h r) * (r : ℂ) := by
    have h1 : pairing (kROp f) h =
        ∫ r, (radialK r : ℂ) * R (⇑f) r * conj (h r) ∂xGMeasure := by
      unfold pairing
      apply integral_congr_ae
      filter_upwards [coeFn_kROp f] with r h1
      rw [h1]
    have h2 : ∫ r, (radialK r : ℂ) * R (⇑f) r * conj (h r) ∂xGMeasure =
        ∫ r in Ioi 0, xGDensity r • ((radialK r : ℂ) * R (⇑f) r * conj (h r)) :=
      integral_withDensity_eq_integral_smul measurable_xGDensity _
    rw [h1, h2, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
    have hr' : (0 : ℝ) < r := hr
    have key : ((radialGaussianWeight r)⁻¹ * r) * radialK r = 4 * Real.pi * (V r * r) := by
      rw [radialK_eq_V_mul_omega]
      linear_combination (V r * r) * gauss_inv_mul_omega r
    have keyC := congrArg (fun x : ℝ => (x : ℂ)) key
    simp only [NNReal.smul_def, coe_xGDensity hr', Complex.real_smul, map_mul,
      Complex.conj_ofReal]
    push_cast at keyC ⊢
    linear_combination (R (⇑f) r * conj (h r)) * keyC
  have e2 : pairing f (omegaRV h) =
      (4 * Real.pi : ℂ) * ∫ r in Ioi 0, f r * conj (R (fun s => (V s : ℂ) * h s) r) * (r : ℂ) := by
    have h1 : pairing f (omegaRV h) =
        ∫ r, f r * conj ((radialOmega r : ℂ) * R (fun s => (V s : ℂ) * h s) r) ∂xGMeasure := by
      unfold pairing
      apply integral_congr_ae
      filter_upwards [coeFn_omegaRV h] with r h1
      rw [h1]
    have h2 : ∫ r, f r * conj ((radialOmega r : ℂ) * R (fun s => (V s : ℂ) * h s) r)
        ∂xGMeasure = ∫ r in Ioi 0, xGDensity r •
          (f r * conj ((radialOmega r : ℂ) * R (fun s => (V s : ℂ) * h s) r)) :=
      integral_withDensity_eq_integral_smul measurable_xGDensity _
    rw [h1, h2, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
    have hr' : (0 : ℝ) < r := hr
    have key : ((radialGaussianWeight r)⁻¹ * r) * radialOmega r = 4 * Real.pi * r := by
      linear_combination r * gauss_inv_mul_omega r
    have keyC := congrArg (fun x : ℝ => (x : ℂ)) key
    simp only [NNReal.smul_def, coe_xGDensity hr', Complex.real_smul, map_mul,
      Complex.conj_ofReal]
    push_cast at keyC ⊢
    linear_combination (f r * conj (R (fun s => (V s : ℂ) * h s) r)) * keyC
  rw [e1, e2, (integral_R_mul_conj_symm hwf hwV).2.2]

/-! ## `eq:st18-t00064`: the bounded adjoint `L₀^* h = 2iΩ[h - R(Vh)]` -/

/-- The manuscript formula `eq:st18-t00064` (tex line 1457) on a radial profile `h`:
`L₀^*h(r) = 2iΩ(r) [h(r) - R(Vh)(r)]`, `V = x - 2`, `R` the Green formula `eq:st18-t00007`. -/
def L0AdjFun (h : ℝ → ℂ) (r : ℝ) : ℂ :=
  2 * Complex.I * (radialOmega r : ℂ) * (h r - R (fun s => (V s : ℂ) * h s) r)

/-- **`eq:st18-t00064`, operator form** (tex lines 1456--1458): the bounded adjoint of `L₀` on
`X_G` is `L₀^* = 2i(Ω - ΩRV)`. -/
theorem adjoint_L0_apply (h : XG) :
    ContinuousLinearMap.adjoint L0 h = (2 * Complex.I) • (omegaOp h - omegaRV h) := by
  refine ext_inner_right ℂ fun v => ?_
  rw [ContinuousLinearMap.adjoint_inner_left]
  have e : L0 v = (-2 * Complex.I) • omegaOp v + (2 * Complex.I) • kROp v := rfl
  rw [e, inner_add_right, inner_smul_right, inner_smul_right, inner_smul_left, inner_sub_left,
    inner_omegaOp_symm, inner_kROp]
  simp only [map_mul, Complex.conj_I, map_ofNat]
  ring

/-- **`eq:st18-t00064`** (tex lines 1456--1458): the bounded `X_G`-adjoint of `L₀`
(`ContinuousLinearMap.adjoint B0012.L0`) is given a.e. by `L₀^*h = 2iΩ[h - R(Vh)]`,
`V = x - 2`. -/
theorem coeFn_adjoint_L0 (h : XG) :
    ⇑(ContinuousLinearMap.adjoint L0 h) =ᵐ[xGMeasure] L0AdjFun ⇑h := by
  rw [adjoint_L0_apply]
  filter_upwards [Lp.coeFn_smul (2 * Complex.I) (omegaOp h - omegaRV h),
    Lp.coeFn_sub (omegaOp h) (omegaRV h), coeFn_omegaOp h, coeFn_omegaRV h] with r h1 h2 h3 h4
  rw [h1, Pi.smul_apply, h2, Pi.sub_apply, h3, h4, L0AdjFun, smul_eq_mul]
  ring

/-- The formula `L0AdjFun` only depends on the `X_G`-class of the profile. -/
theorem L0AdjFun_congr {h g : ℝ → ℂ} (hhg : h =ᵐ[xGMeasure] g) :
    L0AdjFun h =ᵐ[xGMeasure] L0AdjFun g := by
  have h' : h =ᵐ[volume.restrict (Ioi (0 : ℝ))] g := restrict_ac.ae_le hhg
  have hV : (fun s => (V s : ℂ) * h s) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun s => (V s : ℂ) * g s := by
    filter_upwards [h'] with s hs
    rw [hs]
  filter_upwards [hhg, ae_xG_pos] with r h1 hr
  rw [L0AdjFun, L0AdjFun, h1, R_congr hV hr]

/-- The formula maps `X_G` into `X_G`: for every profile `h₂ ∈ X_G`, `L₀^*h₂ ∈ X_G`. -/
theorem memLp_L0AdjFun {h₂ : ℝ → ℂ} (hh : MemLp h₂ 2 xGMeasure) :
    MemLp (L0AdjFun h₂) 2 xGMeasure :=
  (Lp.memLp (ContinuousLinearMap.adjoint L0 (hh.toLp h₂))).ae_eq
    ((coeFn_adjoint_L0 _).trans (L0AdjFun_congr hh.coeFn_toLp))

/-- **`eq:st18-t00064`, profile form** (tex lines 1456--1458): on a profile `h₂ ∈ X_G`, the
bounded adjoint of `L₀` is the class of `2iΩ[h₂ - R(Vh₂)]`. -/
theorem adjoint_L0_toLp {h₂ : ℝ → ℂ} (hh : MemLp h₂ 2 xGMeasure) :
    ContinuousLinearMap.adjoint L0 (hh.toLp h₂) = (memLp_L0AdjFun hh).toLp (L0AdjFun h₂) :=
  Lp.ext ((coeFn_adjoint_L0 _).trans ((L0AdjFun_congr hh.coeFn_toLp).trans
    (memLp_L0AdjFun hh).coeFn_toLp.symm))

/-- The `X_G` pairing integrand of two profiles in `X_G` is integrable on `(0, ∞)`
(Cauchy--Schwarz in `L²(G⁻¹ r dr)`; tex line 678), so the pairing integrals below are genuine
Lebesgue integrals, not Bochner junk values. -/
theorem integrableOn_mul_conj {f₂ g₂ : ℝ → ℂ} (hf : MemLp f₂ 2 xGMeasure)
    (hg : MemLp g₂ 2 xGMeasure) :
    IntegrableOn (fun r => f₂ r * conj (g₂ r) * (((radialGaussianWeight r)⁻¹ * r : ℝ) : ℂ))
      (Ioi 0) := by
  have h1 : Integrable (fun r => f₂ r * conj (g₂ r)) xGMeasure := by
    refine (L2.integrable_inner (𝕜 := ℂ) (hg.toLp g₂) (hf.toLp f₂)).congr ?_
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with r a b
    rw [a, b, RCLike.inner_apply]
  rw [xGMeasure, integrable_withDensity_iff_integrable_smul measurable_xGDensity] at h1
  refine h1.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  simp only [NNReal.smul_def, coe_xGDensity hr, Complex.real_smul]
  ring

/-- **`eq:st18-t00064`, integral form** (tex lines 1456--1461): for profiles `f₂, h₂ ∈ X_G`,
both integrands of the adjoint identity are integrable on `(0, ∞)` ("all integrals are
justified", tex line 1460) and
`∫₀^∞ (L₀f₂) conj(h₂) G⁻¹ r dr = ∫₀^∞ f₂ conj(2iΩ[h₂ - R(Vh₂)]) G⁻¹ r dr`, with `L₀f₂` the
formula of `eq:st18-t00006` (B0012 `L0Fun`). Both formulas define elements of `X_G`
(B0012 `memLp_L0Fun`, `memLp_L0AdjFun`). -/
theorem integral_L0Fun_mul_conj {f₂ h₂ : ℝ → ℂ} (hf : MemLp f₂ 2 xGMeasure)
    (hh : MemLp h₂ 2 xGMeasure) :
    IntegrableOn
        (fun r => L0Fun f₂ r * conj (h₂ r) * (((radialGaussianWeight r)⁻¹ * r : ℝ) : ℂ))
        (Ioi 0) ∧
      IntegrableOn
        (fun r => f₂ r * conj (L0AdjFun h₂ r) * (((radialGaussianWeight r)⁻¹ * r : ℝ) : ℂ))
        (Ioi 0) ∧
      ∫ r in Ioi 0, L0Fun f₂ r * conj (h₂ r) * (((radialGaussianWeight r)⁻¹ * r : ℝ) : ℂ) =
        ∫ r in Ioi 0, f₂ r * conj (L0AdjFun h₂ r) *
          (((radialGaussianWeight r)⁻¹ * r : ℝ) : ℂ) := by
  refine ⟨integrableOn_mul_conj (memLp_L0Fun hf) hh,
    integrableOn_mul_conj hf (memLp_L0AdjFun hh), ?_⟩
  rw [← pairing_toLp (memLp_L0Fun hf) hh, ← pairing_toLp hf (memLp_L0AdjFun hh),
    ← L0_toLp hf, ← adjoint_L0_toLp hh, pairing_eq_inner, pairing_eq_inner,
    ContinuousLinearMap.adjoint_inner_left]

end UnforcedLeray.B0090
