import UnforcedLeray.Units.B0225.Laplace
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Topology.Homotopy.HSpaces

/-!
# B0225 helper: `R_0(μ)f` evaluated pointwise

Blueprint unit B0225 (label `eq:st18-t00118`), `paper/main.tex` lines 3379–3383. The `H`-valued
integral `R_0(μ)f = ∫_0^∞ e^{-μt} T_0(t) f dt` is computed fibre by fibre: for every strongly
measurable representative `F` of `f`, for a.e. `p = (s, q, η)` the scalar integrand
`t ↦ e^{-μt} (T_0(t)F)(p)` (explicit formula `jointRep`) is integrable on `(0, ∞)`, and
`R_0(μ)f(p) = ∫_0^∞ e^{-μt} (T_0(t)F)(p) dt` (`R0_ae_eq`).

The proof tests both sides against the sets `A` of finite `H`-measure: `f ↦ ∫_A f` is a bounded
functional on `H` (`setIntL`, copied with `p` general from `Lib/HeatR3/Comm.lean`,
`setIntegralLp`, whose section variables there ask for a translation-invariant measure), so it
commutes with the Bochner integral in time; Fubini on `A × (0, ∞)` uses
`∫_A |T_0(t)f| ≤ |A|^{1/2} ‖T_0(t)f‖_H ≤ |A|^{1/2} e^{-t/4} ‖f‖_H`. The same method resolves the
scoping risk R2 in `Lib/HeatR3/Comm.lean` (`heatLp_eq_integral`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal

namespace UnforcedLeray.B0225

open UnforcedLeray.B0220 UnforcedLeray.B0224

/-! ### Integration over a set of finite measure as a functional on `L^p` -/

section SetIntegral

variable {α : Type*} [MeasurableSpace α] {m : Measure α}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {p : ℝ≥0∞} [hp1 : Fact (1 ≤ p)]

/-- Copied from `Lib/HeatR3/Comm.lean` (`integrableOn_of_memLp`), for a general measure. -/
theorem integrableOn_of_memLp' {f : α → E} (hf : MemLp f p m) {A : Set α} (hA : m A < ∞) :
    IntegrableOn f A m := by
  have : Fact (m A < ∞) := ⟨hA⟩
  exact (hf.restrict A).integrable hp1.out

/-- `∫_A |f| ≤ m(A)^{1 - 1/p} ‖f‖_p` (Hölder); adapted from `Lib/HeatR3/Comm.lean`
(`norm_setIntegral_le_Lp`). -/
theorem integral_norm_le_Lp (f : Lp E p m) {A : Set α} (hA : m A < ∞) :
    ∫ x in A, ‖f x‖ ∂m ≤ (m A).toReal ^ (1 - 1 / p.toReal) * ‖f‖ := by
  have hint := integrableOn_of_memLp' (Lp.memLp f) hA
  have h1 : ∫ x in A, ‖f x‖ ∂m = (eLpNorm f 1 (m.restrict A)).toReal := by
    rw [integral_norm_eq_lintegral_enorm hint.1, eLpNorm_one_eq_lintegral_enorm]
  rw [h1]
  have h2 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := m.restrict A) (p := 1) (q := p)
    hp1.out (Lp.aestronglyMeasurable f).restrict
  rw [Measure.restrict_apply_univ, ENNReal.toReal_one, div_one] at h2
  have h3 : eLpNorm f p (m.restrict A) ≤ eLpNorm f p m :=
    eLpNorm_mono_measure _ Measure.restrict_le_self
  have hfin : eLpNorm f p m * m A ^ (1 - 1 / p.toReal) ≠ ∞ :=
    ENNReal.mul_ne_top (Lp.eLpNorm_ne_top f)
      (ENNReal.rpow_ne_top_of_nonneg (by
        have : 1 / p.toReal ≤ 1 := by
          rcases eq_or_ne p ∞ with rfl | hp
          · simp
          · have := ENNReal.toReal_mono hp hp1.out
            rw [ENNReal.toReal_one] at this
            exact div_le_one_of_le₀ this (by positivity)
        linarith) hA.ne)
  calc (eLpNorm f 1 (m.restrict A)).toReal
      ≤ (eLpNorm f p m * m A ^ (1 - 1 / p.toReal)).toReal :=
        ENNReal.toReal_mono hfin (h2.trans (by gcongr))
    _ = (m A).toReal ^ (1 - 1 / p.toReal) * ‖f‖ := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_rpow, Lp.norm_def, mul_comm]

variable [CompleteSpace E]

/-- `f ↦ ∫_A f dm` as a bounded complex-linear functional on `L^p(m; E)` (`m A < ∞`). -/
def setIntL (A : Set α) (hA : m A < ∞) : Lp E p m →L[ℂ] E :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x in A, f x ∂m
      map_add' := fun f g => by
        rw [← integral_add (integrableOn_of_memLp' (Lp.memLp f) hA)
          (integrableOn_of_memLp' (Lp.memLp g) hA)]
        exact integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_add f g))
      map_smul' := fun a f => by
        rw [RingHom.id_apply, ← integral_smul]
        exact integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_smul a f)) }
    ((m A).toReal ^ (1 - 1 / p.toReal))
    (fun f => (norm_integral_le_integral_norm _).trans (integral_norm_le_Lp f hA))

theorem setIntL_apply (A : Set α) (hA : m A < ∞) (f : Lp E p m) :
    setIntL A hA f = ∫ x in A, f x ∂m := rfl

end SetIntegral

/-! ### Pointwise evaluation of `R_0(μ) f` -/

variable {c : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [TopologicalSpace.SeparableSpace E]

/-- The integrand `(p, t) ↦ e^{-μt} (T_0(t)F)(p)` on `Profile × ℝ`. -/
def lapRep (c ν : ℝ) (μ : ℂ) (F : Profile → E) (x : Profile × ℝ) : E :=
  Complex.exp (-(μ * x.2)) • jointRep c ν F (x.2, x.1)

theorem stronglyMeasurable_lapRep (c ν : ℝ) (μ : ℂ) {F : Profile → E}
    (hF : StronglyMeasurable F) : StronglyMeasurable (lapRep c ν μ F) := by
  refine (Continuous.stronglyMeasurable (by fun_prop :
    Continuous fun x : Profile × ℝ => Complex.exp (-(μ * x.2)))).smul ?_
  exact (stronglyMeasurable_jointRep c ν hF).comp_measurable measurable_swap

/-- Fubini on `A × (0, ∞)`: the integrand is integrable for every `A` of finite `H`-measure. -/
theorem integrable_lapRep (hc : 0 < c) (ν : ℝ) {μ : ℂ} (hμ : 0 < μ.re + 1 / 4)
    (f : HSpace c E) {F : Profile → E} (hF : StronglyMeasurable F)
    (hFf : F =ᵐ[measureH c] f) {A : Set Profile} (hA : measureH c A < ∞) :
    Integrable (lapRep c ν μ F) (((measureH c).restrict A).prod (volume.restrict (Ioi 0))) := by
  have hK := stronglyMeasurable_lapRep c ν μ hF
  rw [integrable_prod_iff' hK.aestronglyMeasurable]
  set C : ℝ := (measureH c A).toReal ^ (1 - 1 / (2 : ℝ≥0∞).toReal) with hC
  have hC0 : 0 ≤ C := by positivity
  constructor
  · refine Eventually.of_forall fun t => ?_
    have hm := memLp_jointRep hc ν t f hF hFf
    exact (integrableOn_of_memLp' hm hA).smul (Complex.exp (-(μ * t)))
  · refine Integrable.mono' ((exp_neg_integrableOn_Ioi 0 hμ).const_mul (C * ‖f‖)) ?_ ?_
    · exact (hK.norm.integral_prod_left' (μ := (measureH c).restrict A)).aestronglyMeasurable
    · refine Eventually.of_forall fun t => ?_
      have h := T0_ae_jointRep hc ν t f hF hFf
      have hT : ‖(T0 hc ν t : HSpace c E →L[ℝ] HSpace c E)‖ ≤ Real.exp (-t / 4) :=
        norm_T0_le hc ν t
      have h1 : ‖T0 hc ν t f‖ ≤ Real.exp (-t / 4) * ‖f‖ :=
        (T0 hc ν t : HSpace c E →L[ℝ] HSpace c E).le_of_opNorm_le hT f
      have h2 : ∫ p in A, ‖lapRep c ν μ F (p, t)‖ ∂measureH c =
          Real.exp (-(μ.re * t)) * ∫ p in A, ‖(T0 hc ν t f : Profile → E) p‖ ∂measureH c := by
        rw [← integral_const_mul]
        refine integral_congr_ae (ae_restrict_of_ae ?_)
        filter_upwards [h] with p hp
        rw [lapRep, norm_smul, Infra.ExpSemigroup.norm_cexp_neg_mul, hp]
      have h3 := integral_norm_le_Lp (T0 hc ν t f) hA
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _), h2]
      calc Real.exp (-(μ.re * t)) * ∫ p in A, ‖(T0 hc ν t f : Profile → E) p‖ ∂measureH c
          ≤ Real.exp (-(μ.re * t)) * (C * (Real.exp (-t / 4) * ‖f‖)) := by
            refine mul_le_mul_of_nonneg_left (h3.trans ?_) (Real.exp_pos _).le
            exact mul_le_mul_of_nonneg_left h1 hC0
        _ = C * ‖f‖ * Real.exp (-(μ.re + 1 / 4) * t) := by
            rw [show -(μ.re + 1 / 4) * t = -(μ.re * t) + -t / 4 by ring, Real.exp_add]
            ring

/-- **Pointwise form of `R_0(μ) f = ∫_0^∞ e^{-μt} T_0(t) f dt`** (tex lines 3379–3383): for a
strongly measurable representative `F` of `f ∈ H` and `Re μ > -1/4`, for a.e. `p` the integrand
`t ↦ e^{-μt} (T_0(t)F)(p)` is integrable on `(0, ∞)` and its integral is `R_0(μ)f(p)`. -/
theorem R0_ae_eq (hc : 0 < c) (ν : ℝ) {μ : ℂ} (hμ : 0 < μ.re + 1 / 4) (f : HSpace c E)
    {F : Profile → E} (hF : StronglyMeasurable F) (hFf : F =ᵐ[measureH c] f) :
    (∀ᵐ p ∂measureH c, IntegrableOn
      (fun t : ℝ => Complex.exp (-(μ * t)) • jointRep c ν F (t, p)) (Ioi 0)) ∧
    (R0 hc ν μ f : Profile → E) =ᵐ[measureH c]
      fun p => ∫ t : ℝ in Ioi 0, Complex.exp (-(μ * t)) • jointRep c ν F (t, p) := by
  constructor
  · refine ae_of_forall_measure_lt_top_ae_restrict _ fun A _ hA => ?_
    exact (integrable_lapRep hc ν hμ f hF hFf hA).prod_right_ae
  · refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
      (fun A _ hA => integrableOn_of_memLp' (Lp.memLp _) hA)
      (fun A _ hA => (integrable_lapRep hc ν hμ f hF hFf hA).integral_prod_left)
      (fun A _ hA => ?_)
    have hint := integrable_lapRep hc ν hμ f hF hFf hA
    have hswap := integral_integral_swap (f := fun p t => lapRep c ν μ F (p, t)) hint
    change ∫ p in A, (R0 hc ν μ f : Profile → E) p ∂measureH c =
      ∫ p in A, ∫ t in Ioi 0, lapRep c ν μ F (p, t) ∂volume ∂measureH c
    rw [hswap, ← setIntL_apply A hA, R0_apply hc ν hμ]
    change setIntL A hA (∫ t in Ioi 0, lapT0 hc ν μ f t) = _
    rw [← (setIntL A hA).integral_comp_comm (integrableOn_lapT0 hc ν hμ f)]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    have h := T0_ae_jointRep hc ν t f hF hFf
    change setIntL A hA (lapT0 hc ν μ f t) = _
    rw [lapT0, map_smul, setIntL_apply, ← integral_smul]
    refine integral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [h] with p hp
    rw [lapRep, hp]

end UnforcedLeray.B0225
