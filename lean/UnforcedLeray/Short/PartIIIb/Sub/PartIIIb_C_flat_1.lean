import UnforcedLeray.Short.PartIIIb.Concrete.YoungFlat
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Decomposition of `PartIII-b:C/flat/1`: the flat class amplitude (source 4624-4626, 4643-4661)

Source: `the November 2 reference manuscript`.

The explicit amplitude (4645-4648) is
`a_{ν,+}(B) = ∫₀^{1.1/ν} t^μ F_+(t,0)⁻¹ ℓ_{+,νt,c} g_B(t) dt`, and the limiting amplitude (4617-4618)
is `a₀(B) = -½ ℓ_+(H₀) ∫₀^∞ t^μ e^{-λt}(d - ie) dt`. Since `B` is supported in `(0, 1.1/ν)`, the
difference is the integral over `(0, 1.1/ν]` of
`t^μ [F⁻¹(-½(d-ie)(ℓH - ℓ_+(H₀)) - ½(d+ie)ℓH̄ - βℓR) + (F⁻¹ - e^{-λt})(-½ ℓ_+(H₀)(d-ie))]`.
With the Gaussian comparison (4650-4654), `c = ν⁻²` (so `c⁻² = ν⁴ ≤ ν`), the two estimates of
`F_+(t,0)⁻¹` below (4655-4658) and the pointwise bound `|B(t)| ≤ ‖B‖_a e^{at} t^{3/2}`
(definition of `‖B‖_a`, 4589-4592), the error has the integrable majorant
`C ν ‖B‖_a t^{μ+3/2}(1+t+t²) e^{-(γ/3-a)t}` (4659-4661; `0 < a < γ/16`, 4586). This file states the
three analytic inputs as `Prop`s and proves `flatClassAmplitudeC_of` from them.

Leaves: `FpmInvSubExp` (4655-4658), `FpmInvBound` (4645-4648 with `t/(1+νt) ≥ t/2.1`, 4666-4667),
`BclassAeBound` (4589-4592).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb.ConcreteYF

namespace FlatAmp

/-! ## The three analytic inputs (leaves) -/

/-- `|F_+(t,0)⁻¹ - e^{-λt}| ≤ C ν (t + t²) e^{-γt/3}` for `0 ≤ t ≤ 1.1/ν` (source 4655-4658),
`γ = Re λ`, with `F_+(t,0)⁻¹ = e^{-λt/(1+νt)}(1+νt)^{-κ}` (4648). True for `Re λ > 0`, with `C`
depending only on `λ, κ`: split `e^{-λz}((1+νt)^{-κ} - 1) + (e^{-λz} - e^{-λt})`, `z = t/(1+νt)`,
`t - z ≤ νt²`, `z ≥ t/3`. -/
def FpmInvSubExp (lam κ : ℂ) : Prop :=
  ∃ C : ℝ, ∀ ν : ℝ, 0 < ν → ∀ t ∈ Icc (0 : ℝ) (1.1 / ν),
    ‖(Fpm true lam κ ν t 0)⁻¹ - Complex.exp (-lam * (t : ℂ))‖ ≤
      C * ν * (t + t ^ 2) * Real.exp (-(lam.re / 3) * t)

/-- `|F_+(t,0)⁻¹| ≤ C e^{-γt/3}` for `0 ≤ t ≤ 1.1/ν` (source 4645-4648: `|F_+(t,0)⁻¹| =
e^{-γ t/(1+νt)} (1+νt)^{-Re κ}`, and `t/(1+νt) ≥ t/2.1 ≥ t/3` on the support, 4666-4667). -/
def FpmInvBound (lam κ : ℂ) : Prop :=
  ∃ C : ℝ, ∀ ν : ℝ, 0 < ν → ∀ t ∈ Icc (0 : ℝ) (1.1 / ν),
    ‖(Fpm true lam κ ν t 0)⁻¹‖ ≤ C * Real.exp (-(lam.re / 3) * t)

/-- Pointwise form of the class norm (source 4589-4592,
`‖B‖_a = ess sup_{s>0} e^{-as} s^{-3/2}|B(s)|`): for `B ∈ 𝓑_a`,
`|B(t)| ≤ ‖B‖_a e^{at} t^{3/2}` for almost every `t > 0`. -/
def BclassAeBound : Prop :=
  ∀ (a ν : ℝ) (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ), IsBclass a ν B →
    ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      matNorm (B t) ≤ bNorm a B * (Real.exp (a * t) * t ^ (3 / 2 : ℝ))

/-! ## Integrands and majorant -/

/-- The integrand of `a_{ν,+}(B)` (source 4645-4648). -/
def ampIntegrand (S : FlatSetting) (lam κ : ℂ) (ν μ : ℝ) (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (t : ℝ) : ℂ :=
  (t : ℂ) ^ (μ : ℂ) * (Fpm true lam κ ν t 0)⁻¹ * (S.pk.ell true t) (S.gB B t)

/-- The integrand of `a₀(B)`, with the prefactor `-½ ℓ_+(H₀)` (source 4617-4618). -/
def zeroIntegrand (lam ell : ℂ) (μ : ℝ) (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) : ℂ :=
  -(1 / 2 : ℂ) * ell * ((t : ℂ) ^ (μ : ℂ) * Complex.exp (-lam * (t : ℂ)) *
    (((Bd (B t) : ℝ) : ℂ) - Complex.I * ((Be (B t) : ℝ) : ℂ)))

/-- The majorant `t^{μ+3/2}(1+t+t²)e^{-bt}`, `b = γ/3 - a` (source 4659-4661). -/
def majorant (μ b t : ℝ) : ℝ := t ^ (μ + 3 / 2) * (1 + t + t ^ 2) * Real.exp (-b * t)

lemma majorant_nonneg (μ b t : ℝ) (ht : 0 ≤ t) : 0 ≤ majorant μ b t := by
  unfold majorant
  positivity

lemma majorant_integrableOn (μ b : ℝ) (hμ : -1 < μ + 3 / 2) (hb : 0 < b) :
    IntegrableOn (majorant μ b) (Ioi 0) := by
  have h0 := integrableOn_rpow_mul_exp_neg_mul_rpow (s := μ + 3 / 2) (p := 1) hμ one_pos hb
  have h1 := integrableOn_rpow_mul_exp_neg_mul_rpow (s := μ + 3 / 2 + 1) (p := 1)
    (by linarith) one_pos hb
  have h2 := integrableOn_rpow_mul_exp_neg_mul_rpow (s := μ + 3 / 2 + 2) (p := 1)
    (by linarith) one_pos hb
  refine ((h0.add h1).add h2).congr_fun (fun t ht => ?_) measurableSet_Ioi
  have ht0 : 0 < t := ht
  simp only [Pi.add_apply, Real.rpow_one]
  rw [Real.rpow_add ht0 (μ + 3 / 2) 1, Real.rpow_add ht0 (μ + 3 / 2) 2, Real.rpow_one,
    Real.rpow_two]
  unfold majorant
  ring

/-! ## Elementary bounds -/

lemma matNorm_nonneg (M : Matrix (Fin 3) (Fin 3) ℝ) : 0 ≤ matNorm M :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))

lemma abs_bd_add_abs_be_le (M : Matrix (Fin 3) (Fin 3) ℝ) : |Bd M| + |Be M| ≤ matNorm M := by
  have hd : |Bd M| ≤ (|M 0 0| + |M 2 2|) / 2 := by
    unfold Bd
    rw [abs_le]
    constructor <;>
      linarith [le_abs_self (M 0 0), neg_abs_le (M 0 0), le_abs_self (M 2 2), neg_abs_le (M 2 2)]
  have he : |Be M| ≤ (|M 0 2| + |M 2 0|) / 2 := by
    unfold Be
    rw [abs_le]
    constructor <;>
      linarith [le_abs_self (M 0 2), neg_abs_le (M 0 2), le_abs_self (M 2 0), neg_abs_le (M 2 0)]
  calc |Bd M| + |Be M| ≤ (|M 0 0| + |M 2 2|) / 2 + (|M 0 2| + |M 2 0|) / 2 := add_le_add hd he
    _ ≤ matNorm M := by
      simp only [matNorm, Fin.sum_univ_three]
      linarith [abs_nonneg (M 0 0), abs_nonneg (M 0 1), abs_nonneg (M 0 2), abs_nonneg (M 1 0),
        abs_nonneg (M 1 1), abs_nonneg (M 1 2), abs_nonneg (M 2 0), abs_nonneg (M 2 1),
        abs_nonneg (M 2 2)]

lemma abs_beta_le (M : Matrix (Fin 3) (Fin 3) ℝ) : |Bbeta M| ≤ matNorm M := by
  have hb : |Bbeta M| ≤ (|M 0 0| + |M 2 2|) / 2 := by
    unfold Bbeta
    rw [abs_le]
    constructor <;>
      linarith [le_abs_self (M 0 0), neg_abs_le (M 0 0), le_abs_self (M 2 2), neg_abs_le (M 2 2)]
  refine hb.trans ?_
  simp only [matNorm, Fin.sum_univ_three]
  linarith [abs_nonneg (M 0 0), abs_nonneg (M 0 1), abs_nonneg (M 0 2), abs_nonneg (M 1 0),
    abs_nonneg (M 1 1), abs_nonneg (M 1 2), abs_nonneg (M 2 0), abs_nonneg (M 2 1),
    abs_nonneg (M 2 2)]

lemma norm_dmie_le (M : Matrix (Fin 3) (Fin 3) ℝ) :
    ‖((Bd M : ℝ) : ℂ) - Complex.I * ((Be M : ℝ) : ℂ)‖ ≤ matNorm M := by
  have h1 : ‖((Bd M : ℝ) : ℂ) - Complex.I * ((Be M : ℝ) : ℂ)‖ ≤ |Bd M| + |Be M| := by
    calc ‖((Bd M : ℝ) : ℂ) - Complex.I * ((Be M : ℝ) : ℂ)‖
        ≤ ‖((Bd M : ℝ) : ℂ)‖ + ‖Complex.I * ((Be M : ℝ) : ℂ)‖ := norm_sub_le _ _
      _ = |Bd M| + |Be M| := by
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
  exact h1.trans (abs_bd_add_abs_be_le M)

lemma norm_dpie_le (M : Matrix (Fin 3) (Fin 3) ℝ) :
    ‖((Bd M : ℝ) : ℂ) + Complex.I * ((Be M : ℝ) : ℂ)‖ ≤ matNorm M := by
  have h1 : ‖((Bd M : ℝ) : ℂ) + Complex.I * ((Be M : ℝ) : ℂ)‖ ≤ |Bd M| + |Be M| := by
    calc ‖((Bd M : ℝ) : ℂ) + Complex.I * ((Be M : ℝ) : ℂ)‖
        ≤ ‖((Bd M : ℝ) : ℂ)‖ + ‖Complex.I * ((Be M : ℝ) : ℂ)‖ := norm_add_le _ _
      _ = |Bd M| + |Be M| := by
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
  exact h1.trans (abs_bd_add_abs_be_le M)

/-- Linearity of the frozen dual on the vorticity source `g_B` (source 4605-4608). -/
lemma ell_gB (S : FlatSetting) (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) :
    S.pk.ell true t (S.gB B t) =
      -(1 / 2 : ℂ) * (((Bd (B t) : ℝ) : ℂ) - Complex.I * ((Be (B t) : ℝ) : ℂ)) *
          S.pk.ell true t (S.Hper t)
        + -(1 / 2 : ℂ) * (((Bd (B t) : ℝ) : ℂ) + Complex.I * ((Be (B t) : ℝ) : ℂ)) *
          S.pk.ell true t (S.conjX (S.Hper t))
        - ((Bbeta (B t) : ℝ) : ℂ) * S.pk.ell true t (S.Rper t) := by
  simp only [FlatSetting.gB, map_add, map_sub, map_smul, smul_eq_mul]

lemma Fpm_true (lam κ : ℂ) (ν s t : ℝ) :
    Fpm true lam κ ν s t =
      Complex.exp (lam * ((zOf ν s - zOf ν t : ℝ) : ℂ)) * ((aOf ν s / aOf ν t : ℝ) : ℂ) ^ κ :=
  rfl

/-! ## Measurability -/

lemma measurable_Fpm_inv (lam κ : ℂ) (ν : ℝ) :
    Measurable (fun t : ℝ => (Fpm true lam κ ν t 0)⁻¹) := by
  have ha : Measurable (fun t : ℝ => aOf ν t) := by
    unfold aOf
    first
      | exact measurable_const.fun_add (measurable_const.fun_mul measurable_id)
      | exact measurable_const.add (measurable_const.mul measurable_id)
      | fun_prop
      | measurability
  have hz : Measurable (fun t : ℝ => zOf ν t) := by
    unfold zOf
    first
      | exact measurable_id.fun_div ha
      | exact measurable_id.div ha
      | fun_prop
      | measurability
  have h1 : Measurable (fun t : ℝ => Complex.exp (lam * ((zOf ν t - zOf ν 0 : ℝ) : ℂ))) :=
    Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp (hz.sub_const _)).const_mul lam)
  have h2 : Measurable (fun t : ℝ => ((aOf ν t / aOf ν 0 : ℝ) : ℂ) ^ κ) :=
    (Complex.measurable_ofReal.comp (ha.div_const _)).pow_const κ
  simp only [Fpm_true]
  first
    | exact (h1.fun_mul h2).inv
    | exact (h1.mul h2).inv
    | exact Measurable.inv (h1.fun_mul h2)
    | fun_prop

lemma measurable_zeroIntegrand (lam ell : ℂ) (μ : ℝ) (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hBd : Measurable (fun t => Bd (B t))) (hBe : Measurable (fun t => Be (B t))) :
    Measurable (zeroIntegrand lam ell μ B) := by
  have hD : Measurable (fun t => ((Bd (B t) : ℝ) : ℂ) - Complex.I * ((Be (B t) : ℝ) : ℂ)) := by
    first
      | exact (Complex.measurable_ofReal.comp hBd).fun_sub
          ((Complex.measurable_ofReal.comp hBe).const_mul Complex.I)
      | exact (Complex.measurable_ofReal.comp hBd).sub
          ((Complex.measurable_ofReal.comp hBe).const_mul Complex.I)
      | fun_prop
  have hw : Measurable (fun t : ℝ => (t : ℂ) ^ (μ : ℂ)) := Complex.measurable_ofReal.pow_const _
  have hex : Measurable (fun t : ℝ => Complex.exp (-lam * (t : ℂ))) :=
    Complex.measurable_exp.comp (Complex.measurable_ofReal.const_mul (-lam))
  unfold zeroIntegrand
  first
    | exact ((hw.fun_mul hex).fun_mul hD).const_mul (-(1 / 2 : ℂ) * ell)
    | exact ((hw.mul hex).mul hD).const_mul (-(1 / 2 : ℂ) * ell)
    | fun_prop

lemma measurable_ampIntegrand (S : FlatSetting) (lam κ : ℂ) (ν μ : ℝ)
    (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hBd : Measurable (fun t => Bd (B t))) (hBe : Measurable (fun t => Be (B t)))
    (hBb : Measurable (fun t => Bbeta (B t)))
    (hpH : Measurable (fun t => S.pk.ell true t (S.Hper t)))
    (hpHb : Measurable (fun t => S.pk.ell true t (S.conjX (S.Hper t))))
    (hpR : Measurable (fun t => S.pk.ell true t (S.Rper t))) :
    Measurable (ampIntegrand S lam κ ν μ B) := by
  have hD : Measurable (fun t => ((Bd (B t) : ℝ) : ℂ) - Complex.I * ((Be (B t) : ℝ) : ℂ)) := by
    first
      | exact (Complex.measurable_ofReal.comp hBd).fun_sub
          ((Complex.measurable_ofReal.comp hBe).const_mul Complex.I)
      | exact (Complex.measurable_ofReal.comp hBd).sub
          ((Complex.measurable_ofReal.comp hBe).const_mul Complex.I)
      | fun_prop
  have hDp : Measurable (fun t => ((Bd (B t) : ℝ) : ℂ) + Complex.I * ((Be (B t) : ℝ) : ℂ)) := by
    first
      | exact (Complex.measurable_ofReal.comp hBd).fun_add
          ((Complex.measurable_ofReal.comp hBe).const_mul Complex.I)
      | exact (Complex.measurable_ofReal.comp hBd).add
          ((Complex.measurable_ofReal.comp hBe).const_mul Complex.I)
      | fun_prop
  have hβ : Measurable (fun t => ((Bbeta (B t) : ℝ) : ℂ)) := Complex.measurable_ofReal.comp hBb
  have hlg : Measurable (fun t => S.pk.ell true t (S.gB B t)) := by
    have hfun : (fun t => S.pk.ell true t (S.gB B t)) = fun t =>
        -(1 / 2 : ℂ) * (((Bd (B t) : ℝ) : ℂ) - Complex.I * ((Be (B t) : ℝ) : ℂ)) *
            S.pk.ell true t (S.Hper t)
          + -(1 / 2 : ℂ) * (((Bd (B t) : ℝ) : ℂ) + Complex.I * ((Be (B t) : ℝ) : ℂ)) *
            S.pk.ell true t (S.conjX (S.Hper t))
          - ((Bbeta (B t) : ℝ) : ℂ) * S.pk.ell true t (S.Rper t) := funext (ell_gB S B)
    rw [hfun]
    first
      | exact (((hD.const_mul (-(1 / 2 : ℂ))).fun_mul hpH).fun_add
          ((hDp.const_mul (-(1 / 2 : ℂ))).fun_mul hpHb)).fun_sub (hβ.fun_mul hpR)
      | exact (((hD.const_mul (-(1 / 2 : ℂ))).mul hpH).add
          ((hDp.const_mul (-(1 / 2 : ℂ))).mul hpHb)).sub (hβ.mul hpR)
      | fun_prop
  have hw : Measurable (fun t : ℝ => (t : ℂ) ^ (μ : ℂ)) := Complex.measurable_ofReal.pow_const _
  have hF := measurable_Fpm_inv lam κ ν
  unfold ampIntegrand
  first
    | exact (hw.fun_mul hF).fun_mul hlg
    | exact (hw.mul hF).mul hlg
    | fun_prop

/-! ## The support reduction of `a₀` -/

lemma aZero_eq (lam ell : ℂ) (μ ν : ℝ) (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hsupp : ∀ s, s ∉ Ioo 0 (1.1 / ν) → B s = 0) :
    aZero lam ell (μ : ℂ) B = ∫ t in Ioc 0 (1.1 / ν), zeroIntegrand lam ell μ B t := by
  unfold aZero zeroIntegrand
  rw [← integral_const_mul]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self ?_
  intro t ht
  have ht0 : 0 < t := ht.1
  have htT : 1.1 / ν < t := by
    by_contra hle
    exact ht.2 ⟨ht0, not_lt.mp hle⟩
  have hBt : B t = 0 := hsupp t (fun h => absurd h.2 (not_lt.mpr htT.le))
  simp [hBt, Bd, Be]

/-! ## Pointwise estimates -/

/-- The algebraic core of the error estimate, with all objects as variables. -/
lemma abstract_bound (W Fi ex D Dp β lH lHb lR ell : ℂ) (w e m ν t CF CS CG : ℝ)
    (hW : ‖W‖ = w) (hw : 0 ≤ w) (he : 0 ≤ e) (hm0 : 0 ≤ m) (hν : 0 < ν) (hν4 : ν ^ 4 ≤ ν)
    (ht : 0 ≤ t)
    (hFi : ‖Fi‖ ≤ CF * e) (hFd : ‖Fi - ex‖ ≤ CS * ν * (t + t ^ 2) * e)
    (hD : ‖D‖ ≤ m) (hDp : ‖Dp‖ ≤ m) (hβ : ‖β‖ ≤ m)
    (hGH : ‖lH - ell‖ ≤ CG * (ν * t + ν ^ 4)) (hGHb : ‖lHb‖ ≤ CG * ν ^ 4)
    (hGR : ‖lR‖ ≤ CG * ν ^ 4) :
    ‖W * Fi * (-(1 / 2 : ℂ) * D * lH + -(1 / 2 : ℂ) * Dp * lHb - β * lR) -
        -(1 / 2 : ℂ) * ell * (W * ex * D)‖ ≤
      (3 * |CF| * |CG| + |CS| * ‖ell‖) * ν * (w * e * m * (1 + t + t ^ 2)) := by
  have key : W * Fi * (-(1 / 2 : ℂ) * D * lH + -(1 / 2 : ℂ) * Dp * lHb - β * lR) -
        -(1 / 2 : ℂ) * ell * (W * ex * D) =
      W * (Fi * (-(1 / 2 : ℂ) * D * (lH - ell) + -(1 / 2 : ℂ) * Dp * lHb - β * lR) +
        (Fi - ex) * (-(1 / 2 : ℂ) * ell * D)) := by ring
  rw [key, norm_mul, hW]
  have hh : ‖(-(1 / 2 : ℂ))‖ = 1 / 2 := by
    first
      | norm_num
      | simp
      | (rw [norm_neg, norm_div, norm_one]; norm_num)
  have hCF' : ‖Fi‖ ≤ |CF| * e := hFi.trans (mul_le_mul_of_nonneg_right (le_abs_self _) he)
  have htt : 0 ≤ t + t ^ 2 := by positivity
  have hFd' : ‖Fi - ex‖ ≤ |CS| * ν * (t + t ^ 2) * e :=
    hFd.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self _) hν.le) htt) he)
  have hνt : 0 ≤ ν * t + ν ^ 4 := by positivity
  have hGH' : ‖lH - ell‖ ≤ |CG| * (ν * t + ν ^ 4) :=
    hGH.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hνt)
  have hν40 : 0 ≤ ν ^ 4 := by positivity
  have hGHb' : ‖lHb‖ ≤ |CG| * ν ^ 4 :=
    hGHb.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hν40)
  have hGR' : ‖lR‖ ≤ |CG| * ν ^ 4 :=
    hGR.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hν40)
  have hs : ‖lH - ell‖ + ‖lHb‖ + ‖lR‖ ≤ |CG| * ν * (t + 3) := by
    have := mul_le_mul_of_nonneg_left hν4 (abs_nonneg CG)
    nlinarith
  have hX : ‖-(1 / 2 : ℂ) * D * (lH - ell) + -(1 / 2 : ℂ) * Dp * lHb - β * lR‖ ≤
      m * (|CG| * ν * (t + 3)) := by
    calc ‖-(1 / 2 : ℂ) * D * (lH - ell) + -(1 / 2 : ℂ) * Dp * lHb - β * lR‖
        ≤ ‖-(1 / 2 : ℂ) * D * (lH - ell)‖ + ‖-(1 / 2 : ℂ) * Dp * lHb‖ + ‖β * lR‖ :=
          (norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
      _ = 1 / 2 * ‖D‖ * ‖lH - ell‖ + 1 / 2 * ‖Dp‖ * ‖lHb‖ + ‖β‖ * ‖lR‖ := by
          simp only [norm_mul, hh]
      _ ≤ m * ‖lH - ell‖ + m * ‖lHb‖ + m * ‖lR‖ := by
          have a1 := mul_le_mul_of_nonneg_right hD (norm_nonneg (lH - ell))
          have a2 := mul_le_mul_of_nonneg_right hDp (norm_nonneg lHb)
          have a3 := mul_le_mul_of_nonneg_right hβ (norm_nonneg lR)
          have b1 := mul_nonneg (norm_nonneg D) (norm_nonneg (lH - ell))
          have b2 := mul_nonneg (norm_nonneg Dp) (norm_nonneg lHb)
          nlinarith
      _ = m * (‖lH - ell‖ + ‖lHb‖ + ‖lR‖) := by ring
      _ ≤ m * (|CG| * ν * (t + 3)) := mul_le_mul_of_nonneg_left hs hm0
  have hY : ‖-(1 / 2 : ℂ) * ell * D‖ ≤ ‖ell‖ * m := by
    rw [norm_mul, norm_mul, hh]
    have c1 := mul_le_mul_of_nonneg_left hD (norm_nonneg ell)
    have c2 := mul_nonneg (norm_nonneg ell) (norm_nonneg D)
    nlinarith
  have hin : ‖Fi * (-(1 / 2 : ℂ) * D * (lH - ell) + -(1 / 2 : ℂ) * Dp * lHb - β * lR) +
        (Fi - ex) * (-(1 / 2 : ℂ) * ell * D)‖ ≤
      |CF| * e * (m * (|CG| * ν * (t + 3))) + |CS| * ν * (t + t ^ 2) * e * (‖ell‖ * m) := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul]
      exact mul_le_mul hCF' hX (norm_nonneg _) (mul_nonneg (abs_nonneg _) he)
    · rw [norm_mul]
      exact mul_le_mul hFd' hY (norm_nonneg _)
        (mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) hν.le) htt) he)
  have hpoly : |CF| * |CG| * (t + 3) + |CS| * ‖ell‖ * (t + t ^ 2) ≤
      (3 * |CF| * |CG| + |CS| * ‖ell‖) * (1 + t + t ^ 2) := by
    have h1 : 0 ≤ |CF| * |CG| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have h2 : 0 ≤ |CS| * ‖ell‖ := mul_nonneg (abs_nonneg _) (norm_nonneg _)
    nlinarith [mul_nonneg h1 ht, mul_nonneg h1 (sq_nonneg t)]
  have hwem : 0 ≤ w * e * m * ν := mul_nonneg (mul_nonneg (mul_nonneg hw he) hm0) hν.le
  calc w * ‖Fi * (-(1 / 2 : ℂ) * D * (lH - ell) + -(1 / 2 : ℂ) * Dp * lHb - β * lR) +
        (Fi - ex) * (-(1 / 2 : ℂ) * ell * D)‖
      ≤ w * (|CF| * e * (m * (|CG| * ν * (t + 3))) +
          |CS| * ν * (t + t ^ 2) * e * (‖ell‖ * m)) := mul_le_mul_of_nonneg_left hin hw
    _ = (w * e * m * ν) * (|CF| * |CG| * (t + 3) + |CS| * ‖ell‖ * (t + t ^ 2)) := by ring
    _ ≤ (w * e * m * ν) * ((3 * |CF| * |CG| + |CS| * ‖ell‖) * (1 + t + t ^ 2)) :=
        mul_le_mul_of_nonneg_left hpoly hwem
    _ = (3 * |CF| * |CG| + |CS| * ‖ell‖) * ν * (w * e * m * (1 + t + t ^ 2)) := by ring

lemma rpow_exp_combine (μ a lr t : ℝ) (ht0 : 0 < t) :
    t ^ μ * t ^ (3 / 2 : ℝ) = t ^ (μ + 3 / 2) ∧
      Real.exp (-(lr / 3) * t) * Real.exp (a * t) = Real.exp (-(lr / 3 - a) * t) := by
  refine ⟨(Real.rpow_add ht0 μ (3 / 2)).symm, ?_⟩
  rw [← Real.exp_add]
  congr 1
  ring

/-- Pointwise error estimate (source 4659-4661). -/
lemma pointwise_error (S : FlatSetting) (lam κ ell : ℂ) (μ a ν t K CF CS CG : ℝ)
    (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hν : 0 < ν) (hν4 : ν ^ 4 ≤ ν) (ht0 : 0 < t) (hK : 0 ≤ K)
    (hm : matNorm (B t) ≤ K * (Real.exp (a * t) * t ^ (3 / 2 : ℝ)))
    (hFi : ‖(Fpm true lam κ ν t 0)⁻¹‖ ≤ CF * Real.exp (-(lam.re / 3) * t))
    (hFd : ‖(Fpm true lam κ ν t 0)⁻¹ - Complex.exp (-lam * (t : ℂ))‖ ≤
      CS * ν * (t + t ^ 2) * Real.exp (-(lam.re / 3) * t))
    (hGH : ‖S.pk.ell true t (S.Hper t) - ell‖ ≤ CG * (ν * t + ν ^ 4))
    (hGHb : ‖S.pk.ell true t (S.conjX (S.Hper t))‖ ≤ CG * ν ^ 4)
    (hGR : ‖S.pk.ell true t (S.Rper t)‖ ≤ CG * ν ^ 4) :
    ‖ampIntegrand S lam κ ν μ B t - zeroIntegrand lam ell μ B t‖ ≤
      (3 * |CF| * |CG| + |CS| * ‖ell‖) * ν * K * majorant μ (lam.re / 3 - a) t := by
  have hWn : ‖(t : ℂ) ^ (μ : ℂ)‖ = t ^ μ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.ofReal_re]
  have hβn : ‖((Bbeta (B t) : ℝ) : ℂ)‖ ≤ matNorm (B t) := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_beta_le _
  have hab := abstract_bound ((t : ℂ) ^ (μ : ℂ)) ((Fpm true lam κ ν t 0)⁻¹)
    (Complex.exp (-lam * (t : ℂ)))
    (((Bd (B t) : ℝ) : ℂ) - Complex.I * ((Be (B t) : ℝ) : ℂ))
    (((Bd (B t) : ℝ) : ℂ) + Complex.I * ((Be (B t) : ℝ) : ℂ))
    ((Bbeta (B t) : ℝ) : ℂ) (S.pk.ell true t (S.Hper t)) (S.pk.ell true t (S.conjX (S.Hper t)))
    (S.pk.ell true t (S.Rper t)) ell (t ^ μ) (Real.exp (-(lam.re / 3) * t)) (matNorm (B t)) ν t
    CF CS CG hWn (Real.rpow_nonneg ht0.le _) (Real.exp_pos _).le (matNorm_nonneg _) hν hν4 ht0.le
    hFi hFd (norm_dmie_le _) (norm_dpie_le _) hβn hGH hGHb hGR
  have hC0 : 0 ≤ 3 * |CF| * |CG| + |CS| * ‖ell‖ := by positivity
  have hp : 0 ≤ 1 + t + t ^ 2 := by positivity
  have hwe : 0 ≤ t ^ μ * Real.exp (-(lam.re / 3) * t) :=
    mul_nonneg (Real.rpow_nonneg ht0.le _) (Real.exp_pos _).le
  obtain ⟨hpow, hexp⟩ := rpow_exp_combine μ a lam.re t ht0
  unfold ampIntegrand zeroIntegrand
  rw [ell_gB]
  refine hab.trans ?_
  show _ ≤ (3 * |CF| * |CG| + |CS| * ‖ell‖) * ν * K *
    (t ^ (μ + 3 / 2) * (1 + t + t ^ 2) * Real.exp (-(lam.re / 3 - a) * t))
  calc (3 * |CF| * |CG| + |CS| * ‖ell‖) * ν *
        (t ^ μ * Real.exp (-(lam.re / 3) * t) * matNorm (B t) * (1 + t + t ^ 2))
      ≤ (3 * |CF| * |CG| + |CS| * ‖ell‖) * ν *
        (t ^ μ * Real.exp (-(lam.re / 3) * t) * (K * (Real.exp (a * t) * t ^ (3 / 2 : ℝ))) *
          (1 + t + t ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC0 hν.le)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hwe) hp
    _ = (3 * |CF| * |CG| + |CS| * ‖ell‖) * ν * K *
        ((t ^ μ * t ^ (3 / 2 : ℝ)) * (1 + t + t ^ 2) *
          (Real.exp (-(lam.re / 3) * t) * Real.exp (a * t))) := by ring
    _ = (3 * |CF| * |CG| + |CS| * ‖ell‖) * ν * K *
        (t ^ (μ + 3 / 2) * (1 + t + t ^ 2) * Real.exp (-(lam.re / 3 - a) * t)) := by
        rw [hpow, hexp]

/-- Pointwise bound of the `a₀` integrand by the majorant. -/
lemma pointwise_zero (lam ell : ℂ) (μ a t K : ℝ) (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hlam : 0 < lam.re) (ht0 : 0 < t) (hK : 0 ≤ K)
    (hm : matNorm (B t) ≤ K * (Real.exp (a * t) * t ^ (3 / 2 : ℝ))) :
    ‖zeroIntegrand lam ell μ B t‖ ≤ ‖ell‖ * K * majorant μ (lam.re / 3 - a) t := by
  have hD := norm_dmie_le (B t)
  have hWn : ‖(t : ℂ) ^ (μ : ℂ)‖ = t ^ μ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.ofReal_re]
  have hexn : ‖Complex.exp (-lam * (t : ℂ))‖ = Real.exp (-(lam.re * t)) := by
    rw [Complex.norm_exp]
    congr 1
    simp
  have hh : ‖(-(1 / 2 : ℂ))‖ = 1 / 2 := by
    first
      | norm_num
      | simp
      | (rw [norm_neg, norm_div, norm_one]; norm_num)
  have hexle : Real.exp (-(lam.re * t)) ≤ Real.exp (-(lam.re / 3) * t) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_pos hlam ht0]
  have htp : 0 ≤ t ^ μ := Real.rpow_nonneg ht0.le _
  obtain ⟨hpow, hexp⟩ := rpow_exp_combine μ a lam.re t ht0
  have h1 : (1 : ℝ) ≤ 1 + t + t ^ 2 := by nlinarith [sq_nonneg t]
  have hX0 : 0 ≤ t ^ μ * Real.exp (-(lam.re * t)) *
      ‖((Bd (B t) : ℝ) : ℂ) - Complex.I * ((Be (B t) : ℝ) : ℂ)‖ :=
    mul_nonneg (mul_nonneg htp (Real.exp_pos _).le) (norm_nonneg _)
  have hXY : t ^ μ * Real.exp (-(lam.re * t)) *
      ‖((Bd (B t) : ℝ) : ℂ) - Complex.I * ((Be (B t) : ℝ) : ℂ)‖ ≤
      t ^ μ * Real.exp (-(lam.re / 3) * t) * (K * (Real.exp (a * t) * t ^ (3 / 2 : ℝ))) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hexle htp) (hD.trans hm) (norm_nonneg _)
      (mul_nonneg htp (Real.exp_pos _).le)
  unfold zeroIntegrand
  simp only [norm_mul]
  rw [hWn, hexn, hh]
  show _ ≤ ‖ell‖ * K * (t ^ (μ + 3 / 2) * (1 + t + t ^ 2) * Real.exp (-(lam.re / 3 - a) * t))
  calc 1 / 2 * ‖ell‖ * (t ^ μ * Real.exp (-(lam.re * t)) *
        ‖((Bd (B t) : ℝ) : ℂ) - Complex.I * ((Be (B t) : ℝ) : ℂ)‖)
      ≤ ‖ell‖ * (t ^ μ * Real.exp (-(lam.re * t)) *
        ‖((Bd (B t) : ℝ) : ℂ) - Complex.I * ((Be (B t) : ℝ) : ℂ)‖) := by
        have := mul_nonneg (norm_nonneg ell) hX0
        linarith
    _ ≤ ‖ell‖ * (t ^ μ * Real.exp (-(lam.re / 3) * t) *
        (K * (Real.exp (a * t) * t ^ (3 / 2 : ℝ)))) :=
        mul_le_mul_of_nonneg_left hXY (norm_nonneg _)
    _ = ‖ell‖ * K * ((t ^ μ * t ^ (3 / 2 : ℝ)) * 1 *
        (Real.exp (-(lam.re / 3) * t) * Real.exp (a * t))) := by ring
    _ ≤ ‖ell‖ * K * ((t ^ μ * t ^ (3 / 2 : ℝ)) * (1 + t + t ^ 2) *
        (Real.exp (-(lam.re / 3) * t) * Real.exp (a * t))) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg _) hK)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = ‖ell‖ * K * (t ^ (μ + 3 / 2) * (1 + t + t ^ 2) * Real.exp (-(lam.re / 3 - a) * t)) := by
        rw [hpow, hexp]

/-! ## The conditional class amplitude -/

/-- `flat-return:class-amplitude` (source 4624-4626, proof 4643-4661) from the three analytic
inputs. -/
theorem flatClassAmplitudeC_of (S : ℕ → FlatSetting) (ν : ℕ → ℝ) (lam κ ell : ℂ) (μ a : ℝ)
    (h1 : FpmInvSubExp lam κ) (h2 : FpmInvBound lam κ) (h3 : BclassAeBound) :
    FlatClassAmplitudeC S ν lam κ ell μ a := by
  intro hyp hG
  obtain ⟨hνpos, hνlim, hlam, -, -⟩ := hyp.young
  obtain ⟨CS, hCS⟩ := h1
  obtain ⟨CF, hCF⟩ := h2
  obtain ⟨CG, NG, hCG⟩ := hG
  have hμ : 0 < μ := hyp.mu_pos
  have ha0 : 0 < a := hyp.a_pos
  have halt : a < lam.re / 16 := hyp.a_lt
  have hb : 0 < lam.re / 3 - a := by linarith
  have hMajInt : IntegrableOn (majorant μ (lam.re / 3 - a)) (Ioi 0) :=
    majorant_integrableOn μ (lam.re / 3 - a) (by linarith) hb
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 (hνlim.eventually (gt_mem_nhds one_pos))
  have hC00 : 0 ≤ 3 * |CF| * |CG| + |CS| * ‖ell‖ := by positivity
  refine ⟨(3 * |CF| * |CG| + |CS| * ‖ell‖) * ∫ t in Ioi (0 : ℝ), majorant μ (lam.re / 3 - a) t,
    max NG N1, fun n hn B hB => ?_⟩
  show ‖((S n).toPkg lam κ (ν n) μ).aNu B - aZero lam ell (μ : ℂ) B‖ ≤ _
  have hnG : NG ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : ν n < 1 := hN1 n (le_trans (le_max_right _ _) hn)
  have hν : 0 < ν n := hνpos n
  have hK : 0 ≤ bNorm a B := ENNReal.toReal_nonneg
  have hc4 : (S n).c⁻¹ ^ 2 = ν n ^ 4 := by
    rw [hyp.c_eq n]
    simp only [inv_pow, inv_inv]
    ring
  have hν4 : ν n ^ 4 ≤ ν n := by
    have h3' : ν n ^ 3 ≤ 1 := pow_le_one₀ hν.le hn1.le
    nlinarith
  obtain ⟨hBm, -, -, hBsupp, -⟩ := id hB
  have hBd : Measurable (fun t => Bd (B t)) := ((hBm 0 0).sub (hBm 2 2)).div_const 2
  have hBe : Measurable (fun t => Be (B t)) := ((hBm 0 2).add (hBm 2 0)).div_const 2
  have hBb : Measurable (fun t => Bbeta (B t)) := ((hBm 0 0).add (hBm 2 2)).div_const 2
  obtain ⟨hpH, hpHb, hpR⟩ := hyp.pair_meas n
  have hmA := measurable_ampIntegrand (S n) lam κ (ν n) μ B hBd hBe hBb hpH hpHb hpR
  have hmZ := measurable_zeroIntegrand lam ell μ B hBd hBe
  have hmE : Measurable (fun t => ampIntegrand (S n) lam κ (ν n) μ B t -
      zeroIntegrand lam ell μ B t) := by
    first
      | exact hmA.fun_sub hmZ
      | exact hmA.sub hmZ
      | fun_prop
  have hA : ((S n).toPkg lam κ (ν n) μ).aNu B =
      ∫ t in Ioc 0 (1.1 / ν n), ampIntegrand (S n) lam κ (ν n) μ B t := rfl
  have hZ := aZero_eq lam ell μ (ν n) B hBsupp
  have hae : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) (1.1 / ν n))),
      matNorm (B t) ≤ bNorm a B * (Real.exp (a * t) * t ^ (3 / 2 : ℝ)) :=
    ae_restrict_of_ae_restrict_of_subset Ioc_subset_Ioi_self (h3 a (ν n) B hB)
  have hmem : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) (1.1 / ν n))), t ∈ Ioc (0 : ℝ) (1.1 / ν n) :=
    ae_restrict_mem measurableSet_Ioc
  have hEb : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) (1.1 / ν n))),
      ‖ampIntegrand (S n) lam κ (ν n) μ B t - zeroIntegrand lam ell μ B t‖ ≤
        (3 * |CF| * |CG| + |CS| * ‖ell‖) * ν n * bNorm a B * majorant μ (lam.re / 3 - a) t := by
    filter_upwards [hae, hmem] with t hm ht
    obtain ⟨hGH, hGHb, hGR⟩ := hCG n hnG t ⟨ht.1.le, ht.2⟩
    rw [hc4] at hGH hGHb hGR
    exact pointwise_error (S n) lam κ ell μ a (ν n) t (bNorm a B) CF CS CG B hν hν4 ht.1 hK hm
      (hCF (ν n) hν t ⟨ht.1.le, ht.2⟩) (hCS (ν n) hν t ⟨ht.1.le, ht.2⟩) hGH hGHb hGR
  have hgb : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) (1.1 / ν n))),
      ‖zeroIntegrand lam ell μ B t‖ ≤ ‖ell‖ * bNorm a B * majorant μ (lam.re / 3 - a) t := by
    filter_upwards [hae, hmem] with t hm ht
    exact pointwise_zero lam ell μ a t (bNorm a B) B hlam ht.1 hK hm
  have hMajIoc : Integrable (majorant μ (lam.re / 3 - a))
      (volume.restrict (Ioc (0 : ℝ) (1.1 / ν n))) :=
    hMajInt.mono_set Ioc_subset_Ioi_self
  have hZI : Integrable (zeroIntegrand lam ell μ B) (volume.restrict (Ioc (0 : ℝ) (1.1 / ν n))) :=
    Integrable.mono' (hMajIoc.const_mul (‖ell‖ * bNorm a B)) hmZ.aestronglyMeasurable hgb
  have hEI : Integrable (fun t => ampIntegrand (S n) lam κ (ν n) μ B t -
      zeroIntegrand lam ell μ B t) (volume.restrict (Ioc (0 : ℝ) (1.1 / ν n))) :=
    Integrable.mono' (hMajIoc.const_mul ((3 * |CF| * |CG| + |CS| * ‖ell‖) * ν n * bNorm a B))
      hmE.aestronglyMeasurable hEb
  have hAI : Integrable (ampIntegrand (S n) lam κ (ν n) μ B)
      (volume.restrict (Ioc (0 : ℝ) (1.1 / ν n))) := by
    refine (hEI.add hZI).congr (Eventually.of_forall (fun t => ?_))
    simp
  rw [hA, hZ, ← integral_sub hAI hZI]
  calc ‖∫ t in Ioc 0 (1.1 / ν n),
        (ampIntegrand (S n) lam κ (ν n) μ B t - zeroIntegrand lam ell μ B t)‖
      ≤ ∫ t in Ioc 0 (1.1 / ν n),
        (3 * |CF| * |CG| + |CS| * ‖ell‖) * ν n * bNorm a B * majorant μ (lam.re / 3 - a) t :=
        norm_integral_le_of_norm_le (hMajIoc.const_mul _) hEb
    _ = (3 * |CF| * |CG| + |CS| * ‖ell‖) * ν n * bNorm a B *
        ∫ t in Ioc 0 (1.1 / ν n), majorant μ (lam.re / 3 - a) t := integral_const_mul _ _
    _ ≤ (3 * |CF| * |CG| + |CS| * ‖ell‖) * ν n * bNorm a B *
        ∫ t in Ioi 0, majorant μ (lam.re / 3 - a) t := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (mul_nonneg hC00 hν.le) hK)
        exact setIntegral_mono_set hMajInt
          (ae_restrict_of_forall_mem measurableSet_Ioi
            (fun t ht => majorant_nonneg μ _ t (le_of_lt (mem_Ioi.mp ht))))
          (LE.le.eventuallyLE Ioc_subset_Ioi_self)
    _ = (3 * |CF| * |CG| + |CS| * ‖ell‖) * (∫ t in Ioi (0 : ℝ), majorant μ (lam.re / 3 - a) t) *
        ν n * bNorm a B := by ring

end FlatAmp

end UnforcedLeray.Short.PartIIIb.ConcreteYF
