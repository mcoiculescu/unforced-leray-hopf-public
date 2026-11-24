import UnforcedLeray.Analysis.Rayleigh.RealSpeed.CriticalPoint
import UnforcedLeray.Analysis.Rayleigh.LimitEquation
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

/-!
# Critical traces from an almost-everywhere equation

A differentiable scalar vanishing at a point cannot multiply an L² function
into a continuous function which is nonzero at that point. The proof integrates
on shrinking intervals and uses the actual finite L² integral; no pointwise
value of the L² representative at the critical point is used.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace UnforcedLeray.Rayleigh.RealSpeed

/-- A genuine weak critical-trace lemma. The product identity is needed only
almost everywhere on an arbitrary neighborhood of the critical point. -/
theorem zero_of_ae_smul_memLp_two {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℝ → ℝ} {g b : ℝ → E} {t₀ : ℝ} {s : Set ℝ}
    (ha : DifferentiableAt ℝ a t₀) (ha₀ : a t₀ = 0)
    (hg : MemLp g 2 volume) (hb : ContinuousAt b t₀) (hs : s ∈ 𝓝 t₀)
    (heq : ∀ᵐ t ∂volume.restrict s, a t • g t = b t) : b t₀ = 0 := by
  by_contra hb₀
  let δ : ℝ := ‖b t₀‖ / 2
  have hδ : 0 < δ := half_pos (norm_pos_iff.mpr hb₀)
  have hδb : δ < ‖b t₀‖ := half_lt_self (norm_pos_iff.mpr hb₀)
  obtain ⟨C, hC, hO⟩ := ha.isBigO_sub.exists_pos
  have haevent : ∀ᶠ t in 𝓝 t₀, ‖a t‖ ≤ C * ‖t - t₀‖ := by
    simpa only [ha₀, sub_zero] using hO.bound
  have hbevent : ∀ᶠ t in 𝓝 t₀, δ < ‖b t‖ :=
    hb.norm (Ioi_mem_nhds hδb)
  obtain ⟨r, hr, hnear⟩ := Metric.eventually_nhds_iff.mp
    (haevent.and (hbevent.and hs))
  have hgi : Integrable (fun t => ‖g t‖ ^ 2) :=
    hg.integrable_norm_pow (by norm_num)
  let energy : ℝ := ∫ t, ‖g t‖ ^ 2
  have henergy : 0 ≤ energy := integral_nonneg (fun _ => sq_nonneg _)
  obtain ⟨q, hq, hqsmall⟩ := exists_pos_mul_lt (sq_pos_of_pos hδ) (C ^ 2 * energy)
  let ε : ℝ := min (r / 2) q
  have hε : 0 < ε := lt_min (half_pos hr) hq
  have hεr : ε < r := (min_le_left _ _).trans_lt (half_lt_self hr)
  have hεq : ε ≤ q := min_le_right _ _
  have hdist {t : ℝ} (ht : t ∈ Ioc t₀ (t₀ + ε)) : dist t t₀ < r := by
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr ht.1)]
    linarith [ht.2]
  have his : Ioc t₀ (t₀ + ε) ⊆ s := fun t ht => (hnear (hdist ht)).2.2
  have heqI := ae_restrict_of_ae_restrict_of_subset his heq
  have hpoint : ∀ᵐ t ∂volume.restrict (Ioc t₀ (t₀ + ε)),
      δ ^ 2 ≤ (C ^ 2 * ε ^ 2) * ‖g t‖ ^ 2 := by
    filter_upwards [heqI, ae_restrict_mem measurableSet_Ioc] with t he ht
    have hanear := (hnear (hdist ht)).1
    have hbnear := (hnear (hdist ht)).2.1.le
    have hnormdist : ‖t - t₀‖ ≤ ε := by
      rw [Real.norm_eq_abs, abs_of_pos (sub_pos.mpr ht.1)]
      linarith [ht.2]
    have habound : ‖a t‖ ≤ C * ε :=
      hanear.trans (mul_le_mul_of_nonneg_left hnormdist hC.le)
    have hbnorm : ‖b t‖ = ‖a t‖ * ‖g t‖ := by rw [← he, norm_smul]
    have hlow : δ ≤ C * ε * ‖g t‖ := by
      calc
        δ ≤ ‖b t‖ := hbnear
        _ = ‖a t‖ * ‖g t‖ := hbnorm
        _ ≤ C * ε * ‖g t‖ := mul_le_mul_of_nonneg_right habound (norm_nonneg _)
    have hsq := (sq_le_sq₀ hδ.le (by positivity : 0 ≤ C * ε * ‖g t‖)).mpr hlow
    simpa only [mul_pow, mul_assoc] using hsq
  have hineq := integral_mono_ae
    (integrableOn_const (μ := volume) (s := Ioc t₀ (t₀ + ε))
      (C := δ ^ 2) (by simp))
    ((hgi.const_mul (C ^ 2 * ε ^ 2)).integrableOn (s := Ioc t₀ (t₀ + ε))) hpoint
  rw [setIntegral_const, Real.volume_real_Ioc_of_le (by linarith : t₀ ≤ t₀ + ε),
    integral_const_mul] at hineq
  simp only [add_sub_cancel_left, smul_eq_mul] at hineq
  have hmass : (∫ t in Ioc t₀ (t₀ + ε), ‖g t‖ ^ 2) ≤ energy :=
    setIntegral_le_integral hgi (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
  have hupper : ε * δ ^ 2 ≤ (C ^ 2 * ε ^ 2) * energy :=
    hineq.trans (mul_le_mul_of_nonneg_left hmass (by positivity))
  have hsmall : C ^ 2 * energy * ε < δ ^ 2 :=
    (mul_le_mul_of_nonneg_left hεq (mul_nonneg (sq_nonneg C) henergy)).trans_lt hqsmall
  have hstrict := mul_lt_mul_of_pos_left hsmall hε
  nlinarith only [hstrict, hupper]

/-- Global almost-everywhere equality is a special case of the local theorem. -/
theorem zero_of_ae_smul_memLp_two_global {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℝ → ℝ} {g b : ℝ → E} {t₀ : ℝ}
    (ha : DifferentiableAt ℝ a t₀) (ha₀ : a t₀ = 0)
    (hg : MemLp g 2 volume) (hb : ContinuousAt b t₀)
    (heq : ∀ᵐ t ∂volume, a t • g t = b t) : b t₀ = 0 :=
  zero_of_ae_smul_memLp_two ha ha₀ hg hb Filter.univ_mem
    (by simpa only [Measure.restrict_univ] using heq)

/-- Complex multiplication by a real scalar has the same weak critical trace. -/
theorem zero_of_ae_real_mul_memLp_two {a : ℝ → ℝ} {g b : ℝ → ℂ}
    {t₀ : ℝ} {s : Set ℝ} (ha : DifferentiableAt ℝ a t₀) (ha₀ : a t₀ = 0)
    (hg : MemLp g 2 volume) (hb : ContinuousAt b t₀) (hs : s ∈ 𝓝 t₀)
    (heq : ∀ᵐ t ∂volume.restrict s, (a t : ℂ) * g t = b t) : b t₀ = 0 := by
  apply zero_of_ae_smul_memLp_two ha ha₀ hg hb hs
  filter_upwards [heq] with t ht
  simpa only [Complex.real_smul] using ht

open Sturm

/-- The actual Gaussian equation forces a zero trace at every nonneutral real
critical point even when its second-derivative residual exists only in L². -/
theorem complex_weak_value_zero_at_critical {F k : ℝ → ℂ} {a c : ℝ}
    (hΩ : neutralOmega a = c) (hc : c ≠ gaussianCriticalSpeed)
    (hF : ContinuousAt F a) (hk : MemLp k 2 volume)
    (heq : ∀ᵐ t ∂volume,
      ((neutralOmega t : ℂ) - (c : ℂ)) * k t -
        (gaussianRayleighCoefficient t : ℂ) * F t = 0) : F a = 0 := by
  have ha : DifferentiableAt ℝ (fun t => neutralOmega t - c) a :=
    (hasDerivAt_neutralOmega a).differentiableAt.sub_const c
  have ha₀ : neutralOmega a - c = 0 := by rw [hΩ]; ring
  have hprod : ContinuousAt (fun t => (gaussianRayleighCoefficient t : ℂ) * F t) a :=
    (Complex.continuous_ofReal.comp continuous_gaussianRayleighCoefficient).continuousAt.mul hF
  have hz : (gaussianRayleighCoefficient a : ℂ) * F a = 0 := by
    apply zero_of_ae_real_mul_memLp_two ha ha₀ hk hprod Filter.univ_mem
    rw [Measure.restrict_univ]
    filter_upwards [heq] with t ht
    simpa only [Complex.ofReal_sub] using sub_eq_zero.mp ht
  apply (mul_eq_zero.mp hz).resolve_left
  exact_mod_cast coefficient_ne_zero_at_critical hΩ hc

/-- Direct application to the continuous representative of the actual L²
whole-line weak limit. No value of the arbitrary L² representative at a is used. -/
theorem continuous_representative_zero_at_critical (u k : ComplexL2)
    {F : ℝ → ℂ} {a c : ℝ} (hΩ : neutralOmega a = c)
    (hc : c ≠ gaussianCriticalSpeed) (hF : ContinuousAt F a)
    (hrep : F =ᵐ[volume] (u : ℝ → ℂ))
    (heq : undividedResidual (c : ℂ) (u : ℝ → ℂ) (k : ℝ → ℂ) =ᵐ[volume] 0) :
    F a = 0 := by
  apply complex_weak_value_zero_at_critical hΩ hc hF (Lp.memLp k)
  filter_upwards [heq, hrep] with t ht hFt
  simpa only [undividedResidual, Pi.zero_apply, hFt] using ht

end UnforcedLeray.Rayleigh.RealSpeed
