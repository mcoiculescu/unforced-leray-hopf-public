import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# Preliminaries for Bochner functions of time (INF14, Wave 1 block 1D)


(targets T1–T2); decisions D9 and D15 of `scoping/README.md` §3 (the Banach-valued FTC in time
is built once, here).

This file collects the analytic tools behind the Banach-valued FTC of `BochnerTime.Basic`:

* `AbsolutelyContinuousOnInterval.of_dist_le`: absolute continuity transfers along pointwise
  Lipschitz comparisons;
* `absolutelyContinuousOnInterval_primitive`: the primitive of a Bochner-integrable function is
  absolutely continuous (Mathlib has only the real-valued case);
* `integral_deriv_smul_primitive`: integration by parts of a test function against the primitive
  `t ↦ ∫ r in a..t, g r` (the product of a smooth function and an absolutely continuous one);
* `ae_eq_const_of_integral_deriv_smul_eq_zero`: the du Bois-Reymond lemma for Banach-valued
  functions on an interval (vanishing weak derivative implies an a.e. constant function).
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology intervalIntegral
open scoped ContDiff

namespace UnforcedLeray.BochnerTime

section AC

/-- **Comparison for absolute continuity.** If `dist (g x) (g y) ≤ K * dist (f x) (f y)` on
`uIcc a b` and `f` is absolutely continuous on `uIcc a b`, so is `g`. -/
theorem _root_.AbsolutelyContinuousOnInterval.of_dist_le {Y Z : Type*} [PseudoMetricSpace Y]
    [PseudoMetricSpace Z] {f : ℝ → Y} {g : ℝ → Z} {a b K : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hK : ∀ x ∈ uIcc a b, ∀ y ∈ uIcc a b, dist (g x) (g y) ≤ K * dist (f x) (f y)) :
    AbsolutelyContinuousOnInterval g a b := by
  unfold AbsolutelyContinuousOnInterval at hf ⊢
  refine squeeze_zero' (Eventually.of_forall fun E => Finset.sum_nonneg fun _ _ => dist_nonneg)
    ?_ (by simpa using hf.const_mul K)
  rw [eventually_inf_principal]
  filter_upwards with E hE
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  exact hK _ (hE.1 i hi).1 _ (hE.1 i hi).2

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- **Absolute continuity of a Bochner primitive.** If `g` is interval integrable on `a..b` and
`c ∈ uIcc a b`, then `x ↦ ∫ r in c..x, g r` is absolutely continuous on `uIcc a b`. -/
theorem absolutelyContinuousOnInterval_primitive {g : ℝ → X} {a b c : ℝ}
    (hg : IntervalIntegrable g volume a b) (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun x => ∫ r in c..x, g r) a b := by
  have hV := (hg.norm).absolutelyContinuousOnInterval_intervalIntegral hc
  refine hV.of_dist_le (K := 1) fun x hx y hy => ?_
  have hcx : IntervalIntegrable g volume c x := hg.mono_set (uIcc_subset_uIcc hc hx)
  have hcy : IntervalIntegrable g volume c y := hg.mono_set (uIcc_subset_uIcc hc hy)
  rw [one_mul, dist_eq_norm, Real.dist_eq, integral_interval_sub_left hcx hcy,
    integral_interval_sub_left hcx.norm hcy.norm]
  exact norm_integral_le_abs_integral_norm

end AC

section Tests

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A continuous compactly supported scalar function with `tsupport φ ⊆ Ioo a b`, multiplied by a
function integrable on `Ioo a b`, is integrable on `ℝ`. -/
theorem integrable_smul_of_tsupport_subset {a b : ℝ} {φ : ℝ → ℝ} {u : ℝ → X}
    (hφc : Continuous φ) (hφs : HasCompactSupport φ) (hφt : tsupport φ ⊆ Ioo a b)
    (hu : IntegrableOn u (Ioo a b)) : Integrable (fun t => φ t • u t) := by
  obtain ⟨C, hC⟩ := hφs.exists_bound_of_continuous hφc
  have h1 : IntegrableOn (fun t => φ t • u t) (Ioo a b) :=
    Integrable.bdd_smul hu C hφc.aestronglyMeasurable.restrict (Eventually.of_forall hC)
  refine (integrableOn_iff_integrable_of_support_subset ?_).1 h1
  intro t ht
  apply hφt
  apply subset_tsupport
  intro h0
  apply ht
  simp [h0]

/-- For `tsupport φ ⊆ Ioo a b`, the integral of `φ • u` over `ℝ` is the interval integral over
`a..b`. -/
theorem integral_smul_eq_intervalIntegral {a b : ℝ} {φ : ℝ → ℝ} {u : ℝ → X}
    (hφt : tsupport φ ⊆ Ioo a b) : ∫ t, φ t • u t = ∫ t in a..b, φ t • u t := by
  symm
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro t ht
  have : t ∈ tsupport φ := subset_tsupport _ fun h0 => ht (by simp [h0])
  exact Ioo_subset_Ioc_self (hφt this)

/-- A smooth function whose topological support lies in `Ioo a b` vanishes outside `Ioo a b`. -/
theorem eq_zero_of_tsupport_subset {a b : ℝ} {φ : ℝ → ℝ} (hφt : tsupport φ ⊆ Ioo a b) {t : ℝ}
    (ht : t ∉ Ioo a b) : φ t = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => ht (hφt h)

/-- The derivative of a function with `tsupport φ ⊆ Ioo a b` has topological support in
`Ioo a b`. -/
theorem tsupport_deriv_subset_Ioo {a b : ℝ} {φ : ℝ → ℝ} (hφt : tsupport φ ⊆ Ioo a b) :
    tsupport (deriv φ) ⊆ Ioo a b :=
  (tsupport_deriv_subset).trans hφt

/-- **Integration by parts against a primitive.** For a smooth `φ` with `tsupport φ ⊆ Ioo a b`
and `g` integrable on `Ioo a b`,
`∫ deriv φ • (∫_a^t g) dt = -∫ φ • g`. -/
theorem integral_deriv_smul_primitive [CompleteSpace X] {a b : ℝ} {φ : ℝ → ℝ} {g : ℝ → X}
    (hφ : ContDiff ℝ ∞ φ) (hφt : tsupport φ ⊆ Ioo a b) (hg : IntegrableOn g (Ioo a b)) :
    ∫ t, deriv φ t • (∫ r in a..t, g r) = -∫ t, φ t • g t := by
  rcases le_or_gt b a with hba | hab
  · have hφ0 : ∀ t, φ t = 0 := fun t => eq_zero_of_tsupport_subset hφt (by
      simp only [mem_Ioo, not_and, not_lt]; intro h; linarith)
    have hd0 : ∀ t, deriv φ t = 0 := fun t => eq_zero_of_tsupport_subset
      (tsupport_deriv_subset_Ioo hφt) (by simp only [mem_Ioo, not_and, not_lt]; intro h; linarith)
    simp [hφ0, hd0]
  have hgI : IntervalIntegrable g volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 hg
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hφ'c : Continuous (deriv φ) := hφ.continuous_deriv (by simp)
  have ha : a ∈ uIcc a b := left_mem_uIcc
  set v : ℝ → X := fun x => ∫ r in a..x, g r with hv_def
  have hvAC : AbsolutelyContinuousOnInterval v a b :=
    absolutelyContinuousOnInterval_primitive hgI ha
  have hvc : ContinuousOn v (uIcc a b) := hvAC.continuousOn
  have hφAC : AbsolutelyContinuousOnInterval φ a b :=
    (hφ.contDiffOn.of_le (by simp)).absolutelyContinuousOnInterval
  have hwAC : AbsolutelyContinuousOnInterval (fun x => φ x • v x) a b := hφAC.fun_smul hvAC
  set k : ℝ → X := fun t => deriv φ t • v t + φ t • g t with hk_def
  have hk1 : IntervalIntegrable (fun t => deriv φ t • v t) volume a b :=
    (hφ'c.continuousOn.smul hvc).intervalIntegrable
  have hk2 : IntervalIntegrable (fun t => φ t • g t) volume a b :=
    hgI.continuousOn_smul hφd.continuous.continuousOn
  have hk : IntervalIntegrable k volume a b := hk1.add hk2
  have hKAC : AbsolutelyContinuousOnInterval (fun x => ∫ r in a..x, k r) a b :=
    absolutelyContinuousOnInterval_primitive hk ha
  have hGAC : AbsolutelyContinuousOnInterval
      (fun x => φ x • v x - ∫ r in a..x, k r) a b := hwAC.sub hKAC
  have hG0 : ∀ᵐ x, x ∈ uIcc a b →
      HasDerivAt (fun x => φ x • v x - ∫ r in a..x, k r) 0 x := by
    filter_upwards [hgI.ae_hasDerivAt_integral, hk.ae_hasDerivAt_integral] with x hx1 hx2 hx
    have hv' : HasDerivAt v (g x) x := hx1 hx a ha
    have hK' : HasDerivAt (fun x => ∫ r in a..x, k r) (k x) x := hx2 hx a ha
    have hw' : HasDerivAt (fun y => φ y • v y) (φ x • g x + deriv φ x • v x) x :=
      (hφd x).hasDerivAt.smul hv'
    exact (hw'.sub hK').congr_deriv (by simp only [hk_def]; abel)
  obtain ⟨C, hC⟩ := hGAC.const_of_ae_hasDerivAt_zero hG0
  have hCa := hC a ha
  have hCb := hC b right_mem_uIcc
  have hφa : φ a = 0 := eq_zero_of_tsupport_subset hφt (by simp)
  have hφb : φ b = 0 := eq_zero_of_tsupport_subset hφt (by simp)
  simp only [hφa, hφb, zero_smul, integral_same, sub_zero, zero_sub] at hCa hCb
  have hkb : ∫ r in a..b, k r = 0 := by
    have := hCb.trans hCa.symm
    simpa using this
  rw [hk_def, intervalIntegral.integral_add hk1 hk2] at hkb
  rw [integral_smul_eq_intervalIntegral (tsupport_deriv_subset_Ioo hφt),
    integral_smul_eq_intervalIntegral hφt]
  exact eq_neg_of_add_eq_zero_left hkb

/-- **du Bois-Reymond lemma (Banach-valued, on an interval).** A function `w` integrable on
`Ioo a b` whose distributional derivative vanishes on `Ioo a b`, i.e. `∫ φ' • w = 0` for every
smooth `φ` compactly supported in `Ioo a b`, is a.e. equal on `Ioo a b` to a constant. -/
theorem ae_eq_const_of_integral_deriv_smul_eq_zero [CompleteSpace X] {a b : ℝ} (hab : a < b)
    {w : ℝ → X} (hw : IntegrableOn w (Ioo a b))
    (h : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo a b →
      ∫ t, deriv φ t • w t = 0) :
    ∃ c : X, ∀ᵐ t ∂(volume.restrict (Ioo a b)), w t = c := by
  set m : ℝ := (a + b) / 2 with hm
  let f0 : ContDiffBump m := ⟨(b - a) / 8, (b - a) / 4, by linarith, by linarith⟩
  set ψ : ℝ → ℝ := f0.normed volume with hψ_def
  have hψc : ContDiff ℝ ∞ ψ := f0.contDiff_normed
  have hψs : HasCompactSupport ψ := f0.hasCompactSupport_normed
  have hψtsupp : tsupport ψ = Metric.closedBall m ((b - a) / 4) := f0.tsupport_normed_eq
  have hψt : tsupport ψ ⊆ Ioo a b := by
    rw [hψtsupp]
    intro x hx
    rw [Metric.mem_closedBall, Real.dist_eq] at hx
    have := abs_le.1 hx
    constructor <;> linarith [this.1, this.2]
  have hψi : ∫ t, ψ t = 1 := f0.integral_normed
  set c : X := ∫ t, ψ t • w t with hc_def
  refine ⟨c, ?_⟩
  have key : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo a b →
      ∫ t, φ t • (w t - c) = 0 := by
    intro φ hφ hφs hφt
    set I : ℝ := ∫ t, φ t with hI_def
    set g : ℝ → ℝ := fun t => φ t - I * ψ t with hg_def
    have hgc : ContDiff ℝ ∞ g := hφ.sub (contDiff_const.mul hψc)
    have hgcont : Continuous g := hgc.continuous
    set χ : ℝ → ℝ := fun x => ∫ s in a..x, g s with hχ_def
    have hχd : ∀ x, HasDerivAt χ (g x) x := fun x =>
      (hgcont.integral_hasStrictDerivAt a x).hasDerivAt
    have hχderiv : deriv χ = g := funext fun x => (hχd x).deriv
    have hχc : ContDiff ℝ ∞ χ :=
      contDiff_infty_iff_deriv.2 ⟨fun x => (hχd x).differentiableAt, hχderiv ▸ hgc⟩
    set K : Set ℝ := tsupport φ ∪ tsupport ψ with hK_def
    have hKc : IsCompact K := hφs.isCompact.union hψs.isCompact
    have hKI : K ⊆ Ioo a b := union_subset hφt hψt
    have hmK : m ∈ K := Or.inr (by
      rw [hψtsupp]; exact Metric.mem_closedBall_self (by linarith))
    have hKne : K.Nonempty := ⟨m, hmK⟩
    set α : ℝ := sInf K with hα_def
    set β : ℝ := sSup K with hβ_def
    have hαK : α ∈ K := hKc.sInf_mem hKne
    have hβK : β ∈ K := hKc.sSup_mem hKne
    have hKαβ : K ⊆ Icc α β := fun x hx => ⟨csInf_le hKc.bddBelow hx, le_csSup hKc.bddAbove hx⟩
    have haα : a < α := (hKI hαK).1
    have hβb : β < b := (hKI hβK).2
    have hg0 : ∀ x, x ∉ K → g x = 0 := by
      intro x hx
      simp only [hK_def, mem_union, not_or] at hx
      simp [hg_def, image_eq_zero_of_notMem_tsupport hx.1, image_eq_zero_of_notMem_tsupport hx.2]
    have hφint : Integrable φ := hφ.continuous.integrable_of_hasCompactSupport hφs
    have hψint : Integrable ψ := hψc.continuous.integrable_of_hasCompactSupport hψs
    have hgint : ∫ t, g t = 0 := by
      simp only [hg_def]
      rw [integral_sub hφint (hψint.const_mul I), MeasureTheory.integral_const_mul, hψi, mul_one, sub_self]
    have hχ0 : ∀ x, x ∉ Icc α β → χ x = 0 := by
      intro x hx
      simp only [mem_Icc, not_and_or, not_le] at hx
      rcases hx with hx | hx
      · have hEq : EqOn g (fun _ => (0 : ℝ)) (uIcc a x) := by
          intro y hy
          refine hg0 y fun hyK => ?_
          have h1 := (hKαβ hyK).1
          have h2 : y ≤ max a x := (mem_uIcc.1 hy).elim (fun h => h.2.trans (le_max_right _ _))
            (fun h => h.2.trans (le_max_left _ _))
          have h3 : max a x < α := max_lt haα hx
          linarith
        simp only [hχ_def]
        rw [intervalIntegral.integral_congr hEq]
        simp
      · simp only [hχ_def]
        rw [intervalIntegral.integral_eq_integral_of_support_subset, hgint]
        intro y hy
        have hyK : y ∈ K := by
          by_contra hyK
          exact hy (hg0 y hyK)
        exact ⟨(hKI hyK).1, ((hKαβ hyK).2.trans hx.le)⟩
    have hsupp : Function.support χ ⊆ Icc α β := fun x hx => by
      by_contra h'
      exact hx (hχ0 x h')
    have hχs : HasCompactSupport χ := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
    have hχt : tsupport χ ⊆ Ioo a b :=
      (closure_minimal hsupp isClosed_Icc).trans (Icc_subset_Ioo haα hβb)
    have h1 := h χ hχc hχs hχt
    rw [hχderiv] at h1
    have hφw : Integrable (fun t => φ t • w t) :=
      integrable_smul_of_tsupport_subset hφ.continuous hφs hφt hw
    have hψw : Integrable (fun t => ψ t • w t) :=
      integrable_smul_of_tsupport_subset hψc.continuous hψs hψt hw
    have h2 : ∫ t, g t • w t = (∫ t, φ t • w t) - I • c := by
      have : (fun t => g t • w t) = fun t => φ t • w t - I • (ψ t • w t) := by
        funext t
        simp only [hg_def, sub_smul, mul_smul]
      have hψw' : Integrable (fun t => I • (ψ t • w t)) := hψw.smul I
      rw [this, integral_sub hφw hψw', MeasureTheory.integral_smul]
    have h3 : ∫ t, φ t • (w t - c) = (∫ t, φ t • w t) - I • c := by
      simp only [smul_sub]
      rw [integral_sub hφw (hφint.smul_const c), _root_.integral_smul_const]
    rw [h3, ← h2, h1]
  have hloc : LocallyIntegrableOn (fun t => w t - c) (Ioo a b) :=
    (hw.sub ((continuous_const (y := c)).integrableOn_Icc.mono_set Ioo_subset_Icc_self)).locallyIntegrableOn
  have hae := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
    (fun φ hφ hφs hφt => key φ hφ hφs hφt)
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [hae] with t ht ht'
  exact sub_eq_zero.1 (ht ht')

end Tests

end UnforcedLeray.BochnerTime
