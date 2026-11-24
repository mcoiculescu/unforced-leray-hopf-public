import UnforcedLeray.Lib.Semigroups.ExpSemigroup
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Laplace-transform resolvents of exponentially bounded semigroups (INF07 T7.2)


§5, target **T7.2** (Wave 1, block 1G), bypass **BP4** ("resolvents defined as Laplace transforms
of the explicit semigroups, plus a core lemma"; external input `STD:laplace-resolvent`). Uses:
blueprint units B0223, B0224, B0418-B0421, B0470, B0486, B0553, B0576, B0775, B0779, B0841,
B1000 (e.g. tex 7304-8058, 8873-9187).

For `Re μ > ω` the Laplace transform
`R(μ) x = ∫_{(0,∞)} e^{-μt} T(t) x dt`
is a bounded operator (`laplace`). Outside the half-plane `laplace` is the junk value `0`; every
theorem below carries the hypothesis `S.ω < μ.re`.

Main results:
* `laplace_apply`, `norm_laplace_le` (`‖R(μ)‖ ≤ M / (Re μ - ω)`);
* `laplace_leftInverse'`/`laplace_leftInverse`: if `t ↦ T(t)x` has derivative `T(t)y`, then
  `R(μ)(μx - y) = x` (the "core lemma" of BP4: no generator is defined);
* `T_comp_laplace`: `T(t) R(μ) = R(μ) T(t)`;
* `T_laplace_apply`: `T(t) R(μ) z = e^{μt} (R(μ) z - ∫_0^t e^{-μr} T(r) z dr)`;
* `hasDerivAt_T_laplace`: `t ↦ T(t) R(μ) z` has derivative `T(t)(μ R(μ) z - z)` at `t > 0`;
* `laplace_sub_laplace`: the resolvent identity `R(μ) - R(μ') = (μ' - μ) R(μ) R(μ')`;
* `continuousOn_laplace`, `hasDerivAt_laplace` (`R'(μ) = -R(μ)²`), `differentiableOn_laplace`;
* `tendsto_norm_T_comp_laplace_sub`: `‖T(t) R(μ) - R(μ)‖ → 0` as `t → 0⁺` (operator norm).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace UnforcedLeray.Infra

namespace ExpSemigroup

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] (S : ExpSemigroup X)

/-- The Laplace integrand `e^{-μt} T(t) x`. -/
def lapInt (μ : ℂ) (x : X) (t : ℝ) : X := Complex.exp (-(μ * t)) • S.T t x

theorem lapInt_def (μ : ℂ) (x : X) (t : ℝ) :
    S.lapInt μ x t = Complex.exp (-(μ * t)) • S.T t x := rfl

theorem norm_cexp_neg_mul (μ : ℂ) (t : ℝ) :
    ‖Complex.exp (-(μ * t))‖ = Real.exp (-(μ.re * t)) := by
  rw [Complex.norm_exp]
  simp

theorem norm_lapInt_le (μ : ℂ) (x : X) {t : ℝ} (ht : 0 ≤ t) :
    ‖S.lapInt μ x t‖ ≤ S.M * ‖x‖ * Real.exp (-(μ.re - S.ω) * t) := by
  rw [lapInt_def, norm_smul, norm_cexp_neg_mul]
  calc Real.exp (-(μ.re * t)) * ‖S.T t x‖
      ≤ Real.exp (-(μ.re * t)) * (S.M * Real.exp (S.ω * t) * ‖x‖) :=
        mul_le_mul_of_nonneg_left (S.norm_T_apply_le ht x) (Real.exp_pos _).le
    _ = S.M * ‖x‖ * (Real.exp (-(μ.re * t)) * Real.exp (S.ω * t)) := by ring
    _ = S.M * ‖x‖ * Real.exp (-(μ.re - S.ω) * t) := by
        rw [← Real.exp_add]
        ring_nf

/-- For `ω < Re μ`, the integrand is bounded by `M ‖x‖` on `[0, ∞)`. -/
theorem norm_lapInt_le_const {μ : ℂ} (hμ : S.ω < μ.re) (x : X) {t : ℝ} (ht : 0 ≤ t) :
    ‖S.lapInt μ x t‖ ≤ S.M * ‖x‖ := by
  refine (S.norm_lapInt_le μ x ht).trans ?_
  have h1 : Real.exp (-(μ.re - S.ω) * t) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  have h2 : 0 ≤ S.M * ‖x‖ := mul_nonneg S.M_nonneg (norm_nonneg _)
  nlinarith

theorem continuous_cexp_neg_mul (μ : ℂ) : Continuous fun t : ℝ => Complex.exp (-(μ * t)) :=
  Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).neg)

theorem continuousOn_lapInt (μ : ℂ) (x : X) : ContinuousOn (S.lapInt μ x) (Ici 0) :=
  (continuous_cexp_neg_mul μ).continuousOn.smul (S.T_cont x)

theorem hasDerivAt_cexp_mul (μ : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (μ * t)) (μ * Complex.exp (μ * t)) t := by
  have h : HasDerivAt (fun t : ℝ => μ * (t : ℂ)) μ t := by
    simpa using ((hasDerivAt_id t).ofReal_comp).const_mul μ
  simpa [mul_comm] using h.cexp

theorem hasDerivAt_cexp_neg_mul (μ : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (-(μ * t))) (-μ * Complex.exp (-(μ * t))) t := by
  simpa [neg_mul] using hasDerivAt_cexp_mul (-μ) t

variable [CompleteSpace X]

theorem integrableOn_lapInt {μ : ℂ} (hμ : S.ω < μ.re) (x : X) :
    IntegrableOn (S.lapInt μ x) (Ioi 0) := by
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi 0 (sub_pos.2 hμ)).const_mul (S.M * ‖x‖))
    (((S.continuousOn_lapInt μ x).mono Ioi_subset_Ici_self).aestronglyMeasurable
      measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact S.norm_lapInt_le μ x (le_of_lt ht)

theorem integral_exp_bound {b : ℝ} (hb : 0 < b) (c : ℝ) :
    ∫ t in Ioi (0 : ℝ), c * Real.exp (-b * t) = c / b := by
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) 0]
  simp
  ring

theorem norm_integral_lapInt_le {μ : ℂ} (hμ : S.ω < μ.re) (x : X) :
    ‖∫ t in Ioi 0, S.lapInt μ x t‖ ≤ S.M / (μ.re - S.ω) * ‖x‖ := by
  have hb : 0 < μ.re - S.ω := sub_pos.2 hμ
  refine (norm_integral_le_of_norm_le
    ((exp_neg_integrableOn_Ioi 0 hb).const_mul (S.M * ‖x‖)) ?_).trans ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact S.norm_lapInt_le μ x (le_of_lt ht)
  · rw [integral_exp_bound hb]
    rw [div_mul_eq_mul_div, mul_comm (S.M) ‖x‖, mul_comm ‖x‖]

/-- The Laplace transform as a linear map, for `ω < Re μ`. -/
def laplaceLM (μ : ℂ) (hμ : S.ω < μ.re) : X →ₗ[ℂ] X where
  toFun x := ∫ t in Ioi 0, S.lapInt μ x t
  map_add' x y := by
    have h : ∀ t, S.lapInt μ (x + y) t = S.lapInt μ x t + S.lapInt μ y t := fun t => by
      simp [lapInt_def, smul_add]
    simp_rw [h]
    exact integral_add (S.integrableOn_lapInt hμ x) (S.integrableOn_lapInt hμ y)
  map_smul' c x := by
    have h : ∀ t, S.lapInt μ (c • x) t = c • S.lapInt μ x t := fun t => by
      simp [lapInt_def, smul_comm c]
    simp_rw [h]
    exact integral_smul c _

/-- **T7.2.** The Laplace transform `R(μ) x = ∫_{(0,∞)} e^{-μt} T(t) x dt` for `ω < Re μ`
(junk value `0` otherwise). -/
def laplace (μ : ℂ) : X →L[ℂ] X :=
  if hμ : S.ω < μ.re then
    (S.laplaceLM μ hμ).mkContinuous (S.M / (μ.re - S.ω)) (S.norm_integral_lapInt_le hμ)
  else 0

theorem laplace_apply {μ : ℂ} (hμ : S.ω < μ.re) (x : X) :
    S.laplace μ x = ∫ t : ℝ in Ioi 0, Complex.exp (-(μ * t)) • S.T t x := by
  rw [laplace, dif_pos hμ]
  rfl

theorem laplace_apply' {μ : ℂ} (hμ : S.ω < μ.re) (x : X) :
    S.laplace μ x = ∫ t in Ioi 0, S.lapInt μ x t :=
  S.laplace_apply hμ x

/-- **T7.2** `‖R(μ)‖ ≤ M / (Re μ - ω)`. -/
theorem norm_laplace_le {μ : ℂ} (hμ : S.ω < μ.re) : ‖S.laplace μ‖ ≤ S.M / (μ.re - S.ω) := by
  rw [laplace, dif_pos hμ]
  exact LinearMap.mkContinuous_norm_le _ (div_nonneg S.M_nonneg (sub_pos.2 hμ).le) _

/-- **T7.2, core lemma** (BP4). If `t ↦ T(t) x` has derivative `T(t) y` at every `t > 0`, then
`R(μ)(μ x - y) = x`. -/
theorem laplace_leftInverse' {μ : ℂ} (hμ : S.ω < μ.re) {x y : X}
    (hxy : ∀ t, 0 < t → HasDerivAt (fun t => S.T t x) (S.T t y) t) :
    S.laplace μ (μ • x - y) = x := by
  set f : ℝ → X := S.lapInt μ x with hf
  set f' : ℝ → X := fun t => S.lapInt μ y t + (-μ) • S.lapInt μ x t with hf'
  have hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt f (f' t) t := by
    intro t ht
    have h := (hasDerivAt_cexp_neg_mul μ t).smul (hxy t ht)
    refine h.congr_deriv ?_
    simp only [hf', lapInt_def, smul_smul]
  have hint : IntegrableOn f' (Ioi 0) :=
    (S.integrableOn_lapInt hμ y).add ((S.integrableOn_lapInt hμ x).smul (-μ))
  have hlim : Tendsto f atTop (𝓝 0) := by
    have hb : 0 < μ.re - S.ω := sub_pos.2 hμ
    have h0 : Tendsto (fun t : ℝ => S.M * ‖x‖ * Real.exp (-(μ.re - S.ω) * t)) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_atBot.comp
        ((tendsto_id (α := ℝ)).const_mul_atTop_of_neg (neg_lt_zero.2 hb))).const_mul (S.M * ‖x‖)
      simpa [Function.comp_def] using this
    refine squeeze_zero_norm' ?_ h0
    filter_upwards [eventually_ge_atTop 0] with t ht
    exact S.norm_lapInt_le μ x ht
  have hcont : ContinuousWithinAt f (Ici 0) 0 := S.continuousOn_lapInt μ x 0 (mem_Ici.2 le_rfl)
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  have hf0 : f 0 = x := by simp [hf, lapInt_def, S.T_zero_apply]
  rw [hf0, zero_sub] at hftc
  rw [S.laplace_apply' hμ]
  have hpt : ∀ t, S.lapInt μ (μ • x - y) t = -f' t := fun t => by
    simp only [hf', lapInt_def, map_sub, map_smul]
    rw [smul_sub, smul_comm (Complex.exp _) μ, neg_smul, neg_add, neg_neg]
    abel
  simp_rw [hpt]
  rw [integral_neg, hftc, neg_neg]

/-- **T7.2, core lemma** in the form of the scoping note (one-sided derivative on `[0, ∞)`). -/
theorem laplace_leftInverse {μ : ℂ} {x y : X}
    (hxy : ∀ t, 0 ≤ t → HasDerivWithinAt (fun t => S.T t x) (S.T t y) (Set.Ici 0) t)
    (hμ : S.ω < μ.re) : S.laplace μ (μ • x - y) = x :=
  S.laplace_leftInverse' hμ fun t ht => (hxy t ht.le).hasDerivAt (Ici_mem_nhds ht)

/-- The semigroup commutes with its Laplace transform. -/
theorem T_comp_laplace {μ : ℂ} (hμ : S.ω < μ.re) {t : ℝ} (ht : 0 ≤ t) :
    S.T t ∘L S.laplace μ = S.laplace μ ∘L S.T t := by
  ext z
  simp only [ContinuousLinearMap.comp_apply]
  rw [S.laplace_apply' hμ, S.laplace_apply' hμ,
    ← (S.T t).integral_comp_comm (S.integrableOn_lapInt hμ z)]
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  simp only [lapInt_def, map_smul]
  rw [S.T_comm_apply ht (le_of_lt hs)]

theorem integrableOn_lapInt_Ioc {μ : ℂ} (x : X) (a b : ℝ) (ha : 0 ≤ a) :
    IntegrableOn (S.lapInt μ x) (Ioc a b) := by
  rcases le_or_gt a b with hab | hab
  · exact ((S.continuousOn_lapInt μ x).mono (Icc_subset_Ici_self.trans
      (Ici_subset_Ici.2 ha))).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  · rw [Ioc_eq_empty (not_lt.2 hab.le)]
    exact integrableOn_empty

/-- **Shift formula.** `T(t) R(μ) z = e^{μt} (R(μ) z - ∫_0^t e^{-μr} T(r) z dr)` for `t ≥ 0`. -/
theorem T_laplace_apply {μ : ℂ} (hμ : S.ω < μ.re) {t : ℝ} (ht : 0 ≤ t) (z : X) :
    S.T t (S.laplace μ z) = Complex.exp (μ * t) •
      (S.laplace μ z - ∫ r in (0 : ℝ)..t, S.lapInt μ z r) := by
  have hI := S.integrableOn_lapInt hμ z
  -- split `(0, ∞) = (0, t] ∪ (t, ∞)`
  have hsplit : ∫ r in Ioi 0, S.lapInt μ z r =
      (∫ r in (0 : ℝ)..t, S.lapInt μ z r) + ∫ r in Ioi t, S.lapInt μ z r := by
    rw [intervalIntegral.integral_of_le ht, ← setIntegral_union Ioc_disjoint_Ioi_same
      measurableSet_Ioi (S.integrableOn_lapInt_Ioc z 0 t le_rfl)
      (hI.mono_set (Ioi_subset_Ioi ht)), Ioc_union_Ioi_eq_Ioi ht]
  -- translate `(t, ∞)` to `(0, ∞)`
  have htrans : ∫ r in Ioi t, S.lapInt μ z r = ∫ s in Ioi 0, S.lapInt μ z (s + t) := by
    have h := (measurePreserving_add_right (volume : Measure ℝ) t).setIntegral_preimage_emb
      (measurableEmbedding_addRight t) (S.lapInt μ z) (Ioi t)
    rw [preimage_add_const_Ioi, sub_self] at h
    exact h.symm
  have hcomm : S.T t (S.laplace μ z) = ∫ s in Ioi 0, Complex.exp (μ * t) • S.lapInt μ z (s + t) := by
    rw [S.laplace_apply' hμ, ← (S.T t).integral_comp_comm hI]
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    simp only [lapInt_def, map_smul, smul_smul]
    rw [← S.T_apply_add ht (le_of_lt hs), add_comm t s, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hcomm, integral_smul, ← htrans, S.laplace_apply' hμ, hsplit, add_sub_cancel_left]

theorem hasDerivAt_integral_lapInt {μ : ℂ} (z : X) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t => ∫ r in (0 : ℝ)..t, S.lapInt μ z r) (S.lapInt μ z t) t := by
  have hc : ContinuousOn (S.lapInt μ z) (Ioi 0) :=
    (S.continuousOn_lapInt μ z).mono Ioi_subset_Ici_self
  refine intervalIntegral.integral_hasDerivAt_right ?_ ?_ ?_
  · exact (((S.continuousOn_lapInt μ z).mono Icc_subset_Ici_self).intervalIntegrable_of_Icc ht.le)
  · exact hc.stronglyMeasurableAtFilter isOpen_Ioi t ht
  · exact hc.continuousAt (Ioi_mem_nhds ht)

/-- `t ↦ T(t) R(μ) z` has derivative `T(t)(μ R(μ) z - z)` at every `t > 0`; in the language of
generators, `R(μ) z` lies in the domain and `A R(μ) z = μ R(μ) z - z`. -/
theorem hasDerivAt_T_laplace {μ : ℂ} (hμ : S.ω < μ.re) (z : X) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t => S.T t (S.laplace μ z)) (S.T t (μ • S.laplace μ z - z)) t := by
  have hF := (hasDerivAt_cexp_mul μ t).smul
    ((hasDerivAt_const t (S.laplace μ z)).sub (S.hasDerivAt_integral_lapInt (μ := μ) z ht))
  have hev : (fun t => S.T t (S.laplace μ z)) =ᶠ[𝓝 t] fun t => Complex.exp (μ * t) •
      (S.laplace μ z - ∫ r in (0 : ℝ)..t, S.lapInt μ z r) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact S.T_laplace_apply hμ (le_of_lt hs) z
  refine (hF.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [map_sub, map_smul, S.T_laplace_apply hμ ht.le z, lapInt_def, zero_sub, smul_neg, smul_smul,
    ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_smul, smul_smul, mul_comm μ]
  abel

/-- **T7.2, resolvent identity** `R(μ) - R(μ') = (μ' - μ) R(μ) R(μ')`. -/
theorem laplace_sub_laplace {μ μ' : ℂ} (hμ : S.ω < μ.re) (hμ' : S.ω < μ'.re) :
    S.laplace μ - S.laplace μ' = (μ' - μ) • (S.laplace μ ∘L S.laplace μ') := by
  ext z
  have h := S.laplace_leftInverse' hμ (x := S.laplace μ' z) (y := μ' • S.laplace μ' z - z)
    fun t ht => S.hasDerivAt_T_laplace hμ' z ht
  have h2 : μ • S.laplace μ' z - (μ' • S.laplace μ' z - z) =
      (μ - μ') • S.laplace μ' z + z := by
    rw [sub_smul]
    abel
  rw [h2, map_add, map_smul] at h
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply]
  calc S.laplace μ z - S.laplace μ' z
      = S.laplace μ z - ((μ - μ') • S.laplace μ (S.laplace μ' z) + S.laplace μ z) := by rw [h]
    _ = (μ' - μ) • S.laplace μ (S.laplace μ' z) := by
      rw [show μ' - μ = -(μ - μ') by ring, neg_smul]
      abel

/-- Local uniform bound: near `μ₀` the resolvents are bounded by `2M / (Re μ₀ - ω)`. -/
theorem eventually_norm_laplace_le {μ₀ : ℂ} (hμ₀ : S.ω < μ₀.re) :
    ∀ᶠ μ in 𝓝 μ₀, S.ω < μ.re ∧ ‖S.laplace μ‖ ≤ 2 * S.M / (μ₀.re - S.ω) := by
  have hδ : S.ω + (μ₀.re - S.ω) / 2 < μ₀.re := by linarith
  filter_upwards [(Complex.continuous_re.tendsto μ₀).eventually (lt_mem_nhds hδ)] with μ hμ
  have hμ' : S.ω < μ.re := by
    have : 0 < (μ₀.re - S.ω) / 2 := by linarith
    linarith
  refine ⟨hμ', (S.norm_laplace_le hμ').trans ?_⟩
  rw [div_le_div_iff₀ (sub_pos.2 hμ') (sub_pos.2 hμ₀)]
  nlinarith [S.M_nonneg]

/-- The resolvent is continuous in operator norm on the half-plane. -/
theorem tendsto_laplace {μ₀ : ℂ} (hμ₀ : S.ω < μ₀.re) :
    Tendsto S.laplace (𝓝 μ₀) (𝓝 (S.laplace μ₀)) := by
  set C := 2 * S.M / (μ₀.re - S.ω)
  have hb : ∀ᶠ μ in 𝓝 μ₀, ‖S.laplace μ - S.laplace μ₀‖ ≤ ‖μ - μ₀‖ * (C * ‖S.laplace μ₀‖) := by
    filter_upwards [S.eventually_norm_laplace_le hμ₀] with μ hμ
    rw [S.laplace_sub_laplace hμ.1 hμ₀, norm_smul, norm_sub_rev]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right hμ.2 (norm_nonneg _))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm' (by simpa using hb) ?_
  have : Tendsto (fun μ : ℂ => ‖μ - μ₀‖ * (C * ‖S.laplace μ₀‖)) (𝓝 μ₀)
      (𝓝 (‖μ₀ - μ₀‖ * (C * ‖S.laplace μ₀‖))) :=
    ((continuous_id.sub continuous_const).norm.mul continuous_const).tendsto μ₀
  simpa using this

theorem continuousOn_laplace : ContinuousOn S.laplace {μ | S.ω < μ.re} :=
  fun μ hμ => (show ContinuousAt S.laplace μ from S.tendsto_laplace hμ).continuousWithinAt

/-- **T7.2** `d/dμ R(μ) = -R(μ)²`. -/
theorem hasDerivAt_laplace {μ₀ : ℂ} (hμ₀ : S.ω < μ₀.re) :
    HasDerivAt S.laplace (-(S.laplace μ₀ ∘L S.laplace μ₀)) μ₀ := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hlim : Tendsto (fun μ => -(S.laplace μ ∘L S.laplace μ₀)) (𝓝[≠] μ₀)
      (𝓝 (-(S.laplace μ₀ ∘L S.laplace μ₀))) := by
    have h : Tendsto S.laplace (𝓝[≠] μ₀) (𝓝 (S.laplace μ₀)) :=
      (S.tendsto_laplace hμ₀).mono_left nhdsWithin_le_nhds
    exact ((ContinuousLinearMap.compL ℂ X X X).flip (S.laplace μ₀) |>.continuous.tendsto _
      |>.comp h).neg
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (S.eventually_norm_laplace_le hμ₀)]
    with μ hne hμ
  rw [slope_def_module, S.laplace_sub_laplace hμ.1 hμ₀, smul_smul,
    show (μ - μ₀)⁻¹ * (μ₀ - μ) = -1 by
      rw [show μ₀ - μ = -(μ - μ₀) by ring, mul_neg, inv_mul_cancel₀ (sub_ne_zero.2 hne)],
    neg_one_smul]

/-- **T7.2** The resolvent is holomorphic on the half-plane `Re μ > ω`. -/
theorem differentiableOn_laplace : DifferentiableOn ℂ S.laplace {μ | S.ω < μ.re} :=
  fun μ hμ => (S.hasDerivAt_laplace hμ).differentiableAt.differentiableWithinAt

/-- Strong continuity at `0` of `T(t) R(μ)` in operator norm:
`‖T(t) R(μ) - R(μ)‖ → 0` as `t → 0⁺`. -/
theorem tendsto_norm_T_comp_laplace_sub {μ : ℂ} (hμ : S.ω < μ.re) :
    Tendsto (fun t => ‖S.T t ∘L S.laplace μ - S.laplace μ‖) (𝓝[≥] 0) (𝓝 0) := by
  set b : ℝ → ℝ := fun t => ‖Complex.exp (μ * t) - 1‖ * ‖S.laplace μ‖ +
    ‖Complex.exp (μ * t)‖ * (S.M * |t|) with hb
  have hbound : ∀ t, 0 ≤ t → ‖S.T t ∘L S.laplace μ - S.laplace μ‖ ≤ b t := by
    intro t ht
    refine ContinuousLinearMap.opNorm_le_bound _ (add_nonneg
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (mul_nonneg (norm_nonneg _) (mul_nonneg S.M_nonneg (abs_nonneg _)))) fun z => ?_
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
    rw [S.T_laplace_apply hμ ht z]
    have hI : ‖∫ r in (0 : ℝ)..t, S.lapInt μ z r‖ ≤ S.M * ‖z‖ * |t - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun r hr => by
        rw [uIoc_of_le ht] at hr
        exact S.norm_lapInt_le_const hμ z (le_of_lt hr.1)
    have heq : Complex.exp (μ * t) • (S.laplace μ z - ∫ r in (0 : ℝ)..t, S.lapInt μ z r) -
        S.laplace μ z = (Complex.exp (μ * t) - 1) • S.laplace μ z -
          Complex.exp (μ * t) • ∫ r in (0 : ℝ)..t, S.lapInt μ z r := by
      rw [smul_sub, sub_smul, one_smul]
      abel
    have hI' : ‖∫ r in (0 : ℝ)..t, S.lapInt μ z r‖ ≤ S.M * ‖z‖ * |t| := by simpa using hI
    rw [heq]
    calc _ ≤ ‖(Complex.exp (μ * t) - 1) • S.laplace μ z‖ +
          ‖Complex.exp (μ * t) • ∫ r in (0 : ℝ)..t, S.lapInt μ z r‖ := norm_sub_le _ _
      _ = ‖Complex.exp (μ * t) - 1‖ * ‖S.laplace μ z‖ +
          ‖Complex.exp (μ * t)‖ * ‖∫ r in (0 : ℝ)..t, S.lapInt μ z r‖ := by
          rw [norm_smul, norm_smul]
      _ ≤ ‖Complex.exp (μ * t) - 1‖ * (‖S.laplace μ‖ * ‖z‖) +
          ‖Complex.exp (μ * t)‖ * (S.M * ‖z‖ * |t|) := by
          gcongr
          exact (S.laplace μ).le_opNorm z
      _ = b t * ‖z‖ := by
          simp only [hb]
          ring
  have hb0 : Tendsto b (𝓝[≥] 0) (𝓝 0) := by
    have hc : Continuous b := by
      simp only [hb]
      have := continuous_cexp_neg_mul (-μ)
      have he : Continuous fun t : ℝ => Complex.exp (μ * t) := by simpa using this
      fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ici 0))
    simpa [hb] using this
  refine squeeze_zero' ?_ ?_ hb0
  · exact Eventually.of_forall fun t => norm_nonneg _
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact hbound t ht

end ExpSemigroup

end UnforcedLeray.Infra
