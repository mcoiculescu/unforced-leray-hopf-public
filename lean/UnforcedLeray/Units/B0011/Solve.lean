import UnforcedLeray.Units.B0011.Kernel
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.Order.Field

/-!
# Unit B0011, helper: the kernel operator solves the radial equation (weighted profiles)

Adapted from the reference formalization
`NonUniqueEuler/lean/NonUniqueEuler/H/Sec4/Sector/GreenSol.lean` (same Lean and Mathlib
versions). The reference works with profiles supported in a compact annulus `[a,b] ⊂ (0,∞)`
(`Prof a b g`). Here the profile is only assumed to satisfy the weighted condition
`WProf g`: `g` is a.e.-strongly measurable on `(0,∞)` and `ρ ‖g ρ‖ ∈ L¹(0,∞)`. This is what the
Gaussian class `X_G` of the manuscript gives (`MemXG.wprof` in `Units/B0011.lean`). All the
kernels are bounded by a constant times `ρ` once `t` stays away from `0`
(`abs_ker_le`, `abs_dker_le_mul'`, `abs_eker_le_mul`), which replaces the compact support in
the Fubini and dominated-convergence steps.

* `Psi n g t = ∫_{(0,∞)} ker(t,ρ) g(ρ) dρ`, `Phi`, `Eps`: the same with `dker`, `eker`.
* `WProf.hasDerivAt_Psi`: `Psi' = Phi` on `(0,∞)`; `WProf.Phi_sub`:
  `Phi(b') - Phi(a') = ∫_{a'}^{b'} Eps - 2n ∫_{a'}^{b'} g`, with `Eps = -Phi/t + n² Psi/t²`.
* `WProf.delta2_solution`: for `n = 2`, `ψ = -(1/4) Psi 2 g` solves
  `ψ'' + ψ'/r - 4ψ/r² = g` on `(0,∞)` in integrated form.
* `WProf.tendsto_Psi_nhdsGT_zero`, `WProf.tendsto_Psi_atTop`: `Psi n g t → 0` as `t → 0⁺` and
  as `t → ∞` (dominated convergence), for `n ≠ 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.B0011

/-- The weighted profile hypothesis: `g` is a.e.-strongly measurable on `(0, ∞)` and
`ρ ‖g ρ‖` is integrable on `(0, ∞)`. -/
structure WProf (g : ℝ → ℂ) : Prop where
  meas : AEStronglyMeasurable g (volume.restrict (Ioi 0))
  int : Integrable (fun ρ => ρ * ‖g ρ‖) (volume.restrict (Ioi 0))

/-- `∫_{(0,∞)} ker(t,ρ) g(ρ) dρ`. -/
def Psi (n : ℕ) (g : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ ρ in Ioi (0 : ℝ), (ker n t ρ : ℂ) * g ρ

/-- `∫_{(0,∞)} dker(t,ρ) g(ρ) dρ`. -/
def Phi (n : ℕ) (g : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ ρ in Ioi (0 : ℝ), (dker n t ρ : ℂ) * g ρ

/-- `∫_{(0,∞)} eker(t,ρ) g(ρ) dρ`. -/
def Eps (n : ℕ) (g : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ ρ in Ioi (0 : ℝ), (eker n t ρ : ℂ) * g ρ

variable {g : ℝ → ℂ}

/-- A measurable real factor bounded by `M ρ` times `g` is integrable on `(0, ∞)`. -/
theorem WProf.integrable_mul (h : WProf g) {F : ℝ → ℝ} (hF : Measurable F) {M : ℝ}
    (hM : ∀ ρ ∈ Ioi (0 : ℝ), |F ρ| ≤ M * ρ) :
    Integrable (fun ρ => (F ρ : ℂ) * g ρ) (volume.restrict (Ioi 0)) := by
  refine Integrable.mono' (h.int.const_mul M)
    ((Complex.measurable_ofReal.comp hF).aestronglyMeasurable.mul h.meas) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun ρ hρ => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |F ρ| * ‖g ρ‖ ≤ (M * ρ) * ‖g ρ‖ := mul_le_mul_of_nonneg_right (hM ρ hρ) (norm_nonneg _)
    _ = M * (ρ * ‖g ρ‖) := by ring

theorem WProf.integrable_ker (h : WProf g) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun ρ => (ker n t ρ : ℂ) * g ρ) (volume.restrict (Ioi 0)) :=
  h.integrable_mul (M := 1) ((measurable_ker n).comp (measurable_const.prodMk measurable_id))
    fun _ hρ => (abs_ker_le ht hρ).trans (one_mul _).symm.le

theorem WProf.integrable_dker (h : WProf g) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun ρ => (dker n t ρ : ℂ) * g ρ) (volume.restrict (Ioi 0)) :=
  h.integrable_mul (M := n / t) ((measurable_dker n).comp (measurable_const.prodMk measurable_id))
    fun _ hρ => abs_dker_le_mul' ht le_rfl hρ

theorem WProf.integrable_indicator (h : WProf g) {a' b' : ℝ} (ha' : 0 < a') :
    Integrable (fun ρ => (((Ioc a' b').indicator (fun _ => (1 : ℝ)) ρ : ℝ) : ℂ) * g ρ)
      (volume.restrict (Ioi 0)) :=
  h.integrable_mul (M := 1 / a') (measurable_const.indicator measurableSet_Ioc) fun ρ hρ => by
    by_cases hm : ρ ∈ Ioc a' b'
    · rw [indicator_of_mem hm, abs_one]
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ ha', one_mul]
      exact hm.1.le
    · rw [indicator_of_notMem hm, abs_zero]
      exact mul_nonneg (div_nonneg zero_le_one ha'.le) (le_of_lt hρ)

/-- `g` is integrable on `(a', b']` for `0 < a'`. -/
theorem WProf.integrableOn_Ioc (h : WProf g) {a' b' : ℝ} (ha' : 0 < a') :
    IntegrableOn g (Ioc a' b') := by
  have hsub : Ioc a' b' ⊆ Ioi (0 : ℝ) := fun x hx => ha'.trans hx.1
  have hint : Integrable (fun ρ => (1 / a') * (ρ * ‖g ρ‖)) (volume.restrict (Ioc a' b')) :=
    (h.int.mono_measure (Measure.restrict_mono hsub le_rfl)).const_mul _
  refine Integrable.mono' hint (h.meas.mono_set hsub) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioc fun ρ hρ => ?_
  rw [← mul_assoc, div_mul_eq_mul_div, one_mul]
  have h1 : (1 : ℝ) ≤ ρ / a' := (one_le_div ha').2 hρ.1.le
  calc ‖g ρ‖ = 1 * ‖g ρ‖ := (one_mul _).symm
    _ ≤ ρ / a' * ‖g ρ‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)

theorem WProf.intervalIntegrable (h : WProf g) {a' b' : ℝ} (ha' : 0 < a') (hb' : 0 < b') :
    IntervalIntegrable g volume a' b' := by
  rw [intervalIntegrable_iff]
  exact h.integrableOn_Ioc (lt_min ha' hb')

/-! ### Fubini -/

/-- Fubini for a measurable kernel bounded by `M ρ` on `(a', b'] × (0, ∞)`. -/
theorem WProf.fubini (h : WProf g) {K : ℝ → ℝ → ℝ}
    (hK : Measurable fun p : ℝ × ℝ => K p.1 p.2) {a' b' M : ℝ}
    (hM : ∀ t ∈ uIoc a' b', ∀ ρ ∈ Ioi (0 : ℝ), |K t ρ| ≤ M * ρ) :
    ∫ t in a'..b', ∫ ρ in Ioi (0 : ℝ), (K t ρ : ℂ) * g ρ =
      ∫ ρ in Ioi (0 : ℝ), ((∫ t in a'..b', K t ρ : ℝ) : ℂ) * g ρ := by
  have : IsFiniteMeasure (volume.restrict (uIoc a' b')) :=
    isFiniteMeasure_restrict.2 ((measure_mono uIoc_subset_uIcc).trans_lt measure_Icc_lt_top).ne
  have hbound : Integrable (fun z : ℝ × ℝ => (1 : ℝ) * (M * (z.2 * ‖g z.2‖)))
      ((volume.restrict (uIoc a' b')).prod (volume.restrict (Ioi 0))) :=
    (integrable_const (1 : ℝ)).mul_prod (h.int.const_mul M)
  have hmeas : AEStronglyMeasurable (fun z : ℝ × ℝ => (K z.1 z.2 : ℂ) * g z.2)
      ((volume.restrict (uIoc a' b')).prod (volume.restrict (Ioi 0))) :=
    (Complex.measurable_ofReal.comp hK).aestronglyMeasurable.mul h.meas.comp_snd
  have hae : ∀ᵐ z ∂((volume.restrict (uIoc a' b')).prod (volume.restrict (Ioi 0))),
      ‖(K z.1 z.2 : ℂ) * g z.2‖ ≤ (1 : ℝ) * (M * (z.2 * ‖g z.2‖)) := by
    rw [Measure.prod_restrict]
    refine ae_restrict_of_forall_mem (measurableSet_uIoc.prod measurableSet_Ioi) fun z hz => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, one_mul]
    calc |K z.1 z.2| * ‖g z.2‖ ≤ (M * z.2) * ‖g z.2‖ :=
          mul_le_mul_of_nonneg_right (hM z.1 hz.1 z.2 hz.2) (norm_nonneg _)
      _ = M * (z.2 * ‖g z.2‖) := by ring
  have hint : Integrable (Function.uncurry fun t ρ => (K t ρ : ℂ) * g ρ)
      ((volume.restrict (uIoc a' b')).prod (volume.restrict (Ioi 0))) :=
    hbound.mono' hmeas hae
  rw [intervalIntegral_integral_swap hint]
  congr 1
  funext ρ
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal]

/-! ### `Psi' = Phi` -/

theorem WProf.integral_Phi (h : WProf g) (n : ℕ) {a' b' : ℝ} (ha' : 0 < a') (hab : a' ≤ b') :
    ∫ t in a'..b', Phi n g t = Psi n g b' - Psi n g a' := by
  have hb' : 0 < b' := ha'.trans_le hab
  simp only [Phi]
  rw [h.fubini (measurable_dker n) (M := n / a') fun t ht ρ hρ =>
    abs_dker_le_mul' ha' (by rw [uIoc_of_le hab] at ht; exact ht.1.le) hρ]
  have hcongr : ∫ ρ in Ioi (0 : ℝ), ((∫ t in a'..b', dker n t ρ : ℝ) : ℂ) * g ρ =
      ∫ ρ in Ioi (0 : ℝ), ((ker n b' ρ : ℂ) * g ρ - (ker n a' ρ : ℂ) * g ρ) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun ρ hρ => ?_
    rw [integral_dker n hρ ha' hab]
    push_cast
    ring
  rw [hcongr, integral_sub (h.integrable_ker n hb'.le) (h.integrable_ker n ha'.le)]
  rfl

theorem WProf.continuousOn_Phi (h : WProf g) (n : ℕ) : ContinuousOn (Phi n g) (Ioi 0) := by
  intro t₀ ht₀
  have ht₀' : (0 : ℝ) < t₀ / 2 := half_pos ht₀
  refine ContinuousAt.continuousWithinAt ?_
  refine continuousAt_of_dominated (bound := fun ρ => n / (t₀ / 2) * (ρ * ‖g ρ‖)) ?_ ?_
    (h.int.const_mul _) ?_
  · exact Eventually.of_forall fun t => (Complex.measurable_ofReal.comp ((measurable_dker n).comp
        (measurable_const.prodMk measurable_id))).aestronglyMeasurable.mul h.meas
  · filter_upwards [Ioi_mem_nhds (half_lt_self ht₀)] with t ht
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun ρ hρ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |dker n t ρ| * ‖g ρ‖ ≤ (n / (t₀ / 2) * ρ) * ‖g ρ‖ :=
          mul_le_mul_of_nonneg_right (abs_dker_le_mul' ht₀' (le_of_lt ht) hρ) (norm_nonneg _)
      _ = n / (t₀ / 2) * (ρ * ‖g ρ‖) := by ring
  · have hne : ∀ᵐ ρ ∂(volume.restrict (Ioi (0 : ℝ))), ρ ≠ t₀ :=
      ae_restrict_of_ae (ae_ne_point t₀)
    filter_upwards [hne] with ρ hρ
    exact (Complex.continuous_ofReal.continuousAt.comp
      (continuousAt_dker n ht₀ (Ne.symm hρ))).mul continuousAt_const

theorem WProf.continuousOn_Psi (h : WProf g) (n : ℕ) : ContinuousOn (Psi n g) (Ici 0) := by
  refine continuousOn_of_dominated (bound := fun ρ => 1 * (ρ * ‖g ρ‖)) (fun t _ =>
    ((Complex.measurable_ofReal.comp ((measurable_ker n).comp
      (measurable_const.prodMk measurable_id))).aestronglyMeasurable.mul h.meas)) ?_
    (h.int.const_mul _) ?_
  · intro t ht
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun ρ hρ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, one_mul]
    exact mul_le_mul_of_nonneg_right (abs_ker_le ht hρ) (norm_nonneg _)
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun ρ hρ => ?_
    exact ((Complex.continuous_ofReal.comp (continuous_ker n hρ)).mul
      continuous_const).continuousOn

theorem WProf.hasDerivAt_Psi (h : WProf g) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (Psi n g) (Phi n g t) t := by
  have hcont := h.continuousOn_Phi n
  have hF : HasDerivAt (fun s => Psi n g t + ∫ u in t..s, Phi n g u)
      (Phi n g t) t :=
    (intervalIntegral.integral_hasDerivAt_right IntervalIntegrable.refl
      (hcont.stronglyMeasurableAtFilter isOpen_Ioi t ht)
      (hcont.continuousAt (Ioi_mem_nhds ht))).const_add _
  refine hF.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds ht] with s hs
  rcases le_total t s with hts | hst
  · rw [h.integral_Phi n ht hts]
    ring
  · rw [intervalIntegral.integral_symm, h.integral_Phi n hs hst]
    ring

/-! ### `Phi' = Eps - 2n g` in integrated form -/

theorem WProf.integral_indicator (_h : WProf g) {a' b' : ℝ} (ha' : 0 < a') (hab : a' ≤ b') :
    ∫ ρ in Ioi (0 : ℝ), (((Ioc a' b').indicator (fun _ => (1 : ℝ)) ρ : ℝ) : ℂ) * g ρ =
      ∫ t in a'..b', g t := by
  have h1 : ∀ ρ, (((Ioc a' b').indicator (fun _ => (1 : ℝ)) ρ : ℝ) : ℂ) * g ρ =
      (Ioc a' b').indicator g ρ := by
    intro ρ
    by_cases hρ : ρ ∈ Ioc a' b' <;> simp [hρ]
  simp_rw [h1]
  rw [setIntegral_indicator measurableSet_Ioc, intervalIntegral.integral_of_le hab]
  congr 2
  exact inter_eq_right.2 fun x hx => ha'.trans hx.1

theorem WProf.Eps_eq (h : WProf g) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Eps n g t = -(Phi n g t / t) + (n : ℂ) ^ 2 * Psi n g t / (t : ℂ) ^ 2 := by
  have hpt : ∀ ρ, (eker n t ρ : ℂ) * g ρ =
      -(1 / (t : ℂ)) * ((dker n t ρ : ℂ) * g ρ) +
        (n : ℂ) ^ 2 / (t : ℂ) ^ 2 * ((ker n t ρ : ℂ) * g ρ) := by
    intro ρ
    simp only [eker]
    push_cast
    ring
  simp only [Eps, hpt]
  rw [integral_add ((h.integrable_dker n ht).const_mul _)
      ((h.integrable_ker n ht.le).const_mul _),
    integral_const_mul, integral_const_mul]
  simp only [Phi, Psi]
  ring

theorem WProf.Phi_sub (h : WProf g) (n : ℕ) {a' b' : ℝ} (ha' : 0 < a') (hab : a' ≤ b') :
    Phi n g b' - Phi n g a' =
      (∫ t in a'..b', Eps n g t) - 2 * n * ∫ t in a'..b', g t := by
  have hb' : 0 < b' := ha'.trans_le hab
  have hE : ∫ t in a'..b', Eps n g t =
      ∫ ρ in Ioi (0 : ℝ), ((∫ t in a'..b', eker n t ρ : ℝ) : ℂ) * g ρ := by
    simp only [Eps]
    exact h.fubini (measurable_eker n) (M := ((n : ℝ) + (n : ℝ) ^ 2) / a' ^ 2)
      fun t ht ρ hρ => abs_eker_le_mul ha' (by rw [uIoc_of_le hab] at ht; exact ht.1.le) hρ
  have hcongr : ∫ ρ in Ioi (0 : ℝ), ((∫ t in a'..b', eker n t ρ : ℝ) : ℂ) * g ρ =
      ∫ ρ in Ioi (0 : ℝ), (((dker n b' ρ : ℂ) * g ρ - (dker n a' ρ : ℂ) * g ρ) +
        2 * n * ((((Ioc a' b').indicator (fun _ => (1 : ℝ)) ρ : ℝ) : ℂ) * g ρ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun ρ hρ => ?_
    have := dker_sub_dker n hρ ha' hab
    have e : (∫ t in a'..b', eker n t ρ) = dker n b' ρ - dker n a' ρ +
        2 * n * (Ioc a' b').indicator (fun _ => (1 : ℝ)) ρ := by linarith
    rw [e]
    push_cast
    ring
  have i1 : Integrable (fun ρ => (dker n b' ρ : ℂ) * g ρ - (dker n a' ρ : ℂ) * g ρ)
      (volume.restrict (Ioi 0)) := (h.integrable_dker n hb').sub (h.integrable_dker n ha')
  have i2 : Integrable (fun ρ => 2 * (n : ℂ) *
      ((((Ioc a' b').indicator (fun _ => (1 : ℝ)) ρ : ℝ) : ℂ) * g ρ))
      (volume.restrict (Ioi 0)) := (h.integrable_indicator (b' := b') ha').const_mul _
  rw [hE, hcongr, integral_add i1 i2,
    integral_sub (h.integrable_dker n hb') (h.integrable_dker n ha'), integral_const_mul,
    h.integral_indicator ha' hab]
  simp only [Phi]
  ring

/-! ### The angular-two solution -/

/-- For `n = 2`, `ψ = -(1/4) Psi 2 g` solves `ψ'' + ψ'/r - 4ψ/r² = g` on `(0, ∞)` in
integrated form, with the continuous derivative `ψ' = -(1/4) Phi 2 g`. -/
theorem WProf.delta2_solution (h : WProf g) :
    (∀ r : ℝ, 0 < r → HasDerivAt (fun t => -(1 / 4 : ℂ) * Psi 2 g t)
        (-(1 / 4 : ℂ) * Phi 2 g r) r) ∧
      ContinuousOn (fun t => -(1 / 4 : ℂ) * Phi 2 g t) (Ioi 0) ∧
      ∀ a b : ℝ, 0 < a → 0 < b →
        -(1 / 4 : ℂ) * Phi 2 g b - -(1 / 4 : ℂ) * Phi 2 g a =
          ∫ r in a..b, (g r - -(1 / 4 : ℂ) * Phi 2 g r / (r : ℂ) +
            4 * (-(1 / 4 : ℂ) * Psi 2 g r) / (r : ℂ) ^ 2) := by
  set c : ℂ := (1 / 4 : ℂ) with hc
  refine ⟨fun t ht => (h.hasDerivAt_Psi 2 ht).const_mul (-c), ?_, ?_⟩
  · exact continuousOn_const.mul (h.continuousOn_Phi 2)
  · have key : ∀ a' b' : ℝ, 0 < a' → a' ≤ b' →
        -c * Phi 2 g b' - -c * Phi 2 g a' =
          ∫ r in a'..b', (g r - -c * Phi 2 g r / (r : ℂ) +
            4 * (-c * Psi 2 g r) / (r : ℂ) ^ 2) := by
      intro a' b' ha' hab
      have hb' : 0 < b' := ha'.trans_le hab
      have hsub : uIcc a' b' ⊆ Ioi 0 := fun r hr => lt_of_lt_of_le (lt_min ha' hb') hr.1
      have hcont : ContinuousOn (fun r : ℝ => -(-c * Phi 2 g r / (r : ℂ)) +
          4 * (-c * Psi 2 g r) / (r : ℂ) ^ 2) (uIcc a' b') := by
        have hP : ContinuousOn (Phi 2 g) (uIcc a' b') := (h.continuousOn_Phi 2).mono hsub
        have hQ : ContinuousOn (Psi 2 g) (uIcc a' b') :=
          (h.continuousOn_Psi 2).mono fun r hr => mem_Ici.2 (le_of_lt (hsub hr))
        have hr0 : ∀ r ∈ uIcc a' b', (r : ℂ) ≠ 0 := fun r hr => by
          exact_mod_cast (ne_of_gt (hsub hr))
        refine ContinuousOn.add (ContinuousOn.neg (ContinuousOn.div (continuousOn_const.mul hP)
          (Complex.continuous_ofReal.continuousOn) hr0)) (ContinuousOn.div
          (continuousOn_const.mul (continuousOn_const.mul hQ))
          (Complex.continuous_ofReal.continuousOn.pow 2) fun r hr => pow_ne_zero 2 (hr0 r hr))
      have hsplit : ∫ r in a'..b', (g r - -c * Phi 2 g r / (r : ℂ) +
            4 * (-c * Psi 2 g r) / (r : ℂ) ^ 2) =
          (∫ r in a'..b', g r) + ∫ r in a'..b', (-(-c * Phi 2 g r / (r : ℂ)) +
            4 * (-c * Psi 2 g r) / (r : ℂ) ^ 2) := by
        rw [← intervalIntegral.integral_add (h.intervalIntegrable ha' hb')
          (hcont.intervalIntegrable)]
        congr 1
        funext r
        ring
      have hcongr : ∫ r in a'..b', (-(-c * Phi 2 g r / (r : ℂ)) +
            4 * (-c * Psi 2 g r) / (r : ℂ) ^ 2) =
          ∫ r in a'..b', -c * Eps 2 g r := by
        refine intervalIntegral.integral_congr fun r hr => ?_
        have hr0 : 0 < r := hsub hr
        rw [h.Eps_eq 2 hr0]
        push_cast
        ring
      rw [hsplit, hcongr, intervalIntegral.integral_const_mul]
      have hPhi := h.Phi_sub 2 ha' hab
      push_cast at hPhi
      rw [hc]
      linear_combination (-(1 / 4 : ℂ)) * hPhi
    intro a' b' ha' hb'
    rcases le_total a' b' with hab | hba
    · exact key a' b' ha' hab
    · rw [intervalIntegral.integral_symm, ← key b' a' hb' hba]
      ring

/-! ### Limits at `0` and at `∞` -/

/-- `Psi n g t → 0` as `t → 0⁺` (dominated convergence), for `n ≠ 0`. -/
theorem WProf.tendsto_Psi_nhdsGT_zero (h : WProf g) {n : ℕ} (hn : n ≠ 0) :
    Tendsto (Psi n g) (𝓝[>] 0) (𝓝 0) := by
  have hlim := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (Ioi 0))
    (l := 𝓝[>] (0 : ℝ)) (F := fun t ρ => (ker n t ρ : ℂ) * g ρ) (f := fun _ => 0)
    (fun ρ => 1 * (ρ * ‖g ρ‖))
    (Eventually.of_forall fun t => (Complex.measurable_ofReal.comp ((measurable_ker n).comp
      (measurable_const.prodMk measurable_id))).aestronglyMeasurable.mul h.meas)
    (by
      filter_upwards [self_mem_nhdsWithin] with t ht
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun ρ hρ => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, one_mul]
      exact mul_le_mul_of_nonneg_right (abs_ker_le (le_of_lt ht) hρ) (norm_nonneg _))
    (h.int.const_mul _)
    (by
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun ρ hρ => ?_
      have h0 : ker n 0 ρ = 0 := by
        have hρ' : (0 : ℝ) < ρ := hρ
        simp only [ker, min_eq_left hρ'.le, zero_div, zero_pow hn, zero_mul]
      have hc := ((Complex.continuous_ofReal.comp (continuous_ker n hρ)).tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      have := hc.mul_const (g ρ)
      simpa [h0] using this)
  rw [show Psi n g = fun t => ∫ ρ in Ioi (0 : ℝ), (ker n t ρ : ℂ) * g ρ from rfl]
  simpa using hlim

/-- `Psi n g t → 0` as `t → ∞` (dominated convergence), for `n ≠ 0`. -/
theorem WProf.tendsto_Psi_atTop (h : WProf g) {n : ℕ} (hn : n ≠ 0) :
    Tendsto (Psi n g) atTop (𝓝 0) := by
  have hlim := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (Ioi 0))
    (l := (atTop : Filter ℝ)) (F := fun t ρ => (ker n t ρ : ℂ) * g ρ) (f := fun _ => 0)
    (fun ρ => 1 * (ρ * ‖g ρ‖))
    (Eventually.of_forall fun t => (Complex.measurable_ofReal.comp ((measurable_ker n).comp
      (measurable_const.prodMk measurable_id))).aestronglyMeasurable.mul h.meas)
    (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun ρ hρ => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, one_mul]
      exact mul_le_mul_of_nonneg_right (abs_ker_le ht hρ) (norm_nonneg _))
    (h.int.const_mul _)
    (by
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun ρ hρ => ?_
      have hq : Tendsto (fun t : ℝ => ρ / t) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      have hk : Tendsto (fun t : ℝ => kR n ρ t) atTop (𝓝 0) := by
        have := (hq.pow n).mul_const ρ
        rw [zero_pow hn, zero_mul] at this
        exact this
      have hk' : Tendsto (fun t : ℝ => ker n t ρ) atTop (𝓝 0) := by
        refine hk.congr' ?_
        filter_upwards [eventually_ge_atTop ρ] with t ht
        exact (ker_of_ge ht).symm
      have := ((Complex.continuous_ofReal.tendsto 0).comp hk').mul_const (g ρ)
      simpa using this)
  rw [show Psi n g = fun t => ∫ ρ in Ioi (0 : ℝ), (ker n t ρ : ℂ) * g ρ from rfl]
  simpa using hlim

end UnforcedLeray.B0011
