import NonUniqueEuler.P.Infra.ConvMinkowski.Minkowski
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# B0284: the age weight `s^α ds` and the Mellin–Minkowski lemma

Unit B0284 (`background:eq:2.24`, tex lines 5247–5250). The age part of the norm
`H_p = L^p(s^{a_p} ds; L^p(q,η))`, `a_p = p/2 - 5/2` (tex lines 4657–4660, 5229–5235), and
the dilation bound "in the weighted measure `‖F(s e^{-t})‖_{H_r} = e^{-γ_r t}‖F‖`"
(blueprint proof outline of B0284; tex lines 4697–4700).

Provenance. `ageWeight`, `lintegral_ageWeight`, `eLpNorm_ageWeight`,
`eLpNorm_const_mul_enn`, `lintegral_image_mul_left`, `eLpNorm_comp_mul_ageWeight` and
`eLpNorm_mellin_le_lintegral` are copied, with `powWeight` renamed `ageWeight`, from the draft

`UnforcedLeray.Conv`, blueprint INF22 A4), which is not compiled at the time of writing and so
cannot be imported. Once it compiles, `ageWeight` is `UnforcedLeray.Conv.powWeight` and these
copies should be replaced by imports. Minkowski's integral inequality is the vendored, compiled
`NonUniqueEuler.Conv.eLpNorm_lintegral_le`.

New here: `lintegral_Ioo_rpow` (`∫_0^1 u^{γ-1} du = 1/γ`) and `lintegral_Ioo_eq_mellin`
(the substitution `t = s u` that writes `∫_0^s ψ` as a Mellin convolution).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace UnforcedLeray.B0284

/-! ### The weighted measures `s^α ds` -/

/-- The power-weighted age measure `s^α ds` on `(0,∞)` (copy of `UnforcedLeray.Conv.powWeight`,
`Lib/ConvIneq/MellinHardy.lean`). -/
def ageWeight (α : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0:ℝ))).withDensity fun s => ENNReal.ofReal (s ^ α)

instance sigmaFinite_ageWeight (α : ℝ) : SigmaFinite (ageWeight α) := by
  unfold ageWeight; infer_instance

theorem ageWeight_ac (α : ℝ) : ageWeight α ≪ volume.restrict (Ioi 0) :=
  withDensity_absolutelyContinuous _ _

theorem ae_ageWeight_pos (α : ℝ) : ∀ᵐ s ∂(ageWeight α), 0 < s :=
  (ageWeight_ac α).ae_le (ae_restrict_mem measurableSet_Ioi)

/-- Lower integrals against `ageWeight α`; no measurability is needed. -/
theorem lintegral_ageWeight (α : ℝ) (φ : ℝ → ℝ≥0∞) :
    ∫⁻ s, φ s ∂(ageWeight α) = ∫⁻ s in Ioi 0, ENNReal.ofReal (s ^ α) * φ s := by
  rw [ageWeight, lintegral_withDensity_eq_lintegral_mul_non_measurable _
    (f := fun s => ENNReal.ofReal (s ^ α)) (by fun_prop)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  rfl

/-- The weighted `L^p` norm as a lower integral; no measurability is needed. -/
theorem eLpNorm_ageWeight {ε : Type*} [ENorm ε] (α : ℝ) {p : ℝ} (hp : 0 < p) (g : ℝ → ε) :
    eLpNorm g (ENNReal.ofReal p) (ageWeight α) =
      (∫⁻ s in Ioi 0, ENNReal.ofReal (s ^ α) * ‖g s‖ₑ ^ p) ^ (1 / p) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp [hp]) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp.le, lintegral_ageWeight]

/-- `eLpNorm (c * g) = c * eLpNorm g` for `[0,∞]`-valued measurable `g` and any `c ∈ [0,∞]`. -/
theorem eLpNorm_const_mul_enn {β : Type*} [MeasurableSpace β] {μ : Measure β} {g : β → ℝ≥0∞}
    (hg : AEMeasurable g μ) (c : ℝ≥0∞) {p : ℝ} (hp : 0 < p) :
    eLpNorm (fun x => c * g x) (ENNReal.ofReal p) μ = c * eLpNorm g (ENNReal.ofReal p) μ := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by simp [hp]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp.le]
  simp only [enorm_eq_self, ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  rw [lintegral_const_mul'' _ (hg.pow_const p), ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    ← ENNReal.rpow_mul, mul_one_div_cancel hp.ne', ENNReal.rpow_one]

/-- The substitution `t = s u` on a measurable set, for any `[0,∞]`-valued integrand. -/
theorem lintegral_image_mul_left {s : ℝ} (hs : 0 < s) {A : Set ℝ} (hA : MeasurableSet A)
    (h : ℝ → ℝ≥0∞) :
    ∫⁻ t in (fun u => s * u) '' A, h t = ENNReal.ofReal s * ∫⁻ u in A, h (s * u) := by
  rw [lintegral_image_eq_lintegral_abs_deriv_mul hA (f' := fun _ => s)
    (fun x _ => (hasDerivAt_const_mul s).hasDerivWithinAt) ((mul_right_injective₀ hs.ne').injOn) h,
    abs_of_pos hs, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- **The dilation identity** (tex lines 4697–4700): for `u > 0`,
`‖φ(·u)‖_{L^p(s^α ds)} = u^{-(α+1)/p} ‖φ‖_{L^p(s^α ds)}`. No measurability is needed. -/
theorem eLpNorm_comp_mul_ageWeight (α : ℝ) {p : ℝ} (hp : 0 < p) (φ : ℝ → ℝ≥0∞) {u : ℝ}
    (hu : 0 < u) :
    eLpNorm (fun s => φ (s * u)) (ENNReal.ofReal p) (ageWeight α) =
      ENNReal.ofReal (u ^ (-(α + 1) / p)) * eLpNorm φ (ENNReal.ofReal p) (ageWeight α) := by
  rw [eLpNorm_ageWeight α hp, eLpNorm_ageWeight α hp]
  simp only [enorm_eq_self]
  set I := ∫⁻ r in Ioi 0, ENNReal.ofReal (r ^ α) * φ r ^ p with hI
  set J := ∫⁻ s in Ioi 0, ENNReal.ofReal (s ^ α) * φ (s * u) ^ p with hJ
  have hIJ : I = ENNReal.ofReal (u ^ (α + 1)) * J := by
    have h1 := lintegral_image_mul_left hu (A := Ioi 0) measurableSet_Ioi
      (fun r => ENNReal.ofReal (r ^ α) * φ r ^ p)
    rw [image_mul_left_Ioi hu, mul_zero] at h1
    rw [hI, h1, hJ, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
    have hs' : (0:ℝ) < s := hs
    rw [show u * s = s * u from mul_comm u s, Real.mul_rpow hs'.le hu.le,
      Real.rpow_add hu, Real.rpow_one, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity)]
    ring
  have hJI : J = ENNReal.ofReal (u ^ (-(α + 1))) * I := by
    rw [hIJ, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add hu,
      neg_add_cancel, Real.rpow_zero, ENNReal.ofReal_one, one_mul]
  rw [hJI, ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), ← Real.rpow_mul hu.le,
    show -(α + 1) * (1 / p) = -(α + 1) / p by ring]

/-- **Mellin–Minkowski**, `[0,∞]`-valued (copy of `UnforcedLeray.Conv.eLpNorm_mellin_le_lintegral`):
for measurable `k, φ ≥ 0` and `p ≥ 1`,
`‖s ↦ ∫_0^∞ k(u) φ(su) du‖_{L^p(s^α)} ≤ (∫_0^∞ k(u) u^{-(α+1)/p} du) ‖φ‖_{L^p(s^α)}`. -/
theorem eLpNorm_mellin_le_lintegral {p α : ℝ} (hp : 1 ≤ p) {k φ : ℝ → ℝ≥0∞}
    (hk : Measurable k) (hφ : Measurable φ) :
    eLpNorm (fun s => ∫⁻ u in Ioi 0, k u * φ (s * u)) (ENNReal.ofReal p) (ageWeight α) ≤
      (∫⁻ u in Ioi 0, k u * ENNReal.ofReal (u ^ (-(α + 1) / p))) *
        eLpNorm φ (ENNReal.ofReal p) (ageWeight α) := by
  have hp0 : 0 < p := by linarith
  have hkm : Measurable fun u => k u * ENNReal.ofReal (u ^ (-(α + 1) / p)) :=
    hk.mul (by fun_prop)
  have hF : AEMeasurable (Function.uncurry fun s u => k u * φ (s * u))
      ((ageWeight α).prod (volume.restrict (Ioi 0))) := by
    refine Measurable.aemeasurable ?_
    show Measurable fun q : ℝ × ℝ => k q.2 * φ (q.1 * q.2)
    exact (hk.comp measurable_snd).mul (hφ.comp (measurable_fst.mul measurable_snd))
  calc eLpNorm (fun s => ∫⁻ u in Ioi 0, k u * φ (s * u)) (ENNReal.ofReal p) (ageWeight α)
      ≤ ∫⁻ u in Ioi 0, eLpNorm (fun s => k u * φ (s * u)) (ENNReal.ofReal p) (ageWeight α) :=
        NonUniqueEuler.Conv.eLpNorm_lintegral_le hF (ENNReal.one_le_ofReal.mpr hp)
          ENNReal.ofReal_ne_top
    _ = ∫⁻ u in Ioi 0, k u * ENNReal.ofReal (u ^ (-(α + 1) / p)) *
          eLpNorm φ (ENNReal.ofReal p) (ageWeight α) := by
        refine setLIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
        have hm : Measurable fun s : ℝ => φ (s * u) := hφ.comp (measurable_id.mul_const u)
        rw [eLpNorm_const_mul_enn hm.aemeasurable (k u) hp0,
          eLpNorm_comp_mul_ageWeight α hp0 φ hu, mul_assoc]
    _ = (∫⁻ u in Ioi 0, k u * ENNReal.ofReal (u ^ (-(α + 1) / p))) *
          eLpNorm φ (ENNReal.ofReal p) (ageWeight α) := lintegral_mul_const _ hkm

/-! ### The Hardy kernel `1_{(0,1)}(u) u^{-1}` -/

/-- `∫_0^1 u^{γ-1} du = 1/γ` for `γ > 0`, as a lower integral over `(0,1)`. -/
theorem lintegral_Ioo_rpow {γ : ℝ} (hγ : 0 < γ) :
    ∫⁻ u in Ioo 0 1, ENNReal.ofReal (u ^ (γ - 1)) = ENNReal.ofReal (1 / γ) := by
  have hr : -1 < γ - 1 := by linarith
  have hint : IntegrableOn (fun u : ℝ => u ^ (γ - 1)) (Ioo 0 1) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) hr)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at this
    exact this.mono_set Ioo_subset_Ioc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun u hu =>
      Real.rpow_nonneg hu.1.le _)), ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl hr)]
  congr 1
  rw [sub_add_cancel, Real.one_rpow, Real.zero_rpow hγ.ne', sub_zero]

/-- The Hardy kernel `k(u) = 1_{(0,1)}(u) u^{-1}`. -/
def hardyKernel : ℝ → ℝ≥0∞ := (Ioo (0:ℝ) 1).indicator fun u => ENNReal.ofReal u⁻¹

theorem measurable_hardyKernel : Measurable hardyKernel :=
  (Measurable.ennreal_ofReal measurable_inv).indicator measurableSet_Ioo

/-- The constant of the Mellin bound for the Hardy kernel: `∫_0^1 u^{-1} u^{γ} du = 1/γ`. -/
theorem lintegral_hardyKernel_rpow {γ : ℝ} (hγ : 0 < γ) :
    ∫⁻ u in Ioi 0, hardyKernel u * ENNReal.ofReal (u ^ γ) = ENNReal.ofReal (1 / γ) := by
  have h : ∀ u, hardyKernel u * ENNReal.ofReal (u ^ γ) =
      (Ioo (0:ℝ) 1).indicator (fun u => ENNReal.ofReal (u ^ (γ - 1))) u := by
    intro u
    by_cases hu : u ∈ Ioo (0:ℝ) 1
    · rw [hardyKernel, indicator_of_mem hu, indicator_of_mem hu, ← ENNReal.ofReal_mul
        (inv_nonneg.2 hu.1.le), Real.rpow_sub_one hu.1.ne', inv_mul_eq_div]
    · rw [hardyKernel, indicator_of_notMem hu, indicator_of_notMem hu, zero_mul]
  simp_rw [h]
  rw [lintegral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
    inter_eq_left.2 Ioo_subset_Ioi_self]
  exact lintegral_Ioo_rpow hγ

/-- The substitution `t = s u`: `∫_0^s ψ(t) dt = ∫_0^∞ k(u) (su) ψ(su) du` for `s > 0`, with
the Hardy kernel `k`. No measurability is needed. -/
theorem lintegral_Ioo_eq_mellin {s : ℝ} (hs : 0 < s) (ψ : ℝ → ℝ≥0∞) :
    ∫⁻ t in Ioo 0 s, ψ t =
      ∫⁻ u in Ioi 0, hardyKernel u * (ENNReal.ofReal (s * u) * ψ (s * u)) := by
  have h1 := lintegral_image_mul_left hs (A := Ioo 0 1) measurableSet_Ioo ψ
  rw [image_mul_left_Ioo hs, mul_zero, mul_one] at h1
  rw [h1]
  have h : ∀ u, hardyKernel u * (ENNReal.ofReal (s * u) * ψ (s * u)) =
      (Ioo (0:ℝ) 1).indicator (fun u => ENNReal.ofReal s * ψ (s * u)) u := by
    intro u
    by_cases hu : u ∈ Ioo (0:ℝ) 1
    · rw [hardyKernel, indicator_of_mem hu, indicator_of_mem hu, ← mul_assoc,
        ← ENNReal.ofReal_mul (inv_nonneg.2 hu.1.le),
        show u⁻¹ * (s * u) = s by field_simp [hu.1.ne']]
    · rw [hardyKernel, indicator_of_notMem hu, indicator_of_notMem hu, zero_mul]
  simp_rw [h]
  rw [lintegral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
    inter_eq_left.2 Ioo_subset_Ioi_self, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end UnforcedLeray.B0284
