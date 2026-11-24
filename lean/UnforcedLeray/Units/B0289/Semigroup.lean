import UnforcedLeray.Units.B0289.Defs

/-!
# B0289: the heat semigroup law on the cylinder

Unit B0289 (tex lines 4771–4775; proof at tex lines 3784–3819). The cutoff argument of the
manuscript (tex lines 3788–3792: "Its zero extension solves the ordinary heat equation with
source `χ P₀F/s + χ' b`") uses the semigroup law `e^{αΔ} e^{βΔ} = e^{(α+β)Δ}`. For the
pointwise definition `B0284.heat` it is proved here:

* `integral_heatKernel1_conv`, `integral_heatKernel2_conv`: `G_α ∗ G_β = G_{α+β}` in one and
  two dimensions (completing the square, as in `Lib/Gaussian/Kernel.lean`,
  `integral_gaussKernel_mul_gaussKernel`);
* `lintegral_heatAbs`: the absolute form `∫ G_α(w) heatAbs_β f (z-w) dw = heatAbs_{α+β} f z`
  (Tonelli; no finiteness needed);
* `heat_heat`: `e^{αΔ}(e^{βΔ} f)(z) = e^{(α+β)Δ} f(z)` whenever `heatAbs_{α+β} f z < ∞`;
* linearity `heat_add_smul`, a.e.-congruence `heat_congr_ae`, periodicity `heatAbs_periodic`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Real
open scoped NNReal ENNReal

namespace UnforcedLeray.B0289

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.B0284

/-! ## Gaussian convolution -/

/-- Completing the square for the one-dimensional kernel `G_θ = B0191.heatKernel 1 θ`. -/
theorem heatKernel1_product {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (y w : ℝ) :
    B0191.heatKernel 1 α (y - w) * B0191.heatKernel 1 β w =
      B0191.heatKernel 1 (α + β) y *
        B0191.heatKernel 1 (α * β / (α + β)) (w - β / (α + β) * y) := by
  unfold B0191.heatKernel
  have hab : 0 < α + β := by positivity
  have hα' := hα.ne'
  have hβ' := hβ.ne'
  have hab' := hab.ne'
  have hpre : (√(4 * π * 1 * α))⁻¹ * (√(4 * π * 1 * β))⁻¹ =
      (√(4 * π * 1 * (α + β)))⁻¹ * (√(4 * π * 1 * (α * β / (α + β))))⁻¹ := by
    rw [← mul_inv, ← mul_inv, ← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    congr 2
    field_simp
  have hexp : -(y - w) ^ 2 / (4 * 1 * α) + -w ^ 2 / (4 * 1 * β) =
      -y ^ 2 / (4 * 1 * (α + β)) +
        -(w - β / (α + β) * y) ^ 2 / (4 * 1 * (α * β / (α + β))) := by
    field_simp
    ring
  calc _ = ((√(4 * π * 1 * α))⁻¹ * (√(4 * π * 1 * β))⁻¹) *
        Real.exp (-(y - w) ^ 2 / (4 * 1 * α) + -w ^ 2 / (4 * 1 * β)) := by
          rw [Real.exp_add]; ring
    _ = _ := by rw [hpre, hexp, Real.exp_add]; ring

theorem integrable_heatKernel1 {θ : ℝ} (hθ : 0 < θ) : Integrable (B0191.heatKernel 1 θ) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_heatKernel_one hθ]
  exact one_ne_zero

theorem integrable_heatKernel1_conv {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (y : ℝ) :
    Integrable (fun w => B0191.heatKernel 1 α (y - w) * B0191.heatKernel 1 β w) := by
  simp_rw [heatKernel1_product hα hβ y]
  exact ((integrable_heatKernel1 (by positivity)).comp_sub_right _).const_mul _

/-- `G_α ∗ G_β = G_{α+β}` on `ℝ`. -/
theorem integral_heatKernel1_conv {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (y : ℝ) :
    ∫ w, B0191.heatKernel 1 α (y - w) * B0191.heatKernel 1 β w =
      B0191.heatKernel 1 (α + β) y := by
  simp_rw [heatKernel1_product hα hβ y]
  rw [integral_const_mul, integral_sub_right_eq_self, integral_heatKernel_one (by positivity),
    mul_one]

theorem heatKernel2_conv_eq {α β : ℝ} (y w : Plane) :
    heatKernel2 α (y - w) * heatKernel2 β w =
      (B0191.heatKernel 1 α (y.1 - w.1) * B0191.heatKernel 1 β w.1) *
        (B0191.heatKernel 1 α (y.2 - w.2) * B0191.heatKernel 1 β w.2) := by
  simp only [heatKernel2, Prod.fst_sub, Prod.snd_sub]
  ring

theorem integrable_heatKernel2_conv {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (y : Plane) :
    Integrable (fun w : Plane => heatKernel2 α (y - w) * heatKernel2 β w) := by
  simp_rw [heatKernel2_conv_eq y]
  exact (integrable_heatKernel1_conv hα hβ y.1).mul_prod (integrable_heatKernel1_conv hα hβ y.2)

/-- `G_α ∗ G_β = G_{α+β}` on the plane. -/
theorem integral_heatKernel2_conv {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (y : Plane) :
    ∫ w : Plane, heatKernel2 α (y - w) * heatKernel2 β w = heatKernel2 (α + β) y := by
  simp_rw [heatKernel2_conv_eq y]
  calc ∫ w : Plane, (B0191.heatKernel 1 α (y.1 - w.1) * B0191.heatKernel 1 β w.1) *
        (B0191.heatKernel 1 α (y.2 - w.2) * B0191.heatKernel 1 β w.2)
      = ∫ w, (B0191.heatKernel 1 α (y.1 - w.1) * B0191.heatKernel 1 β w.1) *
        (B0191.heatKernel 1 α (y.2 - w.2) * B0191.heatKernel 1 β w.2)
          ∂((volume : Measure ℝ).prod volume) := rfl
    _ = (∫ x, B0191.heatKernel 1 α (y.1 - x) * B0191.heatKernel 1 β x) *
          ∫ x, B0191.heatKernel 1 α (y.2 - x) * B0191.heatKernel 1 β x :=
        integral_prod_mul (fun x => B0191.heatKernel 1 α (y.1 - x) * B0191.heatKernel 1 β x)
          (fun x => B0191.heatKernel 1 α (y.2 - x) * B0191.heatKernel 1 β x)
    _ = heatKernel2 (α + β) y := by
        rw [integral_heatKernel1_conv hα hβ, integral_heatKernel1_conv hα hβ]
        rfl

/-- The lower-integral form of `G_α ∗ G_β = G_{α+β}`, in the order used below. -/
theorem lintegral_heatKernel2_conv {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (y : Plane) :
    ∫⁻ w : Plane, ENNReal.ofReal (heatKernel2 α w) * ENNReal.ofReal (heatKernel2 β (y - w)) =
      ENNReal.ofReal (heatKernel2 (α + β) y) := by
  have h1 : ∀ w : Plane, ENNReal.ofReal (heatKernel2 α w) *
      ENNReal.ofReal (heatKernel2 β (y - w)) =
        ENNReal.ofReal (heatKernel2 β (y - w) * heatKernel2 α w) := by
    intro w
    rw [mul_comm, ENNReal.ofReal_mul (heatKernel2_nonneg hβ _)]
  simp_rw [h1]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_heatKernel2_conv hβ hα y)
    (Eventually.of_forall fun w => mul_nonneg (heatKernel2_nonneg hβ _)
      (heatKernel2_nonneg hα _)), integral_heatKernel2_conv hβ hα y, add_comm]

/-! ## The absolute semigroup law -/

theorem aestronglyMeasurable_comp_sub {f : Plane → Plane} (hf : AEStronglyMeasurable f volume)
    (z : Plane) : AEStronglyMeasurable (fun y : Plane => f (z - y)) volume :=
  hf.comp_quasiMeasurePreserving
    (quasiMeasurePreserving_sub_left_of_right_invariant (volume : Measure Plane) z)

theorem measurable_ofReal_heatKernel2 (θ : ℝ) :
    Measurable fun w : Plane => ENNReal.ofReal (heatKernel2 θ w) :=
  ENNReal.measurable_ofReal.comp (measurable_heatKernel2_right θ)

/-- The iterated absolute integral `∫∫ G_α(w) G_β(y-w) |f(z-y)| dy dw = heatAbs_{α+β} f z`. -/
theorem lintegral_lintegral_heatKernel {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) {f : Plane → Plane}
    (hf : AEStronglyMeasurable f volume) (z : Plane) :
    ∫⁻ w : Plane, ∫⁻ y : Plane, ENNReal.ofReal (heatKernel2 α w) *
        (ENNReal.ofReal (heatKernel2 β (y - w)) * ‖f (z - y)‖ₑ) =
      heatAbs (α + β) f z := by
  have hm : AEMeasurable (Function.uncurry fun (w y : Plane) =>
      ENNReal.ofReal (heatKernel2 α w) *
        (ENNReal.ofReal (heatKernel2 β (y - w)) * ‖f (z - y)‖ₑ))
      ((volume : Measure Plane).prod volume) := by
    have h1 : Measurable fun q : Plane × Plane => ENNReal.ofReal (heatKernel2 α q.1) :=
      (measurable_ofReal_heatKernel2 α).comp measurable_fst
    have h2 : Measurable fun q : Plane × Plane => ENNReal.ofReal (heatKernel2 β (q.2 - q.1)) :=
      (measurable_ofReal_heatKernel2 β).comp (measurable_snd.sub measurable_fst)
    have h3 : AEMeasurable (fun q : Plane × Plane => ‖f (z - q.2)‖ₑ)
        ((volume : Measure Plane).prod volume) :=
      (aestronglyMeasurable_comp_sub hf z).enorm.comp_snd
    exact h1.aemeasurable.mul (h2.aemeasurable.mul h3)
  rw [lintegral_lintegral_swap hm]
  have h4 : ∀ y : Plane, ∫⁻ w : Plane, ENNReal.ofReal (heatKernel2 α w) *
      (ENNReal.ofReal (heatKernel2 β (y - w)) * ‖f (z - y)‖ₑ) =
        ENNReal.ofReal (heatKernel2 (α + β) y) * ‖f (z - y)‖ₑ := by
    intro y
    simp_rw [← mul_assoc]
    rw [lintegral_mul_const' _ _ enorm_ne_top, lintegral_heatKernel2_conv hα hβ y]
  simp_rw [h4]
  rfl

/-- **Absolute semigroup law**: `∫ G_α(w) heatAbs_β f (z-w) dw = heatAbs_{α+β} f z`. -/
theorem lintegral_heatAbs {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) {f : Plane → Plane}
    (hf : AEStronglyMeasurable f volume) (z : Plane) :
    ∫⁻ w : Plane, ENNReal.ofReal (heatKernel2 α w) * heatAbs β f (z - w) =
      heatAbs (α + β) f z := by
  rw [← lintegral_lintegral_heatKernel hα hβ hf z]
  refine lintegral_congr fun w => ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  unfold heatAbs
  rw [← lintegral_sub_right_eq_self _ w]
  refine lintegral_congr fun y => ?_
  congr 2
  abel_nf

/-! ## Integrability and the Bochner semigroup law -/

theorem integrable_heat_integrand {θ : ℝ} (hθ : 0 < θ) {f : Plane → Plane}
    (hf : AEStronglyMeasurable f volume) {z : Plane} (hfin : heatAbs θ f z ≠ ⊤) :
    Integrable (fun w => heatKernel2 θ w • f (z - w)) := by
  refine ⟨(measurable_heatKernel2_right θ).aestronglyMeasurable.smul
    (aestronglyMeasurable_comp_sub hf z), ?_⟩
  rw [HasFiniteIntegral]
  calc ∫⁻ w, ‖heatKernel2 θ w • f (z - w)‖ₑ = heatAbs θ f z := by
        refine lintegral_congr fun w => ?_
        rw [enorm_smul, Real.enorm_of_nonneg (heatKernel2_nonneg hθ w)]
    _ < ⊤ := lt_top_iff_ne_top.2 hfin

/-- **Semigroup law** `e^{αΔ}(e^{βΔ} f)(z) = e^{(α+β)Δ} f(z)`, for `α, β > 0`, an a.e. strongly
measurable `f` and a point `z` with `heatAbs_{α+β} f z < ∞`. -/
theorem heat_heat {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) {f : Plane → Plane}
    (hf : AEStronglyMeasurable f volume) {z : Plane} (hfin : heatAbs (α + β) f z ≠ ⊤) :
    heat α (heat β f) z = heat (α + β) f z := by
  rw [heat_apply_of_pos hα, heat_apply_of_pos (add_pos hα hβ)]
  set Φ : Plane → Plane → Plane :=
    fun w y => (heatKernel2 α w * heatKernel2 β (y - w)) • f (z - y) with hΦ
  have h1 : ∀ w, heatKernel2 α w • heat β f (z - w) = ∫ y, Φ w y := by
    intro w
    rw [heat_apply_of_pos hβ, ← integral_smul,
      ← integral_sub_right_eq_self (fun v => heatKernel2 α w • heatKernel2 β v • f (z - w - v)) w]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hΦ, smul_smul]
    congr 2
    abel_nf
  have hint : Integrable (Function.uncurry Φ) ((volume : Measure Plane).prod volume) := by
    refine ⟨?_, ?_⟩
    · have hk : Measurable fun q : Plane × Plane => heatKernel2 α q.1 * heatKernel2 β (q.2 - q.1) :=
        ((measurable_heatKernel2_right α).comp measurable_fst).mul
          ((measurable_heatKernel2_right β).comp (measurable_snd.sub measurable_fst))
      exact hk.aestronglyMeasurable.smul (aestronglyMeasurable_comp_sub hf z).comp_snd
    · rw [HasFiniteIntegral]
      have he : ∀ q : Plane × Plane, ‖Function.uncurry Φ q‖ₑ =
          ENNReal.ofReal (heatKernel2 α q.1) *
            (ENNReal.ofReal (heatKernel2 β (q.2 - q.1)) * ‖f (z - q.2)‖ₑ) := by
        intro q
        simp only [Function.uncurry, hΦ]
        rw [enorm_smul, Real.enorm_of_nonneg (mul_nonneg (heatKernel2_nonneg hα _)
          (heatKernel2_nonneg hβ _)), ENNReal.ofReal_mul (heatKernel2_nonneg hα _), mul_assoc]
      simp_rw [he]
      have hm : AEMeasurable (fun q : Plane × Plane => ENNReal.ofReal (heatKernel2 α q.1) *
          (ENNReal.ofReal (heatKernel2 β (q.2 - q.1)) * ‖f (z - q.2)‖ₑ))
          ((volume : Measure Plane).prod volume) := by
        have h1 : Measurable fun q : Plane × Plane => ENNReal.ofReal (heatKernel2 α q.1) :=
          (measurable_ofReal_heatKernel2 α).comp measurable_fst
        have h2 : Measurable fun q : Plane × Plane =>
            ENNReal.ofReal (heatKernel2 β (q.2 - q.1)) :=
          (measurable_ofReal_heatKernel2 β).comp (measurable_snd.sub measurable_fst)
        exact h1.aemeasurable.mul (h2.aemeasurable.mul
          (aestronglyMeasurable_comp_sub hf z).enorm.comp_snd)
      rw [lintegral_prod _ hm, lintegral_lintegral_heatKernel hα hβ hf z]
      exact lt_top_iff_ne_top.2 hfin
  calc ∫ w, heatKernel2 α w • heat β f (z - w) = ∫ w, ∫ y, Φ w y :=
        integral_congr_ae (Eventually.of_forall h1)
    _ = ∫ y, ∫ w, Φ w y := integral_integral_swap hint
    _ = ∫ y, heatKernel2 (α + β) y • f (z - y) := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only [hΦ]
        rw [integral_smul_const]
        congr 1
        have h2 := integral_heatKernel2_conv hβ hα y
        rw [add_comm] at h2
        rw [← h2]
        refine integral_congr_ae (Eventually.of_forall fun w => ?_)
        simp only
        ring

/-! ## Linearity, congruence, periodicity -/

/-- Linearity of `e^{θΔ}` at a point where both absolute integrals are finite. -/
theorem heat_add_smul {θ : ℝ} (hθ : 0 < θ) {f g : Plane → Plane}
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume) (a b : ℝ)
    {z : Plane} (hff : heatAbs θ f z ≠ ⊤) (hgf : heatAbs θ g z ≠ ⊤) :
    heat θ (fun x => a • f x + b • g x) z = a • heat θ f z + b • heat θ g z := by
  have h1 : Integrable (fun w => a • (heatKernel2 θ w • f (z - w))) :=
    (integrable_heat_integrand hθ hf hff).smul a
  have h2 : Integrable (fun w => b • (heatKernel2 θ w • g (z - w))) :=
    (integrable_heat_integrand hθ hg hgf).smul b
  rw [heat_apply_of_pos hθ, heat_apply_of_pos hθ, heat_apply_of_pos hθ, ← integral_smul,
    ← integral_smul, ← integral_add h1 h2]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only [smul_add]
  rw [smul_comm (heatKernel2 θ w) a, smul_comm (heatKernel2 θ w) b]

/-- `e^{θΔ} f` only depends on the a.e. class of `f` (`θ > 0`). -/
theorem heat_congr_ae {θ : ℝ} (hθ : 0 < θ) {f f' : Plane → Plane} (h : f =ᵐ[volume] f') :
    heat θ f = heat θ f' := by
  funext z
  rw [heat_apply_of_pos hθ, heat_apply_of_pos hθ]
  refine integral_congr_ae ?_
  have h' := (quasiMeasurePreserving_sub_left_of_right_invariant (volume : Measure Plane) z).ae h
  filter_upwards [h'] with w hw
  rw [hw]

/-- The absolute heat integral of a periodic field is periodic. -/
theorem heatAbs_periodic {c θ : ℝ} {f : Plane → Plane} (hf : IsQPeriodic c f) :
    IsQPeriodic c (heatAbs θ f) := by
  intro z
  unfold heatAbs
  refine lintegral_congr fun w => ?_
  have hz : ((z.1 + c, z.2) : Plane) - w = ((z - w).1 + c, (z - w).2) := by
    ext
    · simp only [Prod.fst_sub]
      ring
    · simp
  rw [hz, hf]

/-- The Duhamel integral of periodic fields is periodic. -/
theorem duhamel_periodic {ν c : ℝ} {h : ℝ → Plane → Plane} (hh : ∀ t, IsQPeriodic c (h t))
    (s : ℝ) : IsQPeriodic c (duhamel ν h s) := by
  intro z
  refine setIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
  exact heat_periodic (hh t) z

end UnforcedLeray.B0289
