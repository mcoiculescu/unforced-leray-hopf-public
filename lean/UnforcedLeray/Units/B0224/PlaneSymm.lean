import UnforcedLeray.Units.B0224.PlaneHeat

/-!
# B0224 helper: the cylinder heat is symmetric on `L²` of one period strip

Blueprint unit B0224 (label `eq:st18-t00117`), `paper/main.tex` lines 3370–3379; proof outline
"the adjoint follows by the same substitution and self-adjointness of heat". For periodic
`u, v` with `∫_strip |u|², ∫_strip |v|² < ∞`,

  `∫_strip ⟨e^{θΔ}u, v⟩ = ∫_strip ⟨u, e^{θΔ}v⟩`        (`integral_strip_inner_planeHeat`).

Proof: Fubini on `strip × ℝ²` (the kernel `G_θ(y)⟨u(x - y), v(x)⟩` is integrable, dominated by
`G_θ(y)(|u(x - y)|² + |v(x)|²)`, whose integral is `‖u‖² + ‖v‖²` by `lintegral_strip_gauss`),
the periodic translation `x ↦ x + y` (`integral_strip_comp_add`) and `G_θ(-y) = G_θ(y)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal InnerProductSpace

namespace UnforcedLeray.B0224

open UnforcedLeray.Gaussian (Euc gaussKernel)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- `ab ≤ a² + b²` in `[0, ∞]`. -/
theorem mul_le_sq_add_sq (a b : ℝ≥0∞) : a * b ≤ a ^ 2 + b ^ 2 := by
  rcases le_total a b with h | h
  · calc a * b ≤ b * b := by gcongr
      _ = b ^ 2 := (sq b).symm
      _ ≤ a ^ 2 + b ^ 2 := le_add_self
  · calc a * b ≤ a * a := by gcongr
      _ = a ^ 2 := (sq a).symm
      _ ≤ a ^ 2 + b ^ 2 := le_self_add

/-- `|⟨a, b⟩| ≤ |a| |b|` in `[0, ∞]`. -/
theorem enorm_inner_le (a b : E) : ‖⟪a, b⟫_ℝ‖ₑ ≤ ‖a‖ₑ * ‖b‖ₑ := by
  calc ‖⟪a, b⟫_ℝ‖ₑ = ENNReal.ofReal ‖⟪a, b⟫_ℝ‖ := (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (‖a‖ * ‖b‖) := ENNReal.ofReal_le_ofReal (norm_inner_le_norm a b)
    _ = ‖a‖ₑ * ‖b‖ₑ := by rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm]

/-- The symmetric kernel `G_θ(y) ⟨u(x - y), v(x)⟩` is integrable on `strip × ℝ²`. -/
theorem integrable_heatKernel_inner {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ) {u v : ℝ × ℝ → E}
    (hu : StronglyMeasurable u) (hv : StronglyMeasurable v) (hup : Cyl.IsPeriodic c u)
    (hu2 : ∫⁻ x in strip c, ‖u x‖ₑ ^ 2 < ∞) (hv2 : ∫⁻ x in strip c, ‖v x‖ₑ ^ 2 < ∞) :
    Integrable (fun q : (ℝ × ℝ) × Euc 2 =>
      gaussKernel 2 θ q.2 * ⟪u (q.1 - planeι q.2), v q.1⟫_ℝ)
      ((volume.restrict (strip c)).prod volume) := by
  have hum : StronglyMeasurable fun q : (ℝ × ℝ) × Euc 2 => u (q.1 - planeι q.2) :=
    hu.comp_measurable (measurable_fst.sub (measurable_planeι.comp measurable_snd))
  have hvm : StronglyMeasurable fun q : (ℝ × ℝ) × Euc 2 => v q.1 :=
    hv.comp_measurable measurable_fst
  have hGm : StronglyMeasurable fun q : (ℝ × ℝ) × Euc 2 => gaussKernel 2 θ q.2 :=
    ((Gaussian.continuous_gaussKernel θ).comp continuous_snd).stronglyMeasurable
  refine ⟨(hGm.mul (hum.inner hvm)).aestronglyMeasurable, ?_⟩
  have hA : Measurable fun q : (ℝ × ℝ) × Euc 2 =>
      ENNReal.ofReal (gaussKernel 2 θ q.2) * ‖u (q.1 - planeι q.2)‖ₑ ^ 2 :=
    ((measurable_ofReal_gauss θ).comp measurable_snd).mul (hum.enorm.pow_const 2)
  have hB : Measurable fun q : (ℝ × ℝ) × Euc 2 =>
      ENNReal.ofReal (gaussKernel 2 θ q.2) * ‖v q.1‖ₑ ^ 2 :=
    ((measurable_ofReal_gauss θ).comp measurable_snd).mul (hvm.enorm.pow_const 2)
  have hle : ∫⁻ q, ‖gaussKernel 2 θ q.2 * ⟪u (q.1 - planeι q.2), v q.1⟫_ℝ‖ₑ
      ∂((volume.restrict (strip c)).prod volume) ≤
      ∫⁻ q, (ENNReal.ofReal (gaussKernel 2 θ q.2) * ‖u (q.1 - planeι q.2)‖ₑ ^ 2 +
        ENNReal.ofReal (gaussKernel 2 θ q.2) * ‖v q.1‖ₑ ^ 2)
      ∂((volume.restrict (strip c)).prod volume) := by
    refine lintegral_mono fun q => ?_
    rw [enorm_mul, Real.enorm_of_nonneg (Gaussian.gaussKernel_nonneg hθ _), ← mul_add]
    gcongr
    calc ‖⟪u (q.1 - planeι q.2), v q.1⟫_ℝ‖ₑ ≤ ‖u (q.1 - planeι q.2)‖ₑ * ‖v q.1‖ₑ :=
          enorm_inner_le _ _
      _ ≤ _ := mul_le_sq_add_sq _ _
  refine lt_of_le_of_lt hle ?_
  rw [lintegral_add_left hA, lintegral_prod _ hA.aemeasurable, lintegral_prod _ hB.aemeasurable]
  have h1 : ∫⁻ x in strip c, ∫⁻ y : Euc 2,
      ENNReal.ofReal (gaussKernel 2 θ y) * ‖u (x - planeι y)‖ₑ ^ 2 =
        ∫⁻ x in strip c, ‖u x‖ₑ ^ 2 :=
    lintegral_strip_gauss hc hθ (hu.enorm.pow_const 2)
      (fun z => by simp only [hup z])
  have h2 : ∫⁻ x in strip c, ∫⁻ y : Euc 2, ENNReal.ofReal (gaussKernel 2 θ y) * ‖v x‖ₑ ^ 2 =
      ∫⁻ x in strip c, ‖v x‖ₑ ^ 2 := by
    refine lintegral_congr fun x => ?_
    rw [lintegral_mul_const _ (measurable_ofReal_gauss θ), lintegral_ofReal_gauss hθ, one_mul]
  rw [h1, h2]
  exact ENNReal.add_lt_top.2 ⟨hu2, hv2⟩

/-- For a.e. `x` in the strip, `⟨e^{θΔ}u(x), v(x)⟩ = ∫ G_θ(y) ⟨u(x - y), v(x)⟩ dy`. -/
theorem ae_inner_planeHeat {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ) {u : ℝ × ℝ → E}
    (hu : StronglyMeasurable u) (hup : Cyl.IsPeriodic c u)
    (hu2 : ∫⁻ x in strip c, ‖u x‖ₑ ^ 2 < ∞) (v : ℝ × ℝ → E) :
    ∀ᵐ x ∂(volume.restrict (strip c)), ⟪planeHeat θ u x, v x⟫_ℝ =
      ∫ y : Euc 2, gaussKernel 2 θ y * ⟪u (x - planeι y), v x⟫_ℝ := by
  have hm : Measurable fun x : ℝ × ℝ => ∫⁻ y : Euc 2,
      ENNReal.ofReal (gaussKernel 2 θ y) * ‖u (x - planeι y)‖ₑ ^ 2 :=
    (((measurable_ofReal_gauss θ).comp measurable_snd).mul
      ((hu.comp_measurable (measurable_fst.sub
        (measurable_planeι.comp measurable_snd))).enorm.pow_const 2)).lintegral_prod_right'
  have hfin : ∀ᵐ x ∂(volume.restrict (strip c)), ∫⁻ y : Euc 2,
      ENNReal.ofReal (gaussKernel 2 θ y) * ‖u (x - planeι y)‖ₑ ^ 2 < ∞ := by
    refine ae_lt_top hm ?_
    rw [lintegral_strip_gauss hc hθ (hu.enorm.pow_const 2)
      (fun z => by simp only [hup z])]
    exact hu2.ne
  filter_upwards [hfin] with x hx
  have hint : Integrable fun y : Euc 2 => gaussKernel 2 θ y • u (x - planeι y) :=
    integrable_gauss_smul hθ
    (hu.comp_measurable (measurable_const.sub measurable_planeι)).aestronglyMeasurable hx
  rw [planeHeat_of_pos hθ, real_inner_comm, ← integral_inner hint]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [real_inner_smul_right, real_inner_comm]

/-- **The cylinder heat is symmetric** on `L²` of one period strip, for periodic fields. -/
theorem integral_strip_inner_planeHeat {c θ : ℝ} (hc : 0 < c) {u v : ℝ × ℝ → E}
    (hu : StronglyMeasurable u) (hv : StronglyMeasurable v)
    (hup : Cyl.IsPeriodic c u) (hvp : Cyl.IsPeriodic c v)
    (hu2 : ∫⁻ x in strip c, ‖u x‖ₑ ^ 2 < ∞) (hv2 : ∫⁻ x in strip c, ‖v x‖ₑ ^ 2 < ∞) :
    ∫ x in strip c, ⟪planeHeat θ u x, v x⟫_ℝ = ∫ x in strip c, ⟪u x, planeHeat θ v x⟫_ℝ := by
  by_cases hθ : 0 < θ
  swap
  · simp only [planeHeat_of_nonpos (not_lt.1 hθ)]
  have hK := integrable_heatKernel_inner hc hθ hu hv hup hu2 hv2
  have hK' := integrable_heatKernel_inner hc hθ hv hu hvp hv2 hu2
  calc ∫ x in strip c, ⟪planeHeat θ u x, v x⟫_ℝ
      = ∫ x in strip c, ∫ y : Euc 2, gaussKernel 2 θ y * ⟪u (x - planeι y), v x⟫_ℝ :=
        integral_congr_ae (ae_inner_planeHeat hc hθ hu hup hu2 v)
    _ = ∫ y : Euc 2, ∫ x in strip c, gaussKernel 2 θ y * ⟪u (x - planeι y), v x⟫_ℝ :=
        integral_integral_swap hK
    _ = ∫ y : Euc 2, ∫ x in strip c, gaussKernel 2 θ y * ⟪u x, v (x + planeι y)⟫_ℝ := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        have hper : Cyl.IsPeriodic c fun x => gaussKernel 2 θ y * ⟪u (x - planeι y), v x⟫_ℝ := by
          intro z
          have h1 := isPeriodic_comp_sub hup (planeι y) z
          simp only at h1
          simp only [h1, hvp z]
        have := integral_strip_comp_add hc hper (planeι y)
        simp only [add_sub_cancel_right] at this
        exact this.symm
    _ = ∫ y : Euc 2, ∫ x in strip c, gaussKernel 2 θ y * ⟪u x, v (x - planeι y)⟫_ℝ := by
        rw [← integral_neg_eq_self]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only [Gaussian.gaussKernel_neg, map_neg, sub_eq_add_neg]
    _ = ∫ x in strip c, ∫ y : Euc 2, gaussKernel 2 θ y * ⟪u x, v (x - planeι y)⟫_ℝ := by
        refine (integral_integral_swap (f := fun x y =>
          gaussKernel 2 θ y * ⟪u x, v (x - planeι y)⟫_ℝ) ?_).symm
        refine hK'.congr (Eventually.of_forall fun q => ?_)
        change _ = gaussKernel 2 θ q.2 * ⟪u q.1, v (q.1 - planeι q.2)⟫_ℝ
        simp only
        rw [real_inner_comm (u q.1)]
    _ = ∫ x in strip c, ⟪u x, planeHeat θ v x⟫_ℝ := by
        refine integral_congr_ae ?_
        filter_upwards [ae_inner_planeHeat hc hθ hv hvp hv2 u] with x hx
        rw [real_inner_comm, hx]
        simp only [real_inner_comm]

end UnforcedLeray.B0224
