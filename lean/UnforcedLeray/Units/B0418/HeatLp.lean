import UnforcedLeray.Analysis.AncientLocalization.FreeEvolution
import NonUniqueEuler.P.Infra.ConvMinkowski.Minkowski

/-!
# B0418 helper: the literal heat flow on spatial `L^p`, `1 ≤ p < ∞`

Blueprint unit B0418 (`eq:free-stress-7`, `paper/main.tex` lines 7411--7427) uses
the heat semigroup `e^{tΔ}` on spatial `L^q`. The library constructs the literal
Gaussian Bochner integral `Heat.average` and the flow `Heat.flow` and proves its
properties on `L²`. This file extends the needed facts to every `L^p`, `1 ≤ p < ∞`:
pointwise convergence of the heat integral, the Young/Minkowski contraction,
the pointwise semigroup law, linearity, and the intertwining with dilations
(`D_λ H_t = H_{t/λ²} D_λ` in the notation of the blueprint proof outline).

The semigroup proof is adapted from `lean/UnforcedLeray/Analysis/Heat/Semigroup.lean`
(`average_add_time`), with the `L²`-to-uniform bound replaced by the elementary
domination `k ‖f‖ ≤ k + N ‖f‖^p`. The contraction proof is adapted from
`lean/UnforcedLeray/Analysis/Heat/ConvolutionL2.lean` (`eLpNorm_convolution_le`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology Convolution

namespace UnforcedLeray.B0418

/-- Elementary domination `a ≤ 1 + a^q` for `a ≥ 0`, `q ≥ 1`. -/
theorem le_one_add_rpow {a q : ℝ} (ha : 0 ≤ a) (hq : 1 ≤ q) : a ≤ 1 + a ^ q := by
  rcases le_total a 1 with h | h
  · have := Real.rpow_nonneg ha q
    linarith
  · have h2 : a ^ (1 : ℝ) ≤ a ^ q := Real.rpow_le_rpow_of_exponent_le h hq
    rw [Real.rpow_one] at h2
    linarith

theorem one_le_toReal {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) : 1 ≤ p.toReal := by
  have := ENNReal.toReal_mono hp hp1
  simpa using this

theorem ne_zero_of_one_le {p : ℝ≥0∞} (hp1 : 1 ≤ p) : p ≠ 0 :=
  (lt_of_lt_of_le zero_lt_one hp1).ne'

/-- The sup bound of the heat kernel. -/
abbrev heatSup (t : ℝ) : ℝ := Heat.Gaussian.normalization (4 * t)

theorem kernel_le_heatSup {t : ℝ} (ht : 0 < t) (y : Space) : Heat.kernel t y ≤ heatSup t :=
  Heat.Gaussian.kernel_le_normalization (by positivity) y

variable {p : ℝ≥0∞}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Pointwise domination of the heat integrand by an integrable function. -/
theorem norm_integrand_le {t : ℝ} (ht : 0 < t) {f : Space → V} (hp1 : 1 ≤ p)
    (hp : p ≠ ∞) (x y : Space) :
    ‖Heat.kernel t y • f (x - y)‖ ≤
      Heat.kernel t y + heatSup t * ‖f (x - y)‖ ^ p.toReal := by
  rw [norm_smul, Real.norm_of_nonneg (Heat.kernel_nonneg ht y)]
  have hk := Heat.kernel_nonneg ht y
  have hkN := kernel_le_heatSup ht y
  have h1 := le_one_add_rpow (norm_nonneg (f (x - y))) (one_le_toReal hp1 hp)
  have hpow : 0 ≤ ‖f (x - y)‖ ^ p.toReal := Real.rpow_nonneg (norm_nonneg _) _
  calc Heat.kernel t y * ‖f (x - y)‖
      ≤ Heat.kernel t y * (1 + ‖f (x - y)‖ ^ p.toReal) :=
        mul_le_mul_of_nonneg_left h1 hk
    _ = Heat.kernel t y + Heat.kernel t y * ‖f (x - y)‖ ^ p.toReal := by ring
    _ ≤ Heat.kernel t y + heatSup t * ‖f (x - y)‖ ^ p.toReal := by
        gcongr

/-- For an `L^p` field the heat integral converges absolutely at every point. -/
theorem heat_integrand_integrable {t : ℝ} (ht : 0 < t) {f : Space → V}
    (hp1 : 1 ≤ p) (hp : p ≠ ∞) (hf : MemLp f p volume) (x : Space) :
    Integrable (fun y : Space => Heat.kernel t y • f (x - y)) := by
  have hmp := Measure.measurePreserving_sub_left (volume : Measure Space) x
  have hs : MemLp (fun y : Space => f (x - y)) p volume := hf.comp_measurePreserving hmp
  have hpow : Integrable (fun y : Space => ‖f (x - y)‖ ^ p.toReal) :=
    hs.integrable_norm_rpow (ne_zero_of_one_le hp1) hp
  refine ((Heat.kernel_integrable ht).add (hpow.const_mul (heatSup t))).mono' ?_ ?_
  · exact (Heat.Gaussian.kernel_smooth (4 * t)).continuous.aestronglyMeasurable.smul
      hs.aestronglyMeasurable
  · exact Eventually.of_forall (fun y => norm_integrand_le ht hp1 hp x y)

/-- Uniform bound of the scalar heat average of `‖f‖`. -/
theorem average_norm_le {t : ℝ} (ht : 0 < t) {f : SpatialField}
    (hp1 : 1 ≤ p) (hp : p ≠ ∞) (hf : MemLp f p volume) (x : Space) :
    Heat.average t (fun z => ‖f z‖) x ≤
      1 + heatSup t * ∫ z : Space, ‖f z‖ ^ p.toReal := by
  have hmp := Measure.measurePreserving_sub_left (volume : Measure Space) x
  have hs : MemLp (fun y : Space => f (x - y)) p volume := hf.comp_measurePreserving hmp
  have hpow : Integrable (fun y : Space => ‖f (x - y)‖ ^ p.toReal) :=
    hs.integrable_norm_rpow (ne_zero_of_one_le hp1) hp
  have hint := heat_integrand_integrable ht hp1 hp hf.norm x
  unfold Heat.average
  calc (∫ y : Space, Heat.kernel t y • ‖f (x - y)‖)
      ≤ ∫ y : Space, (Heat.kernel t y + heatSup t * ‖f (x - y)‖ ^ p.toReal) := by
        apply integral_mono hint ((Heat.kernel_integrable ht).add (hpow.const_mul _))
        intro y
        have := norm_integrand_le ht hp1 hp (f := fun z => ‖f z‖) x y
        simp only [norm_norm] at this
        exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using this)
    _ = 1 + heatSup t * ∫ z : Space, ‖f z‖ ^ p.toReal := by
        rw [integral_add (Heat.kernel_integrable ht) (hpow.const_mul _), Heat.integral_kernel ht,
          integral_const_mul]
        congr 2
        exact integral_sub_left_eq_self (fun z => ‖f z‖ ^ p.toReal) volume x

/-- The nested norm convolution converges, by the uniform bound. -/
theorem norm_average_outer_integrable {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    {f : SpatialField} (hp1 : 1 ≤ p) (hp : p ≠ ∞) (hf : MemLp f p volume) (x : Space) :
    Integrable (fun y : Space => Heat.kernel s y * Heat.average t (fun z => ‖f z‖) (x - y)) := by
  let C : ℝ := 1 + heatSup t * ∫ z : Space, ‖f z‖ ^ p.toReal
  have hm := (Heat.average_aestronglyMeasurable t hf.norm.aestronglyMeasurable).comp_quasiMeasurePreserving
    (Measure.measurePreserving_sub_left (volume : Measure Space) x).quasiMeasurePreserving
  apply ((Heat.kernel_integrable hs).mul_const C).mono'
    ((Heat.kernel_integrable hs).aestronglyMeasurable.mul hm)
  filter_upwards [] with y
  change ‖Heat.kernel s y * Heat.average t (fun z => ‖f z‖) (x - y)‖ ≤ Heat.kernel s y * C
  have hnn : 0 ≤ Heat.average t (fun z => ‖f z‖) (x - y) := by
    unfold Heat.average
    exact integral_nonneg (fun z => smul_nonneg (Heat.kernel_nonneg ht z) (norm_nonneg _))
  rw [norm_mul, Real.norm_of_nonneg (Heat.kernel_nonneg hs y), Real.norm_of_nonneg hnn]
  exact mul_le_mul_of_nonneg_left (average_norm_le ht hp1 hp hf (x - y))
    (Heat.kernel_nonneg hs y)

/-- Positive-time semigroup law of the literal heat integral on `L^p`, at every point. -/
theorem average_add_time {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    {f : SpatialField} (hp1 : 1 ≤ p) (hp : p ≠ ∞) (hf : MemLp f p volume) :
    Heat.average (s + t) f = Heat.average s (Heat.average t f) := by
  let MM : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.mul ℝ ℝ
  let SM : ℝ →L[ℝ] Space →L[ℝ] Space := ContinuousLinearMap.lsmul ℝ ℝ
  have hks : (fun y => ‖Heat.kernel s y‖) = Heat.kernel s := by
    funext y
    exact Real.norm_of_nonneg (Heat.kernel_nonneg hs y)
  have hkt : (fun y => ‖Heat.kernel t y‖) = Heat.kernel t := by
    funext y
    exact Real.norm_of_nonneg (Heat.kernel_nonneg ht y)
  have hfg : ∀ᵐ y : Space, ConvolutionExistsAt (Heat.kernel s) (Heat.kernel t) y MM volume :=
    Eventually.of_forall (fun y => Heat.kernel_product_integrable hs ht y)
  have hgk : ∀ᵐ y : Space,
      ConvolutionExistsAt (fun z => ‖Heat.kernel t z‖) (fun z => ‖f z‖) y MM volume := by
    rw [hkt]
    exact Eventually.of_forall (fun y => heat_integrand_integrable ht hp1 hp hf.norm y)
  have hkconv : (Heat.kernel s ⋆[MM] Heat.kernel t) = Heat.kernel (s + t) :=
    funext (fun x => Heat.integral_kernel_product hs ht x)
  funext x
  have hfgk : ConvolutionExistsAt (fun z => ‖Heat.kernel s z‖)
      ((fun z => ‖Heat.kernel t z‖) ⋆[MM] (fun z => ‖f z‖)) x MM volume := by
    rw [hks, hkt]
    exact norm_average_outer_integrable hs ht hp1 hp hf x
  have ha := MeasureTheory.convolution_assoc MM SM SM SM
    (fun a b v => mul_smul a b v)
    (Heat.kernel_integrable hs).aestronglyMeasurable
    (Heat.kernel_integrable ht).aestronglyMeasurable hf.aestronglyMeasurable hfg hgk hfgk
  rw [hkconv] at ha
  exact ha

/-- The semigroup law of the literal heat flow on `L^p` for nonnegative times. -/
theorem flow_add_time {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    {f : SpatialField} (hp1 : 1 ≤ p) (hp : p ≠ ∞) (hf : MemLp f p volume) :
    Heat.flow (Heat.flow f t) s = Heat.flow f (s + t) := by
  rcases hs.eq_or_lt with rfl | hs'
  · simp
  rcases ht.eq_or_lt with rfl | ht'
  · simp
  rw [Heat.flow_pos f ht', Heat.flow_pos _ hs', Heat.flow_pos f (add_pos hs' ht'),
    average_add_time hs' ht' hp1 hp hf]

/-- Linearity of the heat flow on `L^p` (subtraction). -/
theorem flow_sub {f g : SpatialField} (hp1 : 1 ≤ p) (hp : p ≠ ∞)
    (hf : MemLp f p volume) (hg : MemLp g p volume) (t : ℝ) :
    Heat.flow (f - g) t = Heat.flow f t - Heat.flow g t := by
  by_cases ht : 0 < t
  · rw [Heat.flow_pos _ ht, Heat.flow_pos _ ht, Heat.flow_pos _ ht]
    funext x
    simp only [Heat.average, Pi.sub_apply, smul_sub]
    exact integral_sub (heat_integrand_integrable ht hp1 hp hf x)
      (heat_integrand_integrable ht hp1 hp hg x)
  · rw [Heat.flow_nonpos _ (not_lt.mp ht), Heat.flow_nonpos _ (not_lt.mp ht),
      Heat.flow_nonpos _ (not_lt.mp ht)]

/-- Homogeneity of the heat flow. -/
theorem flow_smul (c : ℝ) (f : SpatialField) (t : ℝ) :
    Heat.flow (c • f) t = c • Heat.flow f t := by
  by_cases ht : 0 < t
  · rw [Heat.flow_pos _ ht, Heat.flow_pos _ ht, Heat.average_smul]
  · rw [Heat.flow_nonpos _ (not_lt.mp ht), Heat.flow_nonpos _ (not_lt.mp ht)]

/-- `‖k_t‖_{L¹} = 1`. -/
theorem eLpNorm_kernel_one {t : ℝ} (ht : 0 < t) :
    eLpNorm (Heat.kernel t) 1 volume = 1 := by
  rw [eLpNorm_one_eq_lintegral_enorm]
  have he : (fun y => ‖Heat.kernel t y‖ₑ) = fun y => ENNReal.ofReal (Heat.kernel t y) := by
    funext y
    exact Real.enorm_eq_ofReal (Heat.kernel_nonneg ht y)
  rw [he, ← ofReal_integral_eq_lintegral_ofReal (Heat.kernel_integrable ht)
    (Eventually.of_forall (fun y => Heat.kernel_nonneg ht y)), Heat.integral_kernel ht,
    ENNReal.ofReal_one]

/-- Young's `L¹ * L^p` contraction of the literal heat integral (Minkowski). -/
theorem eLpNorm_average_le {t : ℝ} (ht : 0 < t) {f : SpatialField}
    (hp1 : 1 ≤ p) (hp : p ≠ ∞) (hf : MemLp f p volume) :
    eLpNorm (Heat.average t f) p volume ≤ eLpNorm f p volume := by
  have hjoint : AEStronglyMeasurable
      (fun z : Space × Space => Heat.kernel t z.2 • f (z.1 - z.2))
      ((volume : Measure Space).prod volume) :=
    (Heat.kernel_integrable ht).aestronglyMeasurable.convolution_integrand
      (ContinuousLinearMap.lsmul ℝ ℝ) hf.aestronglyMeasurable
  have hM := NonUniqueEuler.Conv.eLpNorm_integral_le
    (F := fun x y => Heat.kernel t y • f (x - y)) hjoint hp1 hp
  refine hM.trans (le_of_eq ?_)
  calc
    (∫⁻ y : Space, eLpNorm (fun x => Heat.kernel t y • f (x - y)) p volume) =
        ∫⁻ y : Space, ‖Heat.kernel t y‖ₑ * eLpNorm f p volume := by
      apply lintegral_congr
      intro y
      change eLpNorm (Heat.kernel t y • (fun x => f (x - y))) p volume = _
      rw [eLpNorm_const_smul]
      congr 1
      exact eLpNorm_comp_measurePreserving hf.aestronglyMeasurable
        (measurePreserving_sub_right (volume : Measure Space) y)
    _ = (∫⁻ y : Space, ‖Heat.kernel t y‖ₑ) * eLpNorm f p volume :=
      lintegral_mul_const' _ _ hf.2.ne
    _ = eLpNorm f p volume := by
      rw [← eLpNorm_one_eq_lintegral_enorm, eLpNorm_kernel_one ht, one_mul]

theorem average_memLp {t : ℝ} (ht : 0 < t) {f : SpatialField}
    (hp1 : 1 ≤ p) (hp : p ≠ ∞) (hf : MemLp f p volume) :
    MemLp (Heat.average t f) p volume :=
  ⟨Heat.average_aestronglyMeasurable t hf.aestronglyMeasurable,
    (eLpNorm_average_le ht hp1 hp hf).trans_lt hf.2⟩

theorem flow_memLp {f : SpatialField} (hp1 : 1 ≤ p) (hp : p ≠ ∞)
    (hf : MemLp f p volume) (t : ℝ) : MemLp (Heat.flow f t) p volume := by
  by_cases ht : 0 < t
  · rw [Heat.flow_pos _ ht]
    exact average_memLp ht hp1 hp hf
  · rw [Heat.flow_nonpos _ (not_lt.mp ht)]
    exact hf

/-- The heat flow is an `L^p` contraction at every time. -/
theorem eLpNorm_flow_le {f : SpatialField} (hp1 : 1 ≤ p) (hp : p ≠ ∞)
    (hf : MemLp f p volume) (t : ℝ) :
    eLpNorm (Heat.flow f t) p volume ≤ eLpNorm f p volume := by
  by_cases ht : 0 < t
  · rw [Heat.flow_pos _ ht]
    exact eLpNorm_average_le ht hp1 hp hf
  · rw [Heat.flow_nonpos _ (not_lt.mp ht)]

/-! ### Dilation intertwining -/

/-- Gaussian scaling: `G_{b²s}(b y) = b⁻³ G_s(y)`. -/
theorem gaussian_scale {b s : ℝ} (hb : 0 < b) (hs : 0 < s) (y : Space) :
    Heat.Gaussian.kernel (b ^ 2 * s) (b • y) = (b ^ 3)⁻¹ * Heat.Gaussian.kernel s y := by
  have hn : Heat.Gaussian.normalization (b ^ 2 * s) =
      (b ^ 3)⁻¹ * Heat.Gaussian.normalization s := by
    rw [Heat.Gaussian.normalization, Heat.Gaussian.normalization,
      show Real.pi * (b ^ 2 * s) = b ^ 2 * (Real.pi * s) by ring,
      Real.mul_rpow (sq_nonneg b) (by positivity),
      ← Real.rpow_natCast b 2, ← Real.rpow_mul hb.le]
    congr 1
    rw [show ((2 : ℕ) : ℝ) * (-(3 : ℝ) / 2) = -((3 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg hb.le, Real.rpow_natCast]
  have he : -(b ^ 2 * s)⁻¹ * ‖b • y‖ ^ 2 = -s⁻¹ * ‖y‖ ^ 2 := by
    rw [norm_smul, Real.norm_of_nonneg hb.le, mul_pow]
    field_simp
  rw [Heat.Gaussian.kernel, hn, he, Heat.Gaussian.kernel]
  ring

/-- Heat-kernel scaling: `k_t(y) = b³ k_{b² t}(b y)`. -/
theorem kernel_scale {b t : ℝ} (hb : 0 < b) (ht : 0 < t) (y : Space) :
    Heat.kernel t y = b ^ 3 * Heat.kernel (b ^ 2 * t) (b • y) := by
  have h := gaussian_scale hb (by positivity : 0 < 4 * t) y
  rw [Heat.kernel, Heat.kernel, show 4 * (b ^ 2 * t) = b ^ 2 * (4 * t) by ring, h]
  have hb3 : b ^ 3 ≠ 0 := pow_ne_zero _ hb.ne'
  field_simp

/-- Intertwining of the heat integral with a positive dilation. -/
theorem average_comp_smul {b t : ℝ} (hb : 0 < b) (ht : 0 < t) (f : SpatialField) (x : Space) :
    Heat.average t (fun z => f (b • z)) x = Heat.average (b ^ 2 * t) f (b • x) := by
  let G : Space → Space := fun w => Heat.kernel (b ^ 2 * t) w • f (b • x - w)
  have hJac := Measure.integral_comp_smul_of_nonneg (volume : Measure Space) G b (hR := hb.le)
  have hd : Module.finrank ℝ Space = 3 := by simp [Space]
  rw [hd] at hJac
  unfold Heat.average
  have hl : (fun y : Space => Heat.kernel t y • f (b • (x - y))) =
      fun y : Space => b ^ 3 • G (b • y) := by
    funext y
    simp only [G, smul_sub]
    rw [kernel_scale hb ht y, mul_smul]
  rw [hl, integral_smul, hJac, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hb.ne'), one_smul]

/-- Intertwining of the heat flow with a positive dilation. -/
theorem flow_comp_smul {b : ℝ} (hb : 0 < b) (f : SpatialField) (t : ℝ) :
    Heat.flow (fun z => f (b • z)) t = fun x => Heat.flow f (b ^ 2 * t) (b • x) := by
  by_cases ht : 0 < t
  · rw [Heat.flow_pos _ ht, Heat.flow_pos _ (by positivity)]
    funext x
    exact average_comp_smul hb ht f x
  · have ht' : b ^ 2 * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg b) (not_lt.mp ht)
    rw [Heat.flow_nonpos _ (not_lt.mp ht), Heat.flow_nonpos _ ht']

end UnforcedLeray.B0418
