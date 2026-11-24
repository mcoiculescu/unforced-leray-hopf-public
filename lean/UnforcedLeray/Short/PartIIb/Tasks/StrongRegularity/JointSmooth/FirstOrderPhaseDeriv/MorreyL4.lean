import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S3_1_1

/-!
# `PartII-b:S3/1/1/1` (`Tasks/StrongRegularity/JointSmooth/FirstOrderPhaseDeriv/MorreyL4.lean`)

Source of record: `the November 2 reference manuscript`
(SP), lines 2557-2562: 3D Morrey/Sobolev embedding `W^{1,4}(ℝ³) ↪ L^∞(ℝ³)` on smooth spatial
vector fields (`SmoothMorreyL4FieldBound`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff BigOperators

namespace UnforcedLeray.Short.IIb

namespace MorreyL4Sub

abbrev R3 := (ℝ × ℝ) × ℝ

/-! ## 1. One-dimensional mean oscillation -/

theorem abs_sub_le_integral_deriv {φ φ' : ℝ → ℝ} (hd : ∀ x, HasDerivAt φ (φ' x) x)
    (hc : Continuous φ') {a b s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    |φ s - φ t| ≤ ∫ x in Icc a b, |φ' x| := by
  have hftc : φ s - φ t = ∫ x in t..s, φ' x :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
      (hc.intervalIntegrable _ _)).symm
  have hsub : Set.uIoc t s ⊆ Icc a b := by
    intro x hx
    rcases Set.mem_uIoc.1 hx with h | h
    · exact ⟨ht.1.trans h.1.le, h.2.trans hs.2⟩
    · exact ⟨hs.1.trans h.1.le, h.2.trans ht.2⟩
  rw [hftc]
  have h1 := intervalIntegral.norm_integral_le_integral_norm_uIoc (f := φ') (a := t) (b := s)
    (μ := volume)
  simp only [Real.norm_eq_abs] at h1
  exact h1.trans (setIntegral_mono_set hc.abs.integrableOn_Icc
    (ae_of_all _ fun x => abs_nonneg _) hsub.eventuallyLE)

theorem abs_avg_sub_avg_le {φ φ' : ℝ → ℝ} (hd : ∀ x, HasDerivAt φ (φ' x) x)
    (hc : Continuous φ') {s s' : ℝ} (hs' : 0 < s') (hss' : s' ≤ s) :
    |s'⁻¹ * (∫ x in Icc 0 s', φ x) - s⁻¹ * ∫ x in Icc 0 s, φ x| ≤
      ∫ x in Icc 0 s, |φ' x| := by
  have hφ : Continuous φ := continuous_iff_continuousAt.2 fun x => (hd x).continuousAt
  have hs : 0 < s := lt_of_lt_of_le hs' hss'
  obtain ⟨xm, hxm, hmin⟩ :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hs.le) hφ.continuousOn
  obtain ⟨xM, hxM, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hs.le) hφ.continuousOn
  have hosc := abs_sub_le_integral_deriv hd hc hxM hxm
  have bounds : ∀ d : ℝ, 0 < d → d ≤ s →
      φ xm ≤ d⁻¹ * (∫ x in Icc 0 d, φ x) ∧
        d⁻¹ * (∫ x in Icc 0 d, φ x) ≤ φ xM := by
    intro d hd0 hds
    have sub : Icc 0 d ⊆ Icc 0 s := Icc_subset_Icc le_rfl hds
    refine ⟨?_, ?_⟩
    · rw [le_inv_mul_iff₀ hd0]
      calc d * φ xm = ∫ _ in Icc 0 d, φ xm := by
            rw [setIntegral_const, Real.volume_real_Icc_of_le hd0.le, sub_zero, smul_eq_mul]
        _ ≤ ∫ x in Icc 0 d, φ x :=
            setIntegral_mono_on continuous_const.integrableOn_Icc hφ.integrableOn_Icc
              measurableSet_Icc fun x hx => isMinOn_iff.1 hmin x (sub hx)
    · rw [inv_mul_le_iff₀ hd0]
      calc ∫ x in Icc 0 d, φ x ≤ ∫ _ in Icc 0 d, φ xM :=
            setIntegral_mono_on hφ.integrableOn_Icc continuous_const.integrableOn_Icc
              measurableSet_Icc fun x hx => isMaxOn_iff.1 hmax x (sub hx)
        _ = d * φ xM := by
            rw [setIntegral_const, Real.volume_real_Icc_of_le hd0.le, sub_zero, smul_eq_mul]
  obtain ⟨h1, h2⟩ := bounds s' hs' hss'
  obtain ⟨h3, h4⟩ := bounds s hs le_rfl
  have : φ xM - φ xm ≤ ∫ x in Icc 0 s, |φ' x| := (le_abs_self _).trans hosc
  rw [abs_le]; constructor <;> linarith

/-! ## 2. 2D rectangles and 3D boxes anchored at the origin -/

def rect0 (s₁ s₂ : ℝ) : Set (ℝ × ℝ) := Icc 0 s₁ ×ˢ Icc 0 s₂

def box0 (s₁ s₂ s₃ : ℝ) : Set R3 := rect0 s₁ s₂ ×ˢ Icc 0 s₃

def rectAvg0 (g : ℝ × ℝ → ℝ) (s₁ s₂ : ℝ) : ℝ :=
  (s₁ * s₂)⁻¹ * ∫ p in rect0 s₁ s₂, g p

def boxAvg0 (f : R3 → ℝ) (s₁ s₂ s₃ : ℝ) : ℝ :=
  (s₁ * s₂ * s₃)⁻¹ * ∫ w in box0 s₁ s₂ s₃, f w

theorem measurableSet_rect0 (s₁ s₂ : ℝ) : MeasurableSet (rect0 s₁ s₂) :=
  measurableSet_Icc.prod measurableSet_Icc

theorem measurableSet_box0 (s₁ s₂ s₃ : ℝ) : MeasurableSet (box0 s₁ s₂ s₃) :=
  (measurableSet_rect0 s₁ s₂).prod measurableSet_Icc

theorem isCompact_rect0 (s₁ s₂ : ℝ) : IsCompact (rect0 s₁ s₂) :=
  isCompact_Icc.prod isCompact_Icc

theorem isCompact_box0 (s₁ s₂ s₃ : ℝ) : IsCompact (box0 s₁ s₂ s₃) :=
  (isCompact_rect0 s₁ s₂).prod isCompact_Icc

theorem box0_subset {s₁ s₂ s₃ s₁' s₂' s₃' : ℝ}
    (h1 : s₁' ≤ s₁) (h2 : s₂' ≤ s₂) (h3 : s₃' ≤ s₃) :
    box0 s₁' s₂' s₃' ⊆ box0 s₁ s₂ s₃ :=
  prod_mono (prod_mono (Icc_subset_Icc le_rfl h1) (Icc_subset_Icc le_rfl h2))
    (Icc_subset_Icc le_rfl h3)

theorem volume_rect0 {s₁ s₂ : ℝ} (h1 : 0 ≤ s₁) :
    volume (rect0 s₁ s₂) = ENNReal.ofReal (s₁ * s₂) := by
  rw [rect0, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc,
    sub_zero, sub_zero, ← ENNReal.ofReal_mul h1]

theorem volume_box0 {s₁ s₂ s₃ : ℝ} (h1 : 0 ≤ s₁) (h2 : 0 ≤ s₂) :
    volume (box0 s₁ s₂ s₃) = ENNReal.ofReal (s₁ * s₂ * s₃) := by
  rw [box0, Measure.volume_eq_prod, Measure.prod_prod, volume_rect0 h1, Real.volume_Icc,
    sub_zero, ← ENNReal.ofReal_mul (mul_nonneg h1 h2)]

theorem integrableOn_rect0 {g : ℝ × ℝ → ℝ} (hg : Continuous g) (s₁ s₂ : ℝ) :
    IntegrableOn g (rect0 s₁ s₂) :=
  hg.continuousOn.integrableOn_compact (isCompact_rect0 s₁ s₂)

theorem integrableOn_box0 {g : R3 → ℝ} (hg : Continuous g) (s₁ s₂ s₃ : ℝ) :
    IntegrableOn g (box0 s₁ s₂ s₃) :=
  hg.continuousOn.integrableOn_compact (isCompact_box0 s₁ s₂ s₃)

theorem memLp_box0 {g : R3 → ℝ} (hg : Continuous g) (P : ℝ≥0∞) (s₁ s₂ s₃ : ℝ) :
    MemLp g P (volume.restrict (box0 s₁ s₂ s₃)) := by
  have hK := isCompact_box0 s₁ s₂ s₃
  have : IsFiniteMeasure (volume.restrict (box0 s₁ s₂ s₃)) :=
    isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  exact MemLp.of_bound hg.aestronglyMeasurable C
    ((ae_restrict_iff' (measurableSet_box0 s₁ s₂ s₃)).2 (ae_of_all _ hC))

theorem integral_rect0_eq_iter {g : ℝ × ℝ → ℝ} (hg : Continuous g) (s₁ s₂ : ℝ) :
    ∫ p in rect0 s₁ s₂, g p = ∫ x in Icc 0 s₁, ∫ y in Icc 0 s₂, g (x, y) := by
  have h := integrableOn_rect0 hg s₁ s₂
  rw [rect0, Measure.volume_eq_prod] at h ⊢
  exact setIntegral_prod g h

theorem integral_rect0_eq_iter_symm {g : ℝ × ℝ → ℝ} (hg : Continuous g) (s₁ s₂ : ℝ) :
    ∫ p in rect0 s₁ s₂, g p = ∫ y in Icc 0 s₂, ∫ x in Icc 0 s₁, g (x, y) := by
  have h := integrableOn_rect0 hg s₁ s₂
  rw [rect0, Measure.volume_eq_prod, IntegrableOn, ← Measure.prod_restrict] at h
  rw [rect0, Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact integral_prod_symm g h

theorem integral_box0_eq_iter {g : R3 → ℝ} (hg : Continuous g) (s₁ s₂ s₃ : ℝ) :
    ∫ w in box0 s₁ s₂ s₃, g w = ∫ p in rect0 s₁ s₂, ∫ z in Icc 0 s₃, g (p, z) := by
  have h := integrableOn_box0 hg s₁ s₂ s₃
  rw [box0, Measure.volume_eq_prod] at h ⊢
  exact setIntegral_prod g h

theorem integral_box0_eq_iter_symm {g : R3 → ℝ} (hg : Continuous g) (s₁ s₂ s₃ : ℝ) :
    ∫ w in box0 s₁ s₂ s₃, g w = ∫ z in Icc 0 s₃, ∫ p in rect0 s₁ s₂, g (p, z) := by
  have h := integrableOn_box0 hg s₁ s₂ s₃
  rw [box0, Measure.volume_eq_prod, IntegrableOn, ← Measure.prod_restrict] at h
  rw [box0, Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact integral_prod_symm g h

theorem integrableOn_box0_marginal_left {g : R3 → ℝ} (hg : Continuous g) (s₁ s₂ s₃ : ℝ) :
    IntegrableOn (fun p => ∫ z in Icc 0 s₃, g (p, z)) (rect0 s₁ s₂) := by
  have h := integrableOn_box0 hg s₁ s₂ s₃
  rw [box0, Measure.volume_eq_prod, IntegrableOn, ← Measure.prod_restrict] at h
  exact h.integral_prod_left

theorem integrableOn_box0_marginal_right {g : R3 → ℝ} (hg : Continuous g) (s₁ s₂ s₃ : ℝ) :
    IntegrableOn (fun z => ∫ p in rect0 s₁ s₂, g (p, z)) (Icc 0 s₃) := by
  have h := integrableOn_box0 hg s₁ s₂ s₃
  rw [box0, Measure.volume_eq_prod, IntegrableOn, ← Measure.prod_restrict] at h
  exact h.integral_prod_right

theorem integrableOn_rect0_marginal_left {g : ℝ × ℝ → ℝ} (hg : Continuous g) (s₁ s₂ : ℝ) :
    IntegrableOn (fun x => ∫ y in Icc 0 s₂, g (x, y)) (Icc 0 s₁) := by
  have h := integrableOn_rect0 hg s₁ s₂
  rw [rect0, Measure.volume_eq_prod, IntegrableOn, ← Measure.prod_restrict] at h
  exact h.integral_prod_left

theorem integrableOn_rect0_marginal_right {g : ℝ × ℝ → ℝ} (hg : Continuous g) (s₁ s₂ : ℝ) :
    IntegrableOn (fun y => ∫ x in Icc 0 s₁, g (x, y)) (Icc 0 s₂) := by
  have h := integrableOn_rect0 hg s₁ s₂
  rw [rect0, Measure.volume_eq_prod, IntegrableOn, ← Measure.prod_restrict] at h
  exact h.integral_prod_right

/-! ## 3. Coordinate derivatives on `R3 = (ℝ × ℝ) × ℝ` -/

def partial1 (f : R3 → ℝ) (w : R3) : ℝ := fderiv ℝ f w ((1, 0), 0)
def partial2 (f : R3 → ℝ) (w : R3) : ℝ := fderiv ℝ f w ((0, 1), 0)
def partial3 (f : R3 → ℝ) (w : R3) : ℝ := fderiv ℝ f w ((0, 0), 1)

theorem continuous_partial1 {f : R3 → ℝ} (hf : ContDiff ℝ 1 f) : Continuous (partial1 f) :=
  (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem continuous_partial2 {f : R3 → ℝ} (hf : ContDiff ℝ 1 f) : Continuous (partial2 f) :=
  (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem continuous_partial3 {f : R3 → ℝ} (hf : ContDiff ℝ 1 f) : Continuous (partial3 f) :=
  (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem hasDerivAt_slice1 {f : R3 → ℝ} (hd : Differentiable ℝ f) (x y z : ℝ) :
    HasDerivAt (fun t => f ((t, y), z)) (partial1 f ((x, y), z)) x := by
  have h1 : HasDerivAt (fun t : ℝ => ((t, y), z)) ((1, 0), 0) x :=
    ((hasDerivAt_id x).prodMk (hasDerivAt_const x y)).prodMk (hasDerivAt_const x z)
  exact (hd ((x, y), z)).hasFDerivAt.comp_hasDerivAt x h1

theorem hasDerivAt_slice2 {f : R3 → ℝ} (hd : Differentiable ℝ f) (x y z : ℝ) :
    HasDerivAt (fun t => f ((x, t), z)) (partial2 f ((x, y), z)) y := by
  have h1 : HasDerivAt (fun t : ℝ => ((x, t), z)) ((0, 1), 0) y :=
    ((hasDerivAt_const y x).prodMk (hasDerivAt_id y)).prodMk (hasDerivAt_const y z)
  exact (hd ((x, y), z)).hasFDerivAt.comp_hasDerivAt y h1

theorem hasDerivAt_slice3 {f : R3 → ℝ} (hd : Differentiable ℝ f) (p : ℝ × ℝ) (z : ℝ) :
    HasDerivAt (fun t => f (p, t)) (partial3 f (p, z)) z := by
  have h1 : HasDerivAt (fun t : ℝ => (p, t)) ((0, 0), 1) z :=
    (hasDerivAt_const z p).prodMk (hasDerivAt_id z)
  exact (hd (p, z)).hasFDerivAt.comp_hasDerivAt z h1

/-! ## 4. Step bounds for 2D slice means and 3D box means -/

theorem rectAvg0_slice_step1 {f : R3 → ℝ} (hf : ContDiff ℝ 1 f) (z : ℝ)
    {s₁ s₁' s₂ : ℝ} (hs₁' : 0 < s₁') (h1 : s₁' ≤ s₁) (hs₂ : 0 < s₂) :
    |rectAvg0 (fun p => f (p, z)) s₁' s₂ - rectAvg0 (fun p => f (p, z)) s₁ s₂| ≤
      s₂⁻¹ * ∫ p in rect0 s₁ s₂, |partial1 f (p, z)| := by
  have hd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hc : Continuous (fun p : ℝ × ℝ => f (p, z)) :=
    hf.continuous.comp (continuous_id.prodMk continuous_const)
  have hcx : Continuous (fun p : ℝ × ℝ => partial1 f (p, z)) :=
    (continuous_partial1 hf).comp (continuous_id.prodMk continuous_const)
  have e : ∀ d : ℝ, rectAvg0 (fun p => f (p, z)) d s₂ =
      s₂⁻¹ * ∫ y in Icc 0 s₂, d⁻¹ * ∫ x in Icc 0 d, f ((x, y), z) := by
    intro d
    rw [rectAvg0, integral_rect0_eq_iter_symm hc, integral_const_mul, mul_inv]
    ring
  have iA' : IntegrableOn (fun y => s₁'⁻¹ * ∫ x in Icc 0 s₁', f ((x, y), z)) (Icc 0 s₂) :=
    (integrableOn_rect0_marginal_right hc s₁' s₂).const_mul _
  have iA : IntegrableOn (fun y => s₁⁻¹ * ∫ x in Icc 0 s₁, f ((x, y), z)) (Icc 0 s₂) :=
    (integrableOn_rect0_marginal_right hc s₁ s₂).const_mul _
  have iG : IntegrableOn (fun y => ∫ x in Icc 0 s₁, |partial1 f ((x, y), z)|) (Icc 0 s₂) :=
    integrableOn_rect0_marginal_right hcx.abs s₁ s₂
  have hpt : ∀ y, |s₁'⁻¹ * (∫ x in Icc 0 s₁', f ((x, y), z)) -
      s₁⁻¹ * ∫ x in Icc 0 s₁, f ((x, y), z)| ≤ ∫ x in Icc 0 s₁, |partial1 f ((x, y), z)| :=
    fun y => abs_avg_sub_avg_le (fun x => hasDerivAt_slice1 hd x y z)
      (hcx.comp (continuous_id.prodMk continuous_const)) hs₁' h1
  rw [e, e, ← mul_sub, ← integral_sub iA' iA, abs_mul,
    abs_of_nonneg (inv_nonneg.2 hs₂.le), integral_rect0_eq_iter_symm hcx.abs]
  gcongr
  calc _ ≤ ∫ y in Icc 0 s₂, |s₁'⁻¹ * (∫ x in Icc 0 s₁', f ((x, y), z)) -
        s₁⁻¹ * ∫ x in Icc 0 s₁, f ((x, y), z)| := abs_integral_le_integral_abs
    _ ≤ _ := integral_mono (iA'.sub iA).abs iG hpt

theorem rectAvg0_slice_step2 {f : R3 → ℝ} (hf : ContDiff ℝ 1 f) (z : ℝ)
    {s₁ s₂ s₂' : ℝ} (hs₂' : 0 < s₂') (h2 : s₂' ≤ s₂) (hs₁ : 0 < s₁) :
    |rectAvg0 (fun p => f (p, z)) s₁ s₂' - rectAvg0 (fun p => f (p, z)) s₁ s₂| ≤
      s₁⁻¹ * ∫ p in rect0 s₁ s₂, |partial2 f (p, z)| := by
  have hd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hc : Continuous (fun p : ℝ × ℝ => f (p, z)) :=
    hf.continuous.comp (continuous_id.prodMk continuous_const)
  have hcy : Continuous (fun p : ℝ × ℝ => partial2 f (p, z)) :=
    (continuous_partial2 hf).comp (continuous_id.prodMk continuous_const)
  have e : ∀ d : ℝ, rectAvg0 (fun p => f (p, z)) s₁ d =
      s₁⁻¹ * ∫ x in Icc 0 s₁, d⁻¹ * ∫ y in Icc 0 d, f ((x, y), z) := by
    intro d
    rw [rectAvg0, integral_rect0_eq_iter hc, integral_const_mul, mul_inv]
    ring
  have iA' : IntegrableOn (fun x => s₂'⁻¹ * ∫ y in Icc 0 s₂', f ((x, y), z)) (Icc 0 s₁) :=
    (integrableOn_rect0_marginal_left hc s₁ s₂').const_mul _
  have iA : IntegrableOn (fun x => s₂⁻¹ * ∫ y in Icc 0 s₂, f ((x, y), z)) (Icc 0 s₁) :=
    (integrableOn_rect0_marginal_left hc s₁ s₂).const_mul _
  have iG : IntegrableOn (fun x => ∫ y in Icc 0 s₂, |partial2 f ((x, y), z)|) (Icc 0 s₁) :=
    integrableOn_rect0_marginal_left hcy.abs s₁ s₂
  have hpt : ∀ x, |s₂'⁻¹ * (∫ y in Icc 0 s₂', f ((x, y), z)) -
      s₂⁻¹ * ∫ y in Icc 0 s₂, f ((x, y), z)| ≤ ∫ y in Icc 0 s₂, |partial2 f ((x, y), z)| :=
    fun x => abs_avg_sub_avg_le (fun y => hasDerivAt_slice2 hd x y z)
      (hcy.comp (continuous_const.prodMk continuous_id)) hs₂' h2
  rw [e, e, ← mul_sub, ← integral_sub iA' iA, abs_mul,
    abs_of_nonneg (inv_nonneg.2 hs₁.le), integral_rect0_eq_iter hcy.abs]
  gcongr
  calc _ ≤ ∫ x in Icc 0 s₁, |s₂'⁻¹ * (∫ y in Icc 0 s₂', f ((x, y), z)) -
        s₂⁻¹ * ∫ y in Icc 0 s₂, f ((x, y), z)| := abs_integral_le_integral_abs
    _ ≤ _ := integral_mono (iA'.sub iA).abs iG hpt

theorem boxAvg0_step1 {f : R3 → ℝ} (hf : ContDiff ℝ 1 f)
    {s₁ s₁' s₂ s₃ : ℝ} (hs₁' : 0 < s₁') (h1 : s₁' ≤ s₁) (hs₂ : 0 < s₂) (hs₃ : 0 < s₃) :
    |boxAvg0 f s₁' s₂ s₃ - boxAvg0 f s₁ s₂ s₃| ≤
      (s₂ * s₃)⁻¹ * ∫ w in box0 s₁ s₂ s₃, |partial1 f w| := by
  have hc : Continuous f := hf.continuous
  have hcx : Continuous (partial1 f) := continuous_partial1 hf
  have e : ∀ d : ℝ, boxAvg0 f d s₂ s₃ =
      s₃⁻¹ * ∫ z in Icc 0 s₃, rectAvg0 (fun p => f (p, z)) d s₂ := by
    intro d
    simp only [boxAvg0, rectAvg0, integral_box0_eq_iter_symm hc, integral_const_mul, mul_inv]
    ring
  have iA' : IntegrableOn (fun z => rectAvg0 (fun p => f (p, z)) s₁' s₂) (Icc 0 s₃) :=
    (integrableOn_box0_marginal_right hc s₁' s₂ s₃).const_mul _
  have iA : IntegrableOn (fun z => rectAvg0 (fun p => f (p, z)) s₁ s₂) (Icc 0 s₃) :=
    (integrableOn_box0_marginal_right hc s₁ s₂ s₃).const_mul _
  have iG : IntegrableOn (fun z => s₂⁻¹ * ∫ p in rect0 s₁ s₂, |partial1 f (p, z)|) (Icc 0 s₃) :=
    (integrableOn_box0_marginal_right hcx.abs s₁ s₂ s₃).const_mul _
  have hpt : ∀ z, |rectAvg0 (fun p => f (p, z)) s₁' s₂ - rectAvg0 (fun p => f (p, z)) s₁ s₂| ≤
      s₂⁻¹ * ∫ p in rect0 s₁ s₂, |partial1 f (p, z)| :=
    fun z => rectAvg0_slice_step1 hf z hs₁' h1 hs₂
  rw [e, e, ← mul_sub, ← integral_sub iA' iA, abs_mul, abs_of_nonneg (inv_nonneg.2 hs₃.le)]
  calc s₃⁻¹ * |∫ z in Icc 0 s₃, (rectAvg0 (fun p => f (p, z)) s₁' s₂ -
          rectAvg0 (fun p => f (p, z)) s₁ s₂)|
      ≤ s₃⁻¹ * ∫ z in Icc 0 s₃, |rectAvg0 (fun p => f (p, z)) s₁' s₂ -
          rectAvg0 (fun p => f (p, z)) s₁ s₂| :=
        mul_le_mul_of_nonneg_left abs_integral_le_integral_abs (inv_nonneg.2 hs₃.le)
    _ ≤ s₃⁻¹ * ∫ z in Icc 0 s₃, s₂⁻¹ * ∫ p in rect0 s₁ s₂, |partial1 f (p, z)| :=
        mul_le_mul_of_nonneg_left (integral_mono (iA'.sub iA).abs iG hpt) (inv_nonneg.2 hs₃.le)
    _ = (s₂ * s₃)⁻¹ * ∫ w in box0 s₁ s₂ s₃, |partial1 f w| := by
        rw [integral_const_mul, integral_box0_eq_iter_symm hcx.abs, mul_inv]
        ring

theorem boxAvg0_step2 {f : R3 → ℝ} (hf : ContDiff ℝ 1 f)
    {s₁ s₂ s₂' s₃ : ℝ} (hs₂' : 0 < s₂') (h2 : s₂' ≤ s₂) (hs₁ : 0 < s₁) (hs₃ : 0 < s₃) :
    |boxAvg0 f s₁ s₂' s₃ - boxAvg0 f s₁ s₂ s₃| ≤
      (s₁ * s₃)⁻¹ * ∫ w in box0 s₁ s₂ s₃, |partial2 f w| := by
  have hc : Continuous f := hf.continuous
  have hcy : Continuous (partial2 f) := continuous_partial2 hf
  have e : ∀ d : ℝ, boxAvg0 f s₁ d s₃ =
      s₃⁻¹ * ∫ z in Icc 0 s₃, rectAvg0 (fun p => f (p, z)) s₁ d := by
    intro d
    simp only [boxAvg0, rectAvg0, integral_box0_eq_iter_symm hc, integral_const_mul, mul_inv]
    ring
  have iA' : IntegrableOn (fun z => rectAvg0 (fun p => f (p, z)) s₁ s₂') (Icc 0 s₃) :=
    (integrableOn_box0_marginal_right hc s₁ s₂' s₃).const_mul _
  have iA : IntegrableOn (fun z => rectAvg0 (fun p => f (p, z)) s₁ s₂) (Icc 0 s₃) :=
    (integrableOn_box0_marginal_right hc s₁ s₂ s₃).const_mul _
  have iG : IntegrableOn (fun z => s₁⁻¹ * ∫ p in rect0 s₁ s₂, |partial2 f (p, z)|) (Icc 0 s₃) :=
    (integrableOn_box0_marginal_right hcy.abs s₁ s₂ s₃).const_mul _
  have hpt : ∀ z, |rectAvg0 (fun p => f (p, z)) s₁ s₂' - rectAvg0 (fun p => f (p, z)) s₁ s₂| ≤
      s₁⁻¹ * ∫ p in rect0 s₁ s₂, |partial2 f (p, z)| :=
    fun z => rectAvg0_slice_step2 hf z hs₂' h2 hs₁
  rw [e, e, ← mul_sub, ← integral_sub iA' iA, abs_mul, abs_of_nonneg (inv_nonneg.2 hs₃.le)]
  calc s₃⁻¹ * |∫ z in Icc 0 s₃, (rectAvg0 (fun p => f (p, z)) s₁ s₂' -
          rectAvg0 (fun p => f (p, z)) s₁ s₂)|
      ≤ s₃⁻¹ * ∫ z in Icc 0 s₃, |rectAvg0 (fun p => f (p, z)) s₁ s₂' -
          rectAvg0 (fun p => f (p, z)) s₁ s₂| :=
        mul_le_mul_of_nonneg_left abs_integral_le_integral_abs (inv_nonneg.2 hs₃.le)
    _ ≤ s₃⁻¹ * ∫ z in Icc 0 s₃, s₁⁻¹ * ∫ p in rect0 s₁ s₂, |partial2 f (p, z)| :=
        mul_le_mul_of_nonneg_left (integral_mono (iA'.sub iA).abs iG hpt) (inv_nonneg.2 hs₃.le)
    _ = (s₁ * s₃)⁻¹ * ∫ w in box0 s₁ s₂ s₃, |partial2 f w| := by
        rw [integral_const_mul, integral_box0_eq_iter_symm hcy.abs, mul_inv]
        ring

theorem boxAvg0_step3 {f : R3 → ℝ} (hf : ContDiff ℝ 1 f)
    {s₁ s₂ s₃ s₃' : ℝ} (hs₃' : 0 < s₃') (h3 : s₃' ≤ s₃) (hs₁ : 0 < s₁) (hs₂ : 0 < s₂) :
    |boxAvg0 f s₁ s₂ s₃' - boxAvg0 f s₁ s₂ s₃| ≤
      (s₁ * s₂)⁻¹ * ∫ w in box0 s₁ s₂ s₃, |partial3 f w| := by
  have hd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hc : Continuous f := hf.continuous
  have hcz : Continuous (partial3 f) := continuous_partial3 hf
  have hs12 : 0 < s₁ * s₂ := mul_pos hs₁ hs₂
  have e : ∀ d : ℝ, boxAvg0 f s₁ s₂ d =
      (s₁ * s₂)⁻¹ * ∫ p in rect0 s₁ s₂, d⁻¹ * ∫ z in Icc 0 d, f (p, z) := by
    intro d
    rw [boxAvg0, integral_box0_eq_iter hc, integral_const_mul, mul_inv]
    ring
  have iA' : IntegrableOn (fun p => s₃'⁻¹ * ∫ z in Icc 0 s₃', f (p, z)) (rect0 s₁ s₂) :=
    (integrableOn_box0_marginal_left hc s₁ s₂ s₃').const_mul _
  have iA : IntegrableOn (fun p => s₃⁻¹ * ∫ z in Icc 0 s₃, f (p, z)) (rect0 s₁ s₂) :=
    (integrableOn_box0_marginal_left hc s₁ s₂ s₃).const_mul _
  have iG : IntegrableOn (fun p => ∫ z in Icc 0 s₃, |partial3 f (p, z)|) (rect0 s₁ s₂) :=
    integrableOn_box0_marginal_left hcz.abs s₁ s₂ s₃
  have hpt : ∀ p, |s₃'⁻¹ * (∫ z in Icc 0 s₃', f (p, z)) -
      s₃⁻¹ * ∫ z in Icc 0 s₃, f (p, z)| ≤ ∫ z in Icc 0 s₃, |partial3 f (p, z)| :=
    fun p => abs_avg_sub_avg_le (fun z => hasDerivAt_slice3 hd p z)
      (hcz.comp (continuous_const.prodMk continuous_id)) hs₃' h3
  rw [e, e, ← mul_sub, ← integral_sub iA' iA, abs_mul,
    abs_of_nonneg (inv_nonneg.2 hs12.le), integral_box0_eq_iter hcz.abs]
  gcongr
  calc _ ≤ ∫ p in rect0 s₁ s₂, |s₃'⁻¹ * (∫ z in Icc 0 s₃', f (p, z)) -
        s₃⁻¹ * ∫ z in Icc 0 s₃, f (p, z)| := abs_integral_le_integral_abs
    _ ≤ _ := integral_mono (iA'.sub iA).abs iG hpt

/-! ## 5. Hölder on 3D boxes and dyadic-16 Campanato chain -/

theorem integral_abs_box0_le {g : R3 → ℝ} (hg : Continuous g)
    {s : ℝ} (hs : 0 ≤ s) :
    ∫ w in box0 s s s, |g w| ≤ (s * s * s) ^ (3 / 4 : ℝ) *
      (eLpNorm g 4 (volume.restrict (box0 s s s))).toReal := by
  have hA : 0 ≤ s * s * s := mul_nonneg (mul_nonneg hs hs) hs
  have hμ : volume.restrict (box0 s s s) univ = ENNReal.ofReal (s * s * s) := by
    rw [Measure.restrict_apply_univ, volume_box0 hs hs]
  have hP : (1 : ℝ≥0∞) ≤ 4 := by norm_num
  have hH := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hP hg.aestronglyMeasurable
    (μ := volume.restrict (box0 s s s))
  have hexp : (1 / (1 : ℝ≥0∞).toReal - 1 / (4 : ℝ≥0∞).toReal) = (3 / 4 : ℝ) := by norm_num
  rw [hμ, hexp] at hH
  have hfin : eLpNorm g 4 (volume.restrict (box0 s s s)) ≠ ⊤ :=
    (memLp_box0 hg 4 s s s).eLpNorm_ne_top
  have hfin2 : ENNReal.ofReal (s * s * s) ^ (3 / 4 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  have hI : ∫ w in box0 s s s, |g w| =
      (eLpNorm g 1 (volume.restrict (box0 s s s))).toReal := by
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← integral_norm_eq_lintegral_enorm hg.aestronglyMeasurable]
    simp only [Real.norm_eq_abs]
  rw [hI]
  calc (eLpNorm g 1 (volume.restrict (box0 s s s))).toReal
      ≤ (eLpNorm g 4 (volume.restrict (box0 s s s)) *
          ENNReal.ofReal (s * s * s) ^ (3 / 4 : ℝ)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top hfin hfin2) hH
    _ = _ := by
        rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hA, mul_comm]

theorem integral_abs_box0_le_unit {g : R3 → ℝ} (hg : Continuous g)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∫ w in box0 s s s, |g w| ≤ (s * s * s) ^ (3 / 4 : ℝ) *
      (eLpNorm g 4 (volume.restrict (box0 1 1 1))).toReal := by
  have hA : 0 ≤ s * s * s := mul_nonneg (mul_nonneg hs0 hs0) hs0
  have hfin : eLpNorm g 4 (volume.restrict (box0 1 1 1)) ≠ ⊤ :=
    (memLp_box0 hg 4 1 1 1).eLpNorm_ne_top
  refine (integral_abs_box0_le hg hs0).trans
    (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hfin ?_) (Real.rpow_nonneg hA _))
  exact eLpNorm_mono_measure _ (Measure.restrict_mono (box0_subset hs1 hs1 hs1) le_rfl)

theorem rpow_step_sixteen (k : ℕ) :
    (((1 / 16 : ℝ) ^ k * (1 / 16 : ℝ) ^ k)⁻¹ *
      (((1 / 16 : ℝ) ^ k * (1 / 16 : ℝ) ^ k * (1 / 16 : ℝ) ^ k) ^ (3 / 4 : ℝ))) =
      (1 / 2 : ℝ) ^ k := by
  set r : ℝ := (1 / 2 : ℝ) ^ k
  have hr : 0 < r := by positivity
  have hs : (1 / 16 : ℝ) ^ k = r ^ 4 := by
    dsimp [r]
    rw [← pow_mul, mul_comm k 4, pow_mul]
    norm_num
  have hcube : r ^ 4 * r ^ 4 * r ^ 4 = (r ^ 3) ^ (4 : ℝ) := by
    rw [Real.rpow_ofNat]
    ring
  have hr3 : 0 ≤ r ^ 3 := by positivity
  rw [hs, hcube, ← Real.rpow_mul hr3, show (4 : ℝ) * (3 / 4 : ℝ) = (3 : ℕ) by norm_num,
    Real.rpow_natCast]
  have hrne : r ≠ 0 := hr.ne'
  field_simp

theorem boxAvg0_step_sixteen {f : R3 → ℝ} (hf : ContDiff ℝ 1 f) (k : ℕ) :
    |boxAvg0 f ((1 / 16 : ℝ) ^ (k + 1)) ((1 / 16 : ℝ) ^ (k + 1)) ((1 / 16 : ℝ) ^ (k + 1)) -
        boxAvg0 f ((1 / 16 : ℝ) ^ k) ((1 / 16 : ℝ) ^ k) ((1 / 16 : ℝ) ^ k)| ≤
      256 * (1 / 2 : ℝ) ^ k *
        ((eLpNorm (partial1 f) 4 (volume.restrict (box0 1 1 1))).toReal +
          (eLpNorm (partial2 f) 4 (volume.restrict (box0 1 1 1))).toReal +
          (eLpNorm (partial3 f) 4 (volume.restrict (box0 1 1 1))).toReal) := by
  set s : ℝ := (1 / 16 : ℝ) ^ k
  set s' : ℝ := (1 / 16 : ℝ) ^ (k + 1)
  have hs : 0 < s := by positivity
  have hs' : 0 < s' := by positivity
  have hs_eq : s' = s / 16 := by
    dsimp [s, s']
    rw [pow_succ]
    ring
  have hss' : s' ≤ s := by linarith
  have hs1 : s ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hc1 := continuous_partial1 hf
  have hc2 := continuous_partial2 hf
  have hc3 := continuous_partial3 hf
  have hst1 := boxAvg0_step1 hf hs' hss' hs hs
  have hst2 := boxAvg0_step2 hf hs' hss' hs' hs
  have hst3 := boxAvg0_step3 hf hs' hss' hs' hs'
  have hsub2 : box0 s' s s ⊆ box0 s s s := box0_subset hss' le_rfl le_rfl
  have hsub3 : box0 s' s' s ⊆ box0 s s s := box0_subset hss' hss' le_rfl
  have hI2 : ∫ w in box0 s' s s, |partial2 f w| ≤ ∫ w in box0 s s s, |partial2 f w| :=
    setIntegral_mono_set (integrableOn_box0 hc2.abs s s s)
      (ae_of_all _ fun _ => abs_nonneg _) hsub2.eventuallyLE
  have hI3 : ∫ w in box0 s' s' s, |partial3 f w| ≤ ∫ w in box0 s s s, |partial3 f w| :=
    setIntegral_mono_set (integrableOn_box0 hc3.abs s s s)
      (ae_of_all _ fun _ => abs_nonneg _) hsub3.eventuallyLE
  set G1 := (eLpNorm (partial1 f) 4 (volume.restrict (box0 1 1 1))).toReal
  set G2 := (eLpNorm (partial2 f) 4 (volume.restrict (box0 1 1 1))).toReal
  set G3 := (eLpNorm (partial3 f) 4 (volume.restrict (box0 1 1 1))).toReal
  have hH1 : ∫ w in box0 s s s, |partial1 f w| ≤ (s * s * s) ^ (3 / 4 : ℝ) * G1 :=
    integral_abs_box0_le_unit hc1 hs.le hs1
  have hH2 : ∫ w in box0 s s s, |partial2 f w| ≤ (s * s * s) ^ (3 / 4 : ℝ) * G2 :=
    integral_abs_box0_le_unit hc2 hs.le hs1
  have hH3 : ∫ w in box0 s s s, |partial3 f w| ≤ (s * s * s) ^ (3 / 4 : ℝ) * G3 :=
    integral_abs_box0_le_unit hc3 hs.le hs1
  have hb1 : |boxAvg0 f s' s s - boxAvg0 f s s s| ≤
      (s * s)⁻¹ * ((s * s * s) ^ (3 / 4 : ℝ) * G1) :=
    hst1.trans (mul_le_mul_of_nonneg_left hH1 (by positivity))
  have hb2 : |boxAvg0 f s' s' s - boxAvg0 f s' s s| ≤
      (s' * s)⁻¹ * ((s * s * s) ^ (3 / 4 : ℝ) * G2) :=
    hst2.trans (mul_le_mul_of_nonneg_left (hI2.trans hH2) (by positivity))
  have hb3 : |boxAvg0 f s' s' s' - boxAvg0 f s' s' s| ≤
      (s' * s')⁻¹ * ((s * s * s) ^ (3 / 4 : ℝ) * G3) :=
    hst3.trans (mul_le_mul_of_nonneg_left (hI3.trans hH3) (by positivity))
  have htri : |boxAvg0 f s' s' s' - boxAvg0 f s s s| ≤
      |boxAvg0 f s' s' s' - boxAvg0 f s' s' s| +
        (|boxAvg0 f s' s' s - boxAvg0 f s' s s| + |boxAvg0 f s' s s - boxAvg0 f s s s|) :=
    (abs_sub_le _ _ _).trans (add_le_add_right (abs_sub_le _ _ _) _)
  have hG1 : 0 ≤ G1 := ENNReal.toReal_nonneg
  have hG2 : 0 ≤ G2 := ENNReal.toReal_nonneg
  have hG3 : 0 ≤ G3 := ENNReal.toReal_nonneg
  have hinv1 : (s * s)⁻¹ ≤ 256 * (s * s)⁻¹ := by
    have : 0 ≤ (s * s)⁻¹ := by positivity
    linarith
  have hinv2 : (s' * s)⁻¹ ≤ 256 * (s * s)⁻¹ := by
    rw [hs_eq]
    have : (s / 16 * s)⁻¹ = 16 * (s * s)⁻¹ := by ring
    rw [this]
    have : 0 ≤ (s * s)⁻¹ := by positivity
    linarith
  have hinv3 : (s' * s')⁻¹ = 256 * (s * s)⁻¹ := by
    rw [hs_eq]
    ring
  have hrpow : 0 ≤ (s * s * s) ^ (3 / 4 : ℝ) := by positivity
  calc |boxAvg0 f s' s' s' - boxAvg0 f s s s|
      ≤ (s' * s')⁻¹ * ((s * s * s) ^ (3 / 4 : ℝ) * G3) +
          ((s' * s)⁻¹ * ((s * s * s) ^ (3 / 4 : ℝ) * G2) +
            (s * s)⁻¹ * ((s * s * s) ^ (3 / 4 : ℝ) * G1)) :=
        htri.trans (add_le_add hb3 (add_le_add hb2 hb1))
    _ ≤ 256 * (s * s)⁻¹ * ((s * s * s) ^ (3 / 4 : ℝ) * G3) +
          (256 * (s * s)⁻¹ * ((s * s * s) ^ (3 / 4 : ℝ) * G2) +
            256 * (s * s)⁻¹ * ((s * s * s) ^ (3 / 4 : ℝ) * G1)) := by
        gcongr
        exact le_of_eq hinv3
    _ = 256 * ((s * s)⁻¹ * (s * s * s) ^ (3 / 4 : ℝ)) * (G1 + G2 + G3) := by ring
    _ = 256 * (1 / 2 : ℝ) ^ k * (G1 + G2 + G3) := by
        rw [rpow_step_sixteen k]

theorem abs_boxAvg0_sub_le {f : R3 → ℝ} (hf : Continuous f) {s c ε : ℝ}
    (hs : 0 < s) (hε : ∀ w ∈ box0 s s s, |f w - c| ≤ ε) :
    |boxAvg0 f s s s - c| ≤ ε := by
  have hA : 0 < s * s * s := mul_pos (mul_pos hs hs) hs
  have hvol : volume.real (box0 s s s) = s * s * s := by
    rw [Measure.real, volume_box0 hs.le hs.le, ENNReal.toReal_ofReal hA.le]
  have hfin : volume (box0 s s s) < ⊤ := by
    rw [volume_box0 hs.le hs.le]; exact ENNReal.ofReal_lt_top
  have hint : ∫ w in box0 s s s, (f w - c) =
      (∫ w in box0 s s s, f w) - (s * s * s) * c := by
    rw [integral_sub (integrableOn_box0 hf s s s) (integrableOn_box0 continuous_const s s s),
      setIntegral_const, hvol, smul_eq_mul]
  have key : boxAvg0 f s s s - c =
      (s * s * s)⁻¹ * ∫ w in box0 s s s, (f w - c) := by
    rw [hint, boxAvg0, mul_sub ((s * s * s)⁻¹), inv_mul_cancel_left₀ hA.ne']
  have hb := norm_setIntegral_le_of_norm_le_const hfin (f := fun w => f w - c)
    (fun w hw => by rw [Real.norm_eq_abs]; exact hε w hw)
  rw [Real.norm_eq_abs, hvol] at hb
  rw [key, abs_mul, abs_of_pos (inv_pos.2 hA), inv_mul_le_iff₀ hA]
  linarith

theorem tendsto_boxAvg0_sixteen {f : R3 → ℝ} (hf : Continuous f) :
    Tendsto (fun k : ℕ => boxAvg0 f ((1 / 16 : ℝ) ^ k) ((1 / 16 : ℝ) ^ k) ((1 / 16 : ℝ) ^ k))
      atTop (𝓝 (f ((0, 0), 0))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousAt_iff.1 hf.continuousAt (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1 / 16 : ℝ) < 1)
  refine ⟨N, fun k hk => ?_⟩
  have hk' : (1 / 16 : ℝ) ^ k < δ :=
    lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) hk) hN
  have hs : 0 < (1 / 16 : ℝ) ^ k := by positivity
  rw [Real.dist_eq]
  refine lt_of_le_of_lt (abs_boxAvg0_sub_le hf hs fun w hw => ?_) (half_lt_self hε)
  rcases w with ⟨⟨x, y⟩, z⟩
  rw [box0, rect0, Set.mem_prod, Set.mem_prod, Set.mem_Icc, Set.mem_Icc, Set.mem_Icc] at hw
  have hdist : dist ((x, y), z) (((0 : ℝ), (0 : ℝ)), (0 : ℝ)) < δ := by
    rw [Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq]
    refine max_lt (max_lt ?_ ?_) ?_ <;> rw [abs_lt] <;> constructor <;> simp only <;> linarith
  rw [← Real.dist_eq]
  exact (hδf hdist).le

theorem geom_sum_half_le_two (n : ℕ) :
    ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ i ≤ 2 := by
  have h := geom_sum_mul_neg (1 / 2 : ℝ) n
  have hpos : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n := by positivity
  linarith

theorem abs_zero_le_morrey_box0 {f : R3 → ℝ} (hf : ContDiff ℝ 1 f) :
    |f ((0, 0), 0)| ≤
      (eLpNorm f 4 (volume.restrict (box0 1 1 1))).toReal +
        512 *
          ((eLpNorm (partial1 f) 4 (volume.restrict (box0 1 1 1))).toReal +
            (eLpNorm (partial2 f) 4 (volume.restrict (box0 1 1 1))).toReal +
            (eLpNorm (partial3 f) 4 (volume.restrict (box0 1 1 1))).toReal) := by
  set G1 := (eLpNorm (partial1 f) 4 (volume.restrict (box0 1 1 1))).toReal
  set G2 := (eLpNorm (partial2 f) 4 (volume.restrict (box0 1 1 1))).toReal
  set G3 := (eLpNorm (partial3 f) 4 (volume.restrict (box0 1 1 1))).toReal
  set A : ℕ → ℝ := fun k =>
    boxAvg0 f ((1 / 16 : ℝ) ^ k) ((1 / 16 : ℝ) ^ k) ((1 / 16 : ℝ) ^ k) with hA
  have hB : 0 ≤ 256 * (G1 + G2 + G3) := by positivity
  have tele : ∀ K : ℕ, |A K - A 0| ≤
      256 * (G1 + G2 + G3) * ∑ k ∈ Finset.range K, (1 / 2 : ℝ) ^ k := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
        rw [Finset.sum_range_succ, mul_add]
        calc |A (K + 1) - A 0|
            ≤ |A (K + 1) - A K| + |A K - A 0| := abs_sub_le _ _ _
          _ ≤ 256 * (1 / 2 : ℝ) ^ K * (G1 + G2 + G3) +
              256 * (G1 + G2 + G3) * ∑ k ∈ Finset.range K, (1 / 2 : ℝ) ^ k :=
            add_le_add (boxAvg0_step_sixteen hf K) ih
          _ = _ := by ring
  have bound : ∀ K : ℕ, |A K - A 0| ≤ 512 * (G1 + G2 + G3) := fun K => by
    calc |A K - A 0|
        ≤ 256 * (G1 + G2 + G3) * ∑ k ∈ Finset.range K, (1 / 2 : ℝ) ^ k := tele K
      _ ≤ 256 * (G1 + G2 + G3) * 2 :=
        mul_le_mul_of_nonneg_left (geom_sum_half_le_two K) hB
      _ = 512 * (G1 + G2 + G3) := by ring
  have hlim : Tendsto (fun K => |A K - A 0|) atTop (𝓝 (|f ((0, 0), 0) - A 0|)) :=
    ((tendsto_boxAvg0_sixteen hf.continuous).sub_const (A 0)).abs
  have key := le_of_tendsto' hlim bound
  have hA0 : A 0 = boxAvg0 f 1 1 1 := by simp [hA]
  rw [hA0] at key
  have havg : |boxAvg0 f 1 1 1| ≤ (eLpNorm f 4 (volume.restrict (box0 1 1 1))).toReal := by
    rw [boxAvg0, show (1 : ℝ) * 1 * 1 = 1 by ring, inv_one, one_mul]
    calc |∫ w in box0 1 1 1, f w|
        ≤ ∫ w in box0 1 1 1, |f w| := abs_integral_le_integral_abs
      _ ≤ ((1 : ℝ) * 1 * 1) ^ (3 / 4 : ℝ) *
          (eLpNorm f 4 (volume.restrict (box0 1 1 1))).toReal :=
        integral_abs_box0_le hf.continuous zero_le_one
      _ = (eLpNorm f 4 (volume.restrict (box0 1 1 1))).toReal := by norm_num
  calc |f ((0, 0), 0)|
      = |boxAvg0 f 1 1 1 + (f ((0, 0), 0) - boxAvg0 f 1 1 1)| := by ring_nf
    _ ≤ |boxAvg0 f 1 1 1| + |f ((0, 0), 0) - boxAvg0 f 1 1 1| := abs_add_le _ _
    _ ≤ _ := add_le_add havg key

/-! ## 6. Measure-preserving bridge from `R3` to `Space` -/

def spaceOfR3 : R3 →L[ℝ] Space :=
  ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)).smulRight
      (coordinateVector 0) +
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)).smulRight
      (coordinateVector 1) +
    (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).smulRight (coordinateVector 2)

theorem spaceOfR3_eq_comp :
    (spaceOfR3 : R3 → Space) =
      (@WithLp.toLp 2 (Fin 3 → ℝ)) ∘
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm ∘
        Prod.map id (MeasurableEquiv.finTwoArrow (α := ℝ)).symm ∘
        MeasurableEquiv.prodAssoc := by
  ext ⟨⟨x₀, x₁⟩, x₂⟩ j
  fin_cases j <;> simp [spaceOfR3, coordinateVector] <;> rfl

theorem measurePreserving_spaceOfR3 :
    MeasurePreserving spaceOfR3 (volume : Measure R3) (volume : Measure Space) := by
  rw [spaceOfR3_eq_comp]
  have h1 : MeasurePreserving (MeasurableEquiv.prodAssoc : R3 ≃ᵐ ℝ × (ℝ × ℝ)) volume volume :=
    MeasureTheory.volume_preserving_prodAssoc
  have h2 : MeasurePreserving
      (Prod.map id (MeasurableEquiv.finTwoArrow (α := ℝ)).symm :
        ℝ × (ℝ × ℝ) → ℝ × (Fin 2 → ℝ)) volume volume :=
    (MeasurePreserving.id volume).prod (MeasureTheory.volume_preserving_finTwoArrow ℝ).symm
  have h3 : MeasurePreserving
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm :
        ℝ × (Fin 2 → ℝ) ≃ᵐ (Fin 3 → ℝ)) volume volume :=
    (MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm
  have h4 : MeasurePreserving (@WithLp.toLp 2 (Fin 3 → ℝ)) volume volume :=
    PiLp.volume_preserving_toLp (Fin 3)
  exact h4.comp (h3.comp (h2.comp h1))

def cubeMap (y : Space) (w : R3) : Space := y + spaceOfR3 w

theorem measurePreserving_cubeMap (y : Space) :
    MeasurePreserving (cubeMap y) (volume : Measure R3) (volume : Measure Space) :=
  (measurePreserving_add_left volume y).comp measurePreserving_spaceOfR3

@[simp]
theorem cubeMap_zero (y : Space) : cubeMap y ((0, 0), 0) = y := by
  change y + spaceOfR3 (0 : R3) = y
  simp

theorem spaceOfR3_basis1 : spaceOfR3 ((1, 0), 0) = coordinateVector 0 := by
  ext j; fin_cases j <;> simp [spaceOfR3, coordinateVector]

theorem spaceOfR3_basis2 : spaceOfR3 ((0, 1), 0) = coordinateVector 1 := by
  ext j; fin_cases j <;> simp [spaceOfR3, coordinateVector]

theorem spaceOfR3_basis3 : spaceOfR3 ((0, 0), 1) = coordinateVector 2 := by
  ext j; fin_cases j <;> simp [spaceOfR3, coordinateVector]

def coordCLM (i : Fin 3) : Space →L[ℝ] ℝ := EuclideanSpace.proj i

theorem norm_coordCLM_apply_le (i : Fin 3) (v : Space) : |coordCLM i v| ≤ ‖v‖ := by
  simpa [coordCLM] using PiLp.norm_apply_le v i

end MorreyL4Sub

open MorreyL4Sub

/-- **`PartII-b:S3/1/1/1` (`SmoothMorreyL4FieldBound`)**
(`the November 2 reference manuscript`,
lines 2557-2562: 3D Morrey/Sobolev embedding `W^{1,4}(ℝ³) ↪ L^∞(ℝ³)` on smooth spatial vector
fields). -/
theorem smoothMorreyL4FieldBound_proof : UnforcedLeray.Short.IIb.SmoothMorreyL4FieldBound := by
  refine ⟨4608, by norm_num, ?_⟩
  intro F hF M₀ M₁ hM₀ hM₁ hLp0 hLp1 y
  have hF_diff : Differentiable ℝ F := hF.differentiable (by simp)
  have hcoord : ∀ i : Fin 3, |F y i| ≤ M₀ + 1536 * M₁ := by
    intro i
    let f : R3 → ℝ := fun w => coordCLM i (F (cubeMap y w))
    have hcube_smooth : ContDiff ℝ ∞ (cubeMap y) := contDiff_const.add spaceOfR3.contDiff
    have hf_smooth : ContDiff ℝ ∞ f := (coordCLM i).contDiff.comp (hF.comp hcube_smooth)
    have hf1 : ContDiff ℝ 1 f := hf_smooth.of_le (by simp)
    have hf_fderiv : ∀ w : R3,
        fderiv ℝ f w = (coordCLM i).comp ((fderiv ℝ F (cubeMap y w)).comp spaceOfR3) := by
      intro w
      have h1 : HasFDerivAt (cubeMap y) spaceOfR3 w := spaceOfR3.hasFDerivAt.const_add y
      have h2 : HasFDerivAt F (fderiv ℝ F (cubeMap y w)) (cubeMap y w) :=
        (hF_diff (cubeMap y w)).hasFDerivAt
      exact ((coordCLM i).hasFDerivAt.comp w (h2.comp w h1)).fderiv
    have hpart_le : ∀ w : R3,
        |partial1 f w| ≤ ‖fderiv ℝ F (cubeMap y w)‖ ∧
        |partial2 f w| ≤ ‖fderiv ℝ F (cubeMap y w)‖ ∧
        |partial3 f w| ≤ ‖fderiv ℝ F (cubeMap y w)‖ := by
      intro w
      have hbound : ∀ u : Space, ‖u‖ ≤ 1 →
          |coordCLM i (fderiv ℝ F (cubeMap y w) u)| ≤ ‖fderiv ℝ F (cubeMap y w)‖ := by
        intro u hu
        calc |coordCLM i (fderiv ℝ F (cubeMap y w) u)|
            ≤ ‖fderiv ℝ F (cubeMap y w) u‖ := norm_coordCLM_apply_le i _
          _ ≤ ‖fderiv ℝ F (cubeMap y w)‖ * ‖u‖ := (fderiv ℝ F (cubeMap y w)).le_opNorm u
          _ ≤ ‖fderiv ℝ F (cubeMap y w)‖ * 1 :=
              mul_le_mul_of_nonneg_left hu (norm_nonneg _)
          _ = ‖fderiv ℝ F (cubeMap y w)‖ := mul_one _
      refine ⟨?_, ?_, ?_⟩
      · simp only [partial1, hf_fderiv w, ContinuousLinearMap.comp_apply, spaceOfR3_basis1]
        exact hbound (coordinateVector 0) (FirstOrderPhaseDerivSub.norm_coordinateVector_le_one 0)
      · simp only [partial2, hf_fderiv w, ContinuousLinearMap.comp_apply, spaceOfR3_basis2]
        exact hbound (coordinateVector 1) (FirstOrderPhaseDerivSub.norm_coordinateVector_le_one 1)
      · simp only [partial3, hf_fderiv w, ContinuousLinearMap.comp_apply, spaceOfR3_basis3]
        exact hbound (coordinateVector 2) (FirstOrderPhaseDerivSub.norm_coordinateVector_le_one 2)
    have hmp := measurePreserving_cubeMap y
    have hf_le_M₀ : (eLpNorm f 4 (volume.restrict (box0 1 1 1))).toReal ≤ M₀ := by
      have h1 : eLpNorm f 4 (volume.restrict (box0 1 1 1)) ≤ eLpNorm f 4 volume :=
        eLpNorm_mono_measure f Measure.restrict_le_self
      have h2 : eLpNorm f 4 volume ≤ eLpNorm (F ∘ cubeMap y) 4 volume :=
        eLpNorm_mono_ae (Eventually.of_forall fun w => by
          simpa [f, Real.norm_eq_abs] using norm_coordCLM_apply_le i (F (cubeMap y w)))
      have h3 : eLpNorm (F ∘ cubeMap y) 4 volume = eLpNorm F 4 volume :=
        eLpNorm_comp_measurePreserving hF.continuous.aestronglyMeasurable hmp
      have htot : eLpNorm f 4 (volume.restrict (box0 1 1 1)) ≤ ENNReal.ofReal M₀ :=
        (h1.trans (h2.trans (le_of_eq h3))).trans hLp0
      exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top htot).trans
        (le_of_eq (ENNReal.toReal_ofReal hM₀))
    have hpart_M₁ : ∀ g : R3 → ℝ, (∀ w, |g w| ≤ ‖fderiv ℝ F (cubeMap y w)‖) →
        (eLpNorm g 4 (volume.restrict (box0 1 1 1))).toReal ≤ M₁ := by
      intro g hg
      have h1 : eLpNorm g 4 (volume.restrict (box0 1 1 1)) ≤ eLpNorm g 4 volume :=
        eLpNorm_mono_measure g Measure.restrict_le_self
      have h2 : eLpNorm g 4 volume ≤ eLpNorm (fderiv ℝ F ∘ cubeMap y) 4 volume :=
        eLpNorm_mono_ae (Eventually.of_forall fun w => by
          simpa [Real.norm_eq_abs] using hg w)
      have h3 : eLpNorm (fderiv ℝ F ∘ cubeMap y) 4 volume = eLpNorm (fderiv ℝ F) 4 volume :=
        eLpNorm_comp_measurePreserving (hF.continuous_fderiv (by simp)).aestronglyMeasurable hmp
      have htot : eLpNorm g 4 (volume.restrict (box0 1 1 1)) ≤ ENNReal.ofReal M₁ :=
        (h1.trans (h2.trans (le_of_eq h3))).trans hLp1
      exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top htot).trans
        (le_of_eq (ENNReal.toReal_ofReal hM₁))
    have hp1 : (eLpNorm (partial1 f) 4 (volume.restrict (box0 1 1 1))).toReal ≤ M₁ :=
      hpart_M₁ (partial1 f) (fun w => (hpart_le w).1)
    have hp2 : (eLpNorm (partial2 f) 4 (volume.restrict (box0 1 1 1))).toReal ≤ M₁ :=
      hpart_M₁ (partial2 f) (fun w => (hpart_le w).2.1)
    have hp3 : (eLpNorm (partial3 f) 4 (volume.restrict (box0 1 1 1))).toReal ≤ M₁ :=
      hpart_M₁ (partial3 f) (fun w => (hpart_le w).2.2)
    have hmorrey := abs_zero_le_morrey_box0 hf1
    have hf0 : f ((0, 0), 0) = F y i := by simp [f, coordCLM]
    rw [hf0] at hmorrey
    linarith
  have hrepr : F y = ∑ i : Fin 3, F y i • coordinateVector i := by
    ext j
    simp [coordinateVector, Pi.single_apply]
  calc ‖F y‖
      = ‖∑ i : Fin 3, F y i • coordinateVector i‖ := by rw [← hrepr]
    _ ≤ ∑ i : Fin 3, ‖F y i • coordinateVector i‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, |F y i| := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul, Real.norm_eq_abs]
        calc |F y i| * ‖coordinateVector i‖
            ≤ |F y i| * 1 := mul_le_mul_of_nonneg_left
              (FirstOrderPhaseDerivSub.norm_coordinateVector_le_one i) (abs_nonneg _)
          _ = |F y i| := mul_one _
    _ ≤ ∑ _i : Fin 3, (M₀ + 1536 * M₁) := Finset.sum_le_sum fun i _ => hcoord i
    _ ≤ 4608 * (M₀ + M₁) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        linarith

end UnforcedLeray.Short.IIb

end
