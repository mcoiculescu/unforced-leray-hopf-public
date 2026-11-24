import UnforcedLeray.Lib.FreeStressCouplings.DilationChart

/-!
# The unitary group `e^{tB}` on `Y₂`: phase translation composed with normalised dilation


§4 bypass **B9** and §5 Level F, target **F1**; blueprint unit **B0459** (tex 7698-7722:
"the generator of the unitary group consisting of phase translation and the `L²`-normalized
spatial dilation").

The flow chart `Θ` of `DilationChart.lean` gives a unitary
`chartY P : Y₂ ≃ L²(ℝ × K, dθ dz)`, `(chartY x)(θ, z) = J(θ) x([θ], e^{-θ/2} z)` with
`J(θ) = e^{-3θ/4}/√P` (`chartY_ae`).  The group is the translation `θ ↦ θ + t` read back on `Y₂`:
`phaseDilation P t = chartY⁻¹ ∘ (θ ↦ θ + t) ∘ chartY`.  `phaseDilation_ae` proves that this is the
manuscript's group (tex 7713-7715, the B0459 proof outline with `r = -t`):

  `(e^{tB} w)(τ, y) = e^{-3t/4} w(τ + t, e^{-t/2} y)`.

* `densityIso`: `L²(m.withDensity w²) ≃ L²(m)`, `f ↦ w f` (general);
* `chartLp`: `L²(haar × dy) ≃ L²(chart measure)`, composition with `Θ`;
* `chartY`, `chartY_ae`, `chartY_symm_ae`;
* `phaseDilation`, `phaseDilation_ae`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal

namespace UnforcedLeray.FreeStress

open UnforcedLeray.PhaseSpace

section Density

variable {γ : Type*} [MeasurableSpace γ] {m : Measure γ}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {w : γ → ℝ}

/-- The measure `w² m`. -/
abbrev densityMeasure (m : Measure γ) (w : γ → ℝ) : Measure γ :=
  m.withDensity fun a => ENNReal.ofReal (w a ^ 2)

theorem densityMeasure_ac : densityMeasure m w ≪ m :=
  withDensity_absolutelyContinuous _ _

theorem ac_densityMeasure (hw : Measurable w) (hpos : ∀ a, 0 < w a) :
    m ≪ densityMeasure m w :=
  withDensity_absolutelyContinuous' (ENNReal.measurable_ofReal.comp (hw.pow_const 2)).aemeasurable
    (Eventually.of_forall fun a => by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact pow_pos (hpos a) 2)

theorem eLpNorm_density_smul (hw : Measurable w) (hpos : ∀ a, 0 < w a) (f : γ → E) :
    eLpNorm (fun a => (w a : ℂ) • f a) 2 m = eLpNorm f 2 (densityMeasure m w) := by
  unfold densityMeasure
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    lintegral_withDensity_eq_lintegral_mul_non_measurable m
      (f := fun a => ENNReal.ofReal (w a ^ 2)) (ENNReal.measurable_ofReal.comp (hw.pow_const 2))
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  refine lintegral_congr fun a => ?_
  simp only [Pi.mul_apply, enorm_smul, ENNReal.toReal_ofNat]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  rw [show ‖(w a : ℂ)‖ₑ = ENNReal.ofReal (w a) by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (hpos a).le]]
  rw [ENNReal.ofReal_rpow_of_nonneg (hpos a).le (by norm_num), Real.rpow_two]

theorem memLp_density_smul (hw : Measurable w) (hpos : ∀ a, 0 < w a) {f : γ → E}
    (hf : MemLp f 2 (densityMeasure m w)) : MemLp (fun a => (w a : ℂ) • f a) 2 m :=
  ⟨((Complex.measurable_ofReal.comp hw).aestronglyMeasurable).smul
      (hf.1.mono_ac (ac_densityMeasure hw hpos)),
    by rw [eLpNorm_density_smul hw hpos]; exact hf.2⟩

theorem memLp_density_inv_smul (hw : Measurable w) (hpos : ∀ a, 0 < w a) {g : γ → E}
    (hg : MemLp g 2 m) : MemLp (fun a => ((w a : ℂ))⁻¹ • g a) 2 (densityMeasure m w) := by
  refine ⟨(((Complex.measurable_ofReal.comp hw).inv).aestronglyMeasurable.smul
      (hg.1.mono_ac densityMeasure_ac)), ?_⟩
  rw [← eLpNorm_density_smul hw hpos]
  have h : (fun a => (w a : ℂ) • ((w a : ℂ))⁻¹ • g a) = g := by
    funext a
    rw [smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 (hpos a).ne'), one_smul]
  rw [h]
  exact hg.2

/-- **`L²(w² m) ≃ L²(m)`**, `f ↦ w f`, for a measurable `w > 0`. -/
def densityIso (hw : Measurable w) (hpos : ∀ a, 0 < w a) :
    Lp E 2 (densityMeasure m w) ≃ₗᵢ[ℂ] Lp E 2 m where
  toFun f := (memLp_density_smul hw hpos (Lp.memLp f)).toLp _
  invFun g := (memLp_density_inv_smul hw hpos (Lp.memLp g)).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(memLp_density_smul hw hpos (Lp.memLp (f + g))).coeFn_toLp,
      (memLp_density_smul hw hpos (Lp.memLp f)).coeFn_toLp,
      (memLp_density_smul hw hpos (Lp.memLp g)).coeFn_toLp,
      Lp.coeFn_add ((memLp_density_smul hw hpos (Lp.memLp f)).toLp _)
        ((memLp_density_smul hw hpos (Lp.memLp g)).toLp _),
      (ac_densityMeasure hw hpos).ae_le (Lp.coeFn_add f g)] with a h1 h2 h3 h4 h5
    rw [h1, h4, Pi.add_apply, h2, h3, h5, Pi.add_apply, smul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(memLp_density_smul hw hpos (Lp.memLp (c • f))).coeFn_toLp,
      (memLp_density_smul hw hpos (Lp.memLp f)).coeFn_toLp,
      Lp.coeFn_smul c ((memLp_density_smul hw hpos (Lp.memLp f)).toLp _),
      (ac_densityMeasure hw hpos).ae_le (Lp.coeFn_smul c f)] with a h1 h2 h3 h4
    rw [h1, RingHom.id_apply, h3, Pi.smul_apply, h2, h4, Pi.smul_apply, smul_comm]
  left_inv f := by
    apply Lp.ext
    filter_upwards [(memLp_density_inv_smul hw hpos (Lp.memLp
        ((memLp_density_smul hw hpos (Lp.memLp f)).toLp _))).coeFn_toLp,
      densityMeasure_ac.ae_le (memLp_density_smul hw hpos (Lp.memLp f)).coeFn_toLp] with a h1 h2
    rw [h1, h2, smul_smul, inv_mul_cancel₀ (Complex.ofReal_ne_zero.2 (hpos a).ne'), one_smul]
  right_inv g := by
    apply Lp.ext
    filter_upwards [(memLp_density_smul hw hpos (Lp.memLp
        ((memLp_density_inv_smul hw hpos (Lp.memLp g)).toLp _))).coeFn_toLp,
      (ac_densityMeasure hw hpos).ae_le (memLp_density_inv_smul hw hpos (Lp.memLp g)).coeFn_toLp]
      with a h1 h2
    rw [h1, h2, smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 (hpos a).ne'), one_smul]
  norm_map' f := by
    change ‖(memLp_density_smul hw hpos (Lp.memLp f)).toLp _‖ = ‖f‖
    rw [Lp.norm_toLp, eLpNorm_density_smul hw hpos, Lp.norm_def]

theorem densityIso_ae (hw : Measurable w) (hpos : ∀ a, 0 < w a) (f : Lp E 2 (densityMeasure m w)) :
    (densityIso hw hpos f : γ → E) =ᵐ[m] fun a => (w a : ℂ) • f a :=
  (memLp_density_smul hw hpos (Lp.memLp f)).coeFn_toLp

theorem densityIso_symm_ae (hw : Measurable w) (hpos : ∀ a, 0 < w a) (g : Lp E 2 m) :
    ((densityIso hw hpos).symm g : γ → E) =ᵐ[densityMeasure m w]
      fun a => ((w a : ℂ))⁻¹ • g a :=
  (memLp_density_inv_smul hw hpos (Lp.memLp g)).coeFn_toLp

end Density

variable (P : ℝ) [hP : Fact (0 < P)]

/-- Composition with the flow chart: `L²(haar × dy) ≃ L²(chart measure)`. -/
def chartLp : Lp CVec3 2 (phaseVol P) ≃ₗᵢ[ℂ] Lp CVec3 2 (chartMeasure P) where
  toFun := Lp.compMeasurePreserving (chartFwd P) (measurePreserving_chartFwd P)
  invFun := Lp.compMeasurePreserving (chartInv P) (measurePreserving_chartInv P)
  map_add' := map_add _
  map_smul' c f :=
    (Lp.compMeasurePreservingₗ ℂ (chartFwd P) (measurePreserving_chartFwd P)).map_smul c f
  left_inv f := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving
        (Lp.compMeasurePreserving (chartFwd P) (measurePreserving_chartFwd P) f)
        (measurePreserving_chartInv P),
      (measurePreserving_chartInv P).quasiMeasurePreserving.ae_eq_comp
        (Lp.coeFn_compMeasurePreserving f (measurePreserving_chartFwd P))] with q h1 h2
    rw [h1, h2]
    simp only [Function.comp_apply, chartFwd_chartInv]
  right_inv g := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving
        (Lp.compMeasurePreserving (chartInv P) (measurePreserving_chartInv P) g)
        (measurePreserving_chartFwd P),
      (measurePreserving_chartFwd P).quasiMeasurePreserving.ae_eq_comp
        (Lp.coeFn_compMeasurePreserving g (measurePreserving_chartInv P)),
      ae_chartInv_chartFwd P] with p h1 h2 h3
    rw [h1, h2]
    simp only [Function.comp_apply, h3]
  norm_map' f := Lp.norm_compMeasurePreserving f (measurePreserving_chartFwd P)

theorem chartLp_ae (f : Lp CVec3 2 (phaseVol P)) :
    (chartLp P f : ℝ × Space → CVec3) =ᵐ[chartMeasure P] fun p => f (chartFwd P p) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_chartFwd P)

theorem chartLp_symm_ae (g : Lp CVec3 2 (chartMeasure P)) :
    ((chartLp P).symm g : AddCircle P × Space → CVec3) =ᵐ[phaseVol P]
      fun q => g (chartInv P q) :=
  Lp.coeFn_compMeasurePreserving g (measurePreserving_chartInv P)

/-- The chart density as a function on `ℝ × ℝ³`. -/
abbrev chartJp (p : ℝ × Space) : ℝ := chartJ P p.1

theorem measurable_chartJp : Measurable (chartJp P) := (measurable_chartJ P).comp measurable_fst

theorem chartJp_pos (p : ℝ × Space) : 0 < chartJp P p := chartJ_pos P p.1

/-- The weight unitary `L²(chart measure) ≃ L²(dθ dz|_K)`, `g ↦ J g`. -/
def chartWeightIso : Lp CVec3 2 (chartMeasure P) ≃ₗᵢ[ℂ] Lp CVec3 2 (chartBase P) :=
  densityIso (m := chartBase P) (measurable_chartJp P) (chartJp_pos P)

/-- **The flow-chart unitary** `chartY P : Y₂ ≃ L²(ℝ × K, dθ dz)`,
`(chartY x)(θ, z) = J(θ) x([θ], e^{-θ/2} z)`. -/
def chartY : Yq P 2 ≃ₗᵢ[ℂ] Lp CVec3 2 (chartBase P) :=
  prodLpEquiv.symm.trans ((chartLp P).trans (chartWeightIso P))

theorem chartY_ae (x : Yq P 2) :
    (chartY P x : ℝ × Space → CVec3) =ᵐ[chartBase P]
      fun p => (chartJ P p.1 : ℂ) •
        (prodLpEquiv.symm x : AddCircle P × Space → CVec3) (chartFwd P p) := by
  have h1 := densityIso_ae (m := chartBase P) (measurable_chartJp P) (chartJp_pos P)
    (chartLp P (prodLpEquiv.symm x))
  have h2 := (chartBase_ac P).ae_le (chartLp_ae P (prodLpEquiv.symm x))
  filter_upwards [h1, h2] with p e1 e2
  exact e1.trans (congrArg (fun v : CVec3 => ((chartJp P p : ℝ) : ℂ) • v) e2)

theorem chartY_symm_ae (g : Lp CVec3 2 (chartBase P)) :
    (prodLpEquiv.symm ((chartY P).symm g) : AddCircle P × Space → CVec3) =ᵐ[phaseVol P]
      fun q => ((chartJ P (chartInv P q).1 : ℂ))⁻¹ • g (chartInv P q) := by
  have hsymm : prodLpEquiv.symm ((chartY P).symm g) =
      (chartLp P).symm ((chartWeightIso P).symm g) := by
    change prodLpEquiv.symm (prodLpEquiv ((chartLp P).symm ((chartWeightIso P).symm g))) = _
    rw [LinearIsometryEquiv.symm_apply_apply]
  rw [hsymm]
  have h1 := chartLp_symm_ae P ((chartWeightIso P).symm g)
  have h2 := (measurePreserving_chartInv P).quasiMeasurePreserving.ae_eq_comp
    (densityIso_symm_ae (m := chartBase P) (measurable_chartJp P) (chartJp_pos P) g)
  filter_upwards [h1, h2] with q e1 e2
  rw [e1]
  exact e2

/-- The translation `(θ, z) ↦ (θ + t, z)` of the chart. -/
theorem measurePreserving_shift (t : ℝ) :
    MeasurePreserving (Prod.map (· + t) id : ℝ × Space → ℝ × Space) (chartBase P) (chartBase P) :=
  (measurePreserving_add_right volume t).prod (MeasurePreserving.id _)

/-- Translation by `t` in the chart variable `θ`, on `L²(ℝ × K)`. -/
def chartShift (t : ℝ) : Lp CVec3 2 (chartBase P) →ₗᵢ[ℂ] Lp CVec3 2 (chartBase P) :=
  Lp.compMeasurePreservingₗᵢ ℂ (Prod.map (· + t) id) (measurePreserving_shift P t)

theorem chartShift_ae (t : ℝ) (h : Lp CVec3 2 (chartBase P)) :
    (chartShift P t h : ℝ × Space → CVec3) =ᵐ[chartBase P] fun p => h (p.1 + t, p.2) :=
  Lp.coeFn_compMeasurePreserving h (measurePreserving_shift P t)

/-- **The unitary group `e^{tB}` on `Y₂`** (B0459, tex 7713-7715): the chart translation read
back on `Y₂`.  Its formula is `phaseDilation_ae`. -/
def phaseDilation (t : ℝ) : Yq P 2 →ₗᵢ[ℂ] Yq P 2 :=
  (chartY P).symm.toLinearIsometry.comp ((chartShift P t).comp (chartY P).toLinearIsometry)

theorem chartY_phaseDilation (t : ℝ) (x : Yq P 2) :
    chartY P (phaseDilation P t x) = chartShift P t (chartY P x) :=
  (chartY P).apply_symm_apply _

theorem chartShift_add (s t : ℝ) (h : Lp CVec3 2 (chartBase P)) :
    chartShift P (s + t) h = chartShift P s (chartShift P t h) := by
  apply Lp.ext
  filter_upwards [chartShift_ae P (s + t) h, chartShift_ae P s (chartShift P t h),
    (measurePreserving_shift P s).quasiMeasurePreserving.ae (chartShift_ae P t h)]
    with p e1 e2 e3
  have e3' : (chartShift P t h : ℝ × Space → CVec3) (p.1 + s, p.2) = h (p.1 + s + t, p.2) := e3
  rw [e1, e2, e3', add_assoc]

theorem chartShift_zero (h : Lp CVec3 2 (chartBase P)) : chartShift P 0 h = h := by
  apply Lp.ext
  filter_upwards [chartShift_ae P 0 h] with p e
  rw [e, add_zero]

/-- `e^{(s+t)B} = e^{sB} e^{tB}` (group law). -/
theorem phaseDilation_add (s t : ℝ) (x : Yq P 2) :
    phaseDilation P (s + t) x = phaseDilation P s (phaseDilation P t x) := by
  apply (chartY P).injective
  rw [chartY_phaseDilation, chartY_phaseDilation, chartY_phaseDilation, chartShift_add]

theorem phaseDilation_zero (x : Yq P 2) : phaseDilation P 0 x = x := by
  apply (chartY P).injective
  rw [chartY_phaseDilation, chartShift_zero]

/-- Each `e^{tB}` is unitary: isometric (`phaseDilation P t` is a linear isometry) with inverse
`e^{-tB}`. -/
theorem phaseDilation_neg_apply (t : ℝ) (x : Yq P 2) :
    phaseDilation P t (phaseDilation P (-t) x) = x := by
  rw [← phaseDilation_add, add_neg_cancel, phaseDilation_zero]

theorem chartFwd_shift_chartInv (t : ℝ) (q : AddCircle P × Space) :
    chartFwd P (Prod.map (· + t) id (chartInv P q)) =
      (q.1 + (t : AddCircle P), Real.exp (-(t / 2)) • q.2) := by
  obtain ⟨τ, y⟩ := q
  change (((chartTheta P (τ, y) + t : ℝ) : AddCircle P),
    Real.exp (-((chartTheta P (τ, y) + t) / 2)) • Real.exp (chartTheta P (τ, y) / 2) • y) = _
  refine Prod.ext ?_ ?_
  · change ((chartTheta P (τ, y) + t : ℝ) : AddCircle P) = τ + (t : AddCircle P)
    rw [AddCircle.coe_add, coe_chartTheta]
  · change Real.exp (-((chartTheta P (τ, y) + t) / 2)) • Real.exp (chartTheta P (τ, y) / 2) • y =
      Real.exp (-(t / 2)) • y
    rw [smul_smul, ← Real.exp_add]
    congr 2
    ring

theorem chartJ_ratio (θ t : ℝ) :
    ((chartJ P θ : ℂ))⁻¹ * (chartJ P (θ + t) : ℂ) = (Real.exp (-(3 / 4) * t) : ℂ) := by
  have h0 : chartJ P θ ≠ 0 := (chartJ_pos P θ).ne'
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul]
  congr 1
  rw [inv_mul_eq_iff_eq_mul₀ h0]
  unfold chartJ
  rw [mul_add, Real.exp_add]
  ring

/-- **The group is phase translation composed with the `L²`-normalised dilation** (B0459,
tex 7713-7715): `(e^{tB} w)(τ, y) = e^{-3t/4} w(τ + t, e^{-t/2} y)`, read on the product model
`prodLpEquiv.symm : Y₂ ≃ L²((ℝ/Pℤ) × ℝ³)`. -/
theorem phaseDilation_ae (t : ℝ) (x : Yq P 2) :
    (prodLpEquiv.symm (phaseDilation P t x) : AddCircle P × Space → CVec3) =ᵐ[phaseVol P]
      fun q => (Real.exp (-(3 / 4) * t) : ℂ) •
        (prodLpEquiv.symm x : AddCircle P × Space → CVec3)
          (q.1 + (t : AddCircle P), Real.exp (-(t / 2)) • q.2) := by
  have hS := chartY_symm_ae P (chartShift P t (chartY P x))
  have hT := (measurePreserving_chartInv P).quasiMeasurePreserving.ae_eq_comp
    ((chartMeasure_ac P).ae_le (chartShift_ae P t (chartY P x)))
  have hY := (measurePreserving_chartInv P).quasiMeasurePreserving.ae_eq_comp
    ((chartMeasure_ac P).ae_le
      ((measurePreserving_shift P t).quasiMeasurePreserving.ae_eq_comp (chartY_ae P x)))
  change (prodLpEquiv.symm ((chartY P).symm (chartShift P t (chartY P x))) :
    AddCircle P × Space → CVec3) =ᵐ[phaseVol P] _
  filter_upwards [hS, hT, hY] with q e1 e2 e3
  rw [e1]
  simp only [Function.comp_apply] at e2 e3
  rw [e2]
  change ((chartJ P (chartInv P q).1 : ℂ))⁻¹ •
    (chartY P x : ℝ × Space → CVec3) (Prod.map (· + t) id (chartInv P q)) = _
  rw [e3, chartFwd_shift_chartInv, smul_smul]
  congr 1
  exact chartJ_ratio P _ t

end UnforcedLeray.FreeStress
