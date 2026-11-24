import UnforcedLeray.Lib.Sobolev
import UnforcedLeray.Lib.Cylinder.IBP

/-!
# Smooth periodic fields on the cylinder are Sobolev (INF11 target S4, cylinder part, step 1)


target S4 (`W.cylinder_dense_smooth`); decision D1 of `scoping/README.md` §3 (the cylinder is the
carrier `ℝ × ℝ` with the cell `[-c/2, c/2) × ℝ` and `c`-periodic tests).  Manuscript uses:
B0433 (tex 7550–7576, smooth approximation on the periodic cylinder), B0892 (tex 13970–13985).

## Main declarations
* `iterD`: the classical iterated directional derivative of an `F`-valued function on any real
  normed space;
* `IsCylSmooth c u`: `u` smooth, `c`-periodic in `q`, vanishing for `|η|` large;
* `hasWeakDeriv_cylinder_of_isCylSmooth`: the classical derivatives of such `u` are its periodic
  weak derivatives (cell integration by parts, `Cyl.integral_cell_deriv_q_of_periodic`,
  `Cyl.integral_cell_deriv_eta`);
* `W.ofCylSmooth`: the element of `W^{k,p}(ρ)` on the cylinder with field `u`;
* `eLpNorm_wμ_le_of_vanish'`, `eLpNorm_le_wμ_of_vanish'`: weighted and unweighted norms of
  functions vanishing outside a compact set are comparable (any measure finite on compacts).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology ContDiff

namespace UnforcedLeray.Sob

/-! ### Classical iterated derivatives -/

section IterD

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `∂_{v₁} ⋯ ∂_{vₘ} u` (classical, `F`-valued), same convention as `iterDirDeriv`. -/
def iterD (vs : List E) (u : E → F) : E → F :=
  vs.foldr (fun v w x => fderiv ℝ w x v) u

@[simp] theorem iterD_nil (u : E → F) : iterD [] u = u := rfl

@[simp] theorem iterD_cons (v : E) (vs : List E) (u : E → F) :
    iterD (v :: vs) u = fun x => fderiv ℝ (iterD vs u) x v := rfl

theorem contDiff_iterD {u : E → F} (hu : ContDiff ℝ ∞ u) (vs : List E) :
    ContDiff ℝ ∞ (iterD vs u) := by
  induction vs with
  | nil => simpa using hu
  | cons v vs ih => exact (ContDiff.fderiv_right (m := ∞) ih (by simp)).clm_apply contDiff_const

/-- Iterated derivatives of functions agreeing on an open set agree there. -/
theorem iterD_eqOn {U : Set E} (hU : IsOpen U) {u₁ u₂ : E → F} (h : EqOn u₁ u₂ U)
    (vs : List E) : EqOn (iterD vs u₁) (iterD vs u₂) U := by
  induction vs with
  | nil => exact h
  | cons v vs ih =>
    intro y hy
    simp only [iterD_cons]
    have : iterD vs u₁ =ᶠ[𝓝 y] iterD vs u₂ := Filter.eventually_of_mem (hU.mem_nhds hy) ih
    rw [this.fderiv_eq]

end IterD

/-! ### Smooth periodic fields -/

section CylSmooth

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {c : ℝ}

/-- **Smooth periodic fields** on the cylinder: smooth on `ℝ × ℝ`, `c`-periodic in `q`, and
zero for `|η|` large (the approximants of S4). -/
structure IsCylSmooth (c : ℝ) (u : ℝ × ℝ → F) : Prop where
  smooth : ContDiff ℝ ∞ u
  periodic : ∀ z : ℝ × ℝ, u (z + (c, 0)) = u z
  bounded : ∃ R : ℝ, ∀ z : ℝ × ℝ, R < |z.2| → u z = 0

theorem IsCylSmooth.dir {u : ℝ × ℝ → F} (hu : IsCylSmooth c u) (v : ℝ × ℝ) :
    IsCylSmooth c (fun z => fderiv ℝ u z v) := by
  refine ⟨(ContDiff.fderiv_right (m := ∞) hu.smooth (by simp)).clm_apply contDiff_const,
    fun z => ?_, ?_⟩
  · show fderiv ℝ u (z + (c, 0)) v = fderiv ℝ u z v
    have e : (fun y => u (y + (c, 0))) = u := funext hu.periodic
    have := fderiv_comp_add_right (𝕜 := ℝ) (f := u) (x := z) ((c, 0) : ℝ × ℝ)
    rw [e] at this
    rw [← this]
  · obtain ⟨R, hR⟩ := hu.bounded
    refine ⟨R, fun z hz => ?_⟩
    have hopen : IsOpen {y : ℝ × ℝ | R < |y.2|} :=
      isOpen_lt continuous_const (continuous_abs.comp continuous_snd)
    have hev : u =ᶠ[𝓝 z] fun _ => (0 : F) :=
      Filter.eventually_of_mem (hopen.mem_nhds hz) fun y hy => hR y hy
    show fderiv ℝ u z v = 0
    rw [hev.fderiv_eq]
    simp

theorem IsCylSmooth.iterD {u : ℝ × ℝ → F} (hu : IsCylSmooth c u) (vs : List (ℝ × ℝ)) :
    IsCylSmooth c (iterD vs u) := by
  induction vs with
  | nil => simpa using hu
  | cons v vs ih => exact ih.dir v

theorem IsCylSmooth.smul_test {u : ℝ × ℝ → F} (hu : IsCylSmooth c u) {φ : ℝ × ℝ → ℝ}
    (hφ : IsCylTest c φ) : IsCylSmooth c (fun z => φ z • u z) := by
  refine ⟨hφ.smooth.smul hu.smooth, fun z => by rw [hφ.periodic, hu.periodic], ?_⟩
  obtain ⟨R, hR⟩ := hu.bounded
  exact ⟨R, fun z hz => by rw [hR z hz, smul_zero]⟩

theorem IsCylTest.isCylSmooth {φ : ℝ × ℝ → ℝ} (hφ : IsCylTest c φ) : IsCylSmooth c φ :=
  ⟨hφ.smooth, hφ.periodic, hφ.bounded⟩

theorem cylCell_subset_box (c R : ℝ) :
    cylCell c ∩ {z : ℝ × ℝ | |z.2| ≤ R} ⊆ Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R := by
  rintro z ⟨⟨h1, -⟩, h2⟩
  exact ⟨Ico_subset_Icc_self h1, abs_le.mp h2⟩

omit [NormedSpace ℝ F] in
/-- A continuous function vanishing for `|η| > R` is integrable on the cell. -/
theorem integrableOn_cylCell {h : ℝ × ℝ → F} (hh : Continuous h) {R : ℝ}
    (hR : ∀ z : ℝ × ℝ, R < |z.2| → h z = 0) : IntegrableOn h (cylCell c) := by
  have hK : IsCompact (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R) :=
    isCompact_Icc.prod isCompact_Icc
  refine (hh.continuousOn.integrableOn_compact hK).of_forall_diff_eq_zero
    (measurableSet_cylCell c) fun z hz => ?_
  apply hR
  by_contra hle
  push_neg at hle
  exact hz.2 (cylCell_subset_box c R ⟨hz.1, hle⟩)

theorem IsCylSmooth.integrableOn {u : ℝ × ℝ → F} (hu : IsCylSmooth c u) :
    IntegrableOn u (cylCell c) := by
  obtain ⟨R, hR⟩ := hu.bounded
  exact integrableOn_cylCell hu.smooth.continuous hR

theorem cyl_cell_eq (c : ℝ) : Cyl.cell c = cylCell c := by
  simp [Cyl.cell, cylCell, neg_div]

/-- **Cell integration by parts**: the cell integral of a directional derivative of a smooth
periodic field vanishing for `|η|` large is zero. -/
theorem integral_cylCell_fderiv_eq_zero [CompleteSpace F] (hc : 0 < c) {h : ℝ × ℝ → F}
    (hh : IsCylSmooth c h) (v : ℝ × ℝ) : ∫ z in cylCell c, fderiv ℝ h z v = 0 := by
  have hd : Differentiable ℝ h := hh.smooth.differentiable (by simp)
  have hsplit : ∀ z, fderiv ℝ h z v =
      v.1 • fderiv ℝ h z ((1 : ℝ), (0 : ℝ)) + v.2 • fderiv ℝ h z ((0 : ℝ), (1 : ℝ)) := by
    intro z
    rw [← map_smul, ← map_smul, ← map_add]
    congr 1
    ext <;> simp
  have hiq : IntegrableOn (fun z => fderiv ℝ h z ((1 : ℝ), (0 : ℝ))) (cylCell c) :=
    (hh.dir _).integrableOn
  have hie : IntegrableOn (fun z => fderiv ℝ h z ((0 : ℝ), (1 : ℝ))) (cylCell c) :=
    (hh.dir _).integrableOn
  have hq : ∫ z in cylCell c, fderiv ℝ h z ((1 : ℝ), (0 : ℝ)) = 0 := by
    rw [← cyl_cell_eq]
    refine Cyl.integral_cell_deriv_q_of_periodic (F := h) hc (fun z => ?_) (fun q η => ?_)
      (by rw [cyl_cell_eq]; exact hiq)
    · have e : ((z.1 + c, z.2) : ℝ × ℝ) = z + (c, 0) := by ext <;> simp
      show h (z.1 + c, z.2) = h z
      rw [e]
      exact hh.periodic z
    · have hl : HasDerivAt (fun q' : ℝ => ((q', η) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) q :=
        (hasDerivAt_id' q).prodMk (hasDerivAt_const q η)
      exact (hd (q, η)).hasFDerivAt.comp_hasDerivAt q hl
  have he : ∫ z in cylCell c, fderiv ℝ h z ((0 : ℝ), (1 : ℝ)) = 0 := by
    rw [← cyl_cell_eq]
    refine Cyl.integral_cell_deriv_eta (F := h) (fun q η => ?_) (by rw [cyl_cell_eq]; exact hh.integrableOn)
      (by rw [cyl_cell_eq]; exact hie)
    have hl : HasDerivAt (fun η' : ℝ => ((q, η') : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) η :=
      (hasDerivAt_const η q).prodMk (hasDerivAt_id' η)
    exact (hd (q, η)).hasFDerivAt.comp_hasDerivAt η hl
  simp_rw [hsplit]
  rw [integral_add (f := fun z => v.1 • fderiv ℝ h z ((1 : ℝ), (0 : ℝ)))
    (g := fun z => v.2 • fderiv ℝ h z ((0 : ℝ), (1 : ℝ))) (hiq.smul v.1) (hie.smul v.2),
    integral_smul, integral_smul, hq, he,
    smul_zero, smul_zero, add_zero]

/-- **First-order periodic weak derivatives of smooth periodic fields.** -/
theorem hasWeakDeriv_cylinder_dir [CompleteSpace F] (hc : 0 < c) {u : ℝ × ℝ → F}
    (hu : IsCylSmooth c u) (v : ℝ × ℝ) :
    HasWeakDeriv (cylinder c) [v] u (fun z => fderiv ℝ u z v) := by
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · exact (hu.smul_test ((cylinder c).deriv_mem hφ v)).integrableOn
  · exact ((hu.dir v).smul_test hφ).integrableOn
  · have hφ' : IsCylTest c φ := hφ
    have hd : ∀ z, fderiv ℝ (fun y => φ y • u y) z v =
        fderiv ℝ φ z v • u z + φ z • fderiv ℝ u z v := by
      intro z
      have h1 : DifferentiableAt ℝ φ z := (hφ'.smooth.differentiable (by simp)) z
      have h2 : DifferentiableAt ℝ u z := (hu.smooth.differentiable (by simp)) z
      show fderiv ℝ (φ • u) z v = _
      rw [fderiv_smul h1 h2]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smulRight_apply]
      rw [add_comm]
    have h0 := integral_cylCell_fderiv_eq_zero hc (hu.smul_test hφ') v
    simp_rw [hd] at h0
    have i1 : IntegrableOn (fun z => fderiv ℝ φ z v • u z) (cylCell c) :=
      (hu.smul_test (hφ'.dirDeriv v)).integrableOn
    have i2 : IntegrableOn (fun z => φ z • fderiv ℝ u z v) (cylCell c) :=
      ((hu.dir v).smul_test hφ').integrableOn
    rw [integral_add i1 i2, add_eq_zero_iff_eq_neg] at h0
    simp only [iterDirDeriv_singleton, cylinder_μ, List.length_singleton, pow_one, neg_smul,
      one_smul]
    exact h0

/-- **Smooth periodic fields are periodic-weakly differentiable** for every word. -/
theorem hasWeakDeriv_cylinder_of_isCylSmooth [CompleteSpace F] (hc : 0 < c) {u : ℝ × ℝ → F}
    (hu : IsCylSmooth c u) (vs : List (ℝ × ℝ)) : HasWeakDeriv (cylinder c) vs u (iterD vs u) := by
  induction vs with
  | nil => exact HasWeakDeriv.nil fun φ hφ => (hu.smul_test hφ).integrableOn
  | cons v vs ih => exact ih.cons (hasWeakDeriv_cylinder_dir hc (hu.iterD vs) v)

end CylSmooth

/-! ### Weighted norms of functions vanishing outside a compact set -/

section Compare

variable {E : Type*} [TopologicalSpace E] [T2Space E] [MeasurableSpace E] [OpensMeasurableSpace E]
  {F : Type*} [NormedAddCommGroup F]

theorem eLpNorm_wμ_le_of_vanish' (μ : Measure E) (ρ : Weight E) {K : Set E} (hK : IsCompact K)
    {p : ℝ≥0∞} (hp : p ≠ ⊤) : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ h : E → F,
      (∀ᵐ x ∂μ, x ∉ K → h x = 0) → eLpNorm h p (wμ μ ρ) ≤ C * eLpNorm h p μ := by
  obtain ⟨a, B, _, hab⟩ := ρ.locBdd K hK
  have hKm : MeasurableSet K := hK.measurableSet
  refine ⟨ENNReal.ofReal B ^ (1 / p).toReal, ENNReal.rpow_ne_top_of_nonneg (by positivity)
    ENNReal.ofReal_ne_top, fun h hh => ?_⟩
  have hind : h =ᵐ[μ] K.indicator h := by
    filter_upwards [hh] with x hx
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK]
    · rw [indicator_of_notMem hxK, hx hxK]
  have hle : (wμ μ ρ).restrict K ≤ ENNReal.ofReal B • μ.restrict K := by
    rw [Measure.le_iff]
    intro s hs
    rw [Measure.restrict_apply hs, Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul,
      wμ, withDensity_apply _ (hs.inter hKm)]
    calc ∫⁻ x in s ∩ K, ENNReal.ofReal (ρ x) ∂μ ≤ ∫⁻ _ in s ∩ K, ENNReal.ofReal B ∂μ :=
          setLIntegral_mono' (hs.inter hKm) fun x hx => ENNReal.ofReal_le_ofReal (hab x hx.2).2
      _ = ENNReal.ofReal B * μ (s ∩ K) := setLIntegral_const _ _
  rw [eLpNorm_congr_ae ((ae_eq_wμ_iff μ ρ).mpr hind), eLpNorm_congr_ae hind,
    eLpNorm_indicator_eq_eLpNorm_restrict hKm, eLpNorm_indicator_eq_eLpNorm_restrict hKm]
  calc eLpNorm h p ((wμ μ ρ).restrict K)
      ≤ eLpNorm h p (ENNReal.ofReal B • μ.restrict K) := eLpNorm_mono_measure _ hle
    _ = ENNReal.ofReal B ^ (1 / p).toReal * eLpNorm h p (μ.restrict K) := by
        rw [eLpNorm_smul_measure_of_ne_top hp]; rfl

theorem eLpNorm_le_wμ_of_vanish' (μ : Measure E) (ρ : Weight E) {K : Set E} (hK : IsCompact K)
    {p : ℝ≥0∞} (hp : p ≠ ⊤) : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ h : E → F,
      (∀ᵐ x ∂μ, x ∉ K → h x = 0) → eLpNorm h p μ ≤ C * eLpNorm h p (wμ μ ρ) := by
  obtain ⟨a, B, ha, hab⟩ := ρ.locBdd K hK
  have hKm : MeasurableSet K := hK.measurableSet
  refine ⟨ENNReal.ofReal a⁻¹ ^ (1 / p).toReal, ENNReal.rpow_ne_top_of_nonneg (by positivity)
    ENNReal.ofReal_ne_top, fun h hh => ?_⟩
  have hind : h =ᵐ[μ] K.indicator h := by
    filter_upwards [hh] with x hx
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK]
    · rw [indicator_of_notMem hxK, hx hxK]
  have hle : μ.restrict K ≤ ENNReal.ofReal a⁻¹ • (wμ μ ρ).restrict K := by
    rw [Measure.le_iff]
    intro s hs
    rw [Measure.restrict_apply hs, Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul,
      wμ, withDensity_apply _ (hs.inter hKm)]
    have h1 : ENNReal.ofReal a * μ (s ∩ K) ≤ ∫⁻ x in s ∩ K, ENNReal.ofReal (ρ x) ∂μ := by
      rw [← setLIntegral_const]
      exact setLIntegral_mono' (hs.inter hKm) fun x hx => ENNReal.ofReal_le_ofReal (hab x hx.2).1
    calc μ (s ∩ K) = ENNReal.ofReal a⁻¹ * (ENNReal.ofReal a * μ (s ∩ K)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr ha.le), inv_mul_cancel₀ ha.ne',
            ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal a⁻¹ * ∫⁻ x in s ∩ K, ENNReal.ofReal (ρ x) ∂μ := by gcongr
  rw [eLpNorm_congr_ae ((ae_eq_wμ_iff μ ρ).mpr hind), eLpNorm_congr_ae hind,
    eLpNorm_indicator_eq_eLpNorm_restrict hKm, eLpNorm_indicator_eq_eLpNorm_restrict hKm]
  calc eLpNorm h p (μ.restrict K)
      ≤ eLpNorm h p (ENNReal.ofReal a⁻¹ • (wμ μ ρ).restrict K) := eLpNorm_mono_measure _ hle
    _ = ENNReal.ofReal a⁻¹ ^ (1 / p).toReal * eLpNorm h p ((wμ μ ρ).restrict K) := by
        rw [eLpNorm_smul_measure_of_ne_top hp]; rfl

end Compare

/-! ### The element of `W` on the cylinder -/

section WCyl

variable {F : Type*} [NormedAddCommGroup F] {𝕜 : Type*} [RCLike 𝕜]
  [InnerProductSpace 𝕜 F] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] [FiniteDimensional 𝕜 F]
  {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {c : ℝ}

/-- A smooth periodic field vanishing for `|η|` large lies in `L^p(ρ)` on the cell. -/
theorem IsCylSmooth.memLp {u : ℝ × ℝ → F} (hu : IsCylSmooth c u) (ρ : Weight (ℝ × ℝ))
    (q : ℝ≥0∞) : MemLp u q (wμ (cylinder c).μ ρ) := by
  obtain ⟨R, hR⟩ := hu.bounded
  set K : Set (ℝ × ℝ) := Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R with hKdef
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hind : u =ᵐ[wμ (cylinder c).μ ρ] K.indicator u := by
    refine (ae_eq_wμ_iff _ ρ).mpr ?_
    rw [cylinder_μ]
    filter_upwards [ae_restrict_mem (measurableSet_cylCell c)] with z hz
    by_cases hzK : z ∈ K
    · rw [indicator_of_mem hzK]
    · rw [indicator_of_notMem hzK]
      apply hR
      by_contra hle
      push_neg at hle
      exact hzK (cylCell_subset_box c R ⟨hz, hle⟩)
  refine (memLp_congr_ae hind).mpr ?_
  rw [memLp_indicator_iff_restrict hK.measurableSet]
  haveI : IsFiniteMeasure ((wμ (cylinder c).μ ρ).restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact wμ_lt_top hK⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hu.smooth.continuous.continuousOn
  exact MemLp.of_bound hu.smooth.continuous.aestronglyMeasurable C
    ((ae_restrict_iff' hK.measurableSet).mpr (Eventually.of_forall hC))

variable (ρ : Weight (ℝ × ℝ)) (𝕜 k p)

/-- **The element of `W^{k,p}(ρ)` on the cylinder with a smooth periodic field** (its
components are the classical derivatives). -/
def W.ofCylSmooth (hc : 0 < c) (u : ℝ × ℝ → F) (hu : IsCylSmooth c u) :
    W (cylinder c) ρ 𝕜 F k p :=
  have := completeSpace_of_finiteDimensional 𝕜 F
  W.ofFields (fun α => iterD ((cylinder c).word α) u) (fun α => (hu.iterD _).memLp ρ p)
    (fun α => hasWeakDeriv_cylinder_of_isCylSmooth hc hu _)

variable {ρ 𝕜 k p}

theorem W.deriv_ofCylSmooth (hc : 0 < c) (u : ℝ × ℝ → F) (hu : IsCylSmooth c u)
    (α : Idx 2 k) :
    ⇑(W.deriv (cylinder c) ρ 𝕜 F k p α (W.ofCylSmooth 𝕜 k p ρ hc u hu)) =ᵐ[wμ (cylinder c).μ ρ]
      iterD ((cylinder c).word α) u :=
  ((hu.iterD _).memLp ρ p).coeFn_toLp

theorem W.value_ofCylSmooth (hc : 0 < c) (u : ℝ × ℝ → F) (hu : IsCylSmooth c u) :
    ⇑(W.value (cylinder c) ρ 𝕜 F k p (W.ofCylSmooth 𝕜 k p ρ hc u hu)) =ᵐ[wμ (cylinder c).μ ρ]
      u :=
  W.deriv_ofCylSmooth hc u hu Idx.zero

end WCyl

end UnforcedLeray.Sob
