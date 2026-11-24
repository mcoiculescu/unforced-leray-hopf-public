import UnforcedLeray.Units.B0005.Unique
import UnforcedLeray.Blueprint.Package
import UnforcedLeray.Lib.PhaseTrace

/-!
# B0005 bridge, part 1: real periodic fields of the interface as elements of `𝒴₂`

Blueprint unit B0005 (tex 136–147) against the interface layer `Blueprint/Package.lean`
(`IsY2Div`, `InPeriodicGraph`, lines 153–191 of that file). The interface encodes a field of
`𝒴_{2,div}` as a real `𝒯`-periodic function `f : ℝ → SpatialField`, jointly measurable and
square integrable on the period slab `(0, 𝒯] × ℝ³`. This file realizes such a field as an
element `toY 𝒯 f` of the Bochner model `𝒴₂ = PhaseSpace.Yq 𝒯 2` (decision D2):

* `cplxL`, `reL`, `imL`: the complexification `ℝ³ → ℂ³` and the real and imaginary parts, as
  real-linear maps;
* `IsY2 𝒯 f`: the first three clauses of `Blueprint.IsY2Div` (periodic, measurable, `L²` on the
  slab); `Blueprint.IsY2Div.isY2`;
* `pathOf f t`: the class in `L²(ℝ³; ℂ³)` of the slice `f(t, ·)` (`BochnerTime.toPathLq`);
* `toY 𝒯 f`: the element of `𝒴₂` whose value at the phase `t mod 𝒯` is `pathOf f t`, with
  `toY_ae`: `(toY 𝒯 f)(t mod 𝒯) = pathOf f t` for almost every `t ∈ ℝ`, and
  `ae_pathOf_eq`: `pathOf f t = f(t, ·)` a.e. for almost every `t ∈ ℝ`.

`ae_of_periodic` passes a periodic almost-everywhere property from one period to the line.

Status: infrastructure for the B0005 bridge. Theorem A is not proved in Lean.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.B0005

open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace

/-! ### Complexification of real vectors -/

/-- The complexification `v ↦ v + 0i` of `ℝ³` into `ℂ³`, as a real-linear map. -/
def cplxL : Space →L[ℝ] CVec3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (fun i => (v i : ℂ))
      map_add' := fun x y => by ext i; simp
      map_smul' := fun c x => by ext i; simp }

@[simp] theorem cplxL_apply (v : Space) (i : Fin 3) : cplxL v i = (v i : ℂ) := rfl

/-- The coordinatewise real part `ℂ³ → ℝ³`. -/
def reL : CVec3 →L[ℝ] Space :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun i => (x i).re)
      map_add' := fun x y => by ext i; simp
      map_smul' := fun c x => by ext i; simp }

/-- The coordinatewise imaginary part `ℂ³ → ℝ³`. -/
def imL : CVec3 →L[ℝ] Space :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun i => (x i).im)
      map_add' := fun x y => by ext i; simp
      map_smul' := fun c x => by ext i; simp }

@[simp] theorem reL_apply (x : CVec3) (i : Fin 3) : reL x i = (x i).re := rfl
@[simp] theorem imL_apply (x : CVec3) (i : Fin 3) : imL x i = (x i).im := rfl

theorem cplxL_re_add_im (x : CVec3) : cplxL (reL x) + Complex.I • cplxL (imL x) = x := by
  ext i
  simp only [PiLp.add_apply, PiLp.smul_apply, cplxL_apply, reL_apply, imL_apply, smul_eq_mul]
  rw [mul_comm Complex.I]
  exact Complex.re_add_im (x i)

theorem norm_cplxL (v : Space) : ‖cplxL v‖ = ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp only [cplxL_apply, Complex.norm_real]

/-- The bilinear dot product of two complexified vectors is the real inner product. -/
theorem dotL_cplxL (a b : Space) : dotL (cplxL a) (cplxL b) = ((inner ℝ b a : ℝ) : ℂ) := by
  rw [dotL_apply]
  simp only [cplxL_apply, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  push_cast
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ### Periodic almost-everywhere properties -/

/-- A `𝒯`-periodic property that holds for almost every `t ∈ (0, 𝒯]` holds for almost every
`t ∈ ℝ`. -/
theorem ae_of_periodic {T : ℝ} (hT : 0 < T) {p : ℝ → Prop} (hp : ∀ t, p (t + T) ↔ p t)
    (h : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) T)), p t) : ∀ᵐ t : ℝ, p t := by
  rw [ae_restrict_iff' measurableSet_Ioc] at h
  have hper : Function.Periodic (fun t => p t) T := fun t => propext (hp t)
  rw [ae_iff] at h ⊢
  refine measure_mono_null (t := ⋃ k : ℤ,
      (fun t => t + (-(k • T))) ⁻¹' {t : ℝ | ¬(t ∈ Ioc 0 T → p t)}) ?_
    (measure_iUnion_null fun k => by rw [measure_preimage_add_right]; exact h)
  intro t ht
  simp only [mem_ofPred_eq] at ht
  refine mem_iUnion.mpr ⟨toIocDiv hT 0 t, ?_⟩
  have hmem := sub_toIocDiv_zsmul_mem_Ioc hT 0 t
  rw [zero_add] at hmem
  have e : p (t - toIocDiv hT 0 t • T) = p t := hper.sub_zsmul_eq (toIocDiv hT 0 t)
  simp only [mem_preimage, mem_ofPred_eq, ← sub_eq_add_neg, e]
  exact fun h' => ht (h' hmem)

/-! ### Real periodic fields of `𝒴₂` -/

/-- The first three clauses of `Blueprint.IsY2Div` (`Package.lean`): a `𝒯`-periodic real field,
jointly measurable, square integrable on the period slab `(0, 𝒯] × ℝ³`. -/
structure IsY2 (𝒯 : ℝ) (f : ℝ → SpatialField) : Prop where
  periodic : Function.Periodic f 𝒯
  measurable : AEStronglyMeasurable (fun z : SpaceTime => f z.1 z.2) volume
  memL2 : MemLp (fun z : SpaceTime => f z.1 z.2) 2 (volume.restrict (Blueprint.periodSlab 𝒯))

theorem _root_.UnforcedLeray.Blueprint.IsY2Div.isY2 {𝒯 : ℝ} {f : ℝ → SpatialField}
    (hf : Blueprint.IsY2Div 𝒯 f) : IsY2 𝒯 f :=
  ⟨hf.periodic, hf.measurable, hf.memL2⟩

/-- The complexified joint field `(t, y) ↦ f(t)(y) ∈ ℂ³`. -/
def jointC (f : ℝ → SpatialField) (z : ℝ × Space) : CVec3 := cplxL (f z.1 z.2)

/-- The class in `L²(ℝ³; ℂ³)` of the slice `y ↦ f(t)(y)` (`0` if the slice is not in `L²`). -/
def pathOf (f : ℝ → SpatialField) (t : ℝ) : Lp CVec3 2 (volume : Measure Space) :=
  BochnerTime.toPathLq 2 volume (jointC f) t

section Realize

variable {𝒯 : ℝ} {f : ℝ → SpatialField}

theorem IsY2.slab_eq (𝒯 : ℝ) :
    (volume : Measure SpaceTime).restrict (Blueprint.periodSlab 𝒯) =
      (volume.restrict (Ioc (0 : ℝ) 𝒯)).prod (volume : Measure Space) := by
  rw [Blueprint.periodSlab, Measure.volume_eq_prod, ← Measure.prod_restrict,
    Measure.restrict_univ]

theorem IsY2.memLp_jointC (hf : IsY2 𝒯 f) :
    MemLp (jointC f) 2 ((volume.restrict (Ioc (0 : ℝ) 𝒯)).prod (volume : Measure Space)) := by
  rw [← IsY2.slab_eq]
  exact cplxL.comp_memLp' hf.memL2

theorem IsY2.aestronglyMeasurable_jointC (hf : IsY2 𝒯 f) :
    AEStronglyMeasurable (jointC f) volume :=
  cplxL.continuous.comp_aestronglyMeasurable hf.measurable

theorem jointC_periodic (hf : IsY2 𝒯 f) (t : ℝ) (y : Space) :
    jointC f (t + 𝒯, y) = jointC f (t, y) := by
  simp only [jointC, hf.periodic t]

theorem pathOf_periodic (hf : IsY2 𝒯 f) (t : ℝ) : pathOf f (t + 𝒯) = pathOf f t := by
  have h : (fun y => jointC f (t + 𝒯, y)) = fun y => jointC f (t, y) :=
    funext fun y => jointC_periodic hf t y
  unfold pathOf
  by_cases hm : MemLp (fun y => jointC f (t, y)) 2 (volume : Measure Space)
  · have hm' : MemLp (fun y => jointC f (t + 𝒯, y)) 2 (volume : Measure Space) := by
      rw [h]; exact hm
    rw [BochnerTime.toPathLq_of_memLp hm, BochnerTime.toPathLq_of_memLp hm']
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun y => jointC_periodic hf t y)
  · have hm' : ¬ MemLp (fun y => jointC f (t + 𝒯, y)) 2 (volume : Measure Space) := by
      rw [h]; exact hm
    rw [BochnerTime.toPathLq_of_not_memLp hm, BochnerTime.toPathLq_of_not_memLp hm']

/-- For almost every `t ∈ ℝ` the slice `f(t, ·)` is in `L²(ℝ³)`. -/
theorem IsY2.ae_memLp_slice (hf : IsY2 𝒯 f) (hT : 0 < 𝒯) :
    ∀ᵐ t : ℝ, MemLp (fun y => jointC f (t, y)) 2 (volume : Measure Space) := by
  refine ae_of_periodic hT (fun t => by simp only [jointC_periodic hf]) ?_
  have hm := hf.memLp_jointC
  have hint := (hm.integrable_norm_rpow two_ne_zero ENNReal.ofNat_ne_top).prod_right_ae
  filter_upwards [hint, hm.aestronglyMeasurable.prodMk_left] with t ht hmt
  rw [memLp_two_iff_integrable_sq_norm hmt]
  simpa using ht

/-- For almost every `t ∈ ℝ`, `pathOf f t` is the class of the slice `f(t, ·)`. -/
theorem IsY2.ae_pathOf_eq (hf : IsY2 𝒯 f) (hT : 0 < 𝒯) :
    ∀ᵐ t : ℝ, (pathOf f t : Space → CVec3) =ᵐ[volume] fun y => jointC f (t, y) := by
  filter_upwards [hf.ae_memLp_slice hT] with t ht
  unfold pathOf
  rw [BochnerTime.toPathLq_of_memLp ht]
  exact MemLp.coeFn_toLp ht

instance fact_two_ne_top : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩

theorem IsY2.aestronglyMeasurable_pathOf (hf : IsY2 𝒯 f) :
    AEStronglyMeasurable (pathOf f) (volume.restrict (Ioc (0 : ℝ) 𝒯)) :=
  (BochnerTime.stronglyMeasurable_toPath_Lq hf.memLp_jointC).1

theorem IsY2.memLp_pathOf (hf : IsY2 𝒯 f) :
    MemLp (pathOf f) 2 (volume.restrict (Ioc (0 : ℝ) 𝒯)) := by
  have h := BochnerTime.stronglyMeasurable_toPath_Lq hf.memLp_jointC
  refine ⟨h.1, ?_⟩
  have h2 : eLpNorm (pathOf f) 2 (volume.restrict (Ioc (0 : ℝ) 𝒯)) ^ (2 : ℝ≥0∞).toReal < ⊤ := by
    rw [BochnerTime.eLpNorm_rpow_eq_lintegral two_ne_zero ENNReal.ofNat_ne_top]
    unfold pathOf
    rw [h.2]
    exact ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg hf.memLp_jointC.2.ne
  exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).mp h2

end Realize

/-! ### The circle chart `AddCircle 𝒯 → (0, 𝒯]` -/

section Circle

variable (𝒯 : ℝ) [hT : Fact (0 < 𝒯)]

/-- The representative in `(0, 𝒯]` of a phase. -/
def phaseRep (τ : AddCircle 𝒯) : ℝ := (AddCircle.equivIoc 𝒯 0 τ : ℝ)

theorem measurable_phaseRep : Measurable (phaseRep 𝒯) :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIoc 𝒯 0).measurable

theorem phase_phaseRep (τ : AddCircle 𝒯) : phase 𝒯 (phaseRep 𝒯 τ) = τ :=
  AddCircle.coe_equivIoc

theorem phaseRep_phase {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 𝒯) : phaseRep 𝒯 (phase 𝒯 t) = t := by
  have ht' : t ∈ Ioc (0 : ℝ) (0 + 𝒯) := by rwa [zero_add]
  simp only [phaseRep, phase, AddCircle.equivIoc_coe_eq ht']

theorem measurePreserving_phaseRep :
    MeasurePreserving (phaseRep 𝒯) (AddCircle.haarAddCircle (T := 𝒯))
      ((ENNReal.ofReal 𝒯)⁻¹ • volume.restrict (Ioc (0 : ℝ) 𝒯)) := by
  have hmp := measurePreserving_phase 𝒯
  refine ⟨measurable_phaseRep 𝒯, ?_⟩
  rw [← hmp.map_eq, Measure.map_map (measurable_phaseRep 𝒯) hmp.measurable]
  have hae : (phaseRep 𝒯 ∘ phase 𝒯) =ᵐ[(ENNReal.ofReal 𝒯)⁻¹ • volume.restrict (Ioc (0 : ℝ) 𝒯)]
      id := by
    refine Measure.ae_smul_measure ?_ _
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact phaseRep_phase 𝒯 ht
  rw [Measure.map_congr hae, Measure.map_id]

end Circle

section ToY

variable (𝒯 : ℝ) [hT : Fact (0 < 𝒯)]

theorem IsY2.memLp_circle {f : ℝ → SpatialField} (hf : IsY2 𝒯 f) :
    MemLp (pathOf f ∘ phaseRep 𝒯) 2 (AddCircle.haarAddCircle (T := 𝒯)) := by
  have hm := hf.memLp_pathOf.smul_measure (c := (ENNReal.ofReal 𝒯)⁻¹)
    (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hT.out).ne')
  exact hm.comp_measurePreserving (measurePreserving_phaseRep 𝒯)

open Classical in
/-- **The element of `𝒴₂` of a real periodic field** of the interface (`Package.lean`):
its value at the phase `t mod 𝒯` is the class of `f(t, ·)`, complexified. Junk `0` if `f` is
not in `L²` on the slab; every statement assumes `IsY2 𝒯 f`. -/
def toY (f : ℝ → SpatialField) : Y 𝒯 2 :=
  if h : MemLp (pathOf f ∘ phaseRep 𝒯) 2 (AddCircle.haarAddCircle (T := 𝒯)) then h.toLp _
  else 0

variable {𝒯}

/-- `(toY 𝒯 f)(t mod 𝒯) = pathOf f t` for almost every `t ∈ ℝ`. -/
theorem IsY2.toY_ae {f : ℝ → SpatialField} (hf : IsY2 𝒯 f) :
    ∀ᵐ t : ℝ, toY 𝒯 f (t : AddCircle 𝒯) = pathOf f t := by
  have hm := hf.memLp_circle 𝒯
  have h1 : (toY 𝒯 f : AddCircle 𝒯 → Lp CVec3 2 volume) =ᵐ[AddCircle.haarAddCircle]
      pathOf f ∘ phaseRep 𝒯 := by
    simp only [toY, hm, dite_true]
    exact MemLp.coeFn_toLp hm
  have h2 := (measurePreserving_phase 𝒯).quasiMeasurePreserving.ae_eq_comp h1
  refine ae_of_periodic hT.out (fun t => ?_) ?_
  · rw [pathOf_periodic hf]
    have : ((t + 𝒯 : ℝ) : AddCircle 𝒯) = (t : AddCircle 𝒯) := by simp
    rw [this]
  · have hne : (ENNReal.ofReal 𝒯)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top
    have h3 : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 𝒯)),
        toY 𝒯 f (phase 𝒯 t) = pathOf f (phaseRep 𝒯 (phase 𝒯 t)) := by
      exact (Measure.ae_ennreal_smul_measure_iff hne).mp h2
    filter_upwards [h3, ae_restrict_mem measurableSet_Ioc] with t ht ht'
    rw [phaseRep_phase 𝒯 ht'] at ht
    exact ht

end ToY

end UnforcedLeray.B0005
