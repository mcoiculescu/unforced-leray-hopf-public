import UnforcedLeray.Lib.SobolevC.CylExtend
import UnforcedLeray.Lib.SobolevB.Density
import UnforcedLeray.Lib.SobolevB.Smooth

/-!
# From the cylinder carrier `ℝ × ℝ` to `ℝ²` (INF11 target S4, cylinder part, step 3)


(S4); decision D1 of `scoping/README.md` §3 (cylinder carrier `ℝ × ℝ`).  The mollifier and Leibniz
machinery of `Lib/SobolevB` lives on `Eucl n`; this module moves the periodic extensions of
`CylExtend` there along the measure-preserving linear equivalence `toPlane : Eucl 2 ≃ ℝ × ℝ`.

## Main declarations
* `toPlane`, `measurePreserving_toPlane`, `toPlane_symm_cylDir`;
* `iterDirDeriv_comp_clm`, `iterD_comp_clm`: chain rule for iterated derivatives along linear maps;
* `hasWeakDeriv_comp_toPlane`: `ℝ × ℝ` weak derivatives become `wholeSpace 2` weak derivatives;
* `map_cylinder_word`: the cylinder words become the coordinate words of `Eucl 2`;
* `eLpNorm_cell_inter_lt_top`, `memLp_box_perExt`, `memLp_boxE_perExt`,
  `locallyIntegrable_perExt_comp`: local `L^p` bounds for the periodic extension of a weighted
  `L^p(cell)` field.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology ContDiff

namespace UnforcedLeray.Sob

/-! ### The equivalence `Eucl 2 ≃ ℝ × ℝ` -/

/-- `y ↦ (y 0, y 1)`. -/
def toPlane : Eucl 2 ≃L[ℝ] ℝ × ℝ :=
  (EuclideanSpace.equiv (Fin 2) ℝ).trans (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)

theorem toPlane_apply (y : Eucl 2) : toPlane y = (y 0, y 1) := rfl

@[simp] theorem toPlane_symm_apply_zero (z : ℝ × ℝ) : (toPlane.symm z) 0 = z.1 := by
  have h := toPlane.apply_symm_apply z
  rw [toPlane_apply] at h
  exact congrArg Prod.fst h

@[simp] theorem toPlane_symm_apply_one (z : ℝ × ℝ) : (toPlane.symm z) 1 = z.2 := by
  have h := toPlane.apply_symm_apply z
  rw [toPlane_apply] at h
  exact congrArg Prod.snd h

theorem toPlane_e (i : Fin 2) : toPlane (e i) = cylDir i := by
  fin_cases i <;> simp [toPlane_apply, e, cylDir]

theorem toPlane_symm_cylDir (i : Fin 2) : toPlane.symm (cylDir i) = e i := by
  rw [← toPlane_e, toPlane.symm_apply_apply]

theorem measurePreserving_toPlane : MeasurePreserving toPlane volume volume := by
  have h : ⇑toPlane = ⇑(MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ) ∘ WithLp.ofLp := by
    funext y; rfl
  rw [h]
  exact (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))

theorem measurePreserving_toPlane_symm : MeasurePreserving toPlane.symm volume volume := by
  have h : ⇑toPlane.symm =
      WithLp.toLp 2 ∘ ⇑(MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ).symm := by
    funext z
    apply toPlane.injective
    rw [toPlane.apply_symm_apply, toPlane_apply]
    rfl
  rw [h]
  exact (PiLp.volume_preserving_toLp (Fin 2)).comp
    (MeasurePreserving.symm _ (volume_preserving_finTwoArrow ℝ))

theorem measurableEmbedding_toPlane : MeasurableEmbedding toPlane :=
  toPlane.toHomeomorph.measurableEmbedding

theorem measurableEmbedding_toPlane_symm : MeasurableEmbedding toPlane.symm :=
  toPlane.symm.toHomeomorph.measurableEmbedding

/-! ### Chain rule along linear maps -/

section Chain

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem iterDirDeriv_comp_clm (L : E →L[ℝ] E') {φ : E' → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (vs : List E) : iterDirDeriv vs (φ ∘ L) = iterDirDeriv (vs.map L) φ ∘ L := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    funext x
    simp only [iterDirDeriv_cons, List.map_cons, Function.comp_apply]
    rw [ih]
    have hd : DifferentiableAt ℝ (iterDirDeriv (vs.map L) φ) (L x) :=
      ((contDiff_iterDirDeriv hφ _).differentiable (by simp)) _
    rw [fderiv_comp x hd L.differentiableAt, L.fderiv]
    rfl

theorem iterD_comp_clm (L : E →L[ℝ] E') {u : E' → F} (hu : ContDiff ℝ ∞ u) (vs : List E) :
    iterD vs (u ∘ L) = iterD (vs.map L) u ∘ L := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    funext x
    simp only [iterD_cons, List.map_cons, Function.comp_apply]
    rw [ih]
    have hd : DifferentiableAt ℝ (iterD (vs.map L) u) (L x) :=
      ((contDiff_iterD hu _).differentiable (by simp)) _
    rw [fderiv_comp x hd L.differentiableAt, L.fderiv]
    rfl

end Chain

/-! ### Weak derivatives along `toPlane` -/

section Weak

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Transfer of weak derivatives** from `ℝ × ℝ` (directions `cylDir`) to `Eucl 2`. -/
theorem hasWeakDeriv_comp_toPlane {vs : List (ℝ × ℝ)} {f g : ℝ × ℝ → F}
    (h : HasWeakDeriv (wholeSpaceOf (ℝ × ℝ) volume cylDir) vs f g) :
    HasWeakDeriv (wholeSpace 2) (vs.map toPlane.symm) (f ∘ toPlane) (g ∘ toPlane) := by
  have hmp := measurePreserving_toPlane
  have hemb := measurableEmbedding_toPlane
  have hadm : ∀ φ : Eucl 2 → ℝ, (wholeSpace 2).Adm φ →
      (wholeSpaceOf (ℝ × ℝ) volume cylDir).Adm (φ ∘ toPlane.symm) := fun φ hφ =>
    ⟨hφ.1.comp toPlane.symm.contDiff, hφ.2.comp_homeomorph toPlane.symm.toHomeomorph⟩
  have hit : ∀ φ : Eucl 2 → ℝ, (wholeSpace 2).Adm φ → ∀ ws : List (ℝ × ℝ),
      iterDirDeriv ws (φ ∘ toPlane.symm) = iterDirDeriv (ws.map toPlane.symm) φ ∘ toPlane.symm :=
    fun φ hφ ws => iterDirDeriv_comp_clm (toPlane.symm : ℝ × ℝ →L[ℝ] Eucl 2) hφ.1 ws
  have hfun : ∀ (a : Eucl 2 → ℝ) (u : ℝ × ℝ → F),
      (fun z => (a ∘ toPlane.symm) z • u z) ∘ toPlane = fun y => a y • (u ∘ toPlane) y := by
    intro a u
    funext y
    simp only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · have h1 := h.int_left _ (hadm φ hφ)
    rw [hit φ hφ] at h1
    have h2 := (hmp.integrable_comp_emb hemb).mpr h1
    rw [hfun] at h2
    exact h2
  · have h1 := h.int_right _ (hadm φ hφ)
    have h2 := (hmp.integrable_comp_emb hemb).mpr h1
    rw [hfun] at h2
    exact h2
  · have h1 := h.identity _ (hadm φ hφ)
    rw [hit φ hφ] at h1
    simp only [wholeSpaceOf_μ] at h1
    simp only [wholeSpace_μ, List.length_map, Function.comp_apply]
    have e1 := hmp.integral_comp hemb
      (fun z => (iterDirDeriv (vs.map toPlane.symm) φ ∘ toPlane.symm) z • f z)
    have e2 := hmp.integral_comp hemb (fun z => (φ ∘ toPlane.symm) z • g z)
    simp only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply] at e1 e2
    rw [e1, e2]
    exact h1

theorem map_cylinder_word (c : ℝ) {k : ℕ} (α : Idx 2 k) :
    ((cylinder c).word α).map toPlane.symm = (wholeSpace 2).word α := by
  rw [TestDomain.word_eq_map, TestDomain.word_eq_map, List.map_map, cylinder_dir, wholeSpace_dir]
  congr 1
  funext i
  simp [toPlane_symm_cylDir]

end Weak

/-! ### Local `L^p` bounds of periodic extensions -/

section Local

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {c : ℝ}

/-- A weighted `L^p(cell)` field is unweighted `L^p` on every `cell ∩ {|η| ≤ M}`. -/
theorem eLpNorm_cell_inter_lt_top (ρ : Weight (ℝ × ℝ)) {p : ℝ≥0∞} (hp : p ≠ ⊤)
    {f : ℝ × ℝ → F} (hf : MemLp f p (wμ (volume.restrict (cylCell c)) ρ)) (M : ℝ) :
    eLpNorm f p (volume.restrict (cylCell c ∩ {z | |z.2| ≤ M})) < ⊤ := by
  have hB := measurableSet_absSnd_le M
  have hK : IsCompact (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-M) M) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC, hle⟩ := eLpNorm_le_wμ_of_vanish' (F := F) (volume.restrict (cylCell c)) ρ hK hp
  have hvan : ∀ᵐ z ∂(volume.restrict (cylCell c)),
      z ∉ Icc (-(c / 2)) (c / 2) ×ˢ Icc (-M) M → {z : ℝ × ℝ | |z.2| ≤ M}.indicator f z = 0 := by
    filter_upwards [ae_restrict_mem (measurableSet_cylCell c)] with z hz hzK
    rw [indicator_of_notMem]
    intro hzB
    exact hzK (cylCell_subset_box c M ⟨hz, hzB⟩)
  have e1 : eLpNorm f p (volume.restrict (cylCell c ∩ {z | |z.2| ≤ M})) =
      eLpNorm ({z : ℝ × ℝ | |z.2| ≤ M}.indicator f) p (volume.restrict (cylCell c)) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hB, Measure.restrict_restrict hB, inter_comm]
  rw [e1]
  calc eLpNorm ({z : ℝ × ℝ | |z.2| ≤ M}.indicator f) p (volume.restrict (cylCell c))
      ≤ C * eLpNorm ({z : ℝ × ℝ | |z.2| ≤ M}.indicator f) p
          (wμ (volume.restrict (cylCell c)) ρ) := hle _ hvan
    _ ≤ C * eLpNorm f p (wμ (volume.restrict (cylCell c)) ρ) := by
        gcongr; exact eLpNorm_indicator_le _
    _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hC) hf.2

/-- **Local `L^p` of the periodic extension** on boxes of `ℝ × ℝ`. -/
theorem memLp_box_perExt (hc : 0 < c) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ⊤) {f : ℝ × ℝ → F}
    (hfm : StronglyMeasurable f)
    (hf : ∀ M, eLpNorm f p (volume.restrict (cylCell c ∩ {z | |z.2| ≤ M})) < ⊤) (A M : ℝ) :
    MemLp (perExt hc f) p (volume.restrict (Icc (-A) A ×ˢ Icc (-M) M)) := by
  refine ⟨(stronglyMeasurable_perExt hc hfm).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hp]
  have h1 := hf M
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hp] at h1
  calc ∫⁻ z in Icc (-A) A ×ˢ Icc (-M) M, ‖perExt hc f z‖ₑ ^ p.toReal
      ≤ ((Finset.Icc (-⌈(A + c / 2) / c⌉) ⌈(A + c / 2) / c⌉).card : ℝ≥0∞) *
          ∫⁻ z in cylCell c ∩ {z | |z.2| ≤ M}, ‖f z‖ₑ ^ p.toReal :=
        lintegral_box_perExt_le hc f _ A M
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) h1

/-- The boxes `{|y 0| ≤ A, |y 1| ≤ M}` of `Eucl 2`. -/
def boxE (A M : ℝ) : Set (Eucl 2) := toPlane ⁻¹' (Icc (-A) A ×ˢ Icc (-M) M)

theorem isCompact_boxE (A M : ℝ) : IsCompact (boxE A M) := by
  have : boxE A M = toPlane.symm '' (Icc (-A) A ×ˢ Icc (-M) M) := by
    rw [boxE, ContinuousLinearEquiv.image_symm_eq_preimage]
  rw [this]
  exact (isCompact_Icc.prod isCompact_Icc).image toPlane.symm.continuous

theorem mem_boxE {A M : ℝ} {y : Eucl 2} : y ∈ boxE A M ↔ |y 0| ≤ A ∧ |y 1| ≤ M := by
  simp only [boxE, mem_preimage, toPlane_apply, mem_prod, mem_Icc, abs_le]

theorem memLp_boxE_perExt (hc : 0 < c) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ⊤)
    {f : ℝ × ℝ → F} (hfm : StronglyMeasurable f)
    (hf : ∀ M, eLpNorm f p (volume.restrict (cylCell c ∩ {z | |z.2| ≤ M})) < ⊤) (A M : ℝ) :
    MemLp (perExt hc f ∘ toPlane) p (volume.restrict (boxE A M)) :=
  (memLp_box_perExt hc hp0 hp hfm hf A M).comp_measurePreserving
    (measurePreserving_toPlane.restrict_preimage_emb measurableEmbedding_toPlane _)

theorem boxE_mem_nhds (y : Eucl 2) : boxE (|y 0| + 1) (|y 1| + 1) ∈ 𝓝 y := by
  have hopen : IsOpen {y' : Eucl 2 | |y' 0| < |y 0| + 1 ∧ |y' 1| < |y 1| + 1} :=
    (isOpen_lt (continuous_abs.comp (EuclideanSpace.proj (0 : Fin 2)).continuous)
      continuous_const).inter
      (isOpen_lt (continuous_abs.comp (EuclideanSpace.proj (1 : Fin 2)).continuous)
        continuous_const)
  refine Filter.mem_of_superset (hopen.mem_nhds ⟨by simp, by simp⟩) fun y' hy' => ?_
  exact mem_boxE.mpr ⟨hy'.1.le, hy'.2.le⟩

theorem locallyIntegrable_perExt_comp (hc : 0 < c) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    {f : ℝ × ℝ → F} (hfm : StronglyMeasurable f)
    (hf : ∀ M, eLpNorm f p (volume.restrict (cylCell c ∩ {z | |z.2| ≤ M})) < ⊤) :
    LocallyIntegrable (perExt hc f ∘ toPlane) volume := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1).ne'
  intro y
  refine ⟨boxE (|y 0| + 1) (|y 1| + 1), boxE_mem_nhds y, ?_⟩
  have : IsFiniteMeasure (volume.restrict (boxE (|y 0| + 1) (|y 1| + 1))) :=
    isFiniteMeasure_restrict.mpr (isCompact_boxE _ _).measure_lt_top.ne
  exact (memLp_boxE_perExt hc hp0 hp hfm hf _ _).integrable hp1

end Local

end UnforcedLeray.Sob
