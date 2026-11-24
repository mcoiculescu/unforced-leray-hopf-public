import UnforcedLeray.Analysis.GaussianVortex.PlanarDefs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Periodic cylinder carrier, centred cell and cell measures (INF13, target CY01)


§4 BP1 and §5 CY01; decision D1 of `scoping/README.md` §3.

A field on the cylinder `C_c = (ℝ / cℤ) × ℝ` (`paper/main.tex` lines 4171-4184, unit B0242;
lines 4569-4578, unit B0271; lines 13840-13866, unit B0655) is a `c`-periodic function on
`Plane = ℝ × ℝ` (`IsPeriodic`).  Norms are integrals over the centred cell
`cell c = [-c/2, c/2) × ℝ` with Lebesgue measure (`cellμ c`, the measure `dq dη` of the
manuscript).  The normalized measure `dq/c dη` of the age-weighted spaces (B0285, tex
4653-4677) is `avgμ c`.

Main declarations: `IsPeriodic`, `cell`, `cellμ`, `avgμ`, `partialQ`, `partialEta`, `curl`,
`divergence`, `isAddFundamentalDomain_strip`, `lintegral_strip_eq_cell`,
`integral_strip_eq_cell`, `lintegral_cell_comp_add`, `integral_cell_comp_add`,
`integral_cell_eq_integral_integral`, `avgμ_univ_prod`, `integral_avgμ`.

Vector fields take values in `Vec2 = EuclideanSpace ℝ (Fin 2)` (D1): `ℝ × ℝ` carries the sup
norm.  Partial derivatives are the classical one-variable derivatives in each coordinate, as
in `GaussianVortex.PlanarDefs`; `partialQ f = GaussianVortex.partialX f` for real `f`
(`partialQ_eq_partialX`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Function
open scoped ENNReal

namespace UnforcedLeray.Cyl

/-- The plane `ℝ × ℝ` with coordinates `(q, η)`. -/
abbrev Plane := ℝ × ℝ

/-- Meridional vectors: the Euclidean plane (not the sup-normed product). -/
abbrev Vec2 := EuclideanSpace ℝ (Fin 2)

variable {E : Type*}

/-- A function on the plane is `c`-periodic in the first coordinate `q` (decision D1). -/
def IsPeriodic (c : ℝ) (f : Plane → E) : Prop := ∀ z : Plane, f (z.1 + c, z.2) = f z

/-- The centred cell `[-c/2, c/2) × ℝ` (decision D1, tex 4171-4184). -/
def cell (c : ℝ) : Set Plane := Ico (-c / 2) (c / 2) ×ˢ univ

/-- Lebesgue measure `dq dη` on the centred cell. -/
def cellμ (c : ℝ) : Measure Plane := volume.restrict (cell c)

/-- The normalized cell measure `dq/c dη` (tex 4653-4677, B0285). -/
def avgμ (c : ℝ) : Measure Plane := ENNReal.ofReal c⁻¹ • cellμ c

section Derivatives

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The classical partial derivative in `q`. -/
def partialQ (f : Plane → E) (z : Plane) : E := deriv (fun q : ℝ => f (q, z.2)) z.1

/-- The classical partial derivative in `η`. -/
def partialEta (f : Plane → E) (z : Plane) : E := deriv (fun η : ℝ => f (z.1, η)) z.2

/-- The scalar curl `∂_q u₂ - ∂_η u₁` of a meridional field. -/
def curl (u : Plane → Vec2) (z : Plane) : ℝ :=
  partialQ (fun w => u w 1) z - partialEta (fun w => u w 0) z

/-- The divergence `∂_q u₁ + ∂_η u₂` of a meridional field. -/
def divergence (u : Plane → Vec2) (z : Plane) : ℝ :=
  partialQ (fun w => u w 0) z + partialEta (fun w => u w 1) z

theorem partialQ_eq_partialX (f : Plane → ℝ) :
    partialQ f = GaussianVortex.partialX f := rfl

theorem partialEta_eq_partialY (f : Plane → ℝ) :
    partialEta f = GaussianVortex.partialY f := rfl

end Derivatives

/-! ### Periodicity -/

section Periodic

variable {c : ℝ} {f : Plane → E}

theorem IsPeriodic.slice (hf : IsPeriodic c f) (η : ℝ) :
    Function.Periodic (fun q : ℝ => f (q, η)) c := fun q => hf (q, η)

theorem IsPeriodic.add_zsmul (hf : IsPeriodic c f) (n : ℤ) (z : Plane) :
    f (z.1 + n • c, z.2) = f z :=
  (hf.slice z.2).zsmul n z.1

theorem IsPeriodic.sub_eq (hf : IsPeriodic c f) (z : Plane) : f (z.1 - c, z.2) = f z := by
  have := hf (z.1 - c, z.2)
  simp only [sub_add_cancel] at this
  exact this.symm

theorem IsPeriodic.comp {F : Type*} (hf : IsPeriodic c f) (g : E → F) :
    IsPeriodic c (g ∘ f) := fun z => by simp [hf z]

theorem IsPeriodic.fun_comp {F : Type*} (hf : IsPeriodic c f) (g : E → F) :
    IsPeriodic c (fun z => g (f z)) := hf.comp g

theorem IsPeriodic.prodMk {F : Type*} {g : Plane → F} (hf : IsPeriodic c f)
    (hg : IsPeriodic c g) : IsPeriodic c (fun z => (f z, g z)) := fun z => by
  simp [hf z, hg z]

theorem IsPeriodic.neg_half (hf : IsPeriodic c f) (η : ℝ) :
    f (-c / 2, η) = f (c / 2, η) := by
  have := hf (-c / 2, η)
  simp only at this
  rw [← this]
  congr 2
  ring

theorem isPeriodic_const (a : E) : IsPeriodic c (fun _ : Plane => a) := fun _ => rfl

/-- Periodicity of the classical `q`-derivative. -/
theorem IsPeriodic.partialQ [NormedAddCommGroup E] [NormedSpace ℝ E] (hf : IsPeriodic c f) :
    IsPeriodic c (partialQ f) := by
  intro z
  simp only [Cyl.partialQ]
  have hfun : (fun q : ℝ => f (q, z.2)) = fun q => f (q + c, z.2) := by
    funext q; exact (hf (q, z.2)).symm
  conv_rhs => rw [hfun]
  exact (deriv_comp_add_const (f := fun q : ℝ => f (q, z.2)) (a := c) (x := z.1)).symm

/-- Periodicity of the classical `η`-derivative. -/
theorem IsPeriodic.partialEta [NormedAddCommGroup E] [NormedSpace ℝ E] (hf : IsPeriodic c f) :
    IsPeriodic c (partialEta f) := by
  intro z
  simp only [Cyl.partialEta]
  have : (fun η : ℝ => f (z.1 + c, η)) = fun η => f (z.1, η) := by
    funext η; exact hf (z.1, η)
  rw [this]

end Periodic

/-! ### The cell as a fundamental domain -/

section FundamentalDomain

/-- Lebesgue measure on `Plane` is an additive Haar measure (the defeq
`volume = volume.prod volume` is not seen by instance search). -/
instance isAddHaarMeasure_volume_plane : Measure.IsAddHaarMeasure (volume : Measure Plane) :=
  Measure.prod.instIsAddHaarMeasure _ _

theorem measurableSet_cell (c : ℝ) : MeasurableSet (cell c) :=
  measurableSet_Ico.prod MeasurableSet.univ

theorem mem_cell {c : ℝ} {z : Plane} : z ∈ cell c ↔ -c / 2 ≤ z.1 ∧ z.1 < c / 2 := by
  simp [cell]

theorem cell_eq_strip (c : ℝ) : cell c = Ico (-c / 2) (-c / 2 + c) ×ˢ univ := by
  rw [cell]; congr 2; ring

instance vaddInvariant_zmultiples (v : Plane) :
    VAddInvariantMeasure (AddSubgroup.zmultiples v) Plane volume :=
  ⟨fun g s _ => by
    simp only [AddSubgroup.vadd_def, vadd_eq_add]
    exact measure_preimage_add _ _ _⟩

/-- Every strip `[a, a + c) × ℝ` is a fundamental domain for `q ↦ q + cℤ`. -/
theorem isAddFundamentalDomain_strip {c : ℝ} (hc : 0 < c) (a : ℝ) :
    IsAddFundamentalDomain (AddSubgroup.zmultiples ((c, 0) : Plane))
      (Ico a (a + c) ×ˢ (univ : Set ℝ)) volume := by
  refine IsAddFundamentalDomain.mk'
    (measurableSet_Ico.prod (MeasurableSet.univ (α := ℝ))).nullMeasurableSet fun x => ?_
  have hinj : Function.Injective (fun n : ℤ => n • ((c, 0) : Plane)) := by
    intro m n h
    have h1 := congrArg Prod.fst h
    simp only [Prod.smul_fst] at h1
    rw [zsmul_eq_mul, zsmul_eq_mul] at h1
    exact_mod_cast mul_right_cancel₀ hc.ne' h1
  have hbij : Function.Bijective (codRestrict (fun n : ℤ => n • ((c, 0) : Plane))
      (AddSubgroup.zmultiples ((c, 0) : Plane)) fun n => ⟨n, rfl⟩) :=
    (Equiv.ofInjective _ hinj).bijective
  refine hbij.existsUnique_iff.2 ?_
  obtain ⟨n, hn, huniq⟩ := existsUnique_add_zsmul_mem_Ico hc x.1 a
  refine ⟨n, ?_, ?_⟩
  · simp only [AddSubgroup.vadd_def, codRestrict, vadd_eq_add, mem_prod, mem_univ, and_true,
      Prod.fst_add, Prod.smul_fst]
    simpa [add_comm] using hn
  · intro m hm
    apply huniq
    simp only [AddSubgroup.vadd_def, codRestrict, vadd_eq_add, mem_prod, mem_univ, and_true,
      Prod.fst_add, Prod.smul_fst] at hm
    simpa [add_comm] using hm

theorem isAddFundamentalDomain_cell {c : ℝ} (hc : 0 < c) :
    IsAddFundamentalDomain (AddSubgroup.zmultiples ((c, 0) : Plane)) (cell c) volume := by
  rw [cell_eq_strip]; exact isAddFundamentalDomain_strip hc _

theorem IsPeriodic.vadd_zmultiples {c : ℝ} {f : Plane → E} (hf : IsPeriodic c f)
    (g : AddSubgroup.zmultiples ((c, 0) : Plane)) (x : Plane) : f (g +ᵥ x) = f x := by
  obtain ⟨g, n, rfl⟩ := g
  simp only [AddSubgroup.vadd_def, vadd_eq_add]
  have := hf.add_zsmul n x
  convert this using 2
  ext <;> simp [add_comm]

/-- For a periodic function the lower integral over any period strip equals the cell
integral. -/
theorem lintegral_strip_eq_cell {c : ℝ} (hc : 0 < c) {f : Plane → ℝ≥0∞}
    (hf : IsPeriodic c f) (a : ℝ) :
    ∫⁻ z in Ico a (a + c) ×ˢ (univ : Set ℝ), f z = ∫⁻ z in cell c, f z :=
  (isAddFundamentalDomain_strip hc a).setLIntegral_eq (isAddFundamentalDomain_cell hc) f
    hf.vadd_zmultiples

theorem integral_strip_eq_cell [NormedAddCommGroup E] [NormedSpace ℝ E] {c : ℝ} (hc : 0 < c)
    {f : Plane → E} (hf : IsPeriodic c f) (a : ℝ) :
    ∫ z in Ico a (a + c) ×ˢ (univ : Set ℝ), f z = ∫ z in cell c, f z :=
  (isAddFundamentalDomain_strip hc a).setIntegral_eq (isAddFundamentalDomain_cell hc)
    hf.vadd_zmultiples

theorem preimage_add_strip (c a : ℝ) (v : Plane) :
    (· + v) ⁻¹' (Ico (a + v.1) (a + v.1 + c) ×ˢ (univ : Set ℝ)) =
      Ico a (a + c) ×ˢ (univ : Set ℝ) := by
  ext z
  simp only [mem_preimage, mem_prod, mem_Ico, Prod.fst_add, mem_univ, and_true]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- Translation invariance of cell integrals of periodic functions (CY01). -/
theorem lintegral_cell_comp_add {c : ℝ} (hc : 0 < c) {f : Plane → ℝ≥0∞}
    (hper : IsPeriodic c f) (v : Plane) :
    ∫⁻ z in cell c, f (z + v) = ∫⁻ z in cell c, f z := by
  have hmp : MeasurePreserving (· + v) (volume : Measure Plane) volume :=
    measurePreserving_add_right volume v
  have hemb : MeasurableEmbedding (· + v : Plane → Plane) :=
    (Homeomorph.addRight v).measurableEmbedding
  calc ∫⁻ z in cell c, f (z + v)
      = ∫⁻ z in (· + v) ⁻¹' (Ico (-c / 2 + v.1) (-c / 2 + v.1 + c) ×ˢ univ), f (z + v) := by
        rw [preimage_add_strip, cell_eq_strip]
    _ = ∫⁻ z in Ico (-c / 2 + v.1) (-c / 2 + v.1 + c) ×ˢ univ, f z :=
        hmp.setLIntegral_comp_preimage_emb hemb _ _
    _ = ∫⁻ z in cell c, f z := lintegral_strip_eq_cell hc hper _

/-- Translation invariance of cell integrals of periodic functions, Bochner version (CY01). -/
theorem integral_cell_comp_add [NormedAddCommGroup E] [NormedSpace ℝ E] {c : ℝ} (hc : 0 < c)
    {f : Plane → E} (hper : IsPeriodic c f) (v : Plane) :
    ∫ z in cell c, f (z + v) = ∫ z in cell c, f z := by
  have hmp : MeasurePreserving (· + v) (volume : Measure Plane) volume :=
    measurePreserving_add_right volume v
  have hemb : MeasurableEmbedding (· + v : Plane → Plane) :=
    (Homeomorph.addRight v).measurableEmbedding
  calc ∫ z in cell c, f (z + v)
      = ∫ z in (· + v) ⁻¹' (Ico (-c / 2 + v.1) (-c / 2 + v.1 + c) ×ˢ univ), f (z + v) := by
        rw [preimage_add_strip, cell_eq_strip]
    _ = ∫ z in Ico (-c / 2 + v.1) (-c / 2 + v.1 + c) ×ˢ univ, f z :=
        hmp.setIntegral_preimage_emb hemb _ _
    _ = ∫ z in cell c, f z := integral_strip_eq_cell hc hper _

end FundamentalDomain

/-! ### Fubini on the cell and the normalized measure -/

section Fubini

theorem cellμ_eq_prod (c : ℝ) :
    cellμ c = (volume.restrict (Ico (-c / 2) (c / 2))).prod (volume : Measure ℝ) := by
  rw [cellμ, cell, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

theorem volume_restrict_cell (c : ℝ) :
    (volume : Measure Plane).restrict (cell c) =
      (volume.restrict (Ico (-c / 2) (c / 2))).prod (volume : Measure ℝ) :=
  cellμ_eq_prod c

/-- Fubini on the cell, with the `η`-integral outside. -/
theorem integral_cell_eq_integral_integral [NormedAddCommGroup E] [NormedSpace ℝ E] {c : ℝ}
    {f : Plane → E} (hf : IntegrableOn f (cell c)) :
    ∫ z in cell c, f z = ∫ η, ∫ q in Ico (-c / 2) (c / 2), f (q, η) := by
  rw [volume_restrict_cell]
  rw [IntegrableOn, volume_restrict_cell] at hf
  exact integral_prod_symm f hf

/-- Fubini on the cell, with the `q`-integral outside. -/
theorem integral_cell_eq_integral_integral' [NormedAddCommGroup E] [NormedSpace ℝ E] {c : ℝ}
    {f : Plane → E} (hf : IntegrableOn f (cell c)) :
    ∫ z in cell c, f z = ∫ q in Ico (-c / 2) (c / 2), ∫ η, f (q, η) := by
  rw [volume_restrict_cell]
  rw [IntegrableOn, volume_restrict_cell] at hf
  exact integral_prod f hf

/-- Tonelli on the cell. -/
theorem lintegral_cell_eq {c : ℝ} {f : Plane → ℝ≥0∞} (hf : AEMeasurable f (cellμ c)) :
    ∫⁻ z in cell c, f z = ∫⁻ q in Ico (-c / 2) (c / 2), ∫⁻ η, f (q, η) := by
  rw [volume_restrict_cell]
  rw [cellμ_eq_prod] at hf
  exact lintegral_prod f hf

theorem cellμ_prod (c : ℝ) (B : Set ℝ) :
    cellμ c (univ ×ˢ B) = ENNReal.ofReal c * volume B := by
  rw [cellμ_eq_prod, Measure.prod_prod, Measure.restrict_apply_univ, Real.volume_Ico]
  congr 2; ring

/-- The normalized cell measure gives the strip `cell c ∩ (ℝ × B)` the mass `|B|`. -/
theorem avgμ_univ_prod {c : ℝ} (hc : 0 < c) (B : Set ℝ) :
    avgμ c (univ ×ˢ B) = volume B := by
  rw [avgμ, Measure.smul_apply, cellμ_prod, smul_eq_mul, ← mul_assoc,
    ← ENNReal.ofReal_mul (inv_nonneg.2 hc.le), inv_mul_cancel₀ hc.ne', ENNReal.ofReal_one,
    one_mul]

theorem integral_avgμ [NormedAddCommGroup E] [NormedSpace ℝ E] {c : ℝ} (hc : 0 ≤ c)
    (f : Plane → E) : ∫ z, f z ∂avgμ c = c⁻¹ • ∫ z in cell c, f z := by
  rw [avgμ, integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.2 hc)]
  rfl

theorem lintegral_avgμ {c : ℝ} (f : Plane → ℝ≥0∞) :
    ∫⁻ z, f z ∂avgμ c = ENNReal.ofReal c⁻¹ * ∫⁻ z in cell c, f z := by
  rw [avgμ, lintegral_smul_measure]
  rfl

instance isFiniteMeasure_cellμ_restrict (c : ℝ) (B : Set ℝ) [hB : Fact (volume B < ⊤)] :
    IsFiniteMeasure ((cellμ c).restrict (univ ×ˢ B)) := by
  constructor
  rw [Measure.restrict_apply_univ, cellμ_eq_prod, Measure.prod_prod, Measure.restrict_apply_univ,
    Real.volume_Ico]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hB.out

end Fubini

end UnforcedLeray.Cyl
