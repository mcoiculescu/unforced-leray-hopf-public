import UnforcedLeray.Short.PartIIIa.Defs
import UnforcedLeray.Units.B0592
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# The vorticity space `X_{m,c}` of the concrete flat setting (source 4349-4350, 2825-2829, 4562)

Source of record: `the November 2 reference manuscript` (73 pages), lines 4349-4350:
"The weighted vorticity space is the centrally even, zero-circulation subspace `X_{m,c}`, with a
fixed `m > 8`", and 2828: `X_{m,c} = L²(C_c, ⟨x⟩^{2m}dx)`.

* `XAmb c m` : the complex Hilbert space `L²(cell, ⟨x⟩^{2m}dx)` of `IIIa.xNorm`
  (`B0579.cellMeasure c m`).
* `reflX`, `circC` : the reflection `f ↦ f(-·)` and the circulation `f ↦ ∫_cell f`, continuous for
  `m > 1` (Cauchy-Schwarz, `B0592.lintegral_cell_le`).
* `xmcSub c m`, `Xmc c m` : the closed subspace of centrally even, zero-circulation fields; it is
  complete (`Fact (1 < m)`).
* `xFn x` : the planar function of `x ∈ X_{m,c}` (the embedding of `ConcreteYF.IsTrainPkg`).
* `conjX` : complex conjugation, with the laws of `ConcreteYF.YoungLaws`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-! ## The ambient space -/

/-- `L²(cell, ⟨x⟩^{2m}dx; ℂ)` (source 2828; the norm is `IIIa.xNorm c m`). -/
abbrev XAmb (c m : ℝ) := Lp ℂ 2 (B0579.cellMeasure c m)

variable {c m : ℝ}

/-! ## The reflection -/

/-- `x ↦ -x` preserves Lebesgue measure on the plane. -/
theorem mp_neg_plane : MeasurePreserving (fun x : ℝ × ℝ => -x)
    (volume : Measure (ℝ × ℝ)) volume := by
  exact (Measure.measurePreserving_neg (volume : Measure ℝ)).prod
    (Measure.measurePreserving_neg (volume : Measure ℝ))

/-- The reflected cell differs from the cell by a null set. -/
theorem neg_preimage_cell_ae (c : ℝ) :
    ((fun x : ℝ × ℝ => -x) ⁻¹' B0579.cell c : Set (ℝ × ℝ)) =ᵐ[volume] B0579.cell c := by
  have e : ((fun x : ℝ × ℝ => -x) ⁻¹' B0579.cell c : Set (ℝ × ℝ)) =
      Ioc (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ) := by
    ext x
    simp only [B0579.cell, mem_preimage, Prod.fst_neg, Prod.snd_neg, mem_prod, mem_Ico, mem_univ,
      and_true, mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩; constructor <;> linarith
    · rintro ⟨h1, h2⟩; constructor <;> linarith
  rw [e, B0579.cell, Measure.volume_eq_prod]
  exact Measure.set_prod_ae_eq Ico_ae_eq_Ioc.symm (ae_eq_refl _)

/-- `x ↦ -x` preserves `dx` on the cell. -/
theorem mp_neg_cell (c : ℝ) : MeasurePreserving (fun x : ℝ × ℝ => -x)
    (volume.restrict (B0579.cell c)) (volume.restrict (B0579.cell c)) := by
  have h := mp_neg_plane.restrict_preimage (B0579.measurableSet_cell c)
  rwa [Measure.restrict_congr_set (neg_preimage_cell_ae c)] at h

theorem jb_neg (x : ℝ × ℝ) : B0579.jb (-x) = B0579.jb x := by
  simp [B0579.jb]

theorem density_neg (x : ℝ × ℝ) : B0579.density m (-x) = B0579.density m x := by
  simp [B0579.density, jb_neg]

/-- `x ↦ -x` preserves the weighted cell measure (the weight is even). -/
theorem mp_neg_cellMeasure (c m : ℝ) : MeasurePreserving (fun x : ℝ × ℝ => -x)
    (B0579.cellMeasure c m) (B0579.cellMeasure c m) := by
  refine ⟨measurable_neg, Measure.ext fun s hs => ?_⟩
  have hd : Measurable fun x : ℝ × ℝ => (B0579.density m x : ℝ≥0∞) :=
    (B0579.measurable_density m).coe_nnreal_ennreal
  have hmc := mp_neg_cell c
  rw [Measure.map_apply measurable_neg hs, B0579.cellMeasure,
    withDensity_apply _ hs, withDensity_apply _ (measurable_neg hs)]
  have := hmc.setLIntegral_comp_preimage hs hd
  rw [← this]
  refine lintegral_congr fun x => ?_
  rw [density_neg]

/-- The reflection `f ↦ f(-·)` of `X_{m,c}`, a linear isometry. -/
def reflX (c m : ℝ) : XAmb c m →ₗᵢ[ℂ] XAmb c m :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ × ℝ => -x) (mp_neg_cellMeasure c m)

theorem coeFn_reflX (f : XAmb c m) :
    (reflX c m f : ℝ × ℝ → ℂ) =ᵐ[B0579.cellMeasure c m] fun x => f (-x) :=
  Lp.coeFn_compMeasurePreserving f (mp_neg_cellMeasure c m)

/-! ## The circulation -/

theorem ae_cell_of_ae_cellMeasure {P : ℝ × ℝ → Prop}
    (h : ∀ᵐ x ∂(B0579.cellMeasure c m), P x) : ∀ᵐ x ∂(volume.restrict (B0579.cell c)), P x :=
  (B0579.ac_cellMeasure c m).ae_le h

theorem ae_cellMeasure_of_ae_cell {P : ℝ × ℝ → Prop}
    (h : ∀ᵐ x ∂(volume.restrict (B0579.cell c)), P x) : ∀ᵐ x ∂(B0579.cellMeasure c m), P x :=
  (B0579.cellMeasure_ac c m).ae_le h

theorem lintegral_cell_enorm_le (f : XAmb c m) :
    ∫⁻ y in B0579.cell c, ‖f y‖ₑ ≤ B0592.weightConst m * ENNReal.ofReal ‖f‖ := by
  set ω : B0579.X c m := (Lp.memLp f).norm.toLp _ with hω
  have hae : (ω : ℝ × ℝ → ℝ) =ᵐ[B0579.cellMeasure c m] fun y => ‖f y‖ :=
    (Lp.memLp f).norm.coeFn_toLp
  have hae' : (ω : ℝ × ℝ → ℝ) =ᵐ[volume.restrict (B0579.cell c)] fun y => ‖f y‖ :=
    ae_cell_of_ae_cellMeasure hae
  have hn : ‖ω‖ = ‖f‖ := by
    rw [Lp.norm_toLp, Lp.norm_def]
    congr 1
    exact eLpNorm_norm _
  have h := B0592.lintegral_cell_le c ω
  rw [hn] at h
  refine le_trans (le_of_eq (lintegral_congr_ae ?_)) h
  filter_upwards [hae'] with y hy
  rw [hy]
  simp

theorem integrableOn_xamb (hm : 1 < m) (f : XAmb c m) : IntegrableOn f (B0579.cell c) := by
  have hmeas : AEStronglyMeasurable f (volume.restrict (B0579.cell c)) :=
    (Lp.aestronglyMeasurable f).mono_ac (B0579.ac_cellMeasure c m)
  refine ⟨hmeas, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  exact (lintegral_cell_enorm_le f).trans_lt
    (ENNReal.mul_lt_top (B0592.weightConst_lt_top hm) ENNReal.ofReal_lt_top)

/-- The circulation `f ↦ ∫_cell f` of `X_{m,c}`, `m > 1` (a linear form). -/
def circL (hm : 1 < m) : XAmb c m →ₗ[ℂ] ℂ where
  toFun f := ∫ x in B0579.cell c, f x
  map_add' f g := by
    rw [← integral_add (integrableOn_xamb hm f) (integrableOn_xamb hm g)]
    refine integral_congr_ae ?_
    filter_upwards [ae_cell_of_ae_cellMeasure (Lp.coeFn_add f g)] with x hx
    simpa using hx
  map_smul' a f := by
    rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [ae_cell_of_ae_cellMeasure (Lp.coeFn_smul a f)] with x hx
    simpa using hx

theorem norm_circL_le (hm : 1 < m) (f : XAmb c m) :
    ‖circL hm f‖ ≤ (B0592.weightConst m).toReal * ‖f‖ := by
  have h1 : ‖∫ x in B0579.cell c, f x‖ₑ ≤ ∫⁻ y in B0579.cell c, ‖f y‖ₑ :=
    enorm_integral_le_lintegral_enorm _
  have h2 := h1.trans (lintegral_cell_enorm_le f)
  have hne : B0592.weightConst m ≠ ⊤ := (B0592.weightConst_lt_top hm).ne
  have h3 : ENNReal.ofReal ‖∫ x in B0579.cell c, f x‖ ≤
      ENNReal.ofReal ((B0592.weightConst m).toReal * ‖f‖) := by
    rw [ofReal_norm, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hne]
    exact h2
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3

/-- The circulation as a continuous linear form. -/
def circC (hm : 1 < m) : XAmb c m →L[ℂ] ℂ :=
  (circL hm).mkContinuous _ (norm_circL_le hm)

theorem circC_apply (hm : 1 < m) (f : XAmb c m) :
    circC hm f = ∫ x in B0579.cell c, f x := rfl

/-! ## The space `X_{m,c}` -/

/-- **The centrally even, zero-circulation subspace** of `L²(cell, ⟨x⟩^{2m}dx)`
(source 4349-4350, 4562). -/
def xmcSub (c m : ℝ) [hm : Fact (1 < m)] : Submodule ℂ (XAmb c m) :=
  LinearMap.ker (circC (c := c) hm.out).toLinearMap ⊓
    LinearMap.ker ((reflX c m).toContinuousLinearMap.toLinearMap - LinearMap.id)

/-- `X_{m,c}` (source 4349-4350). -/
abbrev Xmc (c m : ℝ) [Fact (1 < m)] := ↥(xmcSub c m)

variable [hm : Fact (1 < m)]

theorem mem_xmcSub {f : XAmb c m} :
    f ∈ xmcSub c m ↔ (∫ x in B0579.cell c, f x) = 0 ∧ reflX c m f = f := by
  simp only [xmcSub, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero]
  rfl

theorem isClosed_xmcSub : IsClosed ((xmcSub c m : Submodule ℂ (XAmb c m)) : Set (XAmb c m)) := by
  have h1 : IsClosed {f : XAmb c m | circC (c := c) hm.out f = 0} :=
    isClosed_eq (circC hm.out).continuous continuous_const
  have h2 : IsClosed {f : XAmb c m | reflX c m f = f} :=
    isClosed_eq (reflX c m).continuous continuous_id
  have e : ((xmcSub c m : Submodule ℂ (XAmb c m)) : Set (XAmb c m)) =
      {f | circC (c := c) hm.out f = 0} ∩ {f | reflX c m f = f} := by
    ext f
    simp only [SetLike.mem_coe, mem_xmcSub, mem_inter_iff, mem_ofPred_eq, circC_apply]
  rw [e]
  exact h1.inter h2

instance : CompleteSpace (Xmc c m) := isClosed_xmcSub.completeSpace_coe

/-- The planar function of `x ∈ X_{m,c}` (the embedding `emb` of `ConcreteYF.IsTrainPkg`). -/
def xFn (x : Xmc c m) : ℝ × ℝ → ℂ := ((x : XAmb c m) : ℝ × ℝ → ℂ)

theorem xFn_add (x y : Xmc c m) :
    xFn (x + y) =ᵐ[volume.restrict (B0579.cell c)] fun p => xFn x p + xFn y p :=
  ae_cell_of_ae_cellMeasure (Lp.coeFn_add (x : XAmb c m) y)

theorem xFn_smul (a : ℂ) (x : Xmc c m) :
    xFn (a • x) =ᵐ[volume.restrict (B0579.cell c)] fun p => a * xFn x p :=
  ae_cell_of_ae_cellMeasure (Lp.coeFn_smul a (x : XAmb c m))

theorem xFn_sub (x y : Xmc c m) :
    xFn (x - y) =ᵐ[volume.restrict (B0579.cell c)] fun p => xFn x p - xFn y p :=
  ae_cell_of_ae_cellMeasure (Lp.coeFn_sub (x : XAmb c m) y)

theorem xFn_rsmul (r : ℝ) (x : Xmc c m) :
    xFn (r • x) =ᵐ[volume.restrict (B0579.cell c)] fun p => (r : ℂ) * xFn x p := by
  have h : ∀ᵐ p ∂(volume.restrict (B0579.cell c)),
      ((r • (x : XAmb c m) : XAmb c m) : ℝ × ℝ → ℂ) p = r • (x : XAmb c m) p :=
    ae_cell_of_ae_cellMeasure (Lp.coeFn_smul r (x : XAmb c m))
  filter_upwards [h] with p hp
  have e : xFn (r • x) p = ((r • (x : XAmb c m) : XAmb c m) : ℝ × ℝ → ℂ) p := rfl
  rw [e, hp, Complex.real_smul]
  rfl

theorem xFn_memLp (x : Xmc c m) : MemLp (xFn x) 2 (B0579.cellMeasure c m) := Lp.memLp _

theorem xFn_integrableOn (x : Xmc c m) : IntegrableOn (xFn x) (B0579.cell c) :=
  integrableOn_xamb hm.out _

theorem xFn_circ (x : Xmc c m) : ∫ p in B0579.cell c, xFn x p = 0 :=
  (mem_xmcSub.1 x.2).1

theorem xFn_zeroCirc (x : Xmc c m) : IIIa.HasZeroCirculation c (xFn x) :=
  ⟨xFn_integrableOn x, xFn_circ x⟩

theorem xFn_even (x : Xmc c m) :
    ∀ᵐ p ∂(volume.restrict (B0579.cell c)), xFn x (-p) = xFn x p := by
  have h := coeFn_reflX (x : XAmb c m)
  rw [(mem_xmcSub.1 x.2).2] at h
  filter_upwards [ae_cell_of_ae_cellMeasure h] with p hp
  exact hp.symm

/-- Elements of `X_{m,c}` are determined by their planar functions on the cell. -/
theorem xmc_ext {x y : Xmc c m} (h : xFn x =ᵐ[volume.restrict (B0579.cell c)] xFn y) : x = y :=
  Subtype.ext (Lp.ext (ae_cellMeasure_of_ae_cell h))

/-! ## Complex conjugation -/

/-- Pointwise conjugation on the ambient space. -/
def conjAmb (f : XAmb c m) : XAmb c m :=
  (Complex.conjCLE : ℂ →L[ℝ] ℂ).compLp f

theorem coeFn_conjAmb (f : XAmb c m) :
    (conjAmb f : ℝ × ℝ → ℂ) =ᵐ[B0579.cellMeasure c m] fun x => conj (f x) := by
  filter_upwards [ContinuousLinearMap.coeFn_compLp (Complex.conjCLE : ℂ →L[ℝ] ℂ) f] with x hx
  rw [conjAmb, hx]
  rfl

theorem conjAmb_mem {f : XAmb c m} (hf : f ∈ xmcSub c m) : conjAmb f ∈ xmcSub c m := by
  obtain ⟨h1, h2⟩ := mem_xmcSub.1 hf
  refine mem_xmcSub.2 ⟨?_, ?_⟩
  · have : ∫ x in B0579.cell c, (conjAmb f : ℝ × ℝ → ℂ) x =
        ∫ x in B0579.cell c, conj (f x) :=
      integral_congr_ae (ae_cell_of_ae_cellMeasure (coeFn_conjAmb f))
    rw [this, integral_conj, h1, map_zero]
  · refine Lp.ext ?_
    have e1 := coeFn_reflX (conjAmb f)
    have e2 := coeFn_reflX f
    rw [h2] at e2
    have e3 := (mp_neg_cellMeasure c m).quasiMeasurePreserving.ae (coeFn_conjAmb f)
    filter_upwards [e1, e2, e3, coeFn_conjAmb f] with x hx1 hx2 hx3 hx4
    rw [hx1, hx3, hx4, hx2]

/-- **Complex conjugation of `X_{m,c}`** (the `conjX` of `ConcreteYF.FlatSetting`, source 4345,
4606). -/
def conjX (x : Xmc c m) : Xmc c m := ⟨conjAmb x.1, conjAmb_mem x.2⟩

theorem xFn_conjX (x : Xmc c m) :
    xFn (conjX x) =ᵐ[volume.restrict (B0579.cell c)] fun p => conj (xFn x p) :=
  ae_cell_of_ae_cellMeasure (coeFn_conjAmb x.1)

theorem conjX_add (x y : Xmc c m) : conjX (x + y) = conjX x + conjX y := by
  refine xmc_ext ?_
  filter_upwards [xFn_conjX (x + y), xFn_add x y, xFn_add (conjX x) (conjX y), xFn_conjX x,
    xFn_conjX y] with p h1 h2 h3 h4 h5
  rw [h1, h2, h3, h4, h5, map_add]

theorem conjX_smul (a : ℂ) (x : Xmc c m) : conjX (a • x) = (starRingEnd ℂ a) • conjX x := by
  refine xmc_ext ?_
  filter_upwards [xFn_conjX (a • x), xFn_smul a x, xFn_smul (starRingEnd ℂ a) (conjX x),
    xFn_conjX x] with p h1 h2 h3 h4
  rw [h1, h2, h3, h4, map_mul]

theorem conjX_conjX (x : Xmc c m) : conjX (conjX x) = x := by
  refine xmc_ext ?_
  filter_upwards [xFn_conjX (conjX x), xFn_conjX x] with p h1 h2
  rw [h1, h2, Complex.conj_conj]

theorem norm_conjX (x : Xmc c m) : ‖conjX x‖ = ‖x‖ := by
  change ‖conjAmb x.1‖ = ‖x.1‖
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  refine (eLpNorm_congr_ae (coeFn_conjAmb x.1)).trans ?_
  exact eLpNorm_congr_norm_ae (Eventually.of_forall fun p => Complex.norm_conj _)

theorem conjX_sub (x y : Xmc c m) : conjX (x - y) = conjX x - conjX y := by
  refine xmc_ext ?_
  filter_upwards [xFn_conjX (x - y), xFn_sub x y, xFn_sub (conjX x) (conjX y), xFn_conjX x,
    xFn_conjX y] with p h1 h2 h3 h4 h5
  rw [h1, h2, h3, h4, h5, map_sub]

/-- Conjugation is an isometry of `X_{m,c}`, in particular continuous. -/
theorem continuous_conjX : Continuous (conjX : Xmc c m → Xmc c m) := by
  refine Metric.continuous_iff.2 fun x ε hε => ⟨ε, hε, fun y hy => ?_⟩
  rw [dist_eq_norm] at hy ⊢
  rwa [← conjX_sub, norm_conjX]

/-- Conjugation as a continuous real-linear equivalence (it passes through Bochner integrals). -/
def conjXL : Xmc c m ≃L[ℝ] Xmc c m where
  toFun := conjX
  invFun := conjX
  map_add' := conjX_add
  map_smul' r x := by
    refine xmc_ext ?_
    filter_upwards [xFn_conjX (r • x), xFn_rsmul r x, xFn_rsmul r (conjX x), xFn_conjX x]
      with p h1 h2 h3 h4
    rw [h1, h2, RingHom.id_apply, h3, h4, map_mul, Complex.conj_ofReal]
  left_inv := conjX_conjX
  right_inv := conjX_conjX
  continuous_toFun := continuous_conjX
  continuous_invFun := continuous_conjX

@[simp] theorem conjXL_apply (x : Xmc c m) : conjXL x = conjX x := rfl

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
