import UnforcedLeray.Short.PartIIb.StatementsMixed
import UnforcedLeray.Short.PartIIIa.Defs
import UnforcedLeray.Units.B0009
import UnforcedLeray.Units.B0061
import UnforcedLeray.Lib.CylinderB.BiotSavart
import Mathlib.NumberTheory.ZetaValues

/-!
# Part II-b, task `PartII-b:F1`: cylinder vs planar interaction comparison and collective compactness

Source of record: `the November 2 reference manuscript` (SP), lines 2117–2144,
display `short-bg:interaction-cylinder` at lines 2129–2131:

  "On the centered strip `|q| ≤ c/2`, let `J_c : X_{m,c} → X_m := L²(ℝ², ⟨x⟩^{2m} dx)` be zero
  extension and `R_c : X_m → X_{m,c}` restriction. At `s = σ/ν` with `0 ≤ σ ≤ Σ`, write
  `a = 1 + σ`, `E_{1+σ}(x) = (1 + σ)^{-2} E₀(x/√(1+σ))`, and
  `A_{pl,σ} f := -(K_{ℝ²} f)·∇E_{1+σ}`.
  Splitting `K_c` and `K_{ℝ²}` into `|x - y| ≤ 1` and `|x - y| > 1`, the cylinder kernel is
  bounded away from `1/|x - y|`, while for `|x|, |y| ≤ c/4` the paired periodic images `±ℓ c e_q`
  cancel to first order and give `|K_c(x - y) - K_{ℝ²}(x - y)| ≤ C c^{-2}(1 + |x| + |y|)`.
  Because `∇E_{1+σ}` is Gaussian on `|x| ≤ c/4` and `≲ e^{-b_Σ c²}` for `|x| > c/4`, weighted
  Cauchy–Schwarz with `m > 8` (and `∫_{|y|>c/4} |f(y)| dy ≲ c^{1-m} ‖f‖_{X_m}`) yields
  `‖J_c A_c(σ/ν) R_c - A_{pl,σ}‖_{X_m → X_m} ≤ C_Σ (c^{-2} + δ_c)`, `0 ≤ σ ≤ Σ`.
  For compactness, split `K_c = K_c^{near} + K_c^{far}` at `|x - y| = 1`. Multiplication by the
  rapidly decaying coefficient `∇E_c(s)` makes the far piece Hilbert–Schmidt on `X_{m,c}`, while
  the near piece gains one derivative by the Fourier multiplier bound for `DK_c` and is compact
  after multiplication by `∇E_c(s)` by Rellich on bounded cylinder disks and tail truncation. The
  same holds for `A_{pl,σ}`, and `σ ↦ A_{pl,σ}` is norm continuous on `[0, Σ]`. Therefore every
  `A_c(s)` and `A_{pl,σ}` is compact and the family `{A_{pl,σ} : 0 ≤ σ ≤ Σ}` is collectively
  compact."

## Statements and concrete definitions

* `planeMeasure`, `Xm`, `Xmc`, `zeroExtIso`, `Jc`, `Rc`: the ambient space
  `X_m = L²(ℝ², ⟨x⟩^{2m} dx)` and cylinder space `X_{m,c} = B0579.X c m = L²(C_c, ⟨x⟩^{2m} dx)`,
  the isometric zero extension `J_c : X_{m,c} → X_m` and the restriction `R_c : X_m → X_{m,c}`;
* `ofPlane`, `scalePlane`, `planarE`, `planarGradE`, `planarGradEVec`: the rescaled planar Gaussian
  vorticity `E_{1+σ}(x) = (1+σ)^{-2} E₀(x/√(1+σ))` and gradient
  `∇E_{1+σ}(x) = (1+σ)^{-5/2} ∇E₀(x/√(1+σ))` built from Part I's `B0009.E0` and `B0009.gradE0`;
* `planarBSKernel`, `planarK`, `Apl`, `IsPlanarInteractionOp`: the real planar Biot–Savart kernel
  and velocity from `B0009.kernel` / `B0009.biotSavart`, and the planar interaction
  `A_{pl,σ} f = -(K_{ℝ²} f)·∇E_{1+σ}` as a bounded operator on `Xm m`;
* `cylAc`, `IsCylInteractionOp`, `AcGauss`, `IsGaussCylInteractionOp`,
  `IsBiotSavartCylInteractionOp`, `TrainCloseM`: the cylinder interaction
  `A_c(s) w = -(K_c w)·∇E_c(s)` on `X_{m,c} = B0579.X c m`, the intermediate Gaussian-coefficient
  cylinder interaction `-(K_c w)·∇E_{1+σ}`, the bridge to `IIIa.IsBiotSavart`
  (`Short/PartIII-a/Defs.lean`), and the `m`-weighted train comparison budget `TrainCloseM`
  (SP 2085–2090);
* `InteractionCylinderComparison`: the target statement `short-bg:interaction-cylinder`
  (SP 2129–2131);
* `InteractionCollectiveCompact`: the target compactness and collective compactness statement
  (SP 2133–2140).

## Proved here (zero `sorry`)

* `cellMeasure_eq_restrict_planeMeasure`, `zeroExtIso`, `Jc`, `Rc`, `Rc_Jc`, `norm_Rc_le`,
  `norm_Jc_comp_Rc_le`, `isCompactOperator_Jc_comp_Rc`: measure compatibility, zero extension
  isometry, restriction contraction, `R_c J_c = I`, operator-norm bound `‖J_c A R_c‖ ≤ ‖A‖`, and
  compactness transfer from `X_{m,c}` to `X_m`;
* `planarBSKernel_eq_planarBSC` and `norm_planarBSKernel`: identification of the planar
  Biot–Savart kernel from `B0009.kernel` with the complex kernel `(2π i z)⁻¹`;
* `norm_bsKernel_sub_planarBSKernel_le_of_norm_le` and `norm_bsKernel_sub_planarBSKernel_paired`:
  the paired periodic image estimate `‖K_c(x - y) - K_{ℝ²}(x - y)‖ ≤ (2π/9) c^{-2}(1 + |x| + |y|)`
  on `|x|, |y| ≤ c/4` (`x ≠ y`), derived from `Kernels.cylinderBS_eq_paired`;
* `gradScaleS`, `planarInteractionCLM`, `isCompactOperator_planarInteractionCLM`: Schwartz
  realization of the dilated Gaussian gradient `-(1+σ)^{-5/2} ∂_k E₀(y/√(1+σ))` and compactness of
  the complex planar interaction `A_{pl,σ}` on `B0008.L2w m` (`m > 1`, `1 + σ > 0`) via
  `B0061.isCompactOperator_mulK`;
* `IsCylInteractionOp.unique`, `IsGaussCylInteractionOp.unique`, `IsPlanarInteractionOp.unique`,
  `isCompact_image_of_continuousOn`, `totallyBounded_image_of_continuousOn`,
  `totallyBounded_biUnion_ball_of_continuousOn`: operator uniqueness and collective compactness
  from norm continuity on `[0, Σ]`;
* `interactionCylinderComparison_of`, `interactionCollectiveCompact_of`, and
  `interactionCylinder_of`: conditional assembly of `InteractionCylinderComparison` and
  `InteractionCollectiveCompact` from the four leaves `CylWeightedKernelStep` (`PartII-b:F1/1`),
  `TrainGradCoeffStep` (`PartII-b:F1/2`), `PlanarInteractionCompactStep` (`PartII-b:F1/3`), and
  `PlanarKernelBoundStep` (`PartII-b:F1/4`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal SchwartzMap

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-! ## 1. Ambient space `X_m`, cylinder space `X_{m,c}`, zero extension `J_c`, and restriction `R_c` -/

/-- The ambient weighted measure `⟨x⟩^{2m} dx = (1 + q² + η²)^m dq dη` on `ℝ²` (`B0579.density`). -/
def planeMeasure (m : ℝ) : Measure B0579.Plane :=
  volume.withDensity fun x => (B0579.density m x : ℝ≥0∞)

/-- The ambient space `X_m = L²(ℝ², ⟨x⟩^{2m} dx)` (SP 2119). -/
abbrev Xm (m : ℝ) : Type := Lp ℝ 2 (planeMeasure m)

/-- The cylinder space `X_{m,c} = L²(C_c, ⟨x⟩^{2m} dx)` (`B0579.X c m`). -/
abbrev Xmc (c m : ℝ) : Type := B0579.X c m

/-- The cylinder measure `B0579.cellMeasure c m` is the restriction of `planeMeasure m` to the
centered cell `B0579.cell c = [-c/2, c/2) × ℝ`. -/
theorem cellMeasure_eq_restrict_planeMeasure (c m : ℝ) :
    B0579.cellMeasure c m = (planeMeasure m).restrict (B0579.cell c) :=
  (restrict_withDensity (B0579.measurableSet_cell c) _).symm

private theorem indicator_ae_eq_of_cell (c m : ℝ) {f g : B0579.Plane → ℝ}
    (h : f =ᵐ[B0579.cellMeasure c m] g) :
    (B0579.cell c).indicator f =ᵐ[planeMeasure m] (B0579.cell c).indicator g := by
  have h' : f =ᵐ[(planeMeasure m).restrict (B0579.cell c)] g := by
    simpa only [cellMeasure_eq_restrict_planeMeasure] using h
  filter_upwards [(ae_restrict_iff' (B0579.measurableSet_cell c)).1 h'] with x hx
  by_cases hxc : x ∈ B0579.cell c
  · simp only [indicator_of_mem hxc, hx hxc]
  · simp only [indicator_of_notMem hxc]

theorem memLp_zeroExt (c m : ℝ) {f : B0579.Plane → ℝ}
    (hf : MemLp f 2 (B0579.cellMeasure c m)) :
    MemLp ((B0579.cell c).indicator f) 2 (planeMeasure m) := by
  have hf' : MemLp f 2 ((planeMeasure m).restrict (B0579.cell c)) := by
    simpa only [cellMeasure_eq_restrict_planeMeasure] using hf
  exact (memLp_indicator_iff_restrict (B0579.measurableSet_cell c)).2 hf'

theorem memLp_restrict_cell (c m : ℝ) {f : B0579.Plane → ℝ}
    (hf : MemLp f 2 (planeMeasure m)) :
    MemLp f 2 (B0579.cellMeasure c m) := by
  rw [cellMeasure_eq_restrict_planeMeasure]
  exact hf.restrict (B0579.cell c)

/-- Underlying function of the zero extension `J_c : X_{m,c} → X_m`. -/
def zeroExtFun (c m : ℝ) (f : Xmc c m) : Xm m :=
  (memLp_zeroExt c m (Lp.memLp f)).toLp ((B0579.cell c).indicator f)

theorem coeFn_zeroExtFun (c m : ℝ) (f : Xmc c m) :
    (zeroExtFun c m f : B0579.Plane → ℝ) =ᵐ[planeMeasure m] (B0579.cell c).indicator f :=
  MemLp.coeFn_toLp _

theorem norm_zeroExtFun (c m : ℝ) (f : Xmc c m) :
    ‖zeroExtFun c m f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (coeFn_zeroExtFun c m f),
    eLpNorm_indicator_eq_eLpNorm_restrict (B0579.measurableSet_cell c),
    ← cellMeasure_eq_restrict_planeMeasure]

/-- **Zero extension** `zeroExtIso c m : X_{m,c} →ₗᵢ[ℝ] X_m`, `f ↦ 1_{cell c} f`, a linear
isometry (SP 2119). -/
def zeroExtIso (c m : ℝ) : Xmc c m →ₗᵢ[ℝ] Xm m where
  toFun := zeroExtFun c m
  map_add' f g := by
    refine Lp.ext ?_
    filter_upwards [coeFn_zeroExtFun c m (f + g),
      Lp.coeFn_add (zeroExtFun c m f) (zeroExtFun c m g),
      coeFn_zeroExtFun c m f, coeFn_zeroExtFun c m g,
      indicator_ae_eq_of_cell c m (Lp.coeFn_add f g)] with x h1 h2 h3 h4 h5
    rw [h1, h2, Pi.add_apply, h3, h4, h5]
    by_cases hxc : x ∈ B0579.cell c
    · simp only [indicator_of_mem hxc, Pi.add_apply]
    · simp only [indicator_of_notMem hxc, add_zero]
  map_smul' a f := by
    refine Lp.ext ?_
    filter_upwards [coeFn_zeroExtFun c m (a • f),
      Lp.coeFn_smul a (zeroExtFun c m f),
      coeFn_zeroExtFun c m f,
      indicator_ae_eq_of_cell c m (Lp.coeFn_smul a f)] with x h1 h2 h3 h4
    rw [h1, RingHom.id_apply, h2, Pi.smul_apply, h3, h4]
    by_cases hxc : x ∈ B0579.cell c
    · simp only [indicator_of_mem hxc, Pi.smul_apply]
    · simp only [indicator_of_notMem hxc, smul_zero]
  norm_map' := norm_zeroExtFun c m

/-- **Zero extension** `J_c : X_{m,c} →L[ℝ] X_m` as a continuous linear map (SP 2119). -/
def Jc (c m : ℝ) : Xmc c m →L[ℝ] Xm m :=
  (zeroExtIso c m).toContinuousLinearMap

theorem norm_Jc_apply (c m : ℝ) (f : Xmc c m) : ‖Jc c m f‖ = ‖f‖ :=
  (zeroExtIso c m).norm_map f

/-- Underlying function of the restriction `R_c : X_m → X_{m,c}`. -/
def restrictCellFun (c m : ℝ) (f : Xm m) : Xmc c m :=
  (memLp_restrict_cell c m (Lp.memLp f)).toLp f

theorem coeFn_restrictCellFun (c m : ℝ) (f : Xm m) :
    (restrictCellFun c m f : B0579.Plane → ℝ) =ᵐ[B0579.cellMeasure c m] f :=
  MemLp.coeFn_toLp _

theorem norm_restrictCellFun_le (c m : ℝ) (f : Xm m) :
    ‖restrictCellFun c m f‖ ≤ ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (coeFn_restrictCellFun c m f),
    cellMeasure_eq_restrict_planeMeasure]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top _)
    (eLpNorm_mono_measure _ Measure.restrict_le_self)

/-- **Restriction** `R_c : X_m →L[ℝ] X_{m,c}` as a continuous linear map (SP 2119). -/
def Rc (c m : ℝ) : Xm m →L[ℝ] Xmc c m :=
  LinearMap.mkContinuous
    { toFun := restrictCellFun c m
      map_add' := fun f g => by
        refine Lp.ext ?_
        have hfg : ((f + g : Xm m) : B0579.Plane → ℝ) =ᵐ[B0579.cellMeasure c m] f + g := by
          rw [cellMeasure_eq_restrict_planeMeasure]
          exact ae_restrict_of_ae (Lp.coeFn_add f g)
        filter_upwards [coeFn_restrictCellFun c m (f + g),
          Lp.coeFn_add (restrictCellFun c m f) (restrictCellFun c m g),
          coeFn_restrictCellFun c m f, coeFn_restrictCellFun c m g, hfg]
          with x h1 h2 h3 h4 h5
        rw [h1, h2, Pi.add_apply, h3, h4, h5, Pi.add_apply]
      map_smul' := fun a f => by
        refine Lp.ext ?_
        have haf : ((a • f : Xm m) : B0579.Plane → ℝ) =ᵐ[B0579.cellMeasure c m] a • f := by
          rw [cellMeasure_eq_restrict_planeMeasure]
          exact ae_restrict_of_ae (Lp.coeFn_smul a f)
        filter_upwards [coeFn_restrictCellFun c m (a • f),
          Lp.coeFn_smul a (restrictCellFun c m f),
          coeFn_restrictCellFun c m f, haf] with x h1 h2 h3 h4
        rw [RingHom.id_apply, h1, h2, Pi.smul_apply, h3, h4, Pi.smul_apply] }
    1
    (fun f => by simpa only [LinearMap.coe_mk, AddHom.coe_mk, one_mul] using
      norm_restrictCellFun_le c m f)

theorem norm_Rc_apply_le (c m : ℝ) (f : Xm m) : ‖Rc c m f‖ ≤ ‖f‖ :=
  norm_restrictCellFun_le c m f

theorem norm_Rc_le (c m : ℝ) : ‖Rc c m‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun f => by
    simpa only [one_mul] using norm_Rc_apply_le c m f)

private theorem ae_cellMeasure_of_restrict (c m : ℝ) {h₁ h₂ : B0579.Plane → ℝ}
    (h : h₁ =ᵐ[(planeMeasure m).restrict (B0579.cell c)] h₂) :
    h₁ =ᵐ[B0579.cellMeasure c m] h₂ := by
  rw [cellMeasure_eq_restrict_planeMeasure]
  exact h

/-- `R_c J_c = I` on `X_{m,c}`. -/
theorem Rc_Jc (c m : ℝ) (f : Xmc c m) : Rc c m (Jc c m f) = f := by
  refine Lp.ext ?_
  have hj : (Jc c m f : B0579.Plane → ℝ) =ᵐ[(planeMeasure m).restrict (B0579.cell c)]
      (B0579.cell c).indicator f :=
    ae_restrict_of_ae (coeFn_zeroExtFun c m f)
  have hind : (B0579.cell c).indicator (f : B0579.Plane → ℝ) =ᵐ[(planeMeasure m).restrict (B0579.cell c)]
      (f : B0579.Plane → ℝ) :=
    indicator_ae_eq_restrict (B0579.measurableSet_cell c)
  exact (coeFn_restrictCellFun c m (Jc c m f)).trans
    (ae_cellMeasure_of_restrict c m (hj.trans hind))

/-- Operator-norm bound `‖J_c A R_c‖_{X_m → X_m} ≤ ‖A‖_{X_{m,c} → X_{m,c}}`. -/
theorem norm_Jc_comp_Rc_le (c m : ℝ) (A : Xmc c m →L[ℝ] Xmc c m) :
    ‖(Jc c m).comp (A.comp (Rc c m))‖ ≤ ‖A‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A) fun f => ?_
  simp only [ContinuousLinearMap.comp_apply, norm_Jc_apply]
  exact (A.le_opNorm (Rc c m f)).trans
    (mul_le_mul_of_nonneg_left (norm_Rc_apply_le c m f) (norm_nonneg A))

/-- Linearity of `A ↦ J_c A R_c`: `J_c (A - B) R_c = J_c A R_c - J_c B R_c`. -/
theorem Jc_comp_Rc_sub (c m : ℝ) (A B : Xmc c m →L[ℝ] Xmc c m) :
    (Jc c m).comp ((A - B).comp (Rc c m)) =
      (Jc c m).comp (A.comp (Rc c m)) - (Jc c m).comp (B.comp (Rc c m)) := by
  ext1 f
  simp only [ContinuousLinearMap.comp_apply, sub_apply, map_sub]

/-- `‖J_c A R_c - J_c B R_c‖_{X_m → X_m} ≤ ‖A - B‖_{X_{m,c} → X_{m,c}}`. -/
theorem norm_Jc_comp_Rc_sub_le (c m : ℝ) (A B : Xmc c m →L[ℝ] Xmc c m) :
    ‖(Jc c m).comp (A.comp (Rc c m)) - (Jc c m).comp (B.comp (Rc c m))‖ ≤ ‖A - B‖ := by
  rw [← Jc_comp_Rc_sub]
  exact norm_Jc_comp_Rc_le c m (A - B)

/-- Compactness of a cylinder interaction `Ac` on `X_{m,c}` transfers to its zero extension
`J_c Ac R_c` on `X_m`. -/
theorem isCompactOperator_Jc_comp_Rc {c m : ℝ} {Ac : Xmc c m →L[ℝ] Xmc c m}
    (hAc : IsCompactOperator Ac) :
    IsCompactOperator ((Jc c m).comp (Ac.comp (Rc c m))) :=
  (hAc.comp_clm (Rc c m)).clm_comp (Jc c m)

/-! ## 2. Planar Gaussian data (`B0009`) and the planar interaction `A_{pl,σ}` -/

/-- Complex coordinate `q + i η` of a point `x = (q, η) ∈ ℝ × ℝ`, inverse to `B0009.toPlane`. -/
def ofPlane (x : B0579.Plane) : ℂ := ⟨x.1, x.2⟩

@[simp]
theorem ofPlane_re (x : B0579.Plane) : (ofPlane x).re = x.1 := rfl

@[simp]
theorem ofPlane_im (x : B0579.Plane) : (ofPlane x).im = x.2 := rfl

@[simp]
theorem toPlane_ofPlane (x : B0579.Plane) : B0009.toPlane (ofPlane x) = x := by
  ext <;> rfl

@[simp]
theorem ofPlane_toPlane (y : ℂ) : ofPlane (B0009.toPlane y) = y := by
  apply Complex.ext <;> rfl

theorem ofPlane_eq_add_mul_I (x : B0579.Plane) :
    ofPlane x = (x.1 : ℂ) + (x.2 : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [ofPlane]

theorem ofPlane_sub (x y : B0579.Plane) : ofPlane (x - y) = ofPlane x - ofPlane y := by
  apply Complex.ext <;> simp [ofPlane]

@[simp]
theorem ofPlane_zero : ofPlane (0 : B0579.Plane) = 0 := by
  apply Complex.ext <;> simp [ofPlane]

theorem ofPlane_ne_zero {z : B0579.Plane} (hz : z ≠ 0) : ofPlane z ≠ 0 := by
  intro h
  apply hz
  have h1 : z.1 = 0 := by simpa [ofPlane] using congrArg Complex.re h
  have h2 : z.2 = 0 := by simpa [ofPlane] using congrArg Complex.im h
  exact Prod.ext h1 h2

/-- Euclidean modulus `|x| = √(q² + η²)` on `ℝ × ℝ`. -/
def euclidNorm (x : B0579.Plane) : ℝ := Real.sqrt (x.1 ^ 2 + x.2 ^ 2)

theorem euclidNorm_nonneg (x : B0579.Plane) : 0 ≤ euclidNorm x := Real.sqrt_nonneg _

theorem norm_ofPlane (x : B0579.Plane) : ‖ofPlane x‖ = euclidNorm x := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  rfl

theorem norm_ofPlane_sq (x : B0579.Plane) : ‖ofPlane x‖ ^ 2 = x.1 ^ 2 + x.2 ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [ofPlane, sq]

theorem euclidNorm_sub_le (x y : B0579.Plane) :
    euclidNorm (x - y) ≤ euclidNorm x + euclidNorm y := by
  rw [← norm_ofPlane, ← norm_ofPlane, ← norm_ofPlane, ofPlane_sub]
  exact norm_sub_le _ _

/-- Rescaled planar coordinates `x / √a = (q / √a, η / √a)`. -/
def scalePlane (a : ℝ) (x : B0579.Plane) : B0579.Plane :=
  (x.1 / Real.sqrt a, x.2 / Real.sqrt a)

/-- The planar Gaussian vorticity `E_{1+σ}(x) = (1+σ)^{-2} E₀(x / √(1+σ))` at slow age `σ`
(SP 2120), built from `B0009.E0`. -/
def planarE (σ : ℝ) (x : B0579.Plane) : ℝ :=
  (1 + σ) ^ (-2 : ℝ) * B0009.E0 (ofPlane (scalePlane (1 + σ) x))

/-- The planar Gaussian vorticity gradient `∇E_{1+σ}(x) = (1+σ)^{-5/2} ∇E₀(x / √(1+σ))` at slow
age `σ` (SP 2120–2122), built from `B0009.gradE0`. -/
def planarGradE (σ : ℝ) (x : B0579.Plane) : B0579.Plane :=
  ((1 + σ) ^ (-5 / 2 : ℝ) * (B0009.gradE0 (ofPlane (scalePlane (1 + σ) x))).1,
   (1 + σ) ^ (-5 / 2 : ℝ) * (B0009.gradE0 (ofPlane (scalePlane (1 + σ) x))).2)

/-- `∇E_{1+σ}(x)` as a vector in `Cyl.Vec2 = EuclideanSpace ℝ (Fin 2)`. -/
def planarGradEVec (σ : ℝ) (x : B0579.Plane) : Cyl.Vec2 :=
  Cyl.vec (planarGradE σ x).1 (planarGradE σ x).2

/-- The real planar Biot–Savart kernel `K_{ℝ²}(z) = z^⊥ / (2π |z|²)` on `ℝ × ℝ`, built from
`B0009.kernel`. -/
def planarBSKernel (z : B0579.Plane) : Cyl.Vec2 :=
  Cyl.vec (B0009.kernel 0 (ofPlane z)).re (B0009.kernel 1 (ofPlane z)).re

/-- The complex planar Biot–Savart kernel `(2π i z)⁻¹` at `z = q + i η`. -/
def planarBSC (z : B0579.Plane) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I * ofPlane z)⁻¹

/-- `planarBSKernel z` is `(Re (2π i z)⁻¹, -Im (2π i z)⁻¹)`, matching the convention of
`Cyl.bsKernel c z = (Re K_c(z), -Im K_c(z))`. -/
theorem planarBSKernel_eq_planarBSC (z : B0579.Plane) :
    planarBSKernel z = Cyl.vec (planarBSC z).re (-(planarBSC z).im) := by
  have hre0 : (B0009.kernel 0 (ofPlane z)).re = -z.2 / (2 * Real.pi * ‖ofPlane z‖ ^ 2) := rfl
  have hre1 : (B0009.kernel 1 (ofPlane z)).re = z.1 / (2 * Real.pi * ‖ofPlane z‖ ^ 2) := rfl
  have h_inv : planarBSC z =
      ⟨-z.2 / (2 * Real.pi * ‖ofPlane z‖ ^ 2), -z.1 / (2 * Real.pi * ‖ofPlane z‖ ^ 2)⟩ := by
    rcases eq_or_ne z 0 with rfl | hz
    · apply Complex.ext <;> simp [planarBSC]
    · refine inv_eq_of_mul_eq_one_right ?_
      have hnz : ‖ofPlane z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (ofPlane_ne_zero hz))
      have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
      apply Complex.ext
      · simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.re_ofNat, Complex.im_ofNat, Complex.I_re, Complex.I_im,
          ofPlane_re, ofPlane_im, Complex.one_re]
        rw [norm_ofPlane_sq] at hnz ⊢
        field_simp
        ring
      · simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.re_ofNat, Complex.im_ofNat, Complex.I_re, Complex.I_im,
          ofPlane_re, ofPlane_im, Complex.one_im]
        ring
  have hcre : (planarBSC z).re = -z.2 / (2 * Real.pi * ‖ofPlane z‖ ^ 2) :=
    congrArg Complex.re h_inv
  have hcim : -(planarBSC z).im = z.1 / (2 * Real.pi * ‖ofPlane z‖ ^ 2) := by
    have him : (planarBSC z).im = -z.1 / (2 * Real.pi * ‖ofPlane z‖ ^ 2) :=
      congrArg Complex.im h_inv
    rw [him, neg_div, neg_neg]
  rw [planarBSKernel, hre0, hre1, hcre, hcim]

theorem norm_planarBSKernel (z : B0579.Plane) :
    ‖planarBSKernel z‖ = ‖planarBSC z‖ := by
  rw [planarBSKernel_eq_planarBSC, Cyl.norm_vec, neg_sq, Complex.norm_eq_sqrt_sq_add_sq]

/-- The real planar Biot–Savart velocity `K_{ℝ²} f(x) = ∫_{ℝ²} f(y) K_{ℝ²}(x - y) dy` on `ℝ × ℝ`. -/
def planarK (f : B0579.Plane → ℝ) (x : B0579.Plane) : Cyl.Vec2 :=
  ∫ y : B0579.Plane, f y • planarBSKernel (x - y)

/-- **The planar interaction** `A_{pl,σ} f(x) = -(K_{ℝ²} f)(x)·∇E_{1+σ}(x)` (SP 2121–2123). -/
def Apl (σ : ℝ) (f : B0579.Plane → ℝ) (x : B0579.Plane) : ℝ :=
  -(planarK f x 0 * (planarGradE σ x).1 + planarK f x 1 * (planarGradE σ x).2)

/-- **`A` is the planar interaction operator `A_{pl,σ}` on `X_m`** (SP 2121–2123):
for every `f ∈ X_m`, `A f = A_{pl,σ} f` almost everywhere on `ℝ²`. -/
def IsPlanarInteractionOp (m σ : ℝ) (A : Xm m →L[ℝ] Xm m) : Prop :=
  ∀ f : Xm m, (A f : B0579.Plane → ℝ) =ᵐ[planeMeasure m] Apl σ f

/-- `A_{pl,σ}` is uniquely determined by its pointwise formula. -/
theorem IsPlanarInteractionOp.unique {m σ : ℝ} {A B : Xm m →L[ℝ] Xm m}
    (hA : IsPlanarInteractionOp m σ A) (hB : IsPlanarInteractionOp m σ B) : A = B := by
  ext1 f
  exact Lp.ext ((hA f).trans (hB f).symm)

/-! ## 3. Cylinder interaction `A_c(s)`, weighted kernel operators, and bridge to `IIIa.IsBiotSavart` -/

/-- The train vorticity gradient `∇E_c(s, x) = (∂_q E_c(s, x), ∂_η E_c(s, x))` on `ℝ × ℝ`. -/
def trainGradE {ν c : ℝ} (tr : B0140.TrainSol ν c) (s : ℝ) (x : B0579.Plane) : B0579.Plane :=
  (B0579.pd 0 (B0238.Ec tr s) x, B0579.pd 1 (B0238.Ec tr s) x)

/-- Pointwise formula for the cylinder Biot–Savart interaction with coefficient `b`:
`-(K_c w)(x) · b(x)`. -/
def cylWeightedOpFun (c : ℝ) (b : B0579.Plane → B0579.Plane)
    (w : B0579.Plane → ℝ) (x : B0579.Plane) : ℝ :=
  -(Cyl.K c w x 0 * (b x).1 + Cyl.K c w x 1 * (b x).2)

/-- `T` realizes `w ↦ -(K_c w) · b` on `X_{m,c}`. -/
def IsCylWeightedOp (c m : ℝ) (b : B0579.Plane → B0579.Plane)
    (T : Xmc c m →L[ℝ] Xmc c m) : Prop :=
  ∀ f : Xmc c m, (T f : B0579.Plane → ℝ) =ᵐ[B0579.cellMeasure c m] cylWeightedOpFun c b f

theorem IsCylWeightedOp.unique {c m : ℝ} {b : B0579.Plane → B0579.Plane}
    {A B : Xmc c m →L[ℝ] Xmc c m}
    (hA : IsCylWeightedOp c m b A) (hB : IsCylWeightedOp c m b B) : A = B := by
  ext1 f
  exact Lp.ext ((hA f).trans (hB f).symm)

theorem IsCylWeightedOp.add {c m : ℝ} {b₁ b₂ : B0579.Plane → B0579.Plane}
    {T₁ T₂ : Xmc c m →L[ℝ] Xmc c m}
    (h₁ : IsCylWeightedOp c m b₁ T₁) (h₂ : IsCylWeightedOp c m b₂ T₂) :
    IsCylWeightedOp c m (fun x => b₁ x + b₂ x) (T₁ + T₂) := by
  intro f
  filter_upwards [Lp.coeFn_add (T₁ f) (T₂ f), h₁ f, h₂ f] with x hadd ha₁ ha₂
  rw [add_apply, hadd, Pi.add_apply, ha₁, ha₂]
  simp only [cylWeightedOpFun, Prod.fst_add, Prod.snd_add]
  ring

/-- A continuous vector coefficient `b : B0579.Plane → B0579.Plane` on the cylinder with
weighted decay `(|(b x).1| + |(b x).2|) * B0579.jb x ^ (m / 2 + 1) ≤ B` on `B0579.cell c`. -/
def IsCylWeightedCoeff (c m B : ℝ) (b : B0579.Plane → B0579.Plane) : Prop :=
  Continuous b ∧ ∀ x ∈ B0579.cell c, (|(b x).1| + |(b x).2|) * B0579.jb x ^ (m / 2 + 1) ≤ B

theorem IsCylWeightedCoeff.add {c m B₁ B₂ : ℝ} {b₁ b₂ : B0579.Plane → B0579.Plane}
    (h₁ : IsCylWeightedCoeff c m B₁ b₁) (h₂ : IsCylWeightedCoeff c m B₂ b₂) :
    IsCylWeightedCoeff c m (B₁ + B₂) (fun x => b₁ x + b₂ x) := by
  refine ⟨h₁.1.add h₂.1, fun x hx => ?_⟩
  have hjb : 0 ≤ B0579.jb x ^ (m / 2 + 1) := Real.rpow_nonneg (B0579.jb_pos x).le _
  have habs : |(b₁ x + b₂ x).1| + |(b₁ x + b₂ x).2| ≤
      (|(b₁ x).1| + |(b₁ x).2|) + (|(b₂ x).1| + |(b₂ x).2|) := by
    have hfst : |(b₁ x).1 + (b₂ x).1| ≤ |(b₁ x).1| + |(b₂ x).1| := abs_add_le _ _
    have hsnd : |(b₁ x).2 + (b₂ x).2| ≤ |(b₁ x).2| + |(b₂ x).2| := abs_add_le _ _
    simp only [Prod.fst_add, Prod.snd_add]
    linarith [hfst, hsnd]
  calc (|(b₁ x + b₂ x).1| + |(b₁ x + b₂ x).2|) * B0579.jb x ^ (m / 2 + 1)
      ≤ ((|(b₁ x).1| + |(b₁ x).2|) + (|(b₂ x).1| + |(b₂ x).2|)) * B0579.jb x ^ (m / 2 + 1) :=
        mul_le_mul_of_nonneg_right habs hjb
    _ = (|(b₁ x).1| + |(b₁ x).2|) * B0579.jb x ^ (m / 2 + 1) +
          (|(b₂ x).1| + |(b₂ x).2|) * B0579.jb x ^ (m / 2 + 1) := add_mul _ _ _
    _ ≤ B₁ + B₂ := add_le_add (h₁.2 x hx) (h₂.2 x hx)

/-- **The cylinder interaction** `A_c(s) w(x) = -(K_c w)(x)·∇E_c(s, x)` on the cylinder strip,
with `K_c = Cyl.K c` (`Lib/CylinderB/BiotSavart.lean`) and `E_c = B0238.Ec` (`Units/B0238.lean`). -/
def cylAc {ν c : ℝ} (tr : B0140.TrainSol ν c) (s : ℝ) (w : B0579.Plane → ℝ) (x : B0579.Plane) : ℝ :=
  -(Cyl.K c w x 0 * B0579.pd 0 (B0238.Ec tr s) x +
    Cyl.K c w x 1 * B0579.pd 1 (B0238.Ec tr s) x)

/-- **`A` is the cylinder interaction operator `A_c(s)` on `X_{m,c} = B0579.X c m`**:
for every `f ∈ X_{m,c}`, `A f = -(K_c f)·∇E_c(s)` almost everywhere on the cell. -/
def IsCylInteractionOp {ν c : ℝ} (tr : B0140.TrainSol ν c) (m s : ℝ)
    (A : Xmc c m →L[ℝ] Xmc c m) : Prop :=
  ∀ f : Xmc c m, (A f : B0579.Plane → ℝ) =ᵐ[B0579.cellMeasure c m] cylAc tr s f

theorem IsCylInteractionOp.unique {ν c m s : ℝ} {tr : B0140.TrainSol ν c}
    {A B : Xmc c m →L[ℝ] Xmc c m}
    (hA : IsCylInteractionOp tr m s A) (hB : IsCylInteractionOp tr m s B) : A = B := by
  ext1 f
  exact Lp.ext ((hA f).trans (hB f).symm)

theorem isCylInteractionOp_iff_isCylWeightedOp {ν c m s : ℝ} (tr : B0140.TrainSol ν c)
    (A : Xmc c m →L[ℝ] Xmc c m) :
    IsCylInteractionOp tr m s A ↔ IsCylWeightedOp c m (trainGradE tr s) A :=
  Iff.rfl

/-- The intermediate cylinder interaction `A_c^{pl}(σ) w = -(K_c w)·∇E_{1+σ}` on the cell strip,
replacing the actual train vorticity gradient `∇E_c(σ/ν)` in `cylAc` by the planar Gaussian
gradient `∇E_{1+σ}`. -/
def AcGauss (c σ : ℝ) (w : B0579.Plane → ℝ) (x : B0579.Plane) : ℝ :=
  -(Cyl.K c w x 0 * (planarGradE σ x).1 + Cyl.K c w x 1 * (planarGradE σ x).2)

/-- `A` realizes the intermediate Gaussian-coefficient cylinder interaction `A_c^{pl}(σ)` on
`X_{m,c}`. -/
def IsGaussCylInteractionOp (c m σ : ℝ) (A : Xmc c m →L[ℝ] Xmc c m) : Prop :=
  ∀ f : Xmc c m, (A f : B0579.Plane → ℝ) =ᵐ[B0579.cellMeasure c m] AcGauss c σ f

theorem IsGaussCylInteractionOp.unique {c m σ : ℝ} {A B : Xmc c m →L[ℝ] Xmc c m}
    (hA : IsGaussCylInteractionOp c m σ A) (hB : IsGaussCylInteractionOp c m σ B) : A = B := by
  ext1 f
  exact Lp.ext ((hA f).trans (hB f).symm)

theorem isGaussCylInteractionOp_iff_isCylWeightedOp (c m σ : ℝ) (A : Xmc c m →L[ℝ] Xmc c m) :
    IsGaussCylInteractionOp c m σ A ↔ IsCylWeightedOp c m (planarGradE σ) A :=
  Iff.rfl

/-- The train comparison on `s ≤ Σ/ν` in the `m`-weighted derivative budget
`⟨x⟩^{m+2} = (1 + q² + η²)^{m/2+1}` on the centered cell `C_c` (SP 2085–2090: "On `s ≤ Σ/ν`, the
train comparison gives, in any fixed finite weighted derivative budget,
`‖v_c - V_c^p‖ + ‖E_c - E_c^p‖ ≤ δ_c`"). For `m > 8` this strengthens `TrainClose` (`jb x ^ 4`),
controlling `∇(E_c - E_c^p)` in `L²(C_c, ⟨x⟩^{2m} dx) ∩ L^∞(C_c, ⟨x⟩^m)`. -/
def TrainCloseM {ν c : ℝ} (m : ℝ) (tr : B0140.TrainSol ν c) (Sg δ : ℝ) : Prop :=
  ∀ s : ℝ, 0 ≤ s → s ≤ Sg / ν → ∀ x ∈ B0579.cell c, ∀ j ≤ 4,
    ‖iteratedFDeriv ℝ j (fun z => tr.v s z - Train.Vc ν c s z) x‖ *
      B0579.jb x ^ (m / 2 + 1) ≤ δ

/-- For `m ≥ 6` (in particular `m > 8`), `TrainCloseM m tr Sg δ` implies `TrainClose tr Sg δ`. -/
theorem TrainCloseM.toTrainClose {ν c m : ℝ} (hm : 6 ≤ m) {tr : B0140.TrainSol ν c} {Sg δ : ℝ}
    (h : TrainCloseM m tr Sg δ) : TrainClose tr Sg δ := by
  intro s hs0 hs1 x hx j hj
  have hjb1 : 1 ≤ B0579.jb x := by
    unfold B0579.jb
    nlinarith [sq_nonneg x.1, sq_nonneg x.2]
  have hpow : B0579.jb x ^ 4 ≤ B0579.jb x ^ (m / 2 + 1) := by
    rw [← Real.rpow_natCast (B0579.jb x) 4]
    exact Real.rpow_le_rpow_of_exponent_le hjb1 (by push_cast; linarith)
  exact (mul_le_mul_of_nonneg_left hpow (norm_nonneg _)).trans (h s hs0 hs1 x hx j hj)

/-- Compatibility of the cylinder interaction `IsCylInteractionOp tr m s A` with the
distributional Biot–Savart characterization `IIIa.IsBiotSavart` (`Short/PartIII-a/Defs.lean`):
`A` is `w ↦ -(K_c w)·∇E_c(s)` on `X_{m,c}`, and for every zero-circulation vorticity `f ∈ X_{m,c}`,
there exists a distributional Biot–Savart velocity `u` satisfying `IIIa.IsBiotSavart c` whose
advection of `E_c(s)` agrees a.e. on the cell with `A f`. -/
def IsBiotSavartCylInteractionOp {ν c : ℝ} (tr : B0140.TrainSol ν c) (m s : ℝ)
    (A : Xmc c m →L[ℝ] Xmc c m) : Prop :=
  IsCylInteractionOp tr m s A ∧
    ∀ f : Xmc c m, IIIa.HasZeroCirculation c (fun x => ((f x : ℝ) : ℂ)) →
      ∃ u : B0579.Plane → Fin 2 → ℂ,
        IIIa.IsBiotSavart c (fun x => ((f x : ℝ) : ℂ)) u ∧
          ∀ᵐ x ∂volume.restrict (B0579.cell c),
            ((A f x : ℝ) : ℂ) =
              -(u x 0 * (B0579.pd 0 (B0238.Ec tr s) x : ℂ) +
                u x 1 * (B0579.pd 1 (B0238.Ec tr s) x : ℂ))

/-! ## 4. Paired periodic image estimate on `|x|, |y| ≤ c/4` (SP 2119–2126, proved) -/

/-- The explicit constant `2π/9` in the paired periodic image bound
`|K_c(x - y) - K_{ℝ²}(x - y)| ≤ C c^{-2}(1 + |x| + |y|)` on `|x|, |y| ≤ c/4`. -/
def pairedImageConst : ℝ := 2 * Real.pi / 9

theorem pairedImageConst_pos : 0 < pairedImageConst := by
  unfold pairedImageConst
  positivity

private theorem hasSum_pnat_inv_sq :
    HasSum (fun n : ℕ+ => 1 / ((n : ℕ) : ℝ) ^ 2) (Real.pi ^ 2 / 6) := by
  refine (PNat.coe_injective.hasSum_iff (fun x hx => ?_)).mpr hasSum_zeta_two
  have hx0 : x = 0 := by
    by_contra hne
    exact hx ⟨⟨x, Nat.pos_of_ne_zero hne⟩, rfl⟩
  simp [hx0]

private theorem pair_norm_ge {z : ℂ} {a : ℝ} (ha : 0 < a) (hza : 2 * ‖z‖ ≤ a) :
    3 / 4 * a ^ 2 ≤ ‖z ^ 2 - (a : ℂ) ^ 2‖ := by
  have h1 : ‖((a : ℂ) ^ 2)‖ - ‖z ^ 2‖ ≤ ‖(a : ℂ) ^ 2 - z ^ 2‖ := norm_sub_norm_le _ _
  rw [norm_sub_rev, norm_pow, norm_pow, Complex.norm_real, Real.norm_of_nonneg ha.le] at h1
  have hz2 : ‖z‖ ^ 2 ≤ a ^ 2 / 4 := by
    have h := pow_le_pow_left₀ (norm_nonneg z) (show ‖z‖ ≤ a / 2 by linarith) 2
    linarith [show (a / 2) ^ 2 = a ^ 2 / 4 by ring]
  linarith

private theorem norm_pair_inv_le_firstOrder {z : ℂ} {a : ℝ} (ha : 0 < a) (hza : 2 * ‖z‖ ≤ a) :
    ‖1 / (z - a) + 1 / (z + a)‖ ≤ 8 / 3 * ‖z‖ / a ^ 2 := by
  have hD := pair_norm_ge ha hza
  have hD0 : 0 < ‖z ^ 2 - (a : ℂ) ^ 2‖ := lt_of_lt_of_le (by positivity) hD
  have hsq_ne : z ^ 2 - (a : ℂ) ^ 2 ≠ 0 := norm_ne_zero_iff.mp hD0.ne'
  have hsub_ne : z - a ≠ 0 := fun h => hsq_ne (by
    rw [show z ^ 2 - (a : ℂ) ^ 2 = (z - a) * (z + a) by ring, h, zero_mul])
  have hadd_ne : z + a ≠ 0 := fun h => hsq_ne (by
    rw [show z ^ 2 - (a : ℂ) ^ 2 = (z - a) * (z + a) by ring, h, mul_zero])
  have hid : 1 / (z - a) + 1 / (z + a) = 2 * z / (z ^ 2 - (a : ℂ) ^ 2) := by
    field_simp
    ring
  rw [hid, norm_div, norm_mul, Complex.norm_ofNat, div_le_div_iff₀ hD0 (by positivity)]
  calc 2 * ‖z‖ * a ^ 2 = 8 / 3 * ‖z‖ * (3 / 4 * a ^ 2) := by ring
    _ ≤ 8 / 3 * ‖z‖ * ‖z ^ 2 - (a : ℂ) ^ 2‖ :=
      mul_le_mul_of_nonneg_left hD (by positivity)

private theorem div_mem_integerComplement {c : ℝ} (hc : 0 < c) {z : ℂ} (hz : z ≠ 0)
    (hzc : ‖z‖ ≤ c / 2) : z / c ∈ Complex.integerComplement := by
  rintro ⟨m, hm⟩
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  rcases eq_or_ne m 0 with rfl | hm0
  · apply hz
    have h0 : z / (c : ℂ) = 0 := by simpa using hm.symm
    exact (div_eq_zero_iff.mp h0).resolve_right hc0
  · have hm1 : (1 : ℝ) ≤ ‖(m : ℂ)‖ := by
      rw [Complex.norm_intCast]
      exact_mod_cast Int.one_le_abs hm0
    have h1 : ‖z / (c : ℂ)‖ ≤ 1 / 2 := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hc.le, div_le_iff₀ hc]
      linarith
    have h2 : ‖(m : ℂ)‖ = ‖z / (c : ℂ)‖ := congrArg norm hm
    linarith

/-- On the centered disk `|z| ≤ c/2` (`z ≠ 0`, `c > 0`), the difference between the cylinder
Biot–Savart kernel `Cyl.bsKernel c z` and the planar kernel `planarBSKernel z` is bounded by
`pairedImageConst * c^{-2} * |z|`. Derived from `Kernels.cylinderBS_eq_paired`. -/
theorem norm_bsKernel_sub_planarBSKernel_le_of_norm_le {c : ℝ} (hc : 0 < c) {z : B0579.Plane}
    (hz : z ≠ 0) (hzc : euclidNorm z ≤ c / 2) :
    ‖Cyl.bsKernel c z - planarBSKernel z‖ ≤ pairedImageConst * c ^ (-2 : ℝ) * euclidNorm z := by
  set w : ℂ := ofPlane z
  have hw0 : w ≠ 0 := ofPlane_ne_zero hz
  have hwn : ‖w‖ = euclidNorm z := norm_ofPlane z
  have hw_le : ‖w‖ ≤ c / 2 := by rwa [hwn]
  have hbsC : Cyl.bsC c z = Kernels.cylinderBS c w := by
    rw [Cyl.bsC, ← ofPlane_eq_add_mul_I]
  have hvec : ‖Cyl.bsKernel c z - planarBSKernel z‖ = ‖Cyl.bsC c z - planarBSC z‖ := by
    rw [Cyl.bsKernel, planarBSKernel_eq_planarBSC]
    have hsub : Cyl.vec (Cyl.bsC c z).re (-(Cyl.bsC c z).im) -
        Cyl.vec (planarBSC z).re (-(planarBSC z).im) =
        Cyl.vec (Cyl.bsC c z - planarBSC z).re (-(Cyl.bsC c z - planarBSC z).im) := by
      ext i
      fin_cases i
      · simp [Cyl.vec]
      · simp [Cyl.vec]; ring
    rw [hsub, Cyl.norm_vec, neg_sq, Complex.norm_eq_sqrt_sq_add_sq]
  rw [hvec, hbsC, planarBSC, ← hwn]
  rw [Kernels.cylinderBS_eq_paired hc (div_mem_integerComplement hc hw0 hw_le)]
  have hexpr : (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (1 / w + ∑' n : ℕ+, (1 / (w - n * c) + 1 / (w + n * c))) -
      (2 * (Real.pi : ℂ) * Complex.I * w)⁻¹ =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ∑' n : ℕ+, (1 / (w - n * c) + 1 / (w + n * c)) := by
    rw [mul_inv]
    ring
  rw [hexpr, norm_mul, norm_inv, norm_mul, norm_mul, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one]
  have hterm : ∀ n : ℕ+,
      ‖1 / (w - (n : ℂ) * c) + 1 / (w + (n : ℂ) * c)‖ ≤
        8 / 3 * ‖w‖ / c ^ 2 * (1 / ((n : ℕ) : ℝ) ^ 2) := by
    intro n
    have hn1 : (1 : ℝ) ≤ (n : ℕ) := by exact_mod_cast Nat.succ_le_of_lt n.pos
    have ha : 0 < ((n : ℕ) : ℝ) * c := by positivity
    have hwa : 2 * ‖w‖ ≤ ((n : ℕ) : ℝ) * c := by nlinarith
    have h := norm_pair_inv_le_firstOrder ha hwa
    push_cast at h
    refine h.trans (le_of_eq ?_)
    have : ((n : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  have hg : HasSum (fun n : ℕ+ => 8 / 3 * ‖w‖ / c ^ 2 * (1 / ((n : ℕ) : ℝ) ^ 2))
      (8 / 3 * ‖w‖ / c ^ 2 * (Real.pi ^ 2 / 6)) :=
    hasSum_pnat_inv_sq.mul_left _
  have ht := tsum_of_norm_bounded hg hterm
  calc (2 * Real.pi)⁻¹ * ‖∑' n : ℕ+, (1 / (w - (n : ℂ) * c) + 1 / (w + (n : ℂ) * c))‖
      ≤ (2 * Real.pi)⁻¹ * (8 / 3 * ‖w‖ / c ^ 2 * (Real.pi ^ 2 / 6)) := by gcongr
    _ = pairedImageConst * c ^ (-2 : ℝ) * ‖w‖ := by
      rw [Real.rpow_neg hc.le, Real.rpow_two]
      unfold pairedImageConst
      have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
      field_simp
      ring

/-- **Paired periodic image estimate** (SP 2119–2126): for `c > 0` and `|x|, |y| ≤ c/4` (`x ≠ y`),
`‖K_c(x - y) - K_{ℝ²}(x - y)‖ ≤ pairedImageConst * c^{-2} * (1 + |x| + |y|)`. -/
theorem norm_bsKernel_sub_planarBSKernel_paired {c : ℝ} (hc : 0 < c) {x y : B0579.Plane}
    (hxy : x ≠ y) (hx : euclidNorm x ≤ c / 4) (hy : euclidNorm y ≤ c / 4) :
    ‖Cyl.bsKernel c (x - y) - planarBSKernel (x - y)‖ ≤
      pairedImageConst * c ^ (-2 : ℝ) * (1 + euclidNorm x + euclidNorm y) := by
  have hz0 : x - y ≠ 0 := sub_ne_zero.2 hxy
  have htri : euclidNorm (x - y) ≤ euclidNorm x + euclidNorm y := euclidNorm_sub_le x y
  have hzc : euclidNorm (x - y) ≤ c / 2 := by linarith
  have h1 := norm_bsKernel_sub_planarBSKernel_le_of_norm_le hc hz0 hzc
  have h2 : euclidNorm (x - y) ≤ 1 + euclidNorm x + euclidNorm y := by linarith
  have hpos : 0 ≤ pairedImageConst * c ^ (-2 : ℝ) :=
    mul_nonneg pairedImageConst_pos.le (Real.rpow_nonneg hc.le _)
  exact h1.trans (mul_le_mul_of_nonneg_left h2 hpos)

/-! ## 5. Compactness of the planar interaction on `B0008.L2w m` and collective compactness -/

/-- The real-linear scaling equivalence `y ↦ (√a)⁻¹ • y` on `ℂ` for `a > 0`. -/
def scaleEquiv (a : ℝ) (ha : 0 < a) : ℂ ≃L[ℝ] ℂ :=
  Units.mk0 (Real.sqrt a)⁻¹ (inv_ne_zero (Real.sqrt_pos.2 ha).ne') •
    ContinuousLinearEquiv.refl ℝ ℂ

@[simp]
theorem scaleEquiv_apply (a : ℝ) (ha : 0 < a) (y : ℂ) :
    scaleEquiv a ha y = (Real.sqrt a)⁻¹ • y := rfl

theorem scaleEquiv_ofPlane (a : ℝ) (ha : 0 < a) (x : B0579.Plane) :
    scaleEquiv a ha (ofPlane x) = ofPlane (scalePlane a x) := by
  rw [scaleEquiv_apply]
  apply Complex.ext <;> (simp [ofPlane, scalePlane]; ring)

/-- The dilated Gaussian vorticity gradient `-(1+σ)^{-5/2} (∂_k E₀)(y / √(1+σ))` as a Schwartz
function in `𝓢(ℂ, ℂ)` for `1 + σ > 0`. -/
def gradScaleS (σ : ℝ) (hσ : 0 < 1 + σ) (k : Fin 2) : 𝓢(ℂ, ℂ) :=
  (-((1 + σ) ^ (-5 / 2 : ℝ) : ℝ) : ℂ) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (scaleEquiv (1 + σ) hσ) (B0061.gradS k)

theorem gradScaleS_zero_ofPlane (σ : ℝ) (hσ : 0 < 1 + σ) (x : B0579.Plane) :
    gradScaleS σ hσ 0 (ofPlane x) = -((planarGradE σ x).1 : ℂ) := by
  simp only [gradScaleS, smul_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    scaleEquiv_ofPlane, B0061.gradS_zero, planarGradE, smul_eq_mul]
  push_cast
  ring

theorem gradScaleS_one_ofPlane (σ : ℝ) (hσ : 0 < 1 + σ) (x : B0579.Plane) :
    gradScaleS σ hσ 1 (ofPlane x) = -((planarGradE σ x).2 : ℂ) := by
  simp only [gradScaleS, smul_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    scaleEquiv_ofPlane, B0061.gradS_one, planarGradE, smul_eq_mul]
  push_cast
  ring

theorem wcoeff_gradScaleS (m : ℝ) (σ : ℝ) (hσ : 0 < 1 + σ) (k : Fin 2) :
    B0061.WCoeff m (gradScaleS σ hσ k : ℂ → ℂ) :=
  B0061.WCoeff.of_schwartz m (gradScaleS σ hσ k)

/-- **The complex planar interaction `A_{pl,σ}` on `B0008.L2w m`** (`m > 1`, `1 + σ > 0`), built
from `B0061.mulK` with the Schwartz coefficients `gradScaleS σ hσ k`. -/
def planarInteractionCLM (m : ℝ) (hm : 1 < m) (σ : ℝ) (hσ : 0 < 1 + σ) :
    B0008.L2w m →L[ℂ] B0008.L2w m :=
  B0061.mulK m hm (wcoeff_gradScaleS m σ hσ 0) 0 +
    B0061.mulK m hm (wcoeff_gradScaleS m σ hσ 1) 1

/-- Almost-everywhere formula for `planarInteractionCLM`: multiplication of `B0009.biotSavart g k`
by the rescaled Gaussian gradient `gradScaleS σ hσ k`. -/
theorem coeFn_planarInteractionCLM {m : ℝ} (hm : 1 < m) {σ : ℝ} (hσ : 0 < 1 + σ)
    (g : B0008.L2w m) :
    (planarInteractionCLM m hm σ hσ g : ℂ → ℂ) =ᵐ[volume]
      fun y => gradScaleS σ hσ 0 y * B0009.biotSavart g 0 y +
        gradScaleS σ hσ 1 y * B0009.biotSavart g 1 y := by
  have hadd : (planarInteractionCLM m hm σ hσ g : ℂ → ℂ) =ᵐ[volume]
      (B0061.mulK m hm (wcoeff_gradScaleS m σ hσ 0) 0 g : ℂ → ℂ) +
        (B0061.mulK m hm (wcoeff_gradScaleS m σ hσ 1) 1 g : ℂ → ℂ) :=
    (B0008.volume_ac m).ae_le (Lp.coeFn_add _ _)
  filter_upwards [hadd,
    B0061.coeFn_mulK hm (wcoeff_gradScaleS m σ hσ 0) 0 g,
    B0061.coeFn_mulK hm (wcoeff_gradScaleS m σ hσ 1) 1 g] with y hy h0 h1
  rw [hy, Pi.add_apply, h0, h1]

/-- **Every planar interaction `planarInteractionCLM m hm σ hσ` is a compact operator on
`B0008.L2w m`** (SP 2133–2140), proved from `B0061.isCompactOperator_mulK`. -/
theorem isCompactOperator_planarInteractionCLM {m : ℝ} (hm : 1 < m) {σ : ℝ} (hσ : 0 < 1 + σ) :
    IsCompactOperator (planarInteractionCLM m hm σ hσ) :=
  (B0061.isCompactOperator_mulK hm (wcoeff_gradScaleS m σ hσ 0) 0).add
    (B0061.isCompactOperator_mulK hm (wcoeff_gradScaleS m σ hσ 1) 1)

section CollectiveCompact

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Norm continuity of an operator family `A : ℝ → E →L[ℝ] E` on `[0, Σ]` implies that the
image `A '' Icc 0 Sg` is compact in operator norm. -/
theorem isCompact_image_of_continuousOn {Sg : ℝ} {A : ℝ → E →L[ℝ] E}
    (hcont : ContinuousOn A (Icc 0 Sg)) :
    IsCompact (A '' Icc 0 Sg) :=
  isCompact_Icc.image_of_continuousOn hcont

/-- Norm continuity of `A : ℝ → E →L[ℝ] E` on `[0, Σ]` implies that `A '' Icc 0 Sg` is totally
bounded in operator norm. -/
theorem totallyBounded_image_of_continuousOn {Sg : ℝ} {A : ℝ → E →L[ℝ] E}
    (hcont : ContinuousOn A (Icc 0 Sg)) :
    TotallyBounded (A '' Icc 0 Sg) :=
  (isCompact_image_of_continuousOn hcont).totallyBounded

/-- **Collective compactness from norm continuity** (SP 2133–2140): if each `A σ` (`σ ∈ [0, Σ]`)
is a compact operator on `E` and `σ ↦ A σ` is norm continuous on `[0, Σ]`, then for every radius
`R`, the collective ball image `⋃ σ ∈ Icc 0 Sg, A σ '' closedBall 0 R` is totally bounded in `E`. -/
theorem totallyBounded_biUnion_ball_of_continuousOn {Sg : ℝ} {A : ℝ → E →L[ℝ] E}
    (hcont : ContinuousOn A (Icc 0 Sg)) (hcomp : ∀ σ ∈ Icc 0 Sg, IsCompactOperator (A σ))
    (R : ℝ) :
    TotallyBounded (⋃ σ ∈ Icc 0 Sg, A σ '' closedBall (0 : E) R) := by
  have h𝒦 : TotallyBounded (A '' Icc 0 Sg) := totallyBounded_image_of_continuousOn hcont
  rw [Metric.totallyBounded_iff]
  intro ε hε
  have hR' : 0 ≤ max R 0 := le_max_right _ _
  have hδ : 0 < ε / (2 * (max R 0 + 1)) := by positivity
  obtain ⟨t, htA, htfin, hcov⟩ := finite_approx_of_totallyBounded h𝒦 _ hδ
  have himg : ∀ K ∈ t, ∃ u : Set E, u.Finite ∧ K '' closedBall (0 : E) R ⊆ ⋃ y ∈ u, ball y (ε / 2) := by
    intro K hK
    rcases htA hK with ⟨σ, hσ, rfl⟩
    have hK' : IsCompactOperator (A σ : E →ₗ[ℝ] E) := hcomp σ hσ
    have htb : TotallyBounded (A σ '' closedBall (0 : E) R) :=
      (hK'.isCompact_closure_image_closedBall R).totallyBounded.subset subset_closure
    exact Metric.totallyBounded_iff.1 htb _ (half_pos hε)
  choose! u hufin hucov using himg
  refine ⟨⋃ K ∈ t, u K, htfin.biUnion fun K hK => hufin K hK, ?_⟩
  intro v hv
  obtain ⟨σ, hσ, x, hx, rfl⟩ : ∃ σ ∈ Icc 0 Sg, ∃ x ∈ closedBall (0 : E) R, A σ x = v := by
    simpa only [mem_iUnion, mem_image, exists_prop] using hv
  obtain ⟨K', hK't, hKK'⟩ := mem_iUnion₂.1 (hcov ⟨σ, hσ, rfl⟩)
  obtain ⟨y, hyu, hy⟩ := mem_iUnion₂.1 (hucov K' hK't ⟨x, hx, rfl⟩)
  refine mem_iUnion₂.2 ⟨y, mem_iUnion₂.2 ⟨K', hK't, hyu⟩, ?_⟩
  have hxR : ‖x‖ ≤ max R 0 := (mem_closedBall_zero_iff.1 hx).trans (le_max_left _ _)
  have hKK'' : ‖A σ - K'‖ < ε / (2 * (max R 0 + 1)) := by rwa [← dist_eq_norm]
  have h1 : dist (A σ x) (K' x) ≤ ε / (2 * (max R 0 + 1)) * max R 0 := by
    rw [dist_eq_norm, ← sub_apply]
    exact ((A σ - K').le_opNorm _).trans (mul_le_mul hKK''.le hxR (norm_nonneg _) hδ.le)
  have h2 : ε / (2 * (max R 0 + 1)) * max R 0 < ε / 2 := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  rw [mem_ball] at hy ⊢
  calc dist (A σ x) y ≤ dist (A σ x) (K' x) + dist (K' x) y := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt (h1.trans h2.le) hy
    _ = ε := add_halves ε

end CollectiveCompact

/-! ## 6. Target statements (`PartII-b:F1`) and leaf decomposition -/

/-- **`short-bg:interaction-cylinder`** (SP 2117–2132, eq. 2129): for `m > 8` and `Σ > 0`, there is
a constant `C_Σ > 0` such that for every parameter point `p` in the background regime with
`1 ≤ p.c`, every `δ ≥ 0` with `TrainCloseM m p.train Sg δ`, and every slow age `σ ∈ [0, Σ]`, the
cylinder interaction `A_c(σ/ν)` on `X_{m,c} = B0579.X p.c m` and the planar interaction `A_{pl,σ}`
on `X_m` exist as bounded operators and satisfy
`‖J_c A_c(σ/ν) R_c - A_{pl,σ}‖_{X_m → X_m} ≤ C_Σ (c^{-2} + δ)`. -/
def InteractionCylinderComparison : Prop :=
  ∀ m : ℝ, 8 < m → ∀ Sg : ℝ, 0 < Sg → ∃ C_Sg : ℝ, 0 < C_Sg ∧
    ∀ (p : Params) (d dm dp : ℝ), BgRegime p d dm dp → 1 ≤ p.c →
    ∀ δ : ℝ, 0 ≤ δ → TrainCloseM m p.train Sg δ →
    ∀ σ : ℝ, σ ∈ Icc 0 Sg →
      (∃ (Ac : Xmc p.c m →L[ℝ] Xmc p.c m) (Apl_σ : Xm m →L[ℝ] Xm m),
        IsCylInteractionOp p.train m (σ / p.ν) Ac ∧
        IsPlanarInteractionOp m σ Apl_σ) ∧
      ∀ (Ac : Xmc p.c m →L[ℝ] Xmc p.c m) (Apl_σ : Xm m →L[ℝ] Xm m),
        IsCylInteractionOp p.train m (σ / p.ν) Ac →
        IsPlanarInteractionOp m σ Apl_σ →
          ‖(Jc p.c m).comp (Ac.comp (Rc p.c m)) - Apl_σ‖ ≤ C_Sg * (p.c ^ (-2 : ℝ) + δ)

/-- **Compactness and collective compactness of the cylinder and planar interactions**
(SP 2133–2140): for `m > 8` and `Σ > 0`:
1. at every parameter point `p` in the background regime with `1 ≤ p.c`, every `δ ≥ 0` with
   `TrainCloseM m p.train Sg δ`, and every age `s ∈ [0, Σ/ν]`, the cylinder interaction `A_c(s)`
   exists on `X_{m,c}`, is compact (`IsCompactOperator`), and its zero extension `J_c A_c(s) R_c` is
   compact on `X_m`;
2. there is a norm-continuous family `σ ↦ A_{pl,σ}` on `[0, Σ]` realizing `IsPlanarInteractionOp`
   such that every `A_{pl,σ}` (`σ ∈ [0, Σ]`) is compact on `X_m`, the operator family
   `{A_{pl,σ} : 0 ≤ σ ≤ Σ}` is totally bounded in operator norm, and for every radius `R` the
   collective ball image `⋃_{0 ≤ σ ≤ Σ} A_{pl,σ}(B_R)` is totally bounded in `X_m`. -/
def InteractionCollectiveCompact : Prop :=
  ∀ m : ℝ, 8 < m → ∀ Sg : ℝ, 0 < Sg →
    (∀ (p : Params) (d dm dp : ℝ), BgRegime p d dm dp → 1 ≤ p.c →
      ∀ δ : ℝ, 0 ≤ δ → TrainCloseM m p.train Sg δ →
      ∀ s : ℝ, s ∈ Icc 0 (Sg / p.ν) →
      (∃ Ac : Xmc p.c m →L[ℝ] Xmc p.c m, IsCylInteractionOp p.train m s Ac) ∧
      ∀ Ac : Xmc p.c m →L[ℝ] Xmc p.c m, IsCylInteractionOp p.train m s Ac →
        IsCompactOperator Ac ∧ IsCompactOperator ((Jc p.c m).comp (Ac.comp (Rc p.c m)))) ∧
    ∃ AplOp : ℝ → (Xm m →L[ℝ] Xm m),
      ContinuousOn AplOp (Icc 0 Sg) ∧
      (∀ σ ∈ Icc 0 Sg, IsPlanarInteractionOp m σ (AplOp σ) ∧ IsCompactOperator (AplOp σ)) ∧
      TotallyBounded (AplOp '' Icc 0 Sg) ∧
      ∀ R : ℝ, TotallyBounded (⋃ σ ∈ Icc 0 Sg, AplOp σ '' closedBall (0 : Xm m) R)

/-! ### Decomposition leaves (`PartII-b:F1/1` .. `PartII-b:F1/4`) and assembly theorems -/

/-- **Leaf 1 (`PartII-b:F1/1`, cylinder weighted Biot–Savart operator bound and compactness,
SP 2117–2118, 2133–2137)**: for `m > 8`, there is a constant `C_K > 0` such that for every period
`c ≥ 1`, every `B ≥ 0`, and every continuous vector coefficient `b : B0579.Plane → B0579.Plane`
satisfying `IsCylWeightedCoeff c m B b` (`(|(b x).1| + |(b x).2|) ⟨x⟩^{m+2} ≤ B` on `cell c`),
the cylinder multiplication-convolution operator `w ↦ -(K_c w)·b` exists as a bounded compact
operator `T` on `X_{m,c}` with `‖T‖ ≤ C_K * B`. -/
def CylWeightedKernelStep : Prop :=
  ∀ m : ℝ, 8 < m → ∃ C_K : ℝ, 0 < C_K ∧
    ∀ c : ℝ, 1 ≤ c → ∀ B : ℝ, 0 ≤ B → ∀ b : B0579.Plane → B0579.Plane,
      IsCylWeightedCoeff c m B b →
      ∃ T : Xmc c m →L[ℝ] Xmc c m,
        IsCylWeightedOp c m b T ∧
        IsCompactOperator T ∧
        ‖T‖ ≤ C_K * B

/-- **Leaf 2 (`PartII-b:F1/2`, weighted coefficient bounds for `∇E_{1+σ}` and
`∇E_c(σ/ν) - ∇E_{1+σ}` on the cylinder cell, SP 2085–2090, 2120–2127)**: for `m > 8` and `Σ > 0`,
there is `C_tr > 0` such that for every parameter point `p` in the background regime with `1 ≤ p.c`,
every `δ ≥ 0` with `TrainCloseM m p.train Sg δ`, and every slow age `σ ∈ [0, Σ]`, the Gaussian
gradient `planarGradE σ` satisfies `IsCylWeightedCoeff p.c m C_tr (planarGradE σ)` and the
coefficient difference `∇E_c(σ/ν) - ∇E_{1+σ}` satisfies
`IsCylWeightedCoeff p.c m (C_tr * (p.c ^ (-2 : ℝ) + δ)) (trainGradE p.train (σ / p.ν) - planarGradE σ)`. -/
def TrainGradCoeffStep : Prop :=
  ∀ m : ℝ, 8 < m → ∀ Sg : ℝ, 0 < Sg → ∃ C_tr : ℝ, 0 < C_tr ∧
    ∀ (p : Params) (d dm dp : ℝ), BgRegime p d dm dp → 1 ≤ p.c →
    ∀ δ : ℝ, 0 ≤ δ → TrainCloseM m p.train Sg δ →
    ∀ σ : ℝ, σ ∈ Icc 0 Sg →
      IsCylWeightedCoeff p.c m C_tr (planarGradE σ) ∧
      IsCylWeightedCoeff p.c m (C_tr * (p.c ^ (-2 : ℝ) + δ))
        (fun x => trainGradE p.train (σ / p.ν) x - planarGradE σ x)

/-- **Leaf 3 (`PartII-b:F1/3`, existence, compactness, and norm continuity of the real planar
interaction family `σ ↦ A_{pl,σ}` on `X_m`, SP 2133–2140)**: for `m > 8` and `Σ > 0`, there is a
norm-continuous operator family `AplOp : ℝ → (Xm m →L[ℝ] Xm m)` on `[0, Σ]` such that for every
`σ ∈ [0, Σ]`, `AplOp σ` realizes `IsPlanarInteractionOp m σ` and is a compact operator on `X_m`. -/
def PlanarInteractionCompactStep : Prop :=
  ∀ m : ℝ, 8 < m → ∀ Sg : ℝ, 0 < Sg →
    ∃ AplOp : ℝ → (Xm m →L[ℝ] Xm m),
      ContinuousOn AplOp (Icc 0 Sg) ∧
      ∀ σ ∈ Icc 0 Sg, IsPlanarInteractionOp m σ (AplOp σ) ∧ IsCompactOperator (AplOp σ)

/-- **Leaf 4 (`PartII-b:F1/4`, cylinder vs planar kernel comparison with Gaussian coefficient
`∇E_{1+σ}`, SP 2117–2131)**: for `m > 8` and `Σ > 0`, there is `C₂ > 0` such that for every `c ≥ 1`
and `σ ∈ [0, Σ]`, if `AcG` realizes `IsGaussCylInteractionOp c m σ` on `X_{m,c}` and `Apl_σ`
realizes `IsPlanarInteractionOp m σ` on `X_m`, then
`‖J_c AcG R_c - Apl_σ‖_{X_m → X_m} ≤ C₂ c^{-2}`. -/
def PlanarKernelBoundStep : Prop :=
  ∀ m : ℝ, 8 < m → ∀ Sg : ℝ, 0 < Sg → ∃ C₂ : ℝ, 0 < C₂ ∧
    ∀ c : ℝ, 1 ≤ c → ∀ σ : ℝ, σ ∈ Icc 0 Sg →
    ∀ (AcG : Xmc c m →L[ℝ] Xmc c m) (Apl_σ : Xm m →L[ℝ] Xm m),
      IsGaussCylInteractionOp c m σ AcG →
      IsPlanarInteractionOp m σ Apl_σ →
        ‖(Jc c m).comp (AcG.comp (Rc c m)) - Apl_σ‖ ≤ C₂ * c ^ (-2 : ℝ)

/-- **Assembly of `InteractionCylinderComparison`** from `CylWeightedKernelStep` (`PartII-b:F1/1`),
`TrainGradCoeffStep` (`PartII-b:F1/2`), `PlanarInteractionCompactStep` (`PartII-b:F1/3`), and
`PlanarKernelBoundStep` (`PartII-b:F1/4`). -/
theorem interactionCylinderComparison_of
    (hK : CylWeightedKernelStep)
    (hTr : TrainGradCoeffStep)
    (hPlC : PlanarInteractionCompactStep)
    (hPlB : PlanarKernelBoundStep) :
    InteractionCylinderComparison := by
  intro m hm Sg hSg
  obtain ⟨C_K, hC_K, hK_op⟩ := hK m hm
  obtain ⟨C_tr, hC_tr, hTr_bd⟩ := hTr m hm Sg hSg
  obtain ⟨AplOp, _, hAplOp⟩ := hPlC m hm Sg hSg
  obtain ⟨C₂, hC₂, hPl_bd⟩ := hPlB m hm Sg hSg
  refine ⟨C_K * C_tr + C₂, by positivity, ?_⟩
  intro p d dm dp hbg hc1 δ hδ hclose σ hσ
  have hc0 : 0 < p.c := by linarith
  obtain ⟨hCoeffG, hCoeffDiff⟩ := hTr_bd p d dm dp hbg hc1 δ hδ hclose σ hσ
  have hB_diff_nn : 0 ≤ C_tr * (p.c ^ (-2 : ℝ) + δ) :=
    mul_nonneg hC_tr.le (add_nonneg (Real.rpow_nonneg hc0.le _) hδ)
  obtain ⟨AcG, hAcG_w, _, _⟩ := hK_op p.c hc1 C_tr hC_tr.le (planarGradE σ) hCoeffG
  obtain ⟨Adiff, hAdiff_w, _, hAdiff_norm⟩ :=
    hK_op p.c hc1 (C_tr * (p.c ^ (-2 : ℝ) + δ)) hB_diff_nn
      (fun x => trainGradE p.train (σ / p.ν) x - planarGradE σ x) hCoeffDiff
  set Ac₀ : Xmc p.c m →L[ℝ] Xmc p.c m := Adiff + AcG
  have hAc₀_w : IsCylWeightedOp p.c m (trainGradE p.train (σ / p.ν)) Ac₀ := by
    have hsum := hAdiff_w.add hAcG_w
    have hfun : (fun x => (trainGradE p.train (σ / p.ν) x - planarGradE σ x) + planarGradE σ x) =
        trainGradE p.train (σ / p.ν) := by
      funext x
      exact sub_add_cancel _ _
    rwa [hfun] at hsum
  have hAc₀ : IsCylInteractionOp p.train m (σ / p.ν) Ac₀ := hAc₀_w
  have hAcG : IsGaussCylInteractionOp p.c m σ AcG := hAcG_w
  have hApl₀ : IsPlanarInteractionOp m σ (AplOp σ) := (hAplOp σ hσ).1
  refine ⟨⟨Ac₀, AplOp σ, hAc₀, hApl₀⟩, ?_⟩
  intro Ac Apl_σ hAc hApl
  rw [hAc.unique hAc₀, hApl.unique hApl₀]
  have hsub_eq : Ac₀ - AcG = Adiff := add_sub_cancel_right Adiff AcG
  have hExt_sub :
      ‖(Jc p.c m).comp (Ac₀.comp (Rc p.c m)) - (Jc p.c m).comp (AcG.comp (Rc p.c m))‖ ≤
        C_K * (C_tr * (p.c ^ (-2 : ℝ) + δ)) := by
    calc ‖(Jc p.c m).comp (Ac₀.comp (Rc p.c m)) - (Jc p.c m).comp (AcG.comp (Rc p.c m))‖
        ≤ ‖Ac₀ - AcG‖ := norm_Jc_comp_Rc_sub_le p.c m Ac₀ AcG
      _ = ‖Adiff‖ := by rw [hsub_eq]
      _ ≤ C_K * (C_tr * (p.c ^ (-2 : ℝ) + δ)) := hAdiff_norm
  have hbd₂ : ‖(Jc p.c m).comp (AcG.comp (Rc p.c m)) - AplOp σ‖ ≤ C₂ * p.c ^ (-2 : ℝ) :=
    hPl_bd p.c hc1 σ hσ AcG (AplOp σ) hAcG hApl₀
  have htri :
      ‖(Jc p.c m).comp (Ac₀.comp (Rc p.c m)) - AplOp σ‖ ≤
        ‖(Jc p.c m).comp (Ac₀.comp (Rc p.c m)) - (Jc p.c m).comp (AcG.comp (Rc p.c m))‖ +
          ‖(Jc p.c m).comp (AcG.comp (Rc p.c m)) - AplOp σ‖ :=
    norm_sub_le_norm_sub_add_norm_sub _ _ _
  calc ‖(Jc p.c m).comp (Ac₀.comp (Rc p.c m)) - AplOp σ‖
      ≤ C_K * (C_tr * (p.c ^ (-2 : ℝ) + δ)) + C₂ * p.c ^ (-2 : ℝ) :=
        htri.trans (add_le_add hExt_sub hbd₂)
    _ ≤ (C_K * C_tr + C₂) * (p.c ^ (-2 : ℝ) + δ) := by nlinarith

/-- **Assembly of `InteractionCollectiveCompact`** from `CylWeightedKernelStep` (`PartII-b:F1/1`),
`TrainGradCoeffStep` (`PartII-b:F1/2`), and `PlanarInteractionCompactStep` (`PartII-b:F1/3`). -/
theorem interactionCollectiveCompact_of
    (hK : CylWeightedKernelStep)
    (hTr : TrainGradCoeffStep)
    (hPlC : PlanarInteractionCompactStep) :
    InteractionCollectiveCompact := by
  intro m hm Sg hSg
  obtain ⟨C_K, hC_K, hK_op⟩ := hK m hm
  obtain ⟨C_tr, hC_tr, hTr_bd⟩ := hTr m hm Sg hSg
  obtain ⟨AplOp, hcont, hPl⟩ := hPlC m hm Sg hSg
  refine ⟨?_, AplOp, hcont, hPl, totallyBounded_image_of_continuousOn hcont,
    totallyBounded_biUnion_ball_of_continuousOn hcont (fun σ hσ => (hPl σ hσ).2)⟩
  intro p d dm dp hbg hc1 δ hδ hclose s hs
  have hν : 0 < p.ν := p.ν_pos
  have hc0 : 0 < p.c := by linarith
  set σ : ℝ := s * p.ν
  have hσ : σ ∈ Icc 0 Sg := by
    refine ⟨mul_nonneg hs.1 hν.le, ?_⟩
    calc s * p.ν ≤ Sg / p.ν * p.ν := mul_le_mul_of_nonneg_right hs.2 hν.le
      _ = Sg := div_mul_cancel₀ Sg hν.ne'
  have hs_eq : σ / p.ν = s := mul_div_cancel_right₀ s hν.ne'
  obtain ⟨hCoeffG, hCoeffDiff⟩ := hTr_bd p d dm dp hbg hc1 δ hδ hclose σ hσ
  have hCoeffTr :
      IsCylWeightedCoeff p.c m (C_tr * (p.c ^ (-2 : ℝ) + δ) + C_tr) (trainGradE p.train s) := by
    have hsum := hCoeffDiff.add hCoeffG
    have hfun : (fun x => (trainGradE p.train (σ / p.ν) x - planarGradE σ x) + planarGradE σ x) =
        trainGradE p.train s := by
      funext x
      rw [hs_eq, sub_add_cancel]
    rwa [hfun] at hsum
  have hB_nn : 0 ≤ C_tr * (p.c ^ (-2 : ℝ) + δ) + C_tr :=
    add_nonneg (mul_nonneg hC_tr.le (add_nonneg (Real.rpow_nonneg hc0.le _) hδ)) hC_tr.le
  obtain ⟨Ac₀, hAc₀_w, hcomp₀, _⟩ :=
    hK_op p.c hc1 (C_tr * (p.c ^ (-2 : ℝ) + δ) + C_tr) hB_nn (trainGradE p.train s) hCoeffTr
  have hAc₀ : IsCylInteractionOp p.train m s Ac₀ := hAc₀_w
  refine ⟨⟨Ac₀, hAc₀⟩, fun Ac hAc => ?_⟩
  rw [hAc.unique hAc₀]
  exact ⟨hcomp₀, isCompactOperator_Jc_comp_Rc hcomp₀⟩

/-- **Combined assembly of `InteractionCylinderComparison ∧ InteractionCollectiveCompact`** from
the four leaves `PartII-b:F1/1` .. `PartII-b:F1/4`. -/
theorem interactionCylinder_of
    (hK : CylWeightedKernelStep)
    (hTr : TrainGradCoeffStep)
    (hPlC : PlanarInteractionCompactStep)
    (hPlB : PlanarKernelBoundStep) :
    InteractionCylinderComparison ∧ InteractionCollectiveCompact :=
  ⟨interactionCylinderComparison_of hK hTr hPlC hPlB,
   interactionCollectiveCompact_of hK hTr hPlC⟩

end UnforcedLeray.Short.IIb

end
