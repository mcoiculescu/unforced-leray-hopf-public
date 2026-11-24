import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2_3_1
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1
import UnforcedLeray.Lib.PlanarSectorsB.DilationPlane
import Mathlib.Topology.Algebra.Order.Floor

/-!
# `PartII-b:F2/3/1/1` (`Bridge.lean`): Real/complex `L²` bridge `Xm m ↔ Planar.L2w m` and Gronwall

Provides:
* `toL2w m : Xm m →ₗᵢ[ℝ] Planar.L2w m` (`f ↦ (f ∘ cToPlane : ℝ → ℂ)`),
* `reXm m, imXm m : Planar.L2w m →L[ℝ] Xm m` (`W ↦ Re/Im (W ∘ planeToC)`),
* `realify` and `PreservesReal` for operators on `Planar.L2w m`,
* `continuousOn_strong_apply` for strongly continuous uniformly bounded operator families,
* `gronwall_zero_Icc` (forward integral Gronwall to zero on `[0, T]`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.IIb.PlanarEulerBridge

open UnforcedLeray.Short.IIIa (cToPlane planeToC cToPlane_planeToC planeToC_cToPlane)
open UnforcedLeray.Short.IIIa.BlockPropagatorSub

/-! ## 1. Measure-preserving bridge `Xm m ↔ Planar.L2w m` -/

theorem planeToC_eq_ofPlane (x : B0579.Plane) : planeToC x = ofPlane x := by
  apply Complex.ext <;> simp [planeToC, ofPlane]

theorem cToPlane_ofPlane (x : B0579.Plane) : cToPlane (ofPlane x) = x := by
  rw [← planeToC_eq_ofPlane, cToPlane_planeToC]

theorem ofPlane_cToPlane (z : ℂ) : ofPlane (cToPlane z) = z := by
  rw [← planeToC_eq_ofPlane, planeToC_cToPlane]

theorem measurePreserving_cToPlane (m : ℝ) :
    MeasurePreserving cToPlane (Planar.wMeasure m) (planeMeasure m) :=
  measurePreserving_cToPlane_wMeasure m

theorem measurePreserving_planeToC (m : ℝ) :
    MeasurePreserving planeToC (planeMeasure m) (Planar.wMeasure m) :=
  measurePreserving_planeToC_wMeasure m

/-- Real-linear isometric embedding `Xm m →ₗᵢ[ℝ] Planar.L2w m`, `f ↦ (x ↦ (f (cToPlane x) : ℂ))`. -/
def toL2w (m : ℝ) : Xm m →ₗᵢ[ℝ] Planar.L2w m :=
  LinearIsometry.comp
    { toLinearMap := Complex.ofRealCLM.compLpₗ 2 (Planar.wMeasure m)
      norm_map' := fun g => by
        rw [Lp.norm_def, Lp.norm_def]
        congr 1
        rw [ContinuousLinearMap.compLpₗ_apply,
          eLpNorm_congr_ae (Complex.ofRealCLM.coeFn_compLp' g)]
        exact eLpNorm_congr_norm_ae (Eventually.of_forall fun z => Complex.norm_real (g z)) }
    (Lp.compMeasurePreservingₗᵢ ℝ cToPlane (measurePreserving_cToPlane m))

theorem coeFn_toL2w (m : ℝ) (f : Xm m) :
    (toL2w m f : ℂ → ℂ) =ᵐ[Planar.wMeasure m] fun z => ((f (cToPlane z) : ℝ) : ℂ) := by
  let g : Lp ℝ 2 (Planar.wMeasure m) :=
    Lp.compMeasurePreservingₗᵢ ℝ cToPlane (measurePreserving_cToPlane m) f
  have h1 : (toL2w m f : ℂ → ℂ) =ᵐ[Planar.wMeasure m] fun z => Complex.ofRealCLM (g z) :=
    Complex.ofRealCLM.coeFn_compLp' g
  have h2 : (g : ℂ → ℝ) =ᵐ[Planar.wMeasure m] fun z => f (cToPlane z) :=
    Lp.coeFn_compMeasurePreserving f (measurePreserving_cToPlane m)
  filter_upwards [h1, h2] with z hz1 hz2
  simpa only [Complex.ofRealCLM_apply, hz2] using hz1

/-- Real part map `Planar.L2w m →L[ℝ] Xm m`, `W ↦ (x ↦ (W (planeToC x)).re)`. -/
def reXm (m : ℝ) : Planar.L2w m →L[ℝ] Xm m :=
  ((Lp.compMeasurePreservingₗᵢ ℝ planeToC
      (measurePreserving_planeToC m)).toContinuousLinearMap).comp
    (Complex.reCLM.compLpL 2 (Planar.wMeasure m))

/-- Imaginary part map `Planar.L2w m →L[ℝ] Xm m`, `W ↦ (x ↦ (W (planeToC x)).im)`. -/
def imXm (m : ℝ) : Planar.L2w m →L[ℝ] Xm m :=
  ((Lp.compMeasurePreservingₗᵢ ℝ planeToC
      (measurePreserving_planeToC m)).toContinuousLinearMap).comp
    (Complex.imCLM.compLpL 2 (Planar.wMeasure m))

theorem coeFn_reXm (m : ℝ) (W : Planar.L2w m) :
    (reXm m W : B0579.Plane → ℝ) =ᵐ[planeMeasure m] fun x => (W (planeToC x)).re := by
  let g : Lp ℝ 2 (Planar.wMeasure m) := Complex.reCLM.compLpL 2 (Planar.wMeasure m) W
  have h1 : (reXm m W : B0579.Plane → ℝ) =ᵐ[planeMeasure m] fun x => g (planeToC x) :=
    Lp.coeFn_compMeasurePreserving g (measurePreserving_planeToC m)
  have h2 : (g : ℂ → ℝ) =ᵐ[Planar.wMeasure m] fun z => (W z).re :=
    Complex.reCLM.coeFn_compLp' W
  filter_upwards [h1, (measurePreserving_planeToC m).quasiMeasurePreserving.ae_eq_comp h2]
    with x hx1 hx2
  exact hx1.trans hx2

theorem coeFn_imXm (m : ℝ) (W : Planar.L2w m) :
    (imXm m W : B0579.Plane → ℝ) =ᵐ[planeMeasure m] fun x => (W (planeToC x)).im := by
  let g : Lp ℝ 2 (Planar.wMeasure m) := Complex.imCLM.compLpL 2 (Planar.wMeasure m) W
  have h1 : (imXm m W : B0579.Plane → ℝ) =ᵐ[planeMeasure m] fun x => g (planeToC x) :=
    Lp.coeFn_compMeasurePreserving g (measurePreserving_planeToC m)
  have h2 : (g : ℂ → ℝ) =ᵐ[Planar.wMeasure m] fun z => (W z).im :=
    Complex.imCLM.coeFn_compLp' W
  filter_upwards [h1, (measurePreserving_planeToC m).quasiMeasurePreserving.ae_eq_comp h2]
    with x hx1 hx2
  exact hx1.trans hx2

theorem norm_reXm_apply_le (m : ℝ) (W : Planar.L2w m) : ‖reXm m W‖ ≤ ‖W‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (coeFn_reXm m W)]
  have hmp := measurePreserving_planeToC m
  have hmeas : AEStronglyMeasurable (fun z : ℂ => (W z).re) (Planar.wMeasure m) :=
    Complex.continuous_re.comp_aestronglyMeasurable (Lp.aestronglyMeasurable W)
  have heq : eLpNorm (fun x => (W (planeToC x)).re) 2 (planeMeasure m) =
      eLpNorm (fun z => (W z).re) 2 (Planar.wMeasure m) :=
    eLpNorm_comp_measurePreserving hmeas hmp
  rw [heq]
  refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top W) (eLpNorm_mono_ae ?_)
  exact Eventually.of_forall fun z => Complex.abs_re_le_norm (W z)

theorem norm_reXm_le (m : ℝ) : ‖reXm m‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun W => by
    simpa only [one_mul] using norm_reXm_apply_le m W

@[simp]
theorem reXm_toL2w (m : ℝ) (f : Xm m) : reXm m (toL2w m f) = f := by
  apply Lp.ext
  have h1 := coeFn_reXm m (toL2w m f)
  have h2 := (measurePreserving_planeToC m).quasiMeasurePreserving.ae_eq_comp (coeFn_toL2w m f)
  filter_upwards [h1, h2] with x hx1 hx2
  rw [hx1]
  have hx2' : (toL2w m f : ℂ → ℂ) (planeToC x) = ((f (cToPlane (planeToC x)) : ℝ) : ℂ) := hx2
  rw [hx2', cToPlane_planeToC, Complex.ofReal_re]

@[simp]
theorem imXm_toL2w (m : ℝ) (f : Xm m) : imXm m (toL2w m f) = 0 := by
  apply Lp.ext
  have h1 := coeFn_imXm m (toL2w m f)
  have h2 := (measurePreserving_planeToC m).quasiMeasurePreserving.ae_eq_comp (coeFn_toL2w m f)
  filter_upwards [h1, h2, Lp.coeFn_zero ℝ 2 (planeMeasure m)] with x hx1 hx2 hz
  rw [hx1, hz]
  have hx2' : (toL2w m f : ℂ → ℂ) (planeToC x) = ((f (cToPlane (planeToC x)) : ℝ) : ℂ) := hx2
  rw [hx2', Complex.ofReal_im]
  rfl

theorem imXm_I_smul_toL2w (m : ℝ) (f : Xm m) : imXm m (Complex.I • toL2w m f) = f := by
  apply Lp.ext
  have hsmul : ((Complex.I • toL2w m f : Planar.L2w m) : ℂ → ℂ) =ᵐ[Planar.wMeasure m]
      fun z => Complex.I * ((f (cToPlane z) : ℝ) : ℂ) := by
    filter_upwards [Lp.coeFn_smul Complex.I (toL2w m f), coeFn_toL2w m f] with z h1 h2
    rw [h1, Pi.smul_apply, smul_eq_mul, h2]
  filter_upwards [coeFn_imXm m (Complex.I • toL2w m f),
    (measurePreserving_planeToC m).quasiMeasurePreserving.ae_eq_comp hsmul] with x hx1 hx2
  rw [hx1]
  have hx2' : ((Complex.I • toL2w m f : Planar.L2w m) : ℂ → ℂ) (planeToC x) =
      Complex.I * ((f (cToPlane (planeToC x)) : ℝ) : ℂ) := hx2
  rw [hx2', cToPlane_planeToC]
  simp

theorem reXm_I_smul_toL2w (m : ℝ) (f : Xm m) : reXm m (Complex.I • toL2w m f) = 0 := by
  apply Lp.ext
  have hsmul : ((Complex.I • toL2w m f : Planar.L2w m) : ℂ → ℂ) =ᵐ[Planar.wMeasure m]
      fun z => Complex.I * ((f (cToPlane z) : ℝ) : ℂ) := by
    filter_upwards [Lp.coeFn_smul Complex.I (toL2w m f), coeFn_toL2w m f] with z h1 h2
    rw [h1, Pi.smul_apply, smul_eq_mul, h2]
  filter_upwards [coeFn_reXm m (Complex.I • toL2w m f),
    (measurePreserving_planeToC m).quasiMeasurePreserving.ae_eq_comp hsmul,
    Lp.coeFn_zero ℝ 2 (planeMeasure m)] with x hx1 hx2 hz
  rw [hx1, hz]
  have hx2' : ((Complex.I • toL2w m f : Planar.L2w m) : ℂ → ℂ) (planeToC x) =
      Complex.I * ((f (cToPlane (planeToC x)) : ℝ) : ℂ) := hx2
  rw [hx2']
  simp

theorem toL2w_re_add_I_im (m : ℝ) (W : Planar.L2w m) :
    toL2w m (reXm m W) + Complex.I • toL2w m (imXm m W) = W := by
  apply Lp.ext
  have hre := (measurePreserving_cToPlane m).quasiMeasurePreserving.ae_eq_comp (coeFn_reXm m W)
  have him := (measurePreserving_cToPlane m).quasiMeasurePreserving.ae_eq_comp (coeFn_imXm m W)
  filter_upwards [Lp.coeFn_add (toL2w m (reXm m W)) (Complex.I • toL2w m (imXm m W)),
    coeFn_toL2w m (reXm m W), Lp.coeFn_smul Complex.I (toL2w m (imXm m W)),
    coeFn_toL2w m (imXm m W), hre, him] with z hadd h1 hsmul h2 h3 h4
  rw [hadd, Pi.add_apply, h1, hsmul, Pi.smul_apply, smul_eq_mul, h2]
  have h3' : (reXm m W : B0579.Plane → ℝ) (cToPlane z) = (W (planeToC (cToPlane z))).re := h3
  have h4' : (imXm m W : B0579.Plane → ℝ) (cToPlane z) = (W (planeToC (cToPlane z))).im := h4
  rw [h3', h4', planeToC_cToPlane, mul_comm Complex.I, Complex.re_add_im]

/-! ## 2. `realify` and `PreservesReal` -/

/-- Real part restriction of a complex-linear operator on `Planar.L2w m` to `Xm m`. -/
def realify {m : ℝ} (S : Planar.L2w m →L[ℂ] Planar.L2w m) : Xm m →L[ℝ] Xm m :=
  (reXm m).comp ((S.restrictScalars ℝ).comp (toL2w m).toContinuousLinearMap)

theorem realify_apply {m : ℝ} (S : Planar.L2w m →L[ℂ] Planar.L2w m) (f : Xm m) :
    realify S f = reXm m (S (toL2w m f)) := rfl

theorem norm_realify_le {m : ℝ} (S : Planar.L2w m →L[ℂ] Planar.L2w m) :
    ‖realify S‖ ≤ ‖S‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg S) fun f => ?_
  calc ‖reXm m (S (toL2w m f))‖
      ≤ ‖S (toL2w m f)‖ := norm_reXm_apply_le m _
    _ ≤ ‖S‖ * ‖toL2w m f‖ := S.le_opNorm _
    _ = ‖S‖ * ‖f‖ := by rw [(toL2w m).norm_map]

/-- An operator `S` on `Planar.L2w m` preserves real functions (`toL2w m (Xm m)`). -/
def PreservesReal {m : ℝ} (S : Planar.L2w m →L[ℂ] Planar.L2w m) : Prop :=
  ∀ f : Xm m, imXm m (S (toL2w m f)) = 0

theorem PreservesReal.toL2w_realify {m : ℝ} {S : Planar.L2w m →L[ℂ] Planar.L2w m}
    (hS : PreservesReal S) (f : Xm m) :
    toL2w m (realify S f) = S (toL2w m f) := by
  have h := toL2w_re_add_I_im m (S (toL2w m f))
  rw [hS f, map_zero, smul_zero, add_zero] at h
  exact h

theorem PreservesReal.reXm_apply {m : ℝ} {S : Planar.L2w m →L[ℂ] Planar.L2w m}
    (hS : PreservesReal S) (W : Planar.L2w m) :
    reXm m (S W) = realify S (reXm m W) := by
  conv_lhs => rw [← toL2w_re_add_I_im m W]
  rw [map_add, map_smul, ← hS.toL2w_realify (reXm m W), ← hS.toL2w_realify (imXm m W),
    map_add, reXm_toL2w, reXm_I_smul_toL2w, add_zero]

theorem PreservesReal.imXm_apply {m : ℝ} {S : Planar.L2w m →L[ℂ] Planar.L2w m}
    (hS : PreservesReal S) (W : Planar.L2w m) :
    imXm m (S W) = realify S (imXm m W) := by
  conv_lhs => rw [← toL2w_re_add_I_im m W]
  rw [map_add, map_smul, ← hS.toL2w_realify (reXm m W), ← hS.toL2w_realify (imXm m W),
    map_add, imXm_toL2w, imXm_I_smul_toL2w, zero_add]

theorem PreservesReal.one (m : ℝ) : PreservesReal (1 : Planar.L2w m →L[ℂ] Planar.L2w m) :=
  fun f => imXm_toL2w m f

theorem realify_one (m : ℝ) :
    realify (1 : Planar.L2w m →L[ℂ] Planar.L2w m) = ContinuousLinearMap.id ℝ (Xm m) := by
  ext1 f
  exact reXm_toL2w m f

theorem PreservesReal.comp {m : ℝ} {S₁ S₂ : Planar.L2w m →L[ℂ] Planar.L2w m}
    (h₁ : PreservesReal S₁) (h₂ : PreservesReal S₂) :
    PreservesReal (S₁ ∘L S₂) := by
  intro f
  rw [ContinuousLinearMap.comp_apply, ← h₂.toL2w_realify f]
  exact h₁ (realify S₂ f)

theorem PreservesReal.realify_comp {m : ℝ} {S₁ S₂ : Planar.L2w m →L[ℂ] Planar.L2w m}
    (_h₁ : PreservesReal S₁) (h₂ : PreservesReal S₂) :
    realify (S₁ ∘L S₂) = (realify S₁).comp (realify S₂) := by
  ext1 f
  rw [ContinuousLinearMap.comp_apply, realify_apply, realify_apply,
    ContinuousLinearMap.comp_apply, ← h₂.toL2w_realify f]

theorem PreservesReal.smul_real {m : ℝ} {S : Planar.L2w m →L[ℂ] Planar.L2w m}
    (hS : PreservesReal S) (c : ℝ) :
    PreservesReal ((c : ℂ) • S) := by
  intro f
  have h : ((c : ℂ) • S) (toL2w m f) = S (toL2w m (c • f)) := by
    change (c : ℂ) • S (toL2w m f) = (S.restrictScalars ℝ) (toL2w m (c • f))
    rw [(toL2w m).map_smul, map_smul, Complex.coe_smul]
    rfl
  rw [h]
  exact hS (c • f)

theorem preservesReal_dilW {m : ℝ} (hm : 1 < m) {a : ℝ} (ha : 0 < a) :
    PreservesReal (Planar.dilW hm ha) := by
  intro f
  apply Lp.ext
  have h1 := coeFn_imXm m (Planar.dilW hm ha (toL2w m f))
  have h2 := Planar.coeFn_dilW hm ha (toL2w m f)
  have h3 := (Planar.qmp_smul_wMeasure (M := m) (Planar.sqrt_inv_ne_zero ha)).ae_eq_comp
    (coeFn_toL2w m f)
  have hdil : (Planar.dilW hm ha (toL2w m f) : ℂ → ℂ) =ᵐ[Planar.wMeasure m]
      fun z => (((a ^ 2)⁻¹ * f (cToPlane ((Real.sqrt a)⁻¹ • z)) : ℝ) : ℂ) := by
    filter_upwards [h2, h3] with z hz2 hz3
    rw [hz2]
    have hz3' : (toL2w m f : ℂ → ℂ) ((Real.sqrt a)⁻¹ • z) =
        ((f (cToPlane ((Real.sqrt a)⁻¹ • z)) : ℝ) : ℂ) := hz3
    rw [hz3', ← Complex.ofReal_mul]
  filter_upwards [h1, (measurePreserving_planeToC m).quasiMeasurePreserving.ae_eq_comp hdil,
    Lp.coeFn_zero ℝ 2 (planeMeasure m)] with x hx1 hx2 hz
  rw [hx1, hz]
  have hx2' : (Planar.dilW hm ha (toL2w m f) : ℂ → ℂ) (planeToC x) =
      (((a ^ 2)⁻¹ * f (cToPlane ((Real.sqrt a)⁻¹ • planeToC x)) : ℝ) : ℂ) := hx2
  rw [hx2', Complex.ofReal_im]
  rfl

/-! ## 3. Joint continuity of a strongly continuous bounded family on a continuous curve -/

theorem continuousOn_strong_apply {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {T : ℝ → E →L[𝕜] E} {s : Set ℝ} {M : ℝ}
    (hbound : ∀ t, ‖T t‖ ≤ M) (hstrong : ∀ x, Continuous fun t => T t x)
    {φ : ℝ → ℝ} (hφ : ContinuousOn φ s) {g : ℝ → E} (hg : ContinuousOn g s) :
    ContinuousOn (fun r => T (φ r) (g r)) s := by
  intro r₀ hr₀
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Tendsto (fun r => max M 0 * ‖g r - g r₀‖) (𝓝[s] r₀) (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_iff_norm_sub_tendsto_zero.1 (hg r₀ hr₀)).const_mul (max M 0)
  have h2 : Tendsto (fun r => ‖T (φ r) (g r₀) - T (φ r₀) (g r₀)‖) (𝓝[s] r₀) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1
      (((hstrong (g r₀)).continuousAt.tendsto).comp (hφ r₀ hr₀))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [add_zero] using h1.add h2) (fun _ => norm_nonneg _) (fun r => ?_)
  have hsplit : T (φ r) (g r) - T (φ r₀) (g r₀) =
      T (φ r) (g r - g r₀) + (T (φ r) (g r₀) - T (φ r₀) (g r₀)) := by
    rw [map_sub, sub_add_sub_cancel]
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
  calc ‖T (φ r) (g r - g r₀)‖
      ≤ ‖T (φ r)‖ * ‖g r - g r₀‖ := (T (φ r)).le_opNorm _
    _ ≤ max M 0 * ‖g r - g r₀‖ :=
        mul_le_mul_of_nonneg_right ((hbound (φ r)).trans (le_max_left M 0)) (norm_nonneg _)

/-! ## 4. Forward integral Gronwall to zero on `[0, T]` -/

/-- If `D : ℝ → ℝ` is continuous and nonnegative on `[0, T]` (`0 ≤ T`) and satisfies
`D t ≤ K * ∫ s in 0..t, D s` (`0 ≤ K`) for all `t ∈ [0, T]`, then `D t = 0` on `[0, T]`. -/
theorem gronwall_zero_Icc {D : ℝ → ℝ} {T K : ℝ} (_hT : 0 ≤ T) (hK : 0 ≤ K)
    (hD : ContinuousOn D (Icc 0 T)) (hnn : ∀ t ∈ Icc 0 T, 0 ≤ D t)
    (hle : ∀ t ∈ Icc 0 T, D t ≤ K * ∫ s in (0 : ℝ)..t, D s) :
    ∀ t ∈ Icc 0 T, D t = 0 := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hD
  have hM' : ∀ t ∈ Icc 0 T, D t ≤ M := fun t ht => by
    have h := hM t ht
    rwa [Real.norm_of_nonneg (hnn t ht)] at h
  have hII : ∀ t ∈ Icc 0 T, IntervalIntegrable D volume 0 t := by
    intro t ht
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht.1]
    exact hD.mono (Icc_subset_Icc le_rfl ht.2)
  have key : ∀ n : ℕ, ∀ t ∈ Icc 0 T,
      D t ≤ M * K ^ n / (Nat.factorial n : ℝ) * t ^ n := by
    intro n
    induction n with
    | zero =>
      intro t ht
      simpa using hM' t ht
    | succ n ih =>
      intro t ht
      have h1 : ∫ s in (0 : ℝ)..t, D s ≤
          ∫ s in (0 : ℝ)..t, M * K ^ n / (Nat.factorial n : ℝ) * s ^ n := by
        refine intervalIntegral.integral_mono_on ht.1 (hII t ht) ?_ fun s hs =>
          ih s ⟨hs.1, hs.2.trans ht.2⟩
        exact (Continuous.intervalIntegrable (by fun_prop) 0 t)
      have h2 : (∫ s in (0 : ℝ)..t, M * K ^ n / (Nat.factorial n : ℝ) * s ^ n) =
          M * K ^ n / (Nat.factorial n : ℝ) * (t ^ (n + 1) / ((n : ℝ) + 1)) := by
        rw [intervalIntegral.integral_const_mul, integral_pow, zero_pow (Nat.succ_ne_zero n),
          sub_zero]
      have hf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
      have hn : (n : ℝ) + 1 ≠ 0 := by positivity
      calc D t ≤ K * ∫ s in (0 : ℝ)..t, D s := hle t ht
        _ ≤ K * ∫ s in (0 : ℝ)..t, M * K ^ n / (Nat.factorial n : ℝ) * s ^ n :=
            mul_le_mul_of_nonneg_left h1 hK
        _ = K * (M * K ^ n / (Nat.factorial n : ℝ) * (t ^ (n + 1) / ((n : ℝ) + 1))) := by
            rw [h2]
        _ = M * K ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) * t ^ (n + 1) := by
            rw [Nat.factorial_succ]
            push_cast
            field_simp
            ring
  intro t ht
  apply le_antisymm _ (hnn t ht)
  have hlim : Tendsto (fun n : ℕ => M * ((K * t) ^ n / (Nat.factorial n : ℝ)))
      atTop (𝓝 0) := by
    simpa using (FloorSemiring.tendsto_pow_div_factorial_atTop (K * t)).const_mul M
  have hev : ∀ n : ℕ, D t ≤ M * ((K * t) ^ n / (Nat.factorial n : ℝ)) := by
    intro n
    refine (key n t ht).trans (le_of_eq ?_)
    rw [mul_pow]
    ring
  exact ge_of_tendsto hlim (Eventually.of_forall hev)

end UnforcedLeray.Short.IIb.PlanarEulerBridge
