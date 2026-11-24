import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2_3_1_1.Bridge
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_b_L4.IntPlanar
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# `PartII-b:F2/3/1/1` (`Interaction.lean`): Dilated planar interaction `A_pl` vs `couplingW`

Proves the Biot–Savart scaling identity
`((1 + σ)²)⁻¹ * ((1 + σ)²)⁻¹ * Apl 0 (fun y => (1 + σ)² * f (√(1 + σ) • y)) (scalePlane (1 + σ) x) = Apl σ f x`
for `0 < 1 + σ`, and deduces that
`couplingDil hm ha = ((1 + σ)²)⁻¹ • (dilW hm ha ∘L couplingW hm ∘L dilW hm ha⁻¹)`
preserves real functions and realifies to an operator `A_pl m σ` satisfying
`IsPlanarInteractionOp m σ (A_pl m σ)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.IIb.PlanarEulerBridge

open UnforcedLeray.Short.IIIa (cToPlane planeToC cToPlane_planeToC planeToC_cToPlane)
open UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit3.PlanarB.L4

/-! ## 1. Pointwise Biot–Savart and `Apl` scaling -/

theorem ofPlane_smul (c : ℝ) (z : B0579.Plane) :
    ofPlane (c • z) = (c : ℂ) * ofPlane z := by
  apply Complex.ext <;> simp [ofPlane]

theorem planarBSC_smul (c : ℝ) (z : B0579.Plane) :
    planarBSC (c • z) = ((c⁻¹ : ℝ) : ℂ) * planarBSC z := by
  unfold planarBSC
  rw [ofPlane_smul, Complex.ofReal_inv]
  have h : 2 * (Real.pi : ℂ) * Complex.I * ((c : ℂ) * ofPlane z) =
      (c : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * ofPlane z) := by ring
  rw [h, mul_inv]

theorem planarBSKernel_smul (c : ℝ) (z : B0579.Plane) :
    planarBSKernel (c • z) = c⁻¹ • planarBSKernel z := by
  rw [planarBSKernel_eq_planarBSC, planarBSKernel_eq_planarBSC, planarBSC_smul]
  ext i
  fin_cases i <;> simp [Cyl.vec]

theorem scalePlane_eq_inv_sqrt_smul (a : ℝ) (x : B0579.Plane) :
    scalePlane a x = (Real.sqrt a)⁻¹ • x := by
  ext <;> simp [scalePlane, div_eq_inv_mul]

theorem planarK_zero_fun (x : B0579.Plane) :
    planarK (fun _ => 0) x = 0 := by
  simp [planarK]

theorem Apl_zero_fun (σ : ℝ) (x : B0579.Plane) :
    Apl σ (fun _ => 0) x = 0 := by
  simp [Apl, planarK_zero_fun]

theorem planarK_scale {a : ℝ} (ha : 0 < a) (f : B0579.Plane → ℝ) (x : B0579.Plane) :
    planarK (fun y => a ^ 2 * f (Real.sqrt a • y)) (scalePlane a x) =
      (a * Real.sqrt a) • planarK f x := by
  set s : ℝ := Real.sqrt a
  have hs : 0 < s := Real.sqrt_pos.2 ha
  have hs2 : s ^ 2 = a := Real.sq_sqrt ha.le
  have hfin : Module.finrank ℝ B0579.Plane = 2 := by
    rw [Module.finrank_prod, Module.finrank_self]
  unfold planarK
  have hker : ∀ y : B0579.Plane,
      (a ^ 2 * f (s • y)) • planarBSKernel (scalePlane a x - y) =
        (a ^ 2 * s) • (f (s • y) • planarBSKernel (x - s • y)) := by
    intro y
    have hsub : scalePlane a x - y = s⁻¹ • (x - s • y) := by
      rw [scalePlane_eq_inv_sqrt_smul, smul_sub, inv_smul_smul₀ hs.ne']
    rw [hsub, planarBSKernel_smul, inv_inv, smul_smul, smul_smul]
    congr 1
    ring
  simp_rw [hker]
  rw [integral_smul]
  have hchg := Measure.integral_comp_smul (μ := (volume : Measure B0579.Plane))
    (fun u => f u • planarBSKernel (x - u)) s
  rw [hfin, hs2, abs_of_pos (inv_pos.2 ha)] at hchg
  change (a ^ 2 * s) • ∫ y : B0579.Plane,
      (fun u => f u • planarBSKernel (x - u)) (s • y) = _
  rw [hchg, smul_smul]
  congr 1
  field_simp

theorem Apl_scale {σ : ℝ} (ha : 0 < 1 + σ) (f : B0579.Plane → ℝ) (x : B0579.Plane) :
    ((1 + σ) ^ 2)⁻¹ * ((1 + σ) ^ 2)⁻¹ *
      Apl 0 (fun y => (1 + σ) ^ 2 * f (Real.sqrt (1 + σ) • y)) (scalePlane (1 + σ) x) =
        Apl σ f x := by
  set a : ℝ := 1 + σ
  set s : ℝ := Real.sqrt a
  have hs : 0 < s := Real.sqrt_pos.2 ha
  have hs2 : s ^ 2 = a := Real.sq_sqrt ha.le
  have hrpow : (a ^ 2)⁻¹ * (a ^ 2)⁻¹ * (a * s) = a ^ (-5 / 2 : ℝ) := by
    have h1 : a ^ (-5 / 2 : ℝ) = (a ^ (2 : ℝ) * a ^ (1 / 2 : ℝ))⁻¹ := by
      rw [← Real.rpow_add ha, ← Real.rpow_neg ha.le]
      congr 1
      norm_num
    rw [h1, Real.rpow_two, ← Real.sqrt_eq_rpow]
    have ha0 : a ≠ 0 := ha.ne'
    have hs0 : s ≠ 0 := hs.ne'
    field_simp
    exact Real.mul_self_sqrt ha.le
  unfold Apl
  rw [planarK_scale ha f x, planarGradE_zero, planeToC_eq_ofPlane]
  unfold planarGradE
  simp only [PiLp.smul_apply, smul_eq_mul]
  calc (a ^ 2)⁻¹ * (a ^ 2)⁻¹ *
        -((a * s * planarK f x 0) * (B0009.gradE0 (ofPlane (scalePlane a x))).1 +
          (a * s * planarK f x 1) * (B0009.gradE0 (ofPlane (scalePlane a x))).2)
      = -((a ^ 2)⁻¹ * (a ^ 2)⁻¹ * (a * s) * planarK f x 0 *
            (B0009.gradE0 (ofPlane (scalePlane a x))).1 +
          (a ^ 2)⁻¹ * (a ^ 2)⁻¹ * (a * s) * planarK f x 1 *
            (B0009.gradE0 (ofPlane (scalePlane a x))).2) := by ring
    _ = -(planarK f x 0 * (a ^ (-5 / 2 : ℝ) * (B0009.gradE0 (ofPlane (scalePlane a x))).1) +
          planarK f x 1 * (a ^ (-5 / 2 : ℝ) * (B0009.gradE0 (ofPlane (scalePlane a x))).2)) := by
        rw [hrpow]
        ring

/-! ## 2. `couplingW`, `couplingDil`, and `A_pl` -/

theorem coeFn_couplingW_toL2w {m : ℝ} (hm : 1 < m) (f : Xm m) :
    (Planar.couplingW hm (toL2w m f) : ℂ → ℂ) =ᵐ[Planar.wMeasure m]
      fun z => ((Apl 0 f (cToPlane z) : ℝ) : ℂ) := by
  let Φ : B0579.Plane → ℂ := fun x => ((f x : ℝ) : ℂ)
  have hW : (toL2w m f : ℂ → ℂ) =ᵐ[volume] fun z => Φ (cToPlane z) :=
    (Planar.volume_ac m).ae_le (coeFn_toL2w m f)
  have hU : (f : B0579.Plane → ℝ) =ᵐ[planeMeasure m] fun x => (Φ x).re :=
    Eventually.of_forall fun x => (Complex.ofReal_re (f x)).symm
  have hV : ((0 : Xm m) : B0579.Plane → ℝ) =ᵐ[planeMeasure m] fun x => (Φ x).im := by
    filter_upwards [Lp.coeFn_zero ℝ 2 (planeMeasure m)] with x hx
    rw [hx]
    simp [Φ]
  filter_upwards [couplingW_ae_eq hm (toL2w m f) hW f 0 hU hV] with z hz
  have hre : (fun x => (Φ x).re) = (f : B0579.Plane → ℝ) := by
    funext x; exact Complex.ofReal_re (f x)
  have him : (fun x => (Φ x).im) = fun _ => (0 : ℝ) := by
    funext x; exact Complex.ofReal_im (f x)
  rw [hz, hre, him, Apl_zero_fun, Complex.ofReal_zero, mul_zero, add_zero]

theorem preservesReal_couplingW {m : ℝ} (hm : 1 < m) :
    PreservesReal (Planar.couplingW hm) := by
  intro f
  apply Lp.ext
  filter_upwards [coeFn_imXm m (Planar.couplingW hm (toL2w m f)),
    (measurePreserving_planeToC m).quasiMeasurePreserving.ae_eq_comp
      (coeFn_couplingW_toL2w hm f),
    Lp.coeFn_zero ℝ 2 (planeMeasure m)] with x hx1 hx2 hz
  rw [hx1, hz]
  have hx2' : (Planar.couplingW hm (toL2w m f) : ℂ → ℂ) (planeToC x) =
      ((Apl 0 f (cToPlane (planeToC x)) : ℝ) : ℂ) := hx2
  rw [hx2', Complex.ofReal_im]
  rfl

/-- Dilated planar Biot–Savart coupling `a⁻² • (J_a ∘ couplingW ∘ J_a⁻¹)` on `Planar.L2w m`. -/
def couplingDil {m : ℝ} (hm : 1 < m) {σ : ℝ} (ha : 0 < 1 + σ) :
    Planar.L2w m →L[ℂ] Planar.L2w m :=
  ((((1 + σ) ^ 2)⁻¹ : ℝ) : ℂ) •
    (Planar.dilW hm ha ∘L Planar.couplingW hm ∘L Planar.dilW hm (inv_pos.2 ha))

theorem preservesReal_couplingDil {m : ℝ} (hm : 1 < m) {σ : ℝ} (ha : 0 < 1 + σ) :
    PreservesReal (couplingDil hm ha) :=
  ((preservesReal_dilW hm ha).comp
    ((preservesReal_couplingW hm).comp (preservesReal_dilW hm (inv_pos.2 ha)))).smul_real _

/-- Real planar interaction operator `A_{pl,σ}` on `Xm m`. -/
def A_pl (m σ : ℝ) : Xm m →L[ℝ] Xm m :=
  if h : 1 < m ∧ 0 < 1 + σ then realify (couplingDil h.1 h.2) else 0

theorem A_pl_eq {m : ℝ} (hm : 1 < m) {σ : ℝ} (ha : 0 < 1 + σ) :
    A_pl m σ = realify (couplingDil hm ha) :=
  dif_pos ⟨hm, ha⟩

theorem toL2w_A_pl {m : ℝ} (hm : 1 < m) {σ : ℝ} (ha : 0 < 1 + σ) (f : Xm m) :
    toL2w m (A_pl m σ f) = couplingDil hm ha (toL2w m f) := by
  rw [A_pl_eq hm ha]
  exact (preservesReal_couplingDil hm ha).toL2w_realify f

theorem cToPlane_smul (c : ℝ) (z : ℂ) :
    cToPlane (c • z) = c • cToPlane z := by
  ext <;> simp [cToPlane]

theorem Apl_congr_ae {m : ℝ} (_hm : 1 < m) (σ : ℝ) {g₁ g₂ : B0579.Plane → ℝ}
    (_hg₁ : MemLp g₁ 2 (planeMeasure m)) (h : g₁ =ᵐ[planeMeasure m] g₂) :
    ∀ᵐ x ∂planeMeasure m, Apl σ g₁ x = Apl σ g₂ x := by
  have hv : g₁ =ᵐ[volume] g₂ := (volume_ac_planeMeasure m).ae_le h
  have hK : ∀ᵐ x ∂(volume : Measure B0579.Plane), planarK g₁ x = planarK g₂ x := by
    refine Eventually.of_forall fun x => ?_
    unfold planarK
    refine integral_congr_ae ?_
    filter_upwards [hv] with y hy
    rw [hy]
  exact (planeMeasure_ac m).ae_le (by
    filter_upwards [hK] with x hx
    simp only [Apl, hx])

theorem isPlanarInteractionOp_A_pl {m : ℝ} (hm : 1 < m) {σ : ℝ} (ha : 0 < 1 + σ) :
    IsPlanarInteractionOp m σ (A_pl m σ) := by
  intro f
  set a : ℝ := 1 + σ
  set s : ℝ := Real.sqrt a
  have hs : 0 < s := Real.sqrt_pos.2 ha
  have hsqrt_inv : (Real.sqrt a⁻¹)⁻¹ = s := by rw [Real.sqrt_inv, inv_inv]
  -- Step 1: `g₀ := reXm (dilW a⁻¹ (toL2w f))` agrees a.e. with `y ↦ a² * f (s • y)`
  let W₀ : Planar.L2w m := Planar.dilW hm (inv_pos.2 ha) (toL2w m f)
  let g₀ : Xm m := reXm m W₀
  have hW₀_to : W₀ = toL2w m g₀ :=
    ((preservesReal_dilW hm (inv_pos.2 ha)).toL2w_realify f).symm
  have hW₀_ae : (W₀ : ℂ → ℂ) =ᵐ[Planar.wMeasure m]
      fun z => ((a ^ 2 * f (s • cToPlane z) : ℝ) : ℂ) := by
    have h1 := Planar.coeFn_dilW hm (inv_pos.2 ha) (toL2w m f)
    have h2 := (Planar.qmp_smul_wMeasure (M := m)
      (Planar.sqrt_inv_ne_zero (inv_pos.2 ha))).ae_eq_comp (coeFn_toL2w m f)
    filter_upwards [h1, h2] with z hz1 hz2
    rw [hz1]
    have hz2' : (toL2w m f : ℂ → ℂ) ((Real.sqrt a⁻¹)⁻¹ • z) =
        ((f (cToPlane ((Real.sqrt a⁻¹)⁻¹ • z)) : ℝ) : ℂ) := hz2
    rw [hz2', hsqrt_inv, cToPlane_smul, inv_pow, inv_inv, ← Complex.ofReal_mul]
  have hg₀_ae : (g₀ : B0579.Plane → ℝ) =ᵐ[planeMeasure m] fun y => a ^ 2 * f (s • y) := by
    filter_upwards [coeFn_reXm m W₀,
      (measurePreserving_planeToC m).quasiMeasurePreserving.ae_eq_comp hW₀_ae] with y hy1 hy2
    rw [hy1]
    have hy2' : (W₀ : ℂ → ℂ) (planeToC y) =
        ((a ^ 2 * f (s • cToPlane (planeToC y)) : ℝ) : ℂ) := hy2
    rw [hy2', cToPlane_planeToC, Complex.ofReal_re]
  -- Step 2: `couplingW W₀` agrees a.e. with `Apl 0 (fun y => a² * f (s • y)) ∘ cToPlane`
  have hApl_g₀ : ∀ᵐ x ∂planeMeasure m,
      Apl 0 g₀ x = Apl 0 (fun y => a ^ 2 * f (s • y)) x :=
    Apl_congr_ae hm 0 (Lp.memLp g₀) hg₀_ae
  have hcpl : (Planar.couplingW hm W₀ : ℂ → ℂ) =ᵐ[Planar.wMeasure m]
      fun z => ((Apl 0 (fun y => a ^ 2 * f (s • y)) (cToPlane z) : ℝ) : ℂ) := by
    rw [hW₀_to]
    filter_upwards [coeFn_couplingW_toL2w hm g₀,
      (measurePreserving_cToPlane m).quasiMeasurePreserving.ae_eq_comp hApl_g₀] with z hz1 hz2
    rw [hz1]
    have hz2' : Apl 0 g₀ (cToPlane z) = Apl 0 (fun y => a ^ 2 * f (s • y)) (cToPlane z) := hz2
    rw [hz2']
  -- Step 3: `couplingDil (toL2w f)` agrees a.e. with `Apl σ f ∘ cToPlane`
  have hcdil : (couplingDil hm ha (toL2w m f) : ℂ → ℂ) =ᵐ[Planar.wMeasure m]
      fun z => ((Apl σ f (cToPlane z) : ℝ) : ℂ) := by
    have hdil := Planar.coeFn_dilW hm ha (Planar.couplingW hm W₀)
    have hcomp := (Planar.qmp_smul_wMeasure (M := m)
      (Planar.sqrt_inv_ne_zero ha)).ae_eq_comp hcpl
    have hsmul := Lp.coeFn_smul ((((a ^ 2)⁻¹ : ℝ) : ℂ))
      (Planar.dilW hm ha (Planar.couplingW hm W₀))
    filter_upwards [hsmul, hdil, hcomp] with z hz0 hz1 hz2
    change ((((a ^ 2)⁻¹ : ℝ) : ℂ) • Planar.dilW hm ha (Planar.couplingW hm W₀) :
      Planar.L2w m) z = _
    rw [hz0, Pi.smul_apply, smul_eq_mul, hz1]
    have hz2' : (Planar.couplingW hm W₀ : ℂ → ℂ) (s⁻¹ • z) =
        ((Apl 0 (fun y => a ^ 2 * f (s • y)) (cToPlane (s⁻¹ • z)) : ℝ) : ℂ) := hz2
    rw [hz2', cToPlane_smul, ← scalePlane_eq_inv_sqrt_smul, ← mul_assoc,
      ← Complex.ofReal_mul, ← Complex.ofReal_mul, Apl_scale ha f (cToPlane z)]
  -- Step 4: apply `reXm`
  rw [A_pl_eq hm ha]
  filter_upwards [coeFn_reXm m (couplingDil hm ha (toL2w m f)),
    (measurePreserving_planeToC m).quasiMeasurePreserving.ae_eq_comp hcdil] with x hx1 hx2
  change (reXm m (couplingDil hm ha (toL2w m f)) : B0579.Plane → ℝ) x = Apl σ f x
  rw [hx1]
  have hx2' : (couplingDil hm ha (toL2w m f) : ℂ → ℂ) (planeToC x) =
      ((Apl σ f (cToPlane (planeToC x)) : ℝ) : ℂ) := hx2
  rw [hx2', cToPlane_planeToC, Complex.ofReal_re]

end UnforcedLeray.Short.IIb.PlanarEulerBridge
