import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2_3_1_1.Bridge
import UnforcedLeray.Short.PartI.Tasks.TransportGroupHjM.Zero
import UnforcedLeray.Short.PartIIb.Tasks.BlockFactorization.FrozenTransportCont.Flow

/-!
# `PartII-b:F2/3/1/1` (`Transport.lean`): Frozen radial transport group `T_pl` on `Xm m`

Constructs `T_pl m σ τ : Xm m →L[ℝ] Xm m` by measure-preserving composition with
`PartIIbF23Sub.frozenRadialFlow σ τ` on `planeMeasure m`, proves all `EulerData` transport
properties, and proves the intertwining identity
`toL2w m (T_pl m σ τ f) = transportDil hm ha τ (toL2w m f)` for `0 < 1 + σ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.IIb.PlanarEulerBridge

open UnforcedLeray.Short.IIIa (cToPlane planeToC cToPlane_planeToC planeToC_cToPlane)
open UnforcedLeray.Short.IIIa.BlockPropagatorSub
open UnforcedLeray.Short.PartI.TransportGroupHjMZero

/-! ## 1. Radial rotation representation on `ℂ` and measure preservation -/

/-- Radial rotation angle `-τ * (1 + σ)⁻² * exp(-(r / √(1 + σ))² / 4)`. -/
def frozenRadialPhase (σ τ r : ℝ) : ℝ :=
  -τ * (((1 + σ) ^ 2)⁻¹ * Real.exp (-((r / Real.sqrt (1 + σ)) ^ 2 / 4)))

/-- Complex form of `frozenRadialFlow σ τ` on `ℂ`. -/
def frozenFlowC (σ τ : ℝ) (z : ℂ) : ℂ :=
  B0062.gexp (frozenRadialPhase σ τ ‖z‖) * z

theorem norm_frozenFlowC (σ τ : ℝ) (z : ℂ) : ‖frozenFlowC σ τ z‖ = ‖z‖ := by
  rw [frozenFlowC, norm_mul, B0062.norm_gexp, one_mul]

theorem measurable_frozenRadialPhase (σ τ : ℝ) : Measurable (frozenRadialPhase σ τ) := by
  unfold frozenRadialPhase
  fun_prop

theorem measurable_frozenFlowC (σ τ : ℝ) : Measurable (frozenFlowC σ τ) :=
  (B0062.contDiff_gexp.continuous.measurable.comp
    ((measurable_frozenRadialPhase σ τ).comp measurable_norm)).mul measurable_id

theorem frozenOmega_cToPlane (σ τ : ℝ) (z : ℂ) :
    -τ * PartIIbF23Sub.frozenOmega σ (cToPlane z) = frozenRadialPhase σ τ ‖z‖ := by
  rw [FrozenTransportContHelp.frozenOmega_eq]
  unfold frozenRadialPhase
  congr 2
  have hsq : ‖z‖ ^ 2 = (cToPlane z).1 ^ 2 + (cToPlane z).2 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [cToPlane, sq]
  rw [div_pow, div_pow, div_pow, ← add_div, hsq]

theorem planeToC_frozenRadialFlow_cToPlane (σ τ : ℝ) (z : ℂ) :
    planeToC (PartIIbF23Sub.frozenRadialFlow σ τ (cToPlane z)) = frozenFlowC σ τ z := by
  have hθ : -τ * PartIIbF23Sub.frozenOmega σ (cToPlane z) = frozenRadialPhase σ τ ‖z‖ :=
    frozenOmega_cToPlane σ τ z
  set θ : ℝ := frozenRadialPhase σ τ ‖z‖
  have hg : B0062.gexp θ = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
    rw [B0062.gexp, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  unfold PartIIbF23Sub.frozenRadialFlow frozenFlowC
  dsimp only
  rw [hθ, hg]
  apply Complex.ext <;>
    simp only [planeToC, cToPlane, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;>
    ring

theorem cToPlane_frozenFlowC_planeToC (σ τ : ℝ) (x : B0579.Plane) :
    cToPlane (frozenFlowC σ τ (planeToC x)) = PartIIbF23Sub.frozenRadialFlow σ τ x := by
  rw [← planeToC_frozenRadialFlow_cToPlane, cToPlane_planeToC, cToPlane_planeToC]

theorem measurePreserving_frozenFlowC_wMeasure (m σ τ : ℝ) :
    MeasurePreserving (frozenFlowC σ τ) (Planar.wMeasure m) (Planar.wMeasure m) := by
  have hρ : Measurable (Planar.wDensity m) := Planar.measurable_wDensity m
  refine B0062.measurePreserving_of_lintegral (measurable_frozenFlowC σ τ) fun g hg => ?_
  have hgc : Measurable fun z => g (frozenFlowC σ τ z) := hg.comp (measurable_frozenFlowC σ τ)
  change ∫⁻ z, g (frozenFlowC σ τ z) ∂(volume.withDensity (Planar.wDensity m)) =
    ∫⁻ z, g z ∂(volume.withDensity (Planar.wDensity m))
  rw [lintegral_withDensity_eq_lintegral_mul volume hρ hgc,
    lintegral_withDensity_eq_lintegral_mul volume hρ hg]
  simp only [Pi.mul_apply]
  have hden : ∀ z : ℂ, Planar.wDensity m z * g (frozenFlowC σ τ z) =
      (fun w => Planar.wDensity m w * g w) (frozenFlowC σ τ z) := by
    intro z
    simp only [Planar.wDensity, norm_frozenFlowC]
  rw [lintegral_congr hden]
  exact B0062.lintegral_comp_rotRadial (measurable_frozenRadialPhase σ τ) (hρ.mul hg)

theorem measurePreserving_frozenRadialFlow (m σ τ : ℝ) :
    MeasurePreserving (PartIIbF23Sub.frozenRadialFlow σ τ) (planeMeasure m) (planeMeasure m) := by
  have hmp := ((measurePreserving_cToPlane m).comp
    (measurePreserving_frozenFlowC_wMeasure m σ τ)).comp (measurePreserving_planeToC m)
  have hfun : (cToPlane ∘ frozenFlowC σ τ) ∘ planeToC = PartIIbF23Sub.frozenRadialFlow σ τ := by
    funext x
    exact cToPlane_frozenFlowC_planeToC σ τ x
  rwa [hfun] at hmp

/-! ## 2. The isometric transport operator `T_pl` on `Xm m` -/

/-- Frozen planar radial transport group `T_pl m σ τ` on `Xm m`. -/
def T_pl (m σ τ : ℝ) : Xm m →L[ℝ] Xm m :=
  (Lp.compMeasurePreservingₗᵢ ℝ (PartIIbF23Sub.frozenRadialFlow σ τ)
    (measurePreserving_frozenRadialFlow m σ τ)).toContinuousLinearMap

theorem coeFn_T_pl (m σ τ : ℝ) (f : Xm m) :
    (T_pl m σ τ f : B0579.Plane → ℝ) =ᵐ[planeMeasure m]
      fun x => f (PartIIbF23Sub.frozenRadialFlow σ τ x) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_frozenRadialFlow m σ τ)

theorem norm_T_pl_apply (m σ τ : ℝ) (f : Xm m) : ‖T_pl m σ τ f‖ = ‖f‖ :=
  (Lp.compMeasurePreservingₗᵢ ℝ (PartIIbF23Sub.frozenRadialFlow σ τ)
    (measurePreserving_frozenRadialFlow m σ τ)).norm_map f

theorem norm_T_pl_le (m σ τ : ℝ) : ‖T_pl m σ τ‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by
    rw [norm_T_pl_apply, one_mul]

theorem T_pl_zero (m σ : ℝ) : T_pl m σ 0 = ContinuousLinearMap.id ℝ (Xm m) := by
  ext1 f
  apply Lp.ext
  filter_upwards [coeFn_T_pl m σ 0 f] with x hx
  rw [hx, FrozenTransportContHelp.flow_zero]
  rfl

theorem T_pl_add (m σ : ℝ) (hσ : 0 ≤ 1 + σ) (τ₁ τ₂ : ℝ) :
    T_pl m σ (τ₁ + τ₂) = (T_pl m σ τ₁).comp (T_pl m σ τ₂) := by
  ext1 f
  apply Lp.ext
  have h1 := coeFn_T_pl m σ (τ₁ + τ₂) f
  have h2 := coeFn_T_pl m σ τ₁ (T_pl m σ τ₂ f)
  have h3 := (measurePreserving_frozenRadialFlow m σ τ₁).quasiMeasurePreserving.ae_eq_comp
    (coeFn_T_pl m σ τ₂ f)
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
  rw [ContinuousLinearMap.comp_apply, hx1, hx2]
  have hx3' : (T_pl m σ τ₂ f : B0579.Plane → ℝ) (PartIIbF23Sub.frozenRadialFlow σ τ₁ x) =
      f (PartIIbF23Sub.frozenRadialFlow σ τ₂ (PartIIbF23Sub.frozenRadialFlow σ τ₁ x)) := hx3
  rw [hx3', FrozenTransportContHelp.flow_add σ hσ τ₂ τ₁ x, add_comm τ₂ τ₁]

/-! ## 3. Intertwining with `Planar.transportGroupW` and strong continuity -/

theorem preservesReal_transportGroupW (m t : ℝ) :
    PreservesReal (Planar.transportGroupW m t) := by
  intro f
  apply Lp.ext
  rw [transportGroupW_eq_compFlow]
  have h1 := coeFn_compFlow m t (toL2w m f)
  have h2 := (measurePreserving_flowMap m t).quasiMeasurePreserving.ae_eq_comp (coeFn_toL2w m f)
  have htr : (compFlow m t (toL2w m f) : ℂ → ℂ) =ᵐ[Planar.wMeasure m]
      fun z => ((f (cToPlane (flowMap t z)) : ℝ) : ℂ) := by
    filter_upwards [h1, h2] with z hz1 hz2
    exact hz1.trans hz2
  filter_upwards [coeFn_imXm m (compFlow m t (toL2w m f)),
    (measurePreserving_planeToC m).quasiMeasurePreserving.ae_eq_comp htr,
    Lp.coeFn_zero ℝ 2 (planeMeasure m)] with x hx1 hx2 hz
  rw [hx1, hz]
  have hx2' : (compFlow m t (toL2w m f) : ℂ → ℂ) (planeToC x) =
      ((f (cToPlane (flowMap t (planeToC x))) : ℝ) : ℂ) := hx2
  rw [hx2', Complex.ofReal_im]
  rfl

/-- Dilated planar transport group `J_a ∘ T_0(τ / a²) ∘ J_a⁻¹` on `Planar.L2w m`. -/
def transportDil {m : ℝ} (hm : 1 < m) {σ : ℝ} (ha : 0 < 1 + σ) (τ : ℝ) :
    Planar.L2w m →L[ℂ] Planar.L2w m :=
  Planar.dilW hm ha ∘L Planar.transportGroupW m (τ / (1 + σ) ^ 2) ∘L Planar.dilW hm (inv_pos.2 ha)

theorem smul_flowMap_inv_smul {σ : ℝ} (ha : 0 < 1 + σ) (τ : ℝ) (z : ℂ) :
    Real.sqrt (1 + σ) • flowMap (τ / (1 + σ) ^ 2) ((Real.sqrt (1 + σ))⁻¹ • z) =
      frozenFlowC σ τ z := by
  set a : ℝ := 1 + σ
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hnorm : ‖(Real.sqrt a)⁻¹ • z‖ = ‖z‖ / Real.sqrt a := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le), inv_mul_eq_div]
  have hphase : -((τ / a ^ 2) * B0009.Omega ((Real.sqrt a)⁻¹ • z)) =
      frozenRadialPhase σ τ ‖z‖ := by
    unfold B0009.Omega GaussianVortex.radialOmega frozenRadialPhase
    rw [hnorm]
    dsimp only [a]
    ring
  unfold flowMap frozenFlowC
  rw [hphase]
  have hg : Complex.exp ((frozenRadialPhase σ τ ‖z‖ : ℂ) * Complex.I) =
      B0062.gexp (frozenRadialPhase σ τ ‖z‖) := rfl
  rw [hg, Complex.real_smul, Complex.real_smul, Complex.ofReal_inv]
  have hsC : (Real.sqrt a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
  calc (Real.sqrt a : ℂ) * (B0062.gexp (frozenRadialPhase σ τ ‖z‖) * ((Real.sqrt a : ℂ)⁻¹ * z))
      = B0062.gexp (frozenRadialPhase σ τ ‖z‖) * ((Real.sqrt a : ℂ) * (Real.sqrt a : ℂ)⁻¹ * z) := by
          ring
    _ = B0062.gexp (frozenRadialPhase σ τ ‖z‖) * z := by
          rw [mul_inv_cancel₀ hsC, one_mul]

theorem toL2w_T_pl {m : ℝ} (hm : 1 < m) {σ : ℝ} (ha : 0 < 1 + σ) (τ : ℝ) (f : Xm m) :
    toL2w m (T_pl m σ τ f) = transportDil hm ha τ (toL2w m f) := by
  set a : ℝ := 1 + σ
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  -- LHS a.e. formula
  have hlhs : (toL2w m (T_pl m σ τ f) : ℂ → ℂ) =ᵐ[Planar.wMeasure m]
      fun z => ((f (PartIIbF23Sub.frozenRadialFlow σ τ (cToPlane z)) : ℝ) : ℂ) := by
    have h1 := coeFn_toL2w m (T_pl m σ τ f)
    have h2 := (measurePreserving_cToPlane m).quasiMeasurePreserving.ae_eq_comp
      (coeFn_T_pl m σ τ f)
    filter_upwards [h1, h2] with z hz1 hz2
    rw [hz1]
    have hz2' : (T_pl m σ τ f : B0579.Plane → ℝ) (cToPlane z) =
        f (PartIIbF23Sub.frozenRadialFlow σ τ (cToPlane z)) := hz2
    rw [hz2']
  -- RHS a.e. formula step 1: `W₀ = dilW a⁻¹ (toL2w f)`
  let W₀ : Planar.L2w m := Planar.dilW hm (inv_pos.2 ha) (toL2w m f)
  have hsqrt_inv : (Real.sqrt a⁻¹)⁻¹ = Real.sqrt a := by
    rw [Real.sqrt_inv, inv_inv]
  have hW₀ : (W₀ : ℂ → ℂ) =ᵐ[Planar.wMeasure m]
      fun w => ((a ^ 2 : ℝ) : ℂ) * ((f (cToPlane (Real.sqrt a • w)) : ℝ) : ℂ) := by
    have h1 := Planar.coeFn_dilW hm (inv_pos.2 ha) (toL2w m f)
    have h2 := (Planar.qmp_smul_wMeasure (M := m)
      (Planar.sqrt_inv_ne_zero (inv_pos.2 ha))).ae_eq_comp (coeFn_toL2w m f)
    filter_upwards [h1, h2] with w hw1 hw2
    rw [hw1]
    have hw2' : (toL2w m f : ℂ → ℂ) ((Real.sqrt a⁻¹)⁻¹ • w) =
        ((f (cToPlane ((Real.sqrt a⁻¹)⁻¹ • w)) : ℝ) : ℂ) := hw2
    rw [hw2', hsqrt_inv, inv_pow, inv_inv]
  -- RHS step 2: `W₁ = transportGroupW (τ / a²) W₀`
  let W₁ : Planar.L2w m := Planar.transportGroupW m (τ / a ^ 2) W₀
  have hW₁ : (W₁ : ℂ → ℂ) =ᵐ[Planar.wMeasure m]
      fun u => ((a ^ 2 : ℝ) : ℂ) *
        ((f (cToPlane (Real.sqrt a • flowMap (τ / a ^ 2) u)) : ℝ) : ℂ) := by
    have htr : W₁ = compFlow m (τ / a ^ 2) W₀ := transportGroupW_eq_compFlow m (τ / a ^ 2) W₀
    rw [htr]
    have h1 := coeFn_compFlow m (τ / a ^ 2) W₀
    have h2 := (measurePreserving_flowMap m (τ / a ^ 2)).quasiMeasurePreserving.ae_eq_comp hW₀
    filter_upwards [h1, h2] with u hu1 hu2
    exact hu1.trans hu2
  -- RHS step 3: `dilW a W₁`
  have hrhs : (transportDil hm ha τ (toL2w m f) : ℂ → ℂ) =ᵐ[Planar.wMeasure m]
      fun z => ((f (PartIIbF23Sub.frozenRadialFlow σ τ (cToPlane z)) : ℝ) : ℂ) := by
    have h1 := Planar.coeFn_dilW hm ha W₁
    have h2 := (Planar.qmp_smul_wMeasure (M := m) (Planar.sqrt_inv_ne_zero ha)).ae_eq_comp hW₁
    filter_upwards [h1, h2] with z hz1 hz2
    show (Planar.dilW hm ha W₁ : ℂ → ℂ) z = _
    rw [hz1]
    have hz2' : (W₁ : ℂ → ℂ) ((Real.sqrt a)⁻¹ • z) =
        ((a ^ 2 : ℝ) : ℂ) *
          ((f (cToPlane (Real.sqrt a • flowMap (τ / a ^ 2) ((Real.sqrt a)⁻¹ • z))) : ℝ) : ℂ) := hz2
    rw [hz2', smul_flowMap_inv_smul ha τ z, ← planeToC_frozenRadialFlow_cToPlane,
      cToPlane_planeToC, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ (pow_ne_zero 2 ha.ne'),
      Complex.ofReal_one, one_mul]
  exact Lp.ext (hlhs.trans hrhs.symm)

theorem continuous_T_pl_apply {m : ℝ} (hm : 1 < m) {σ : ℝ} (ha : 0 < 1 + σ) (f : Xm m) :
    Continuous fun τ => T_pl m σ τ f := by
  have heq : (fun τ => T_pl m σ τ f) =
      fun τ => reXm m (transportDil hm ha τ (toL2w m f)) := by
    funext τ
    rw [← toL2w_T_pl hm ha τ f, reXm_toL2w]
  rw [heq]
  let W₀ : Planar.L2w m := Planar.dilW hm (inv_pos.2 ha) (toL2w m f)
  have h1 : Continuous fun τ : ℝ => Planar.transportGroupW m (τ / (1 + σ) ^ 2) W₀ :=
    (Planar.continuous_transportGroupW_apply m W₀).comp (continuous_id.div_const _)
  have h2 : Continuous fun τ : ℝ => transportDil hm ha τ (toL2w m f) :=
    (Planar.dilW hm ha).continuous.comp h1
  exact (reXm m).continuous.comp h2

end UnforcedLeray.Short.IIb.PlanarEulerBridge
