import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointResidual.RepsVecAdjointOfWeakEq.OuterSGenPair.Forward
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N04_3_3_Org

/-!
# Generator pairs of `S_ε` on axis-reaching vector test fields (helper for `PartII-a:N04/3/3/1`
and `PartII-a:N04/3/3/3`)

Source of record: `the November 2 reference manuscript`,
lines 3343–3352 (the outer semigroup `S_ε` on `L²(dx dτ)` and its generator
`νε²Δ_x + x·∇/2 + 1/2 - ∂_τ`, acting componentwise on vector fields).

For a `C²`, `2εc`-periodic vector field `V` of bounded `x`-support (`IsCoreTestFieldVec`, no
condition at the axis) the complexified phase function `phaseFn V (τ, x) = V(x, τ)` is a `C²` phase
test, the Cartesian operator `B0222.outerGenVec ν ε V` is `fwdGen (νε²) (phaseFn V)` read back in the
physical variables (`cplx3_outerGenVec`), and `isGenPair_phaseTest2` gives the generator pair.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.OuterSGen

open UnforcedLeray.Short.PartIIIb.NearInst (XC cellFn)
open UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization (cplx3 toX toX_ae mp_toCell_phys)
open UnforcedLeray.PhaseSpace
open UnforcedLeray.B0223 (PSpace SpaceC)

/-! ### Slices of the joint derivative -/

/-- The spatial slice derivative of a component is a component of the joint derivative. -/
theorem fderiv_slice_x {F : Space × ℝ → Space} {x : Space} {τ : ℝ}
    (hF : DifferentiableAt ℝ F (x, τ)) (i : Fin 3) (v : Space) :
    fderiv ℝ (fun x' => F (x', τ) i) x v = fderiv ℝ F (x, τ) (v, 0) i := by
  have h1 : HasFDerivAt (fun x' : Space => (x', τ)) (ContinuousLinearMap.inl ℝ Space ℝ) x :=
    hasFDerivAt_prodMk_left x τ
  have h3 : HasFDerivAt (fun x' => F (x', τ) i)
      ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp
        ((fderiv ℝ F (x, τ)).comp (ContinuousLinearMap.inl ℝ Space ℝ))) x :=
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp x (hF.hasFDerivAt.comp x h1)
  rw [h3.fderiv]
  rfl

/-- The phase slice derivative of a component is a component of the joint derivative. -/
theorem deriv_slice_t {F : Space × ℝ → Space} {x : Space} {τ : ℝ}
    (hF : DifferentiableAt ℝ F (x, τ)) (i : Fin 3) :
    deriv (fun σ => F (x, σ) i) τ = fderiv ℝ F (x, τ) (0, 1) i := by
  have h1 : HasFDerivAt (fun σ : ℝ => (x, σ)) (ContinuousLinearMap.inr ℝ Space ℝ) τ :=
    hasFDerivAt_prodMk_right x τ
  have h3 : HasFDerivAt (fun σ => F (x, σ) i)
      ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp
        ((fderiv ℝ F (x, τ)).comp (ContinuousLinearMap.inr ℝ Space ℝ))) τ :=
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp τ (hF.hasFDerivAt.comp τ h1)
  rw [h3.hasDerivAt.deriv]
  rfl

/-- The joint spatial directional derivative `∂_j V`. -/
def Dj (j : Fin 3) (V : Space × ℝ → Space) : Space × ℝ → Space := fun y =>
  fderiv ℝ V y (UnforcedLeray.coordinateVector j, 0)

theorem differentiable_Dj {V : Space × ℝ → Space} (hV : ContDiff ℝ 2 V) (j : Fin 3) :
    Differentiable ℝ (Dj j V) :=
  ((hV.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
    (by norm_num)

/-! ### The phase function of a vector field -/

theorem fderiv_phaseFn {V : Space × ℝ → Space} (hV : Differentiable ℝ V) (q w : ℝ × Space) :
    fderiv ℝ (phaseFn V) q w = cplx3 (fderiv ℝ V (q.2, q.1) (w.2, w.1)) := by
  have hs : HasFDerivAt (fun q : ℝ × Space => (q.2, q.1))
      ((ContinuousLinearMap.snd ℝ ℝ Space).prod (ContinuousLinearMap.fst ℝ ℝ Space)) q :=
    hasFDerivAt_snd.prodMk hasFDerivAt_fst
  have h : HasFDerivAt (phaseFn V)
      (cplx3.comp ((fderiv ℝ V (q.2, q.1)).comp
        ((ContinuousLinearMap.snd ℝ ℝ Space).prod (ContinuousLinearMap.fst ℝ ℝ Space)))) q :=
    cplx3.hasFDerivAt.comp q ((hV (q.2, q.1)).hasFDerivAt.comp q hs)
  rw [h.fderiv]
  rfl

theorem dy_phaseFn {V : Space × ℝ → Space} (hV : Differentiable ℝ V) (j : Fin 3) :
    dy j (phaseFn V) = phaseFn (Dj j V) := by
  funext q
  exact fderiv_phaseFn hV q _

theorem dτ_phaseFn {V : Space × ℝ → Space} (hV : Differentiable ℝ V) (τ : ℝ) (x : Space) :
    dτ (phaseFn V) (τ, x) = cplx3 (fderiv ℝ V (x, τ) (0, 1)) :=
  fderiv_phaseFn hV (τ, x) (1, 0)

theorem lapT_phaseFn {V : Space × ℝ → Space} (hV : ContDiff ℝ 2 V) (τ : ℝ) (x : Space) :
    lapT (phaseFn V) (τ, x) =
      ∑ j : Fin 3, cplx3 (fderiv ℝ (Dj j V) (x, τ) (UnforcedLeray.coordinateVector j, 0)) := by
  have hV1 : Differentiable ℝ V := hV.differentiable (by norm_num)
  show ∑ j : Fin 3, dy j (dy j (phaseFn V)) (τ, x) = _
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dy_phaseFn hV1 j, dy_phaseFn (differentiable_Dj hV j) j]
  rfl

theorem radialT_phaseFn {V : Space × ℝ → Space} (hV : Differentiable ℝ V) (τ : ℝ) (x : Space) :
    radialT (phaseFn V) (τ, x) = ∑ j : Fin 3, x j • cplx3 (Dj j V (x, τ)) := by
  show ∑ j : Fin 3, ((τ, x).2 j) • dy j (phaseFn V) (τ, x) = _
  simp only [dy_phaseFn hV]
  rfl

/-! ### The Cartesian outer operator in terms of the joint derivatives -/

theorem spatialPartial_comp {V : Space × ℝ → Space} (hV : Differentiable ℝ V) (i j : Fin 3)
    (x : Space) (τ : ℝ) :
    UnforcedLeray.B0221.spatialPartial (fun y => V y i) j (x, τ) = Dj j V (x, τ) i :=
  fderiv_slice_x (hV (x, τ)) i _

theorem spatialLap_comp {V : Space × ℝ → Space} (hV : ContDiff ℝ 2 V) (i : Fin 3) (x : Space)
    (τ : ℝ) :
    UnforcedLeray.B0221.spatialLap (fun y => V y i) (x, τ) =
      ∑ j : Fin 3, fderiv ℝ (Dj j V) (x, τ) (UnforcedLeray.coordinateVector j, 0) i := by
  have hV1 : Differentiable ℝ V := hV.differentiable (by norm_num)
  show ∑ j : Fin 3, fderiv ℝ (fun x₁ : Space => fderiv ℝ (fun x' : Space => V (x', τ) i) x₁
      (UnforcedLeray.coordinateVector j)) x (UnforcedLeray.coordinateVector j) = _
  refine Finset.sum_congr rfl fun j _ => ?_
  have hfun : (fun x₁ : Space => fderiv ℝ (fun x' : Space => V (x', τ) i) x₁
      (UnforcedLeray.coordinateVector j)) = fun x₁ => Dj j V (x₁, τ) i := by
    funext x₁
    exact fderiv_slice_x (hV1 (x₁, τ)) i _
  rw [hfun]
  exact fderiv_slice_x (differentiable_Dj hV j (x, τ)) i _

theorem timePartial_comp {V : Space × ℝ → Space} (hV : Differentiable ℝ V) (i : Fin 3)
    (x : Space) (τ : ℝ) :
    UnforcedLeray.B0221.timePartial (fun y => V y i) (x, τ) = fderiv ℝ V (x, τ) (0, 1) i :=
  deriv_slice_t (hV (x, τ)) i

theorem outerGenVec_eq {V : Space × ℝ → Space} (hV : ContDiff ℝ 2 V) (ν ε : ℝ) (x : Space)
    (τ : ℝ) :
    UnforcedLeray.B0222.outerGenVec ν ε V (x, τ) =
      (ν * ε ^ 2) • (∑ j : Fin 3, fderiv ℝ (Dj j V) (x, τ) (UnforcedLeray.coordinateVector j, 0)) +
      (1 / 2 : ℝ) • (∑ j : Fin 3, x j • Dj j V (x, τ)) + (1 / 2 : ℝ) • V (x, τ) -
      fderiv ℝ V (x, τ) (0, 1) := by
  have hV1 : Differentiable ℝ V := hV.differentiable (by norm_num)
  ext i
  have h1 : UnforcedLeray.B0222.outerGenVec ν ε V (x, τ) i =
      UnforcedLeray.B0221.outerGen ν ε (fun y => V y i) (x, τ) := by
    simp only [UnforcedLeray.B0222.outerGenVec, PiLp.toLp_apply]
  rw [h1]
  show ν * ε ^ 2 * UnforcedLeray.B0221.spatialLap (fun y => V y i) (x, τ) +
      (∑ j : Fin 3, x j * UnforcedLeray.B0221.spatialPartial (fun y => V y i) j (x, τ)) / 2 +
      V (x, τ) i / 2 - UnforcedLeray.B0221.timePartial (fun y => V y i) (x, τ) = _
  simp only [spatialLap_comp hV, spatialPartial_comp hV1, timePartial_comp hV1]
  simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, WithLp.ofLp_sum,
    Finset.sum_apply]
  ring

theorem cplx3_outerGenVec {V : Space × ℝ → Space} (hV : ContDiff ℝ 2 V) (ν ε : ℝ) (x : Space)
    (τ : ℝ) :
    cplx3 (UnforcedLeray.B0222.outerGenVec ν ε V (x, τ)) =
      fwdGen (ν * ε ^ 2) (phaseFn V) (τ, x) := by
  have hV1 : Differentiable ℝ V := hV.differentiable (by norm_num)
  rw [outerGenVec_eq hV]
  simp only [fwdGen]
  rw [lapT_phaseFn hV, radialT_phaseFn hV1, dτ_phaseFn hV1]
  simp only [map_sub, map_add, map_smul, map_sum]
  rfl

/-! ### Axis-reaching test fields as `C²` phase tests -/

theorem contDiff_of_core {ε c : ℝ} {V : Space × ℝ → Space}
    (hV : UnforcedLeray.Short.PartIIa.IsCoreTestFieldVec ε c V) : ContDiff ℝ 2 V :=
  (contDiff_piLp 2).2 fun j => hV.smooth j

theorem isPhaseTest2_phaseFn_core {ε c : ℝ} {V : Space × ℝ → Space}
    (hV : UnforcedLeray.Short.PartIIa.IsCoreTestFieldVec ε c V) :
    IsPhaseTest2 (2 * ε * c) (phaseFn V) where
  smooth := cplx3.contDiff.comp ((contDiff_of_core hV).comp (contDiff_snd.prodMk contDiff_fst))
  periodic τ y := by simp only [phaseFn, hV.periodic y τ]
  bounded_support := by
    obtain ⟨R, hR⟩ := hV.bounded
    exact ⟨R, fun τ y hy => by simp only [phaseFn, hR (y, τ) hy, map_zero]⟩

/-- The `X`-class of a physical field is the cell function of its phase function. -/
theorem toX_ae_cellFn {ε c P : ℝ} [Fact (0 < P)] (hP : P = 2 * ε * c)
    {V : Space × ℝ → Space} {W : UnforcedLeray.B0220.PhysL2 ε c}
    (hW : (W : Space × ℝ → Space) =ᵐ[UnforcedLeray.B0220.physMeasure ε c] V) :
    (toX hP W : PSpace P → SpaceC) =ᵐ[volume] cellFn (phaseFn V) := by
  have h1 := toX_ae hP W
  have h2 := (mp_toCell_phys (P := P) hP).quasiMeasurePreserving.ae_eq_comp hW
  filter_upwards [h1, h2] with z hz1 hz2
  rw [hz1]
  simp only [Function.comp_apply] at hz2
  rw [hz2]
  rfl

end UnforcedLeray.Short.PartIIa.OuterSGen

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization (toX)

/-- **Generator pairs on axis-reaching vector test fields** (source 3343–3352): the outer
semigroup `B0223.outerS hν ε` differentiates in `X SpaceC P` on lifted axis-reaching vector test
fields `IsCoreTestFieldVec ε c V` as the Cartesian outer vector operator `B0222.outerGenVec ν ε V`
(`OuterSIsGenPairOnTestFieldVec` with `IsTestFieldVec` replaced by `IsCoreTestFieldVec`). -/
def OuterSIsGenPairOnCoreTestFieldVec : Prop :=
  ∀ (ν c ε : ℝ) (hν : 0 < ν) (_hc : 0 < c) (_hε : 0 < ε)
    (P : ℝ) [Fact (0 < P)] (hP : P = 2 * ε * c)
    (V : Space × ℝ → Space), IsCoreTestFieldVec ε c V →
    ∀ W GW : B0220.PhysL2 ε c,
      (W : Space × ℝ → Space) =ᵐ[B0220.physMeasure ε c] V →
      (GW : Space × ℝ → Space) =ᵐ[B0220.physMeasure ε c] B0222.outerGenVec ν ε V →
      B0223.IsGenPair (B0223.outerS hν ε) (toX hP W) (toX hP GW)

theorem outerSIsGenPairOnCoreTestFieldVec : OuterSIsGenPairOnCoreTestFieldVec := by
  intro ν c ε hν _hc _hε P _ hP V hV W GW hW hGW
  have hV2 : ContDiff ℝ 2 V := OuterSGen.contDiff_of_core hV
  have hψ : OuterSGen.IsPhaseTest2 P (OuterSGen.phaseFn V) := by
    subst hP
    exact OuterSGen.isPhaseTest2_phaseFn_core hV
  refine OuterSGen.isGenPair_phaseTest2 hν ε (OuterSGen.phaseFn V) hψ (toX hP W) (toX hP GW)
    (OuterSGen.toX_ae_cellFn hP hW) ?_
  filter_upwards [OuterSGen.toX_ae_cellFn hP hGW] with z hz
  rw [hz]
  exact OuterSGen.cplx3_outerGenVec hV2 ν ε _ _

end UnforcedLeray.Short.PartIIa
