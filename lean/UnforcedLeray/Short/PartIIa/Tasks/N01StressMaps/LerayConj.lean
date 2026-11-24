import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_3
import UnforcedLeray.Short.PartIIa.Sub.N01.LerayConjSlice
import UnforcedLeray.Units.B0414.PhaseOrthogonal
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_3_3.A.Fund
import UnforcedLeray.Units.B0414.Orthogonal
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.Real.ConjExponents
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.Normed.Lp.PiLp

set_option autoImplicit false

noncomputable section


/-!
# `PartII-a:N01/3/2` (phase gradients are orthogonal to `solenoidalY`)

Source `the November 2 reference manuscript`,
line 1669 and lines 1639-1643 (chart `y = R x`, `R = ε⁻¹`).

For a physical test `φ`, the `τ`-slice of `physGradPhase ε φ` is `ε⁻¹` times the spatial
gradient of the real test `ψ_τ(y) = φ(ε y, τ)`. Slice-wise distributional solenoidality
(`IsSolenoidalC`, no conjugation) therefore kills each slice inner product, and integrating over
the phase circle gives the claim.
-/



open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.PhaseSpace
open UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization (cplx3 toX cplx3_apply)

/-- The phase representative of a point of the circle, in `(0, P]`. -/
def repPhase (P : ℝ) [Fact (0 < P)] (θ : AddCircle P) : ℝ :=
  ((AddCircle.measurableEquivIoc P 0 θ : Ioc (0 : ℝ) (0 + P)) : ℝ)

theorem coe_repPhase (P : ℝ) [Fact (0 < P)] (θ : AddCircle P) :
    ((repPhase P θ : ℝ) : AddCircle P) = θ :=
  AddCircle.coe_equivIoc

/-- The slice of `testElem` is a.e. the slice of the periodic function `Φ`. -/
theorem testElem_ae_slice {P : ℝ} [Fact (0 < P)] {Φ : ℝ × UnforcedLeray.Space → CVec3}
    (hΦ : IsSliceTest P 2 Φ) :
    ∀ᵐ θ ∂(AddCircle.haarAddCircle (T := P)),
      ((testElem P 2 Φ : Yq P 2) θ : UnforcedLeray.Space → CVec3) =ᵐ[volume]
        fun y => Φ (repPhase P θ, y) := by
  rw [testElem_of hΦ]
  filter_upwards [ContinuousMap.coeFn_toLp (E := Lp CVec3 2 (volume : Measure UnforcedLeray.Space))
    (p := 2) (μ := AddCircle.haarAddCircle (T := P)) (𝕜 := ℂ) (circleSlice hΦ)] with θ hθ
  rw [hθ]
  conv_lhs => rw [← coe_repPhase P θ]
  rw [show (circleSlice hΦ) ((repPhase P θ : ℝ) : AddCircle P) = sliceMap hΦ.2 (repPhase P θ) from
    circleSlice_coe hΦ (repPhase P θ)]
  exact MemLp.coeFn_toLp _

/-- The derivative of the rescaled slice `y ↦ φ(εy, τ)`. -/
private theorem fderiv_slice' {ε : ℝ} {φ : UnforcedLeray.Space × ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (τ : ℝ)
    (y v : UnforcedLeray.Space) :
    fderiv ℝ (fun y' : UnforcedLeray.Space => φ (ε • y', τ)) y v =
      ε * fderiv ℝ φ (ε • y, τ) (v, 0) := by
  have hL : HasFDerivAt (fun y' : UnforcedLeray.Space => (ε • y', τ))
      ((ε • ContinuousLinearMap.id ℝ UnforcedLeray.Space).prod 0) y :=
    ((hasFDerivAt_id y).const_smul ε).prodMk (hasFDerivAt_const τ y)
  have hφd : HasFDerivAt φ (fderiv ℝ φ (ε • y, τ)) (ε • y, τ) :=
    ((hφ.differentiable (by simp)) _).hasFDerivAt
  have hc := hφd.comp y hL
  show fderiv ℝ (φ ∘ fun y' : UnforcedLeray.Space => (ε • y', τ)) y v = _
  rw [hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    smul_apply, ContinuousLinearMap.id_apply, zero_apply]
  rw [show ((ε • v, (0 : ℝ))) = ε • ((v, (0 : ℝ)) : UnforcedLeray.Space × ℝ) from by simp,
    map_smul, smul_eq_mul]

/-- Slice-wise solenoidality kills the slice inner product of `physGradPhase`. -/
theorem slice_inner_zero {ε P : ℝ} (hε : 0 < ε) {φ : UnforcedLeray.Space × ℝ → ℝ}
    (hφ : UnforcedLeray.B0226.IsPhysTest P φ) (τ : ℝ) (G : UnforcedLeray.Space → CVec3)
    (hG : UnforcedLeray.B0414.IsSolenoidalC G) :
    ∫ y, inner ℂ (physGradPhase ε φ (τ, y)) (G y) = 0 := by
  obtain ⟨R, hR⟩ := hφ.bounded
  have hψ : UnforcedLeray.IsSpatialTest (fun y : UnforcedLeray.Space => φ (ε • y, τ)) := by
    refine ⟨hφ.smooth.comp ((contDiff_id.const_smul ε).prodMk contDiff_const), ?_⟩
    refine HasCompactSupport.intro (isCompact_closedBall (0 : UnforcedLeray.Space) (R / ε)) ?_
    intro y hy
    by_contra hne
    have h1 := hR _ hne
    simp only at h1
    rw [norm_smul, Real.norm_of_nonneg hε.le] at h1
    have hy' : R / ε < ‖y‖ := by simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hy
    have h2 := (div_lt_iff₀ hε).1 hy'
    nlinarith
  have hpt : ∀ y : UnforcedLeray.Space,
      inner ℂ (physGradPhase ε φ (τ, y)) (G y) =
        (ε⁻¹ : ℂ) * ∑ i : Fin 3, G y i *
          ((UnforcedLeray.spatialTestDerivative i (fun y' : UnforcedLeray.Space => φ (ε • y', τ)) y : ℝ) : ℂ) := by
    intro y
    rw [PiLp.inner_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hgi : UnforcedLeray.B0226.gradX φ (ε • y, τ) i =
        fderiv ℝ φ (ε • y, τ) (UnforcedLeray.coordinateVector i, 0) := by
      rw [← UnforcedLeray.B0226.inner_gradX, UnforcedLeray.coordinateVector,
        EuclideanSpace.inner_single_right]
      simp
    have hd : UnforcedLeray.spatialTestDerivative i (fun y' : UnforcedLeray.Space => φ (ε • y', τ)) y
        = ε * UnforcedLeray.B0226.gradX φ (ε • y, τ) i := by
      unfold UnforcedLeray.spatialTestDerivative
      rw [fderiv_slice' hφ.smooth τ y, hgi]
    simp only [physGradPhase, cplx3_apply, hd]
    have hε0 : ε ≠ 0 := hε.ne'
    have hεc : (ε : ℂ) ≠ 0 := by exact_mod_cast hε0
    simp only [RCLike.inner_apply, Complex.conj_ofReal]
    push_cast
    field_simp
  have hint := hG.identity (fun y' : UnforcedLeray.Space => φ (ε • y', τ)) hψ
  simp only [hpt]
  rw [integral_const_mul, hint, mul_zero]

/-- **Sub-lemma 2 (`PartII-a:N01/3/2`).** -/
theorem physGradPhaseOrth : UnforcedLeray.Short.PartIIa.N01.PhysGradPhaseOrth := by
  intro ε P _ hε φ hφ g hg
  have hΦ : IsSliceTest P 2 (physGradPhase ε φ) := (physGradPhase_isPhaseTest hε hφ).isSliceTest 2
  have hT := testElem_ae_slice hΦ
  have hS := (UnforcedLeray.B0414.mem_solenoidalY_iff_slices g).1 hg
  have key : ∀ᵐ θ ∂(AddCircle.haarAddCircle (T := P)),
      inner ℂ ((testElem P 2 (physGradPhase ε φ) : Yq P 2) θ) (g θ) = 0 := by
    filter_upwards [hT, hS] with θ h1 h2
    have hsol := (UnforcedLeray.B0414.mem_solenoidalC_iff (g θ)).1 h2
    rw [L2.inner_def]
    refine (integral_congr_ae ?_).trans
      (slice_inner_zero hε hφ (repPhase P θ) (⇑(g θ)) hsol)
    filter_upwards [h1] with y hy
    rw [hy]
  rw [L2.inner_def]
  exact integral_eq_zero_of_ae key

end UnforcedLeray.Short.PartIIa.N01

/-!
# `PartII-a:N01/3/3` (decomposition of `PhysSolenoidalToY`)

Source `the November 2 reference manuscript`,
line 1669 (`P_ε` is the conjugated Cartesian Leray projection) and lines 1639-1643 (chart
`y = R x`, `R = ε⁻¹`); phase measure lines 1339-1343.

A physically solenoidal `V ∈ L²(dx dτ; ℝ³)` has a.e. `τ`-slice weakly solenoidal in `x`
(`PhysSliceVanish`, from `mem_physSolenoidal_iff` tested against `χ(τ)ψ(x)` and the fundamental
lemma in `τ`).  Rescaling `x = εy` (`DilTest`), transferring a.e. `τ ∈ (0,P]` to a.e. circle point
(`CircleTransfer`), taking a countable dense family of spatial tests (`CountableTestFamily`,
`SolenoidalOfCountable`) and the proved slice formula `phaseSlice_formula` gives
`U (toX V) ∈ solenoidalY`.
-/



open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.PhaseSpace
open UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization (cplx3 toX cplx3_apply)

/-- **Leaf `PartII-a:N01/3/3/A` (physical slices are weakly solenoidal in `x`).** If
`V ∈ L²(dx dτ)` is distributionally divergence free (`physSolenoidal`), then for every spatial
test `ψ` and a.e. `τ ∈ (0, 2εc]`, `∫ ∑ᵢ Vᵢ(x,τ) ∂ᵢψ(x) dx = 0`.
(Test `mem_physSolenoidal_iff` against `φ(x,τ) = χ(τ)ψ(x)`, `χ` smooth `P`-periodic;
Fubini on `physMeasure`; fundamental lemma in `τ`.) -/
def PhysSliceVanish : Prop :=
  ∀ (ε c : ℝ), 0 < ε → 0 < c → ∀ V : UnforcedLeray.B0220.PhysL2 ε c,
    V ∈ UnforcedLeray.B0226.physSolenoidal ε c →
    ∀ ψ : UnforcedLeray.Space → ℝ, UnforcedLeray.IsSpatialTest ψ →
      ∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) (2 * ε * c))),
        ∫ x, ∑ i : Fin 3, (V : UnforcedLeray.Space × ℝ → UnforcedLeray.Space) (x, τ) i *
          UnforcedLeray.spatialTestDerivative i ψ x = 0

/-- **Leaf `PartII-a:N01/3/3/B` (dilation of a spatial test).** For `ε > 0` the dilate
`x ↦ ψ(ε⁻¹ x)` is a spatial test, and pairings with its derivatives are `ε²` times the pairings
in the variable `y = ε⁻¹ x` (`dx = ε³ dy`, `∂ᵢ[ψ(ε⁻¹·)](εy) = ε⁻¹ (∂ᵢψ)(y)`). -/
def DilTest : Prop :=
  ∀ (ε : ℝ), 0 < ε → ∀ ψ : UnforcedLeray.Space → ℝ, UnforcedLeray.IsSpatialTest ψ →
    UnforcedLeray.IsSpatialTest (fun x => ψ (ε⁻¹ • x)) ∧
    ∀ W : UnforcedLeray.Space → UnforcedLeray.Space,
      ∫ x, ∑ i : Fin 3, W x i * UnforcedLeray.spatialTestDerivative i (fun x => ψ (ε⁻¹ • x)) x =
        ε ^ 2 * ∫ y, ∑ i : Fin 3, W (ε • y) i * UnforcedLeray.spatialTestDerivative i ψ y

/-- **Leaf `PartII-a:N01/3/3/C` (a.e. `τ ∈ (0,P]` to a.e. circle point).** -/
def CircleTransfer : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (q : ℝ → Prop),
    (∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) P)), q τ) →
      ∀ᵐ θ ∂(AddCircle.haarAddCircle (T := P)), q (repPhase P θ)

/-- **Leaf `PartII-a:N01/3/3/D` (countable family of spatial tests).** There is a countable set
`D` of spatial tests whose gradients are dense (in `L²`, componentwise) among all gradients of
spatial tests: this is separability of `L²(ℝ³; ℝ³)`. -/
def CountableTestFamily : Prop :=
  ∃ D : Set (UnforcedLeray.Space → ℝ), D.Countable ∧ (∀ ψ ∈ D, UnforcedLeray.IsSpatialTest ψ) ∧
    ∀ ψ : UnforcedLeray.Space → ℝ, UnforcedLeray.IsSpatialTest ψ → ∀ δ : ℝ, 0 < δ →
      ∃ ψ' ∈ D, ∀ i : Fin 3,
        eLpNorm (fun x => UnforcedLeray.spatialTestDerivative i ψ x -
          UnforcedLeray.spatialTestDerivative i ψ' x) 2 volume < ENNReal.ofReal δ

/-- **Leaf `PartII-a:N01/3/3/E` (solenoidality from a dense family).** An `L²` field whose
pairings vanish against every member of a family `D` with the density property of
`CountableTestFamily` is distributionally solenoidal (`IsSolenoidalC`; pairing without
conjugation; integrability by Cauchy-Schwarz; continuity of the pairing in `∂ψ ∈ L²`). -/
def SolenoidalOfDense : Prop :=
  ∀ D : Set (UnforcedLeray.Space → ℝ), (∀ ψ ∈ D, UnforcedLeray.IsSpatialTest ψ) →
    (∀ ψ : UnforcedLeray.Space → ℝ, UnforcedLeray.IsSpatialTest ψ → ∀ δ : ℝ, 0 < δ →
      ∃ ψ' ∈ D, ∀ i : Fin 3,
        eLpNorm (fun x => UnforcedLeray.spatialTestDerivative i ψ x -
          UnforcedLeray.spatialTestDerivative i ψ' x) 2 volume < ENNReal.ofReal δ) →
    ∀ G : UnforcedLeray.Space → UnforcedLeray.B0223.SpaceC, MemLp G 2 volume →
      (∀ ψ ∈ D, ∫ x, ∑ i : Fin 3, G x i *
        ((UnforcedLeray.spatialTestDerivative i ψ x : ℝ) : ℂ) = 0) →
      UnforcedLeray.B0414.IsSolenoidalC G

/-- **The slice formula** (proved): the `θ`-slice of the phase lift of `toX V` is
`√P ε^{3/2} · cplx3 (V (ε y, τ_θ))` a.e. in `y`, for a.e. `θ`. -/
theorem phaseSlice_formula {ε c P : ℝ} [Fact (0 < P)] (hε : 0 < ε) (hP : P = 2 * ε * c)
    (U : UnforcedLeray.B0223.X UnforcedLeray.B0223.SpaceC P →ₗᵢ[ℂ] Yq P 2)
    (hU : IsPhaseLift ε P U) (V : UnforcedLeray.B0220.PhysL2 ε c) :
    ∀ᵐ θ ∂(AddCircle.haarAddCircle (T := P)),
      ((U (toX hP V) θ : Lp CVec3 2 (volume : Measure UnforcedLeray.Space)) :
          UnforcedLeray.Space → CVec3) =ᵐ[volume]
        fun y => (((Real.sqrt P * ε ^ (3 / 2 : ℝ) : ℝ) : ℂ)) •
          cplx3 ((V : UnforcedLeray.Space × ℝ → UnforcedLeray.Space) (ε • y, repPhase P θ)) := by
  have hP0 : (0 : ℝ) < P := Fact.out
  set F := toX hP V with hFdef
  have hF : ∀ᵐ w ∂(volume : Measure (UnforcedLeray.B0223.PSpace P)),
      (F : UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) w =
        cplx3 ((V : UnforcedLeray.Space × ℝ → UnforcedLeray.Space) (w.1, repPhase P w.2)) :=
    UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.toX_ae hP V
  have hdil : Measure.QuasiMeasurePreserving
      (fun z : UnforcedLeray.B0223.PSpace P => (ε • z.1, z.2)) volume volume := by
    refine ⟨((measurable_const_smul ε).comp measurable_fst).prodMk measurable_snd, ?_⟩
    rw [UnforcedLeray.B0223.map_dil hε]
    exact Measure.smul_absolutelyContinuous
  have hF2 : ∀ᵐ w ∂(volume : Measure (UnforcedLeray.B0223.PSpace P)),
      (F : UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) (ε • w.1, w.2) =
        cplx3 ((V : UnforcedLeray.Space × ℝ → UnforcedLeray.Space) (ε • w.1, repPhase P w.2)) :=
    hdil.ae hF
  have hsw : MeasurePreserving (Prod.swap : AddCircle P × UnforcedLeray.Space →
      UnforcedLeray.B0223.PSpace P)
      ((volume : Measure (AddCircle P)).prod (volume : Measure UnforcedLeray.Space))
      (volume : Measure (UnforcedLeray.B0223.PSpace P)) :=
    MeasureTheory.Measure.measurePreserving_swap
  have hall0 : ∀ᵐ θ ∂(volume : Measure (AddCircle P)), ∀ᵐ y ∂(volume : Measure UnforcedLeray.Space),
      (F : UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) (ε • y, θ) =
        cplx3 ((V : UnforcedLeray.Space × ℝ → UnforcedLeray.Space) (ε • y, repPhase P θ)) :=
    Measure.ae_ae_of_ae_prod (hsw.quasiMeasurePreserving.ae hF2)
  have hall : ∀ᵐ θ ∂(AddCircle.haarAddCircle (T := P)), ∀ᵐ y ∂(volume : Measure UnforcedLeray.Space),
      (F : UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) (ε • y, θ) =
        cplx3 ((V : UnforcedLeray.Space × ℝ → UnforcedLeray.Space) (ε • y, repPhase P θ)) := by
    have h' : ∀ᵐ θ ∂(ENNReal.ofReal P • (AddCircle.haarAddCircle (T := P))),
        ∀ᵐ y ∂(volume : Measure UnforcedLeray.Space),
        (F : UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) (ε • y, θ) =
          cplx3 ((V : UnforcedLeray.Space × ℝ → UnforcedLeray.Space) (ε • y, repPhase P θ)) := by
      rw [← AddCircle.volume_eq_smul_haarAddCircle]
      exact hall0
    exact (Measure.ae_ennreal_smul_measure_iff (ENNReal.ofReal_pos.mpr hP0).ne').1 h'
  filter_upwards [hU F, hall] with θ h1 h2
  filter_upwards [h1, h2] with y e1 e2
  rw [e1, e2]

/-- **Assembly.** `PhysSolenoidalToY` from the five leaves. -/
theorem physSolenoidalToY_of (hA : PhysSliceVanish) (hB : DilTest) (hC : CircleTransfer)
    (hD : CountableTestFamily) (hE : SolenoidalOfDense) : PhysSolenoidalToY := by
  intro ε c P _ hε hc hP U hU V hV
  obtain ⟨D, hDc, hDt, hDa⟩ := hD
  have hvan : ∀ ψ ∈ D, ∀ᵐ θ ∂(AddCircle.haarAddCircle (T := P)),
      ∫ y, ∑ i : Fin 3, (V : UnforcedLeray.Space × ℝ → UnforcedLeray.Space)
          (ε • y, repPhase P θ) i * UnforcedLeray.spatialTestDerivative i ψ y = 0 := by
    intro ψ hψ
    obtain ⟨hT, hI⟩ := hB ε hε ψ (hDt ψ hψ)
    have h1 := hA ε c hε hc V hV (fun x => ψ (ε⁻¹ • x)) hT
    have h2 : ∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) P)), ∫ y, ∑ i : Fin 3,
        (V : UnforcedLeray.Space × ℝ → UnforcedLeray.Space) (ε • y, τ) i *
          UnforcedLeray.spatialTestDerivative i ψ y = 0 := by
      rw [hP]
      filter_upwards [h1] with τ hτ
      have h3 := hI (fun x => (V : UnforcedLeray.Space × ℝ → UnforcedLeray.Space) (x, τ))
      rw [h3] at hτ
      exact (mul_eq_zero.1 hτ).resolve_left (by positivity)
    exact hC P (fun τ => ∫ y, ∑ i : Fin 3, (V : UnforcedLeray.Space × ℝ → UnforcedLeray.Space)
      (ε • y, τ) i * UnforcedLeray.spatialTestDerivative i ψ y = 0) h2
  have hall : ∀ᵐ θ ∂(AddCircle.haarAddCircle (T := P)), ∀ ψ ∈ D,
      ∫ y, ∑ i : Fin 3, (V : UnforcedLeray.Space × ℝ → UnforcedLeray.Space)
          (ε • y, repPhase P θ) i * UnforcedLeray.spatialTestDerivative i ψ y = 0 :=
    (ae_ball_iff hDc).2 hvan
  rw [UnforcedLeray.B0414.mem_solenoidalY_iff]
  filter_upwards [hall, phaseSlice_formula hε hP U hU V] with θ h1 h2
  refine hE D hDt hDa _ (Lp.memLp _) fun ψ hψ => ?_
  have hcongr : (∫ x, ∑ i : Fin 3, ((U (toX hP V) θ : Lp CVec3 2 (volume : Measure UnforcedLeray.Space)) :
        UnforcedLeray.Space → CVec3) x i * ((UnforcedLeray.spatialTestDerivative i ψ x : ℝ) : ℂ)) =
      ∫ x, (((Real.sqrt P * ε ^ (3 / 2 : ℝ) : ℝ) : ℂ)) *
        ((∑ i : Fin 3, (V : UnforcedLeray.Space × ℝ → UnforcedLeray.Space)
          (ε • x, repPhase P θ) i * UnforcedLeray.spatialTestDerivative i ψ x : ℝ) : ℂ) := by
    refine integral_congr_ae ?_
    filter_upwards [h2] with x hx
    rw [hx]
    simp [cplx3_apply, Finset.mul_sum, mul_assoc]
  rw [hcongr, integral_const_mul, integral_complex_ofReal, h1 ψ hψ]
  simp

end UnforcedLeray.Short.PartIIa.N01

/-!
# `PartII-a:N01/3/3/A` (physical slices are weakly solenoidal in `x`)

Reduction of `PhysSliceVanish` to the one-dimensional fundamental lemma for periodic smooth
test factors (`PeriodicFundamental`, a separate leaf). Tests `χ(τ) ψ(x)` are inserted into
`mem_physSolenoidal_iff`, the pairing is rewritten by `inner_gradX_eq_sum`, and Fubini on
`physMeasure = volume ⊗ volume|_(0,P]` gives `∫_(0,P] χ F = 0` with `F τ = ∫ x G(x,τ)`.
-/



open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.B0220 UnforcedLeray.B0226

/-- A product `χ(τ) ψ(x)` of a smooth `P`-periodic factor and a spatial test is a physical test. -/
theorem isPhysTest_mul {P : ℝ} {ψ : UnforcedLeray.Space → ℝ}
    (hψ : UnforcedLeray.IsSpatialTest ψ) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hper : Function.Periodic χ P) :
    IsPhysTest P (fun y => χ y.2 * ψ y.1) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (hχ.comp contDiff_snd).mul (hψ.smooth.comp contDiff_fst)
  · intro x τ
    simp only
    rw [hper τ]
  · obtain ⟨R, hR⟩ := (hψ.compact.isCompact).isBounded.subset_closedBall (0 : UnforcedLeray.Space)
    refine ⟨R, fun y hy => ?_⟩
    have hψy : ψ y.1 ≠ 0 := fun h => hy (by simp [h])
    have hmem : y.1 ∈ tsupport ψ := subset_tsupport ψ hψy
    have := hR hmem
    simpa using this

/-- The spatial test `ψ(x)` viewed as a physical test (constant in `τ`). -/
theorem isPhysTest_spatial {P : ℝ} {ψ : UnforcedLeray.Space → ℝ}
    (hψ : UnforcedLeray.IsSpatialTest ψ) :
    IsPhysTest P (fun y => ψ y.1) := by
  have h := isPhysTest_mul (P := P) hψ (χ := fun _ => (1 : ℝ)) contDiff_const
    (fun τ => rfl)
  exact ⟨by simpa using h.smooth, by intro x τ; simp, by simpa using h.bounded⟩

/-- Pairing with a product test: `⟪V, ∇ₓ(χ(τ)ψ)⟫ = χ(τ) ⟪V, ∇ₓψ⟫`. -/
theorem inner_gradX_mul {P : ℝ} {ψ : UnforcedLeray.Space → ℝ}
    (hψ : UnforcedLeray.IsSpatialTest ψ) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hper : Function.Periodic χ P) (v : UnforcedLeray.Space) (y : UnforcedLeray.Space × ℝ) :
    ⟪v, gradX (fun y => χ y.2 * ψ y.1) y⟫_ℝ = χ y.2 * ⟪v, gradX (fun y => ψ y.1) y⟫_ℝ := by
  have hφ := (isPhysTest_mul (P := P) hψ hχ hper).smooth
  have hφ0 := (isPhysTest_spatial (P := P) hψ).smooth
  rw [inner_gradX_eq_sum hφ, inner_gradX_eq_sum hφ0, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hdiff : DifferentiableAt ℝ ψ y.1 := (hψ.smooth.differentiable (by simp)) y.1
  have hd : spatialTestDerivative i (fun x => χ y.2 * ψ x) y.1 =
      χ y.2 * spatialTestDerivative i ψ y.1 := by
    unfold spatialTestDerivative
    rw [fderiv_const_mul hdiff]
    simp
  beta_reduce
  rw [hd]
  ring


/-- The physical measure is the product of Lebesgue measure on `ℝ³` and the restricted measure
on the period `(0, 2εc]`. -/
theorem physMeasure_eq_prod (ε c : ℝ) :
    physMeasure ε c =
      (volume : Measure UnforcedLeray.Space).prod (volume.restrict (Ioc 0 (2 * ε * c))) := by
  unfold physMeasure physDomain
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

/-- Reduction of `PhysSliceVanish` to the one-dimensional fundamental lemma in `τ`. -/
theorem physSliceVanish_of_fund
    (hFund : ∀ (P : ℝ), 0 < P → ∀ F : ℝ → ℝ, IntegrableOn F (Ioc 0 P) →
      (∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → Function.Periodic χ P →
        ∫ τ in Ioc 0 P, χ τ * F τ = 0) →
      ∀ᵐ τ ∂(volume.restrict (Ioc 0 P)), F τ = 0) :
    PhysSliceVanish := by
  intro ε c hε hc V hV ψ hψ
  have hP : (0 : ℝ) < 2 * ε * c := by positivity
  let G : UnforcedLeray.Space × ℝ → ℝ := fun y =>
    ⟪(V : UnforcedLeray.Space × ℝ → UnforcedLeray.Space) y, gradX (fun y => ψ y.1) y⟫_ℝ
  have hG_meas : Integrable G (physMeasure ε c) := by
    let hφ0 : PhysTest ε c := ⟨fun y => ψ y.1, isPhysTest_spatial (P := 2 * ε * c) hψ⟩
    have hL : Integrable (fun y => ⟪(V : UnforcedLeray.Space × ℝ → UnforcedLeray.Space) y,
        (physGrad ε c hφ0 : UnforcedLeray.Space × ℝ → UnforcedLeray.Space) y⟫_ℝ)
        (physMeasure ε c) := MeasureTheory.L2.integrable_inner V (physGrad ε c hφ0)
    refine hL.congr ?_
    filter_upwards [coeFn_physGrad ε c hφ0] with y hy
    simp only [G]
    rw [hy]
  have hFint : IntegrableOn (fun τ => ∫ x, G (x, τ)) (Ioc 0 (2 * ε * c)) := by
    have hG' : Integrable G ((volume : Measure UnforcedLeray.Space).prod
        (volume.restrict (Ioc 0 (2 * ε * c)))) := by
      rw [← physMeasure_eq_prod ε c]
      exact hG_meas
    exact hG'.integral_prod_right
  have hχ : ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → Function.Periodic χ (2 * ε * c) →
      ∫ τ in Ioc 0 (2 * ε * c), χ τ * (fun τ => ∫ x, G (x, τ)) τ = 0 := by
    intro χ hχs hχp
    have h0 := (mem_physSolenoidal_iff V).1 hV ⟨fun y => χ y.2 * ψ y.1, isPhysTest_mul hψ hχs hχp⟩
    have h0' : ∫ y, χ y.2 * G y ∂(physMeasure ε c) = 0 := by
      refine Eq.trans ?_ h0
      exact integral_congr_ae (Filter.Eventually.of_forall fun y =>
        (inner_gradX_mul hψ hχs hχp _ y).symm)
    obtain ⟨C, hC⟩ := (hχp.isBounded_of_continuous hP.ne' hχs.continuous).exists_norm_le
    have hint : Integrable (fun y : UnforcedLeray.Space × ℝ => χ y.2 * G y)
        (physMeasure ε c) :=
      hG_meas.bdd_mul (f := fun y : UnforcedLeray.Space × ℝ => χ y.2)
        (hχs.continuous.comp continuous_snd).aestronglyMeasurable
        (Filter.Eventually.of_forall fun y : UnforcedLeray.Space × ℝ => hC _ ⟨y.2, rfl⟩)
    rw [physMeasure_eq_prod ε c] at h0' hint
    rw [integral_prod_symm _ hint] at h0'
    calc ∫ τ in Ioc 0 (2 * ε * c), χ τ * (fun τ => ∫ x, G (x, τ)) τ
        = ∫ τ in Ioc 0 (2 * ε * c), ∫ x, χ τ * G (x, τ) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
          simp only
          rw [integral_const_mul]
      _ = 0 := h0'
  have hF := hFund (2 * ε * c) hP (fun τ => ∫ x, G (x, τ)) hFint hχ
  filter_upwards [hF] with τ hτ
  refine Eq.trans ?_ hτ
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [G]
  have hφ0 : ContDiff ℝ ∞ (fun y : UnforcedLeray.Space × ℝ => ψ y.1) :=
    hψ.smooth.comp contDiff_fst
  rw [inner_gradX_eq_sum hφ0]

/-- Target: physical slices are weakly solenoidal in `x` (source line 1669). -/
theorem physSliceVanish : PhysSliceVanish :=
  physSliceVanish_of_fund periodicFundamental

end UnforcedLeray.Short.PartIIa.N01

/-!
# `PartII-a:N01/3/3/B` (dilation of a spatial test)
-/



open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa.N01

/-- Leaf `PartII-a:N01/3/3/B`: dilation of a spatial test. -/
theorem dilTest : UnforcedLeray.Short.PartIIa.N01.DilTest := by
  intro ε hε ψ hψ
  have hc : ε⁻¹ ≠ 0 := inv_ne_zero hε.ne'
  have hsm : ContDiff ℝ ∞ (fun x : UnforcedLeray.Space => ψ (ε⁻¹ • x)) :=
    hψ.smooth.comp (contDiff_id.const_smul ε⁻¹)
  have hT : UnforcedLeray.IsSpatialTest (fun x : UnforcedLeray.Space => ψ (ε⁻¹ • x)) :=
    ⟨hsm, hψ.compact.comp_smul hc⟩
  refine ⟨hT, fun W => ?_⟩
  have hd : ∀ (i : Fin 3) (x : UnforcedLeray.Space),
      UnforcedLeray.spatialTestDerivative i (fun y => ψ (ε⁻¹ • y)) x =
        ε⁻¹ * UnforcedLeray.spatialTestDerivative i ψ (ε⁻¹ • x) := by
    intro i x
    have hψd : HasFDerivAt ψ (fderiv ℝ ψ (ε⁻¹ • x)) (ε⁻¹ • x) :=
      ((hψ.smooth.differentiable (by simp)) (ε⁻¹ • x)).hasFDerivAt
    have hL : HasFDerivAt (fun y : UnforcedLeray.Space => ε⁻¹ • y)
        (ε⁻¹ • ContinuousLinearMap.id ℝ UnforcedLeray.Space) x :=
      (hasFDerivAt_id x).const_smul ε⁻¹
    have hcomp : HasFDerivAt (fun y : UnforcedLeray.Space => ψ (ε⁻¹ • y))
        ((fderiv ℝ ψ (ε⁻¹ • x)).comp (ε⁻¹ • ContinuousLinearMap.id ℝ UnforcedLeray.Space)) x :=
      hψd.comp x hL
    unfold UnforcedLeray.spatialTestDerivative
    rw [hcomp.fderiv]
    simp [smul_eq_mul]
  have hcancel : ∀ x : UnforcedLeray.Space, ε • (ε⁻¹ • x) = x := fun x => by
    rw [smul_smul, mul_inv_cancel₀ hε.ne', one_smul]
  have hpt : ∀ x : UnforcedLeray.Space,
      (∑ i : Fin 3, W x i * UnforcedLeray.spatialTestDerivative i (fun y => ψ (ε⁻¹ • y)) x) =
        ε⁻¹ * ∑ i : Fin 3, W (ε • (ε⁻¹ • x)) i *
          UnforcedLeray.spatialTestDerivative i ψ (ε⁻¹ • x) := by
    intro x
    rw [hcancel x, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hd i x]
    ring
  have hfin : Module.finrank ℝ UnforcedLeray.Space = 3 := finrank_euclideanSpace_fin
  have hc3 : ∫ x : UnforcedLeray.Space, (∑ i : Fin 3, W (ε • (ε⁻¹ • x)) i *
        UnforcedLeray.spatialTestDerivative i ψ (ε⁻¹ • x)) =
      |((ε⁻¹ : ℝ) ^ Module.finrank ℝ UnforcedLeray.Space)⁻¹| •
        ∫ x : UnforcedLeray.Space, ∑ i : Fin 3, W (ε • x) i *
          UnforcedLeray.spatialTestDerivative i ψ x :=
    MeasureTheory.Measure.integral_comp_smul (volume : Measure UnforcedLeray.Space)
      (fun z : UnforcedLeray.Space => ∑ i : Fin 3, W (ε • z) i *
        UnforcedLeray.spatialTestDerivative i ψ z) ε⁻¹
  rw [hfin] at hc3
  have hab : |((ε⁻¹ : ℝ) ^ 3)⁻¹| = ε ^ 3 := by
    rw [inv_pow, inv_inv, abs_of_pos (pow_pos hε 3)]
  have hεinv : ε⁻¹ * ε ^ 3 = ε ^ 2 := by
    field_simp
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul, hc3, hab,
    smul_eq_mul]
  linear_combination (∫ x : UnforcedLeray.Space, ∑ i : Fin 3, W (ε • x) i *
    UnforcedLeray.spatialTestDerivative i ψ x) * hεinv

end UnforcedLeray.Short.PartIIa.N01

/-!
# `PartII-a:N01/3/3/C` (a.e. `τ ∈ (0,P]` to a.e. circle point)
-/



open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIa.N01

/-- Leaf `PartII-a:N01/3/3/C`: a.e. `τ ∈ (0,P]` to a.e. circle point. -/
theorem circleTransfer : UnforcedLeray.Short.PartIIa.N01.CircleTransfer := by
  intro P hPf q hq
  have hP0 : (0 : ℝ) < P := hPf.out
  have hq' : ∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) (0 + P))), q τ := by
    rw [zero_add]
    exact hq
  have key : ∀ᵐ y ∂(Measure.comap (Subtype.val : Ioc (0 : ℝ) (0 + P) → ℝ) volume),
      q ((y : Ioc (0 : ℝ) (0 + P)) : ℝ) :=
    (ae_restrict_iff_subtype measurableSet_Ioc).1 hq'
  have hmp : MeasurePreserving (AddCircle.equivIoc P 0) (volume : Measure (AddCircle P))
      (Measure.comap (Subtype.val : Ioc (0 : ℝ) (0 + P) → ℝ) volume) :=
    AddCircle.measurePreserving_equivIoc P (a := (0 : ℝ))
  have hvol : ∀ᵐ θ ∂(volume : Measure (AddCircle P)),
      q ((AddCircle.equivIoc P 0 θ : ℝ)) :=
    hmp.quasiMeasurePreserving.ae (p := fun y : Ioc (0 : ℝ) (0 + P) => q (y : ℝ)) key
  have hsm : ∀ᵐ θ ∂(ENNReal.ofReal P • (AddCircle.haarAddCircle (T := P))),
      q ((AddCircle.equivIoc P 0 θ : ℝ)) := by
    rw [← AddCircle.volume_eq_smul_haarAddCircle]
    exact hvol
  exact (Measure.ae_ennreal_smul_measure_iff (ENNReal.ofReal_pos.mpr hP0).ne').1 hsm

end UnforcedLeray.Short.PartIIa.N01

/-!
# `PartII-a:N01/3/3/D` (countable family of spatial tests)
-/



open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa.N01

/-- Helper: an `L²`-distance of gradient classes controls the `eLpNorm` of the difference. -/
theorem countableTest_aux {f g : UnforcedLeray.Space → ℝ}
    (hf : MemLp f 2 (volume : Measure UnforcedLeray.Space))
    (hg : MemLp g 2 (volume : Measure UnforcedLeray.Space)) {δ : ℝ} (hδ : 0 < δ)
    (h : dist (hf.toLp f) (hg.toLp g) < δ) :
    eLpNorm (fun x => f x - g x) 2 (volume : Measure UnforcedLeray.Space) < ENNReal.ofReal δ := by
  have h1 : eLpNorm (fun x => f x - g x) 2 (volume : Measure UnforcedLeray.Space) =
      eLpNorm (⇑(hf.toLp f) - ⇑(hg.toLp g)) 2 (volume : Measure UnforcedLeray.Space) := by
    apply eLpNorm_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx1 hx2
    simp [hx1, hx2]
  rw [h1]
  have hfin : eLpNorm (⇑(hf.toLp f) - ⇑(hg.toLp g)) 2 (volume : Measure UnforcedLeray.Space) ≠ ⊤ := by
    have h2 : eLpNorm (⇑(hf.toLp f) - ⇑(hg.toLp g)) 2 (volume : Measure UnforcedLeray.Space) =
        eLpNorm (⇑(hf.toLp f - hg.toLp g)) 2 (volume : Measure UnforcedLeray.Space) := by
      apply eLpNorm_congr_ae
      exact (MeasureTheory.Lp.coeFn_sub _ _).symm
    rw [h2]
    exact MeasureTheory.Lp.eLpNorm_ne_top _
  rw [MeasureTheory.Lp.dist_def] at h
  rw [← ENNReal.ofReal_toReal hfin]
  exact (ENNReal.ofReal_lt_ofReal_iff hδ).2 h

/-- Leaf `PartII-a:N01/3/3/D`: countable family of spatial tests. -/
theorem countableTestFamily : UnforcedLeray.Short.PartIIa.N01.CountableTestFamily := by
  classical
  let S := {ψ : UnforcedLeray.Space → ℝ // UnforcedLeray.IsSpatialTest ψ}
  have hS : Nonempty S := ⟨⟨fun _ => 0, ⟨contDiff_const, HasCompactSupport.zero⟩⟩⟩
  let G : S → (Fin 3 → Lp ℝ 2 (volume : Measure UnforcedLeray.Space)) :=
    fun ψ i => (ψ.2.derivative_memLp i 2).toLp (UnforcedLeray.spatialTestDerivative i ψ.1)
  have hsepU : TopologicalSpace.IsSeparable (Set.univ : Set (Fin 3 → Lp ℝ 2 (volume : Measure UnforcedLeray.Space))) :=
    TopologicalSpace.isSeparable_univ_iff.2 inferInstance
  have hsepR : TopologicalSpace.IsSeparable (Set.range G) := hsepU.mono (Set.subset_univ _)
  obtain ⟨t, htR, htc, hcl⟩ := hsepR.exists_countable_dense_subset
  refine ⟨(fun y => (Function.invFunOn G Set.univ y).1) '' t, htc.image _, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact (Function.invFunOn G Set.univ y).2
  · intro ψ hψ δ hδ
    have hmem : G ⟨ψ, hψ⟩ ∈ closure t := hcl ⟨⟨ψ, hψ⟩, rfl⟩
    obtain ⟨b, hbt, hdb⟩ := Metric.mem_closure_iff.1 hmem δ hδ
    obtain ⟨a, ha⟩ := htR hbt
    have hGb : G (Function.invFunOn G Set.univ b) = b :=
      Function.invFunOn_eq ⟨a, Set.mem_univ _, ha⟩
    have hdb' : dist (G ⟨ψ, hψ⟩) (G (Function.invFunOn G Set.univ b)) < δ := by
      rw [hGb]
      exact hdb
    refine ⟨(Function.invFunOn G Set.univ b).1, ⟨b, hbt, rfl⟩, fun i => ?_⟩
    have hi := (dist_pi_lt_iff hδ).1 hdb' i
    exact countableTest_aux (hψ.derivative_memLp i 2)
      ((Function.invFunOn G Set.univ b).2.derivative_memLp i 2) hδ hi

end UnforcedLeray.Short.PartIIa.N01

/-!
# `PartII-a:N01/3/3/E` (solenoidality from a dense family)

Proves `SolenoidalOfDense`. Source
`the November 2 reference manuscript`,
line 1669 and lines 1639-1643 (the `N01/3/3` chart).

Strategy: for a spatial test `φ` pick, by density, a member `ψ'` of `D` whose gradient is
`δ`-close in `L²` to that of `φ`. The pairing of `G` with `φ` minus the pairing with `ψ'`
is the pairing with the difference, which is bounded by `(∑ᵢ ‖Gᵢ‖₂) δ` by Hölder. Since the
pairing with `ψ'` vanishes, the pairing with `φ` is `0`.
-/



open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa.N01

/-- Hölder bound for one coordinate pairing: an `L²` complex function against a real `L²`
function is integrable and its integral is bounded by the product of the `L²` norms. -/
lemma solDense_pair_bound (f : UnforcedLeray.Space → ℂ) (hf : MemLp f 2 volume)
    (g : UnforcedLeray.Space → ℝ) (hg : MemLp g 2 volume) :
    Integrable (fun x => f x * ((g x : ℝ) : ℂ)) ∧
      ‖∫ x, f x * ((g x : ℝ) : ℂ)‖ ≤
        (∫ x, ‖f x‖ ^ (2:ℝ)) ^ ((2:ℝ)⁻¹) * (∫ x, ‖g x‖ ^ (2:ℝ)) ^ ((2:ℝ)⁻¹) := by
  have hgC : MemLp (fun x => ((g x : ℝ) : ℂ)) 2 volume := hg.ofReal
  have hp : ENNReal.ofReal (2:ℝ) = 2 := ENNReal.ofReal_ofNat 2
  refine ⟨hf.integrable_mul hgC, ?_⟩
  have h1 := integral_mul_norm_le_Lp_mul_Lq (μ := volume) (f := f)
    (g := fun x => ((g x : ℝ) : ℂ)) (p := 2) (q := 2) Real.HolderConjugate.two_two
    (by rw [hp]; exact hf) (by rw [hp]; exact hgC)
  have h2 : ∀ x, ‖((g x : ℝ) : ℂ)‖ = ‖g x‖ := fun x => Complex.norm_real _
  simp only [h2, one_div] at h1
  calc ‖∫ x, f x * ((g x : ℝ) : ℂ)‖ ≤ ∫ x, ‖f x * ((g x : ℝ) : ℂ)‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ x, ‖f x‖ * ‖g x‖ := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [norm_mul, h2]
    _ ≤ _ := h1

/-- **Leaf `PartII-a:N01/3/3/E` (solenoidality from a dense family).** -/
theorem solenoidalOfDense : UnforcedLeray.Short.PartIIa.N01.SolenoidalOfDense := by
  intro D hDt hDdense G hG hD
  have hGi : ∀ i : Fin 3, MemLp (fun x => G x i) 2 volume := by
    intro i
    refine MemLp.of_le hG.norm ?_ (Eventually.of_forall fun x => ?_)
    · exact ((EuclideanSpace.proj i : EuclideanSpace ℂ (Fin 3) →L[ℂ] ℂ).continuous.comp_aestronglyMeasurable
        hG.aestronglyMeasurable)
    · show ‖G x i‖ ≤ ‖‖G x‖‖
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      exact PiLp.norm_apply_le _ _
  have hderiv : ∀ φ : UnforcedLeray.Space → ℝ, UnforcedLeray.IsSpatialTest φ → ∀ i : Fin 3,
      MemLp (fun x => UnforcedLeray.spatialTestDerivative i φ x) 2 volume := fun φ hφ i =>
    UnforcedLeray.IsSpatialTest.derivative_memLp hφ i 2
  have hpair : ∀ φ : UnforcedLeray.Space → ℝ, UnforcedLeray.IsSpatialTest φ → ∀ i : Fin 3,
      Integrable (fun x => G x i * ((UnforcedLeray.spatialTestDerivative i φ x : ℝ) : ℂ)) :=
    fun φ hφ i => (solDense_pair_bound (fun x => G x i) (hGi i)
      (fun x => UnforcedLeray.spatialTestDerivative i φ x) (hderiv φ hφ i)).1
  have hint : ∀ φ : UnforcedLeray.Space → ℝ, UnforcedLeray.IsSpatialTest φ →
      Integrable (fun x => ∑ i : Fin 3, G x i * ((UnforcedLeray.spatialTestDerivative i φ x : ℝ) : ℂ)) :=
    fun φ hφ => integrable_finsetSum _ (fun i _ => hpair φ hφ i)
  refine ⟨fun φ hφ => hint φ hφ, fun φ hφ => ?_⟩
  -- the pairing of `G` against `φ`
  have hnorm_small : ∀ ψ' : UnforcedLeray.Space → ℝ, UnforcedLeray.IsSpatialTest ψ' →
      ∀ δ : ℝ, 0 < δ → ∀ i : Fin 3,
        eLpNorm (fun x => UnforcedLeray.spatialTestDerivative i φ x -
          UnforcedLeray.spatialTestDerivative i ψ' x) 2 volume < ENNReal.ofReal δ →
        (∫ x, ‖UnforcedLeray.spatialTestDerivative i φ x -
          UnforcedLeray.spatialTestDerivative i ψ' x‖ ^ (2:ℝ)) ^ ((2:ℝ)⁻¹) ≤ δ := by
    intro ψ' hψ' δ hδ i hclose
    have hdiff : MemLp (fun x => UnforcedLeray.spatialTestDerivative i φ x -
        UnforcedLeray.spatialTestDerivative i ψ' x) 2 volume :=
      (hderiv φ hφ i).sub (hderiv ψ' hψ' i)
    rw [hdiff.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)] at hclose
    simp only [ENNReal.toReal_ofNat] at hclose
    exact ((ENNReal.ofReal_lt_ofReal_iff hδ).1 hclose).le
  set L : ℂ := ∫ x, ∑ i : Fin 3, G x i * ((UnforcedLeray.spatialTestDerivative i φ x : ℝ) : ℂ)
    with hLdef
  have hbound : ∀ δ : ℝ, 0 < δ →
      ‖L‖ ≤ (∑ i : Fin 3, (∫ x, ‖G x i‖ ^ (2:ℝ)) ^ ((2:ℝ)⁻¹)) * δ := by
    intro δ hδ
    obtain ⟨ψ', hψ'D, hclose⟩ := hDdense φ hφ δ hδ
    have hψ't : UnforcedLeray.IsSpatialTest ψ' := hDt ψ' hψ'D
    have hz := hD ψ' hψ'D
    have hL : L = ∑ i : Fin 3, ∫ x, G x i *
        ((UnforcedLeray.spatialTestDerivative i φ x - UnforcedLeray.spatialTestDerivative i ψ' x : ℝ)
          : ℂ) := by
      calc L = L - ∫ x, ∑ i : Fin 3, G x i *
            ((UnforcedLeray.spatialTestDerivative i ψ' x : ℝ) : ℂ) := by rw [hz, sub_zero]
        _ = ∫ x, (∑ i : Fin 3, G x i * ((UnforcedLeray.spatialTestDerivative i φ x : ℝ) : ℂ) -
              ∑ i : Fin 3, G x i * ((UnforcedLeray.spatialTestDerivative i ψ' x : ℝ) : ℂ)) :=
            (integral_sub (hint φ hφ) (hint ψ' hψ't)).symm
        _ = ∫ x, ∑ i : Fin 3, G x i *
              ((UnforcedLeray.spatialTestDerivative i φ x - UnforcedLeray.spatialTestDerivative i ψ' x
                : ℝ) : ℂ) := by
            refine integral_congr_ae (Eventually.of_forall fun x => ?_)
            dsimp only
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun i _ => ?_
            push_cast
            ring
        _ = ∑ i : Fin 3, ∫ x, G x i *
              ((UnforcedLeray.spatialTestDerivative i φ x - UnforcedLeray.spatialTestDerivative i ψ' x
                : ℝ) : ℂ) := by
            refine integral_finsetSum _ (fun i _ => ?_)
            have hdiff : MemLp (fun x => UnforcedLeray.spatialTestDerivative i φ x -
                UnforcedLeray.spatialTestDerivative i ψ' x) 2 volume :=
              (hderiv φ hφ i).sub (hderiv ψ' hψ't i)
            exact (solDense_pair_bound (fun x => G x i) (hGi i)
              (fun x => UnforcedLeray.spatialTestDerivative i φ x -
                UnforcedLeray.spatialTestDerivative i ψ' x) hdiff).1
    rw [hL]
    calc ‖∑ i : Fin 3, ∫ x, G x i *
            ((UnforcedLeray.spatialTestDerivative i φ x - UnforcedLeray.spatialTestDerivative i ψ' x
              : ℝ) : ℂ)‖
        ≤ ∑ i : Fin 3, ‖∫ x, G x i *
            ((UnforcedLeray.spatialTestDerivative i φ x - UnforcedLeray.spatialTestDerivative i ψ' x
              : ℝ) : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin 3, (∫ x, ‖G x i‖ ^ (2:ℝ)) ^ ((2:ℝ)⁻¹) * δ := by
          refine Finset.sum_le_sum fun i _ => ?_
          have hdiff : MemLp (fun x => UnforcedLeray.spatialTestDerivative i φ x -
              UnforcedLeray.spatialTestDerivative i ψ' x) 2 volume :=
            (hderiv φ hφ i).sub (hderiv ψ' hψ't i)
          have hh := (solDense_pair_bound (fun x => G x i) (hGi i)
            (fun x => UnforcedLeray.spatialTestDerivative i φ x -
              UnforcedLeray.spatialTestDerivative i ψ' x) hdiff).2
          have hs := hnorm_small ψ' hψ't δ hδ i (hclose i)
          exact le_trans hh (mul_le_mul_of_nonneg_left hs
            (Real.rpow_nonneg (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _) _))
      _ = (∑ i : Fin 3, (∫ x, ‖G x i‖ ^ (2:ℝ)) ^ ((2:ℝ)⁻¹)) * δ := (Finset.sum_mul _ _ _).symm
  -- conclude `L = 0` by letting `δ → 0`
  have hS : 0 ≤ ∑ i : Fin 3, (∫ x, ‖G x i‖ ^ (2:ℝ)) ^ ((2:ℝ)⁻¹) :=
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _) _
  have hL0 : ‖L‖ ≤ 0 := by
    by_contra hcon
    have hpos : 0 < ‖L‖ := not_le.1 hcon
    have h1 := hbound (‖L‖ / (2 * ((∑ i : Fin 3, (∫ x, ‖G x i‖ ^ (2:ℝ)) ^ ((2:ℝ)⁻¹)) + 1)))
      (by positivity)
    have h2 : (∑ i : Fin 3, (∫ x, ‖G x i‖ ^ (2:ℝ)) ^ ((2:ℝ)⁻¹)) *
        (‖L‖ / (2 * ((∑ i : Fin 3, (∫ x, ‖G x i‖ ^ (2:ℝ)) ^ ((2:ℝ)⁻¹)) + 1))) ≤ ‖L‖ / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  exact norm_le_zero_iff.1 hL0

end UnforcedLeray.Short.PartIIa.N01

/-!
# `PartII-a:N01/3/3` (assembly: `PhysSolenoidalToY` from the five leaves)

Source `the November 2 reference manuscript`,
line 1669 and lines 1639-1643. The leaves are `physSliceVanish` (A), `dilTest` (B),
`circleTransfer` (C), `countableTestFamily` (D) and `solenoidalOfDense` (E); the assembly
`physSolenoidalToY_of` is in `PartII-a_N01_3_3`.
-/



namespace UnforcedLeray.Short.PartIIa.N01

theorem physSolenoidalToY : UnforcedLeray.Short.PartIIa.N01.PhysSolenoidalToY :=
  physSolenoidalToY_of physSliceVanish dilTest circleTransfer countableTestFamily solenoidalOfDense

end UnforcedLeray.Short.PartIIa.N01

/-!
# `PartII-a:N01/3` (assembly: `PhaseLerayConj` from the three sub-lemmas)

Source `the November 2 reference manuscript`,
line 1669 (`P_ε` is the conjugated Cartesian Leray projection) and lines 1639-1643 (chart `y = R x`).

The three sub-lemmas are `physGradPhaseSliceTest` (N01/3/1, `LerayConjSlice`),
`physGradPhaseOrth` (N01/3/2, `LerayConjOrth`) and `physSolenoidalToY` (N01/3/3,
`LerayConjSolenoidal`); the abstract assembly `phaseLerayConj_of` is in `PartII-a_N01_3`.
-/



namespace UnforcedLeray.Short.PartIIa.N01

theorem phaseLerayConj : UnforcedLeray.Short.PartIIa.N01.PhaseLerayConj :=
  phaseLerayConj_of physGradPhaseSliceTest physGradPhaseOrth physSolenoidalToY

end UnforcedLeray.Short.PartIIa.N01
