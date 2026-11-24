import UnforcedLeray.Short.PartIIa.Sub.N01.Defs

/-!
# `PartII-a:N01/4` (sub-lemmas of `PhaseDivScale`)

Source `the November 2 reference manuscript`,
lines 1639-1643 (`y = R x`), 1655-1665 (the Cartesian divergence), 1339-1343 (phase measure).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.PhaseSpace
open UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization (IsCartTest cartDiv outerField toX)

/-- The rows of a Cartesian test tensor are smooth phase tests (lines 1647-1650). -/
theorem cartRowsC_isPhaseTest {P : ℝ} {T : ℝ → UnforcedLeray.Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hT : IsCartTest P T) (i : Fin 3) : IsPhaseTest P (cartRowsC T i) := by
  refine ⟨?_, ?_, ?_⟩
  · apply PiLp.contDiff_toLp.comp
    apply contDiff_pi.2
    intro j
    have hf : ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => T x.1 x.2 i j) :=
      (hT.smooth i j).comp (contDiff_snd.prodMk contDiff_fst)
    exact Complex.ofRealCLM.contDiff.comp hf
  · intro τ y
    simp only [cartRowsC]
    rw [hT.periodic]
  · obtain ⟨r, hr⟩ := hT.bounded
    refine ⟨r, fun τ y hy => ?_⟩
    have h0 : T τ y = 0 := by
      by_contra hne
      exact absurd (hr τ y hne) (not_le.mpr hy)
    simp [cartRowsC, h0]
    rfl

/-- **Sub-lemma 1 (pointwise chain rule).** -/
def DivScaleChain : Prop :=
  ∀ (ε P : ℝ), 0 < ε → ∀ T : ℝ → UnforcedLeray.Space → Matrix (Fin 3) (Fin 3) ℝ, IsCartTest P T →
    ∀ (x : UnforcedLeray.Space) (τ : ℝ) (i : Fin 3),
      ((cartDiv (outerField ε⁻¹ T) (x, τ) i : ℝ) : ℂ) =
        ((ε⁻¹ : ℝ) : ℂ) * tensorDiv (cartRowsC T) (τ, ε⁻¹ • x) i

theorem divScaleChain : DivScaleChain := by
  intro ε P hε T hT x τ i
  simp only [cartDiv, outerField, tensorDiv, PiLp.toLp_apply]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hf : ContDiff ℝ ∞ (fun q : ℝ × UnforcedLeray.Space => T q.1 q.2 i j) :=
    (hT.smooth i j).comp (contDiff_snd.prodMk contDiff_fst)
  have hfd : Differentiable ℝ (fun q : ℝ × UnforcedLeray.Space => T q.1 q.2 i j) :=
    hf.differentiable (by simp)
  have hΦ : Differentiable ℝ (cartRowsC T i) := ((cartRowsC_isPhaseTest hT i).smooth).differentiable (by simp)
  set v : UnforcedLeray.Space := UnforcedLeray.coordinateVector j with hv
  set q : ℝ × UnforcedLeray.Space := (τ, ε⁻¹ • x) with hq
  have h1 : fderiv ℝ (fun x' : UnforcedLeray.Space => T τ (ε⁻¹ • x') i j) x v =
      ε⁻¹ * fderiv ℝ (fun q : ℝ × UnforcedLeray.Space => T q.1 q.2 i j) q (0, v) := by
    have hin : HasFDerivAt (fun x' : UnforcedLeray.Space => ((τ, ε⁻¹ • x') : ℝ × UnforcedLeray.Space))
        ((0 : UnforcedLeray.Space →L[ℝ] ℝ).prod (ε⁻¹ • ContinuousLinearMap.id ℝ UnforcedLeray.Space)) x :=
      (hasFDerivAt_const τ x).prodMk ((hasFDerivAt_id x).const_smul ε⁻¹)
    have hc := (hfd q).hasFDerivAt.comp x hin
    have := hc.fderiv
    change fderiv ℝ (fun x' : UnforcedLeray.Space => T τ (ε⁻¹ • x') i j) x v = _
    rw [show (fun x' : UnforcedLeray.Space => T τ (ε⁻¹ • x') i j) =
      (fun q : ℝ × UnforcedLeray.Space => T q.1 q.2 i j) ∘
        (fun x' : UnforcedLeray.Space => ((τ, ε⁻¹ • x') : ℝ × UnforcedLeray.Space)) from rfl, this]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.zero_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
    rw [show ((0 : ℝ), ε⁻¹ • v) = ε⁻¹ • ((0 : ℝ), v) by simp, map_smul, smul_eq_mul]
  have h2 : (fderiv ℝ (cartRowsC T i) q (0, v)) j =
      ((fderiv ℝ (fun q : ℝ × UnforcedLeray.Space => T q.1 q.2 i j) q (0, v) : ℝ) : ℂ) := by
    have hA : HasFDerivAt (fun p => (cartRowsC T i p) j)
        (((EuclideanSpace.proj j : CVec3 →L[ℂ] ℂ).restrictScalars ℝ).comp (fderiv ℝ (cartRowsC T i) q)) q :=
      ((EuclideanSpace.proj j : CVec3 →L[ℂ] ℂ).restrictScalars ℝ).hasFDerivAt.comp q (hΦ q).hasFDerivAt
    have hB : HasFDerivAt (fun p : ℝ × UnforcedLeray.Space => (cartRowsC T i p) j)
        (Complex.ofRealCLM.comp (fderiv ℝ (fun q : ℝ × UnforcedLeray.Space => T q.1 q.2 i j) q)) q :=
      Complex.ofRealCLM.hasFDerivAt.comp q (hfd q).hasFDerivAt
    have := congrArg (fun L => L (0, v)) (hA.unique hB)
    simpa using this
  show ((fderiv ℝ (fun x' : UnforcedLeray.Space => T τ (ε⁻¹ • x') i j) x v : ℝ) : ℂ) = _
  rw [h1]
  have h3 : dy j (cartRowsC T i) q j = (fderiv ℝ (cartRowsC T i) q (0, v)) j := rfl
  rw [h3, h2]
  push_cast
  ring

/-- **Sub-lemma 2.** The row divergence of a Cartesian test tensor is a phase test (hence a slice
test, so `testElem` is the genuine slice element). -/
theorem tensorDiv_isPhaseTest {P : ℝ} {T : ℝ → UnforcedLeray.Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hT : IsCartTest P T) : IsPhaseTest P (tensorDiv (cartRowsC T)) := by
  have hsum : tensorDiv (cartRowsC T) = ∑ i : Fin 3, ∑ j : Fin 3, fun p =>
      (((EuclideanSpace.proj j : CVec3 →L[ℂ] ℂ).restrictScalars ℝ).smulRight
        (EuclideanSpace.single i (1 : ℂ) : CVec3)) (dy j (cartRowsC T i) p) := by
    funext p
    ext k
    simp only [tensorDiv, Finset.sum_apply, PiLp.toLp_apply]
    simp [WithLp.ofLp_sum, Finset.sum_apply, Pi.single_apply]
  rw [hsum]
  refine IsPhaseTest.sum _ fun i _ => IsPhaseTest.sum _ fun j _ => ?_
  exact ((cartRowsC_isPhaseTest hT i).dy j).clm_comp _

/-- **Sub-lemma 3 (identification of the phase lift of a dilated test field).** If the complexified
field `g` of `L²(dx dτ)` equals `a • Φ(τ, x/ε)` a.e. for a slice test `Φ`, then its phase lift is
`√P ε^{3/2} a` times the slice element of `Φ`. -/
theorem divScaleTransfer {ε c P : ℝ} [Fact (0 < P)] (hε : 0 < ε) (hP : P = 2 * ε * c)
    (U : UnforcedLeray.B0223.X UnforcedLeray.B0223.SpaceC P →ₗᵢ[ℂ] Yq P 2)
    (hU : IsPhaseLift ε P U) (g : UnforcedLeray.B0220.PhysL2 ε c)
    (Φ : ℝ × UnforcedLeray.Space → CVec3) (hΦ : IsSliceTest P 2 Φ) (a : ℂ)
    (hg : ∀ᵐ w ∂(UnforcedLeray.B0220.physMeasure ε c),
      UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.cplx3 (g w) =
        a • Φ (w.2, ε⁻¹ • w.1)) :
    U (toX hP g) = ((((Real.sqrt P * ε ^ (3 / 2 : ℝ) : ℝ)) : ℂ) * a) • testElem P 2 Φ := by
  have hP0 : (0 : ℝ) < P := Fact.out
  set F := toX hP g with hFdef
  let rep : AddCircle P → ℝ := fun θ =>
    ((AddCircle.measurableEquivIoc P 0 θ : Ioc (0 : ℝ) (0 + P)) : ℝ)
  have hrep : ∀ θ, ((rep θ : ℝ) : AddCircle P) = θ := fun θ => AddCircle.coe_equivIoc
  have hF : ∀ᵐ w ∂(volume : Measure (UnforcedLeray.B0223.PSpace P)),
      (F : UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) w =
        a • Φ (rep w.2, ε⁻¹ • w.1) := by
    filter_upwards [UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.toX_ae hP g,
      (UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.mp_toCell_phys
        hP).quasiMeasurePreserving.ae hg] with w h1 h2
    rw [h1]
    exact h2
  have hdil : Measure.QuasiMeasurePreserving
      (fun z : UnforcedLeray.B0223.PSpace P => (ε • z.1, z.2)) volume volume := by
    refine ⟨((measurable_const_smul ε).comp measurable_fst).prodMk measurable_snd, ?_⟩
    rw [UnforcedLeray.B0223.map_dil hε]
    exact Measure.smul_absolutelyContinuous
  have hF2 : ∀ᵐ w ∂(volume : Measure (UnforcedLeray.B0223.PSpace P)),
      (F : UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) (ε • w.1, w.2) =
        a • Φ (rep w.2, w.1) := by
    filter_upwards [hdil.ae hF] with w hw
    rw [hw]
    simp [smul_smul, inv_mul_cancel₀ hε.ne']
  have hsw : MeasurePreserving (Prod.swap : AddCircle P × UnforcedLeray.Space →
      UnforcedLeray.B0223.PSpace P)
      ((volume : Measure (AddCircle P)).prod (volume : Measure UnforcedLeray.Space))
      (volume : Measure (UnforcedLeray.B0223.PSpace P)) :=
    MeasureTheory.Measure.measurePreserving_swap
  have hall0 : ∀ᵐ θ ∂(volume : Measure (AddCircle P)), ∀ᵐ y ∂(volume : Measure UnforcedLeray.Space),
      (F : UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) (ε • y, θ) =
        a • Φ (rep θ, y) :=
    Measure.ae_ae_of_ae_prod (hsw.quasiMeasurePreserving.ae hF2)
  have hall : ∀ᵐ θ ∂(AddCircle.haarAddCircle (T := P)), ∀ᵐ y ∂(volume : Measure UnforcedLeray.Space),
      (F : UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) (ε • y, θ) =
        a • Φ (rep θ, y) := by
    have h' : ∀ᵐ θ ∂(ENNReal.ofReal P • (AddCircle.haarAddCircle (T := P))), ∀ᵐ y ∂(volume : Measure UnforcedLeray.Space),
        (F : UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) (ε • y, θ) =
          a • Φ (rep θ, y) := by
      rw [← AddCircle.volume_eq_smul_haarAddCircle]
      exact hall0
    exact (Measure.ae_ennreal_smul_measure_iff (ENNReal.ofReal_pos.mpr hP0).ne').1 h'
  have hT : ∀ᵐ θ ∂(AddCircle.haarAddCircle (T := P)),
      ((testElem P 2 Φ : Yq P 2) θ : UnforcedLeray.Space → CVec3) =ᵐ[volume]
        fun y => Φ (rep θ, y) := by
    rw [testElem_of hΦ]
    filter_upwards [ContinuousMap.coeFn_toLp (E := Lp CVec3 2 (volume : Measure UnforcedLeray.Space))
      (p := 2) (μ := AddCircle.haarAddCircle (T := P)) (𝕜 := ℂ) (circleSlice hΦ)] with θ hθ
    rw [hθ]
    conv_lhs => rw [← hrep θ]
    rw [show (circleSlice hΦ) ((rep θ : ℝ) : AddCircle P) = sliceMap hΦ.2 (rep θ) from
      circleSlice_coe hΦ (rep θ)]
    exact MemLp.coeFn_toLp _
  apply Lp.ext
  filter_upwards [hU F, hall, hT,
    Lp.coeFn_smul ((((Real.sqrt P * ε ^ (3 / 2 : ℝ) : ℝ)) : ℂ) * a) (testElem P 2 Φ : Yq P 2)]
    with θ h1 h2 h3 h4
  rw [h4, Pi.smul_apply]
  apply Lp.ext
  filter_upwards [h1, h2, h3,
    Lp.coeFn_smul ((((Real.sqrt P * ε ^ (3 / 2 : ℝ) : ℝ)) : ℂ) * a)
      ((testElem P 2 Φ : Yq P 2) θ)] with y e1 e2 e3 e4
  rw [e1, e4, Pi.smul_apply, e3]
  simp only [e2]
  rw [smul_smul, Complex.ofReal_mul]

end UnforcedLeray.Short.PartIIa.N01
