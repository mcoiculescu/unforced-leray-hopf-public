import UnforcedLeray.Short.PartIIb.Sub.R1
import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedFieldAE
import UnforcedLeray.Units.B0415.Commute

/-!
# Part II-b, task `PartII-b:R1/3`: the Leray projection on the force space (conditional)

Target (`Sub/R1.lean`, `def LerayOnForce`): `theorem lerayOnForce_proof : LerayOnForce`.
Source of record: `the November 2 reference manuscript`, lines 2042-2046 and 2519-2524
(`g = 𝔓F` in the force space `Y = Y_{q₀,σ} ∩ real ∩ 𝒪`-invariant), `paper/main.tex` lines 5085 and
5385.

This file proves, with no extra hypothesis, every part of `LerayOnForce` except the phase-pairing
identity `⟪Φ, 𝔓f⟫ = ⟪Φ, f⟫` for solenoidal phase tests `Φ` (`LerayPhaseSymm`):

* `lerayY_mem_realSub`: the Leray projection of a real field is real (`realSub`);
* `lerayY_mem_Ysigma`: its phase slices are solenoidal (`lerayY_isPhaseSolenoidal`);
* `lerayY_mem_Osym`: it is `𝒪`-invariant (`act = actY`, then `lerayY_actY`);
* the bound `‖𝔓f‖ ≤ (‖𝔓_{ℂ³}‖ + 1) ‖f‖`, with `K` independent of the period;
* `lerayOnForce_of_phaseSymm`: `LerayOnForce` from the Y-level Prop `LerayPhaseSymm`.

`LerayPhaseSymm` is the self-adjointness of `𝔓` against solenoidal phase tests. It is reduced
(see the end of the file) to two slice-level facts, `LerayCTranspose` (complex transpose of the
spatial Leray projection) and `SolSliceFixed` (`𝔓φ = φ` for a smooth compactly supported
pointwise divergence-free `φ`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.RieszLp
  UnforcedLeray.B0412

/-! ## Step 1: the action `act` on `Y_q` is `actY` -/

/-- `gC g = actV g` on `ℂ³`: both are the complexification of the isometry `g`. -/
theorem gC_eq_actV (g : Space ≃ₗᵢ[ℝ] Space) :
    UnforcedLeray.B0412.gC g = UnforcedLeray.B0415.actV g := by
  refine ContinuousLinearMap.ext fun v => ?_
  have hR : ∀ x : Space, UnforcedLeray.B0412.realC x = ofReV x := fun x =>
    congrFun realC_eq_ofReV x
  have hgR : ∀ x : Space, UnforcedLeray.B0412.gC g (ofReV x) = ofReV (g x) := by
    intro x
    rw [← hR x, UnforcedLeray.B0412.gC_realC, hR (g x)]
  have hsplit : v = ofReV (reV v) + Complex.I • ofReV (imV v) := by
    have h := ofReV_reV_add_ofImV_imV v
    rw [← I_smul_ofReV] at h
    exact h.symm
  conv_lhs => rw [hsplit]
  rw [map_add, map_smul, hgR, hgR, UnforcedLeray.B0415.actV_apply, complexifyIso_apply,
    ← I_smul_ofReV]

/-- The two actions of `g` on `Y_q` agree: `act P q g = actY P q g`. -/
theorem act_eq_actY (P : ℝ) [Fact (0 < P)] (q : ℝ≥0∞) [Fact (1 ≤ q)] (g : Space ≃ₗᵢ[ℝ] Space) :
    UnforcedLeray.B0412.act P q g = UnforcedLeray.B0415.actY P q g := by
  unfold UnforcedLeray.B0412.act UnforcedLeray.B0415.actY UnforcedLeray.B0412.spatialAct
    UnforcedLeray.B0415.actLp
  rw [gC_eq_actV]

/-! ## Step 2: `𝔓` commutes with the `𝒪`-action -/

/-- If `f` is fixed by `g`, so is `𝔓f`. -/
theorem act_lerayY_eq (P : ℝ) [Fact (0 < P)] (g : Space ≃ₗᵢ[ℝ] Space) (f : Yq P q0E)
    (hf : act P q0E g f = f) :
    act P q0E g (lerayY P q0E one_lt_q0E q0E_ne_top f) =
      lerayY P q0E one_lt_q0E q0E_ne_top f := by
  rw [act_eq_actY, ← UnforcedLeray.B0415.lerayY_actY one_lt_q0E q0E_ne_top g f, ← act_eq_actY, hf]

/-- `𝔓` maps `𝒪`-invariant elements of `Y_{q₀}` to `𝒪`-invariant elements (`mem_Osym`). -/
theorem lerayY_mem_Osym (P : ℝ) [Fact (0 < P)] (f : Yq P q0E) (hf : f ∈ Osym P q0E) :
    lerayY P q0E one_lt_q0E q0E_ne_top f ∈ Osym P q0E :=
  mem_Osym.2 fun g hg => act_lerayY_eq P g f (mem_Osym.1 hf g hg)

/-! ## Step 3: solenoidal values -/

/-- `𝔓f` has solenoidal phase slices (`lerayY_isPhaseSolenoidal`). -/
theorem lerayY_mem_Ysigma (P : ℝ) [Fact (0 < P)] (f : Yq P q0E) :
    lerayY P q0E one_lt_q0E q0E_ne_top f ∈ UnforcedLeray.B0411.Ysigma P q0E :=
  UnforcedLeray.B0411.mem_Ysigma.2 (lerayY_isPhaseSolenoidal one_lt_q0E q0E_ne_top f)

/-! ## Step 4: the real structure -/

/-- The real slice projection `F ↦ ofReV (reV F)` commutes with `𝔓` on `L^{q₀}(ℝ³;ℂ³)`. -/
theorem lerayC_realSliceProjection (F : Lp CVec3 q0E (volume : Measure Space)) :
    lerayC q0E one_lt_q0E q0E_ne_top (realSliceProjection (q := q0E) F) =
      realSliceProjection (q := q0E) (lerayC q0E one_lt_q0E q0E_ne_top F) := by
  have h1 : realSliceProjection (q := q0E) F =
      ofReV.compLpL q0E volume (reV.compLpL q0E volume F) := rfl
  have h2 : realSliceProjection (q := q0E) (lerayC q0E one_lt_q0E q0E_ne_top F) =
      ofReV.compLpL q0E volume
        (lerayLp q0E one_lt_q0E q0E_ne_top (reV.compLpL q0E volume F)) := by
    show ofReV.compLpL q0E volume
      (reV.compLpL q0E volume (lerayC q0E one_lt_q0E q0E_ne_top F)) = _
    rw [UnforcedLeray.B0414.reV_lerayC]
  rw [h1, h2, lerayC_ofRe]

/-- The slice-wise commutation hypothesis of `lerayY_comm_slicewise`. -/
theorem lerayC_comp_realSliceProjection :
    ((lerayC q0E one_lt_q0E q0E_ne_top).restrictScalars ℝ).comp
        (realSliceProjection (q := q0E)) =
      (realSliceProjection (q := q0E)).comp
        ((lerayC q0E one_lt_q0E q0E_ne_top).restrictScalars ℝ) := by
  ext1 F
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars']
  exact lerayC_realSliceProjection F

/-- `𝔓` commutes with the real phase projection `realPhaseProjection` on `Y_{q₀}`. -/
theorem lerayY_realPhaseProjection (P : ℝ) [Fact (0 < P)] (f : Yq P q0E) :
    lerayY P q0E one_lt_q0E q0E_ne_top (realPhaseProjection f) =
      realPhaseProjection (lerayY P q0E one_lt_q0E q0E_ne_top f) := by
  have h := lerayY_comm_slicewise (P := P) one_lt_q0E q0E_ne_top
    (realSliceProjection (q := q0E)) lerayC_comp_realSliceProjection
  have h' := congrArg (fun T : Yq P q0E →L[ℝ] Yq P q0E => T f) h
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars'] at h'
  exact h'

/-- A fixed point of `realPhaseProjection` is real. -/
theorem mem_realSub_of_fixed (P : ℝ) [Fact (0 < P)] (w : Yq P q0E)
    (h : w = realPhaseProjection w) : w ∈ realSub P q0E := by
  rw [mem_realSub]
  intro φ hφ
  have hfun : (fun x : ℝ × Space => UnforcedLeray.B0412.realC (φ x)) =
      fun x => ofReV (φ x) := by
    funext x
    exact congrFun realC_eq_ofReV (φ x)
  have hw : phasePair P q0E (fun x => ofReV (φ x)) w =
      phasePair P q0E (fun x => ofReV (φ x)) (realPhaseProjection w) := by
    rw [← h]
  have e := phasePair_realPhaseProjection_of_realTest (P := P) (q := q0E) φ hφ w
  rw [hfun, hw, e, Complex.ofReal_im]

/-- The Leray projection of a real element of `Y_{q₀}` is real. -/
theorem lerayY_mem_realSub (P : ℝ) [Fact (0 < P)] (f : Yq P q0E) (hf : f ∈ realSub P q0E) :
    lerayY P q0E one_lt_q0E q0E_ne_top f ∈ realSub P q0E := by
  have hf' : f = realPhaseProjection f := realPhaseProjection_eq_of_realSub f hf
  refine mem_realSub_of_fixed P _ ?_
  calc lerayY P q0E one_lt_q0E q0E_ne_top f
      = lerayY P q0E one_lt_q0E q0E_ne_top (realPhaseProjection f) := by rw [← hf']
    _ = realPhaseProjection (lerayY P q0E one_lt_q0E q0E_ne_top f) :=
        lerayY_realPhaseProjection P f

/-! ## Step 5: the self-adjointness identity (missing from the library) and the conditional target -/

/-- **The missing Y-level identity.** `𝔓` is self-adjoint for the phase pairing against solenoidal
phase tests: `⟪Φ, 𝔓f⟫ = ⟪Φ, f⟫` for every period `P`, every solenoidal phase test `Φ`
(`IsSolTest`) and every `f ∈ Y_{q₀}`. This is `⟪𝔓Φ, f⟫ = ⟪Φ, f⟫` with `𝔓Φ = Φ` on solenoidal
slices. The library has the real `L^p` duality `RieszLp.integral_inner_lerayLp_symm` and
`RieszLp.lerayLp_eq_self`, but not the complex phase-level form. -/
def LerayPhaseSymm : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (Φ : ℝ × Space → CVec3) (f : Yq P q0E),
    IsSolTest P Φ →
      phasePair P q0E Φ (lerayY P q0E one_lt_q0E q0E_ne_top f) = phasePair P q0E Φ f

/-- **The conditional target.** `LerayOnForce` follows from `LerayPhaseSymm`, with the constant
`K = ‖𝔓_{ℂ³}‖ + 1` (independent of the period, by `norm_lerayY_le`). -/
theorem lerayOnForce_of_phaseSymm (hS : LerayPhaseSymm) : LerayOnForce := by
  refine ⟨‖lerayC q0E one_lt_q0E q0E_ne_top‖ + 1, by positivity, fun p f hr ho => ?_⟩
  have hbound : ‖lerayY p.period q0E one_lt_q0E q0E_ne_top f‖ ≤
      (‖lerayC q0E one_lt_q0E q0E_ne_top‖ + 1) * ‖f‖ := by
    have h2 : ‖lerayY p.period q0E one_lt_q0E q0E_ne_top‖ ≤
        ‖lerayC q0E one_lt_q0E q0E_ne_top‖ :=
      norm_lerayY_le (P := p.period) one_lt_q0E q0E_ne_top
    have h1 := (lerayY p.period q0E one_lt_q0E q0E_ne_top).le_opNorm f
    have h3 : ‖lerayY p.period q0E one_lt_q0E q0E_ne_top‖ * ‖f‖ ≤
        (‖lerayC q0E one_lt_q0E q0E_ne_top‖ + 1) * ‖f‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    exact h1.trans h3
  refine ⟨⟨lerayY p.period q0E one_lt_q0E q0E_ne_top f,
    (mem_forceSpace p.period).2 ⟨lerayY_mem_realSub p.period f hr,
      lerayY_mem_Ysigma p.period f, lerayY_mem_Osym p.period f ho⟩⟩, ?_, ?_⟩
  · exact hbound
  · intro Φ hΦ
    exact hS p.period Φ f hΦ

/-! ## Step 6: `LerayPhaseSymm` from two slice-level facts -/

/-- The conjugate exponent of `q₀ = 11/4` is `> 1`. -/
theorem one_lt_conjExp_q0E : 1 < conjExp q0E := by
  unfold conjExp
  rw [ENNReal.one_lt_inv]
  have h1 : q0E⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 q0E_ne_top
  exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero h1

/-- The conjugate exponent of `q₀ = 11/4` is finite. -/
theorem conjExp_q0E_ne_top : conjExp q0E ≠ ⊤ := by
  unfold conjExp
  rw [Ne, ENNReal.inv_eq_top, tsub_eq_zero_iff_le, not_le]
  exact ENNReal.inv_lt_one.2 one_lt_q0E

/-- **Leaf `PartII-b:R1/3/1`: the complex transpose of the spatial Leray projection**
(SP 2042-2046 and 2519-2524, `paper/main.tex` 7336-7344, B0414). The complexification
`lerayC = 𝔓 ⊗ ℂ` of the real Leray projection is symmetric for the bilinear (non-conjugated) dot
pairing between `L^{q₀'}(ℝ³;ℂ³)` and `L^{q₀}(ℝ³;ℂ³)`:
`∫ G · 𝔓_{q₀}F = ∫ 𝔓_{q₀'}G · F`. Route: split `F, G` into real and imaginary parts
(`lerayC_apply`, `lerayC_ofRe`) and apply `RieszLp.integral_inner_lerayLp_symm`
(`Lib/LerayLp/Duality.lean`) to each of the four real pairings. -/
def LerayCTranspose : Prop :=
  ∀ (G : Lp CVec3 (conjExp q0E) (volume : Measure Space))
    (F : Lp CVec3 q0E (volume : Measure Space)),
    ∫ y, dotL (G y) (lerayC q0E one_lt_q0E q0E_ne_top F y) =
      ∫ y, dotL (lerayC (conjExp q0E) one_lt_conjExp_q0E conjExp_q0E_ne_top G y) (F y)

/-- **Leaf `PartII-b:R1/3/2`: `𝔓` fixes smooth compactly supported divergence-free fields**
(SP 2519-2524, `paper/main.tex` 7364-7387, B0439/B0797). If `φ : ℝ³ → ℂ³` is `C^∞`, compactly
supported and `∑ⱼ ∂ⱼφⱼ = 0` pointwise, then (as an element of `L^{q₀'}`) `𝔓_{q₀'}φ = φ`.
Route: pointwise divergence-free + compact support gives `IsSolenoidalC φ` by integration by parts
(`B0414.IsSolenoidalC`, `isSolenoidalC_iff` in `Units/B0414/Orthogonal.lean`), then
`RieszLp.lerayLp_eq_self` (`Lib/LerayLp/Helmholtz.lean`) on the real and imaginary parts and
`lerayC_apply`. -/
def SolSliceFixed : Prop :=
  ∀ (φ : Space → CVec3), ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∀ y, ∑ j : Fin 3, fderiv ℝ φ y (coordinateVector j) j = 0) →
    ∀ hm : MemLp φ (conjExp q0E) volume,
      lerayC (conjExp q0E) one_lt_conjExp_q0E conjExp_q0E_ne_top (hm.toLp φ) = hm.toLp φ

theorem lps_testElem_ae {P : ℝ} [Fact (0 < P)] {r : ℝ≥0∞} [Fact (1 ≤ r)]
    {Φ : ℝ × Space → CVec3} (hΦ : IsSliceTest P r Φ) :
    ⇑(testElem P r Φ) =ᵐ[AddCircle.haarAddCircle (T := P)] ⇑(circleSlice hΦ) := by
  rw [testElem_of hΦ]
  exact ContinuousMap.coeFn_toLp _ _

theorem lerayY_fderiv_slice (Φ : ℝ × Space → CVec3) (hΦ : ContDiff ℝ ∞ Φ) (t : ℝ)
    (y v : Space) :
    fderiv ℝ (fun z : Space => Φ (t, z)) y v = fderiv ℝ Φ (t, y) (0, v) := by
  have hd : DifferentiableAt ℝ Φ (t, y) := (hΦ.differentiable (by simp)).differentiableAt
  have h := hd.hasFDerivAt.comp y (hasFDerivAt_prodMk_right (𝕜 := ℝ) t y)
  rw [show (fun z : Space => Φ (t, z)) = Φ ∘ (fun z : Space => (t, z)) from rfl, h.fderiv]
  rfl

/-- `LerayPhaseSymm` follows from the slice-level transpose identity and the fixed-point property:
every slice of a solenoidal phase test is smooth, compactly supported and pointwise
divergence-free, so `𝔓_{q₀'}` fixes it, and then `⟪Φ(τ), 𝔓f(τ)⟫ = ⟪𝔓Φ(τ), f(τ)⟫ = ⟪Φ(τ), f(τ)⟫`. -/
theorem leraySymm_of (hT : LerayCTranspose) (hF : SolSliceFixed) : LerayPhaseSymm := by
  intro P _ Φ f hΦ
  have hS : IsSliceTest P (conjExp q0E) Φ := hΦ.1.isSliceTest (conjExp q0E)
  have hfix : ∀ x : AddCircle P,
      lerayC (conjExp q0E) one_lt_conjExp_q0E conjExp_q0E_ne_top (circleSlice hS x) =
        circleSlice hS x := by
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H t =>
      rw [circleSlice_coe]
      unfold sliceMap
      refine hF (fun y => Φ (t, y)) ?_ ?_ ?_ (hS.2.memLp t)
      · exact hΦ.1.smooth.comp (contDiff_const.prodMk contDiff_id)
      · obtain ⟨R, hR⟩ := hΦ.1.bounded_support
        refine HasCompactSupport.intro (isCompact_closedBall (0 : Space) R) fun y hy => ?_
        exact hR t y (by simpa using hy)
      · intro y
        have h := hΦ.2 (t, y)
        simp only [dy] at h
        simp only [lerayY_fderiv_slice Φ hΦ.1.smooth t y]
        exact h
  unfold phasePair
  rw [phasePairing_apply, phasePairing_apply]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_lerayY (P := P) one_lt_q0E q0E_ne_top f, lps_testElem_ae hS] with x h1 h2
  rw [h1, h2, innerPair_apply, innerPair_apply, hT, hfix]

/-- **The conditional target of `PartII-b:R1/3`**: `LerayOnForce` from the two slice-level leaves. -/
theorem lerayOnForce_of (hT : LerayCTranspose) (hF : SolSliceFixed) : LerayOnForce :=
  lerayOnForce_of_phaseSymm (leraySymm_of hT hF)

end UnforcedLeray.Short.IIb
