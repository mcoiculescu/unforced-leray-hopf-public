import UnforcedLeray.Units.B0005.Bridge.Weak

/-!
# B0005 bridge, part 5: `div f = 0` in the two encodings

Blueprint unit B0005 (tex 141: `f ∈ 𝒴_{q,div}`) against `Blueprint/Package.lean`
(`IsY2Div.solenoidal : ∀ᵐ τ, IsSolenoidal (f τ)`, the compiled `IsSolenoidal` of
`Statement.lean` at almost every phase). For a real periodic field `f` (`IsY2`):

* `IsY2.isPhaseSolenoidal_of_ae`: `div f(τ) = 0` for a.e. `τ` gives `div (toY f) = 0` against
  scalar phase tests;
* `IsY2.ae_isSolenoidal_of_phase`: the converse. The quantifier over spatial tests is moved
  inside "almost every `τ`" with the closed subspace `Ksol ⊂ L²(ℝ³; ℂ³)` of solenoidal fields:
  `∫ θ(t) f(t) dt ∈ Ksol` for every time test `θ`, and the complementary orthogonal projection
  `C = 1 - P_Ksol` commutes with the Bochner integral, so `C f(t) = 0` for a.e. `t` by Mathlib's
  `ae_eq_zero_of_integral_contDiff_smul_eq_zero`;
* `IsY2.ae_isSolenoidal_iff`: the equivalence.

Status: infrastructure for the B0005 bridge. Theorem A is not proved in Lean.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.B0005

open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace

/-! ### Slices of scalar tests -/

section Slice

theorem fderiv_re_slice {φ : ℝ × Space → ℂ} (hd : Differentiable ℝ φ) (t : ℝ) (y : Space) :
    fderiv ℝ (fun x => (φ (t, x)).re) y =
      Complex.reCLM.comp ((fderiv ℝ φ (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ Space)) := by
  have h1 : HasFDerivAt (fun x => φ (t, x))
      ((fderiv ℝ φ (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ Space)) y :=
    (hd (t, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right t y)
  exact (Complex.reCLM.hasFDerivAt.comp y h1).fderiv

theorem fderiv_im_slice {φ : ℝ × Space → ℂ} (hd : Differentiable ℝ φ) (t : ℝ) (y : Space) :
    fderiv ℝ (fun x => (φ (t, x)).im) y =
      Complex.imCLM.comp ((fderiv ℝ φ (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ Space)) := by
  have h1 : HasFDerivAt (fun x => φ (t, x))
      ((fderiv ℝ φ (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ Space)) y :=
    (hd (t, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right t y)
  exact (Complex.imCLM.hasFDerivAt.comp y h1).fderiv

theorem dy_eq_re_add_im {φ : ℝ × Space → ℂ} (hd : Differentiable ℝ φ) (t : ℝ) (y : Space)
    (j : Fin 3) :
    dy j φ (t, y) = (spatialTestDerivative j (fun x => (φ (t, x)).re) y : ℂ) +
      Complex.I * (spatialTestDerivative j (fun x => (φ (t, x)).im) y : ℂ) := by
  simp only [spatialTestDerivative, fderiv_re_slice hd, fderiv_im_slice hd,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, Complex.reCLM_apply,
    Complex.imCLM_apply, dy]
  rw [mul_comm]
  exact (Complex.re_add_im _).symm

theorem hasCompactSupport_of_bound {G : Type*} [NormedAddCommGroup G] {u : Space → G} {R : ℝ}
    (hR : ∀ y, R < ‖y‖ → u y = 0) : HasCompactSupport u :=
  HasCompactSupport.intro (isCompact_closedBall (0 : Space) R) fun y hy => hR y (by
    simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hy)

theorem isSpatialTest_re_slice {P : ℝ} {φ : ℝ × Space → ℂ} (hφ : IsPhaseTest P φ) (t : ℝ) :
    IsSpatialTest (fun x => (φ (t, x)).re) where
  smooth := Complex.reCLM.contDiff.comp (hφ.smooth.comp (contDiff_const.prodMk contDiff_id))
  compact := by
    obtain ⟨R, hR⟩ := hφ.bounded_support
    exact hasCompactSupport_of_bound (R := R) fun y hy => by simp [hR t y hy]

theorem isSpatialTest_im_slice {P : ℝ} {φ : ℝ × Space → ℂ} (hφ : IsPhaseTest P φ) (t : ℝ) :
    IsSpatialTest (fun x => (φ (t, x)).im) where
  smooth := Complex.imCLM.contDiff.comp (hφ.smooth.comp (contDiff_const.prodMk contDiff_id))
  compact := by
    obtain ⟨R, hR⟩ := hφ.bounded_support
    exact hasCompactSupport_of_bound (R := R) fun y hy => by simp [hR t y hy]

theorem dotL_gradT_cplxL (φ : ℝ × Space → ℂ) (p : ℝ × Space) (v : Space) :
    dotL (gradT φ p) (cplxL v) = ∑ i : Fin 3, dy i φ p * (v i : ℂ) := by
  simp [gradT, dotL_apply]

/-- A solenoidal real field pairs to zero with the gradient of a scalar phase test, at every
phase. -/
theorem integral_dotL_gradT_eq_zero {P : ℝ} {φ : ℝ × Space → ℂ} (hφ : IsPhaseTest P φ)
    (t : ℝ) {v : SpatialField} (hv : IsSolenoidal v) :
    ∫ y, dotL (gradT φ (t, y)) (cplxL (v y)) = 0 := by
  have hd : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
  set u : Space → ℝ := fun x => (φ (t, x)).re
  set w : Space → ℝ := fun x => (φ (t, x)).im
  have hu := isSpatialTest_re_slice hφ t
  have hw := isSpatialTest_im_slice hφ t
  have hpt : ∀ y, dotL (gradT φ (t, y)) (cplxL (v y)) =
      ((∑ i : Fin 3, (v y) i * spatialTestDerivative i u y : ℝ) : ℂ) +
        Complex.I * ((∑ i : Fin 3, (v y) i * spatialTestDerivative i w y : ℝ) : ℂ) := by
    intro y
    rw [dotL_gradT_cplxL]
    simp only [dy_eq_re_add_im hd t y]
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [hpt]
  rw [integral_add (hv.integrable u hu).ofReal ((hv.integrable w hw).ofReal.const_mul _),
    integral_const_mul, integral_complex_ofReal, integral_complex_ofReal, hv.identity u hu,
    hv.identity w hw]
  simp

end Slice

/-! ### `⇐`: a.e. solenoidal slices give a phase-solenoidal element -/

section Forward

variable {𝒯 : ℝ} [hT : Fact (0 < 𝒯)] {f : ℝ → SpatialField}

theorem IsY2.isPhaseSolenoidal_of_ae (hf : IsY2 𝒯 f) (h : ∀ᵐ τ, IsSolenoidal (f τ)) :
    IsPhaseSolenoidal (toY 𝒯 f) := by
  intro φ hφ
  rw [phasePair_eq_periodIntegral hφ.gradT]
  have hz : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) (0 + 𝒯))),
      ∫ y, dotL (gradT φ (t, y)) ((toY 𝒯 f (t : AddCircle 𝒯) : Space → CVec3) y) = 0 := by
    refine ae_restrict_of_ae ?_
    filter_upwards [h, hf.toY_ae, hf.ae_pathOf_eq hT.out] with t ht ht' ht''
    rw [ht']
    rw [integral_congr_ae (g := fun y => dotL (gradT φ (t, y)) (cplxL (f t y))) (by
      filter_upwards [ht''] with y hy
      rw [hy]
      rfl)]
    exact integral_dotL_gradT_eq_zero hφ t ht
  rw [integral_congr_ae hz, integral_zero, smul_zero]

end Forward

/-! ### The solenoidal subspace of `L²(ℝ³; ℂ³)` -/

section Ksol

/-- `∇φ` of a real spatial test, complexified. -/
def gvec (φ : Space → ℝ) (y : Space) : CVec3 :=
  ∑ j : Fin 3, (spatialTestDerivative j φ y : ℂ) • EuclideanSpace.single j (1 : ℂ)

/-- The map `Dφ(y) ↦ ∇φ(y)`. -/
def gradOfFDeriv (D : Space →L[ℝ] ℝ) : CVec3 :=
  ∑ j : Fin 3, (D (coordinateVector j) : ℂ) • EuclideanSpace.single j (1 : ℂ)

theorem continuous_gradOfFDeriv : Continuous gradOfFDeriv := by
  unfold gradOfFDeriv
  refine continuous_finsetSum _ fun j _ => ?_
  exact (Complex.continuous_ofReal.comp
    ((ContinuousLinearMap.apply ℝ ℝ (coordinateVector j)).continuous)).smul continuous_const

theorem gvec_eq (φ : Space → ℝ) : gvec φ = gradOfFDeriv ∘ fderiv ℝ φ := rfl

theorem continuous_gvec {φ : Space → ℝ} (hφ : IsSpatialTest φ) : Continuous (gvec φ) := by
  rw [gvec_eq]
  exact continuous_gradOfFDeriv.comp (hφ.smooth.continuous_fderiv (by simp))

theorem hasCompactSupport_gvec {φ : Space → ℝ} (hφ : IsSpatialTest φ) :
    HasCompactSupport (gvec φ) := by
  rw [gvec_eq]
  exact (hφ.compact.fderiv (𝕜 := ℝ)).comp_left (by simp [gradOfFDeriv])

theorem memLp_gvec {φ : Space → ℝ} (hφ : IsSpatialTest φ) (r : ℝ≥0∞) :
    MemLp (gvec φ) r (volume : Measure Space) :=
  (continuous_gvec hφ).memLp_of_hasCompactSupport (hasCompactSupport_gvec hφ)

/-- The functional `g ↦ ∫ ∇φ · g` on `L²(ℝ³; ℂ³)`. -/
def ellS {φ : Space → ℝ} (hφ : IsSpatialTest φ) : Lp CVec3 2 (volume : Measure Space) →L[ℂ] ℂ :=
  innerPair 2 ((memLp_gvec hφ (conjExp 2)).toLp _)

theorem ellS_apply {φ : Space → ℝ} (hφ : IsSpatialTest φ) (g : Lp CVec3 2 (volume : Measure Space)) :
    ellS hφ g = ∫ y, dotL (gvec φ y) ((g : Space → CVec3) y) := by
  rw [ellS, innerPair_apply]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_gvec hφ (conjExp 2))] with y hy
  rw [hy]

/-- The closed subspace of solenoidal fields in `L²(ℝ³; ℂ³)` (real spatial tests). -/
def Ksol : Submodule ℂ (Lp CVec3 2 (volume : Measure Space)) where
  carrier := {v | ∀ φ (hφ : IsSpatialTest φ), ellS hφ v = 0}
  add_mem' := fun ha hb φ hφ => by rw [map_add, ha φ hφ, hb φ hφ, add_zero]
  zero_mem' := fun φ hφ => map_zero _
  smul_mem' := fun c v hv φ hφ => by rw [map_smul, hv φ hφ, smul_zero]

theorem isClosed_Ksol : IsClosed (Ksol : Set (Lp CVec3 2 (volume : Measure Space))) := by
  have h : (Ksol : Set (Lp CVec3 2 (volume : Measure Space))) =
      ⋂ φ : Space → ℝ, ⋂ hφ : IsSpatialTest φ, {v | ellS hφ v = 0} := by
    ext v
    simp [Ksol]
  rw [h]
  exact isClosed_iInter fun φ => isClosed_iInter fun hφ =>
    isClosed_eq (ellS hφ).continuous continuous_const

instance : CompleteSpace Ksol := isClosed_Ksol.completeSpace_coe

theorem dotL_gvec_cplxL (φ : Space → ℝ) (y v : Space) :
    dotL (gvec φ y) (cplxL v) = ((∑ i : Fin 3, v i * spatialTestDerivative i φ y : ℝ) : ℂ) := by
  rw [dotL_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [gvec, Pi.single_apply, mul_comm]

end Ksol

/-! ### `⇒`: a phase-solenoidal element has a.e. solenoidal slices -/

section Backward

variable {𝒯 : ℝ} [hT : Fact (0 < 𝒯)] {f : ℝ → SpatialField}

/-- The scalar product test `θ(t) φ(y)`, complexified. -/
def scalarTest (θ : ℝ → ℝ) (φ : Space → ℝ) (p : ℝ × Space) : ℂ := ((θ p.1 * φ p.2 : ℝ) : ℂ)

theorem contDiff_scalarTest {θ : ℝ → ℝ} {φ : Space → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (scalarTest θ φ) :=
  Complex.ofRealCLM.contDiff.comp ((hθ.comp contDiff_fst).mul (hφ.comp contDiff_snd))

theorem dy_scalarTest {θ : ℝ → ℝ} {φ : Space → ℝ} (hθ : ContDiff ℝ ∞ θ) (hφ : ContDiff ℝ ∞ φ)
    (j : Fin 3) (p : ℝ × Space) :
    dy j (scalarTest θ φ) p = ((θ p.1 * spatialTestDerivative j φ p.2 : ℝ) : ℂ) := by
  have hd := (contDiff_scalarTest hθ hφ).differentiable (by simp)
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  obtain ⟨t, y⟩ := p
  have e : dy j (scalarTest θ φ) (t, y) =
      fderiv ℝ (fun x => scalarTest θ φ (t, x)) y (coordinateVector j) := by
    simp only [dy, fderiv_slice_space (hd (t, y)), ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply]
  rw [e]
  have hfun : (fun x => scalarTest θ φ (t, x)) = fun x => Complex.ofRealCLM (θ t * φ x) := rfl
  have h2 : HasFDerivAt (fun x => Complex.ofRealCLM (θ t * φ x))
      (Complex.ofRealCLM.comp (θ t • fderiv ℝ φ y)) y :=
    Complex.ofRealCLM.hasFDerivAt.comp y (((hφd y).hasFDerivAt).const_mul (θ t))
  rw [hfun, h2.fderiv]
  simp [spatialTestDerivative]

theorem dotL_gradT_scalarTest {θ : ℝ → ℝ} {φ : Space → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (hφ : ContDiff ℝ ∞ φ) (p : ℝ × Space) (w : CVec3) :
    dotL (gradT (scalarTest θ φ) p) w = (θ p.1 : ℂ) * dotL (gvec φ p.2) w := by
  rw [dotL_apply, dotL_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [gradT, gvec, dy_scalarTest hθ hφ, Pi.single_apply]
  try ring

theorem gradT_perT {P : ℝ} (hP : 0 < P) {Ψ : ℝ × Space → ℂ} {A B : ℝ} (hΨ : TimeSupp A B Ψ)
    (hΨs : ContDiff ℝ ∞ Ψ) : gradT (perT P Ψ) = perT P (gradT Ψ) := by
  funext p₀
  have hidx : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {H : ℝ × Space → F},
      TimeSupp A B H → perT P H p₀ =
        ∑ k ∈ perIdx P A B (p₀.1 - 1) (p₀.1 + 1), H (p₀.1 + k * P, p₀.2) := fun hH =>
    perT_eq_sum hH _ p₀
      (fun k hk => mem_perIdx (a := p₀.1 - 1) (b := p₀.1 + 1) hP ⟨by linarith, by linarith⟩ hk)
  have hGT : TimeSupp A B (gradT Ψ) := fun τ y hτ => by
    simp [gradT, timeSupp_dy hΨ _ τ y hτ]
  simp only [gradT]
  simp_rw [dy_perT hP hΨ hΨs, hidx (timeSupp_dy hΨ _)]
  rw [hidx hGT]
  simp only [gradT, Finset.sum_smul]
  exact Finset.sum_comm

theorem isPhaseTest_scalarTest {θ : ℝ → ℝ} {φ : Space → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (hφ : IsSpatialTest φ) : IsPhaseTest 0 (scalarTest θ φ) where
  smooth := contDiff_scalarTest hθ hφ.smooth
  periodic := fun τ y => by simp
  bounded_support := by
    obtain ⟨R, hR⟩ := exists_bound_of_hasCompactSupport hφ.compact
    exact ⟨R, fun τ y hy => by simp [scalarTest, hR y hy]⟩

theorem integral_mem_Ksol (h : IsPhaseSolenoidal (toY 𝒯 f)) {θ : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ) :
    ∫ t, θ t • (toY 𝒯 f (t : AddCircle 𝒯) : Lp CVec3 2 (volume : Measure Space)) ∈ Ksol := by
  intro φ hφ
  have hloc := locallyIntegrable_comp_mk (toY 𝒯 f)
  have hint : Integrable (fun t => θ t • (toY 𝒯 f (t : AddCircle 𝒯) :
      Lp CVec3 2 (volume : Measure Space))) :=
    hloc.integrable_smul_left_of_hasCompactSupport hθ.continuous hθc
  have e1 : ellS hφ (∫ t, θ t • (toY 𝒯 f (t : AddCircle 𝒯) : Lp CVec3 2 (volume : Measure Space))) =
      ∫ t, θ t • ellS hφ (toY 𝒯 f (t : AddCircle 𝒯)) := by
    have := ((ellS hφ).restrictScalars ℝ).integral_comp_comm hint
    simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.map_smul_of_tower]
      at this
    exact this.symm
  rw [e1]
  obtain ⟨A, B, hAB, hθAB⟩ := exists_Icc_of_hasCompactSupport hθc
  have hΨ0 := isPhaseTest_scalarTest hθ hφ
  have hΨT : TimeSupp A B (scalarTest θ φ) := fun τ y hτ => by simp [scalarTest, hθAB τ hτ]
  have hG0 : IsPhaseTest 0 (gradT (scalarTest θ φ)) := hΨ0.gradT
  have hGT : TimeSupp A B (gradT (scalarTest θ φ)) := fun τ y hτ => by
    simp [gradT, timeSupp_dy hΨT _ τ y hτ]
  have hz := h _ (isPhaseTest_perT hT.out hΨT hΨ0)
  rw [gradT_perT hT.out hΨT hΨ0.smooth, PhaseTrace.phasePair_perT hG0 hAB hGT] at hz
  have hz' : ∫ t, pairH hG0 (toY 𝒯 f) t = 0 := by
    rcases smul_eq_zero.mp hz with h0 | h0
    · exact absurd h0 (inv_ne_zero hT.out.ne')
    · exact h0
  rw [← hz']
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only
  rw [pairH_eq, ellS_apply, Complex.real_smul, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [dotL_gradT_scalarTest hθ hφ.smooth]

/-- The complementary projection `C = 1 - P_Ksol`; `C v = 0` iff `v ∈ Ksol`. -/
def compKsol : Lp CVec3 2 (volume : Measure Space) →L[ℂ] Lp CVec3 2 (volume : Measure Space) :=
  ContinuousLinearMap.id ℂ _ - Ksol.starProjection

theorem compKsol_eq_zero_iff (v : Lp CVec3 2 (volume : Measure Space)) :
    compKsol v = 0 ↔ v ∈ Ksol := by
  rw [compKsol, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, sub_eq_zero, eq_comm,
    Submodule.starProjection_eq_self_iff]

theorem ae_mem_Ksol (h : IsPhaseSolenoidal (toY 𝒯 f)) :
    ∀ᵐ t : ℝ, (toY 𝒯 f (t : AddCircle 𝒯) : Lp CVec3 2 (volume : Measure Space)) ∈ Ksol := by
  have hloc := locallyIntegrable_comp_mk (toY 𝒯 f)
  set C := compKsol.restrictScalars ℝ with hC
  have hlocC : LocallyIntegrable (fun t : ℝ => C (toY 𝒯 f (t : AddCircle 𝒯))) volume :=
    locallyIntegrableOn_univ.mp (C.locallyIntegrableOn_comp (locallyIntegrableOn_univ.mpr hloc))
  have hzero : ∀ᵐ t : ℝ, C (toY 𝒯 f (t : AddCircle 𝒯)) = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hlocC fun θ hθ hθc => ?_
    have hint : Integrable (fun t => θ t • (toY 𝒯 f (t : AddCircle 𝒯) :
        Lp CVec3 2 (volume : Measure Space))) :=
      hloc.integrable_smul_left_of_hasCompactSupport hθ.continuous hθc
    have := C.integral_comp_comm hint
    simp only [ContinuousLinearMap.map_smul] at this
    rw [this, hC, ContinuousLinearMap.coe_restrictScalars',
      compKsol_eq_zero_iff]
    exact integral_mem_Ksol h hθ hθc
  filter_upwards [hzero] with t ht
  exact (compKsol_eq_zero_iff _).mp ht

theorem reL_cplxL (v : Space) : reL (cplxL v) = v := by
  ext i; simp

/-- **`IsY2Div.solenoidal` from the phase model**: `div (toY f) = 0` against scalar phase tests
gives `IsSolenoidal (f τ)` for almost every `τ`. -/
theorem IsY2.ae_isSolenoidal_of_phase (hf : IsY2 𝒯 f) (h : IsPhaseSolenoidal (toY 𝒯 f)) :
    ∀ᵐ τ : ℝ, IsSolenoidal (f τ) := by
  filter_upwards [ae_mem_Ksol h, hf.toY_ae, hf.ae_pathOf_eq hT.out,
    hf.ae_memLp_slice hT.out] with t hK ht ht' hm
  have hmf : MemLp (f t) 2 (volume : Measure Space) :=
    (reL.comp_memLp' hm).ae_eq (Eventually.of_forall fun y => reL_cplxL (f t y))
  have hder : ∀ φ : Space → ℝ, IsSpatialTest φ → ∀ i : Fin 3,
      MemLp (spatialTestDerivative i φ) 2 (volume : Measure Space) := fun φ hφ i =>
    ((hφ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hφ.compact.fderiv_apply (𝕜 := ℝ) _)
  have hintg : ∀ φ : Space → ℝ, IsSpatialTest φ →
      Integrable (fun x => ∑ i : Fin 3, (f t x) i * spatialTestDerivative i φ x) := by
    intro φ hφ
    refine integrable_finsetSum _ fun i _ => ?_
    have h1 : MemLp (fun x => (f t x) i) 2 (volume : Measure Space) :=
      (EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp_memLp' hmf
    exact h1.integrable_mul (hder φ hφ i)
  refine ⟨hintg, fun φ hφ => ?_⟩
  have h0 := hK φ hφ
  rw [ellS_apply, ht] at h0
  rw [integral_congr_ae (g := fun y => dotL (gvec φ y) (cplxL (f t y))) (by
    filter_upwards [ht'] with y hy
    rw [hy]
    rfl)] at h0
  simp_rw [dotL_gvec_cplxL] at h0
  rw [integral_complex_ofReal, Complex.ofReal_eq_zero] at h0
  exact h0

/-- **The solenoidal clauses agree**: `∀ᵐ τ, IsSolenoidal (f τ)` iff `div (toY f) = 0` in the
phase model. -/
theorem IsY2.ae_isSolenoidal_iff (hf : IsY2 𝒯 f) :
    (∀ᵐ τ : ℝ, IsSolenoidal (f τ)) ↔ IsPhaseSolenoidal (toY 𝒯 f) :=
  ⟨hf.isPhaseSolenoidal_of_ae, hf.ae_isSolenoidal_of_phase⟩

end Backward

end UnforcedLeray.B0005
