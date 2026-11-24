import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedPotentialJointSmooth
import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedPotential
import UnforcedLeray.Lib.PhaseSpace.ExtendedTest
import UnforcedLeray.Lib.CZL2.TestOffSupport

/-!
# `PartII-b:T10/org/3/2/1`: the smooth Leray projection of a phase test

Source of record `the November 2 reference manuscript`:
lines 119-120 (`𝔓 = ℙ` is the Cartesian Leray projection and `R_j = ∂_j(-Δ)^{-1/2}`, so
`ℙΦ = Φ + ∇(-Δ)^{-1} div Φ = Φ + ∇(N ∗ div Φ)` with `N(z) = 1/(4π|z|)`), line 1364 ("its projected
inverse is obtained by applying Cartesian Leray projection to `f`"), lines 1474-1475 ("Leray
commutes with heat, dilation and phase translation, so projection preserves all identities"),
lines 1498-1500 (graph elements have representatives in `C(ℝ/Pℤ; L^r)`).

`lerayTest2 Φ` is a concrete smooth representative of the slice-wise Leray projection
`ℙΦ(τ) = Φ(τ) + ∇(N ∗ div Φ(τ))` of a complex phase test `Φ`: the real and imaginary parts are
projected separately, through the joint Newton potentials `newtonJoint` of the real scalar phase
tests `div Re Φ = projectedPotentialReDiv Φ` and `div Im Φ = projectedPotentialImDiv Φ`.  The
existing slice-wise projection `lerayProjectedPhaseTest` (`Cons/L2/BackgroundConcrete/ProjectedTest`)
is only an a.e. `L^r` representative; `lerayTest2` agrees with it slice by slice a.e.
(`lerayTest2_slice` with `lerayProjectedPhaseTest_eq_newtonPotentialGrad_ae`, `testElem_lerayTest2`).

Proved here (no hypotheses): the parameter form and smoothness of `newtonJoint`
(`newtonJoint_eq_param`, `contDiff_newtonJoint`), joint-versus-slice derivatives
(`fderiv_slice_real`, `slice_dy_real`), real symmetry of second derivatives
(`fderiv_apply_comm_real`, `dτ_dy_comm_real`), smoothness and periodicity of `lerayTest2`, its slice
formula, and the identification of its `Y_{2'}` test element with that of the slice-wise Leray
projection.

The leaves, stated as `Prop`s and consumed by `UnforcedLeray.Short.IIb.lerayTestSchwartz_of`
(`Sub/PartII-b_T10_org_3_2_1_of.lean`), are `DecayOfFarBound`, `NewtonJointFDeriv`,
`NewtonHessFar` and `PhasePairLerayY`.  Everything here lives in the namespace
`UnforcedLeray.Short.IIb.LTS`, so that it cannot clash with the sibling decomposition of
`LerayTestComm` (namespace `UnforcedLeray.Short.IIb.LTC`) when both are imported.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIb.LTS

open UnforcedLeray.PhaseSpace UnforcedLeray.RieszLp UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PressureAnalysis

/-! ### The dual exponent `2' = 2` -/

theorem conjExp_two : conjExp 2 = 2 := by
  simp [conjExp, ENNReal.one_sub_inv_two]

theorem one_lt_conjExp_two : 1 < conjExp 2 := by
  rw [conjExp_two]
  exact ENNReal.one_lt_two

theorem conjExp_two_ne_top : conjExp 2 ≠ ⊤ := by
  rw [conjExp_two]
  exact ENNReal.ofNat_ne_top

theorem toReal_conjExp_two : (conjExp 2).toReal = 2 := by
  rw [conjExp_two]
  rfl

/-! ### The joint Newton potential of a real scalar phase test -/

/-- The joint Newton potential `(τ, y) ↦ (N ∗ D(τ, ·))(y) = ∫ N(y - x) D(τ, x) dx`,
`N(z) = 1/(4π|z|)`, of a real scalar phase test `D` (source lines 119-120: `(-Δ)^{-1} = N ∗`). -/
def newtonJoint (D : ℝ × Space → ℝ) : ℝ × Space → ℝ :=
  fun p => newtonConv (fun x => D (p.1, x)) p.2

/-- The parameter-integral form `∫ N(x) D(p - (0, x)) dx` of the joint Newton potential. -/
theorem newtonJoint_eq_param (D : ℝ × Space → ℝ) (p : ℝ × Space) :
    newtonJoint D p = ∫ x, newtonPotential x * D (p - (0, x)) := by
  have h := integral_sub_left_eq_self
    (fun t : Space => newtonPotential (p.2 - t) * D (p.1, t)) (volume : Measure Space) p.2
  simp only [sub_sub_cancel] at h
  show ∫ y, newtonPotential (p.2 - y) * D (p.1, y) = _
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have hp : p - ((0 : ℝ), x) = (p.1, p.2 - x) := by ext <;> simp
  simp only [hp]

/-- The joint Newton potential of a phase test is smooth in `(τ, y)`. -/
theorem contDiff_newtonJoint {P : ℝ} {D : ℝ × Space → ℝ} (hD : IsPhaseTest P D) :
    ContDiff ℝ ∞ (newtonJoint D) := by
  have he : newtonJoint D = fun p => ∫ x, newtonPotential x * D (p - (0, x)) :=
    funext (newtonJoint_eq_param D)
  rw [he]
  exact contDiff_newtonSourceParamIntegral hD

theorem newtonJoint_periodic {P : ℝ} {D : ℝ × Space → ℝ} (hD : IsPhaseTest P D) :
    ∀ τ y, newtonJoint D (τ + P, y) = newtonJoint D (τ, y) := by
  intro τ y
  have h : (fun x => D (τ + P, x)) = fun x => D (τ, x) := funext fun x => hD.periodic τ x
  show newtonConv (fun x => D (τ + P, x)) y = newtonConv (fun x => D (τ, x)) y
  rw [h]

/-- The slice of a scalar phase test is a compact smooth spatial test. -/
theorem isSpatialTest_slice {P : ℝ} {D : ℝ × Space → ℝ} (hD : IsPhaseTest P D) (τ : ℝ) :
    IsSpatialTest (fun x => D (τ, x)) :=
  ⟨hD.smooth.comp (contDiff_const.prodMk contDiff_id), hD.hasCompactSupport_slice τ⟩

/-! ### Joint and slice derivatives of real functions -/

/-- Derivative of a real function along a phase slice. -/
theorem fderiv_slice_real {F : ℝ × Space → ℝ} {τ : ℝ} {y : Space}
    (hF : DifferentiableAt ℝ F (τ, y)) (v : Space) :
    fderiv ℝ (fun x : Space => F (τ, x)) y v = fderiv ℝ F (τ, y) (0, v) := by
  have hcomp := hF.hasFDerivAt.comp y (hasFDerivAt_prodMk_right τ y)
  have heq := hcomp.fderiv
  change fderiv ℝ (fun x : Space => F (τ, x)) y = _ at heq
  rw [heq]
  simp

/-- The slice of `∂ⱼF` is the coordinate derivative of the slice of `F`. -/
theorem slice_dy_real {F : ℝ × Space → ℝ} (hF : Differentiable ℝ F) (k : Fin 3) (τ : ℝ) :
    (fun x : Space => dy k F (τ, x)) = spatialTestDerivative k (fun x => F (τ, x)) := by
  funext x
  exact (fderiv_slice_real (hF (τ, x)) (coordinateVector k)).symm

theorem contDiff_dy_real {F : ℝ × Space → ℝ} (hF : ContDiff ℝ ∞ F) (k : Fin 3) :
    ContDiff ℝ ∞ (dy k F) :=
  (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem contDiff_dτ_real {F : ℝ × Space → ℝ} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (dτ F) :=
  (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem fderiv_apply_formula_real {F : ℝ × Space → ℝ} (hF : ContDiff ℝ ∞ F)
    (v w p : ℝ × Space) :
    fderiv ℝ (fun p => fderiv ℝ F p w) p v = fderiv ℝ (fderiv ℝ F) p v w := by
  have hd : Differentiable ℝ (fderiv ℝ F) :=
    (hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have hx : HasFDerivAt (fun y => fderiv ℝ F y w) ((fderiv ℝ (fderiv ℝ F) p).flip w) p := by
    simpa using (hd p).hasFDerivAt.clm_apply (hasFDerivAt_const w p)
  rw [hx.fderiv]
  rfl

/-- Symmetry of second derivatives of a smooth real function on `ℝ × ℝ³`. -/
theorem fderiv_apply_comm_real {F : ℝ × Space → ℝ} (hF : ContDiff ℝ ∞ F) (v w p : ℝ × Space) :
    fderiv ℝ (fun p => fderiv ℝ F p w) p v = fderiv ℝ (fun p => fderiv ℝ F p v) p w := by
  rw [fderiv_apply_formula_real hF v w p, fderiv_apply_formula_real hF w v p]
  exact (hF.contDiffAt.isSymmSndFDerivAt (by simp)).eq v w

theorem dτ_dy_comm_real {F : ℝ × Space → ℝ} (hF : ContDiff ℝ ∞ F) (k : Fin 3) :
    dτ (dy k F) = dy k (dτ F) :=
  funext fun p => fderiv_apply_comm_real hF _ _ p

/-- A function vanishing for `|y| > R` has vanishing derivative there. -/
theorem fderiv_eq_zero_of_far {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {D : ℝ × Space → F} {R : ℝ} (hR : ∀ τ y, R < ‖y‖ → D (τ, y) = 0) {τ : ℝ} {y : Space}
    (hy : R < ‖y‖) : fderiv ℝ D (τ, y) = 0 := by
  have hev : D =ᶠ[𝓝 ((τ, y) : ℝ × Space)] fun _ => 0 := by
    have hopen : IsOpen {p : ℝ × Space | R < ‖p.2‖} :=
      isOpen_lt continuous_const (continuous_norm.comp continuous_snd)
    filter_upwards [hopen.mem_nhds (show R < ‖((τ, y) : ℝ × Space).2‖ from hy)] with p hp
    exact hR p.1 p.2 hp
  simp [hev.fderiv_eq]

/-- The joint `∂ₖ` of the Newton potential is the slice coordinate derivative. -/
theorem dy_newtonJoint_eq {P : ℝ} {D : ℝ × Space → ℝ} (hD : IsPhaseTest P D) (k : Fin 3)
    (τ : ℝ) (y : Space) :
    dy k (newtonJoint D) (τ, y) = spatialTestDerivative k (newtonConv fun x => D (τ, x)) y := by
  have h1 : Differentiable ℝ (newtonJoint D) :=
    (contDiff_newtonJoint hD).differentiable (by simp)
  exact congrFun (slice_dy_real h1 k τ) y

/-- The joint `∂ⱼ∂ₖ` of the Newton potential is the slice Newton Hessian `rieszPairTest`. -/
theorem dy_dy_newtonJoint_eq {P : ℝ} {D : ℝ × Space → ℝ} (hD : IsPhaseTest P D) (j k : Fin 3)
    (τ : ℝ) (y : Space) :
    dy j (dy k (newtonJoint D)) (τ, y) = rieszPairTest j k (fun x => D (τ, x)) y := by
  have h1 : Differentiable ℝ (newtonJoint D) :=
    (contDiff_newtonJoint hD).differentiable (by simp)
  have h2 : Differentiable ℝ (dy k (newtonJoint D)) :=
    (contDiff_dy_real (contDiff_newtonJoint hD) k).differentiable (by simp)
  have e1 : (fun x : Space => dy k (newtonJoint D) (τ, x)) =
      spatialTestDerivative k (newtonConv fun x => D (τ, x)) := slice_dy_real h1 k τ
  have e2 := congrFun (slice_dy_real h2 j τ) y
  show _ = spatialTestDerivative j (spatialTestDerivative k (newtonConv fun x => D (τ, x))) y
  rw [← e1]
  exact e2

/-! ### The smooth Leray projection of a phase test -/

/-- **The smooth Leray projection of a phase test** (source lines 119-120, 1364):
`ℙΦ = Φ + ∇(N ∗ div Re Φ) + i ∇(N ∗ div Im Φ)`, written with the joint derivatives `∂ₖ` of the
two real Newton potentials `ψ_R = newtonJoint (div Re Φ)` and `ψ_I = newtonJoint (div Im Φ)`:
`lerayTest2 Φ = Φ + Σₖ ∂ₖψ_R eₖ + Σₖ ∂ₖψ_I (i eₖ)`.  On every phase slice it is the Cartesian
Leray projection of `Φ(τ, ·)` (`lerayTest2_slice`, `testElem_lerayTest2`). -/
def lerayTest2 (Φ : ℝ × Space → CVec3) : ℝ × Space → CVec3 := fun p =>
  Φ p + ∑ k : Fin 3, dy k (newtonJoint (projectedPotentialReDiv Φ)) p • ofReV (coordinateVector k)
    + ∑ k : Fin 3, dy k (newtonJoint (projectedPotentialImDiv Φ)) p • ofImV (coordinateVector k)

/-- `lerayTest2 Φ` is smooth on `ℝ × ℝ³`. -/
theorem contDiff_lerayTest2 {P : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) :
    ContDiff ℝ ∞ (lerayTest2 Φ) := by
  have hR := contDiff_newtonJoint (isPhaseTest_projectedPotentialReDiv hΦ)
  have hI := contDiff_newtonJoint (isPhaseTest_projectedPotentialImDiv hΦ)
  unfold lerayTest2
  refine (hΦ.smooth.add ?_).add ?_
  · exact ContDiff.sum fun k _ => (contDiff_dy_real hR k).smul contDiff_const
  · exact ContDiff.sum fun k _ => (contDiff_dy_real hI k).smul contDiff_const

/-- `lerayTest2 Φ` is `P`-periodic in the phase. -/
theorem lerayTest2_periodic {P : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) :
    ∀ τ y, lerayTest2 Φ (τ + P, y) = lerayTest2 Φ (τ, y) := by
  have hR := periodic_dy (newtonJoint_periodic (isPhaseTest_projectedPotentialReDiv hΦ))
  have hI := periodic_dy (newtonJoint_periodic (isPhaseTest_projectedPotentialImDiv hΦ))
  intro τ y
  simp only [lerayTest2, hΦ.periodic τ y, hR _ τ y, hI _ τ y]

theorem lerayPotential_reTest_eq {P : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    (τ : ℝ) : lerayPotential (projectedPotentialReTest Φ τ) =
      fun y => newtonJoint (projectedPotentialReDiv Φ) (τ, y) := by
  funext y
  show newtonConv (divTest (projectedPotentialReTest Φ τ)) y =
    newtonConv (fun x => projectedPotentialReDiv Φ (τ, x)) y
  congr 1
  funext x
  exact (projectedPotentialReDiv_slice Φ hΦ τ x).symm

theorem lerayPotential_imTest_eq {P : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    (τ : ℝ) : lerayPotential (projectedPotentialImTest Φ τ) =
      fun y => newtonJoint (projectedPotentialImDiv Φ) (τ, y) := by
  funext y
  show newtonConv (divTest (projectedPotentialImTest Φ τ)) y =
    newtonConv (fun x => projectedPotentialImDiv Φ (τ, x)) y
  congr 1
  funext x
  exact (projectedPotentialImDiv_slice Φ hΦ τ x).symm

/-- The spatial gradient of a slice of the joint potential is given by its joint derivatives. -/
theorem gradField_slice_newtonJoint {P : ℝ} {D : ℝ × Space → ℝ} (hD : IsPhaseTest P D)
    (τ : ℝ) (y : Space) :
    gradField (fun x => newtonJoint D (τ, x)) y =
      ∑ k : Fin 3, dy k (newtonJoint D) (τ, y) • coordinateVector k := by
  have hd : Differentiable ℝ (newtonJoint D) :=
    (contDiff_newtonJoint hD).differentiable (by simp)
  unfold gradField
  refine Finset.sum_congr rfl fun k _ => ?_
  exact congrArg (fun r : ℝ => r • coordinateVector k)
    (fderiv_slice_real (hd (τ, y)) (coordinateVector k))

/-- **Slice formula**: on every phase slice `lerayTest2 Φ` is `Φ + ∇ψ_R + i∇ψ_I` with the slice
Newton potentials `ψ = N ∗ div` of the real and imaginary parts, the right side of
`lerayProjectedPhaseTest_eq_newtonPotentialGrad_ae`. -/
theorem lerayTest2_slice {P : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) (τ : ℝ)
    (y : Space) :
    lerayTest2 Φ (τ, y) = Φ (τ, y) +
      ofReV (gradField (lerayPotential (projectedPotentialReTest Φ τ)) y) +
      ofImV (gradField (lerayPotential (projectedPotentialImTest Φ τ)) y) := by
  rw [lerayPotential_reTest_eq hΦ τ, lerayPotential_imTest_eq hΦ τ,
    gradField_slice_newtonJoint (isPhaseTest_projectedPotentialReDiv hΦ) τ y,
    gradField_slice_newtonJoint (isPhaseTest_projectedPotentialImDiv hΦ) τ y,
    map_sum, map_sum]
  simp only [map_smul]
  rfl

set_option maxHeartbeats 1600000 in
/-- **The `Y_{2'}` test element of `lerayTest2 Φ` is that of the slice-wise Leray projection**
(`lerayProjectedPhaseTest`, the slice map `τ ↦ ℙ(Φ(τ))` into `L^{2'}`). -/
theorem testElem_lerayTest2 {P : ℝ} [Fact (0 < P)] {Φ : ℝ × Space → CVec3}
    (hΦ : IsPhaseTest P Φ) (hs : IsSliceTest P (conjExp 2) (lerayTest2 Φ)) :
    testElem P (conjExp 2) (lerayTest2 Φ) = testElem P (conjExp 2)
      (lerayProjectedPhaseTest one_lt_conjExp_two conjExp_two_ne_top
        (hΦ.isSliceTest (conjExp 2))) := by
  have hp := isSliceTest_lerayProjectedPhaseTest one_lt_conjExp_two conjExp_two_ne_top
    (hΦ.isSliceTest (conjExp 2))
  have hae : ∀ τ : ℝ, (fun y => lerayTest2 Φ (τ, y)) =ᵐ[volume]
      fun y => lerayProjectedPhaseTest one_lt_conjExp_two conjExp_two_ne_top
        (hΦ.isSliceTest (conjExp 2)) (τ, y) := fun τ =>
    (lerayProjectedPhaseTest_eq_newtonPotentialGrad_ae one_lt_conjExp_two
      conjExp_two_ne_top hΦ τ).mono fun y hy => (lerayTest2_slice hΦ τ y).trans hy.symm
  have hc : circleSlice hs = circleSlice hp :=
    circleSlice_ext hs hp fun τ => MemLp.toLp_congr _ _ (hae τ)
  rw [testElem_of hs, testElem_of hp, hc]

/-! ### The leaves -/

/-- **Leaf (uniform decay from a far-field bound).**  A continuous `P`-periodic field
`F : ℝ × ℝ³ → ℂ³` with `|F(τ, y)| ≤ C |y|^{-n}` for `τ ∈ [0, P]`, `|y| ≥ ρ > 0`, satisfies
`|F(τ, y)| ≤ C' (1 + |y|)^{-n}` for all `(τ, y)`.  Proof: `F` is bounded by some `B` on the compact
set `[0, P] × B̄_ρ`; every phase reduces to `[0, P)` by periodicity
(`Function.Periodic.exists_mem_Ico₀`); for `|y| ≤ ρ`, `B ≤ B (1 + ρ)^n (1 + |y|)^{-n}`, and for
`|y| ≥ ρ`, `|y|^{-n} ≤ ((1 + ρ)/ρ)^n (1 + |y|)^{-n}`.  (Used for the slice continuity of
`lerayTest2 Φ` and its derivatives into `C(ℝ/Pℤ; L²)`, source lines 1498-1500.) -/
def DecayOfFarBound : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ (n : ℕ) (F : ℝ × Space → CVec3), Continuous F →
    (∀ τ y, F (τ + P, y) = F (τ, y)) → ∀ (ρ C : ℝ), 0 < ρ →
      (∀ τ ∈ Icc (0 : ℝ) P, ∀ y : Space, ρ ≤ ‖y‖ → ‖F (τ, y)‖ ≤ C * (‖y‖ ^ n)⁻¹) →
        ∃ C' : ℝ, ∀ (τ : ℝ) (y : Space), ‖F (τ, y)‖ ≤ C' * (1 + ‖y‖) ^ (-(n : ℝ))

/-- **Leaf (derivatives of the joint Newton potential fall on the source).**  For a real scalar
phase test `D` and every direction `v ∈ ℝ × ℝ³`,
`∂_v (N ∗ D)(p) = (N ∗ ∂_v D)(p)`: in the parameter form
`newtonJoint D p = ∫ N(x) D(p - (0, x)) dx` (`newtonJoint_eq_param`) one differentiates under the
integral sign (`hasFDerivAt_integral_of_dominated_of_fderiv_le`; the source derivatives are bounded
and vanish for `|p.2 - x|` beyond the support radius, `N` is integrable on balls,
`integrable_newtonPotential_abs_on_closedBall`; the domination is that of
`contDiff_newtonSourceParamIntegral`).  In particular `∂_τ` and `∂ⱼ` commute with the Newton
potential (source lines 1474-1475: Leray commutes with heat and phase translation). -/
def NewtonJointFDeriv : Prop :=
  ∀ (P : ℝ) (D : ℝ × Space → ℝ), IsPhaseTest P D → ∀ (p v : ℝ × Space),
    fderiv ℝ (newtonJoint D) p v = newtonJoint (fun q => fderiv ℝ D q v) p

/-- **Leaf (far-field bound of the Newton Hessian, explicit constants).**  For a compact smooth
test `f` vanishing for `|x| > ρ ≥ 0`, and `|y| ≥ 2ρ + 1`,
`|∂ᵢ∂ₖ(N ∗ f)(y)| ≤ 8 π⁻¹ ‖f‖_{L¹} |y|^{-3}`.  This is `rieszPairTest_decay`
(`Lib/CZL2/TestOffSupport.lean`) with its constants made explicit: off the support
`∂ᵢ∂ₖ(N ∗ f)(y) = ∫ K_ik(y - x) f(x) dx` (`rieszPairTest_offSupport`) and
`|K_ik(z)| ≤ π⁻¹ (|y|/2)^{-3}` for `|z| ≥ |y|/2` (`abs_newtonHessianKernel_le_of_le`). -/
def NewtonHessFar : Prop :=
  ∀ (f : Space → ℝ), IsSpatialTest f → ∀ (ρ : ℝ), 0 ≤ ρ → (∀ x : Space, ρ < ‖x‖ → f x = 0) →
    ∀ (i k : Fin 3) (y : Space), 2 * ρ + 1 ≤ ‖y‖ →
      |rieszPairTest i k f y| ≤ 8 * Real.pi⁻¹ * (∫ x, |f x|) * (‖y‖ ^ 3)⁻¹

/-- **Leaf (the phase pairing transposes the Leray projection).**  For a slice test `Φ` in
`L^{2'}` and `f ∈ Y_2`, `⟪Φ, ℙf⟫ = ⟪ℙΦ, f⟫`, where `ℙΦ` is the slice-wise projection
`lerayProjectedPhaseTest`.  Proof: write both pairings as phase integrals of `innerPair 2`
(`phasePairing_apply`, `ContinuousMap.coeFn_toLp`, `coeFn_lerayY`) and apply the slice symmetry
`LerayCSymm` (`lerayCSymm_proof`, `Sub/PartII-b_T10_org_2_3_2.lean`) at `p = 2`; the slice of
`lerayProjectedPhaseTest` at `τ` is `lerayC (conjExp 2) (sliceMap τ)` (source line 1364 and the
self-adjointness of `ℙ` at `r = 2`, lines 1365-1366). -/
def PhasePairLerayY : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (Φ : ℝ × Space → CVec3) (hΦ : IsSliceTest P (conjExp 2) Φ)
    (f : Yq P 2),
    phasePair P 2 Φ (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top f) =
      phasePair P 2 (lerayProjectedPhaseTest one_lt_conjExp_two conjExp_two_ne_top hΦ) f

end UnforcedLeray.Short.IIb.LTS
