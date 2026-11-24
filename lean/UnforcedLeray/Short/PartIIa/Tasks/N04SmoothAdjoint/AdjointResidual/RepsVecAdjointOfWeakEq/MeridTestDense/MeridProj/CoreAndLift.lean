import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointResidual.RepsVecAdjointOfWeakEq.MeridTestDense.MeridProj.PhaseEquiv
import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointResidual.RepsVecAdjointOfWeakEq.LeftOnCore
import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointResidual.RepsVecAdjointOfWeakEq.CoreMemLp
import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointResidual.CoreSupport
import UnforcedLeray.Units.B0226.AxisTests

/-!
# Chart meridional projection, core-test regularity, and generator commutation

Helper 2 for `PartII-a:N04/3/3/2/2` (`MeridProjOfPhaseTest`).
Source of record: `the November 2 reference manuscript`,
lines 1477–1478 (`O(2)`-averaging kills swirl and preserves smoothness across the axis) and
3290–3352 (chart lift `fieldU` and meridional vector generator `A_ε^vec`).

Main results:
* `meridProjProfile ε φ`: the `O(2)`-averaged chart profile of a phase test `φ`;
* `coreFieldRe_eq_fieldU`: off the axis, `(jConst ε)⁻¹ • reVec3 (meridAvgPhase φ (τ, x))` equals
  `B0220.fieldU ε (reMerid (meridProjProfile ε φ)) (x, τ)`;
* `isMeridCoreTest_meridProjProfile`: `IsPhaseTest P φ → IsMeridCoreTest ε c (meridProjProfile ε φ)`;
* `meridProjProfile_phaseGen`: `meridProjProfile ε (phaseGen ν ε ψ) p = AepsVecC ν ε (meridProjProfile ε ψ) p`
  for `0 < p.1`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa.MeridProjAux

open UnforcedLeray.PhaseSpace
open UnforcedLeray.Short.PartIIIb.NearInst.Masked (merReL merReL_apply)
open UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization (cplx3 cplx3_apply)

/-! ### 1. Angular projection in cylindrical frame -/

/-- Complex unit horizontal radial vector `(cos θ, sin θ, 0)` at angle `θ`. -/
def uThetaC (θ : ℝ) : B0223.SpaceC := B0223.ofRealVec (B0226.uTheta θ)

/-- Pointwise meridional frame adjoint `w ↦ (⟪u_θ, w⟫_ℂ, ⟪e_z, w⟫_ℂ)`. -/
def projThetaCLin (θ : ℝ) : B0223.SpaceC →ₗ[ℂ] B0223.MeridC where
  toFun w := !₂[inner ℂ (uThetaC θ) w, inner ℂ B0223.unitZC w]
  map_add' u v := by
    ext i
    fin_cases i <;> simp
  map_smul' c v := by
    ext i
    fin_cases i <;> simp

/-- Continuous `ℂ`-linear meridional frame adjoint at angle `θ`. -/
def projThetaC (θ : ℝ) : B0223.SpaceC →L[ℂ] B0223.MeridC :=
  LinearMap.toContinuousLinearMap (projThetaCLin θ)

@[simp] theorem projThetaC_apply_zero (θ : ℝ) (w : B0223.SpaceC) :
    projThetaC θ w 0 = inner ℂ (uThetaC θ) w := rfl

@[simp] theorem projThetaC_apply_one (θ : ℝ) (w : B0223.SpaceC) :
    projThetaC θ w 1 = inner ℂ B0223.unitZC w := rfl

theorem inner_frameC_rotPt {r : ℝ} (hr : 0 < r) (θ z : ℝ)
    (v : B0223.MeridC) (w : B0223.SpaceC) :
    inner ℂ (B0223.frameC (B0226.rotPt θ r z) v) w = inner ℂ v (projThetaC θ w) := by
  have hu : B0223.unitRC (B0226.rotPt θ r z) = uThetaC θ := by
    rw [B0223.unitRC_eq, B0226.unitR_rotPt hr θ z, uThetaC]
  rw [B0223.frameC_apply, hu, inner_add_left, inner_smul_left, inner_smul_left]
  conv_rhs => rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp only [projThetaC_apply_zero, projThetaC_apply_one, RCLike.inner_apply]
  ring

theorem merReL_projThetaC_zero (θ : ℝ) (w : B0223.SpaceC) :
    merReL (projThetaC θ w) 0 = inner ℝ (B0226.uTheta θ) (reVec3 w) := by
  rw [merReL_apply, projThetaC_apply_zero, PiLp.inner_apply, PiLp.inner_apply,
    Fin.sum_univ_three, Fin.sum_univ_three]
  simp [uThetaC, B0223.ofRealVec_apply, RCLike.inner_apply, reVec3_apply]

theorem merReL_projThetaC_one (θ : ℝ) (w : B0223.SpaceC) :
    merReL (projThetaC θ w) 1 = reVec3 w 2 := by
  rw [merReL_apply, projThetaC_apply_one, B0223.unitZC_eq, PiLp.inner_apply, Fin.sum_univ_three]
  simp [B0223.ofRealVec_apply, B0220.unitZ, RCLike.inner_apply, reVec3_apply]

theorem integrable_angμ_of_continuous {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    (hf : Continuous f) : Integrable f Axi.angμ := by
  have hIoc : IntegrableOn f (Ioc 0 (2 * Real.pi)) volume :=
    hf.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hne : (ENNReal.ofReal (2 * Real.pi))⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 Real.two_pi_pos).ne'
  exact hIoc.smul_measure hne

theorem continuous_projThetaC_comp {f : ℝ → B0223.SpaceC} (hf : Continuous f) :
    Continuous fun θ : ℝ => projThetaC θ (f θ) := by
  have hu : Continuous uThetaC := by
    have heq : uThetaC = fun θ =>
        (Real.cos θ : ℂ) • EuclideanSpace.single 0 (1 : ℂ) +
          (Real.sin θ : ℂ) • EuclideanSpace.single 1 (1 : ℂ) := by
      funext θ
      ext i
      fin_cases i <;> simp [uThetaC, B0226.uTheta, B0226.rotPt]
    rw [heq]
    exact ((Complex.continuous_ofReal.comp Real.continuous_cos).smul continuous_const).add
      ((Complex.continuous_ofReal.comp Real.continuous_sin).smul continuous_const)
  have heq : (fun θ : ℝ => projThetaC θ (f θ)) = fun θ =>
      inner ℂ (uThetaC θ) (f θ) • (EuclideanSpace.single (0 : Fin 2) (1 : ℂ) : B0223.MeridC) +
        inner ℂ B0223.unitZC (f θ) • (EuclideanSpace.single (1 : Fin 2) (1 : ℂ) : B0223.MeridC) := by
    funext θ
    ext i
    fin_cases i <;> simp
  rw [heq]
  exact ((Continuous.inner (𝕜 := ℂ) hu hf).smul continuous_const).add
    ((Continuous.inner (𝕜 := ℂ) continuous_const hf).smul continuous_const)

/-! ### 2. Meridional chart profile `meridProjProfile` -/

/-- The `O(2)`-averaged chart profile of `φ : ℝ × Space → CVec3`, representing `(liftVec)^* Φ`. -/
def meridProjProfile (ε : ℝ) (φ : ℝ × Space → CVec3) (p : B0220.Profile) : B0223.MeridC :=
  if 0 < p.1 then
    ((B0220.jConst ε)⁻¹ * √(p.1⁻¹) : ℝ) •
      ∫ θ, projThetaC θ (φ (2 * ε * p.2.1 + Real.log p.1,
        B0226.rotPt θ (√(p.1⁻¹)) (ε * p.2.2 * √(p.1⁻¹)))) ∂Axi.angμ
  else 0

theorem meridProjProfile_smul (ε : ℝ) (k : ℂ) (φ : ℝ × Space → CVec3) :
    meridProjProfile ε (k • φ) = k • meridProjProfile ε φ := by
  funext p
  by_cases hp : 0 < p.1
  · simp only [meridProjProfile, hp, ↓reduceIte, Pi.smul_apply, map_smul]
    rw [integral_smul]
    exact smul_comm ((B0220.jConst ε)⁻¹ * √(p.1⁻¹) : ℝ) k _
  · simp [meridProjProfile, hp]

private theorem reMerid_meridProjProfile_negI (ε : ℝ) (φ : ℝ × Space → CVec3) :
    reMerid (meridProjProfile ε ((-Complex.I) • φ)) = imMerid (meridProjProfile ε φ) := by
  funext q
  change merReL (meridProjProfile ε ((-Complex.I) • φ) q) =
    merReL ((-Complex.I) • meridProjProfile ε φ q)
  rw [meridProjProfile_smul]
  rfl

private theorem meridC_ext_re_im {u v : B0223.MeridC}
    (hre : merReL u = merReL v)
    (him : merReL ((-Complex.I) • u) = merReL ((-Complex.I) • v)) : u = v := by
  ext i
  have hr := congrArg (fun w : B0220.Merid => w i) hre
  have hi := congrArg (fun w : B0220.Merid => w i) him
  simp only [merReL_apply, PiLp.smul_apply, smul_eq_mul, Complex.mul_re,
    Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    neg_zero, zero_mul] at hr hi
  exact Complex.ext hr (by linarith)

theorem qPeriodic_meridProjProfile {ε c : ℝ} {φ : ℝ × Space → CVec3}
    (hper : ∀ τ y, φ (τ + 2 * ε * c, y) = φ (τ, y)) :
    B0220.QPeriodic c (meridProjProfile ε φ) := by
  intro p
  by_cases hp : 0 < p.1
  · simp only [meridProjProfile, hp, ↓reduceIte]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    dsimp only
    have hτ : 2 * ε * (p.2.1 + c) + Real.log p.1 =
        (2 * ε * p.2.1 + Real.log p.1) + 2 * ε * c := by ring
    rw [hτ, hper]
  · simp [meridProjProfile, hp]

/-! ### 3. Off-axis Cartesian lift identity -/

/-- Smooth Cartesian vector field extending `B0220.fieldU ε (reMerid (meridProjProfile ε φ))`
across the symmetry axis. -/
def coreFieldRe (ε : ℝ) (φ : ℝ × Space → CVec3) (y : Space × ℝ) : Space :=
  (B0220.jConst ε)⁻¹ • reVec3 (meridAvgPhase φ (y.2, y.1))

theorem isCoreTestFieldVec_coreFieldRe {ε c P : ℝ} (hPpos : 0 < P) (hP : P = 2 * ε * c)
    {φ : ℝ × Space → CVec3} (hφ : IsPhaseTest P φ) :
    IsCoreTestFieldVec ε c (coreFieldRe ε φ) := by
  have hm := isPhaseTest_meridAvgPhase hPpos hφ
  refine ⟨?_, ?_, ?_⟩
  · intro j
    have hsm : ContDiff ℝ ∞ (fun y : Space × ℝ => coreFieldRe ε φ y j) := by
      have hV : ContDiff ℝ ∞ (coreFieldRe ε φ) :=
        (reVec3.contDiff.comp (hm.smooth.comp (contDiff_snd.prodMk contDiff_fst))).const_smul
          (B0220.jConst ε)⁻¹
      exact (EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff.comp hV
    exact hsm.of_le (by simp)
  · obtain ⟨R, hR⟩ := hm.bounded_support
    exact ⟨R, fun y hy => by simp [coreFieldRe, hR y.2 y.1 hy]⟩
  · intro x τ
    simp only [coreFieldRe, ← hP, hm.periodic τ x]

private theorem unitR_eq_eR (x : Space) : B0220.unitR x = Axi.eR x := by
  ext i
  fin_cases i <;> simp [B0220.unitR, Axi.eR, B0226.radius_eq_ϱ, div_eq_inv_mul]

private theorem unitZ_eq_e3 : B0220.unitZ = Axi.e3 := by
  ext i
  fin_cases i <;> simp [B0220.unitZ, Axi.e3, coordinateVector]

private theorem reflY_reflY (y : Space) : Axi.reflY (Axi.reflY y) = y :=
  Axi.reflFun_reflFun y

private theorem rotZ_neg_cancel (α : ℝ) (v : Space) :
    B0226.rotZ α (B0226.rotZ (-α) v) = v := by
  simpa [B0226.rotZ_apply] using B0226.rotFun_inv (-α) v

private theorem reflY_rotPt (β r z : ℝ) :
    Axi.reflY (B0226.rotPt β r z) = B0226.rotPt (-β) r z := by
  ext i
  fin_cases i <;> simp [Axi.reflY_apply, Axi.reflFun, B0226.rotPt]

private theorem uTheta_rotZ (α γ : ℝ) :
    B0226.rotZ α (B0226.uTheta γ) = B0226.uTheta (α + γ) := by
  simpa [B0226.uTheta] using B0226.rotZ_rotPt α γ 1 0

private theorem continuous_rotPt_angle (r z : ℝ) :
    Continuous fun θ : ℝ => B0226.rotPt θ r z := by
  have h : (fun θ : ℝ => B0226.rotPt θ r z) = fun θ =>
      (r * Real.cos θ) • coordinateVector 0 + (r * Real.sin θ) • coordinateVector 1 +
        z • coordinateVector 2 := funext fun θ => B0226.rotPt_eq_comb θ r z
  rw [h]
  fun_prop

private theorem continuous_rotZ_apply (x : Space) :
    Continuous fun α : ℝ => B0226.rotZ α x := by
  have heq : (fun α : ℝ => B0226.rotZ α x) = fun α =>
      (Real.cos α * x 0 - Real.sin α * x 1) • EuclideanSpace.single 0 (1 : ℝ) +
        (Real.sin α * x 0 + Real.cos α * x 1) • EuclideanSpace.single 1 (1 : ℝ) +
        x 2 • EuclideanSpace.single 2 (1 : ℝ) := by
    funext α
    ext i
    fin_cases i <;> simp [B0226.rotZ_apply, B0226.rotFun]
  rw [heq]
  exact ((((Real.continuous_cos.mul continuous_const).sub
    (Real.continuous_sin.mul continuous_const)).smul continuous_const).add
    (((Real.continuous_sin.mul continuous_const).add
      (Real.continuous_cos.mul continuous_const)).smul continuous_const)).add continuous_const

private theorem continuous_actVec_angle {W : Space → Space} (hW : Continuous W) (x : Space) :
    Continuous fun α : ℝ => B0226.rotZ (-α) (W (B0226.rotZ α x)) := by
  have hin : Continuous fun α : ℝ => W (B0226.rotZ α x) :=
    hW.comp (continuous_rotZ_apply x)
  have heq : (fun α : ℝ => B0226.rotZ (-α) (W (B0226.rotZ α x))) = fun α =>
      (Real.cos (-α) * (W (B0226.rotZ α x)) 0 - Real.sin (-α) * (W (B0226.rotZ α x)) 1) •
        EuclideanSpace.single 0 (1 : ℝ) +
      (Real.sin (-α) * (W (B0226.rotZ α x)) 0 + Real.cos (-α) * (W (B0226.rotZ α x)) 1) •
        EuclideanSpace.single 1 (1 : ℝ) +
      (W (B0226.rotZ α x)) 2 • EuclideanSpace.single 2 (1 : ℝ) := by
    funext α
    ext i
    fin_cases i <;> simp [B0226.rotZ_apply, B0226.rotFun]
  rw [heq]
  have hw0 : Continuous fun α : ℝ => (W (B0226.rotZ α x)) 0 :=
    (PiLp.continuous_apply 2 _ 0).comp hin
  have hw1 : Continuous fun α : ℝ => (W (B0226.rotZ α x)) 1 :=
    (PiLp.continuous_apply 2 _ 1).comp hin
  have hw2 : Continuous fun α : ℝ => (W (B0226.rotZ α x)) 2 :=
    (PiLp.continuous_apply 2 _ 2).comp hin
  have hc1 : Continuous fun α : ℝ => Real.cos (-α) := Real.continuous_cos.comp continuous_neg
  have hs1 : Continuous fun α : ℝ => Real.sin (-α) := Real.continuous_sin.comp continuous_neg
  exact ((((hc1.mul hw0).sub (hs1.mul hw1)).smul continuous_const).add
    (((hs1.mul hw0).add (hc1.mul hw1)).smul continuous_const)).add (hw2.smul continuous_const)

/-- Off the axis, `coreFieldRe ε φ` agrees pointwise with
`B0220.fieldU ε (reMerid (meridProjProfile ε φ))`. -/
theorem coreFieldRe_eq_fieldU {ε : ℝ} (hε : 0 < ε) {φ : ℝ × Space → CVec3}
    (hφ : Continuous φ) (y : Space × ℝ) (hr : B0220.radius y.1 ≠ 0) :
    coreFieldRe ε φ y = B0220.fieldU ε (reMerid (meridProjProfile ε φ)) y := by
  obtain ⟨x, τ⟩ := y
  set r := B0220.radius x with hr_def
  have hr_pos : 0 < r := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hr)
  set z := x 2 with hz_def
  obtain ⟨β, hβ⟩ := B0226.exists_rotPt_eq x
  set W : Space → Space := fun x' => reVec3 (φ (τ, x')) with hW_def
  have hW_cont : Continuous W :=
    reVec3.continuous.comp (hφ.comp (continuous_const.prodMk continuous_id))
  set Rvec : Space → Space := fun x' =>
    ∫ α, B0226.rotZ (-α) (W (B0226.rotZ α x')) ∂Axi.angμ with hRvec_def
  have hre_rot : ∀ x' : Space, reVec3 (rotAvgPhase φ (τ, x')) = Rvec x' := by
    intro x'
    have hf_cont : Continuous fun α : ℝ => actPhase (B0226.rotZ α) φ (τ, x') := by
      have hin_c : Continuous fun α : ℝ => φ (prodCLM (B0226.rotZ α) (τ, x')) :=
        hφ.comp (continuous_const.prodMk (continuous_rotZ_apply x'))
      -- use componentwise representation of `linIsoC (B0226.rotZ (-α))`
      have heq : (fun α : ℝ => actPhase (B0226.rotZ α) φ (τ, x')) = fun α =>
          let w := φ (prodCLM (B0226.rotZ α) (τ, x'))
          (Real.cos (-α) * w 0 - Real.sin (-α) * w 1) • EuclideanSpace.single 0 (1 : ℂ) +
            (Real.sin (-α) * w 0 + Real.cos (-α) * w 1) • EuclideanSpace.single 1 (1 : ℂ) +
            w 2 • EuclideanSpace.single 2 (1 : ℂ) := by
        funext α
        ext i
        have hsym : (B0226.rotZ α).symm = B0226.rotZ (-α) := by ext v j; rfl
        fin_cases i <;>
          (simp [actPhase, hsym, linIsoC_apply, rc, B0226.rotZ_apply, B0226.rotFun,
            Fin.sum_univ_three, coordinateVector]; try ring)
      rw [heq]
      have hw0 : Continuous fun α : ℝ => φ (prodCLM (B0226.rotZ α) (τ, x')) 0 :=
        (PiLp.continuous_apply 2 _ 0).comp hin_c
      have hw1 : Continuous fun α : ℝ => φ (prodCLM (B0226.rotZ α) (τ, x')) 1 :=
        (PiLp.continuous_apply 2 _ 1).comp hin_c
      have hw2 : Continuous fun α : ℝ => φ (prodCLM (B0226.rotZ α) (τ, x')) 2 :=
        (PiLp.continuous_apply 2 _ 2).comp hin_c
      have hc1 : Continuous fun α : ℝ => (Real.cos (-α) : ℂ) :=
        Complex.continuous_ofReal.comp (Real.continuous_cos.comp continuous_neg)
      have hs1 : Continuous fun α : ℝ => (Real.sin (-α) : ℂ) :=
        Complex.continuous_ofReal.comp (Real.continuous_sin.comp continuous_neg)
      exact ((((hc1.mul hw0).sub (hs1.mul hw1)).smul continuous_const).add
        (((hs1.mul hw0).add (hc1.mul hw1)).smul continuous_const)).add
          (hw2.smul continuous_const)
    rw [rotAvgPhase, ← reVec3.integral_comp_comm (integrable_angμ_of_continuous hf_cont), hRvec_def]
    refine integral_congr_ae (Filter.Eventually.of_forall fun α => ?_)
    have hsym : (B0226.rotZ α).symm = B0226.rotZ (-α) := by ext v j; rfl
    simp only [actPhase, hsym, reVec3_linIsoC, prodCLM_apply, hW_def]
  have hre_mer : reVec3 (meridAvgPhase φ (τ, x)) =
      (1 / 2 : ℝ) • (Rvec x + Axi.reflY (Rvec (Axi.reflY x))) := by
    simp only [meridAvgPhase, map_smul, map_add, hre_rot x]
    congr 2
    have hsym : Axi.reflY.symm = Axi.reflY := by ext v j; rfl
    simp only [actPhase, hsym, reVec3_linIsoC, prodCLM_apply, hre_rot (Axi.reflY x)]
  -- cylindrical projections of `Rvec (rotPt γ r z)` are independent of `γ`
  set Ir : ℝ := ∫ θ, inner ℝ (B0226.uTheta θ) (W (B0226.rotPt θ r z)) ∂Axi.angμ
  set Iz : ℝ := ∫ θ, W (B0226.rotPt θ r z) 2 ∂Axi.angμ
  set Iφ : ℝ := ∫ θ, inner ℝ (Axi.eΦ (B0226.rotPt θ r z)) (W (B0226.rotPt θ r z)) ∂Axi.angμ
  have hR_rad : ∀ γ : ℝ, inner ℝ (Rvec (B0226.rotPt γ r z)) (Axi.eR (B0226.rotPt γ r z)) = Ir := by
    intro γ
    rw [← unitR_eq_eR, B0226.unitR_rotPt hr_pos γ z, real_inner_comm]
    have hint := integrable_angμ_of_continuous (continuous_actVec_angle hW_cont (B0226.rotPt γ r z))
    have hL : inner ℝ (B0226.uTheta γ) (Rvec (B0226.rotPt γ r z)) =
        ∫ α, inner ℝ (B0226.uTheta γ)
          (B0226.rotZ (-α) (W (B0226.rotZ α (B0226.rotPt γ r z)))) ∂Axi.angμ :=
      ((innerSL ℝ (B0226.uTheta γ)).integral_comp_comm hint).symm
    rw [hL]
    have hpt : ∀ α : ℝ, inner ℝ (B0226.uTheta γ)
        (B0226.rotZ (-α) (W (B0226.rotZ α (B0226.rotPt γ r z)))) =
        inner ℝ (B0226.uTheta (γ + α)) (W (B0226.rotPt (γ + α) r z)) := fun α => by
      rw [← (B0226.rotZ α).inner_map_map, rotZ_neg_cancel, uTheta_rotZ, B0226.rotZ_rotPt,
        add_comm α γ]
    simp_rw [hpt]
    exact Axi.integral_angμ_add
      (g := fun θ => inner ℝ (B0226.uTheta θ) (W (B0226.rotPt θ r z)))
      (fun θ => by simp only [B0226.uTheta, B0226.rotPt_add_two_pi]) γ
  have hR_ax : ∀ γ : ℝ, Rvec (B0226.rotPt γ r z) 2 = Iz := by
    intro γ
    have hint := integrable_angμ_of_continuous (continuous_actVec_angle hW_cont (B0226.rotPt γ r z))
    have hL : Rvec (B0226.rotPt γ r z) 2 =
        ∫ α, (B0226.rotZ (-α) (W (B0226.rotZ α (B0226.rotPt γ r z)))) 2 ∂Axi.angμ :=
      ((EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).integral_comp_comm hint).symm
    rw [hL]
    have hpt : ∀ α : ℝ, (B0226.rotZ (-α) (W (B0226.rotZ α (B0226.rotPt γ r z)))) 2 =
        W (B0226.rotPt (γ + α) r z) 2 := fun α => by
      rw [B0226.rotZ_rotPt, add_comm α γ]
      rfl
    simp_rw [hpt]
    exact Axi.integral_angμ_add
      (g := fun θ => W (B0226.rotPt θ r z) 2)
      (fun θ => by dsimp only; rw [B0226.rotPt_add_two_pi]) γ
  have hR_phi : ∀ γ : ℝ, inner ℝ (Rvec (B0226.rotPt γ r z)) (Axi.eΦ (B0226.rotPt γ r z)) = Iφ := by
    intro γ
    rw [real_inner_comm]
    have hint := integrable_angμ_of_continuous (continuous_actVec_angle hW_cont (B0226.rotPt γ r z))
    have hL : inner ℝ (Axi.eΦ (B0226.rotPt γ r z)) (Rvec (B0226.rotPt γ r z)) =
        ∫ α, inner ℝ (Axi.eΦ (B0226.rotPt γ r z))
          (B0226.rotZ (-α) (W (B0226.rotZ α (B0226.rotPt γ r z)))) ∂Axi.angμ :=
      ((innerSL ℝ (Axi.eΦ (B0226.rotPt γ r z))).integral_comp_comm hint).symm
    rw [hL]
    have hpt : ∀ α : ℝ, inner ℝ (Axi.eΦ (B0226.rotPt γ r z))
        (B0226.rotZ (-α) (W (B0226.rotZ α (B0226.rotPt γ r z)))) =
        inner ℝ (Axi.eΦ (B0226.rotPt (γ + α) r z)) (W (B0226.rotPt (γ + α) r z)) := fun α => by
      rw [← (B0226.rotZ α).inner_map_map, rotZ_neg_cancel]
      have heφ : B0226.rotZ α (Axi.eΦ (B0226.rotPt γ r z)) =
          Axi.eΦ (B0226.rotZ α (B0226.rotPt γ r z)) := (Axi.eΦ_rotZ α (B0226.rotPt γ r z)).symm
      rw [heφ, B0226.rotZ_rotPt, add_comm α γ]
    simp_rw [hpt]
    exact Axi.integral_angμ_add
      (g := fun θ => inner ℝ (Axi.eΦ (B0226.rotPt θ r z)) (W (B0226.rotPt θ r z)))
      (fun θ => by dsimp only; rw [B0226.rotPt_add_two_pi]) γ
  -- evaluate on `M = (1/2) • (Rvec x + reflY (Rvec (reflY x)))`
  set M := (1 / 2 : ℝ) • (Rvec x + Axi.reflY (Rvec (Axi.reflY x)))
  have hx_eq : x = B0226.rotPt β r z := hβ.symm
  have hSx_eq : Axi.reflY x = B0226.rotPt (-β) r z := by rw [hx_eq, reflY_rotPt]
  have hM_rad : inner ℝ M (Axi.eR x) = Ir := by
    have hS : inner ℝ (Axi.reflY (Rvec (Axi.reflY x))) (Axi.eR x) = Ir := by
      have heR : Axi.reflY (Axi.eR x) = Axi.eR (Axi.reflY x) :=
        (Axi.eR_map Axi.fixesAxis_reflY x).symm
      rw [← Axi.reflY.inner_map_map, reflY_reflY, heR, hSx_eq]
      exact hR_rad (-β)
    have h1 : inner ℝ (Rvec x) (Axi.eR x) = Ir := by rw [hx_eq]; exact hR_rad β
    simp only [M, real_inner_smul_left, inner_add_left, h1, hS]
    ring
  have hM_phi : inner ℝ M (Axi.eΦ x) = 0 := by
    have hS : inner ℝ (Axi.reflY (Rvec (Axi.reflY x))) (Axi.eΦ x) = -Iφ := by
      have heΦ : Axi.reflY (Axi.eΦ x) = -Axi.eΦ (Axi.reflY x) :=
        neg_eq_iff_eq_neg.1 (Axi.eΦ_reflY x).symm
      rw [← Axi.reflY.inner_map_map, reflY_reflY, heΦ, inner_neg_right, hSx_eq, hR_phi (-β)]
    have h1 : inner ℝ (Rvec x) (Axi.eΦ x) = Iφ := by rw [hx_eq]; exact hR_phi β
    simp only [M, real_inner_smul_left, inner_add_left, h1, hS]
    ring
  have hM_ax : M 2 = Iz := by
    have h1 : Rvec x 2 = Iz := by rw [hx_eq]; exact hR_ax β
    have hS : (Axi.reflY (Rvec (Axi.reflY x))) 2 = Iz := by
      rw [Axi.reflY_apply, Axi.reflFun_apply_two, hSx_eq]
      exact hR_ax (-β)
    simp only [M, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul, h1, hS]
    ring
  have hM_frame : M = B0220.frame x !₂[Ir, Iz] := by
    have hdec := Axi.eq_frame_decomp (B0226.notMem_axis hr) M
    rw [hM_rad, hM_phi, hM_ax, zero_smul, add_zero, ← unitR_eq_eR, ← unitZ_eq_e3] at hdec
    simpa [B0220.frame_apply] using hdec
  -- match `B0220.fieldU ε (reMerid (meridProjProfile ε φ)) (x, τ)`
  set q := B0220.chart ε (x, τ)
  have hq1 : 0 < q.1 := by
    show 0 < (r ^ 2)⁻¹
    positivity
  have hsqrt : √(q.1⁻¹) = r := by
    show √(((r ^ 2)⁻¹)⁻¹) = r
    rw [inv_inv, Real.sqrt_sq hr_pos.le]
  have hz_q : ε * q.2.2 * √(q.1⁻¹) = z := by
    rw [hsqrt]
    simp only [q, B0220.chart, B0220.etaCoord, hr_def, hz_def]
    have hε0 : ε ≠ 0 := hε.ne'
    have hr0 : B0220.radius x ≠ 0 := hr
    field_simp
  have hτ_q : 2 * ε * q.2.1 + Real.log q.1 = τ := by
    simp only [q, B0220.chart, B0220.cellQ, B0220.ageS]
    have hε0 : ε ≠ 0 := hε.ne'
    rw [Real.log_inv, Real.log_pow]
    field_simp
    ring
  have hre_q : reMerid (meridProjProfile ε φ) q =
      ((B0220.jConst ε)⁻¹ * r) • !₂[Ir, Iz] := by
    have hin_pt : Continuous fun θ : ℝ => ((τ, B0226.rotPt θ r z) : ℝ × Space) :=
      Continuous.prodMk continuous_const (continuous_rotPt_angle r z)
    have hf_cont : Continuous fun θ : ℝ =>
        projThetaC θ (φ (τ, B0226.rotPt θ r z)) :=
      continuous_projThetaC_comp (hφ.comp hin_pt)
    have hint := integrable_angμ_of_continuous hf_cont
    have hre_int : merReL (∫ θ, projThetaC θ (φ (τ, B0226.rotPt θ r z)) ∂Axi.angμ) =
        ∫ θ, merReL (projThetaC θ (φ (τ, B0226.rotPt θ r z))) ∂Axi.angμ :=
      (merReL.integral_comp_comm hint).symm
    have hmer_int : ∫ θ, merReL (projThetaC θ (φ (τ, B0226.rotPt θ r z))) ∂Axi.angμ =
        !₂[Ir, Iz] := by
      have hint_re : Integrable (fun θ => merReL (projThetaC θ (φ (τ, B0226.rotPt θ r z))))
          Axi.angμ := merReL.integrable_comp hint
      ext i
      fin_cases i
      · have hp0 := ((EuclideanSpace.proj (0 : Fin 2) : B0220.Merid →L[ℝ] ℝ).integral_comp_comm
          hint_re).symm
        change (EuclideanSpace.proj (0 : Fin 2) : B0220.Merid →L[ℝ] ℝ)
          (∫ θ, merReL (projThetaC θ (φ (τ, B0226.rotPt θ r z))) ∂Axi.angμ) = Ir
        rw [hp0]
        refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
        exact merReL_projThetaC_zero θ _
      · have hp1 := ((EuclideanSpace.proj (1 : Fin 2) : B0220.Merid →L[ℝ] ℝ).integral_comp_comm
          hint_re).symm
        change (EuclideanSpace.proj (1 : Fin 2) : B0220.Merid →L[ℝ] ℝ)
          (∫ θ, merReL (projThetaC θ (φ (τ, B0226.rotPt θ r z))) ∂Axi.angμ) = Iz
        rw [hp1]
        refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
        exact merReL_projThetaC_one θ _
    have hz_r : ε * q.2.2 * r = z := by rwa [hsqrt] at hz_q
    show merReL (meridProjProfile ε φ q) = _
    simp only [meridProjProfile, hq1, ↓reduceIte, hsqrt, hz_r, hτ_q, map_smul]
    rw [hre_int, hmer_int]
  have hlift : B0220.liftA x * ((B0220.jConst ε)⁻¹ * r) = (B0220.jConst ε)⁻¹ := by
    simp only [B0220.liftA, hr_def]
    have hr0 : B0220.radius x ≠ 0 := hr
    field_simp
  rw [coreFieldRe, hre_mer, hM_frame, B0220.fieldU, show B0220.chart ε (x, τ) = q from rfl, hre_q,
    LinearMap.map_smul, smul_smul, hlift]

/-! ### 4. Smoothness on `{s > 0}`, `IsMeridCoreTest`, and generator commutation -/

/-- Canonical off-axis spatial chart section `p ↦ (s^{-1/2}, 0, ε η s^{-1/2})`. -/
def chartPtX (ε : ℝ) (p : B0220.Profile) : Space :=
  B0226.rotPt 0 (√(p.1⁻¹)) (ε * p.2.2 * √(p.1⁻¹))

/-- Canonical phase chart section `p ↦ 2εq + log s`. -/
def chartPtTau (ε : ℝ) (p : B0220.Profile) : ℝ :=
  2 * ε * p.2.1 + Real.log p.1

private theorem radius_chartPtX {ε : ℝ} {p : B0220.Profile} (_hp : 0 < p.1) :
    B0220.radius (chartPtX ε p) = √(p.1⁻¹) :=
  B0226.radius_rotPt (Real.sqrt_nonneg _) 0 _

private theorem chart_chartPt {ε : ℝ} (hε : 0 < ε) {p : B0220.Profile} (hp : 0 < p.1) :
    B0220.chart ε (chartPtX ε p, chartPtTau ε p) = p := by
  have hpinv : 0 < p.1⁻¹ := inv_pos.2 hp
  have hrad := radius_chartPtX (ε := ε) hp
  have hr_pos : 0 < B0220.radius (chartPtX ε p) := by
    rw [hrad]
    exact Real.sqrt_pos.2 hpinv
  have hr2 : B0220.radius (chartPtX ε p) ^ 2 = p.1⁻¹ := by
    rw [hrad]
    exact Real.sq_sqrt hpinv.le
  have hlogr : Real.log (B0220.radius (chartPtX ε p)) = -Real.log p.1 / 2 := by
    rw [hrad, Real.log_sqrt hpinv.le, Real.log_inv]
  have h1 : B0220.ageS (chartPtX ε p) = p.1 := by
    unfold B0220.ageS
    rw [hr2, inv_inv]
  have h2 : B0220.cellQ ε (chartPtX ε p) (chartPtTau ε p) = p.2.1 := by
    unfold B0220.cellQ
    rw [hlogr, chartPtTau]
    have hε0 : ε ≠ 0 := hε.ne'
    field_simp
    ring
  have h3 : B0220.etaCoord ε (chartPtX ε p) = p.2.2 := by
    unfold B0220.etaCoord
    rw [hrad]
    change (ε * p.2.2 * √(p.1⁻¹)) / (ε * √(p.1⁻¹)) = p.2.2
    have hε0 : ε ≠ 0 := hε.ne'
    have hsq0 : √(p.1⁻¹) ≠ 0 := (Real.sqrt_pos.2 hpinv).ne'
    field_simp
  unfold B0220.chart
  rw [h1, h2, h3]

private theorem fieldU_at_chartPt {ε : ℝ} (hε : 0 < ε) (g : B0220.Profile → B0220.Merid)
    {p : B0220.Profile} (hp : 0 < p.1) :
    g p = √(p.1⁻¹) • !₂[B0220.fieldU ε g (chartPtX ε p, chartPtTau ε p) 0,
      B0220.fieldU ε g (chartPtX ε p, chartPtTau ε p) 2] := by
  have hpinv : 0 < p.1⁻¹ := inv_pos.2 hp
  have hsq_pos : 0 < √(p.1⁻¹) := Real.sqrt_pos.2 hpinv
  have hsq1 : √p.1 ≠ 0 := (Real.sqrt_pos.2 hp).ne'
  have hrad := radius_chartPtX (ε := ε) hp
  have huR : B0220.unitR (chartPtX ε p) = B0226.uTheta 0 := by
    simpa [chartPtX] using B0226.unitR_rotPt hsq_pos 0 (ε * p.2.2 * √(p.1⁻¹))
  have hf0 : B0220.frame (chartPtX ε p) (g p) 0 = g p 0 := by
    simp [B0220.frame_apply, huR, B0226.uTheta, B0226.rotPt, B0220.unitZ]
  have hf2 : B0220.frame (chartPtX ε p) (g p) 2 = g p 1 := by
    simp [B0220.frame_apply, huR, B0226.uTheta, B0226.rotPt, B0220.unitZ]
  have hU : B0220.fieldU ε g (chartPtX ε p, chartPtTau ε p) =
      (√(p.1⁻¹))⁻¹ • B0220.frame (chartPtX ε p) (g p) := by
    simp [B0220.fieldU, B0220.liftA, hrad, chart_chartPt hε hp]
  ext i
  fin_cases i
  · simp [hU, hf0, inv_mul_cancel_left₀ hsq1]
  · simp [hU, hf2, inv_mul_cancel_left₀ hsq1]

theorem meridProjProfile_eq_meridAvg {ε : ℝ} (hε : 0 < ε) {φ : ℝ × Space → CVec3}
    (hφ : Continuous φ) {p : B0220.Profile} (hp : 0 < p.1) :
    meridProjProfile ε φ p =
      ((B0220.jConst ε)⁻¹ * √(p.1⁻¹) : ℝ) •
        !₂[meridAvgPhase φ (chartPtTau ε p, chartPtX ε p) 0,
          meridAvgPhase φ (chartPtTau ε p, chartPtX ε p) 2] := by
  have hr_ne : B0220.radius (chartPtX ε p) ≠ 0 := by
    rw [radius_chartPtX hp]
    exact (Real.sqrt_pos.2 (inv_pos.2 hp)).ne'
  have hRe := fieldU_at_chartPt hε (reMerid (meridProjProfile ε φ)) hp
  rw [← coreFieldRe_eq_fieldU hε hφ (chartPtX ε p, chartPtTau ε p) hr_ne] at hRe
  have hIm_eq := (reMerid_meridProjProfile_negI ε φ).symm
  have hIm := fieldU_at_chartPt hε (reMerid (meridProjProfile ε ((-Complex.I) • φ))) hp
  rw [← coreFieldRe_eq_fieldU hε (hφ.const_smul (-Complex.I))
    (chartPtX ε p, chartPtTau ε p) hr_ne, ← hIm_eq] at hIm
  refine meridC_ext_re_im ?_ ?_
  · rw [show merReL (meridProjProfile ε φ p) = reMerid (meridProjProfile ε φ) p from rfl, hRe]
    ext i
    fin_cases i <;>
      (simp [merReL_apply, coreFieldRe, reVec3_apply]; ring)
  · rw [show merReL ((-Complex.I) • meridProjProfile ε φ p) =
      imMerid (meridProjProfile ε φ) p from rfl, hIm]
    simp only [coreFieldRe, meridAvgPhase_smul]
    ext i
    fin_cases i <;>
      (simp [merReL_apply, reVec3_apply]; ring)

theorem contDiffOn_meridProjProfile {ε P : ℝ} (hε : 0 < ε) (hPpos : 0 < P)
    {φ : ℝ × Space → CVec3} (hφ : IsPhaseTest P φ) :
    ContDiffOn ℝ ∞ (meridProjProfile ε φ) {p : B0220.Profile | 0 < p.1} := by
  have hm := (isPhaseTest_meridAvgPhase hPpos hφ).smooth
  have hopen : IsOpen {p : B0220.Profile | 0 < p.1} := isOpen_lt continuous_const continuous_fst
  intro p hp
  have hp' : 0 < p.1 := hp
  have hf1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : B0220.Profile =>
        ((B0220.jConst ε)⁻¹ * √(q.1⁻¹) : ℝ) •
          (!₂[meridAvgPhase φ (chartPtTau ε q, chartPtX ε q) 0,
            meridAvgPhase φ (chartPtTau ε q, chartPtX ε q) 2] : B0223.MeridC)) p := by
    have hsq : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : B0220.Profile => √(q.1⁻¹)) p :=
      (Real.contDiffAt_sqrt (inv_ne_zero hp'.ne')).comp p
        ((contDiffAt_inv ℝ hp'.ne').comp p contDiffAt_fst)
    have hlog : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : B0220.Profile => Real.log q.1) p :=
      (Real.contDiffAt_log.2 hp'.ne').comp p contDiffAt_fst
    have hη : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : B0220.Profile => q.2.2) p :=
      (contDiff_snd.comp contDiff_snd).contDiffAt
    have hq : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : B0220.Profile => q.2.1) p :=
      (contDiff_fst.comp contDiff_snd).contDiffAt
    have hsec : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : B0220.Profile => (chartPtTau ε q, chartPtX ε q)) p := by
      have heq : (fun q : B0220.Profile => (chartPtTau ε q, chartPtX ε q)) =
          fun q => (2 * ε * q.2.1 + Real.log q.1,
            √(q.1⁻¹) • coordinateVector 0 +
              (ε * q.2.2 * √(q.1⁻¹)) • coordinateVector 2) := by
        funext q
        simp [chartPtTau, chartPtX, B0226.rotPt_eq_comb]
      rw [heq]
      exact ((contDiffAt_const.mul hq).add hlog).prodMk
        ((hsq.smul contDiffAt_const).add (((contDiffAt_const.mul hη).mul hsq).smul contDiffAt_const))
    have hcomp : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : B0220.Profile => meridAvgPhase φ (chartPtTau ε q, chartPtX ε q)) p :=
      hm.contDiffAt.comp p hsec
    have hpair : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : B0220.Profile =>
          (!₂[meridAvgPhase φ (chartPtTau ε q, chartPtX ε q) 0,
            meridAvgPhase φ (chartPtTau ε q, chartPtX ε q) 2] : B0223.MeridC)) p := by
      set L0c : CVec3 →L[ℂ] B0223.MeridC :=
        (EuclideanSpace.proj (0 : Fin 3) : CVec3 →L[ℂ] ℂ).smulRight
            (EuclideanSpace.single (0 : Fin 2) (1 : ℂ) : B0223.MeridC) +
          (EuclideanSpace.proj (2 : Fin 3) : CVec3 →L[ℂ] ℂ).smulRight
            (EuclideanSpace.single (1 : Fin 2) (1 : ℂ) : B0223.MeridC)
      set L0 : CVec3 →L[ℝ] B0223.MeridC := L0c.restrictScalars ℝ
      have hL : (fun q : B0220.Profile =>
          (!₂[meridAvgPhase φ (chartPtTau ε q, chartPtX ε q) 0,
            meridAvgPhase φ (chartPtTau ε q, chartPtX ε q) 2] : B0223.MeridC)) =
          fun q => L0 (meridAvgPhase φ (chartPtTau ε q, chartPtX ε q)) := by
        funext q
        ext i
        fin_cases i <;> simp [L0, L0c]
      rw [hL]
      exact L0.contDiff.contDiffAt.comp p hcomp
    exact (contDiffAt_const.mul hsq).smul hpair
  have hev : meridProjProfile ε φ =ᶠ[𝓝 p] fun q : B0220.Profile =>
      ((B0220.jConst ε)⁻¹ * √(q.1⁻¹) : ℝ) •
        (!₂[meridAvgPhase φ (chartPtTau ε q, chartPtX ε q) 0,
          meridAvgPhase φ (chartPtTau ε q, chartPtX ε q) 2] : B0223.MeridC) := by
    filter_upwards [hopen.mem_nhds hp'] with q hq
    exact meridProjProfile_eq_meridAvg hε hφ.continuous hq
  exact (hf1.congr_of_eventuallyEq hev).contDiffWithinAt

theorem measurable_meridProjProfile {ε P : ℝ} (hε : 0 < ε) (hPpos : 0 < P)
    {φ : ℝ × Space → CVec3} (hφ : IsPhaseTest P φ) :
    Measurable (meridProjProfile ε φ) := by
  classical
  have hopen : IsOpen {p : B0220.Profile | 0 < p.1} := isOpen_lt continuous_const continuous_fst
  have hcont : ContinuousOn (meridProjProfile ε φ) {p : B0220.Profile | 0 < p.1} :=
    (contDiffOn_meridProjProfile hε hPpos hφ).continuousOn
  have hpw : meridProjProfile ε φ =
      {p : B0220.Profile | 0 < p.1}.piecewise (meridProjProfile ε φ) 0 := by
    funext p
    by_cases hp : 0 < p.1
    · simp [Set.piecewise, hp]
    · simp [Set.piecewise, meridProjProfile, hp]
  rw [hpw]
  exact hcont.measurable_piecewise continuousOn_const hopen.measurableSet

/-- **Theorem A (`IsMeridCoreTest`)**: for any phase test `φ`, `meridProjProfile ε φ` is an
axis-reaching meridional core test. -/
theorem isMeridCoreTest_meridProjProfile {ε c P : ℝ} (hε : 0 < ε) (hPpos : 0 < P)
    (hP : P = 2 * ε * c) {φ : ℝ × Space → CVec3} (hφ : IsPhaseTest P φ) :
    IsMeridCoreTest ε c (meridProjProfile ε φ) where
  smooth := contDiffOn_meridProjProfile hε hPpos hφ
  periodic := qPeriodic_meridProjProfile (by simpa [hP] using hφ.periodic)
  re_core := ⟨coreFieldRe ε φ, isCoreTestFieldVec_coreFieldRe hPpos hP hφ,
    fun y hr => coreFieldRe_eq_fieldU hε hφ.continuous y hr⟩
  im_core := by
    have hφ_im : IsPhaseTest P ((-Complex.I) • φ) :=
      hφ.clm_comp ((ContinuousLinearMap.lsmul ℂ ℂ (-Complex.I)).restrictScalars ℝ)
    refine ⟨coreFieldRe ε ((-Complex.I) • φ),
      isCoreTestFieldVec_coreFieldRe hPpos hP hφ_im, fun y hr => ?_⟩
    rw [← reMerid_meridProjProfile_negI]
    exact coreFieldRe_eq_fieldU hε hφ_im.continuous y hr

private theorem reVec3_phaseGen_eq_outerGenVec (ν ε : ℝ) {Φ : ℝ × Space → CVec3}
    (hΦ : ContDiff ℝ ∞ Φ) (x : Space) (τ : ℝ) :
    reVec3 (phaseGen ν ε Φ (τ, x)) =
      B0222.outerGenVec ν ε (fun y => reVec3 (Φ (y.2, y.1))) (x, τ) := by
  set V : Space × ℝ → Space := fun y => reVec3 (Φ (y.2, y.1))
  have hV : ContDiff ℝ 2 V :=
    (reVec3.contDiff.comp (hΦ.comp (contDiff_snd.prodMk contDiff_fst))).of_le (by simp)
  have hout := OuterSGen.cplx3_outerGenVec hV ν ε x τ
  have hre_out : B0222.outerGenVec ν ε V (x, τ) =
      reVec3 (phaseGen ν ε (OuterSGen.phaseFn V) (τ, x)) := by
    have h := congrArg reVec3 hout
    rw [reVec3_cplx3] at h
    exact h
  rw [hre_out]
  -- `reVec3` commutes with `phaseGen ν ε`
  set P_re : CVec3 →L[ℝ] CVec3 := cplx3.comp reVec3
  have hΦ1 : Differentiable ℝ Φ := hΦ.differentiable (by simp)
  have hfderiv_Pre : ∀ q w, fderiv ℝ (fun p => P_re (Φ p)) q w = P_re (fderiv ℝ Φ q w) := by
    intro q w
    have hc : HasFDerivAt (fun p => P_re (Φ p)) (P_re.comp (fderiv ℝ Φ q)) q :=
      P_re.hasFDerivAt.comp q (hΦ1 q).hasFDerivAt
    rw [hc.fderiv]
    rfl
  have hdy_Pre : ∀ j : Fin 3, dy j (fun p => P_re (Φ p)) = fun p => P_re (dy j Φ p) :=
    fun j => funext fun p => hfderiv_Pre p (0, coordinateVector j)
  have hdy_diff : ∀ j : Fin 3, Differentiable ℝ (dy j Φ) := fun j =>
    ((hΦ.fderiv_right (m := 1) (by simp)).clm_apply contDiff_const).differentiable (by simp)
  have hlap_Pre : lapT (fun p => P_re (Φ p)) (τ, x) = P_re (lapT Φ (τ, x)) := by
    simp only [lapT, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hdy_Pre j]
    have hc : HasFDerivAt (fun p => P_re (dy j Φ p))
        (P_re.comp (fderiv ℝ (dy j Φ) (τ, x))) (τ, x) :=
      P_re.hasFDerivAt.comp (τ, x) (hdy_diff j (τ, x)).hasFDerivAt
    show fderiv ℝ (fun p => P_re (dy j Φ p)) (τ, x) (0, coordinateVector j) = _
    rw [hc.fderiv]
    rfl
  have hrad_Pre : radialT (fun p => P_re (Φ p)) (τ, x) = P_re (radialT Φ (τ, x)) := by
    simp only [radialT, hdy_Pre, map_sum, map_smul]
  have hdτ_Pre : dτ (fun p => P_re (Φ p)) (τ, x) = P_re (dτ Φ (τ, x)) :=
    hfderiv_Pre (τ, x) (1, 0)
  have hphaseFn : OuterSGen.phaseFn V = fun p => P_re (Φ p) := rfl
  rw [hphaseFn]
  have hgen_Pre : phaseGen ν ε (fun p => P_re (Φ p)) (τ, x) = P_re (phaseGen ν ε Φ (τ, x)) := by
    simp only [phaseGen, hlap_Pre, hrad_Pre, hdτ_Pre, map_sub, map_add, map_smul]
  rw [hgen_Pre]
  simp [P_re, reVec3_cplx3]

private theorem reMerid_meridProjProfile_phaseGen (ν : ℝ) {ε c P : ℝ} (hε : 0 < ε)
    (hPpos : 0 < P) (_hP : P = 2 * ε * c) {φ : ℝ × Space → CVec3} (hφ : IsPhaseTest P φ)
    {p : B0220.Profile} (hp : 0 < p.1) :
    reMerid (meridProjProfile ε (phaseGen ν ε φ)) p =
      B0222.AepsVec ν ε (reMerid (meridProjProfile ε φ)) p := by
  set b := reMerid (meridProjProfile ε φ)
  set b' := reMerid (meridProjProfile ε (phaseGen ν ε φ))
  set V := coreFieldRe ε φ
  have hφ' : IsPhaseTest P (phaseGen ν ε φ) := isPhaseTest_phaseGen ν ε hφ
  have hb_smooth : ContDiffOn ℝ ∞ b {q : B0220.Profile | 0 < q.1} :=
    merReL.contDiff.comp_contDiffOn (contDiffOn_meridProjProfile hε hPpos hφ)
  have hopen : IsOpen {y : Space × ℝ | B0220.radius y.1 ≠ 0} :=
    isOpen_ne_fun (B0220.continuous_radius.comp continuous_fst) continuous_const
  have hopenS : IsOpen {q : B0220.Profile | 0 < q.1} := isOpen_lt continuous_const continuous_fst
  set y_p : Space × ℝ := (chartPtX ε p, chartPtTau ε p)
  have hr_ne : B0220.radius y_p.1 ≠ 0 := by
    rw [radius_chartPtX hp]
    exact (Real.sqrt_pos.2 (inv_pos.2 hp)).ne'
  -- 1. `outerGenVec ν ε V y_p = fieldU ε (AepsVec ν ε b) y_p`
  have hev : V =ᶠ[𝓝 y_p] B0220.fieldU ε b :=
    Filter.eventually_of_mem (hopen.mem_nhds hr_ne) fun y' hy' =>
      coreFieldRe_eq_fieldU hε hφ.continuous y' hy'
  have hpos_chart : 0 < (B0220.chart ε y_p).1 := by
    rw [chart_chartPt hε hp]
    exact hp
  have hbat : ContDiffAt ℝ 2 b (B0220.chart ε y_p) :=
    (hb_smooth.contDiffAt (hopenS.mem_nhds hpos_chart)).of_le (by simp)
  have hout1 : B0222.outerGenVec ν ε V y_p = B0220.fieldU ε (B0222.AepsVec ν ε b) y_p := by
    rw [outerGenVec_congr hev]
    exact B0222.outerGenVec_fieldU hε.ne' hr_ne hbat
  -- 2. `outerGenVec ν ε V y_p = fieldU ε b' y_p`
  have hm_smooth : ContDiff ℝ ∞ ((B0220.jConst ε)⁻¹ • meridAvgPhase φ) :=
    (isPhaseTest_meridAvgPhase hPpos hφ).smooth.const_smul (B0220.jConst ε)⁻¹
  have hV_eq : V = fun y => reVec3 (((B0220.jConst ε)⁻¹ • meridAvgPhase φ) (y.2, y.1)) := by
    funext y
    simp [V, coreFieldRe]
  have hsmul_gen : phaseGen ν ε ((B0220.jConst ε)⁻¹ • meridAvgPhase φ) (y_p.2, y_p.1) =
      (B0220.jConst ε)⁻¹ • phaseGen ν ε (meridAvgPhase φ) (y_p.2, y_p.1) := by
    set c0 : ℝ := (B0220.jConst ε)⁻¹
    have h := phaseGen_clm_comp ν ε
      (ContinuousLinearMap.lsmul ℂ ℂ (c0 : ℂ))
      (isPhaseTest_meridAvgPhase hPpos hφ).smooth (y_p.2, y_p.1)
    have hfun : (fun q => (ContinuousLinearMap.lsmul ℂ ℂ (c0 : ℂ))
        (meridAvgPhase φ q)) = c0 • meridAvgPhase φ := by
      funext q
      exact Complex.coe_smul c0 (meridAvgPhase φ q)
    rw [← hfun, h]
    exact Complex.coe_smul c0 (phaseGen ν ε (meridAvgPhase φ) (y_p.2, y_p.1))
  have hout2 : B0222.outerGenVec ν ε V y_p = B0220.fieldU ε b' y_p := by
    rw [hV_eq, ← reVec3_phaseGen_eq_outerGenVec ν ε hm_smooth y_p.1 y_p.2, hsmul_gen,
      map_smul, phaseGen_meridAvgPhase ν ε hPpos hφ (y_p.2, y_p.1)]
    exact coreFieldRe_eq_fieldU hε hφ'.continuous y_p hr_ne
  -- 3. compare at `y_p` via `fieldU_at_chartPt`
  have hU_eq : B0220.fieldU ε b' y_p = B0220.fieldU ε (B0222.AepsVec ν ε b) y_p :=
    hout2.symm.trans hout1
  rw [fieldU_at_chartPt hε b' hp, fieldU_at_chartPt hε (B0222.AepsVec ν ε b) hp, hU_eq]

/-- **Theorem C (`meridProjProfile_phaseGen`)**: for `0 < p.1`, `meridProjProfile` intertwines
`phaseGen ν ε` with `AepsVecC ν ε`. -/
theorem meridProjProfile_phaseGen (ν : ℝ) {ε c P : ℝ} (hε : 0 < ε) (hPpos : 0 < P)
    (hP : P = 2 * ε * c) {ψ : ℝ × Space → CVec3} (hψ : IsPhaseTest P ψ)
    {p : B0220.Profile} (hp : 0 < p.1) :
    meridProjProfile ε (phaseGen ν ε ψ) p = AepsVecC ν ε (meridProjProfile ε ψ) p := by
  set u := meridProjProfile ε ψ
  set u' := meridProjProfile ε (phaseGen ν ε ψ)
  have hopenS : IsOpen {q : B0220.Profile | 0 < q.1} := isOpen_lt continuous_const continuous_fst
  have hu_at : ContDiffAt ℝ 2 u p :=
    ((contDiffOn_meridProjProfile hε hPpos hψ).contDiffAt (hopenS.mem_nhds hp)).of_le (by simp)
  have hRe : merReL (u' p) = merReL (AepsVecC ν ε u p) := by
    rw [merReL_AepsVecC ν ε hu_at]
    exact reMerid_meridProjProfile_phaseGen ν hε hPpos hP hψ hp
  have hψ_im : IsPhaseTest P ((-Complex.I) • ψ) :=
    hψ.clm_comp ((ContinuousLinearMap.lsmul ℂ ℂ (-Complex.I)).restrictScalars ℝ)
  have hgen_im : phaseGen ν ε ((-Complex.I) • ψ) = (-Complex.I) • phaseGen ν ε ψ := by
    funext q
    exact phaseGen_clm_comp ν ε (ContinuousLinearMap.lsmul ℂ ℂ (-Complex.I)) hψ.smooth q
  have hIm : merReL ((-Complex.I) • u' p) = merReL ((-Complex.I) • AepsVecC ν ε u p) := by
    rw [merIm_AepsVecC ν ε hu_at]
    have h1 := reMerid_meridProjProfile_phaseGen ν hε hPpos hP hψ_im hp
    have he1 : reMerid (meridProjProfile ε (phaseGen ν ε ((-Complex.I) • ψ))) = imMerid u' := by
      rw [hgen_im]
      exact reMerid_meridProjProfile_negI ε (phaseGen ν ε ψ)
    have he2 : reMerid (meridProjProfile ε ((-Complex.I) • ψ)) = imMerid u :=
      reMerid_meridProjProfile_negI ε ψ
    rwa [he1, he2] at h1
  exact meridC_ext_re_im hRe hIm

end UnforcedLeray.Short.PartIIa.MeridProjAux
