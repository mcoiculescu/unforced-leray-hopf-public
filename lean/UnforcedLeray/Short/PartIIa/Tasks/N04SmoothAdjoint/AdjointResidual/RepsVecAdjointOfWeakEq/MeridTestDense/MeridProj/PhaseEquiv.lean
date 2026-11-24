import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N04_3_3_2
import UnforcedLeray.Short.PartIIa.Tasks.F05aAdjResolventSolution.OpsUnderIntegral
import UnforcedLeray.Short.PartIIa.Tasks.F05aAdjResolventSolution.PhaseTestDerivBounded
import UnforcedLeray.Lib.AxisymmetricB.Average
import UnforcedLeray.Units.B0226.Rotation

/-!
# `O(2)`-averaging on phase tests and commutation with `phaseGen`

Helper 1 for `PartII-a:N04/3/3/2/2` (`MeridProjOfPhaseTest`).
Source of record: `the November 2 reference manuscript`,
lines 1477–1478 (the outer generator commutes with rotations and reflections fixing the axis) and
3340–3352 (Cartesian outer operator `νε²Δ + x·∇/2 + 1/2 - ∂_τ`).

For any `g : Space ≃ₗᵢ[ℝ] Space`, `actPhase g φ (τ, x) = g⁻¹ φ(τ, g x)` preserves `IsPhaseTest P`
and commutes pointwise with `phaseGen ν ε`. Averaging over `θ ∈ (0, 2π]` via `Axi.angμ`
(`rotAvgPhase`) and symmetrizing with `Axi.reflY` (`meridAvgPhase`) preserves `IsPhaseTest P` and
commutes pointwise with `phaseGen ν ε` via `paramIntegralSmooth_proof` and `opsUnderIntegral_proof`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa.MeridProjAux

open UnforcedLeray.PhaseSpace
open UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization (cplx3 cplx3_apply)

/-! ### 1. Real part and complexified orthogonal maps on `CVec3` -/

/-- Real part map `CVec3 →ₗ[ℝ] Space`. -/
def reVec3Lin : CVec3 →ₗ[ℝ] Space where
  toFun w := WithLp.toLp 2 fun i => (w i).re
  map_add' u v := by ext i; simp
  map_smul' r v := by ext i; simp

/-- Real part continuous linear map `CVec3 →L[ℝ] Space`. -/
def reVec3 : CVec3 →L[ℝ] Space := LinearMap.toContinuousLinearMap reVec3Lin

@[simp] theorem reVec3_apply (w : CVec3) (i : Fin 3) : reVec3 w i = (w i).re := rfl

theorem reVec3_cplx3 (v : Space) : reVec3 (cplx3 v) = v := by
  ext i
  simp [reVec3_apply, cplx3_apply]

theorem cplx3_re_im (w : CVec3) :
    cplx3 (reVec3 w) + Complex.I • cplx3 (reVec3 ((-Complex.I) • w)) = w := by
  ext i
  simp only [PiLp.add_apply, PiLp.smul_apply, cplx3_apply, reVec3_apply, smul_eq_mul]
  apply Complex.ext <;> simp

theorem norm_sq_split_cvec3 (w : CVec3) :
    ‖w‖ ^ 2 = ‖reVec3 w‖ ^ 2 + ‖reVec3 ((-Complex.I) • w)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
  simp [reVec3_apply, Complex.sq_norm, Complex.normSq_apply]
  ring

/-- Matrix entries `(g e_j)_i` of a linear isometry equivalence `g : Space ≃ₗᵢ[ℝ] Space`. -/
def rc (g : Space ≃ₗᵢ[ℝ] Space) (i j : Fin 3) : ℝ := g (coordinateVector j) i

theorem inner_coord_left (i : Fin 3) (v : Space) : inner ℝ (coordinateVector i) v = v i := by
  simp [coordinateVector, EuclideanSpace.inner_single_left]

theorem space_eq_sum_coord (v : Space) : v = ∑ j : Fin 3, v j • coordinateVector j := by
  ext i
  fin_cases i <;> simp [Fin.sum_univ_three, coordinateVector]

theorem g_apply_coord (g : Space ≃ₗᵢ[ℝ] Space) (x : Space) (i : Fin 3) :
    g x i = ∑ j : Fin 3, rc g i j * x j := by
  conv_lhs => rw [space_eq_sum_coord x]
  rw [map_sum]
  simp only [map_smul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, rc,
    mul_comm]

theorem rc_symm (g : Space ≃ₗᵢ[ℝ] Space) (i j : Fin 3) : rc g.symm i j = rc g j i := by
  rw [rc, rc, ← inner_coord_left i (g.symm (coordinateVector j)),
    ← g.inner_map_map (coordinateVector i), g.apply_symm_apply, real_inner_comm,
    inner_coord_left]

theorem sum_rc_mul_rc (g : Space ≃ₗᵢ[ℝ] Space) (j k : Fin 3) :
    ∑ i : Fin 3, rc g i j * rc g i k = if j = k then 1 else 0 := by
  have h : ∑ i : Fin 3, rc g i j * rc g i k =
      inner ℝ (g (coordinateVector j)) (g (coordinateVector k)) := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [rc, mul_comm]
  rw [h, g.inner_map_map, inner_coord_left]
  simp [coordinateVector]

theorem sum_rc_mul_rc_right (g : Space ≃ₗᵢ[ℝ] Space) (i k : Fin 3) :
    ∑ j : Fin 3, rc g i j * rc g k j = if i = k then 1 else 0 := by
  simp_rw [← rc_symm g]
  exact sum_rc_mul_rc g.symm i k

/-- Complexification of `g : Space ≃ₗᵢ[ℝ] Space` as a `ℂ`-linear map on `CVec3`. -/
def linIsoCLin (g : Space ≃ₗᵢ[ℝ] Space) : CVec3 →ₗ[ℂ] CVec3 where
  toFun w := WithLp.toLp 2 fun i => ∑ j : Fin 3, (rc g i j : ℂ) * w j
  map_add' u v := by
    ext i
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    ext i
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring

/-- Complexification of `g : Space ≃ₗᵢ[ℝ] Space` as a continuous `ℂ`-linear map on `CVec3`. -/
def linIsoC (g : Space ≃ₗᵢ[ℝ] Space) : CVec3 →L[ℂ] CVec3 :=
  LinearMap.toContinuousLinearMap (linIsoCLin g)

@[simp] theorem linIsoC_apply (g : Space ≃ₗᵢ[ℝ] Space) (w : CVec3) (i : Fin 3) :
    linIsoC g w i = ∑ j : Fin 3, (rc g i j : ℂ) * w j := rfl

theorem linIsoC_cplx3 (g : Space ≃ₗᵢ[ℝ] Space) (v : Space) :
    linIsoC g (cplx3 v) = cplx3 (g v) := by
  ext i
  simp [linIsoC_apply, cplx3_apply, g_apply_coord]

theorem reVec3_linIsoC (g : Space ≃ₗᵢ[ℝ] Space) (w : CVec3) :
    reVec3 (linIsoC g w) = g (reVec3 w) := by
  ext i
  simp [reVec3_apply, linIsoC_apply, g_apply_coord]

theorem norm_linIsoC_apply (g : Space ≃ₗᵢ[ℝ] Space) (w : CVec3) :
    ‖linIsoC g w‖ = ‖w‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_split_cvec3, norm_sq_split_cvec3,
    reVec3_linIsoC, ← map_smul, reVec3_linIsoC, g.norm_map, g.norm_map]

theorem norm_linIsoCR_le (g : Space ≃ₗᵢ[ℝ] Space) :
    ‖(linIsoC g).restrictScalars ℝ‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by
    rw [one_mul]
    exact (norm_linIsoC_apply g w).le

/-! ### 2. Orthogonal action `actPhase` and commutation with `phaseGen` -/

/-- `(τ, x) ↦ (τ, g x)` as a continuous `ℝ`-linear map on `ℝ × Space`. -/
def prodCLM (g : Space ≃ₗᵢ[ℝ] Space) : (ℝ × Space) →L[ℝ] (ℝ × Space) :=
  (ContinuousLinearMap.id ℝ ℝ).prodMap g.toLinearIsometry.toContinuousLinearMap

@[simp] theorem prodCLM_apply (g : Space ≃ₗᵢ[ℝ] Space) (q : ℝ × Space) :
    prodCLM g q = (q.1, g q.2) := rfl

theorem norm_prodCLM_le (g : Space ≃ₗᵢ[ℝ] Space) : ‖prodCLM g‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun q => by
    rw [one_mul, Prod.norm_def, Prod.norm_def, prodCLM_apply, g.norm_map]

/-- Orthogonal action `(g · φ)(τ, x) = g⁻¹ (φ(τ, g x))` on phase functions. -/
def actPhase (g : Space ≃ₗᵢ[ℝ] Space) (φ : ℝ × Space → CVec3) : ℝ × Space → CVec3 :=
  fun q => linIsoC g.symm (φ (prodCLM g q))

theorem actPhase_smul (g : Space ≃ₗᵢ[ℝ] Space) (c : ℂ) (φ : ℝ × Space → CVec3) :
    actPhase g (c • φ) = c • actPhase g φ := by
  funext q
  simp [actPhase]

theorem isPhaseTest_actPhase (g : Space ≃ₗᵢ[ℝ] Space) {P : ℝ} {φ : ℝ × Space → CVec3}
    (hφ : IsPhaseTest P φ) : IsPhaseTest P (actPhase g φ) where
  smooth := ((linIsoC g.symm).restrictScalars ℝ).contDiff.comp
    (hφ.smooth.comp (prodCLM g).contDiff)
  periodic τ y := by simp [actPhase, prodCLM_apply, hφ.periodic τ (g y)]
  bounded_support := by
    obtain ⟨R, hR⟩ := hφ.bounded_support
    refine ⟨R, fun τ y hy => ?_⟩
    rw [← g.norm_map y] at hy
    simp [actPhase, prodCLM_apply, hR τ (g y) hy]

theorem isPhaseTest_phaseGen (ν ε : ℝ) {P : ℝ} {φ : ℝ × Space → CVec3}
    (hφ : IsPhaseTest P φ) : IsPhaseTest P (phaseGen ν ε φ) := by
  have heq : phaseGen ν ε φ =
      (ν * ε ^ 2) • lapT φ + (1 / 2 : ℝ) • radialT φ + (1 / 2 : ℝ) • φ + (-dτ φ) := by
    funext q
    simp [phaseGen, sub_eq_add_neg, add_assoc]
  rw [heq]
  exact (((hφ.lapT.const_smul _).add (hφ.radialT.const_smul _)).add
    (hφ.const_smul _)).add hφ.dτ.neg

private theorem fderiv_clm_comp {L : CVec3 →L[ℂ] CVec3} {φ : ℝ × Space → CVec3}
    (hφ : Differentiable ℝ φ) (q v : ℝ × Space) :
    fderiv ℝ (fun p => L (φ p)) q v = L (fderiv ℝ φ q v) := by
  have h : HasFDerivAt (fun p => L (φ p))
      ((L.restrictScalars ℝ).comp (fderiv ℝ φ q)) q :=
    (L.restrictScalars ℝ).hasFDerivAt.comp q (hφ q).hasFDerivAt
  rw [h.fderiv]
  rfl

theorem phaseGen_clm_comp (ν ε : ℝ) (L : CVec3 →L[ℂ] CVec3) {φ : ℝ × Space → CVec3}
    (hφ : ContDiff ℝ ∞ φ) (q : ℝ × Space) :
    phaseGen ν ε (fun p => L (φ p)) q = L (phaseGen ν ε φ q) := by
  have hφ1 : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hdτ : dτ (fun p => L (φ p)) q = L (dτ φ q) := fderiv_clm_comp hφ1 q (1, 0)
  have hdy : ∀ j : Fin 3, dy j (fun p => L (φ p)) = fun p => L (dy j φ p) :=
    fun j => funext fun p => fderiv_clm_comp hφ1 p (0, coordinateVector j)
  have hdy_diff : ∀ j : Fin 3, Differentiable ℝ (dy j φ) := fun j =>
    ((hφ.fderiv_right (m := 1) (by simp)).clm_apply contDiff_const).differentiable (by simp)
  have hrad : radialT (fun p => L (φ p)) q = L (radialT φ q) := by
    simp only [radialT, hdy, map_sum, ContinuousLinearMap.map_smul_of_tower]
  have hlap : lapT (fun p => L (φ p)) q = L (lapT φ q) := by
    simp only [lapT, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hdy j]
    exact fderiv_clm_comp (hdy_diff j) q (0, coordinateVector j)
  simp only [phaseGen, hlap, hrad, hdτ, map_sub, map_add,
    ContinuousLinearMap.map_smul_of_tower]

private theorem dy_comp_prodCLM (g : Space ≃ₗᵢ[ℝ] Space) {φ : ℝ × Space → CVec3}
    (hφ : ContDiff ℝ ∞ φ) (j : Fin 3) :
    dy j (fun p => φ (prodCLM g p)) =
      fun q => ∑ k : Fin 3, rc g k j • dy k φ (prodCLM g q) := by
  have hφ1 : Differentiable ℝ φ := hφ.differentiable (by simp)
  funext q
  have hc : HasFDerivAt (fun p => φ (prodCLM g p))
      ((fderiv ℝ φ (prodCLM g q)).comp (prodCLM g)) q :=
    (hφ1 (prodCLM g q)).hasFDerivAt.comp q (prodCLM g).hasFDerivAt
  have hej : prodCLM g (0, coordinateVector j) =
      ∑ k : Fin 3, rc g k j • ((0, coordinateVector k) : ℝ × Space) := by
    ext
    · simp [Prod.fst_sum]
    · simp only [prodCLM_apply, Prod.snd_sum, Prod.smul_snd]
      rw [space_eq_sum_coord (g (coordinateVector j))]
      rfl
  show fderiv ℝ (fun p => φ (prodCLM g p)) q (0, coordinateVector j) = _
  rw [hc.fderiv, ContinuousLinearMap.comp_apply, hej, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul]
  rfl

private theorem dτ_comp_prodCLM (g : Space ≃ₗᵢ[ℝ] Space) {φ : ℝ × Space → CVec3}
    (hφ : ContDiff ℝ ∞ φ) (q : ℝ × Space) :
    dτ (fun p => φ (prodCLM g p)) q = dτ φ (prodCLM g q) := by
  have hφ1 : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hc : HasFDerivAt (fun p => φ (prodCLM g p))
      ((fderiv ℝ φ (prodCLM g q)).comp (prodCLM g)) q :=
    (hφ1 (prodCLM g q)).hasFDerivAt.comp q (prodCLM g).hasFDerivAt
  show fderiv ℝ (fun p => φ (prodCLM g p)) q (1, 0) = _
  rw [hc.fderiv, ContinuousLinearMap.comp_apply]
  simp [prodCLM_apply, dτ]

private theorem radialT_comp_prodCLM (g : Space ≃ₗᵢ[ℝ] Space) {φ : ℝ × Space → CVec3}
    (hφ : ContDiff ℝ ∞ φ) (q : ℝ × Space) :
    radialT (fun p => φ (prodCLM g p)) q = radialT φ (prodCLM g q) := by
  simp only [radialT, dy_comp_prodCLM g hφ, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  simp only [prodCLM_apply, g_apply_coord g q.2 k]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

private theorem lapT_comp_prodCLM (g : Space ≃ₗᵢ[ℝ] Space) {φ : ℝ × Space → CVec3}
    (hφ : ContDiff ℝ ∞ φ) (q : ℝ × Space) :
    lapT (fun p => φ (prodCLM g p)) q = lapT φ (prodCLM g q) := by
  have hdy_smooth : ∀ k : Fin 3, ContDiff ℝ ∞ (dy k φ) := fun k =>
    (hφ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  have hstep : ∀ j : Fin 3, dy j (dy j (fun p => φ (prodCLM g p))) q =
      ∑ k : Fin 3, ∑ l : Fin 3, (rc g k j * rc g l j) • dy l (dy k φ) (prodCLM g q) := by
    intro j
    rw [dy_comp_prodCLM g hφ]
    have hd : ∀ k : Fin 3, DifferentiableAt ℝ (fun p => dy k φ (prodCLM g p)) q := fun k =>
      ((hdy_smooth k).comp (prodCLM g).contDiff).differentiable (by simp) q
    have hsum : HasFDerivAt
        (fun p => ∑ k : Fin 3, rc g k j • dy k φ (prodCLM g p))
        (∑ k : Fin 3, rc g k j • fderiv ℝ (fun p => dy k φ (prodCLM g p)) q) q :=
      HasFDerivAt.fun_sum fun k _ => (hd k).hasFDerivAt.const_smul (rc g k j)
    show fderiv ℝ (fun p => ∑ k : Fin 3, rc g k j • dy k φ (prodCLM g p)) q
        (0, coordinateVector j) = _
    rw [hsum.fderiv, sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_apply]
    change rc g k j • dy j (fun p => dy k φ (prodCLM g p)) q = _
    rw [dy_comp_prodCLM g (hdy_smooth k), Finset.smul_sum]
    exact Finset.sum_congr rfl fun l _ => smul_smul _ _ _
  simp only [lapT, hstep]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  have hinner : ∀ l : Fin 3,
      (∑ j : Fin 3, (rc g k j * rc g l j) • dy l (dy k φ) (prodCLM g q)) =
      (if k = l then (1 : ℝ) else 0) • dy l (dy k φ) (prodCLM g q) := fun l => by
    rw [← Finset.sum_smul, sum_rc_mul_rc_right g k l]
  simp_rw [hinner]
  simp

/-- `phaseGen ν ε` commutes pointwise with `actPhase g` for every `g : Space ≃ₗᵢ[ℝ] Space`. -/
theorem phaseGen_actPhase (ν ε : ℝ) (g : Space ≃ₗᵢ[ℝ] Space) {φ : ℝ × Space → CVec3}
    (hφ : ContDiff ℝ ∞ φ) (q : ℝ × Space) :
    phaseGen ν ε (actPhase g φ) q = actPhase g (phaseGen ν ε φ) q := by
  have hcomp : ContDiff ℝ ∞ (fun p => φ (prodCLM g p)) := hφ.comp (prodCLM g).contDiff
  show phaseGen ν ε (fun p => linIsoC g.symm (φ (prodCLM g p))) q =
    linIsoC g.symm (phaseGen ν ε φ (prodCLM g q))
  rw [phaseGen_clm_comp ν ε (linIsoC g.symm) hcomp q]
  congr 1
  simp only [phaseGen, lapT_comp_prodCLM g hφ, radialT_comp_prodCLM g hφ,
    dτ_comp_prodCLM g hφ]

/-! ### 3. Parameter family over `Axi.angμ` and `O(2)`-averaging -/

private def rotBasis0 : Space →L[ℝ] Space :=
  (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).smulRight (coordinateVector 0) +
    (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).smulRight (coordinateVector 1)

private def rotBasis1 : Space →L[ℝ] Space :=
  (-(EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ)).smulRight (coordinateVector 0) +
    (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).smulRight (coordinateVector 1)

private def rotBasis2 : Space →L[ℝ] Space :=
  (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).smulRight (coordinateVector 2)

private theorem rotZ_clm_eq (θ : ℝ) :
    (B0226.rotZ θ).toLinearIsometry.toContinuousLinearMap =
      Real.cos θ • rotBasis0 + Real.sin θ • rotBasis1 + rotBasis2 := by
  ext x i
  fin_cases i <;>
    simp [B0226.rotZ_apply, B0226.rotFun, rotBasis0, rotBasis1, rotBasis2, coordinateVector] <;>
    ring

private theorem continuous_prodCLM_rotZ :
    Continuous fun θ : ℝ => prodCLM (B0226.rotZ θ) := by
  have hrot : Continuous fun θ : ℝ => (B0226.rotZ θ).toLinearIsometry.toContinuousLinearMap := by
    simp_rw [rotZ_clm_eq]
    exact ((Real.continuous_cos.smul continuous_const).add
      (Real.continuous_sin.smul continuous_const)).add continuous_const
  have h : (fun θ : ℝ => prodCLM (B0226.rotZ θ)) = fun θ =>
      ((ContinuousLinearMap.inl ℝ ℝ Space).comp (ContinuousLinearMap.fst ℝ ℝ Space)) +
        ((ContinuousLinearMap.inr ℝ ℝ Space).comp
          (((B0226.rotZ θ).toLinearIsometry.toContinuousLinearMap).comp
            (ContinuousLinearMap.snd ℝ ℝ Space))) := by
    ext θ q <;> simp [prodCLM_apply]
  rw [h]
  have hcomp : Continuous fun θ : ℝ =>
      (ContinuousLinearMap.inr ℝ ℝ Space).comp
        (((B0226.rotZ θ).toLinearIsometry.toContinuousLinearMap).comp
          (ContinuousLinearMap.snd ℝ ℝ Space)) := by
    fun_prop
  exact continuous_const.add hcomp

private def rotBasisC0 : CVec3 →L[ℝ] CVec3 :=
  ((EuclideanSpace.proj (0 : Fin 3) : CVec3 →L[ℂ] ℂ).restrictScalars ℝ).smulRight
      (EuclideanSpace.single 0 (1 : ℂ)) +
    ((EuclideanSpace.proj (1 : Fin 3) : CVec3 →L[ℂ] ℂ).restrictScalars ℝ).smulRight
      (EuclideanSpace.single 1 (1 : ℂ))

private def rotBasisC1 : CVec3 →L[ℝ] CVec3 :=
  (-((EuclideanSpace.proj (1 : Fin 3) : CVec3 →L[ℂ] ℂ).restrictScalars ℝ)).smulRight
      (EuclideanSpace.single 0 (1 : ℂ)) +
    ((EuclideanSpace.proj (0 : Fin 3) : CVec3 →L[ℂ] ℂ).restrictScalars ℝ).smulRight
      (EuclideanSpace.single 1 (1 : ℂ))

private def rotBasisC2 : CVec3 →L[ℝ] CVec3 :=
  ((EuclideanSpace.proj (2 : Fin 3) : CVec3 →L[ℂ] ℂ).restrictScalars ℝ).smulRight
    (EuclideanSpace.single 2 (1 : ℂ))

private theorem linIsoCR_rotZ_eq (θ : ℝ) :
    (linIsoC (B0226.rotZ θ)).restrictScalars ℝ =
      Real.cos θ • rotBasisC0 + Real.sin θ • rotBasisC1 + rotBasisC2 := by
  ext w i
  fin_cases i <;>
    (simp [linIsoC_apply, rc, B0226.rotZ_apply, B0226.rotFun, Fin.sum_univ_three,
      rotBasisC0, rotBasisC1, rotBasisC2, coordinateVector]; try ring)

private theorem continuous_linIsoCR_rotZ_symm :
    Continuous fun θ : ℝ => (linIsoC (B0226.rotZ θ).symm).restrictScalars ℝ := by
  have heq : ∀ θ : ℝ, (B0226.rotZ θ).symm = B0226.rotZ (-θ) := fun θ => by
    ext x i
    rfl
  simp_rw [heq, linIsoCR_rotZ_eq]
  exact (((Real.continuous_cos.comp continuous_neg).smul continuous_const).add
    ((Real.continuous_sin.comp continuous_neg).smul continuous_const)).add continuous_const

private theorem iteratedFDeriv_actPhase (g : Space ≃ₗᵢ[ℝ] Space) {φ : ℝ × Space → CVec3}
    (hφ : ContDiff ℝ ∞ φ) (k : ℕ) (q : ℝ × Space) :
    iteratedFDeriv ℝ k (actPhase g φ) q =
      ((linIsoC g.symm).restrictScalars ℝ).compContinuousMultilinearMap
        ((iteratedFDeriv ℝ k φ (prodCLM g q)).compContinuousLinearMap
          (fun _ => prodCLM g)) := by
  have hcomp : ContDiff ℝ ∞ (φ ∘ prodCLM g) := hφ.comp (prodCLM g).contDiff
  have e1 : actPhase g φ = ((linIsoC g.symm).restrictScalars ℝ) ∘ (φ ∘ prodCLM g) := rfl
  rw [e1, ((linIsoC g.symm).restrictScalars ℝ).iteratedFDeriv_comp_left
    (hcomp.contDiffAt.of_le (by exact_mod_cast le_top)) le_rfl,
    (prodCLM g).iteratedFDeriv_comp_right (i := k) hφ q (by exact_mod_cast le_top)]

theorem paramFamilyHyp_rotZ {P : ℝ} (hP : 0 < P) {φ : ℝ × Space → CVec3}
    (hφ : IsPhaseTest P φ) :
    ParamFamilyHyp Axi.angμ (fun θ => actPhase (B0226.rotZ θ) φ) := by
  refine ⟨Filter.Eventually.of_forall fun θ => (isPhaseTest_actPhase (B0226.rotZ θ) hφ).smooth,
    ?_, ?_⟩
  · intro k q
    have hcont : Continuous fun θ : ℝ =>
        iteratedFDeriv ℝ k (actPhase (B0226.rotZ θ) φ) q := by
      simp_rw [iteratedFDeriv_actPhase (B0226.rotZ _) hφ.smooth k q]
      have hT : Continuous (iteratedFDeriv ℝ k φ) :=
        hφ.smooth.continuous_iteratedFDeriv (by exact_mod_cast le_top)
      have hS : Continuous fun θ : ℝ => iteratedFDeriv ℝ k φ (prodCLM (B0226.rotZ θ) q) :=
        hT.comp (continuous_prodCLM_rotZ.clm_apply continuous_const)
      have hL : Continuous fun θ : ℝ =>
          (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
            ℝ (fun _ : Fin k => ℝ × Space) (fun _ : Fin k => ℝ × Space) CVec3)
              (fun _ => prodCLM (B0226.rotZ θ)) :=
        (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
          ℝ (fun _ : Fin k => ℝ × Space) (fun _ : Fin k => ℝ × Space) CVec3).cont.comp
            (continuous_pi fun _ => continuous_prodCLM_rotZ)
      have hinner : Continuous fun θ : ℝ =>
          (iteratedFDeriv ℝ k φ (prodCLM (B0226.rotZ θ) q)).compContinuousLinearMap
            (fun _ => prodCLM (B0226.rotZ θ)) :=
        hL.clm_apply hS
      exact ((ContinuousLinearMap.compContinuousMultilinearMapL ℝ
        (fun _ : Fin k => ℝ × Space) CVec3 CVec3).continuous.comp
          continuous_linIsoCR_rotZ_symm).clm_apply hinner
    exact hcont.aestronglyMeasurable
  · intro k
    obtain ⟨M, hM0, hM⟩ := phaseTestDerivBounded_proof P hP φ hφ k
    refine ⟨fun _ => M, integrable_const M, Filter.Eventually.of_forall fun θ q => ?_⟩
    rw [iteratedFDeriv_actPhase (B0226.rotZ θ) hφ.smooth k q]
    have h1 := ((linIsoC (B0226.rotZ θ).symm).restrictScalars ℝ).norm_compContinuousMultilinearMap_le
      ((iteratedFDeriv ℝ k φ (prodCLM (B0226.rotZ θ) q)).compContinuousLinearMap
        (fun _ => prodCLM (B0226.rotZ θ)))
    have h2 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDeriv ℝ k φ (prodCLM (B0226.rotZ θ) q))
      (fun _ : Fin k => prodCLM (B0226.rotZ θ))
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h2
    have h3 : ‖prodCLM (B0226.rotZ θ)‖ ^ k ≤ 1 := by
      calc ‖prodCLM (B0226.rotZ θ)‖ ^ k ≤ (1 : ℝ) ^ k :=
            pow_le_pow_left₀ (norm_nonneg _) (norm_prodCLM_le _) k
        _ = 1 := one_pow k
    have h4 : ‖(iteratedFDeriv ℝ k φ (prodCLM (B0226.rotZ θ) q)).compContinuousLinearMap
        (fun _ => prodCLM (B0226.rotZ θ))‖ ≤ M := by
      calc ‖(iteratedFDeriv ℝ k φ (prodCLM (B0226.rotZ θ) q)).compContinuousLinearMap
              (fun _ => prodCLM (B0226.rotZ θ))‖
          ≤ ‖iteratedFDeriv ℝ k φ (prodCLM (B0226.rotZ θ) q)‖ *
              ‖prodCLM (B0226.rotZ θ)‖ ^ k := h2
        _ ≤ M * 1 := mul_le_mul (hM _) h3 (pow_nonneg (norm_nonneg _) k) hM0
        _ = M := mul_one M
    calc ‖((linIsoC (B0226.rotZ θ).symm).restrictScalars ℝ).compContinuousMultilinearMap _‖
        ≤ ‖(linIsoC (B0226.rotZ θ).symm).restrictScalars ℝ‖ *
            ‖(iteratedFDeriv ℝ k φ (prodCLM (B0226.rotZ θ) q)).compContinuousLinearMap
              (fun _ => prodCLM (B0226.rotZ θ))‖ := h1
      _ ≤ 1 * M := mul_le_mul (norm_linIsoCR_le _) h4 (norm_nonneg _) zero_le_one
      _ = M := one_mul M

/-- Rotational average of a phase function over `θ ∈ (0, 2π]` with respect to `Axi.angμ`. -/
def rotAvgPhase (φ : ℝ × Space → CVec3) (q : ℝ × Space) : CVec3 :=
  ∫ θ, actPhase (B0226.rotZ θ) φ q ∂Axi.angμ

/-- Meridional `O(2)`-average (rotational average symmetrized under `Axi.reflY`). -/
def meridAvgPhase (φ : ℝ × Space → CVec3) (q : ℝ × Space) : CVec3 :=
  (1 / 2 : ℝ) • (rotAvgPhase φ q + actPhase Axi.reflY (rotAvgPhase φ) q)

theorem rotAvgPhase_eq_setIntegral (φ : ℝ × Space → CVec3) (q : ℝ × Space) :
    rotAvgPhase φ q =
      (2 * Real.pi)⁻¹ • ∫ θ in Ioc 0 (2 * Real.pi), actPhase (B0226.rotZ θ) φ q := by
  rw [rotAvgPhase, Axi.angμ, integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (by positivity)]

theorem rotAvgPhase_smul (c : ℂ) (φ : ℝ × Space → CVec3) :
    rotAvgPhase (c • φ) = c • rotAvgPhase φ := by
  funext q
  simp only [rotAvgPhase, actPhase_smul, Pi.smul_apply]
  exact integral_smul c _

theorem meridAvgPhase_smul (c : ℂ) (φ : ℝ × Space → CVec3) :
    meridAvgPhase (c • φ) = c • meridAvgPhase φ := by
  funext q
  simp only [meridAvgPhase, rotAvgPhase_smul, actPhase_smul, Pi.smul_apply]
  rw [← smul_add]
  exact smul_comm (1 / 2 : ℝ) c (rotAvgPhase φ q + actPhase Axi.reflY (rotAvgPhase φ) q)

theorem isPhaseTest_rotAvgPhase {P : ℝ} (hP : 0 < P) {φ : ℝ × Space → CVec3}
    (hφ : IsPhaseTest P φ) : IsPhaseTest P (rotAvgPhase φ) where
  smooth := (paramIntegralSmooth_proof (ℝ × Space) ℝ Axi.angμ _
    (paramFamilyHyp_rotZ hP hφ)).1
  periodic τ y := by
    simp only [rotAvgPhase]
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    exact (isPhaseTest_actPhase (B0226.rotZ θ) hφ).periodic τ y
  bounded_support := by
    obtain ⟨R, hR⟩ := hφ.bounded_support
    refine ⟨R, fun τ y hy => ?_⟩
    have h0 : ∀ θ : ℝ, actPhase (B0226.rotZ θ) φ (τ, y) = 0 := fun θ => by
      have hy' : R < ‖B0226.rotZ θ y‖ := by rwa [(B0226.rotZ θ).norm_map]
      simp [actPhase, prodCLM_apply, hR τ (B0226.rotZ θ y) hy']
    simp [rotAvgPhase, h0]

theorem isPhaseTest_meridAvgPhase {P : ℝ} (hP : 0 < P) {φ : ℝ × Space → CVec3}
    (hφ : IsPhaseTest P φ) : IsPhaseTest P (meridAvgPhase φ) := by
  have hr := isPhaseTest_rotAvgPhase hP hφ
  exact (hr.add (isPhaseTest_actPhase Axi.reflY hr)).const_smul (1 / 2 : ℝ)

theorem phaseGen_rotAvgPhase (ν ε : ℝ) {P : ℝ} (hP : 0 < P) {φ : ℝ × Space → CVec3}
    (hφ : IsPhaseTest P φ) (q : ℝ × Space) :
    phaseGen ν ε (rotAvgPhase φ) q = rotAvgPhase (phaseGen ν ε φ) q := by
  obtain ⟨h0, hdτ, _hdy, hrad, hlap, edτ, _edy, erad, elap⟩ :=
    opsUnderIntegral_proof ℝ Axi.angμ (fun θ => actPhase (B0226.rotZ θ) φ)
      (paramFamilyHyp_rotZ hP hφ) q
  have hcomb : phaseGen ν ε (rotAvgPhase φ) q =
      ∫ θ, phaseGen ν ε (actPhase (B0226.rotZ θ) φ) q ∂Axi.angμ := by
    unfold phaseGen rotAvgPhase
    rw [elap, erad, edτ]
    have h1 : Integrable (fun x => (ν * ε ^ 2) • lapT (actPhase (B0226.rotZ x) φ) q) Axi.angμ :=
      hlap.smul (ν * ε ^ 2)
    have h2 : Integrable (fun x => (1 / 2 : ℝ) • radialT (actPhase (B0226.rotZ x) φ) q) Axi.angμ :=
      hrad.smul (1 / 2 : ℝ)
    have h3 : Integrable (fun x => (1 / 2 : ℝ) • actPhase (B0226.rotZ x) φ q) Axi.angμ :=
      h0.smul (1 / 2 : ℝ)
    have h12 : Integrable (fun x =>
        (ν * ε ^ 2) • lapT (actPhase (B0226.rotZ x) φ) q +
          (1 / 2 : ℝ) • radialT (actPhase (B0226.rotZ x) φ) q) Axi.angμ :=
      h1.add h2
    have h123 : Integrable (fun x =>
        (ν * ε ^ 2) • lapT (actPhase (B0226.rotZ x) φ) q +
          (1 / 2 : ℝ) • radialT (actPhase (B0226.rotZ x) φ) q +
          (1 / 2 : ℝ) • actPhase (B0226.rotZ x) φ q) Axi.angμ :=
      h12.add h3
    rw [← integral_smul, ← integral_smul, ← integral_smul,
      ← integral_add h1 h2, ← integral_add h12 h3,
      ← integral_sub h123 hdτ]
  rw [hcomb, rotAvgPhase]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  exact phaseGen_actPhase ν ε (B0226.rotZ θ) hφ.smooth q

theorem phaseGen_meridAvgPhase (ν ε : ℝ) {P : ℝ} (hP : 0 < P) {φ : ℝ × Space → CVec3}
    (hφ : IsPhaseTest P φ) (q : ℝ × Space) :
    phaseGen ν ε (meridAvgPhase φ) q = meridAvgPhase (phaseGen ν ε φ) q := by
  have hr := isPhaseTest_rotAvgPhase hP hφ
  have h1 : ContDiff ℝ ∞ (rotAvgPhase φ) := hr.smooth
  have h2 : ContDiff ℝ ∞ (actPhase Axi.reflY (rotAvgPhase φ)) :=
    (isPhaseTest_actPhase Axi.reflY hr).smooth
  have hd1 : Differentiable ℝ (rotAvgPhase φ) := h1.differentiable (by simp)
  have hd2 : Differentiable ℝ (actPhase Axi.reflY (rotAvgPhase φ)) := h2.differentiable (by simp)
  have hdτ : dτ (meridAvgPhase φ) q =
      (1 / 2 : ℝ) • (dτ (rotAvgPhase φ) q + dτ (actPhase Axi.reflY (rotAvgPhase φ)) q) := by
    have hsm : HasFDerivAt (meridAvgPhase φ)
        ((1 / 2 : ℝ) • (fderiv ℝ (rotAvgPhase φ) q +
          fderiv ℝ (actPhase Axi.reflY (rotAvgPhase φ)) q)) q :=
      ((hd1 q).hasFDerivAt.fun_add (hd2 q).hasFDerivAt).const_smul (1 / 2 : ℝ)
    show fderiv ℝ (meridAvgPhase φ) q (1, 0) = _
    rw [hsm.fderiv]
    simp [dτ]
  have hdy : ∀ j : Fin 3, dy j (meridAvgPhase φ) =
      fun p => (1 / 2 : ℝ) • (dy j (rotAvgPhase φ) p +
        dy j (actPhase Axi.reflY (rotAvgPhase φ)) p) := by
    intro j
    funext p
    have hsm : HasFDerivAt (meridAvgPhase φ)
        ((1 / 2 : ℝ) • (fderiv ℝ (rotAvgPhase φ) p +
          fderiv ℝ (actPhase Axi.reflY (rotAvgPhase φ)) p)) p :=
      ((hd1 p).hasFDerivAt.fun_add (hd2 p).hasFDerivAt).const_smul (1 / 2 : ℝ)
    show fderiv ℝ (meridAvgPhase φ) p (0, coordinateVector j) = _
    rw [hsm.fderiv]
    simp [dy]
  have hrad : radialT (meridAvgPhase φ) q =
      (1 / 2 : ℝ) • (radialT (rotAvgPhase φ) q +
        radialT (actPhase Axi.reflY (rotAvgPhase φ)) q) := by
    simp only [radialT, hdy, smul_add, Finset.sum_add_distrib, Finset.smul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _
  have hlap : lapT (meridAvgPhase φ) q =
      (1 / 2 : ℝ) • (lapT (rotAvgPhase φ) q +
        lapT (actPhase Axi.reflY (rotAvgPhase φ)) q) := by
    simp only [lapT, Finset.smul_sum, smul_add, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hdy j]
    have hd1' : DifferentiableAt ℝ (dy j (rotAvgPhase φ)) q :=
      ((h1.fderiv_right (m := 1) (by simp)).clm_apply contDiff_const).differentiable (by simp) q
    have hd2' : DifferentiableAt ℝ (dy j (actPhase Axi.reflY (rotAvgPhase φ))) q :=
      ((h2.fderiv_right (m := 1) (by simp)).clm_apply contDiff_const).differentiable (by simp) q
    have hsm : HasFDerivAt
        (fun p => (1 / 2 : ℝ) • (dy j (rotAvgPhase φ) p +
          dy j (actPhase Axi.reflY (rotAvgPhase φ)) p))
        ((1 / 2 : ℝ) • (fderiv ℝ (dy j (rotAvgPhase φ)) q +
          fderiv ℝ (dy j (actPhase Axi.reflY (rotAvgPhase φ))) q)) q :=
      (hd1'.hasFDerivAt.fun_add hd2'.hasFDerivAt).const_smul (1 / 2 : ℝ)
    show fderiv ℝ _ q (0, coordinateVector j) = _
    rw [hsm.fderiv]
    simp [dy, smul_add]
  have hlin : phaseGen ν ε (meridAvgPhase φ) q =
      (1 / 2 : ℝ) • (phaseGen ν ε (rotAvgPhase φ) q +
        phaseGen ν ε (actPhase Axi.reflY (rotAvgPhase φ)) q) := by
    simp only [phaseGen, meridAvgPhase, hlap, hrad, hdτ]
    module
  rw [hlin, phaseGen_actPhase ν ε Axi.reflY h1 q, phaseGen_rotAvgPhase ν ε hP hφ q]
  have hr_eq : phaseGen ν ε (rotAvgPhase φ) = rotAvgPhase (phaseGen ν ε φ) :=
    funext (phaseGen_rotAvgPhase ν ε hP hφ)
  rw [hr_eq]
  rfl

end UnforcedLeray.Short.PartIIa.MeridProjAux
