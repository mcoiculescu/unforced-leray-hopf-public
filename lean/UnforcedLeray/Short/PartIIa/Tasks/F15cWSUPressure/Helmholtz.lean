import UnforcedLeray.Short.PartIIa.Tasks.F15cWSUPressure.NewtonSchwartz
import UnforcedLeray.Units.B0005.Bridge.Commute

/-!
# Helmholtz decomposition and cutoff convergence for phase tests

Helper for `PartII-a:F15/3` (`Tasks/F15cWSUPressure.lean`).
Proves `wsuPressureApprox : WSUPressureApprox`: every phase test `Φ` is approximated in the
`L0T ν` graph norm on `Y_{2'}` by `Ψ_n + gradT ψ_n` with `Ψ_n` a divergence-free phase test
and `ψ_n` a scalar phase test.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa.F15c

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp
open UnforcedLeray.Short.IIb

/-! ### Calculus helpers for scalar complex functions -/

theorem dy_clm_gen {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] (L : E₁ →L[ℝ] E₂)
    {Φ : ℝ × Space → E₁} (hΦ : Differentiable ℝ Φ) (j : Fin 3) :
    dy j (fun p => L (Φ p)) = fun p => L (dy j Φ p) := by
  funext p
  have h := (L.hasFDerivAt.comp p (hΦ p).hasFDerivAt).fderiv
  show fderiv ℝ (L ∘ Φ) p (0, coordinateVector j) = L (fderiv ℝ Φ p (0, coordinateVector j))
  rw [h]
  rfl

theorem contDiff_dy_c {φ : ℝ × Space → ℂ} (hφ : ContDiff ℝ ∞ φ) (j : Fin 3) :
    ContDiff ℝ ∞ (dy j φ) :=
  (hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem fderiv_apply_formula_c {φ : ℝ × Space → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (v w p : ℝ × Space) :
    fderiv ℝ (fun p => fderiv ℝ φ p w) p v = fderiv ℝ (fderiv ℝ φ) p v w := by
  have hd : Differentiable ℝ (fderiv ℝ φ) :=
    (hφ.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have hx : HasFDerivAt (fun y => fderiv ℝ φ y w) ((fderiv ℝ (fderiv ℝ φ) p).flip w) p := by
    simpa using (hd p).hasFDerivAt.clm_apply (hasFDerivAt_const w p)
  rw [hx.fderiv]
  rfl

theorem dy_dy_comm_c {φ : ℝ × Space → ℂ} (hφ : ContDiff ℝ ∞ φ) (j k : Fin 3) :
    dy j (dy k φ) = dy k (dy j φ) := by
  funext p
  show fderiv ℝ (fun q => fderiv ℝ φ q (0, coordinateVector k)) p (0, coordinateVector j) =
    fderiv ℝ (fun q => fderiv ℝ φ q (0, coordinateVector j)) p (0, coordinateVector k)
  rw [fderiv_apply_formula_c hφ, fderiv_apply_formula_c hφ]
  exact (hφ.contDiffAt.isSymmSndFDerivAt (by simp)).eq _ _

theorem dy_add_c {φ ψ : ℝ × Space → ℂ} (hφ : Differentiable ℝ φ) (hψ : Differentiable ℝ ψ)
    (j : Fin 3) : dy j (φ + ψ) = dy j φ + dy j ψ := by
  funext p
  simp [dy, fderiv_add (hφ p) (hψ p)]

theorem dy_sub_c {φ ψ : ℝ × Space → ℂ} (hφ : Differentiable ℝ φ) (hψ : Differentiable ℝ ψ)
    (j : Fin 3) : dy j (φ - ψ) = dy j φ - dy j ψ := by
  funext p
  simp [dy, fderiv_sub (hφ p) (hψ p)]

theorem dy_neg_c (φ : ℝ × Space → ℂ) (j : Fin 3) : dy j (-φ) = -dy j φ := by
  funext p
  simp [dy, fderiv_neg]

theorem dy_sum_c {ι : Type*} (s : Finset ι) {φ : ι → ℝ × Space → ℂ}
    (hφ : ∀ k ∈ s, Differentiable ℝ (φ k)) (j : Fin 3) :
    dy j (∑ k ∈ s, φ k) = ∑ k ∈ s, dy j (φ k) := by
  funext p
  simp only [dy, Finset.sum_apply]
  rw [fderiv_sum fun k hk => (hφ k hk) p]
  simp

/-! ### Complex joint Newton potential `newtonJointC` -/

def rePart (φ : ℝ × Space → ℂ) : ℝ × Space → ℝ := fun p => Complex.reCLM (φ p)
def imPart (φ : ℝ × Space → ℂ) : ℝ × Space → ℝ := fun p => Complex.imCLM (φ p)

theorem isPhaseTest_rePart {P : ℝ} {φ : ℝ × Space → ℂ} (hφ : IsPhaseTest P φ) :
    IsPhaseTest P (rePart φ) :=
  hφ.clm_comp Complex.reCLM

theorem isPhaseTest_imPart {P : ℝ} {φ : ℝ × Space → ℂ} (hφ : IsPhaseTest P φ) :
    IsPhaseTest P (imPart φ) :=
  hφ.clm_comp Complex.imCLM

def ofImCLM : ℝ →L[ℝ] ℂ :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight Complex.I

@[simp] theorem ofImCLM_apply (x : ℝ) : ofImCLM x = (x : ℂ) * Complex.I := by
  simp [ofImCLM, Complex.real_smul]

def newtonJointC (φ : ℝ × Space → ℂ) : ℝ × Space → ℂ :=
  fun p => Complex.ofRealCLM (LTS.newtonJoint (rePart φ) p) +
    ofImCLM (LTS.newtonJoint (imPart φ) p)

theorem contDiff_newtonJointC {P : ℝ} {φ : ℝ × Space → ℂ} (hφ : IsPhaseTest P φ) :
    ContDiff ℝ ∞ (newtonJointC φ) :=
  (Complex.ofRealCLM.contDiff.comp (LTS.contDiff_newtonJoint (isPhaseTest_rePart hφ))).add
    (ofImCLM.contDiff.comp (LTS.contDiff_newtonJoint (isPhaseTest_imPart hφ)))

theorem newtonJointC_periodic {P : ℝ} {φ : ℝ × Space → ℂ} (hφ : IsPhaseTest P φ) :
    ∀ τ y, newtonJointC φ (τ + P, y) = newtonJointC φ (τ, y) := by
  intro τ y
  simp [newtonJointC, LTS.newtonJoint_periodic (isPhaseTest_rePart hφ) τ y,
    LTS.newtonJoint_periodic (isPhaseTest_imPart hφ) τ y]

theorem dy_newtonJointC {P : ℝ} {φ : ℝ × Space → ℂ} (hφ : IsPhaseTest P φ) (k : Fin 3) :
    dy k (newtonJointC φ) =
      fun p => Complex.ofRealCLM (dy k (LTS.newtonJoint (rePart φ)) p) +
        ofImCLM (dy k (LTS.newtonJoint (imPart φ)) p) := by
  funext p
  have hR : DifferentiableAt ℝ (LTS.newtonJoint (rePart φ)) p :=
    (LTS.contDiff_newtonJoint (isPhaseTest_rePart hφ)).differentiable (by simp) p
  have hI : DifferentiableAt ℝ (LTS.newtonJoint (imPart φ)) p :=
    (LTS.contDiff_newtonJoint (isPhaseTest_imPart hφ)).differentiable (by simp) p
  have h := ((Complex.ofRealCLM.hasFDerivAt.comp p hR.hasFDerivAt).add
    (ofImCLM.hasFDerivAt.comp p hI.hasFDerivAt)).fderiv
  exact congrArg (fun A : ℝ × Space →L[ℝ] ℂ => A (0, coordinateVector k)) h

theorem lapT_newtonJointC {P : ℝ} {φ : ℝ × Space → ℂ} (hφ : IsPhaseTest P φ) :
    lapT (newtonJointC φ) = -φ := by
  have hR : ContDiff ℝ ∞ (LTS.newtonJoint (rePart φ)) :=
    LTS.contDiff_newtonJoint (isPhaseTest_rePart hφ)
  have hI : ContDiff ℝ ∞ (LTS.newtonJoint (imPart φ)) :=
    LTS.contDiff_newtonJoint (isPhaseTest_imPart hφ)
  have h2 : ∀ j : Fin 3, dy j (dy j (newtonJointC φ)) =
      fun p => Complex.ofRealCLM (dy j (dy j (LTS.newtonJoint (rePart φ))) p) +
        ofImCLM (dy j (dy j (LTS.newtonJoint (imPart φ))) p) := by
    intro j
    rw [dy_newtonJointC hφ j]
    funext p
    have hdR : DifferentiableAt ℝ (dy j (LTS.newtonJoint (rePart φ))) p :=
      (LTS.contDiff_dy_real hR j).differentiable (by simp) p
    have hdI : DifferentiableAt ℝ (dy j (LTS.newtonJoint (imPart φ))) p :=
      (LTS.contDiff_dy_real hI j).differentiable (by simp) p
    have h := ((Complex.ofRealCLM.hasFDerivAt.comp p hdR.hasFDerivAt).add
      (ofImCLM.hasFDerivAt.comp p hdI.hasFDerivAt)).fderiv
    exact congrArg (fun A : ℝ × Space →L[ℝ] ℂ => A (0, coordinateVector j)) h
  funext p
  show ∑ j : Fin 3, dy j (dy j (newtonJointC φ)) p = -φ p
  simp only [h2, Finset.sum_add_distrib, ← map_sum]
  change Complex.ofRealCLM (lapT (LTS.newtonJoint (rePart φ)) p) +
    ofImCLM (lapT (LTS.newtonJoint (imPart φ)) p) = -φ p
  rw [lapT_newtonJoint (isPhaseTest_rePart hφ), lapT_newtonJoint (isPhaseTest_imPart hφ)]
  simp only [Pi.neg_apply, Complex.ofRealCLM_apply, ofImCLM_apply, rePart, imPart,
    Complex.reCLM_apply, Complex.imCLM_apply]
  apply Complex.ext <;> simp

/-! ### Good scalar potentials (`IsGoodScalar`) -/

/-- A complex scalar potential whose coordinate embeddings and their spatial derivatives are
Schwartz-type `L²` phase tests. -/
structure IsGoodScalar (P : ℝ) [Fact (0 < P)] (α : ℝ × Space → ℂ) : Prop where
  smooth : ContDiff ℝ ∞ α
  periodic : ∀ τ y, α (τ + P, y) = α (τ, y)
  schwartz : ∀ i : Fin 3, IsPhaseSchwartz P (conjExp 2) (fun p => B0005.embedJ i (α p))
  schwartz_dy : ∀ i j : Fin 3,
    IsPhaseSchwartz P (conjExp 2) (dy j (fun p => B0005.embedJ i (α p)))

namespace IsGoodScalar

variable {P : ℝ} [Fact (0 < P)]

theorem zero : IsGoodScalar P 0 where
  smooth := contDiff_const
  periodic _ _ := rfl
  schwartz i := by
    have h : (fun p : ℝ × Space => B0005.embedJ i ((0 : ℝ × Space → ℂ) p)) = 0 := by
      funext p; simp
    rw [h]; exact isPhaseSchwartz_zero
  schwartz_dy i j := by
    have h : dy j (fun p : ℝ × Space => B0005.embedJ i ((0 : ℝ × Space → ℂ) p)) = 0 := by
      funext p; simp [dy]
    rw [h]; exact isPhaseSchwartz_zero

theorem add {α β : ℝ × Space → ℂ} (hα : IsGoodScalar P α) (hβ : IsGoodScalar P β) :
    IsGoodScalar P (α + β) where
  smooth := hα.smooth.add hβ.smooth
  periodic τ y := by simp [hα.periodic τ y, hβ.periodic τ y]
  schwartz i := by
    have h : (fun p => B0005.embedJ i ((α + β) p)) =
        (fun p => B0005.embedJ i (α p)) + (fun p => B0005.embedJ i (β p)) := by
      funext p; simp
    rw [h]; exact isPhaseSchwartz_add (hα.schwartz i) (hβ.schwartz i)
  schwartz_dy i j := by
    have h : (fun p => B0005.embedJ i ((α + β) p)) =
        (fun p => B0005.embedJ i (α p)) + (fun p => B0005.embedJ i (β p)) := by
      funext p; simp
    rw [h, dy_add ((hα.schwartz i).smooth.differentiable (by simp))
      ((hβ.schwartz i).smooth.differentiable (by simp)) j]
    exact isPhaseSchwartz_add (hα.schwartz_dy i j) (hβ.schwartz_dy i j)

theorem neg {α : ℝ × Space → ℂ} (hα : IsGoodScalar P α) : IsGoodScalar P (-α) where
  smooth := hα.smooth.neg
  periodic τ y := by simp [hα.periodic τ y]
  schwartz i := by
    have h : (fun p => B0005.embedJ i ((-α) p)) = -(fun p => B0005.embedJ i (α p)) := by
      funext p; simp
    rw [h]; exact isPhaseSchwartz_neg (hα.schwartz i)
  schwartz_dy i j := by
    have h : (fun p => B0005.embedJ i ((-α) p)) = -(fun p => B0005.embedJ i (α p)) := by
      funext p; simp
    rw [h, dy_neg]
    exact isPhaseSchwartz_neg (hα.schwartz_dy i j)

theorem sub {α β : ℝ × Space → ℂ} (hα : IsGoodScalar P α) (hβ : IsGoodScalar P β) :
    IsGoodScalar P (α - β) := by
  rw [sub_eq_add_neg]
  exact hα.add hβ.neg

theorem sum {ι : Type*} (s : Finset ι) {α : ι → ℝ × Space → ℂ}
    (h : ∀ k ∈ s, IsGoodScalar P (α k)) : IsGoodScalar P (∑ k ∈ s, α k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : IsGoodScalar P 0)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

end IsGoodScalar

theorem isGoodScalar_dy_newtonJointC {P : ℝ} [Fact (0 < P)] {φ : ℝ × Space → ℂ}
    (hφ : IsPhaseTest P φ) (k : Fin 3) :
    IsGoodScalar P (dy k (newtonJointC φ)) := by
  have hR := isPhaseTest_rePart hφ
  have hI := isPhaseTest_imPart hφ
  have hdecomp : ∀ i : Fin 3, (fun p => B0005.embedJ i (dy k (newtonJointC φ) p)) =
      (fun p => (dy k (LTS.newtonJoint (rePart φ)) p) • EuclideanSpace.single i (1 : ℂ)) +
      (fun p => (dy k (LTS.newtonJoint (imPart φ)) p) •
        ((Complex.I : ℂ) • EuclideanSpace.single i (1 : ℂ))) := by
    intro i
    funext p
    rw [dy_newtonJointC hφ k]
    ext m
    simp only [B0005.embedJ, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.id_apply, WithLp.ofLp_add, Pi.add_apply,
      WithLp.ofLp_smul, Pi.smul_apply, PiLp.single_apply,
      Complex.real_smul, smul_eq_mul, Complex.ofRealCLM_apply, ofImCLM]
    split_ifs <;> ring
  refine ⟨contDiff_dy_c (contDiff_newtonJointC hφ) k,
    periodic_dy (newtonJointC_periodic hφ) k, fun i => ?_, fun i j => ?_⟩
  · rw [hdecomp i]
    exact isPhaseSchwartz_add (isPhaseSchwartz_dy_newtonJoint hR k _)
      (isPhaseSchwartz_dy_newtonJoint hI k _)
  · have hd1 : Differentiable ℝ
        (fun p => (dy k (LTS.newtonJoint (rePart φ)) p) • EuclideanSpace.single i (1 : ℂ)) :=
      (isPhaseSchwartz_dy_newtonJoint hR k _).smooth.differentiable (by simp)
    have hd2 : Differentiable ℝ
        (fun p => (dy k (LTS.newtonJoint (imPart φ)) p) •
          ((Complex.I : ℂ) • EuclideanSpace.single i (1 : ℂ))) :=
      (isPhaseSchwartz_dy_newtonJoint hI k _).smooth.differentiable (by simp)
    rw [hdecomp i, dy_add hd1 hd2 j]
    exact isPhaseSchwartz_add (isPhaseSchwartz_dy_dy_newtonJoint hR k j _)
      (isPhaseSchwartz_dy_dy_newtonJoint hI k j _)

/-! ### Scalar cutoff `cutS` and vector curl `curlScalar` -/

/-- Spatial cutoff of a complex scalar function: `cutS n α (τ, y) = cutχ n y • α (τ, y)`. -/
def cutS (n : ℕ) (α : ℝ × Space → ℂ) : ℝ × Space → ℂ :=
  fun p => cutχ n p.2 • α p

theorem embedJ_cutS (i : Fin 3) (n : ℕ) (α : ℝ × Space → ℂ) :
    (fun p => B0005.embedJ i (cutS n α p)) =
      mulT (cutχ n) (fun p => B0005.embedJ i (α p)) := by
  funext p
  ext m
  simp [cutS, mulT, B0005.embedJ, Complex.real_smul]

theorem isPhaseTest_cutS {P : ℝ} [Fact (0 < P)] {α : ℝ × Space → ℂ} (hα : IsGoodScalar P α)
    (n : ℕ) : IsPhaseTest P (cutS n α) := by
  have h := ((hα.schwartz 0).isPhaseTest_cut n).clm_comp (B0005.projC 0)
  have heq : (fun p => B0005.projC 0 (mulT (cutχ n) (fun q => B0005.embedJ 0 (α q)) p)) =
      cutS n α := by
    funext p
    rw [← congrFun (embedJ_cutS 0 n α) p, B0005.projC_embedJ]
  rwa [heq] at h

/-- Curl of a 3-tuple of complex scalar functions:
`(curlScalar a)_i = ∂_{i+1} a_{i+2} - ∂_{i+2} a_{i+1}`. -/
def curlScalar (a : Fin 3 → ℝ × Space → ℂ) : ℝ × Space → CVec3 :=
  ∑ i : Fin 3, (dy (i + 1) (fun p => B0005.embedJ i (a (i + 2) p)) -
    dy (i + 2) (fun p => B0005.embedJ i (a (i + 1) p)))

theorem gradT_eq_sum_dy_embedJ {φ : ℝ × Space → ℂ} (hφ : Differentiable ℝ φ) :
    gradT φ = ∑ i : Fin 3, dy i (fun p => B0005.embedJ i (φ p)) := by
  funext p
  simp only [gradT, Finset.sum_apply, dy_clm_gen (B0005.embedJ _) hφ]
  rfl

theorem isPhaseTest_curlScalar {P : ℝ} {a : Fin 3 → ℝ × Space → ℂ}
    (ha : ∀ m, IsPhaseTest P (a m)) : IsPhaseTest P (curlScalar a) :=
  IsPhaseTest.sum _ fun i _ =>
    (((ha (i + 2)).clm_comp (B0005.embedJ i)).dy (i + 1)).sub
      (((ha (i + 1)).clm_comp (B0005.embedJ i)).dy (i + 2))

theorem curlScalar_apply {a : Fin 3 → ℝ × Space → ℂ} (ha : ∀ m, Differentiable ℝ (a m))
    (p : ℝ × Space) (i : Fin 3) :
    curlScalar a p i = dy (i + 1) (a (i + 2)) p - dy (i + 2) (a (i + 1)) p := by
  have h1 : ∀ k : Fin 3,
      (dy (k + 1) (fun q => B0005.embedJ k (a (k + 2) q)) p -
        dy (k + 2) (fun q => B0005.embedJ k (a (k + 1) q)) p) =
      B0005.embedJ k (dy (k + 1) (a (k + 2)) p - dy (k + 2) (a (k + 1)) p) := by
    intro k
    rw [dy_clm_gen (B0005.embedJ k) (ha (k + 2)) (k + 1),
      dy_clm_gen (B0005.embedJ k) (ha (k + 1)) (k + 2), map_sub]
  have hsum : curlScalar a p =
      ∑ k : Fin 3, B0005.embedJ k (dy (k + 1) (a (k + 2)) p - dy (k + 2) (a (k + 1)) p) := by
    simp only [curlScalar, Finset.sum_apply, Pi.sub_apply, h1]
  rw [hsum, WithLp.ofLp_sum, Finset.sum_apply]
  simp only [B0005.embedJ, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, WithLp.ofLp_smul, Pi.smul_apply,
    PiLp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

theorem div_curlScalar_eq_zero {a : Fin 3 → ℝ × Space → ℂ} (ha : ∀ m, ContDiff ℝ ∞ (a m))
    (p : ℝ × Space) :
    ∑ i : Fin 3, dy i (curlScalar a) p i = 0 := by
  have had : ∀ m, Differentiable ℝ (a m) := fun m => (ha m).differentiable (by simp)
  have hcs : ContDiff ℝ ∞ (curlScalar a) := by
    have hfun : curlScalar a = fun q => ∑ i : Fin 3,
        (dy (i + 1) (fun p => B0005.embedJ i (a (i + 2) p)) q -
          dy (i + 2) (fun p => B0005.embedJ i (a (i + 1) p)) q) := by
      funext q
      simp [curlScalar]
    rw [hfun]
    exact ContDiff.sum fun i _ =>
      (PhaseSpace.contDiff_dy ((B0005.embedJ i).contDiff.comp (ha (i + 2))) (i + 1)).sub
        (PhaseSpace.contDiff_dy ((B0005.embedJ i).contDiff.comp (ha (i + 1))) (i + 2))
  have hcd : Differentiable ℝ (curlScalar a) := hcs.differentiable (by simp)
  have hcoord : ∀ i : Fin 3, dy i (curlScalar a) p i =
      dy i (dy (i + 1) (a (i + 2))) p - dy i (dy (i + 2) (a (i + 1))) p := by
    intro i
    have hproj := congrFun (dy_clm_gen (B0005.projC i) hcd i) p
    simp only [B0005.projC_apply] at hproj
    rw [← hproj]
    have hfun : (fun q => curlScalar a q i) = dy (i + 1) (a (i + 2)) - dy (i + 2) (a (i + 1)) :=
      funext fun q => curlScalar_apply had q i
    rw [hfun, dy_sub_c ((contDiff_dy_c (ha (i + 2)) (i + 1)).differentiable (by simp))
      ((contDiff_dy_c (ha (i + 1)) (i + 2)).differentiable (by simp)) i]
    rfl
  simp only [hcoord, Fin.sum_univ_three]
  have h10 : ∀ m, dy 1 (dy 0 (a m)) p = dy 0 (dy 1 (a m)) p :=
    fun m => congrFun (dy_dy_comm_c (ha m) 1 0) p
  have h20 : ∀ m, dy 2 (dy 0 (a m)) p = dy 0 (dy 2 (a m)) p :=
    fun m => congrFun (dy_dy_comm_c (ha m) 2 0) p
  have h21 : ∀ m, dy 2 (dy 1 (a m)) p = dy 1 (dy 2 (a m)) p :=
    fun m => congrFun (dy_dy_comm_c (ha m) 2 1) p
  change (dy 0 (dy 1 (a 2)) p - dy 0 (dy 2 (a 1)) p) +
    (dy 1 (dy 2 (a 0)) p - dy 1 (dy 0 (a 2)) p) +
    (dy 2 (dy 0 (a 1)) p - dy 2 (dy 1 (a 0)) p) = 0
  rw [h10, h20, h21]
  ring

/-! ### Vector calculus identity `curl (curl B) - grad (div B) = - lap B` -/

theorem curlScalar_curl_add_gradT_neg_div {B : Fin 3 → ℝ × Space → ℂ}
    (hB : ∀ m, ContDiff ℝ ∞ (B m)) :
    curlScalar (fun i => dy (i + 1) (B (i + 2)) - dy (i + 2) (B (i + 1))) +
      gradT (-∑ k : Fin 3, dy k (B k)) =
      fun p => WithLp.toLp 2 fun i => -lapT (B i) p := by
  let A_c : Fin 3 → ℝ × Space → ℂ := fun i => dy (i + 1) (B (i + 2)) - dy (i + 2) (B (i + 1))
  let N : ℝ × Space → ℂ := -∑ k : Fin 3, dy k (B k)
  have hBs : ∀ m k, ContDiff ℝ ∞ (dy k (B m)) := fun m k => contDiff_dy_c (hB m) k
  have hBd : ∀ m k, Differentiable ℝ (dy k (B m)) := fun m k => (hBs m k).differentiable (by simp)
  have hAd : ∀ i, Differentiable ℝ (A_c i) := fun i =>
    (hBd (i + 2) (i + 1)).sub (hBd (i + 1) (i + 2))
  funext p
  ext i
  rw [Pi.add_apply, WithLp.ofLp_add, Pi.add_apply, WithLp.ofLp_toLp,
    curlScalar_apply hAd p i]
  have hgrad : gradT N p i = dy i N p := B0005.projC_gradT N p i
  rw [hgrad]
  have hdyA : ∀ j k : Fin 3, dy j (A_c k) p =
      dy j (dy (k + 1) (B (k + 2))) p - dy j (dy (k + 2) (B (k + 1))) p := fun j k =>
    congrFun (dy_sub_c (hBd (k + 2) (k + 1)) (hBd (k + 1) (k + 2)) j) p
  have hdyN : dy i N p = -∑ k : Fin 3, dy i (dy k (B k)) p := by
    change dy i (-∑ k : Fin 3, dy k (B k)) p = _
    rw [dy_neg_c, Pi.neg_apply, dy_sum_c _ (fun k _ => hBd k k) i, Finset.sum_apply]
  rw [hdyA (i + 1) (i + 2), hdyA (i + 2) (i + 1), hdyN]
  have h10 : ∀ m, dy 1 (dy 0 (B m)) p = dy 0 (dy 1 (B m)) p :=
    fun m => congrFun (dy_dy_comm_c (hB m) 1 0) p
  have h20 : ∀ m, dy 2 (dy 0 (B m)) p = dy 0 (dy 2 (B m)) p :=
    fun m => congrFun (dy_dy_comm_c (hB m) 2 0) p
  have h21 : ∀ m, dy 2 (dy 1 (B m)) p = dy 1 (dy 2 (B m)) p :=
    fun m => congrFun (dy_dy_comm_c (hB m) 2 1) p
  show _ = -∑ j : Fin 3, dy j (dy j (B i)) p
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  rcases hi with rfl | rfl | rfl <;>
  · simp only [Fin.sum_univ_three, show (0 : Fin 3) + 1 = 1 from rfl,
      show (0 : Fin 3) + 2 = 2 from rfl, show (1 : Fin 3) + 1 = 2 from rfl,
      show (1 : Fin 3) + 2 = 0 from rfl, show (2 : Fin 3) + 1 = 0 from rfl,
      show (2 : Fin 3) + 2 = 1 from rfl, h10, h20, h21]
    ring

/-! ### Graph convergence of `curlScalar (cutS n A) + gradT (cutS n N)` -/

section ApproxSum

variable {P : ℝ} [Fact (0 < P)] {r : ℝ≥0∞} [Fact (1 ≤ r)]

theorem testElem_sub_schwartz {A B : ℝ × Space → CVec3} (hA : IsPhaseSchwartz P r A)
    (hB : IsPhaseSchwartz P r B) :
    testElem P r (A - B) = testElem P r A - testElem P r B := by
  rw [sub_eq_add_neg, testElem_add hA.sliceTest hB.sliceTest.neg, testElem_neg hB.sliceTest,
    ← sub_eq_add_neg]

theorem testElem_sum_schwartz {ι : Type*} (s : Finset ι) {F : ι → ℝ × Space → CVec3}
    (h : ∀ i ∈ s, IsPhaseSchwartz P r (F i)) :
    testElem P r (∑ i ∈ s, F i) = ∑ i ∈ s, testElem P r (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [testElem_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      testElem_add (h a (Finset.mem_insert_self a s)).sliceTest
        (isPhaseSchwartz_sum s fun i hi => h i (Finset.mem_insert_of_mem hi)).sliceTest,
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

theorem L0T_zero (ν : ℝ) : L0T ν (0 : ℝ × Space → CVec3) = 0 := by
  have h := L0T_const_smul ν (A := (0 : ℝ × Space → CVec3)) contDiff_const (0 : ℂ)
  simpa using h

theorem L0T_sum_schwartz (ν : ℝ) {ι : Type*} (s : Finset ι) {F : ι → ℝ × Space → CVec3}
    (h : ∀ i ∈ s, IsPhaseSchwartz P r (F i)) :
    L0T ν (∑ i ∈ s, F i) = ∑ i ∈ s, L0T ν (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [L0T_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      L0T_add_smooth ν (h a (Finset.mem_insert_self a s)).smooth
        (isPhaseSchwartz_sum s fun i hi => h i (Finset.mem_insert_of_mem hi)).smooth,
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

theorem testElem_L0T_add_schwartz (ν : ℝ) {A B : ℝ × Space → CVec3} (hA : IsPhaseSchwartz P r A)
    (hB : IsPhaseSchwartz P r B) :
    testElem P r (L0T ν (A + B)) = testElem P r (L0T ν A) + testElem P r (L0T ν B) := by
  rw [L0T_add_smooth ν hA.smooth hB.smooth, testElem_add (sliceTest_L0T ν hA) (sliceTest_L0T ν hB)]

theorem testElem_L0T_sub_schwartz (ν : ℝ) {A B : ℝ × Space → CVec3} (hA : IsPhaseSchwartz P r A)
    (hB : IsPhaseSchwartz P r B) :
    testElem P r (L0T ν (A - B)) = testElem P r (L0T ν A) - testElem P r (L0T ν B) := by
  rw [L0T_sub_smooth ν hA.smooth hB.smooth, sub_eq_add_neg,
    testElem_add (sliceTest_L0T ν hA) (sliceTest_L0T ν hB).neg,
    testElem_neg (sliceTest_L0T ν hB), ← sub_eq_add_neg]

theorem testElem_L0T_sum_schwartz (ν : ℝ) {ι : Type*} (s : Finset ι) {F : ι → ℝ × Space → CVec3}
    (h : ∀ i ∈ s, IsPhaseSchwartz P r (F i)) :
    testElem P r (L0T ν (∑ i ∈ s, F i)) = ∑ i ∈ s, testElem P r (L0T ν (F i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [L0T_zero, testElem_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      testElem_L0T_add_schwartz ν (h a (Finset.mem_insert_self a s))
        (isPhaseSchwartz_sum s fun i hi => h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

end ApproxSum

theorem tendsto_curlScalar_add_gradT_cutS {P : ℝ} [Fact (0 < P)] (ν : ℝ)
    {A_c : Fin 3 → ℝ × Space → ℂ} {N : ℝ × Space → ℂ}
    (hA : ∀ m, IsGoodScalar P (A_c m)) (hN : IsGoodScalar P N) :
    Tendsto (fun n => testElem P (conjExp 2)
        (curlScalar (fun m => cutS n (A_c m)) + gradT (cutS n N))) atTop
      (𝓝 (testElem P (conjExp 2) (curlScalar A_c + gradT N))) ∧
    Tendsto (fun n => testElem P (conjExp 2)
        (L0T ν (curlScalar (fun m => cutS n (A_c m)) + gradT (cutS n N)))) atTop
      (𝓝 (testElem P (conjExp 2) (L0T ν (curlScalar A_c + gradT N)))) := by
  have hr : conjExp 2 ≠ ⊤ := LTS.conjExp_two_ne_top
  -- Rewrite `gradT` via `gradT_eq_sum_dy_embedJ` and `embedJ_cutS`
  have hgrad_cut : ∀ n, gradT (cutS n N) =
      ∑ i : Fin 3, dy i (mulT (cutχ n) (fun p => B0005.embedJ i (N p))) := fun n => by
    rw [gradT_eq_sum_dy_embedJ ((isPhaseTest_cutS hN n).smooth.differentiable (by simp))]
    simp only [embedJ_cutS]
  have hgrad_uncut : gradT N = ∑ i : Fin 3, dy i (fun p => B0005.embedJ i (N p)) :=
    gradT_eq_sum_dy_embedJ (hN.smooth.differentiable (by simp))
  have hcurl_cut : ∀ n, curlScalar (fun m => cutS n (A_c m)) =
      ∑ i : Fin 3, (dy (i + 1) (mulT (cutχ n) (fun p => B0005.embedJ i (A_c (i + 2) p))) -
        dy (i + 2) (mulT (cutχ n) (fun p => B0005.embedJ i (A_c (i + 1) p)))) := fun n => by
    simp only [curlScalar, embedJ_cutS]
  -- Schwartz properties of each uncut and cut piece
  have hS_A_cut : ∀ n (i j m : Fin 3), IsPhaseSchwartz P (conjExp 2)
      (dy j (mulT (cutχ n) (fun p => B0005.embedJ i (A_c m p)))) := fun n i j m =>
    (((hA m).schwartz i).isPhaseTest_cut n |>.dy j).isPhaseSchwartz _
  have hS_N_cut : ∀ n (i : Fin 3), IsPhaseSchwartz P (conjExp 2)
      (dy i (mulT (cutχ n) (fun p => B0005.embedJ i (N p)))) := fun n i =>
    ((hN.schwartz i).isPhaseTest_cut n |>.dy i).isPhaseSchwartz _
  have hS_curl_cut : ∀ n, IsPhaseSchwartz P (conjExp 2)
      (curlScalar (fun m => cutS n (A_c m))) := fun n => by
    rw [hcurl_cut n]
    exact isPhaseSchwartz_sum _ fun i _ =>
      isPhaseSchwartz_sub (hS_A_cut n i (i + 1) (i + 2)) (hS_A_cut n i (i + 2) (i + 1))
  have hS_grad_cut : ∀ n, IsPhaseSchwartz P (conjExp 2) (gradT (cutS n N)) := fun n => by
    rw [hgrad_cut n]
    exact isPhaseSchwartz_sum _ fun i _ => hS_N_cut n i
  have hS_curl : IsPhaseSchwartz P (conjExp 2) (curlScalar A_c) :=
    isPhaseSchwartz_sum _ fun i _ =>
      isPhaseSchwartz_sub ((hA (i + 2)).schwartz_dy i (i + 1))
        ((hA (i + 1)).schwartz_dy i (i + 2))
  have hS_grad : IsPhaseSchwartz P (conjExp 2) (gradT N) := by
    rw [hgrad_uncut]
    exact isPhaseSchwartz_sum _ fun i _ => hN.schwartz_dy i i
  -- Term-by-term convergence
  have h_elem : ∀ n, testElem P (conjExp 2)
      (curlScalar (fun m => cutS n (A_c m)) + gradT (cutS n N)) =
      (∑ i : Fin 3, (testElem P (conjExp 2)
          (dy (i + 1) (mulT (cutχ n) (fun p => B0005.embedJ i (A_c (i + 2) p)))) -
        testElem P (conjExp 2)
          (dy (i + 2) (mulT (cutχ n) (fun p => B0005.embedJ i (A_c (i + 1) p)))))) +
      ∑ i : Fin 3, testElem P (conjExp 2)
        (dy i (mulT (cutχ n) (fun p => B0005.embedJ i (N p)))) := fun n => by
    rw [testElem_add (hS_curl_cut n).sliceTest (hS_grad_cut n).sliceTest,
      hcurl_cut n, hgrad_cut n,
      testElem_sum_schwartz _ fun i _ =>
        isPhaseSchwartz_sub (hS_A_cut n i (i + 1) (i + 2)) (hS_A_cut n i (i + 2) (i + 1)),
      testElem_sum_schwartz _ fun i _ => hS_N_cut n i]
    congr 1
    exact Finset.sum_congr rfl fun i _ =>
      testElem_sub_schwartz (hS_A_cut n i (i + 1) (i + 2)) (hS_A_cut n i (i + 2) (i + 1))
  have h_elem_uncut : testElem P (conjExp 2) (curlScalar A_c + gradT N) =
      (∑ i : Fin 3, (testElem P (conjExp 2)
          (dy (i + 1) (fun p => B0005.embedJ i (A_c (i + 2) p))) -
        testElem P (conjExp 2)
          (dy (i + 2) (fun p => B0005.embedJ i (A_c (i + 1) p))))) +
      ∑ i : Fin 3, testElem P (conjExp 2)
        (dy i (fun p => B0005.embedJ i (N p))) := by
    rw [testElem_add hS_curl.sliceTest hS_grad.sliceTest]
    unfold curlScalar
    rw [hgrad_uncut,
      testElem_sum_schwartz _ fun i _ =>
        isPhaseSchwartz_sub ((hA (i + 2)).schwartz_dy i (i + 1))
          ((hA (i + 1)).schwartz_dy i (i + 2)),
      testElem_sum_schwartz _ fun i _ => hN.schwartz_dy i i]
    congr 1
    exact Finset.sum_congr rfl fun i _ =>
      testElem_sub_schwartz ((hA (i + 2)).schwartz_dy i (i + 1))
        ((hA (i + 1)).schwartz_dy i (i + 2))
  have h_L0T : ∀ n, testElem P (conjExp 2)
      (L0T ν (curlScalar (fun m => cutS n (A_c m)) + gradT (cutS n N))) =
      (∑ i : Fin 3, (testElem P (conjExp 2)
          (L0T ν (dy (i + 1) (mulT (cutχ n) (fun p => B0005.embedJ i (A_c (i + 2) p))))) -
        testElem P (conjExp 2)
          (L0T ν (dy (i + 2) (mulT (cutχ n) (fun p => B0005.embedJ i (A_c (i + 1) p))))))) +
      ∑ i : Fin 3, testElem P (conjExp 2)
        (L0T ν (dy i (mulT (cutχ n) (fun p => B0005.embedJ i (N p))))) := fun n => by
    rw [testElem_L0T_add_schwartz ν (hS_curl_cut n) (hS_grad_cut n),
      hcurl_cut n, hgrad_cut n,
      testElem_L0T_sum_schwartz ν _ fun i _ =>
        isPhaseSchwartz_sub (hS_A_cut n i (i + 1) (i + 2)) (hS_A_cut n i (i + 2) (i + 1)),
      testElem_L0T_sum_schwartz ν _ fun i _ => hS_N_cut n i]
    congr 1
    exact Finset.sum_congr rfl fun i _ =>
      testElem_L0T_sub_schwartz ν (hS_A_cut n i (i + 1) (i + 2)) (hS_A_cut n i (i + 2) (i + 1))
  have h_L0T_uncut : testElem P (conjExp 2) (L0T ν (curlScalar A_c + gradT N)) =
      (∑ i : Fin 3, (testElem P (conjExp 2)
          (L0T ν (dy (i + 1) (fun p => B0005.embedJ i (A_c (i + 2) p)))) -
        testElem P (conjExp 2)
          (L0T ν (dy (i + 2) (fun p => B0005.embedJ i (A_c (i + 1) p)))))) +
      ∑ i : Fin 3, testElem P (conjExp 2)
        (L0T ν (dy i (fun p => B0005.embedJ i (N p)))) := by
    rw [testElem_L0T_add_schwartz ν hS_curl hS_grad]
    unfold curlScalar
    rw [hgrad_uncut,
      testElem_L0T_sum_schwartz ν _ fun i _ =>
        isPhaseSchwartz_sub ((hA (i + 2)).schwartz_dy i (i + 1))
          ((hA (i + 1)).schwartz_dy i (i + 2)),
      testElem_L0T_sum_schwartz ν _ fun i _ => hN.schwartz_dy i i]
    congr 1
    exact Finset.sum_congr rfl fun i _ =>
      testElem_L0T_sub_schwartz ν ((hA (i + 2)).schwartz_dy i (i + 1))
        ((hA (i + 1)).schwartz_dy i (i + 2))
  simp only [h_elem, h_elem_uncut, h_L0T, h_L0T_uncut]
  refine ⟨?_, ?_⟩
  · exact (tendsto_finsetSum _ fun i _ =>
      (tendsto_dy_cut hr ((hA (i + 2)).schwartz i) (i + 1)).sub
        (tendsto_dy_cut hr ((hA (i + 1)).schwartz i) (i + 2))).add
      (tendsto_finsetSum _ fun i _ => tendsto_dy_cut hr (hN.schwartz i) i)
  · exact (tendsto_finsetSum _ fun i _ =>
      (tendsto_L0T_dy_cut hr ν ((hA (i + 2)).schwartz i) ((hA (i + 2)).schwartz_dy i) (i + 1)).sub
        (tendsto_L0T_dy_cut hr ν ((hA (i + 1)).schwartz i) ((hA (i + 1)).schwartz_dy i) (i + 2))).add
      (tendsto_finsetSum _ fun i _ =>
        tendsto_L0T_dy_cut hr ν (hN.schwartz i) (hN.schwartz_dy i) i)

end UnforcedLeray.Short.PartIIa.F15c
