import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1_5

/-!
# Calculus helpers for the curl and divergence identities (IIIb-D2 1.3.1.2.1.3.1.5)

Shared by `CurlIsSolTest`, `DivIsPhaseTest` and `CurlCurlId`. Source
`the November 2 reference manuscript`
lines 1351-1362, 1470-1480 (the Leray-density decomposition).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- `v ↦ a × v` as a complex-linear map on `ℂ³`. -/
def crossCLin (a : CVec3) : CVec3 →ₗ[ℂ] CVec3 where
  toFun v := crossC a v
  map_add' v w := by
    ext i
    fin_cases i <;> simp [crossC] <;> ring
  map_smul' c v := by
    ext i
    fin_cases i <;> simp [crossC] <;> ring

/-- `v ↦ a × v` as a real-linear continuous map on `ℂ³`. -/
def crossCL (a : CVec3) : CVec3 →L[ℝ] CVec3 :=
  (LinearMap.toContinuousLinearMap (crossCLin a)).restrictScalars ℝ

theorem crossCL_apply (a v : CVec3) : crossCL a v = crossC a v := by
  simp [crossCL, crossCLin]

/-- The `k`-th coordinate of a `ℂ³` vector, real-linearly. -/
def coordL (k : Fin 3) : CVec3 →L[ℝ] ℂ :=
  (EuclideanSpace.proj k : CVec3 →L[ℂ] ℂ).restrictScalars ℝ

theorem coordL_apply (k : Fin 3) (v : CVec3) : coordL k v = v k := by
  simp [coordL]

/-- Spatial derivatives commute with post-composition by a real-linear map. -/
theorem curlH_dy_clm {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (L : CVec3 →L[ℝ] G)
    (j : Fin 3) (g : ℝ × Space → CVec3) (hg : Differentiable ℝ g) :
    PhaseSpace.dy j (fun x => L (g x)) = fun x => L (PhaseSpace.dy j g x) := by
  funext x
  have hd : HasFDerivAt g (fderiv ℝ g x) x := (hg x).hasFDerivAt
  have hc : HasFDerivAt (fun y => L (g y)) (L.comp (fderiv ℝ g x)) x :=
    L.hasFDerivAt.comp x hd
  simp only [PhaseSpace.dy]
  rw [hc.fderiv]
  rfl

/-- Spatial derivative of a finite sum, for any value type. -/
theorem dy_finsum {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*}
    (s : Finset ι) (G : ι → ℝ × Space → F) (hG : ∀ i ∈ s, Differentiable ℝ (G i)) (j : Fin 3) :
    PhaseSpace.dy j (∑ i ∈ s, G i) = ∑ i ∈ s, PhaseSpace.dy j (G i) := by
  funext p
  simp only [PhaseSpace.dy, Finset.sum_apply]
  rw [fderiv_sum fun i hi => (hG i hi) p]
  simp

theorem contDiff_dy (A : ℝ × Space → CVec3) (hA : ContDiff ℝ ∞ A) (j : Fin 3) :
    ContDiff ℝ ∞ (PhaseSpace.dy j A) := by
  unfold PhaseSpace.dy
  exact (hA.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem differentiable_dy (A : ℝ × Space → CVec3) (hA : ContDiff ℝ ∞ A) (j : Fin 3) :
    Differentiable ℝ (PhaseSpace.dy j A) :=
  (contDiff_dy A hA j).differentiable (by simp)

theorem curlH_curlT_apply (Θ : ℝ × Space → CVec3) (x : ℝ × Space) :
    curlT Θ x = ∑ j : Fin 3, crossC (EuclideanSpace.single j (1 : ℂ)) (PhaseSpace.dy j Θ x) :=
  rfl

/-- The curl as a sum of real-linear post-compositions of the spatial derivatives. -/
theorem curlT_eq_sum (A : ℝ × Space → CVec3) :
    curlT A = ∑ k : Fin 3, fun x => crossCL (EuclideanSpace.single k (1 : ℂ)) (PhaseSpace.dy k A x) := by
  funext x
  simp [curlT, Finset.sum_apply, crossCL_apply]

/-- Spatial derivative of the curl of a smooth field. -/
theorem dy_curlT (A : ℝ × Space → CVec3) (hA : ContDiff ℝ ∞ A) (j : Fin 3) :
    PhaseSpace.dy j (curlT A) = fun x => ∑ k : Fin 3,
      crossC (EuclideanSpace.single k (1 : ℂ)) (PhaseSpace.dy j (PhaseSpace.dy k A) x) := by
  have hdiff : ∀ k ∈ (Finset.univ : Finset (Fin 3)),
      Differentiable ℝ (fun x => crossCL (EuclideanSpace.single k (1 : ℂ)) (PhaseSpace.dy k A x)) :=
    fun k _ => (crossCL _).differentiable.comp (differentiable_dy A hA k)
  have hterm : ∀ k : Fin 3, PhaseSpace.dy j (fun x => crossCL (EuclideanSpace.single k (1 : ℂ))
      (PhaseSpace.dy k A x)) = fun x => crossCL (EuclideanSpace.single k (1 : ℂ))
        (PhaseSpace.dy j (PhaseSpace.dy k A) x) :=
    fun k => curlH_dy_clm _ j _ (differentiable_dy A hA k)
  rw [curlT_eq_sum, PhaseSpace.dy_sum Finset.univ hdiff j]
  simp only [hterm]
  funext x
  simp [Finset.sum_apply, crossCL_apply]

/-- `divT A = ∑ₖ ∂ₖ Aₖ` written with the real-linear coordinate maps. -/
theorem divT_eq_sum (A : ℝ × Space → CVec3) :
    divT A = ∑ k : Fin 3, fun x => coordL k (PhaseSpace.dy k A x) := by
  funext x
  simp [divT, Finset.sum_apply, coordL_apply]

/-- Spatial derivative of the divergence. -/
theorem dy_divT (A : ℝ × Space → CVec3) (hA : ContDiff ℝ ∞ A) (i : Fin 3) :
    PhaseSpace.dy i (divT A) = fun x => ∑ k : Fin 3, (PhaseSpace.dy i (PhaseSpace.dy k A) x) k := by
  have hdiff : ∀ k ∈ (Finset.univ : Finset (Fin 3)),
      Differentiable ℝ (fun x => coordL k (PhaseSpace.dy k A x)) :=
    fun k _ => (coordL k).differentiable.comp (differentiable_dy A hA k)
  have hterm : ∀ k : Fin 3, PhaseSpace.dy i (fun x => coordL k (PhaseSpace.dy k A x)) =
      fun x => coordL k (PhaseSpace.dy i (PhaseSpace.dy k A) x) :=
    fun k => curlH_dy_clm _ i _ (differentiable_dy A hA k)
  rw [divT_eq_sum, dy_finsum Finset.univ _ hdiff i]
  simp only [hterm]
  funext x
  simp [Finset.sum_apply, coordL_apply]

end UnforcedLeray.Short.PartIIIb.Concrete
