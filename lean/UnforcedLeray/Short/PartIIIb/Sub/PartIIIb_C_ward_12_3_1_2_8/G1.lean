import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8
import UnforcedLeray.Cons.L2.BackgroundConcrete.GraphStateSolenoidal
import UnforcedLeray.Lib.PhaseSpace.Leibniz

/-!
# `D_j w` is solenoidal (source 2525-2537)

Task `PartIII-b:C/ward/12/3/1/2/8/1`.  Source of record
`the November 2 reference manuscript`.

For a scalar phase test `φ`, `⟪∇φ, g_j⟫ = -⟪∇(∂_jφ), w⟫ = 0`: the first equality is the weak
derivative `HasPhaseOp (-∂_j) w g_j` tested at `∇φ` together with `∂_j∇φ = ∇∂_jφ`, and the
last is `w ∈ Y_σ` tested at the scalar phase test `∂_jφ`.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (Params)

/-- Symmetry of mixed second derivatives of a smooth scalar test. -/
private theorem g1_dy_dy_comm {φ : ℝ × UnforcedLeray.Space → ℂ} (hΦ : ContDiff ℝ ∞ φ)
    (j k : Fin 3) : dy j (dy k φ) = dy k (dy j φ) := by
  funext p
  have hd : ∀ v w : ℝ × UnforcedLeray.Space,
      fderiv ℝ (fun q => fderiv ℝ φ q w) p v = fderiv ℝ (fderiv ℝ φ) p v w := by
    intro v w
    have hdf : Differentiable ℝ (fderiv ℝ φ) :=
      (hΦ.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
    have hx : HasFDerivAt (fun y => fderiv ℝ φ y w) ((fderiv ℝ (fderiv ℝ φ) p).flip w) p := by
      simpa using (hdf p).hasFDerivAt.clm_apply (hasFDerivAt_const w p)
    rw [hx.fderiv]
    rfl
  have hsym : ∀ v w : ℝ × UnforcedLeray.Space,
      fderiv ℝ (fderiv ℝ φ) p v w = fderiv ℝ (fderiv ℝ φ) p w v :=
    fun v w => (hΦ.contDiffAt.isSymmSndFDerivAt (by simp)).eq v w
  show fderiv ℝ (fun q => fderiv ℝ φ q (0, coordinateVector k)) p (0, coordinateVector j) =
    fderiv ℝ (fun q => fderiv ℝ φ q (0, coordinateVector j)) p (0, coordinateVector k)
  rw [hd, hd]
  exact hsym _ _

/-- `∂_j(f • v) = (∂_j f) • v` for a fixed vector `v`. -/
private theorem g1_dy_smul_const (j : Fin 3) {c : ℝ × UnforcedLeray.Space → ℂ}
    (hc : Differentiable ℝ c) (v : CVec3) :
    dy j (fun q => c q • v) = fun q => dy j c q • v := by
  funext q
  simp [dy, fderiv_smul_const (hc q)]

/-- `∂_j ∇φ = ∇(∂_jφ)` for a smooth scalar test. -/
theorem g1_dy_gradT {φ : ℝ × UnforcedLeray.Space → ℂ} (hΦ : ContDiff ℝ ∞ φ) (j : Fin 3) :
    dy j (gradT φ) = gradT (dy j φ) := by
  have hdk : ∀ k : Fin 3, Differentiable ℝ (dy k φ) := fun k =>
    ((hΦ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).differentiable (by simp)
  have hsplit : gradT φ = ∑ k : Fin 3,
      (fun q => dy k φ q • EuclideanSpace.single k (1 : ℂ)) := by
    funext q
    simp [gradT, Finset.sum_apply]
  have hsplit' : gradT (dy j φ) = ∑ k : Fin 3,
      (fun q => dy k (dy j φ) q • EuclideanSpace.single k (1 : ℂ)) := by
    funext q
    simp [gradT, Finset.sum_apply]
  rw [hsplit, dy_sum Finset.univ (fun k _ => (hdk k).smul_const _) j, hsplit']
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [g1_dy_smul_const j (hdk k), g1_dy_dy_comm hΦ j k]

/-- **`D_j w` is solenoidal** (source 2525-2537). -/
theorem gEGradSol_proof : GEGradSol := by
  intro p z g hd j
  rw [UnforcedLeray.B0411.mem_Ysigma]
  intro φ hφ
  have hwσ : IsPhaseSolenoidal (p.wOf z) := by
    have hwX : p.wOf z ∈ UnforcedLeray.B0412.X p.period p.ν
        UnforcedLeray.B0412.q0E := (p.graphX z).property
    rcases UnforcedLeray.B0412.mem_X.mp hwX with ⟨hdiv, _, _, _⟩
    simpa [Params.graphX] using hdiv
  have h1 : phasePair p.period UnforcedLeray.B0412.q0E (-dy j (gradT φ)) (p.wOf z) =
      phasePair p.period UnforcedLeray.B0412.q0E (gradT φ) (g j) :=
    hd.2 j (gradT φ) hφ.gradT
  have h2 : -dy j (gradT φ) = -gradT (dy j φ) := by
    rw [g1_dy_gradT hφ.smooth j]
  have h3 : phasePair p.period UnforcedLeray.B0412.q0E (gradT (dy j φ)) (p.wOf z) = 0 :=
    hwσ (dy j φ) (hφ.dy j)
  rw [h2, phasePair_neg (hφ.dy j).gradT, h3, neg_zero] at h1
  exact h1.symm

end UnforcedLeray.Short.PartIIIb.Concrete
