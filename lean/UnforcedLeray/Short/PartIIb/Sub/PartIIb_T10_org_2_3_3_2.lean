import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_2_3_3_of

/-!
# `PartII-b:T10/org/2/3/3/2`: the identity `f + ∇(N ∗ div f) = curl (N ∗ curl f)`

For a smooth compactly supported real field `f`, with `ψ = N ∗ div f` and `(curl f)ᵢ = ∂ᵢ₊₁ fᵢ₊₂ - ∂ᵢ₊₂ fᵢ₊₁`,
the pointwise identity `curl curl f = ∇ div f - Δ f` and `N ∗ Δ g = -g` give
`fᵢ + ∂ᵢψ = (curl (N ∗ curl f))ᵢ` (`NewtonCurlIdentity`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.RieszLp

/-- Linearity of the coordinate derivative under subtraction of smooth functions. -/
private theorem sdt_sub_aux2 {a b : Space → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (j : Fin 3) (x : Space) :
    spatialTestDerivative j (fun y => a y - b y) x =
      spatialTestDerivative j a x - spatialTestDerivative j b x := by
  unfold spatialTestDerivative
  rw [fderiv_fun_sub ((ha.differentiable (by simp)).differentiableAt)
    ((hb.differentiable (by simp)).differentiableAt)]
  simp

/-- Symmetry of coordinate derivatives of a smooth compactly supported test. -/
private theorem sdt_comm_aux2 {φ : Space → ℝ} (hφ : IsSpatialTest φ) (i j : Fin 3) :
    spatialTestDerivative i (spatialTestDerivative j φ) =
      spatialTestDerivative j (spatialTestDerivative i φ) := by
  have hform : ∀ a b : Fin 3, ∀ x : Space, spatialTestDerivative a (spatialTestDerivative b φ) x =
      fderiv ℝ (fderiv ℝ φ) x (coordinateVector a) (coordinateVector b) := by
    intro a b x
    have hd : Differentiable ℝ (fderiv ℝ φ) :=
      (ContDiff.fderiv_right (m := ∞) hφ.smooth (by simp)).differentiable (by simp)
    have hx : HasFDerivAt (fun y => fderiv ℝ φ y (coordinateVector b))
        ((fderiv ℝ (fderiv ℝ φ) x).flip (coordinateVector b)) x := by
      simpa using (hd x).hasFDerivAt.clm_apply (hasFDerivAt_const (coordinateVector b) x)
    unfold spatialTestDerivative
    rw [hx.fderiv]
    rfl
  funext x
  rw [hform i j x, hform j i x]
  exact (hφ.smooth.contDiffAt.isSymmSndFDerivAt (by simp)).eq
    (coordinateVector i) (coordinateVector j)

/-- Differences of tests are tests. -/
private theorem isSpatialTest_sub_aux2 {g h : Space → ℝ} (hg : IsSpatialTest g)
    (hh : IsSpatialTest h) : IsSpatialTest (fun y => g y - h y) :=
  ⟨hg.smooth.sub hh.smooth, hg.compact.sub hh.compact⟩

/-- Finite sums of tests are tests. -/
private theorem isSpatialTest_sum_aux2 {ι : Type*} (s : Finset ι) {a : ι → Space → ℝ}
    (ha : ∀ j, IsSpatialTest (a j)) : IsSpatialTest (fun y => ∑ j ∈ s, a j y) := by
  constructor
  · exact ContDiff.sum (fun j _ => (ha j).smooth)
  · have he : (fun y => ∑ j ∈ s, a j y) = ∑ j ∈ s, a j := by
      funext y
      simp [Finset.sum_apply]
    rw [he]
    exact HasCompactSupport.finset_sum (fun j _ => (ha j).compact)

/-- The Newton potential is linear on tests (difference form). -/
private theorem newtonConv_sub_aux2 {g h : Space → ℝ} (hg : IsSpatialTest g)
    (hh : IsSpatialTest h) (x : Space) :
    newtonConv (fun y => g y - h y) x = newtonConv g x - newtonConv h x := by
  simp only [newtonConv, mul_sub]
  exact integral_sub (newtonConv_integrable hg.continuous hg.compact x)
    (newtonConv_integrable hh.continuous hh.compact x)

/-- Pointwise rotation of a sum over `Fin 3`. -/
private theorem sum_fin3_rot2 (G : Fin 3 → ℝ) (j : Fin 3) :
    ∑ k, G k = G j + G (j + 1) + G (j + 2) := by
  fin_cases j <;> simp [Fin.sum_univ_three] <;> ring

theorem newtonCurlIdentity_proof : UnforcedLeray.Short.IIb.NewtonCurlIdentity := by
  intro f hf i x
  have hs1 : ∀ a k, ContDiff ℝ ∞ (spatialTestDerivative a (f k)) := fun a k =>
    UnforcedLeray.PressureAnalysis.contDiff_spatialTestDerivative (hf k).smooth a
  have hC : ∀ k : Fin 3, IsSpatialTest (curlComp f k) := fun k =>
    isSpatialTest_sub_aux2 ((hf (k + 2)).derivative (k + 1)) ((hf (k + 1)).derivative (k + 2))
  have hD : IsSpatialTest (divTest f) := isSpatialTest_divTest hf
  have hLap : IsSpatialTest (Heat.laplacian (f i)) :=
    isSpatialTest_sum_aux2 (s := Finset.univ)
      (a := fun k => spatialTestDerivative k (spatialTestDerivative k (f i)))
      (fun k => ((hf i).derivative k).derivative k)
  have hA : IsSpatialTest (spatialTestDerivative i (divTest f)) := hD.derivative i
  have hT1 : IsSpatialTest (spatialTestDerivative (i + 1) (curlComp f (i + 2))) :=
    (hC (i + 2)).derivative (i + 1)
  have hT2 : IsSpatialTest (spatialTestDerivative (i + 2) (curlComp f (i + 1))) :=
    (hC (i + 1)).derivative (i + 2)
  have h1 : ∀ j : Fin 3, j + 2 + 1 = j := by decide
  have h2 : ∀ j : Fin 3, j + 2 + 2 = j + 1 := by decide
  have h3 : ∀ j : Fin 3, j + 1 + 2 = j := by decide
  have h4 : ∀ j : Fin 3, j + 1 + 1 = j + 2 := by decide
  have hC2 : curlComp f (i + 2) =
      fun y => spatialTestDerivative i (f (i + 1)) y - spatialTestDerivative (i + 1) (f i) y := by
    funext y
    show spatialTestDerivative (i + 2 + 1) (f (i + 2 + 2)) y
        - spatialTestDerivative (i + 2 + 2) (f (i + 2 + 1)) y = _
    rw [h1 i, h2 i]
  have hC1 : curlComp f (i + 1) =
      fun y => spatialTestDerivative (i + 2) (f i) y - spatialTestDerivative i (f (i + 2)) y := by
    funext y
    show spatialTestDerivative (i + 1 + 1) (f (i + 1 + 2)) y
        - spatialTestDerivative (i + 1 + 2) (f (i + 1 + 1)) y = _
    rw [h4 i, h3 i]
  have hpt : ∀ y, spatialTestDerivative (i + 1) (curlComp f (i + 2)) y
      - spatialTestDerivative (i + 2) (curlComp f (i + 1)) y
      = spatialTestDerivative i (divTest f) y - Heat.laplacian (f i) y := by
    intro y
    have c1 := congrFun (sdt_comm_aux2 (hf (i + 1)) (i + 1) i) y
    have c2 := congrFun (sdt_comm_aux2 (hf (i + 2)) (i + 2) i) y
    rw [hC2, hC1, sdt_sub_aux2 (hs1 i (i + 1)) (hs1 (i + 1) i),
      sdt_sub_aux2 (hs1 (i + 2) i) (hs1 i (i + 2))]
    have hdiv : divTest f = fun z => ∑ k ∈ Finset.univ, spatialTestDerivative k (f k) z := rfl
    have hA' : spatialTestDerivative i (divTest f) y =
        spatialTestDerivative i (spatialTestDerivative i (f i)) y
        + spatialTestDerivative i (spatialTestDerivative (i + 1) (f (i + 1))) y
        + spatialTestDerivative i (spatialTestDerivative (i + 2) (f (i + 2))) y := by
      rw [hdiv, spatialTestDerivative_sum' Finset.univ (fun k => hs1 k k) i y]
      exact sum_fin3_rot2 (fun k => spatialTestDerivative i (spatialTestDerivative k (f k)) y) i
    have hB' : Heat.laplacian (f i) y =
        spatialTestDerivative i (spatialTestDerivative i (f i)) y
        + spatialTestDerivative (i + 1) (spatialTestDerivative (i + 1) (f i)) y
        + spatialTestDerivative (i + 2) (spatialTestDerivative (i + 2) (f i)) y :=
      sum_fin3_rot2 (fun k => spatialTestDerivative k (spatialTestDerivative k (f i)) y) i
    linarith [c1, c2, hA', hB']
  rw [lerayPotential, spatialTestDerivative_newtonConv hD i]
  show f i x + newtonConv (spatialTestDerivative i (divTest f)) x =
    spatialTestDerivative (i + 1) (newtonConv (curlComp f (i + 2))) x
      - spatialTestDerivative (i + 2) (newtonConv (curlComp f (i + 1))) x
  rw [spatialTestDerivative_newtonConv (hC (i + 2)) (i + 1),
    spatialTestDerivative_newtonConv (hC (i + 1)) (i + 2)]
  rw [← newtonConv_sub_aux2 hT1 hT2 x]
  have hfun : (fun y => spatialTestDerivative (i + 1) (curlComp f (i + 2)) y
      - spatialTestDerivative (i + 2) (curlComp f (i + 1)) y)
      = fun y => spatialTestDerivative i (divTest f) y - Heat.laplacian (f i) y := funext hpt
  rw [hfun, newtonConv_sub_aux2 hA hLap x, newtonConv_laplacian_test (hf i) x]
  ring

end UnforcedLeray.Short.IIb
