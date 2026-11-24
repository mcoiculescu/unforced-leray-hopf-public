import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_10
import UnforcedLeray.Lib.PhaseSpace.Leibniz

/-!
# `weakSolOfCurl`: a weak curl is weakly solenoidal

Source `the November 2 reference manuscript` lines 1334-1337, 1351-1362, 1470-1480.
For a scalar phase test `φ`, `∇φ` is a vector phase test and `curl ∇φ = 0`: the second
`y`-derivatives of `φ` are symmetric, and the antisymmetry of the cross product kills the sum.
Hence `⟨∇φ, v⟩ = ⟨curl ∇φ, u⟩ = 0` whenever `curl u = v` weakly.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- Smoothness of a `y`-derivative of a smooth scalar function. -/
theorem wcs_contDiff_dy {Φ : ℝ × Space → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (j : Fin 3) :
    ContDiff ℝ ∞ (dy j Φ) :=
  (hΦ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- Symmetry of second derivatives of a smooth scalar function (`dy_dy_comm` for `ℂ`-valued). -/
theorem wcs_dy_dy_comm {Φ : ℝ × Space → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (j k : Fin 3) :
    dy j (dy k Φ) = dy k (dy j Φ) := by
  funext p
  have hd : Differentiable ℝ (fderiv ℝ Φ) :=
    (hΦ.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have hf : ∀ w v : ℝ × Space,
      fderiv ℝ (fun q => fderiv ℝ Φ q w) p v = fderiv ℝ (fderiv ℝ Φ) p v w := by
    intro w v
    have hx : HasFDerivAt (fun y => fderiv ℝ Φ y w) ((fderiv ℝ (fderiv ℝ Φ) p).flip w) p := by
      simpa using (hd p).hasFDerivAt.clm_apply (hasFDerivAt_const w p)
    rw [hx.fderiv]
    rfl
  show fderiv ℝ (fun q => fderiv ℝ Φ q (0, coordinateVector k)) p (0, coordinateVector j) =
    fderiv ℝ (fun q => fderiv ℝ Φ q (0, coordinateVector j)) p (0, coordinateVector k)
  rw [hf, hf]
  exact (hΦ.contDiffAt.isSymmSndFDerivAt (by simp)).eq _ _

/-- The `ℂ`-linear-in-scalar map `z ↦ z • v` as a continuous `ℝ`-linear map. -/
def wcsL (v : CVec3) : ℂ →L[ℝ] CVec3 :=
  { toFun := fun z => z • v
    map_add' := fun z w => by simp [add_smul]
    map_smul' := fun r z => by
      show (r • z) • v = r • (z • v)
      exact smul_assoc r z v
    cont := continuous_id.smul continuous_const }

/-- Chain rule for a `ℝ`-linear map applied to a scalar function, in the `y`-derivative. -/
theorem wcs_dy_clm (L : ℂ →L[ℝ] CVec3) {F : ℝ × Space → ℂ} (hF : Differentiable ℝ F)
    (j : Fin 3) : dy j (fun p => L (F p)) = fun p => L (dy j F p) := by
  funext p
  have h := ((L.hasFDerivAt).comp p (hF p).hasFDerivAt).fderiv
  simp only [dy]
  rw [show (fun q => L (F q)) = L ∘ F from rfl, h]
  rfl

/-- Cross product is antisymmetric. -/
theorem wcs_crossC_anti (a b : CVec3) : crossC a b = -crossC b a := by
  ext i
  fin_cases i <;> simp [crossC] <;> ring

/-- Cross product is additive in its second argument. -/
theorem wcs_crossC_add_right (a b c : CVec3) : crossC a (b + c) = crossC a b + crossC a c := by
  ext i
  fin_cases i <;> simp [crossC] <;> ring

/-- Cross product is `ℂ`-linear in its second argument. -/
theorem wcs_crossC_smul_right (a : CVec3) (c : ℂ) (b : CVec3) :
    crossC a (c • b) = c • crossC a b := by
  ext i
  fin_cases i <;> simp [crossC] <;> ring

/-- Cross product distributes over finite sums in its second argument. -/
theorem wcs_crossC_sum_right {ι : Type*} (a : CVec3) (s : Finset ι) (f : ι → CVec3) :
    crossC a (∑ i ∈ s, f i) = ∑ i ∈ s, crossC a (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [crossC]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, wcs_crossC_add_right, ih]

/-- A symmetric coefficient against an antisymmetric family sums to zero. -/
theorem wcs_sym_antisym_sum (a : Fin 3 → Fin 3 → ℂ) (C : Fin 3 → Fin 3 → CVec3)
    (ha : ∀ j k, a j k = a k j) (hC : ∀ j k, C j k = -C k j) :
    ∑ j, ∑ k, a j k • C j k = 0 := by
  set S := ∑ j, ∑ k, a j k • C j k with hS
  have h1 : S = ∑ j, ∑ k, a k j • C k j := Finset.sum_comm
  have h2 : ∑ j, ∑ k, a k j • C k j = -S := by
    rw [hS, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ha k j, hC k j, smul_neg]
  have h3 : S + S = 0 := by
    calc S + S = S + ∑ j, ∑ k, a k j • C k j := by rw [← h1]
      _ = S + -S := by rw [h2]
      _ = 0 := add_neg_cancel S
  have h4 : (2 : ℂ) • S = 0 := by
    rw [two_smul]
    exact h3
  exact (smul_eq_zero.1 h4).resolve_left two_ne_zero

/-- `curl ∇φ = 0` pointwise for a smooth scalar phase test `φ`. -/
theorem wcs_curl_gradT {P : ℝ} {φ : ℝ × Space → ℂ} (hφ : IsPhaseTest P φ) (x : ℝ × Space) :
    curlT (gradT φ) x = 0 := by
  have hs : ContDiff ℝ ∞ φ := hφ.smooth
  have hd : ∀ k : Fin 3, Differentiable ℝ (dy k φ) := fun k =>
    (wcs_contDiff_dy hs k).differentiable (by simp)
  have hgrad : gradT φ = ∑ k : Fin 3, (fun p => dy k φ p • EuclideanSpace.single k (1 : ℂ)) := by
    funext p
    simp [gradT, Finset.sum_apply]
  have hdy : ∀ j : Fin 3, dy j (gradT φ) =
      ∑ k : Fin 3, (fun p => dy j (dy k φ) p • EuclideanSpace.single k (1 : ℂ)) := by
    intro j
    rw [hgrad, dy_sum (G := fun k p => dy k φ p • EuclideanSpace.single k (1 : ℂ))
      Finset.univ (fun k _ => (wcsL _).differentiable.comp (hd k)) j]
    exact Finset.sum_congr rfl fun k _ => wcs_dy_clm (wcsL (EuclideanSpace.single k (1 : ℂ))) (hd k) j
  have hcurl : curlT (gradT φ) x = ∑ j : Fin 3, ∑ k : Fin 3,
      dy j (dy k φ) x • crossC (EuclideanSpace.single j (1 : ℂ))
        (EuclideanSpace.single k (1 : ℂ)) := by
    simp only [curlT, hdy, Finset.sum_apply, wcs_crossC_sum_right, wcs_crossC_smul_right]
  rw [hcurl]
  refine wcs_sym_antisym_sum (fun j k => dy j (dy k φ) x)
    (fun j k => crossC (EuclideanSpace.single j (1 : ℂ)) (EuclideanSpace.single k (1 : ℂ)))
    (fun j k => ?_) (fun j k => wcs_crossC_anti _ _)
  exact congrFun (wcs_dy_dy_comm hs j k) x

/-- **WeakSolOfCurl** (source 1334-1337, 1351-1362, 1470-1480): a weak curl is weakly
solenoidal. -/
theorem weakSolOfCurl : WeakSolOfCurl := by
  intro P u v huv
  unfold IsWeakSolenoidal
  intro φ hφ
  have hg : IsPhaseTest P (gradT φ) := IsPhaseTest.gradT hφ
  have hrel := huv (gradT φ) hg
  have hc0 : curlT (gradT φ) = fun _ => (0 : CVec3) := funext fun x => wcs_curl_gradT hφ x
  rw [hc0] at hrel
  have h0 : pairF P (fun _ => (0 : CVec3)) u = 0 := by
    unfold pairF phaseInt
    simp
  rw [h0] at hrel
  exact hrel.symm

end UnforcedLeray.Short.PartIIIb.Concrete
