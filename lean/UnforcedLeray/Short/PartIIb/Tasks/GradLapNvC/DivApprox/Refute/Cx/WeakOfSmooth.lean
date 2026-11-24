import UnforcedLeray.Short.PartIIb.Sub.T09_2_1.Counter
import UnforcedLeray.Short.PartIIb.Tasks.GradLapNvC.DivSmooth.WeakClassical

/-!
# Part II-b, leaf `PartII-b:T09R/1/2` (`WeakOfSmooth`)

Classical derivatives of smooth profiles are weak derivatives: for smooth `v`, `d`, `b`,
`HasWeakVec v d b (classOp v d b)`.  The scalar integration by parts `ibp_gen`
(`DivSmooth/WeakClassical.lean`) gives the transposed identity against each test `φ` with
`IsCoordTest φ`; integrability holds because `coordTranspose v d φ` is continuous and vanishes
outside `tsupport φ`.  Componentwise `i : Fin 2` with `u = b · i`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

namespace WeakOfSmoothHelp

open DivWeakClassicalHelp

/-- Scalar weak identity for a smooth `u`: `divF v d u` is the weak `v·∇u + d u`. -/
lemma hasWeakFO_of_smooth (v : Coord → Fin 3 → ℝ) (d : Coord → ℝ) (u : Coord → ℂ)
    (hu : ContDiff ℝ ∞ u) (hv : ∀ j, ContDiff ℝ ∞ (fun x => v x j)) (hd : ContDiff ℝ ∞ d) :
    HasWeakFO v d u (divF v d u) := by
  have hvc : ∀ j, Continuous (fun x => (v x j : ℂ)) := fun j =>
    Complex.continuous_ofReal.comp (hv j).continuous
  have hDc : ∀ j, Continuous (fun x => fderiv ℝ u x (cdir j)) := fun j =>
    (hu.continuous_fderiv (by simp)).clm_apply continuous_const
  have hFc : Continuous (divF v d u) := by
    unfold divF
    refine Continuous.add (continuous_finsetSum _ fun j _ => (hvc j).mul (hDc j)) ?_
    exact (Complex.continuous_ofReal.comp hd.continuous).mul hu.continuous
  refine ⟨fun φ hφ => ⟨?_, ?_⟩, fun φ hφ => (ibp_gen v d u hu hv hd φ hφ).symm⟩
  · have hcpd : ∀ j, Continuous
        (fun x => fderiv ℝ (fun y : Coord => v y j * φ y) x (cdir j)) := fun j =>
      ((((hv j).mul hφ.smooth)).continuous_fderiv (by simp)).clm_apply continuous_const
    have hctR : Continuous (fun x => coordTranspose v d φ x) := by
      unfold coordTranspose cpd
      exact (continuous_finsetSum _ fun j _ => hcpd j).neg.add
        (hd.continuous.mul hφ.smooth.continuous)
    have hctc : HasCompactSupport (fun x => coordTranspose v d φ x) := by
      refine HasCompactSupport.intro hφ.compact (fun x hx => ?_)
      have hz : ∀ j : Fin 3, fderiv ℝ (fun y : Coord => v y j * φ y) x (cdir j) = 0 := by
        intro j
        have hx' : x ∉ tsupport (fun y : Coord => v y j * φ y) :=
          fun h => hx (tsupport_mul_subset_right h)
        have hnot : x ∉ Function.support (fderiv ℝ (fun y : Coord => v y j * φ y)) :=
          fun h => hx' (support_fderiv_subset ℝ h)
        have h0 : fderiv ℝ (fun y : Coord => v y j * φ y) x = 0 :=
          Function.notMem_support.1 hnot
        simp [h0]
      have hφ0 : φ x = 0 := by
        by_contra hne
        exact hx (subset_tsupport φ (Function.mem_support.2 hne))
      simp [coordTranspose, cpd, hz, hφ0]
    have hctc_c : HasCompactSupport (fun x => (coordTranspose v d φ x : ℂ)) :=
      hctc.comp_left Complex.ofReal_zero
    have hφc_c : HasCompactSupport (fun x => (φ x : ℂ)) :=
      hφ.compact.comp_left Complex.ofReal_zero
    have hint1 : Integrable (fun x => u x * (coordTranspose v d φ x : ℂ)) :=
      (hu.continuous.mul (Complex.continuous_ofReal.comp hctR)).integrable_of_hasCompactSupport
        hctc_c.mul_left
    exact hint1
  · have hint2 : Integrable (fun x => divF v d u x * (φ x : ℂ)) :=
      (hFc.mul (Complex.continuous_ofReal.comp hφ.smooth.continuous)
        ).integrable_of_hasCompactSupport (hφ.compact.comp_left Complex.ofReal_zero).mul_left
    exact hint2

end WeakOfSmoothHelp

end UnforcedLeray.Short.IIb

open UnforcedLeray.Short.IIb WeakOfSmoothHelp DivWeakClassicalHelp in
theorem weakOfSmooth_proof : UnforcedLeray.Short.IIb.DivCounter.WeakOfSmooth := by
  intro v d b hv hd hb
  have hsmooth : ContDiff ℝ ∞ b := hb
  have hcomp_smooth : ∀ i : Fin 2, ContDiff ℝ ∞ (fun y => b y i) := by
    intro i
    exact ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp hsmooth
  have hfd : ∀ (i : Fin 2) (x : Coord) (w : Coord),
      fderiv ℝ (fun y => b y i) x w = fderiv ℝ b x w i := by
    intro i x w
    have hbd : DifferentiableAt ℝ b x := hsmooth.differentiable (by simp) x
    have hL := ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).restrictScalars ℝ).hasFDerivAt.comp
      x hbd.hasFDerivAt
    have hL' : fderiv ℝ (fun y => b y i) x =
        ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).restrictScalars ℝ).comp (fderiv ℝ b x) :=
      hL.fderiv
    rw [hL']
    simp
  intro i
  have key := hasWeakFO_of_smooth v d (fun y => b y i) (hcomp_smooth i) hv hd
  have hcl : (fun x => classOp v d b x i) = DivWeakClassicalHelp.divF v d (fun y => b y i) := by
    funext x
    simp [classOp, divF, hfd, Finset.sum_apply, Complex.real_smul]
  rw [hcl]
  exact key
