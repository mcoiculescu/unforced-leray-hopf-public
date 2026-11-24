import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1_2

/-!
# `splitIdentity`: the slice Laplacian identity survives the real/imaginary splitting

Source `the November 2 reference manuscript` lines 1351-1362.
`L²`-membership and real-valuedness of `reC`, `imC` are immediate.  For the identity, test the
hypothesis with the coordinatewise conjugate `θ̄` of `θ` (`lapS` commutes with conjugation, since
conjugation is a real-linear continuous map on `ℂ³`), conjugate the resulting identity, and
recombine with `reC f = (f + f̄)/2`, `imC f = (f - f̄)/(2i)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Real part of the `i`-th coordinate, as a real-linear map on `ℂ³`. -/
def h1scProjR (i : Fin 3) : CVec3 →L[ℝ] ℂ :=
  (EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).restrictScalars ℝ

lemma h1scMemLpProj (g : Space → CVec3) (hg : MemLp g 2 volume) (i : Fin 3) :
    MemLp (fun y => g y i) 2 volume :=
  (EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).comp_memLp' hg

lemma h1scDCont (θ : Space → CVec3) (hθ : ContDiff ℝ ∞ θ) (i j : Fin 3) :
    Continuous fun y => fderiv ℝ (fun z => θ z i) y (EuclideanSpace.single j (1 : ℝ)) := by
  have hd : Differentiable ℝ θ := hθ.differentiable (by simp)
  have e : ∀ y, fderiv ℝ (fun z => θ z i) y = (h1scProjR i).comp (fderiv ℝ θ y) := fun y => by
    have h : HasFDerivAt (fun z => θ z i) ((h1scProjR i).comp (fderiv ℝ θ y)) y :=
      (h1scProjR i).hasFDerivAt.comp y (hd y).hasFDerivAt
    exact h.fderiv
  have : (fun y => fderiv ℝ (fun z => θ z i) y (EuclideanSpace.single j (1 : ℝ)))
      = fun y => h1scProjR i (fderiv ℝ θ y (EuclideanSpace.single j (1 : ℝ))) := by
    funext y
    rw [e y]
    rfl
  rw [this]
  exact (h1scProjR i).continuous.comp
    ((hθ.continuous_fderiv (by simp)).clm_apply continuous_const)

lemma h1scDComp (θ : Space → CVec3) (hc : HasCompactSupport θ) (i j : Fin 3) :
    HasCompactSupport fun y => fderiv ℝ (fun z => θ z i) y (EuclideanSpace.single j (1 : ℝ)) := by
  have h0 : HasCompactSupport (fun z => θ z i) :=
    hc.comp_left (g := fun z : CVec3 => z i) (by simp)
  exact h0.fderiv_apply ℝ (EuclideanSpace.single j (1 : ℝ))

lemma h1scCompI (θ : Space → CVec3) (hc : HasCompactSupport θ) (i : Fin 3) :
    HasCompactSupport fun y => θ y i :=
  hc.comp_left (g := fun z : CVec3 => z i) (by simp)

lemma h1scContI (θ : Space → CVec3) (hθ : ContDiff ℝ ∞ θ) (i : Fin 3) :
    Continuous fun y => θ y i :=
  (EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).continuous.comp hθ.continuous

/-- Integrability of `y ↦ ∑ᵢ g y i * ψ i y` for `g ∈ L²` and compactly supported continuous `ψ i`. -/
lemma h1scInt (g : Space → CVec3) (hg : MemLp g 2 volume) (ψ : Fin 3 → Space → ℂ)
    (hψ : ∀ i, Continuous (ψ i)) (hψc : ∀ i, HasCompactSupport (ψ i)) :
    Integrable (fun y => ∑ i : Fin 3, g y i * ψ i y) volume := by
  refine integrable_finsetSum _ fun i _ => ?_
  exact MemLp.integrable_mul (p := 2) (q := 2) (h1scMemLpProj g hg i)
    ((hψ i).memLp_of_hasCompactSupport (hψc i))

lemma h1scMemLpRe (f : Space → CVec3) (hf : MemLp f 2 volume) : MemLp (reC f) 2 volume := by
  refine MemLp.of_le hf ?_ ?_
  · have hΦ : Continuous fun z : CVec3 => (WithLp.toLp 2 fun i => (((z i).re : ℝ) : ℂ) : CVec3) := by
      fun_prop
    exact hΦ.comp_aestronglyMeasurable hf.aestronglyMeasurable
  · refine ae_of_all _ fun y => ?_
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro i _
    have h1 : ‖reC f y i‖ = |(f y i).re| := by simp [reC]
    rw [h1]
    gcongr
    exact Complex.abs_re_le_norm _

lemma h1scMemLpIm (f : Space → CVec3) (hf : MemLp f 2 volume) : MemLp (imC f) 2 volume := by
  refine MemLp.of_le hf ?_ ?_
  · have hΦ : Continuous fun z : CVec3 => (WithLp.toLp 2 fun i => (((z i).im : ℝ) : ℂ) : CVec3) := by
      fun_prop
    exact hΦ.comp_aestronglyMeasurable hf.aestronglyMeasurable
  · refine ae_of_all _ fun y => ?_
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro i _
    have h1 : ‖imC f y i‖ = |(f y i).im| := by simp [imC]
    rw [h1]
    gcongr
    exact Complex.abs_im_le_norm _

/-- Coordinatewise complex conjugation on `ℂ³`, as a real-linear continuous map. -/
def h1scConj : CVec3 →L[ℝ] CVec3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => WithLp.toLp 2 (fun i => (starRingEnd ℂ) (w i))
      map_add' := by
        intro a b
        ext i
        simp
      map_smul' := by
        intro r a
        ext i
        simp [Complex.real_smul] }

lemma h1scConj_apply (w : CVec3) (i : Fin 3) : h1scConj w i = (starRingEnd ℂ) (w i) := by
  simp [h1scConj]

lemma h1scConj_contDiff (θ : Space → CVec3) (hθ : ContDiff ℝ ∞ θ) :
    ContDiff ℝ ∞ (fun z => h1scConj (θ z)) :=
  h1scConj.contDiff.comp hθ

lemma h1scConj_hasCompactSupport (θ : Space → CVec3) (hc : HasCompactSupport θ) :
    HasCompactSupport (fun z => h1scConj (θ z)) :=
  hc.comp_left (g := h1scConj) (map_zero h1scConj)

lemma h1scLapConj (θ : Space → CVec3) (hθ : ContDiff ℝ ∞ θ) (y : Space) :
    UnforcedLeray.Short.PartIIIb.Concrete.lapS (fun z => h1scConj (θ z)) y
      = h1scConj (UnforcedLeray.Short.PartIIIb.Concrete.lapS θ y) := by
  unfold UnforcedLeray.Short.PartIIIb.Concrete.lapS
  have hD : ∀ j : Fin 3, DifferentiableAt ℝ (fun z => fderiv ℝ θ z (EuclideanSpace.single j (1 : ℝ))) y := by
    intro j
    have hf1 : ContDiff ℝ 1 (fderiv ℝ θ) := hθ.fderiv_right (m := 1) (by simp)
    exact (hf1.clm_apply contDiff_const).differentiable one_ne_zero y
  have key : ∀ j : Fin 3,
      fderiv ℝ (fun z => h1scConj (fderiv ℝ θ z (EuclideanSpace.single j (1 : ℝ)))) y
        (EuclideanSpace.single j (1 : ℝ))
      = h1scConj (fderiv ℝ (fun z => fderiv ℝ θ z (EuclideanSpace.single j (1 : ℝ))) y
          (EuclideanSpace.single j (1 : ℝ))) := by
    intro j
    have := (h1scConj.hasFDerivAt.comp y (hD j).hasFDerivAt).fderiv
    rw [show (fun z => h1scConj (fderiv ℝ θ z (EuclideanSpace.single j (1 : ℝ))))
        = h1scConj ∘ (fun z => fderiv ℝ θ z (EuclideanSpace.single j (1 : ℝ))) from rfl, this]
    rfl
  have hG : ∀ j : Fin 3, ∀ z : Space, fderiv ℝ (fun z => h1scConj (θ z)) z (EuclideanSpace.single j (1 : ℝ))
      = h1scConj (fderiv ℝ θ z (EuclideanSpace.single j (1 : ℝ))) := by
    intro j z
    have h2 := (h1scConj.hasFDerivAt.comp z (hθ.differentiable (by simp) z).hasFDerivAt).fderiv
    rw [show (fun z => h1scConj (θ z)) = h1scConj ∘ θ from rfl, h2]
    rfl
  simp only [hG]
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => key j

lemma h1scLapCont (θ : Space → CVec3) (hθ : ContDiff ℝ ∞ θ) :
    Continuous (UnforcedLeray.Short.PartIIIb.Concrete.lapS θ) := by
  unfold UnforcedLeray.Short.PartIIIb.Concrete.lapS
  simp only [Fin.sum_univ_three]
  have hG : ∀ j : Fin 3, ContDiff ℝ ∞ (fun z => fderiv ℝ θ z (EuclideanSpace.single j (1 : ℝ))) := by
    intro j
    have hf1 : ContDiff ℝ ∞ (fderiv ℝ θ) := hθ.fderiv_right (m := ∞) (by simp)
    exact hf1.clm_apply contDiff_const
  have hc' : ∀ j : Fin 3, Continuous fun y => fderiv ℝ (fun z => fderiv ℝ θ z (EuclideanSpace.single j (1 : ℝ))) y
      (EuclideanSpace.single j (1 : ℝ)) := fun j =>
    (hG j |>.continuous_fderiv (by simp)).clm_apply continuous_const
  exact ((hc' 0).add (hc' 1)).add (hc' 2)

lemma h1scLapComp (θ : Space → CVec3) (hc : HasCompactSupport θ) :
    HasCompactSupport (UnforcedLeray.Short.PartIIIb.Concrete.lapS θ) := by
  unfold UnforcedLeray.Short.PartIIIb.Concrete.lapS
  simp only [Fin.sum_univ_three]
  have hGc : ∀ j : Fin 3, HasCompactSupport (fun z => fderiv ℝ θ z (EuclideanSpace.single j (1 : ℝ))) := by
    intro j
    exact (hc.fderiv ℝ).comp_left (g := fun L : Space →L[ℝ] CVec3 => L (EuclideanSpace.single j (1 : ℝ)))
      (by simp)
  have hd : ∀ j : Fin 3, HasCompactSupport fun y => fderiv ℝ (fun z => fderiv ℝ θ z (EuclideanSpace.single j (1 : ℝ))) y
      (EuclideanSpace.single j (1 : ℝ)) := fun j =>
    (hGc j).fderiv_apply ℝ _
  exact ((hd 0).add (hd 1)).add (hd 2)

lemma h1scCoordCont (θ : Space → CVec3) (hθ : ContDiff ℝ ∞ θ) (i : Fin 3) :
    Continuous fun y => UnforcedLeray.Short.PartIIIb.Concrete.lapS θ y i :=
  (EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).continuous.comp (h1scLapCont θ hθ)

lemma h1scCoordComp (θ : Space → CVec3) (hc : HasCompactSupport θ) (i : Fin 3) :
    HasCompactSupport fun y => UnforcedLeray.Short.PartIIIb.Concrete.lapS θ y i :=
  (h1scLapComp θ hc).comp_left (g := fun z : CVec3 => z i) (by simp)

/-- Conjugation of the identity: `∫ f̄·Lθ = ∫ h̄·θ` for `SliceLapPair f h`. -/
lemma h1scConjPair (f h : Space → CVec3) (hid : SliceLapPair f h) :
    ∀ θ : Space → CVec3, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ y : Space, ∑ i : Fin 3, (starRingEnd ℂ) (f y i) *
          UnforcedLeray.Short.PartIIIb.Concrete.lapS θ y i)
        = ∫ y : Space, ∑ i : Fin 3, (starRingEnd ℂ) (h y i) * θ y i := by
  intro θ hθ hc
  have A := hid (fun z => h1scConj (θ z)) (h1scConj_contDiff θ hθ) (h1scConj_hasCompactSupport θ hc)
  simp only [h1scLapConj θ hθ, h1scConj_apply] at A
  have B := congrArg (starRingEnd ℂ) A
  rw [← integral_conj, ← integral_conj] at B
  simp only [map_sum, map_mul, Complex.conj_conj] at B
  exact B

lemma h1scSliceRe (f h : Space → CVec3) (hf : MemLp f 2 volume) (hh : MemLp h 2 volume)
    (hid : SliceLapPair f h) : SliceLapPair (reC f) (reC h) := by
  unfold SliceLapPair
  intro θ hθ hc
  have iF : Integrable (fun y => ∑ i : Fin 3, f y i *
      UnforcedLeray.Short.PartIIIb.Concrete.lapS θ y i) volume :=
    h1scInt f hf (fun i y => UnforcedLeray.Short.PartIIIb.Concrete.lapS θ y i)
      (fun i => h1scCoordCont θ hθ i) (fun i => h1scCoordComp θ hc i)
  have iF' : Integrable (fun y => ∑ i : Fin 3, (starRingEnd ℂ) (f y i) *
      UnforcedLeray.Short.PartIIIb.Concrete.lapS θ y i) volume := by
    have := h1scInt (fun y => h1scConj (f y)) (h1scConj.comp_memLp' hf)
      (fun i y => UnforcedLeray.Short.PartIIIb.Concrete.lapS θ y i)
      (fun i => h1scCoordCont θ hθ i) (fun i => h1scCoordComp θ hc i)
    simp only [h1scConj_apply] at this
    exact this
  have iG : Integrable (fun y => ∑ i : Fin 3, h y i * θ y i) volume :=
    h1scInt h hh (fun i y => θ y i) (fun i => h1scContI θ hθ i) (fun i => h1scCompI θ hc i)
  have iG' : Integrable (fun y => ∑ i : Fin 3, (starRingEnd ℂ) (h y i) * θ y i) volume := by
    have := h1scInt (fun y => h1scConj (h y)) (h1scConj.comp_memLp' hh)
      (fun i y => θ y i) (fun i => h1scContI θ hθ i) (fun i => h1scCompI θ hc i)
    simp only [h1scConj_apply] at this
    exact this
  have ptF : ∀ y, ∑ i : Fin 3, reC f y i * UnforcedLeray.Short.PartIIIb.Concrete.lapS θ y i
      = (1 / 2 : ℂ) * (∑ i : Fin 3, f y i * UnforcedLeray.Short.PartIIIb.Concrete.lapS θ y i
        + ∑ i : Fin 3, (starRingEnd ℂ) (f y i) * UnforcedLeray.Short.PartIIIb.Concrete.lapS θ y i) := by
    intro y
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [reC, PiLp.toLp_apply]
    rw [Complex.re_eq_add_conj]
    ring
  have ptH : ∀ y, ∑ i : Fin 3, reC h y i * θ y i
      = (1 / 2 : ℂ) * (∑ i : Fin 3, h y i * θ y i + ∑ i : Fin 3, (starRingEnd ℂ) (h y i) * θ y i) := by
    intro y
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [reC, PiLp.toLp_apply]
    rw [Complex.re_eq_add_conj]
    ring
  simp only [ptF, ptH]
  rw [integral_const_mul, integral_const_mul, integral_add iF iF', integral_add iG iG']
  rw [hid θ hθ hc, h1scConjPair f h hid θ hθ hc]

lemma h1scSliceIm (f h : Space → CVec3) (hf : MemLp f 2 volume) (hh : MemLp h 2 volume)
    (hid : SliceLapPair f h) : SliceLapPair (imC f) (imC h) := by
  unfold SliceLapPair
  intro θ hθ hc
  have iF : Integrable (fun y => ∑ i : Fin 3, f y i *
      UnforcedLeray.Short.PartIIIb.Concrete.lapS θ y i) volume :=
    h1scInt f hf (fun i y => UnforcedLeray.Short.PartIIIb.Concrete.lapS θ y i)
      (fun i => h1scCoordCont θ hθ i) (fun i => h1scCoordComp θ hc i)
  have iF' : Integrable (fun y => ∑ i : Fin 3, (starRingEnd ℂ) (f y i) *
      UnforcedLeray.Short.PartIIIb.Concrete.lapS θ y i) volume := by
    have := h1scInt (fun y => h1scConj (f y)) (h1scConj.comp_memLp' hf)
      (fun i y => UnforcedLeray.Short.PartIIIb.Concrete.lapS θ y i)
      (fun i => h1scCoordCont θ hθ i) (fun i => h1scCoordComp θ hc i)
    simp only [h1scConj_apply] at this
    exact this
  have ptF : ∀ y, ∑ i : Fin 3, imC f y i * UnforcedLeray.Short.PartIIIb.Concrete.lapS θ y i
      = (1 / (2 * Complex.I)) * (∑ i : Fin 3, f y i * UnforcedLeray.Short.PartIIIb.Concrete.lapS θ y i
        - ∑ i : Fin 3, (starRingEnd ℂ) (f y i) * UnforcedLeray.Short.PartIIIb.Concrete.lapS θ y i) := by
    intro y
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [imC, PiLp.toLp_apply]
    rw [Complex.im_eq_sub_conj]
    ring
  have ptH : ∀ y, ∑ i : Fin 3, imC h y i * θ y i
      = (1 / (2 * Complex.I)) * (∑ i : Fin 3, h y i * θ y i
        - ∑ i : Fin 3, (starRingEnd ℂ) (h y i) * θ y i) := by
    intro y
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [imC, PiLp.toLp_apply]
    rw [Complex.im_eq_sub_conj]
    ring
  have iG : Integrable (fun y => ∑ i : Fin 3, h y i * θ y i) volume :=
    h1scInt h hh (fun i y => θ y i) (fun i => h1scContI θ hθ i) (fun i => h1scCompI θ hc i)
  have iG' : Integrable (fun y => ∑ i : Fin 3, (starRingEnd ℂ) (h y i) * θ y i) volume := by
    have := h1scInt (fun y => h1scConj (h y)) (h1scConj.comp_memLp' hh)
      (fun i y => θ y i) (fun i => h1scContI θ hθ i) (fun i => h1scCompI θ hc i)
    simp only [h1scConj_apply] at this
    exact this
  simp only [ptF, ptH]
  rw [integral_const_mul, integral_const_mul, integral_sub iF iF', integral_sub iG iG']
  rw [hid θ hθ hc, h1scConjPair f h hid θ hθ hc]

theorem splitIdentity : SplitIdentity := by
  unfold SplitIdentity
  intro f h hf hh hid
  refine ⟨h1scMemLpRe f hf, h1scMemLpRe h hh, h1scMemLpIm f hf, h1scMemLpIm h hh,
    ?_, ?_, ?_, ?_, h1scSliceRe f h hf hh hid, h1scSliceIm f h hf hh hid⟩
  · intro y i
    simp [reC]
  · intro y i
    simp [reC]
  · intro y i
    simp [imC]
  · intro y i
    simp [imC]

end UnforcedLeray.Short.PartIIIb.Concrete
