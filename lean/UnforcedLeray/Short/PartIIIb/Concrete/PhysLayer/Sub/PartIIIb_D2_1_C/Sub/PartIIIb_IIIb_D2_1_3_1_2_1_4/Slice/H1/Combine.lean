import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1_2

/-!
# `combineWeak`: recombining weak derivatives of the real and imaginary parts

Source `the November 2 reference manuscript` lines 1351-1362.
Pointwise `f y i = reC f y i + I * imC f y i`; integrals split by linearity, the integrands being
integrable because `f`, `gr`, `gi` are in `L²` and the test derivatives are continuous with
compact support.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Real part of the `i`-th coordinate, as a real-linear map on `ℂ³`. -/
def h1cwProjR (i : Fin 3) : CVec3 →L[ℝ] ℂ :=
  (EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).restrictScalars ℝ

lemma h1cwMemLpProj (g : Space → CVec3) (hg : MemLp g 2 volume) (i : Fin 3) :
    MemLp (fun y => g y i) 2 volume :=
  (EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).comp_memLp' hg

lemma h1cwDCont (θ : Space → CVec3) (hθ : ContDiff ℝ ∞ θ) (i j : Fin 3) :
    Continuous fun y => fderiv ℝ (fun z => θ z i) y (EuclideanSpace.single j (1 : ℝ)) := by
  have hd : Differentiable ℝ θ := hθ.differentiable (by simp)
  have e : ∀ y, fderiv ℝ (fun z => θ z i) y = (h1cwProjR i).comp (fderiv ℝ θ y) := fun y => by
    have h : HasFDerivAt (fun z => θ z i) ((h1cwProjR i).comp (fderiv ℝ θ y)) y :=
      (h1cwProjR i).hasFDerivAt.comp y (hd y).hasFDerivAt
    exact h.fderiv
  have : (fun y => fderiv ℝ (fun z => θ z i) y (EuclideanSpace.single j (1 : ℝ)))
      = fun y => h1cwProjR i (fderiv ℝ θ y (EuclideanSpace.single j (1 : ℝ))) := by
    funext y
    rw [e y]
    rfl
  rw [this]
  exact (h1cwProjR i).continuous.comp
    ((hθ.continuous_fderiv (by simp)).clm_apply continuous_const)

lemma h1cwDComp (θ : Space → CVec3) (hc : HasCompactSupport θ) (i j : Fin 3) :
    HasCompactSupport fun y => fderiv ℝ (fun z => θ z i) y (EuclideanSpace.single j (1 : ℝ)) := by
  have h0 : HasCompactSupport (fun z => θ z i) :=
    hc.comp_left (g := fun z : CVec3 => z i) (by simp)
  exact h0.fderiv_apply ℝ (EuclideanSpace.single j (1 : ℝ))

lemma h1cwCompI (θ : Space → CVec3) (hc : HasCompactSupport θ) (i : Fin 3) :
    HasCompactSupport fun y => θ y i :=
  hc.comp_left (g := fun z : CVec3 => z i) (by simp)

lemma h1cwContI (θ : Space → CVec3) (hθ : ContDiff ℝ ∞ θ) (i : Fin 3) :
    Continuous fun y => θ y i :=
  (EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).continuous.comp hθ.continuous

/-- Integrability of `y ↦ ∑ᵢ g y i * ψ i y` for `g ∈ L²` and compactly supported continuous `ψ i`. -/
lemma h1cwInt (g : Space → CVec3) (hg : MemLp g 2 volume) (ψ : Fin 3 → Space → ℂ)
    (hψ : ∀ i, Continuous (ψ i)) (hψc : ∀ i, HasCompactSupport (ψ i)) :
    Integrable (fun y => ∑ i : Fin 3, g y i * ψ i y) volume := by
  refine integrable_finsetSum _ fun i _ => ?_
  exact MemLp.integrable_mul (p := 2) (q := 2) (h1cwMemLpProj g hg i)
    ((hψ i).memLp_of_hasCompactSupport (hψc i))

lemma h1cwMemLpRe (f : Space → CVec3) (hf : MemLp f 2 volume) : MemLp (reC f) 2 volume := by
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

lemma h1cwMemLpIm (f : Space → CVec3) (hf : MemLp f 2 volume) : MemLp (imC f) 2 volume := by
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

theorem combineWeak : CombineWeak := by
  unfold CombineWeak
  intro f gr gi j hf hgr hgi hr hi
  unfold WeakDer at hr hi ⊢
  intro θ hθ hc
  dsimp only
  have hr' := hr θ hθ hc
  have hi' := hi θ hθ hc
  have hA : ∀ y, ∑ i : Fin 3, f y i * fderiv ℝ (fun z => θ z i) y (EuclideanSpace.single j (1 : ℝ))
      = ∑ i : Fin 3, reC f y i * fderiv ℝ (fun z => θ z i) y (EuclideanSpace.single j (1 : ℝ))
        + Complex.I * ∑ i : Fin 3, imC f y i * fderiv ℝ (fun z => θ z i) y (EuclideanSpace.single j (1 : ℝ)) := by
    intro y
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h := Complex.re_add_im (f y i)
    simp only [reC, imC, PiLp.toLp_apply]
    linear_combination (-(fderiv ℝ (fun z => θ z i) y (EuclideanSpace.single j (1 : ℝ)))) * h
  have hB : ∀ y, ∑ i : Fin 3, (gr y + Complex.I • gi y) i * θ y i
      = ∑ i : Fin 3, gr y i * θ y i + Complex.I * ∑ i : Fin 3, gi y i * θ y i := by
    intro y
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have iR : Integrable (fun y => ∑ i : Fin 3, reC f y i *
      fderiv ℝ (fun z => θ z i) y (EuclideanSpace.single j (1 : ℝ))) volume :=
    h1cwInt (reC f) (h1cwMemLpRe f hf) (fun i y => fderiv ℝ (fun z => θ z i) y (EuclideanSpace.single j (1 : ℝ)))
      (fun i => h1cwDCont θ hθ i j) (fun i => h1cwDComp θ hc i j)
  have iI : Integrable (fun y => ∑ i : Fin 3, imC f y i *
      fderiv ℝ (fun z => θ z i) y (EuclideanSpace.single j (1 : ℝ))) volume :=
    h1cwInt (imC f) (h1cwMemLpIm f hf) (fun i y => fderiv ℝ (fun z => θ z i) y (EuclideanSpace.single j (1 : ℝ)))
      (fun i => h1cwDCont θ hθ i j) (fun i => h1cwDComp θ hc i j)
  have iGr : Integrable (fun y => ∑ i : Fin 3, gr y i * θ y i) volume :=
    h1cwInt gr hgr (fun i y => θ y i) (fun i => h1cwContI θ hθ i) (fun i => h1cwCompI θ hc i)
  have iGi : Integrable (fun y => ∑ i : Fin 3, gi y i * θ y i) volume :=
    h1cwInt gi hgi (fun i y => θ y i) (fun i => h1cwContI θ hθ i) (fun i => h1cwCompI θ hc i)
  have e1 : ∫ y, ∑ i : Fin 3, f y i * fderiv ℝ (fun z => θ z i) y (EuclideanSpace.single j (1 : ℝ))
      = (∫ y, ∑ i : Fin 3, reC f y i * fderiv ℝ (fun z => θ z i) y (EuclideanSpace.single j (1 : ℝ)))
        + Complex.I * ∫ y, ∑ i : Fin 3, imC f y i * fderiv ℝ (fun z => θ z i) y (EuclideanSpace.single j (1 : ℝ)) := by
    simp only [hA]
    rw [integral_add iR (iI.const_mul _), integral_const_mul]
  have e2 : ∫ y, ∑ i : Fin 3, (gr y + Complex.I • gi y) i * θ y i
      = (∫ y, ∑ i : Fin 3, gr y i * θ y i) + Complex.I * ∫ y, ∑ i : Fin 3, gi y i * θ y i := by
    simp only [hB]
    rw [integral_add iGr (iGi.const_mul _), integral_const_mul]
  rw [e1, e2]
  rw [show -((∫ y, ∑ i : Fin 3, reC f y i * fderiv ℝ (fun z => θ z i) y (EuclideanSpace.single j (1 : ℝ)))
        + Complex.I * ∫ y, ∑ i : Fin 3, imC f y i * fderiv ℝ (fun z => θ z i) y (EuclideanSpace.single j (1 : ℝ)))
      = -(∫ y, ∑ i : Fin 3, reC f y i * fderiv ℝ (fun z => θ z i) y (EuclideanSpace.single j (1 : ℝ)))
        + Complex.I * -(∫ y, ∑ i : Fin 3, imC f y i * fderiv ℝ (fun z => θ z i) y (EuclideanSpace.single j (1 : ℝ))) by ring]
  rw [hr', hi']

end UnforcedLeray.Short.PartIIIb.Concrete
