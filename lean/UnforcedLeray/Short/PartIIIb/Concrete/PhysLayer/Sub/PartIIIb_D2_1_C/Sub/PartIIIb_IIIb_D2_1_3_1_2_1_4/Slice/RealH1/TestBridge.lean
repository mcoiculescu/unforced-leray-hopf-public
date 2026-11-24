import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1_2_1

/-!
# Real test bridge (`RealTestBridge`)

Source `the November 2 reference manuscript` lines 1351-1362.
Restriction of the complex slice identity `SliceLapPair` to real vector tests `θ = embR φ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Chain rule for the continuous linear map `embL`. -/
theorem fderiv_embL_comp (g : Space → Space) (x : Space) (hg : DifferentiableAt ℝ g x) :
    fderiv ℝ (fun z => embL (g z)) x = embL.comp (fderiv ℝ g x) :=
  (HasFDerivAt.comp x (ContinuousLinearMap.hasFDerivAt (f := embL) (x := g x))
    hg.hasFDerivAt).fderiv

/-- The Laplacian of `embR φ` is `embR (Δφ)` for a vector test `φ`. -/
theorem lapS_embR (φ : Space → Space) (hφ : UnforcedLeray.Blueprint.IsVectorTest φ) (y : Space) :
    lapS (embR φ) y = embR (UnforcedLeray.Blueprint.ModeId.testLap φ) y := by
  have hg : ∀ j : Fin 3, DifferentiableAt ℝ
      (fun z => fderiv ℝ φ z (EuclideanSpace.single j (1 : ℝ))) y := fun j =>
    (((hφ.smooth.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).differentiable
      (by simp)) y
  have hsum : lapS (embR φ) y = ∑ j : Fin 3, embL (fderiv ℝ
      (fun z => fderiv ℝ φ z (EuclideanSpace.single j (1 : ℝ))) y
        (EuclideanSpace.single j (1 : ℝ))) := by
    unfold lapS
    refine Finset.sum_congr rfl fun j _ => ?_
    have hfun : (fun z => fderiv ℝ (embR φ) z (EuclideanSpace.single j (1 : ℝ)))
        = fun z => embL (fderiv ℝ φ z (EuclideanSpace.single j (1 : ℝ))) := by
      funext z
      rw [embR_eq, fderiv_embL_comp φ z (hφ.smooth.differentiable (by simp) z)]
      rfl
    rw [hfun, fderiv_embL_comp _ y (hg j)]
    rfl
  rw [hsum, embR_eq]
  simp only [UnforcedLeray.Blueprint.ModeId.testLap, map_sum]
  rfl

/-- For a real field `f`, the pairing `∑ᵢ f_i (embR u)_i` is the real inner product `⟨reV f, u⟩`. -/
theorem sum_real_embR (f : Space → CVec3) (hf : IsRealV f) (u : Space → Space) (y : Space) :
    (∑ i : Fin 3, f y i * embR u y i) = ((inner ℝ (reV f y) (u y) : ℝ) : ℂ) := by
  have hr : ∀ i, f y i = (((f y i).re : ℝ) : ℂ) := fun i =>
    Complex.ext (by simp) (by simpa using hf y i)
  have e : ∀ i, f y i * embR u y i = (((u y i) * (f y i).re : ℝ) : ℂ) := by
    intro i
    conv_lhs => rw [hr i]
    simp [embR]
    ring
  have hin : inner ℝ (reV f y) (u y) = ∑ i : Fin 3, (u y i) * (f y i).re := by
    simp [reV, PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  rw [hin, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun i _ => e i

theorem realTestBridge : RealTestBridge := by
  intro f h hf hh _mf _mh hid φ hφ
  have hθ : ContDiff ℝ ∞ (embR φ) := by
    rw [embR_eq]
    exact embL.contDiff.comp hφ.smooth
  have hc : HasCompactSupport (embR φ) := by
    rw [embR_eq]
    exact HasCompactSupport.comp_left (g := ⇑embL) hφ.compact (map_zero embL)
  have key := hid (embR φ) hθ hc
  simp_rw [lapS_embR φ hφ, sum_real_embR f hf, sum_real_embR h hh] at key
  rw [integral_complex_ofReal, integral_complex_ofReal] at key
  exact Complex.ofReal_injective key

end UnforcedLeray.Short.PartIIIb.Concrete
