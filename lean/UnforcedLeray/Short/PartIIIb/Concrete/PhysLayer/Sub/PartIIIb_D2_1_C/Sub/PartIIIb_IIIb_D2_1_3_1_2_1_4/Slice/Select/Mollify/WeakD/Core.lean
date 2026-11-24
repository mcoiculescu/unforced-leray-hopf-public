import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4.Slice.Select.Mollify.WeakD.Deriv

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ContDiff Convolution
namespace UnforcedLeray.Short.PartIIIb.Concrete
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem convYW_comp_hasFDerivAt (i : Fin 3) {C : Space → CVec3} {L : Space →L[ℝ] CVec3} {x : Space}
    (h : HasFDerivAt C L x) :
    HasFDerivAt (fun y => C y i) (((EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).restrictScalars ℝ).comp L) x :=
  ((EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).restrictScalars ℝ).hasFDerivAt.comp x h

theorem convYW_comp_fderiv (K : Space → ℝ) (hK : ContDiff ℝ ∞ K) (hKc : HasCompactSupport K)
    (f : Space → CVec3) (hf : LocallyIntegrable f volume) (e : Space) (i : Fin 3) (x : Space) :
    fderiv ℝ (fun y => (∫ z : Space, K (y - z) • f z) i) x e
      = (∫ z : Space, fderiv ℝ K (x - z) e • f z) i := by
  rw [(convYW_comp_hasFDerivAt i (convYW_fderiv K hK hKc f hf x)).fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  rw [convYW_fderiv_apply K hK hKc f hf x e]
  rfl

theorem convYW_core (K : Space → ℝ) (hK : ContDiff ℝ ∞ K) (hKc : HasCompactSupport K)
    (f : Space → CVec3) (hf : LocallyIntegrable f volume) (e : Space)
    (θ : Space → CVec3) (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ) :
    -(∫ y : Space, ∑ i : Fin 3, (∫ z : Space, K (y - z) • f z) i *
        fderiv ℝ (fun z => θ z i) y e)
      = ∫ y : Space, ∑ i : Fin 3, (∫ z : Space, fderiv ℝ K (y - z) e • f z) i * θ y i := by
  have hCcont : Continuous (fun y : Space => ∫ z : Space, K (y - z) • f z) :=
    continuous_iff_continuousAt.2 fun x => (convYW_fderiv K hK hKc f hf x).continuousAt
  have hDc := convYW_D_cont K hK hKc f hf
  have hDe : Continuous (fun y : Space => ∫ z : Space, fderiv ℝ K (y - z) e • f z) := by
    have h1 : Continuous (fun y : Space => (convolution (fderiv ℝ K) f
        ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] CVec3 →L[ℝ] CVec3).precompL Space) volume y) e) :=
      (ContinuousLinearMap.apply ℝ CVec3 e).continuous.comp hDc
    refine h1.congr (fun y => ?_)
    exact convYW_fderiv_apply K hK hKc f hf y e
  have hCi_cont : ∀ i : Fin 3, Continuous (fun y => (∫ z : Space, K (y - z) • f z) i) := fun i =>
    ((EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).restrictScalars ℝ).continuous.comp hCcont
  have hDi_cont : ∀ i : Fin 3, Continuous (fun y => (∫ z : Space, fderiv ℝ K (y - z) e • f z) i) :=
    fun i => ((EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).restrictScalars ℝ).continuous.comp hDe
  have hθi : ∀ i : Fin 3, ContDiff ℝ ∞ (fun z => θ z i) := fun i =>
    ((EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp hθ
  have hθic : ∀ i : Fin 3, HasCompactSupport (fun z => θ z i) := fun i =>
    hθc.comp_left (g := fun v : CVec3 => v i) (by simp)
  have hdθ_cont : ∀ i : Fin 3, Continuous (fun y => fderiv ℝ (fun z => θ z i) y e) := fun i =>
    ((hθi i).continuous_fderiv (by simp)).clm_apply continuous_const
  have hdθ_cs : ∀ i : Fin 3, HasCompactSupport (fun y => fderiv ℝ (fun z => θ z i) y e) := fun i =>
    (hθic i).fderiv_apply (𝕜 := ℝ) e
  have hint1 : ∀ i : Fin 3, Integrable
      (fun y => (∫ z : Space, K (y - z) • f z) i * fderiv ℝ (fun z => θ z i) y e) := fun i =>
    Continuous.integrable_of_hasCompactSupport ((hCi_cont i).mul (hdθ_cont i))
      (HasCompactSupport.mul_left (hdθ_cs i))
  have hint2 : ∀ i : Fin 3, Integrable
      (fun y => (∫ z : Space, fderiv ℝ K (y - z) e • f z) i * θ y i) := fun i =>
    Continuous.integrable_of_hasCompactSupport ((hDi_cont i).mul (hθi i).continuous)
      (HasCompactSupport.mul_left (hθic i))
  have hsc : ∀ i : Fin 3, ∫ y : Space, (∫ z : Space, K (y - z) • f z) i *
        fderiv ℝ (fun z => θ z i) y e
      = -∫ y : Space, (∫ z : Space, fderiv ℝ K (y - z) e • f z) i * θ y i := by
    intro i
    have hA : Integrable (fun x : Space =>
        fderiv ℝ (fun y => (∫ z : Space, K (y - z) • f z) i) x e * θ x i) volume :=
      (hint2 i).congr (Filter.Eventually.of_forall fun x => by
        simp only [convYW_comp_fderiv K hK hKc f hf e i])
    have hC : Integrable (fun x : Space => (∫ z : Space, K (x - z) • f z) i * θ x i) volume :=
      Continuous.integrable_of_hasCompactSupport ((hCi_cont i).mul (hθi i).continuous)
        (HasCompactSupport.mul_left (hθic i))
    have hIBP := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      (f := fun y : Space => (∫ z : Space, K (y - z) • f z) i) (g := fun z => θ z i) (v := e)
      hA (hint1 i) hC
      (fun x _ => (convYW_comp_hasFDerivAt i (convYW_fderiv K hK hKc f hf x)).differentiableAt)
      (fun x _ => ((hθi i).differentiable (by simp)) x)
    simp only [convYW_comp_fderiv K hK hKc f hf e i] at hIBP
    exact hIBP
  rw [integral_finsetSum _ (fun i _ => hint1 i), integral_finsetSum _ (fun i _ => hint2 i)]
  simp only [hsc, Finset.sum_neg_distrib, neg_neg]

end UnforcedLeray.Short.PartIIIb.Concrete
