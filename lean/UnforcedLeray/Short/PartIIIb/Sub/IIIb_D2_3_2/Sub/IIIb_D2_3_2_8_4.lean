import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_8
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.SmoothResidualWeakForm

/-!
# `IBPGrad`: the gradient term is killed by `div Φ = 0` (source 4268-4270)

Proof: for `Φ` a solenoidal phase test and `q` smooth, pointwise
`Φ · ∇q = ∑ᵢ ∂ᵢ(Φᵢ q) - q ∑ᵢ ∂ᵢΦᵢ = ∑ᵢ ∂ᵢ(Φᵢ q)`, and each slab integral of
`∂ᵢ(Φᵢ q)` vanishes by `srwf_slab_dy` (compact `y`-support of `Φ`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)
open UnforcedLeray.Short.IIb

/-- `∂_{y_i}` of a complexified real function, pointwise (scalar analogue of
`IIb.dy_realC_comp`). -/
theorem ig_dy_ofReal {G : ℝ × Space → ℝ} (hG : ContDiff ℝ ∞ G) (i : Fin 3) (x : ℝ × Space) :
    dy i (fun w : ℝ × Space => ((G w : ℝ) : ℂ)) x =
      ((fderiv ℝ (fun y => G (x.1, y)) x.2 (coordinateVector i) : ℝ) : ℂ) := by
  have hd : DifferentiableAt ℝ G x := (hG.differentiable (by simp)) x
  have h : HasFDerivAt (fun w : ℝ × Space => ((G w : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ G x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x hd.hasFDerivAt
  have hs : fderiv ℝ (fun y => G (x.1, y)) x.2 =
      (fderiv ℝ G x).comp (ContinuousLinearMap.inr ℝ ℝ Space) :=
    UnforcedLeray.B0005.fderiv_slice_space hd
  simp only [dy]
  rw [h.fderiv, hs]
  simp [coordinateVector]

/-- The integrand `Φᵢ · q` (complex). -/
def ibpGradK (q : ℝ → Space → ℝ) (Φ : ℝ × Space → CVec3) (i : Fin 3) : ℝ × Space → ℂ :=
  fun w => Φ w i * ((q w.1 w.2 : ℝ) : ℂ)

theorem ibpGrad_proved : IBPGrad := by
  intro P q hq Φ hΦ
  obtain ⟨hΦs, hΦdiv⟩ := hΦ
  obtain ⟨R, hR⟩ := hΦs.bounded_support
  have hΦc : ContDiff ℝ ∞ Φ := hΦs.smooth
  have hQ : ContDiff ℝ ∞ (fun w : ℝ × Space => ((q w.1 w.2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hq
  have hKc : ∀ i, ContDiff ℝ ∞ (ibpGradK q Φ i) := fun i =>
    (srwf_coord_contDiff hΦc i).mul hQ
  have hK_bdd : ∀ i, ∀ τ y, R < ‖y‖ → ibpGradK q Φ i (τ, y) = 0 := fun i τ y hy => by
    simp [ibpGradK, hR τ y hy]
  have hint : ∀ i, Integrable (fun z => dy i (ibpGradK q Φ i) z) (srwfSlab P) ∧
      ∫ z, dy i (ibpGradK q Φ i) z ∂(srwfSlab P) = 0 := fun i =>
    srwf_slab_dy (R := R) (hKc i) (hK_bdd i) i
  have hpt : ∀ x : ℝ × Space,
      dotL (Φ x) (realCf (fun τ y => physGrad (q τ) y) x) =
        ∑ i : Fin 3, dy i (ibpGradK q Φ i) x := by
    intro x
    have hz : ∑ i : Fin 3, dy i Φ x i = 0 := hΦdiv x
    have hstep : ∀ i : Fin 3, dy i (ibpGradK q Φ i) x =
        dy i Φ x i * ((q x.1 x.2 : ℝ) : ℂ) +
          Φ x i * ((fderiv ℝ (fun y => q x.1 y) x.2 (coordinateVector i) : ℝ) : ℂ) := by
      intro i
      have hf : Differentiable ℝ (fun w : ℝ × Space => Φ w i) :=
        (srwf_coord_contDiff hΦc i).differentiable (by simp)
      have hg : Differentiable ℝ (fun w : ℝ × Space => ((q w.1 w.2 : ℝ) : ℂ)) :=
        hQ.differentiable (by simp)
      have h1 := srwf_dy_mul hf hg i x
      have h2 := srwf_dy_coord (U := Φ) (hΦc.differentiable (by simp)) i i x
      have h3 := ig_dy_ofReal (G := fun w : ℝ × Space => q w.1 w.2) hq i x
      unfold ibpGradK
      rw [h1, h2, h3]
    rw [Finset.sum_congr rfl fun i _ => hstep i, Finset.sum_add_distrib, ← Finset.sum_mul, hz,
      zero_mul, zero_add]
    rw [dotL_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [realCf, B0412.realC_apply, physGrad]
  unfold pairF
  show phaseInt P (fun x => dotL (Φ x) (realCf (fun τ y => physGrad (q τ) y) x)) = 0
  rw [show (fun x => dotL (Φ x) (realCf (fun τ y => physGrad (q τ) y) x)) =
      fun x => ∑ i : Fin 3, dy i (ibpGradK q Φ i) x from funext hpt]
  rw [srwf_phaseInt_eq (integrable_finsetSum _ fun i _ => (hint i).1),
    integral_finsetSum _ fun i _ => (hint i).1,
    Finset.sum_eq_zero fun i _ => (hint i).2, smul_zero]

end UnforcedLeray.Short.PartIIIb.Concrete
