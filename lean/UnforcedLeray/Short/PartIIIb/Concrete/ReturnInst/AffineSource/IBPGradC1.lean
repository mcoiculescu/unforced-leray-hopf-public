import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.RADefs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.IBPGradC1.C1Calculus

/-!
# `IBPGradC1`: `⟨Φ, ∇q⟩ = -⟨q, div Φ⟩` for `C¹` scalars and every phase test (source 5001-5008,
5040-5043)

Pointwise, `Φ · ∇q = ∑ᵢ ∂ᵢ(Φᵢ q) - q ∑ᵢ ∂ᵢΦᵢ`.  The divergence terms `∂ᵢ(Φᵢ q)` are `C¹` with
bounded `y`-support and integrate to zero over the slab (`c1_slab_dy`), leaving `-scalarPair`.
This is `ibpGrad_proved` without `div Φ = 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)
open UnforcedLeray.Short.IIb

/-- The integrand `Φᵢ · q` (complex). -/
def ibpGradC1K (q : ℝ → Space → ℝ) (Φ : ℝ × Space → CVec3) (i : Fin 3) : ℝ × Space → ℂ :=
  fun w => Φ w i * ((q w.1 w.2 : ℝ) : ℂ)

theorem ibpGradC1 : IBPGradC1 := by
  intro P q hq Φ hΦ
  obtain ⟨R, hR⟩ := hΦ.bounded_support
  have hΦc : ContDiff ℝ ∞ Φ := hΦ.smooth
  have hQ : ContDiff ℝ 1 (fun w : ℝ × Space => ((q w.1 w.2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hq
  have hKc : ∀ i, ContDiff ℝ 1 (ibpGradC1K q Φ i) := fun i =>
    ((srwf_coord_contDiff hΦc i).of_le (by simp)).mul hQ
  have hK_bdd : ∀ i, ∀ τ y, R < ‖y‖ → ibpGradC1K q Φ i (τ, y) = 0 := fun i τ y hy => by
    simp [ibpGradC1K, hR τ y hy]
  have hint : ∀ i, Integrable (fun z => dy i (ibpGradC1K q Φ i) z) (srwfSlab P) ∧
      ∫ z, dy i (ibpGradC1K q Φ i) z ∂(srwfSlab P) = 0 := fun i =>
    c1_slab_dy (R := R) (hKc i) (hK_bdd i) i
  have hc : ∀ x : ℝ × Space, ∀ i : Fin 3, realCf (fun τ y => physGrad (q τ) y) x i =
      ((fderiv ℝ (fun y => q x.1 y) x.2 (coordinateVector i) : ℝ) : ℂ) := by
    intro x i
    simp [realCf, B0412.realC_apply, physGrad]
  have hpt : ∀ x : ℝ × Space,
      dotL (Φ x) (realCf (fun τ y => physGrad (q τ) y) x) =
        ∑ i : Fin 3, dy i (ibpGradC1K q Φ i) x -
          ((q x.1 x.2 : ℝ) : ℂ) * ∑ i : Fin 3, dy i Φ x i := by
    intro x
    have hstep : ∀ i : Fin 3, dy i (ibpGradC1K q Φ i) x =
        dy i Φ x i * ((q x.1 x.2 : ℝ) : ℂ) +
          Φ x i * ((fderiv ℝ (fun y => q x.1 y) x.2 (coordinateVector i) : ℝ) : ℂ) := by
      intro i
      have hf : Differentiable ℝ (fun w : ℝ × Space => Φ w i) :=
        (srwf_coord_contDiff hΦc i).differentiable (by simp)
      have hg : Differentiable ℝ (fun w : ℝ × Space => ((q w.1 w.2 : ℝ) : ℂ)) :=
        hQ.differentiable (by simp)
      have h1 := srwf_dy_mul hf hg i x
      have h2 := srwf_dy_coord (U := Φ) (hΦc.differentiable (by simp)) i i x
      have h3 := c1_id_dy_ofReal (G := fun w : ℝ × Space => q w.1 w.2) hq i x
      unfold ibpGradC1K
      rw [h1, h2, h3]
    rw [dotL_apply, Finset.sum_congr rfl fun i _ => hstep i, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hc x i]
    ring
  unfold pairF
  show phaseInt P (fun x => dotL (Φ x) (realCf (fun τ y => physGrad (q τ) y) x)) =
    -scalarPair P (fun x => q x.1 x.2) Φ
  have hqcont : Continuous (fun z : ℝ × Space => ((q z.1 z.2 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp hq.continuous
  have hdyΦ : ∀ i : Fin 3, ∀ τ y, R < ‖y‖ → dy i Φ (τ, y) = 0 := fun i τ y hy =>
    srwf_dy_bdd hR i τ y hy
  have hqsum_cont : Continuous (fun z : ℝ × Space => ∑ i : Fin 3, dy i Φ z i) :=
    continuous_finset_sum _ fun i _ =>
      (srwf_coord_contDiff (UnforcedLeray.PhaseSpace.contDiff_dy hΦc i) i).continuous
  have hqsum_bdd : ∀ τ y, R < ‖y‖ → ∑ i : Fin 3, dy i Φ (τ, y) i = 0 := fun τ y hy => by
    simp [hdyΦ _ τ y hy]
  have hqI : Integrable (fun z : ℝ × Space => ((q z.1 z.2 : ℝ) : ℂ) * ∑ i : Fin 3, dy i Φ z i)
      (srwfSlab P) := by
    have hcont := hqcont.mul hqsum_cont
    have hbdd : ∀ τ y, R < ‖y‖ →
        ((q (τ, y).1 (τ, y).2 : ℝ) : ℂ) * ∑ i : Fin 3, dy i Φ (τ, y) i = 0 := fun τ y hy => by
      simp [hqsum_bdd τ y hy]
    exact UnforcedLeray.B0005.integrable_slab (𝒯 := P) hcont hbdd
  have hsumI : Integrable (fun z => ∑ i : Fin 3, dy i (ibpGradC1K q Φ i) z) (srwfSlab P) :=
    integrable_finsetSum _ fun i _ => (hint i).1
  have hI : Integrable (fun z : ℝ × Space => ∑ i : Fin 3, dy i (ibpGradC1K q Φ i) z -
      ((q z.1 z.2 : ℝ) : ℂ) * ∑ i : Fin 3, dy i Φ z i) (srwfSlab P) :=
    hsumI.sub hqI
  rw [show (fun x : ℝ × Space => dotL (Φ x) (realCf (fun τ y => physGrad (q τ) y) x)) =
      fun x => ∑ i : Fin 3, dy i (ibpGradC1K q Φ i) x -
        ((q x.1 x.2 : ℝ) : ℂ) * ∑ i : Fin 3, dy i Φ x i from funext hpt]
  unfold scalarPair
  rw [srwf_phaseInt_eq hI, srwf_phaseInt_eq hqI, integral_sub hsumI hqI,
    integral_finsetSum _ fun i _ => (hint i).1, Finset.sum_eq_zero fun i _ => (hint i).2,
    zero_sub, smul_neg]

end UnforcedLeray.Short.PartIIIb.Concrete
