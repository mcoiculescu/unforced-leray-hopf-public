import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.AdjWeakSmooth
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.MovingPhiH1.WeakFromSmooth

/-!
# Part III-a: cell integration by parts for the adjoint (`adjWIBP`)

Source of record: `the November 2 reference manuscript` (SP) line 3060 and 2854-2865.

For a jointly smooth weak solution, `ladChi - ladDt = ν ladLapCx + ladTransport` by definition, and
the cell integration by parts against the cylinder test `ψ` moves the spatial derivatives of `φ`
onto `ψ`: the Laplacian by two applications of `mpWeakCore`, the transport term by the same with
`Φ_j = φ v_j`, and the divergence of the train velocity vanishes (`solenoidal`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

lemma ibpPdCx_periodic {c : ℝ} (k : Fin 2) (Φ : ℝ × ℝ → ℂ)
    (hper : ∀ x : ℝ × ℝ, Φ (x.1 + c, x.2) = Φ x) :
    ∀ x : ℝ × ℝ, pdCx k Φ (x.1 + c, x.2) = pdCx k Φ x := by
  intro x
  have hfun : (fun y : ℝ × ℝ => Φ (y + ((c, 0) : ℝ × ℝ))) = Φ := by
    funext y
    have hy : y + ((c, 0) : ℝ × ℝ) = (y.1 + c, y.2) := by ext <;> simp
    rw [hy]
    exact hper y
  have h1 : fderiv ℝ (fun y : ℝ × ℝ => Φ (y + ((c, 0) : ℝ × ℝ))) x
      = fderiv ℝ Φ (x + ((c, 0) : ℝ × ℝ)) := fderiv_comp_add_right _
  rw [hfun] at h1
  have hx : (x.1 + c, x.2) = x + ((c, 0) : ℝ × ℝ) := by ext <;> simp
  unfold pdCx
  rw [hx, ← h1]

lemma ibpPdCx_smooth {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (k : Fin 2) :
    ContDiff ℝ ∞ (pdCx k Φ) := by
  unfold pdCx
  exact (hΦ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

lemma ibpPdCx_mul {Φ w : ℝ × ℝ → ℂ} (hΦ : Differentiable ℝ Φ) (hw : Differentiable ℝ w)
    (k : Fin 2) (x : ℝ × ℝ) :
    pdCx k (fun y => Φ y * w y) x = pdCx k Φ x * w x + Φ x * pdCx k w x := by
  unfold pdCx
  rw [show (fun y => Φ y * w y) = Φ * w from rfl, fderiv_mul (hΦ x) (hw x)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

lemma ibpPdCx_ofReal (f : ℝ × ℝ → ℝ) (hf : Differentiable ℝ f) (k : Fin 2) (x : ℝ × ℝ) :
    pdCx k (fun y => ((f y : ℝ) : ℂ)) x = ((B0579.pd k f x : ℝ) : ℂ) := by
  unfold pdCx B0579.pd
  exact mpOfRealFderiv f hf x (B0579.dir k)

/-- **Leaf** `adjWIBP` (SP 3060, 2854-2865): cell integration by parts for a jointly smooth weak
solution against a cylinder test. -/
theorem adjWIBP (m : ℝ) : AdjWIBP m := by
  intro ν c tr t s g φ hctx ρ hρ ψ hψ
  obtain ⟨_, hc, ht, _, _, hA, hjs⟩ := hctx
  have hρ0 : 0 < ρ := lt_of_le_of_lt ht hρ.1
  have hφs : ContDiff ℝ ∞ (φ ρ) := adjContDiff_slice hjs (Ioo_subset_Ico_self hρ)
  have hper : ∀ x : ℝ × ℝ, φ ρ (x.1 + c, x.2) = φ ρ x :=
    fun x => hA.periodic ρ (Ioo_subset_Ico_self hρ) x
  have hφd : Differentiable ℝ (φ ρ) := hφs.differentiable (by simp)
  -- the train velocity at age ρ
  have hvC : ContDiff ℝ ∞ (fun x : ℝ × ℝ => tr.v ρ x) :=
    tr.isTrain.smooth_v.comp_contDiff (contDiff_const.prodMk contDiff_id)
      (fun x => ⟨hρ0.le, mem_univ _⟩)
  have hcoord : ∀ j : Fin 2, ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin 2) => v j) := fun j =>
    (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff
  have hvr : ∀ j : Fin 2, Differentiable ℝ (fun x : ℝ × ℝ => tr.v ρ x j) := fun j =>
    ((hcoord j).comp hvC).differentiable (by simp)
  have hvj : ∀ j : Fin 2, ContDiff ℝ ∞ (fun x : ℝ × ℝ => ((tr.v ρ x j : ℝ) : ℂ)) := fun j =>
    Complex.ofRealCLM.contDiff.comp ((hcoord j).comp hvC)
  have hvd : ∀ j : Fin 2, Differentiable ℝ (fun x : ℝ × ℝ => ((tr.v ρ x j : ℝ) : ℂ)) :=
    fun j => (hvj j).differentiable (by simp)
  have hvper : ∀ x : ℝ × ℝ, tr.v ρ (x.1 + c, x.2) = tr.v ρ x :=
    fun x => tr.isTrain.periodic_v ρ hρ0.le x
  -- the divergence of the train velocity vanishes pointwise
  have hdiv : ∀ x : ℝ × ℝ, pdCx 0 (fun y => ((tr.v ρ y 0 : ℝ) : ℂ)) x +
      pdCx 1 (fun y => ((tr.v ρ y 1 : ℝ) : ℂ)) x = 0 := by
    intro x
    rw [ibpPdCx_ofReal _ (hvr 0) 0 x, ibpPdCx_ofReal _ (hvr 1) 1 x, ← Complex.ofReal_add]
    have hd := tr.isTrain.solenoidal ρ hρ0.le x
    unfold UnforcedLeray.Cyl.divergence at hd
    rw [UnforcedLeray.Cyl.partialQ_eq_fderiv (hvr 0) x,
      UnforcedLeray.Cyl.partialEta_eq_fderiv (hvr 1) x] at hd
    have hd' : B0579.pd 0 (fun y => tr.v ρ y 0) x + B0579.pd 1 (fun y => tr.v ρ y 1) x = 0 := hd
    rw [hd', Complex.ofReal_zero]
  -- the product rule for the velocity pieces
  have hΦs : ∀ j : Fin 2, ContDiff ℝ ∞ (fun x => φ ρ x * ((tr.v ρ x j : ℝ) : ℂ)) :=
    fun j => hφs.mul (hvj j)
  have hΦper : ∀ j : Fin 2, ∀ x : ℝ × ℝ,
      φ ρ (x.1 + c, x.2) * ((tr.v ρ (x.1 + c, x.2) j : ℝ) : ℂ) = φ ρ x * ((tr.v ρ x j : ℝ) : ℂ) :=
    fun j x => by rw [hper x, hvper x]
  have hc' : 0 < c := hc
  -- the transport piece, integrated by parts
  have hP : ∀ j : Fin 2,
      IntegrableOn (fun x => φ ρ x * ((tr.v ρ x j : ℝ) : ℂ) * (B0579.pd j ψ x : ℂ))
        (B0579.cell c) ∧
      IntegrableOn (fun x => pdCx j (fun y => φ ρ y * ((tr.v ρ y j : ℝ) : ℂ)) x * (ψ x : ℂ))
        (B0579.cell c) ∧
      ∫ x in B0579.cell c, φ ρ x * ((tr.v ρ x j : ℝ) : ℂ) * (B0579.pd j ψ x : ℂ) =
        -∫ x in B0579.cell c, pdCx j (fun y => φ ρ y * ((tr.v ρ y j : ℝ) : ℂ)) x * (ψ x : ℂ) :=
    fun j => mpWeakCore c hc' _ (hΦs j) (hΦper j) j ψ hψ
  -- the Laplacian piece, integrated by parts twice
  have hLap : ∀ k : Fin 2,
      IntegrableOn (fun x => φ ρ x * (B0579.pd k (B0579.pd k ψ) x : ℂ)) (B0579.cell c) ∧
      IntegrableOn (fun x => pdCx k (pdCx k (φ ρ)) x * (ψ x : ℂ)) (B0579.cell c) ∧
      ∫ x in B0579.cell c, φ ρ x * (B0579.pd k (B0579.pd k ψ) x : ℂ) =
        ∫ x in B0579.cell c, pdCx k (pdCx k (φ ρ)) x * (ψ x : ℂ) := by
    intro k
    obtain ⟨i1, _, e1⟩ := mpWeakCore c hc' (φ ρ) hφs hper k (B0579.pd k ψ) (hψ.pd k)
    obtain ⟨_, i2, e2⟩ := mpWeakCore c hc' (pdCx k (φ ρ)) (ibpPdCx_smooth hφs k)
      (ibpPdCx_periodic k (φ ρ) hper) k ψ hψ
    refine ⟨i1, i2, ?_⟩
    rw [e1, e2, neg_neg]
  -- the transport pieces agree with the integrand of `ladTransport`
  have hTpt : ∀ x : ℝ × ℝ,
      pdCx 0 (fun y => φ ρ y * ((tr.v ρ y 0 : ℝ) : ℂ)) x * (ψ x : ℂ) +
        pdCx 1 (fun y => φ ρ y * ((tr.v ρ y 1 : ℝ) : ℂ)) x * (ψ x : ℂ) =
        ladTransport tr ρ (φ ρ) x * (ψ x : ℂ) := by
    intro x
    rw [ibpPdCx_mul hφd (hvd 0) 0 x, ibpPdCx_mul hφd (hvd 1) 1 x]
    have hdx := hdiv x
    simp only [ladTransport]
    linear_combination (φ ρ x * (ψ x : ℂ)) * hdx
  have hTint : IntegrableOn (fun x => ladTransport tr ρ (φ ρ) x * (ψ x : ℂ)) (B0579.cell c) :=
    ((hP 0).2.1.add (hP 1).2.1).congr_fun (fun x _ => by
      simp only [Pi.add_apply]
      exact hTpt x) (B0579.measurableSet_cell c)
  -- the Laplacian part of the left side
  have hA1 : ∫ x in B0579.cell c, φ ρ x * (lapP ψ x : ℂ) =
      ∫ x in B0579.cell c, ladLapCx (φ ρ) x * (ψ x : ℂ) := by
    have hsplit : (fun x => φ ρ x * (lapP ψ x : ℂ)) = fun x =>
        φ ρ x * (B0579.pd 0 (B0579.pd 0 ψ) x : ℂ) + φ ρ x * (B0579.pd 1 (B0579.pd 1 ψ) x : ℂ) := by
      funext x
      simp only [lapP]
      push_cast
      ring
    rw [hsplit, integral_add (hLap 0).1 (hLap 1).1, (hLap 0).2.2, (hLap 1).2.2,
      ← integral_add (hLap 0).2.1 (hLap 1).2.1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [ladLapCx]
    ring
  -- the transport part of the left side
  have hB1 : ∫ x in B0579.cell c, φ ρ x *
      ((tr.v ρ x 0 * B0579.pd 0 ψ x + tr.v ρ x 1 * B0579.pd 1 ψ x : ℝ) : ℂ) =
      -∫ x in B0579.cell c, ladTransport tr ρ (φ ρ) x * (ψ x : ℂ) := by
    have hsplit : (fun x => φ ρ x * ((tr.v ρ x 0 * B0579.pd 0 ψ x + tr.v ρ x 1 * B0579.pd 1 ψ x : ℝ) : ℂ))
        = fun x => φ ρ x * ((tr.v ρ x 0 : ℝ) : ℂ) * (B0579.pd 0 ψ x : ℂ) +
            φ ρ x * ((tr.v ρ x 1 : ℝ) : ℂ) * (B0579.pd 1 ψ x : ℂ) := by
      funext x
      push_cast
      ring
    rw [hsplit, integral_add (hP 0).1 (hP 1).1, (hP 0).2.2, (hP 1).2.2, ← neg_add,
      ← integral_add (hP 0).2.1 (hP 1).2.1]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact hTpt x
  -- the left side
  have hI1 : IntegrableOn (fun x => φ ρ x * (lapP ψ x : ℂ)) (B0579.cell c) := by
    have hfun : (fun x => φ ρ x * (lapP ψ x : ℂ)) = fun x =>
        φ ρ x * (B0579.pd 0 (B0579.pd 0 ψ) x : ℂ) + φ ρ x * (B0579.pd 1 (B0579.pd 1 ψ) x : ℂ) := by
      funext x
      simp only [lapP]
      push_cast
      ring
    rw [hfun]
    exact (hLap 0).1.add (hLap 1).1
  have hI2 : IntegrableOn (fun x => φ ρ x *
      ((tr.v ρ x 0 * B0579.pd 0 ψ x + tr.v ρ x 1 * B0579.pd 1 ψ x : ℝ) : ℂ)) (B0579.cell c) := by
    refine ((hP 0).1.add (hP 1).1).congr_fun (fun x _ => ?_) (B0579.measurableSet_cell c)
    simp only [Pi.add_apply]
    push_cast
    ring
  have hLHS : ∫ x in B0579.cell c, φ ρ x *
      ((ν * lapP ψ x - (tr.v ρ x 0 * B0579.pd 0 ψ x + tr.v ρ x 1 * B0579.pd 1 ψ x) : ℝ) : ℂ) =
      (ν : ℂ) * (∫ x in B0579.cell c, φ ρ x * (lapP ψ x : ℂ)) -
        ∫ x in B0579.cell c, φ ρ x *
          ((tr.v ρ x 0 * B0579.pd 0 ψ x + tr.v ρ x 1 * B0579.pd 1 ψ x : ℝ) : ℂ) := by
    have hpt : (fun x => φ ρ x *
        ((ν * lapP ψ x - (tr.v ρ x 0 * B0579.pd 0 ψ x + tr.v ρ x 1 * B0579.pd 1 ψ x) : ℝ) : ℂ))
        = fun x => (ν : ℂ) * (φ ρ x * (lapP ψ x : ℂ)) -
            φ ρ x * ((tr.v ρ x 0 * B0579.pd 0 ψ x + tr.v ρ x 1 * B0579.pd 1 ψ x : ℝ) : ℂ) := by
      funext x
      push_cast
      ring
    rw [hpt, integral_sub ((Integrable.const_mul hI1 (ν : ℂ))) hI2, integral_const_mul]
  -- the right side
  have hRHS : ∫ x in B0579.cell c, (ladChi tr φ ρ x - ladDt φ ρ x) * (ψ x : ℂ) =
      (ν : ℂ) * (∫ x in B0579.cell c, ladLapCx (φ ρ) x * (ψ x : ℂ)) +
        ∫ x in B0579.cell c, ladTransport tr ρ (φ ρ) x * (ψ x : ℂ) := by
    have hL : IntegrableOn (fun x => ladLapCx (φ ρ) x * (ψ x : ℂ)) (B0579.cell c) := by
      have hfun : (fun x => ladLapCx (φ ρ) x * (ψ x : ℂ)) = fun x =>
          pdCx 0 (pdCx 0 (φ ρ)) x * (ψ x : ℂ) + pdCx 1 (pdCx 1 (φ ρ)) x * (ψ x : ℂ) := by
        funext x
        simp only [ladLapCx]
        ring
      rw [hfun]
      exact (hLap 0).2.1.add (hLap 1).2.1
    rw [← integral_const_mul, ← integral_add (Integrable.const_mul hL (ν : ℂ)) hTint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [ladChi, ladTransport, ladLapCx]
    ring
  rw [hLHS, hRHS, hA1, hB1]
  ring

end UnforcedLeray.Short.IIIa
