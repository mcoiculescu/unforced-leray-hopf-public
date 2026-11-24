import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.KF.KF3.PresGrad
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.KF.KF3.PresSmooth
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.KF.KF3.HeatNewtonComp
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.KF.KF3.TailIBP

/-!
# `kf3HeatPres : KF3HeatPres` (source 3597-3601, 3617-3618)

Route: by `kf3PresGrad`, `∂_ip(x - y, τ) = Σ_j (∂_jN ⋆ h_j)(x - y)` with
`h_j = fderiv (cartDiv M (·, τ) j) · e_i`, a spatial test (`kf3hp_spatial`).  Split the finite sum
(`integrable_finset_sum`, `integral_finset_sum`), apply `kf3HeatNewtonComp` to each `h_j`, and
conclude with `kf3TailIBP`, which also gives the integrability of the right-hand side.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

/-- The components of `cartDiv M` are smooth in `(x, τ)`. -/
theorem kf3hp_cart_smooth {P : ℝ} {M : Space × ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hM : IsOuterTest P M) (j : Fin 3) :
    ContDiff ℝ ∞ (fun q : Space × ℝ => cartDiv M (q.1, q.2) j) := by
  have h1 : ContDiff ℝ ∞ (fun y : Space × ℝ => (y.2, y.1)) := contDiff_snd.prodMk contDiff_fst
  exact (kf3p_phi_smooth P M hM j).comp h1

/-- The slice derivative of a far-supported `cartDiv` vanishes outside the support ball. -/
theorem kf3hp_slice_far (P : ℝ) (M : Space × ℝ → Matrix (Fin 3) (Fin 3) ℝ) (hM : IsOuterTest P M)
    (r : ℝ) (hr : ∀ y : Space × ℝ, M y ≠ 0 → ‖y.1‖ ≤ r) (z : Space) (τ : ℝ) (hz : r < ‖z‖)
    (i j : Fin 3) :
    fderiv ℝ (fun x' : Space => cartDiv M (x', τ) j) z (UnforcedLeray.coordinateVector i) = 0 := by
  have hev : (fun x' : Space => cartDiv M (x', τ) j) =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
    filter_upwards [(isOpen_lt (continuous_const (y := r)) continuous_norm :
      IsOpen {x'' : Space | r < ‖x''‖}).mem_nhds hz] with x' hx''
    exact kf3g_cartDiv_far P M hM r hr x' τ hx'' j
  rw [hev.fderiv_eq]
  simp

/-- The `i`-th derivative of a slice of `cartDiv M` in the `j`-th component is a spatial test. -/
theorem kf3hp_spatial (P : ℝ) (M : Space × ℝ → Matrix (Fin 3) (Fin 3) ℝ) (hM : IsOuterTest P M)
    (τ : ℝ) (i j : Fin 3) :
    UnforcedLeray.IsSpatialTest
      (fun z : Space => fderiv ℝ (fun x' : Space => cartDiv M (x', τ) j) z
        (UnforcedLeray.coordinateVector i)) := by
  obtain ⟨r, hr⟩ := hM.bounded
  have hpair : ContDiff ℝ ∞ (fun x' : Space => (x', τ)) := contDiff_id.prodMk contDiff_const
  have hslice : ContDiff ℝ ∞ (fun x' : Space => cartDiv M (x', τ) j) :=
    (kf3hp_cart_smooth hM j).comp hpair
  have hsm : ContDiff ℝ ∞ (fun z : Space => fderiv ℝ (fun x' : Space => cartDiv M (x', τ) j) z) :=
    hslice.fderiv_right (m := ∞) (by simp)
  refine ⟨hsm.clm_apply contDiff_const, HasCompactSupport.intro
    (isCompact_closedBall (0 : Space) r) (fun z hz => ?_)⟩
  have hz' : r < ‖z‖ := lt_of_not_ge (fun h => hz (mem_closedBall_zero_iff.2 h))
  exact kf3hp_slice_far P M hM r hr z τ hz' i j

/-- **Leaf: the heat integral of the pressure gradient** (source 3597-3601, 3617-3618). -/
theorem kf3HeatPres : KF3HeatPres := by
  intro P M hM τ x θ hθ i
  obtain ⟨hTI1, hTI2⟩ := kf3TailIBP P M hM τ x θ hθ i
  have hsp : ∀ j : Fin 3, UnforcedLeray.IsSpatialTest
      (fun z : Space => fderiv ℝ (fun x' : Space => cartDiv M (x', τ) j) z
        (UnforcedLeray.coordinateVector i)) := fun j => kf3hp_spatial P M hM τ i j
  have hN : ∀ j : Fin 3,
      Integrable (fun y : Space => UnforcedLeray.Short.IIIa.heatG θ y *
        UnforcedLeray.PressureAnalysis.newtonComponent j
          (fun z : Space => fderiv ℝ (fun x' : Space => cartDiv M (x', τ) j) z
            (UnforcedLeray.coordinateVector i)) (x - y)) ∧
      ∫ y : Space, UnforcedLeray.Short.IIIa.heatG θ y *
          UnforcedLeray.PressureAnalysis.newtonComponent j
            (fun z : Space => fderiv ℝ (fun x' : Space => cartDiv M (x', τ) j) z
              (UnforcedLeray.coordinateVector i)) (x - y) =
        ∫ z : Space, fderiv ℝ (UnforcedLeray.Short.IIIa.heatTail θ) (x - z)
          (UnforcedLeray.coordinateVector j) *
          fderiv ℝ (fun x' : Space => cartDiv M (x', τ) j) z
            (UnforcedLeray.coordinateVector i) :=
    fun j => kf3HeatNewtonComp θ hθ _ (hsp j) x j
  have e1 : (fun y : Space => UnforcedLeray.Short.IIIa.heatG θ y *
        UnforcedLeray.B0226.gradX (lerayPres M) (x - y, τ) i) =
      fun y : Space => ∑ j : Fin 3, UnforcedLeray.Short.IIIa.heatG θ y *
        UnforcedLeray.PressureAnalysis.newtonComponent j
          (fun z : Space => fderiv ℝ (fun x' : Space => cartDiv M (x', τ) j) z
            (UnforcedLeray.coordinateVector i)) (x - y) := by
    funext y
    rw [kf3PresGrad P M hM (x - y) τ i, Finset.mul_sum]
  have hIntL : Integrable (fun y : Space => UnforcedLeray.Short.IIIa.heatG θ y *
      UnforcedLeray.B0226.gradX (lerayPres M) (x - y, τ) i) := by
    rw [e1]
    exact integrable_finsetSum _ (fun j _ => (hN j).1)
  have hEq : ∫ y : Space, UnforcedLeray.Short.IIIa.heatG θ y *
        UnforcedLeray.B0226.gradX (lerayPres M) (x - y, τ) i =
      ∫ z : Space, ∑ j : Fin 3, ∑ k : Fin 3,
        fderiv ℝ (UnforcedLeray.Short.IIIa.part2 (UnforcedLeray.Short.IIIa.heatTail θ) i j) (x - z)
          (UnforcedLeray.coordinateVector k) * M (z, τ) j k := by
    rw [e1, integral_finsetSum _ (fun j _ => (hN j).1)]
    refine (Finset.sum_congr rfl (fun j _ => (hN j).2)).trans ?_
    exact hTI2
  exact ⟨hIntL, hTI1, hEq⟩

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
