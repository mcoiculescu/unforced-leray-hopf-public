import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.SubKF3
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.KF.KF3.PresSmooth
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.KF.KF3.PresGrad
import UnforcedLeray.Analysis.Pressure.ConvolutionIdentity
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# `kf3SolSlice : KF3SolSlice` (source 117-120, 3586-3589)

For a physical test `φ`, phase `τ`, with `ψ = φ(·, τ)`, `g_j = (div M)_j(·, τ)`, `p = lerayPres M (·, τ)`:
`∫ (g + ∇ₓp) · ∇ₓψ dx = Σ_i ∫ g_i ∂_iψ + Σ_i ∫ ∂_ip ∂_iψ`.
Integration by parts (`ψ` compactly supported) gives `Σ_i ∫ ∂_ip ∂_iψ = -∫ p Δψ`, and the Poisson
identity `newtonComponent_laplacian_test` gives `∫ p Δψ = Σ_j ∫ g_j ∂_jψ`, which cancels.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

/-- Partial derivatives of a smooth function are smooth. -/
theorem kf3s_cd_fderiv_apply {h : Space → ℝ} (hh : ContDiff ℝ ∞ h) (v : Space) :
    ContDiff ℝ ∞ (fun x => fderiv ℝ h x v) :=
  (hh.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem kf3s_cont_fderiv_apply {h : Space → ℝ} (hh : ContDiff ℝ ∞ h) (v : Space) :
    Continuous (fun x => fderiv ℝ h x v) :=
  (kf3s_cd_fderiv_apply hh v).continuous

/-- Continuous times compactly supported is integrable. -/
theorem kf3s_integrable_mul {a b : Space → ℝ} (ha : Continuous a) (hb : Continuous b)
    (hbc : HasCompactSupport b) : Integrable (fun x => a x * b x) := by
  refine Continuous.integrable_of_hasCompactSupport (ha.mul hb) ?_
  exact hbc.mul_left

/-- The gradient component of the Leray pressure is the slice derivative. -/
theorem kf3s_gradX_comp (P : ℝ) (M : Space × ℝ → Matrix (Fin 3) (Fin 3) ℝ) (hM : IsOuterTest P M)
    (x : Space) (τ : ℝ) (i : Fin 3) :
    UnforcedLeray.B0226.gradX (lerayPres M) (x, τ) i =
      fderiv ℝ (fun x' : Space => lerayPres M (x', τ)) x (UnforcedLeray.coordinateVector i) := by
  have hS := kf3PresSmooth P M hM
  have hgrad : UnforcedLeray.B0226.gradX (lerayPres M) (x, τ) i =
      inner ℝ (UnforcedLeray.B0226.gradX (lerayPres M) (x, τ))
        (UnforcedLeray.coordinateVector i) := by
    simp [UnforcedLeray.coordinateVector, EuclideanSpace.inner_single_right]
  rw [hgrad, UnforcedLeray.B0226.inner_gradX, kf3g_slice_fderiv _ hS x τ]

/-- **Leaf: the projected divergence is divergence free, slice by slice** (source 117-120,
3586-3589). -/
theorem kf3SolSlice : KF3SolSlice := by
  intro P M hM φ hφ τ
  obtain ⟨r, hr⟩ := hM.bounded
  obtain ⟨R, hR⟩ := hφ.bounded
  -- the slice `ψ = φ(·, τ)` is a spatial test
  have hψs : UnforcedLeray.IsSpatialTest (fun x : Space => φ (x, τ)) := by
    refine ⟨hφ.smooth.comp (contDiff_id.prodMk contDiff_const), ?_⟩
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Space) R) (fun x hx => ?_)
    have hx' : R < ‖x‖ := by
      have : ¬ (‖x‖ ≤ R) := fun h => hx (mem_closedBall_zero_iff.2 h)
      exact not_le.1 this
    by_contra hne
    have h1 := hR (x, τ) hne
    have h2 : ‖x‖ ≤ R := h1
    linarith
  have hψS : ContDiff ℝ ∞ (fun x : Space => φ (x, τ)) := hψs.smooth
  have hψC : HasCompactSupport (fun x : Space => φ (x, τ)) := hψs.compact
  -- the Leray pressure slice and the divergence slices
  have hpS : ContDiff ℝ ∞ (fun x : Space => lerayPres M (x, τ)) :=
    (kf3PresSmooth P M hM).comp (contDiff_id.prodMk contDiff_const)
  have hgS : ∀ j : Fin 3, ContDiff ℝ ∞ (fun x : Space => cartDiv M (x, τ) j) :=
    fun j => (kf3p_phi_smooth P M hM j).comp (contDiff_const.prodMk contDiff_id)
  have hgC : ∀ j : Fin 3, HasCompactSupport (fun x : Space => cartDiv M (x, τ) j) := by
    intro j
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Space) r) (fun z hz => ?_)
    have hz' : r < ‖z‖ := by
      have : ¬ (‖z‖ ≤ r) := fun h => hz (mem_closedBall_zero_iff.2 h)
      exact not_le.1 this
    exact kf3g_cartDiv_far P M hM r hr z τ hz' j
  -- pointwise integrand
  have hpt : ∀ x : Space,
      inner ℝ (lerayField M (x, τ)) (UnforcedLeray.B0226.gradX φ (x, τ)) =
        ∑ i : Fin 3, (cartDiv M (x, τ) i *
            fderiv ℝ (fun y : Space => φ (y, τ)) x (UnforcedLeray.coordinateVector i) +
          fderiv ℝ (fun y : Space => lerayPres M (y, τ)) x (UnforcedLeray.coordinateVector i) *
            fderiv ℝ (fun y : Space => φ (y, τ)) x (UnforcedLeray.coordinateVector i)) := by
    intro x
    rw [UnforcedLeray.B0226.inner_gradX_eq_sum hφ.smooth]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [lerayField, Pi.add_apply, PiLp.add_apply, UnforcedLeray.spatialTestDerivative]
    rw [kf3s_gradX_comp P M hM x τ i]
    ring
  -- integrability of the two kinds of summands
  have hD_cs : ∀ i : Fin 3, HasCompactSupport
      (fun x : Space => fderiv ℝ (fun y : Space => φ (y, τ)) x (UnforcedLeray.coordinateVector i)) :=
    fun i => hψC.fderiv_apply ℝ _
  have hDD_cs : ∀ i : Fin 3, HasCompactSupport (fun x : Space =>
      fderiv ℝ (fun y : Space => fderiv ℝ (fun z : Space => φ (z, τ)) y
        (UnforcedLeray.coordinateVector i)) x (UnforcedLeray.coordinateVector i)) :=
    fun i => HasCompactSupport.fderiv_apply (𝕜 := ℝ)
      (HasCompactSupport.fderiv_apply (𝕜 := ℝ) hψC (UnforcedLeray.coordinateVector i))
      (UnforcedLeray.coordinateVector i)
  have int_GD : ∀ i : Fin 3, Integrable (fun x : Space => cartDiv M (x, τ) i *
      fderiv ℝ (fun y : Space => φ (y, τ)) x (UnforcedLeray.coordinateVector i)) := fun i =>
    kf3s_integrable_mul (hgS i).continuous
      (kf3s_cont_fderiv_apply hψS (UnforcedLeray.coordinateVector i)) (hD_cs i)
  have int_PD : ∀ i : Fin 3, Integrable (fun x : Space =>
      fderiv ℝ (fun y : Space => lerayPres M (y, τ)) x (UnforcedLeray.coordinateVector i) *
        fderiv ℝ (fun y : Space => φ (y, τ)) x (UnforcedLeray.coordinateVector i)) := fun i =>
    kf3s_integrable_mul (kf3s_cont_fderiv_apply hpS (UnforcedLeray.coordinateVector i))
      (kf3s_cont_fderiv_apply hψS (UnforcedLeray.coordinateVector i)) (hD_cs i)
  have int_pDD : ∀ i : Fin 3, Integrable (fun x : Space =>
      lerayPres M (x, τ) * fderiv ℝ (fun y : Space => fderiv ℝ (fun z : Space => φ (z, τ)) y
        (UnforcedLeray.coordinateVector i)) x (UnforcedLeray.coordinateVector i)) := fun i =>
    kf3s_integrable_mul hpS.continuous
      (kf3s_cont_fderiv_apply (kf3s_cd_fderiv_apply hψS (UnforcedLeray.coordinateVector i))
        (UnforcedLeray.coordinateVector i)) (hDD_cs i)
  have int_pD : ∀ i : Fin 3, Integrable (fun x : Space =>
      lerayPres M (x, τ) * fderiv ℝ (fun y : Space => φ (y, τ)) x (UnforcedLeray.coordinateVector i)) :=
    fun i => kf3s_integrable_mul hpS.continuous
      (kf3s_cont_fderiv_apply hψS (UnforcedLeray.coordinateVector i)) (hD_cs i)
  -- integration by parts in each direction
  have hIBP : ∀ i : Fin 3,
      (∫ x : Space, fderiv ℝ (fun y : Space => lerayPres M (y, τ)) x
          (UnforcedLeray.coordinateVector i) *
        fderiv ℝ (fun y : Space => φ (y, τ)) x (UnforcedLeray.coordinateVector i)) =
      -∫ x : Space, lerayPres M (x, τ) * fderiv ℝ (fun y : Space =>
        fderiv ℝ (fun z : Space => φ (z, τ)) y (UnforcedLeray.coordinateVector i)) x
          (UnforcedLeray.coordinateVector i) := by
    intro i
    have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := volume) (f := fun y : Space => lerayPres M (y, τ))
      (g := fun y : Space => fderiv ℝ (fun z : Space => φ (z, τ)) y
        (UnforcedLeray.coordinateVector i)) (v := UnforcedLeray.coordinateVector i)
      (int_PD i) (int_pDD i) (int_pD i)
      (fun x _ => hpS.differentiable (by simp) x)
      (fun x _ => (kf3s_cd_fderiv_apply hψS (UnforcedLeray.coordinateVector i)).differentiable
        (by simp) x)
    rw [key, neg_neg]
  -- Poisson identity for the pressure
  have hpsum : ∀ x : Space, lerayPres M (x, τ) * Heat.laplacian (fun y : Space => φ (y, τ)) x =
      ∑ j : Fin 3, (UnforcedLeray.PressureAnalysis.newtonComponent j
        (fun z : Space => cartDiv M (z, τ) j) x *
          Heat.laplacian (fun y : Space => φ (y, τ)) x) := by
    intro x
    unfold lerayPres
    rw [Finset.sum_mul]
  have hL3 : ∫ x : Space, lerayPres M (x, τ) * Heat.laplacian (fun y : Space => φ (y, τ)) x =
      ∑ j : Fin 3, ∫ x : Space, cartDiv M (x, τ) j *
        fderiv ℝ (fun y : Space => φ (y, τ)) x (UnforcedLeray.coordinateVector j) := by
    have hf1 : ∀ j : Fin 3, MemLp (fun z : Space => cartDiv M (z, τ) j) 1 volume := fun j =>
      memLp_one_iff_integrable.mpr ((hgS j).continuous.integrable_of_hasCompactSupport (hgC j))
    calc ∫ x : Space, lerayPres M (x, τ) * Heat.laplacian (fun y : Space => φ (y, τ)) x
        = ∫ x : Space, ∑ j : Fin 3, (UnforcedLeray.PressureAnalysis.newtonComponent j
            (fun z : Space => cartDiv M (z, τ) j) x *
              Heat.laplacian (fun y : Space => φ (y, τ)) x) :=
          integral_congr_ae (Eventually.of_forall hpsum)
      _ = ∑ j : Fin 3, ∫ x : Space, UnforcedLeray.PressureAnalysis.newtonComponent j
            (fun z : Space => cartDiv M (z, τ) j) x *
              Heat.laplacian (fun y : Space => φ (y, τ)) x :=
          integral_finset_sum _ (fun j _ =>
            UnforcedLeray.PressureAnalysis.newtonComponent_laplacian_test_integrable j
              (hf1 j) hψs)
      _ = ∑ j : Fin 3, ∫ x : Space, cartDiv M (x, τ) j *
            fderiv ℝ (fun y : Space => φ (y, τ)) x (UnforcedLeray.coordinateVector j) :=
          Finset.sum_congr rfl (fun j _ =>
            (UnforcedLeray.PressureAnalysis.newtonComponent_laplacian_test j (hf1 j) hψs).trans rfl)
  -- the Laplacian sum of the second derivatives
  have hLap : ∑ i : Fin 3, ∫ x : Space, lerayPres M (x, τ) * fderiv ℝ (fun y : Space =>
        fderiv ℝ (fun z : Space => φ (z, τ)) y (UnforcedLeray.coordinateVector i)) x
          (UnforcedLeray.coordinateVector i) =
      ∫ x : Space, lerayPres M (x, τ) * Heat.laplacian (fun y : Space => φ (y, τ)) x := by
    rw [← integral_finset_sum _ (fun i _ => int_pDD i)]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      simp only [Heat.laplacian, Finset.mul_sum]
  have hsumIBP : ∑ i : Fin 3, (∫ x : Space,
      fderiv ℝ (fun y : Space => lerayPres M (y, τ)) x (UnforcedLeray.coordinateVector i) *
        fderiv ℝ (fun y : Space => φ (y, τ)) x (UnforcedLeray.coordinateVector i)) =
      -∑ i : Fin 3, ∫ x : Space, cartDiv M (x, τ) i *
        fderiv ℝ (fun y : Space => φ (y, τ)) x (UnforcedLeray.coordinateVector i) := by
    rw [Finset.sum_congr rfl (fun i _ => hIBP i), Finset.sum_neg_distrib, hLap, hL3]
  -- split the integrand
  have hint : ∫ x : Space, inner ℝ (lerayField M (x, τ)) (UnforcedLeray.B0226.gradX φ (x, τ)) =
      (∑ i : Fin 3, ∫ x : Space, cartDiv M (x, τ) i *
        fderiv ℝ (fun y : Space => φ (y, τ)) x (UnforcedLeray.coordinateVector i)) +
      ∑ i : Fin 3, ∫ x : Space,
        fderiv ℝ (fun y : Space => lerayPres M (y, τ)) x (UnforcedLeray.coordinateVector i) *
          fderiv ℝ (fun y : Space => φ (y, τ)) x (UnforcedLeray.coordinateVector i) := by
    rw [← integral_finset_sum _ (fun i _ => int_GD i),
      ← integral_finset_sum _ (fun i _ => int_PD i),
      ← integral_add (integrable_finset_sum _ (fun i _ => int_GD i))
        (integrable_finset_sum _ (fun i _ => int_PD i))]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      simp only [hpt x, Finset.sum_add_distrib]
  rw [hint, hsumIBP, add_neg_cancel]

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
