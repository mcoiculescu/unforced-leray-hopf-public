import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.Hess.Defs
import UnforcedLeray.Short.PartIIa.Tasks.F04bFieldToY.WindowTestIdentity

/-!
# The window identity against `η(τ)Φ(τ,y)`, Hessian version

Task `PartIII-b:C/ward/12/3/1/2/2/10`.  Proves `WindowTestIdentityHess` (Hessian analogue of
`windowTestIdentity_proof`).  Apply `IsWindowHess` to `ψ = η(τ) Φ(τ, y)`.  Since `η` depends only
on `τ`, `∂_{y_j}∂_{y_k}(η Φ) = η ∂_{y_j}∂_{y_k} Φ`; the two double integrals become iterated
ones by Fubini, and the dot product is symmetric.  Source of record:
`the November 2 reference manuscript`, lines 1437-1441.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff Manifold

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.Short.PartIIa.Rep
open UnforcedLeray.Parabolic (PS IsSTTest sD2)
open UnforcedLeray.Short.PartIIa (WindowCutoff windowField windowLap winSet)
open UnforcedLeray.Short.PartIIa (dy_timeMul_wti dotL_comm_wti dotL_smul_real_wti)

/-- `ν∂_j∂_k (η(τ) Φ) = η(τ) ν∂_j∂_k Φ` for a phase test `Φ` (Hessian analogue of
`lapT_timeMul_wti`). -/
private theorem hsWT_nuHessT_mul (ν : ℝ) (j k : Fin 3) (η : ℝ → ℝ) (hη : Differentiable ℝ η)
    {P : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) :
    nuHessT ν j k (fun q : ℝ × Space => η q.1 • Φ q) = fun p => η p.1 • nuHessT ν j k Φ p := by
  funext p
  have hd1 : Differentiable ℝ Φ := hΦ.smooth.differentiable (by simp)
  have hd2 : Differentiable ℝ (dy k Φ) := (hΦ.dy k).smooth.differentiable (by simp)
  show ν • dy j (dy k (fun q : ℝ × Space => η q.1 • Φ q)) p = η p.1 • (ν • dy j (dy k Φ)) p
  rw [dy_timeMul_wti η hη Φ hd1 k, dy_timeMul_wti η hη (dy k Φ) hd2 j]
  show ν • (η p.1 • dy j (dy k Φ) p) = η p.1 • (ν • dy j (dy k Φ) p)
  exact smul_comm _ _ _

/-- **The window identity against `η(τ)Φ(τ,y)`** (source 1437-1441; Hessian analogue of
`windowTestIdentity_proof`). -/
theorem windowTestIdentityHess : WindowTestIdentityHess := by
  intro P ν τ₀ j k W H hW η hη hηc hηs Φ hΦ
  have hηd : Differentiable ℝ η := hη.differentiable (by simp)
  have hηp : ContDiff ℝ ∞ (fun p : ℝ × Space => η p.1) := hη.comp contDiff_fst
  have hψs : ContDiff ℝ ∞ (fun p : ℝ × Space => η p.1 • Φ p) := hηp.smul hΦ.smooth
  obtain ⟨R, hR⟩ := hΦ.bounded_support
  have hψc : HasCompactSupport (fun p : ℝ × Space => η p.1 • Φ p) := by
    apply HasCompactSupport.intro (hηc.isCompact.prod (isCompact_closedBall (0 : Space) R))
    intro p hp
    by_cases h1 : p.1 ∈ tsupport η
    · have h2 : R < ‖p.2‖ := by
        by_contra h
        apply hp
        exact ⟨h1, by rw [Metric.mem_closedBall, dist_zero_right]; exact not_lt.mp h⟩
      simp [hR p.1 p.2 h2]
    · have h0 : η p.1 = 0 := by
        by_contra hne
        exact h1 (subset_tsupport η hne)
      simp [h0]
  have hψsupp : tsupport (fun p : ℝ × Space => η p.1 • Φ p) ⊆
      Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space) := by
    have hcl : tsupport (fun p : ℝ × Space => η p.1 • Φ p) ⊆ tsupport η ×ˢ (univ : Set Space) := by
      apply closure_minimal
      · intro p hp
        rw [Function.mem_support] at hp
        exact ⟨subset_tsupport η (fun h : η p.1 = 0 => hp (by simp [h])), mem_univ _⟩
      · exact (isClosed_tsupport η).prod isClosed_univ
    exact hcl.trans (Set.prod_mono hηs subset_rfl)
  obtain ⟨h1, h2, h3⟩ := hW (fun p : ℝ × Space => η p.1 • Φ p) hψs hψc hψsupp
  have hl := hsWT_nuHessT_mul ν j k η hηd hΦ
  have hA : ∀ p : ℝ × Space,
      dotL (W p) (nuHessT ν j k (fun q : ℝ × Space => η q.1 • Φ q) p)
        = (η p.1 : ℂ) * dotL (nuHessT ν j k Φ p) (W p) := by
    intro p
    rw [congrFun hl p, dotL_smul_real_wti, dotL_comm_wti (nuHessT ν j k Φ p) (W p)]
  have hvol : (volume : Measure (ℝ × Space)) = (volume : Measure ℝ).prod (volume : Measure Space) :=
    rfl
  have hf1 : ∫ p : ℝ × Space, dotL (W p) (nuHessT ν j k (fun q : ℝ × Space => η q.1 • Φ q) p)
      = ∫ t : ℝ, ∫ y : Space,
          dotL (W (t, y)) (nuHessT ν j k (fun q : ℝ × Space => η q.1 • Φ q) (t, y)) := by
    rw [hvol]
    exact integral_prod _ (by rw [← hvol]; exact h1)
  have hf2 : ∫ p : ℝ × Space, dotL (H p) (η p.1 • Φ p)
      = ∫ t : ℝ, ∫ y : Space, dotL (H (t, y)) (η (t, y).1 • Φ (t, y)) := by
    rw [hvol]
    exact integral_prod _ (by rw [← hvol]; exact h2)
  have hL_t : ∀ t : ℝ, (η t : ℂ) * ∫ y : Space, dotL (nuHessT ν j k Φ (t, y)) (W (t, y))
      = ∫ y : Space,
          dotL (W (t, y)) (nuHessT ν j k (fun q : ℝ × Space => η q.1 • Φ q) (t, y)) := by
    intro t
    simp only [hA]
    rw [integral_const_mul]
  have hR_t : ∀ t : ℝ, ∫ y : Space, dotL (H (t, y)) (η (t, y).1 • Φ (t, y))
      = (η t : ℂ) * ∫ y : Space, dotL (Φ (t, y)) (H (t, y)) := by
    intro t
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    dsimp only
    rw [dotL_smul_real_wti, dotL_comm_wti (Φ (t, y)) (H (t, y))]
  calc (∫ t : ℝ, (η t : ℂ) * ∫ y : Space, dotL (nuHessT ν j k Φ (t, y)) (W (t, y)))
      = ∫ t : ℝ, ∫ y : Space,
          dotL (W (t, y)) (nuHessT ν j k (fun q : ℝ × Space => η q.1 • Φ q) (t, y)) :=
        integral_congr_ae (ae_of_all _ hL_t)
    _ = ∫ p : ℝ × Space, dotL (W p) (nuHessT ν j k (fun q : ℝ × Space => η q.1 • Φ q) p) :=
        hf1.symm
    _ = ∫ p : ℝ × Space, dotL (H p) (η p.1 • Φ p) := h3
    _ = ∫ t : ℝ, ∫ y : Space, dotL (H (t, y)) (η (t, y).1 • Φ (t, y)) := hf2
    _ = ∫ t : ℝ, (η t : ℂ) * ∫ y : Space, dotL (Φ (t, y)) (H (t, y)) :=
        integral_congr_ae (ae_of_all _ hR_t)

end UnforcedLeray.Short.PartIIIb.Concrete
