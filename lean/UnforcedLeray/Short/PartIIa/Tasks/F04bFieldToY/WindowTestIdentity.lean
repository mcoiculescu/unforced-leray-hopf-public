import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F04_2

/-!


Source of record: `the November 2 reference manuscript`, lines 1470-1480.
Apply `IsWindowLaplacian` to `ψ = η(τ) Φ(τ, y)`. Since `η` depends only on `τ`,
`Δ_y (η Φ) = η Δ_y Φ`; the two double integrals become iterated ones by Fubini, and the
dot product is symmetric.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace

/-- The `y`-derivative of `η(τ) Φ` is `η(τ)` times the `y`-derivative of `Φ`. -/
theorem dy_timeMul_wti {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (η : ℝ → ℝ) (hη : Differentiable ℝ η) (Φ : ℝ × Space → F) (hΦ : Differentiable ℝ Φ)
    (j : Fin 3) :
    dy j (fun q : ℝ × Space => η q.1 • Φ q) = fun p => η p.1 • dy j Φ p := by
  funext p
  have hc : HasFDerivAt (fun q : ℝ × Space => η q.1)
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (deriv η p.1)).comp
        (ContinuousLinearMap.fst ℝ ℝ Space)) p :=
    HasFDerivAt.comp p (hη p.1).hasDerivAt.hasFDerivAt hasFDerivAt_fst
  have hs : fderiv ℝ (fun q : ℝ × Space => η q.1 • Φ q) p = _ :=
    (hc.smul (hΦ p).hasFDerivAt).fderiv
  simp only [dy]
  rw [hs]
  simp

/-- `Δ_y (η(τ) Φ) = η(τ) Δ_y Φ` for a phase test `Φ`. -/
theorem lapT_timeMul_wti (η : ℝ → ℝ) (hη : Differentiable ℝ η) {P : ℝ}
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) :
    lapT (fun q : ℝ × Space => η q.1 • Φ q) = fun p => η p.1 • lapT Φ p := by
  funext p
  simp only [lapT]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hd1 : Differentiable ℝ Φ := hΦ.smooth.differentiable (by simp)
  have hd2 : Differentiable ℝ (dy j Φ) := (hΦ.dy j).smooth.differentiable (by simp)
  rw [dy_timeMul_wti η hη Φ hd1 j, dy_timeMul_wti η hη (dy j Φ) hd2 j]

theorem dotL_comm_wti (a b : CVec3) : dotL a b = dotL b a := by
  simp only [dotL_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem dotL_smul_real_wti (a b : CVec3) (r : ℝ) :
    dotL a (r • b) = (r : ℂ) * dotL a b := by
  simp only [dotL_apply, PiLp.smul_apply, Complex.real_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem windowTestIdentity_proof : UnforcedLeray.Short.PartIIa.WindowTestIdentityF04 := by
  intro P ν τ₀ W Λ hW η hη hηc hηs Φ hΦ
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
  have hl := lapT_timeMul_wti η hηd hΦ
  have hA : ∀ p : ℝ × Space,
      dotL (W p) (ν • lapT (fun q : ℝ × Space => η q.1 • Φ q) p)
        = (η p.1 : ℂ) * dotL (nuLapT ν Φ p) (W p) := by
    intro p
    have hn : nuLapT ν Φ p = ν • lapT Φ p := rfl
    rw [congrFun hl p, smul_comm, dotL_smul_real_wti, hn, dotL_comm_wti (ν • lapT Φ p) (W p)]
  have hvol : (volume : Measure (ℝ × Space)) = (volume : Measure ℝ).prod (volume : Measure Space) :=
    rfl
  have hf1 : ∫ p : ℝ × Space, dotL (W p) (ν • lapT (fun q : ℝ × Space => η q.1 • Φ q) p)
      = ∫ t : ℝ, ∫ y : Space,
          dotL (W (t, y)) (ν • lapT (fun q : ℝ × Space => η q.1 • Φ q) (t, y)) := by
    rw [hvol]
    exact integral_prod _ (by rw [← hvol]; exact h1)
  have hf2 : ∫ p : ℝ × Space, dotL (Λ p) (η p.1 • Φ p)
      = ∫ t : ℝ, ∫ y : Space, dotL (Λ (t, y)) (η (t, y).1 • Φ (t, y)) := by
    rw [hvol]
    exact integral_prod _ (by rw [← hvol]; exact h2)
  have hL_t : ∀ t : ℝ, (η t : ℂ) * ∫ y : Space, dotL (nuLapT ν Φ (t, y)) (W (t, y))
      = ∫ y : Space, dotL (W (t, y)) (ν • lapT (fun q : ℝ × Space => η q.1 • Φ q) (t, y)) := by
    intro t
    simp only [hA]
    rw [integral_const_mul]
  have hR_t : ∀ t : ℝ, ∫ y : Space, dotL (Λ (t, y)) (η (t, y).1 • Φ (t, y))
      = (η t : ℂ) * ∫ y : Space, dotL (Φ (t, y)) (Λ (t, y)) := by
    intro t
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    dsimp only
    rw [dotL_smul_real_wti, dotL_comm_wti (Φ (t, y)) (Λ (t, y))]
  calc (∫ t : ℝ, (η t : ℂ) * ∫ y : Space, dotL (nuLapT ν Φ (t, y)) (W (t, y)))
      = ∫ t : ℝ, ∫ y : Space,
          dotL (W (t, y)) (ν • lapT (fun q : ℝ × Space => η q.1 • Φ q) (t, y)) :=
        integral_congr_ae (ae_of_all _ hL_t)
    _ = ∫ p : ℝ × Space, dotL (W p) (ν • lapT (fun q : ℝ × Space => η q.1 • Φ q) p) := hf1.symm
    _ = ∫ p : ℝ × Space, dotL (Λ p) (η p.1 • Φ p) := h3
    _ = ∫ t : ℝ, ∫ y : Space, dotL (Λ (t, y)) (η (t, y).1 • Φ (t, y)) := hf2
    _ = ∫ t : ℝ, (η t : ℂ) * ∫ y : Space, dotL (Φ (t, y)) (Λ (t, y)) :=
        integral_congr_ae (ae_of_all _ hR_t)

end UnforcedLeray.Short.PartIIa
