import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T12_1_4_2

/-!
# Part II-b, task `PartII-b:T12/1/4/2/7` (`pplTransfer`): transfer of the planar Helmholtz identities
along a.e. equality on every window.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- The windows exhaust the plane when `c > 0`. -/
theorem ppWindow_iUnion_eq_univ {c : ℝ} (hc : 0 < c) : (⋃ M : ℕ, ppWindow c M) = univ := by
  ext z
  simp only [mem_iUnion, mem_univ, iff_true]
  obtain ⟨M, hM⟩ := exists_nat_gt (|z.1| / c)
  have h1 : |z.1| < (M : ℝ) * c := (div_lt_iff₀ hc).1 hM
  have h2 := abs_lt.mp h1
  refine ⟨M, ?_, ?_⟩
  · linarith [h2.1]
  · linarith [h2.2]

theorem pplTransfer : UnforcedLeray.Short.IIb.PPLTransfer := by
  intro c F G Gp hc hwin hG
  have hae : Gp =ᵐ[volume] G := by
    have h : ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)).restrict (⋃ M : ℕ, ppWindow c M), Gp z = G z := by
      rw [ae_restrict_iUnion_iff]
      exact fun M => hwin M
    rwa [ppWindow_iUnion_eq_univ hc, Measure.restrict_univ] at h
  have key1 : ∀ φ : ℝ × ℝ → ℝ,
      (fun z : ℝ × ℝ => Gp z 0 * (fderiv ℝ φ z (1, 0) : ℂ) + Gp z 1 * (fderiv ℝ φ z (0, 1) : ℂ)) =ᵐ[volume]
        (fun z : ℝ × ℝ => G z 0 * (fderiv ℝ φ z (1, 0) : ℂ) + G z 1 * (fderiv ℝ φ z (0, 1) : ℂ)) := by
    intro φ
    filter_upwards [hae] with z hz
    simp only [hz]
  have key2 : ∀ Ψ : ℝ × ℝ → Fin 2 → ℝ,
      (fun z : ℝ × ℝ => ∑ i : Fin 2, (F z i - Gp z i) * (Ψ z i : ℂ)) =ᵐ[volume]
        (fun z : ℝ × ℝ => ∑ i : Fin 2, (F z i - G z i) * (Ψ z i : ℂ)) := by
    intro Ψ
    filter_upwards [hae] with z hz
    simp only [hz]
  obtain ⟨h1, h2⟩ := hG
  refine ⟨fun φ hφ => ?_, fun Ψ hΨ => ?_⟩
  · obtain ⟨i1, i2⟩ := h1 φ hφ
    refine ⟨i1.congr (key1 φ).symm, ?_⟩
    rw [integral_congr_ae (key1 φ)]
    exact i2
  · obtain ⟨i1, i2⟩ := h2 Ψ hΨ
    refine ⟨i1.congr (key2 Ψ).symm, ?_⟩
    rw [integral_congr_ae (key2 Ψ)]
    exact i2

end UnforcedLeray.Short.IIb
