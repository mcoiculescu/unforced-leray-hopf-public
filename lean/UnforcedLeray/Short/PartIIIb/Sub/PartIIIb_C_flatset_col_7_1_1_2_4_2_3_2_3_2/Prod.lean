import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_2_dec
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.GradMember

/-!
# Product test profiles `χ(s) ψ(q,η)` (helper for `pepsC0SliceDivFreeAE`)
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem hj3_hasFDerivAt_prod (χ : ℝ → ℝ) (ψ : ℝ × ℝ → ℝ) (hχ : Differentiable ℝ χ)
    (hψ : Differentiable ℝ ψ) (p : ℝ × (ℝ × ℝ)) :
    HasFDerivAt (fun q : ℝ × (ℝ × ℝ) => χ q.1 * ψ q.2)
      (χ p.1 • ((fderiv ℝ ψ p.2).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
        + ψ p.2 • (deriv χ p.1 • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))) p := by
  have h1 : HasFDerivAt (fun q : ℝ × (ℝ × ℝ) => χ q.1)
      (deriv χ p.1 • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) p :=
    (hχ p.1).hasDerivAt.comp_hasFDerivAt p hasFDerivAt_fst
  have h2 : HasFDerivAt (fun q : ℝ × (ℝ × ℝ) => ψ q.2)
      ((fderiv ℝ ψ p.2).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) p :=
    (hψ p.2).hasFDerivAt.comp p hasFDerivAt_snd
  exact h1.mul h2

theorem hj3_dQ_prod (χ : ℝ → ℝ) (ψ : ℝ × ℝ → ℝ) (hχ : Differentiable ℝ χ)
    (hψ : Differentiable ℝ ψ) (p : ℝ × (ℝ × ℝ)) :
    UnforcedLeray.Axi.dQ (fun q : ℝ × (ℝ × ℝ) => χ q.1 * ψ q.2) p
      = χ p.1 * UnforcedLeray.B0579.pd 0 ψ p.2 := by
  unfold UnforcedLeray.Axi.dQ
  rw [(hj3_hasFDerivAt_prod χ ψ hχ hψ p).fderiv]
  simp [UnforcedLeray.B0579.pd, UnforcedLeray.B0579.dir]

theorem hj3_dEta_prod (χ : ℝ → ℝ) (ψ : ℝ × ℝ → ℝ) (hχ : Differentiable ℝ χ)
    (hψ : Differentiable ℝ ψ) (p : ℝ × (ℝ × ℝ)) :
    UnforcedLeray.Axi.dEta (fun q : ℝ × (ℝ × ℝ) => χ q.1 * ψ q.2) p
      = χ p.1 * UnforcedLeray.B0579.pd 1 ψ p.2 := by
  unfold UnforcedLeray.Axi.dEta
  rw [(hj3_hasFDerivAt_prod χ ψ hχ hψ p).fderiv]
  simp [UnforcedLeray.B0579.pd, UnforcedLeray.B0579.dir]


theorem hj3_band_of_compact {χ : ℝ → ℝ} (hK : HasCompactSupport χ)
    (hpos : tsupport χ ⊆ Ioi 0) : ∃ s0 s1 : ℝ, 0 < s0 ∧ tsupport χ ⊆ Icc s0 s1 := by
  rcases (tsupport χ).eq_empty_or_nonempty with h | hne
  · exact ⟨1, 1, one_pos, by rw [h]; exact empty_subset _⟩
  obtain ⟨m, hm, hmin⟩ := hK.isCompact.exists_isMinOn hne continuousOn_id
  obtain ⟨M, hM⟩ := hK.isCompact.bddAbove
  refine ⟨m, M, hpos hm, fun x hx => ⟨hmin hx, hM hx⟩⟩

theorem hj3_isProfileTest (c : ℝ) {χ : ℝ → ℝ} {ψ : ℝ × ℝ → ℝ} (hχs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχp : tsupport χ ⊆ Ioi 0)
    (hψ : UnforcedLeray.B0579.IsCylTest c ψ) :
    UnforcedLeray.B0226.IsProfileTest c (fun p : ℝ × (ℝ × ℝ) => χ p.1 * ψ p.2) := by
  obtain ⟨s0, s1, hs0, hsub⟩ := hj3_band_of_compact hχc hχp
  obtain ⟨R, hR⟩ := hψ.band
  refine ⟨?_, ?_, ?_⟩
  · exact (hχs.comp contDiff_fst).mul (hψ.smooth.comp contDiff_snd)
  · intro p
    show χ p.1 * ψ (p.2.1 + c, p.2.2) = χ p.1 * ψ (p.2.1, p.2.2)
    rw [hψ.periodic (p.2.1, p.2.2)]
  · refine ⟨s0, s1, R, hs0, fun p hp => ?_⟩
    have hχ0 : χ p.1 ≠ 0 := fun h => hp (by simp [h])
    have hψ0 : ψ p.2 ≠ 0 := fun h => hp (by simp [h])
    refine ⟨hsub (subset_tsupport χ (Function.mem_support.2 hχ0)), ?_⟩
    by_contra hlt
    exact hψ0 (hR p.2 (not_le.1 hlt))

theorem hj3_cgrad_zero_apply (Φ : ℝ × (ℝ × ℝ) → ℝ) (p : ℝ × (ℝ × ℝ)) :
    UnforcedLeray.Short.PartIIa.cgrad 0 Φ p 0 = ((UnforcedLeray.Axi.dQ Φ p : ℝ) : ℂ) := by
  have h := congrFun (UnforcedLeray.B0226.Deps_zero Φ) p
  simp only [UnforcedLeray.Short.PartIIa.cgrad, h]
  simp

theorem hj3_cgrad_one_apply (Φ : ℝ × (ℝ × ℝ) → ℝ) (p : ℝ × (ℝ × ℝ)) :
    UnforcedLeray.Short.PartIIa.cgrad 0 Φ p 1 = ((UnforcedLeray.Axi.dEta Φ p : ℝ) : ℂ) := by
  simp [UnforcedLeray.Short.PartIIa.cgrad]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
