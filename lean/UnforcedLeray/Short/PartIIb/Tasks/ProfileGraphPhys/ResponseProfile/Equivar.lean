import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ResponseProfile.Div
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.DriftNoSwirl

/-!
# `PartII-b:T10/5` helper: rotation equivariance of the free response

Source of record: `the November 2 reference manuscript`, lines 1912-1938, 1356-1420.
If `w` solves the free response problem with datum `f`, then `gAct g w` solves it with datum `gAct g f`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.RespProf

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete UnforcedLeray.B0412
  UnforcedLeray.B0411

theorem gAct_gAct_symm (g : Sp ≃ₗᵢ[ℝ] Sp) (Φ : ℝ × Sp → CVec3) : gAct g (gAct g.symm Φ) = Φ := by
  have := gActInv g.symm Φ
  rwa [LinearIsometryEquiv.symm_symm] at this

theorem pairF_gAct_right (P : ℝ) (g : Sp ≃ₗᵢ[ℝ] Sp) (Φ u : ℝ × Sp → CVec3) :
    pairF P Φ (gAct g u) = pairF P (gAct g.symm Φ) u := by
  calc pairF P Φ (gAct g u) = pairF P (gAct g (gAct g.symm Φ)) (gAct g u) := by
        rw [gAct_gAct_symm]
    _ = pairF P (gAct g.symm Φ) u := gActPair P g _ _

theorem hasPtwOp_gAct {P : ℝ} (g : Sp ≃ₗᵢ[ℝ] Sp)
    (Lt : (ℝ × Sp → CVec3) → ℝ × Sp → CVec3)
    (hcomm : ∀ Φ, IsPhaseTest P Φ → gAct g.symm (Lt Φ) = Lt (gAct g.symm Φ))
    {w a : ℝ × Sp → CVec3} (h : HasPtwOp P Lt w a) :
    HasPtwOp P Lt (gAct g w) (gAct g a) := by
  intro Φ hΦ
  rw [pairF_gAct_right, hcomm Φ hΦ, h _ (gActPhaseTest P g.symm Φ hΦ), pairF_gAct_right]

theorem L0T_gAct (P ν : ℝ) (g : Sp ≃ₗᵢ[ℝ] Sp) (Φ : ℝ × Sp → CVec3) (hΦ : IsPhaseTest P Φ) :
    L0T ν (gAct g Φ) = gAct g (L0T ν Φ) := by
  have h1 := gActDrift P g Φ hΦ
  have h2 := nuLapT_gAct P ν g Φ hΦ
  funext x
  have e1 := congrFun h1 x
  have e2 := congrFun h2 x
  simp only [L0T, Pi.sub_apply, Pi.smul_apply, e1, e2, gAct, map_sub]
  rw [GActLeaf3.smul_gC_leaf3]

theorem isFreeResponse_gAct {ν : ℝ} {μ : ℂ} {r P : ℝ} {f w : ℝ × Sp → CVec3} (hP : 0 < P)
    (h : IsFreeResponse ν μ r P f w) (g : Sp ≃ₗᵢ[ℝ] Sp) :
    IsFreeResponse ν μ r P (gAct g f) (gAct g w) := by
  obtain ⟨hmem, ⟨a, ha, hap⟩, ⟨b, hb, hbp⟩, hsol, heq⟩ := h
  refine ⟨gActInYr P r g w hP hmem, ⟨gAct g a, gActInYr P r g a hP ha, ?_⟩,
    ⟨gAct g b, gActInYr P r g b hP hb, ?_⟩, fun φ hφ => ?_, fun Φ hΦ => ?_⟩
  · refine hasPtwOp_gAct g _ (fun Φ hΦ => ?_) hap
    exact (nuLapT_gAct P ν g.symm Φ hΦ).symm
  · refine hasPtwOp_gAct g _ (fun Φ hΦ => ?_) hbp
    exact (gActDrift P g.symm Φ hΦ).symm
  · rw [pairF_gAct_right]
    have hd : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
    have := gradT_rotS g φ hd
    -- `gAct g.symm (gradT φ) = gradT (rotS g.symm φ)`
    have h2 := gradT_rotS g.symm φ hd
    rw [← h2]
    exact hsol _ (isPhaseTest_rotS P g.symm φ hφ)
  · rw [pairF_gAct_right]
    have hΨ := isSolTest_gAct P g.symm Φ hΦ
    have e : gAct g.symm (fun x => L0T ν Φ x + μ • Φ x) =
        fun x => L0T ν (gAct g.symm Φ) x + μ • gAct g.symm Φ x := by
      funext x
      have := L0T_gAct P ν g.symm Φ hΦ.1
      simp only [gAct, map_add]
      rw [← (UnforcedLeray.B0412.gC g.symm).map_smul]
      have h3 := congrFun this x
      simp only [gAct] at h3
      rw [h3]
    rw [e, heq _ hΨ, ← pairF_gAct_right]

end UnforcedLeray.Short.IIb.RespProf
