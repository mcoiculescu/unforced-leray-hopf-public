import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_11
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymMu
import UnforcedLeray.Short.PartIIIb.NearInst.Body.Proofs.BodyFormNorm
import UnforcedLeray.Short.PartIIIb.NearInst.Body.Proofs.GainInvContract
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.CompactWindow.Comparison.FlatStress.CellPtChangeAll

/-!
# `ropFreeBodyBound` (`PartIII-b:C/rep/11/1`, source 1351-1362, 1675-1677, 4116-4118)

`R_μ = bodyG R_ε`, `R_ε` the real form of `T_ε = R_ε^vec(μ) P_ε` (`IsBodyTransport`).  Then
`‖R_ε‖ ≤ ‖T_ε‖ ≤ (μ + 1/4)⁻¹ ≤ 4` (`bodyFormNorm_of`, `norm_RepsVec_le`, `P_ε` an orthogonal
projection) for `μ ≥ 0`, and `bodyG` conjugates by isometries and the contraction `g⁻¹`
(`gainLp_symm_norm_le`), so `‖R_μ f‖ ≤ 4 ‖f‖` (`k = 0`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace SeqData

variable (D : SeqData)

theorem rop_norm_le_four (hγ : 0 ≤ gRate D.Pl) (n : ℕ) {z : ℝ}
    (hpin : RegimePins D.Pl D.K (D.level n) (D.mu n z)) (hμ : 0 ≤ D.mu n z)
    (f : LSrc (D.level n)) :
    ‖Rop D.Pl (D.level n) (D.mu n z) f‖ ≤ 4 * ‖f‖ := by
  generalize D.level n = L at *
  generalize D.mu n z = μ at *
  have hspec : NearInst.IsBodyTransport (bodyReps D.Pl L μ)
      (UnforcedLeray.Short.PartIIa.Teps (P := (L.params D.Pl).period) (L.params D.Pl).ν_pos
        (L.params D.Pl).ε_pos (L.params D.Pl).c_pos rfl (μ : ℂ)) :=
    Classical.epsilon_spec hpin.body
  have hc : 0 < cOf L.ν := cOf_pos L.ν_pos
  have h1 := NearInst.Body.bodyFormNorm_of
    (fun c hc => NearInst.Masked.cpcH_eq c hc) (fun c hc => NearInst.Masked.cpcInvH_eq c hc)
    (cOf L.ν) hc _ _ hspec
  have hT : ‖UnforcedLeray.Short.PartIIa.Teps (P := (L.params D.Pl).period) (L.params D.Pl).ν_pos
        (L.params D.Pl).ε_pos (L.params D.Pl).c_pos rfl (μ : ℂ)‖ ≤ 4 := by
    unfold UnforcedLeray.Short.PartIIa.Teps
    have hre : 0 < ((μ : ℂ)).re + 1 / 4 := by simp; linarith
    have a := UnforcedLeray.B0223.norm_RepsVec_le (P := (L.params D.Pl).period) (L.params D.Pl).ν_pos (L.params D.Pl).ε_pos
      (L.params D.Pl).c_pos rfl hre
    have b : ‖UnforcedLeray.Short.PartIIa.PepsC (L.params D.Pl).ε (L.params D.Pl).c‖ ≤ 1 :=
      Submodule.starProjection_norm_le _
    calc _ ≤ _ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ((μ : ℂ).re + 1 / 4)⁻¹ * 1 := mul_le_mul a b (norm_nonneg _) (inv_nonneg.2 hre.le)
      _ ≤ 4 := by
        have : ((μ : ℂ).re + 1 / 4)⁻¹ ≤ 4 := by
          rw [inv_le_comm₀ hre (by norm_num)]; simp; linarith
        linarith
  have key : ∀ g : Hsp (cOf L.ν), ‖bodyReps D.Pl L μ g‖ ≤ 4 * ‖g‖ := fun g =>
    (h1 g).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
  have hg := (NearInst.Body.gainInvContract (cOf L.ν) 0 0 (gRate D.Pl) L.ν L.ν_pos hγ).1
  have e : ‖Rop D.Pl L μ f‖ = ‖(NearInst.gainH (cOf L.ν) (gRate D.Pl) L.ν_pos).symm
      (bodyReps D.Pl L μ (NearInst.srcIso (cOf L.ν) f))‖ :=
    (NearInst.velIso (cOf L.ν) (gRate D.Pl) L.ν).symm.norm_map _
  rw [e]
  calc _ ≤ ‖bodyReps D.Pl L μ (NearInst.srcIso (cOf L.ν) f)‖ := hg _
    _ ≤ 4 * ‖NearInst.srcIso (cOf L.ν) f‖ := key _
    _ = 4 * ‖f‖ := by rw [LinearIsometryEquiv.norm_map]

end SeqData

theorem ropFreeBodyBound (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    D.RopFreeBodyBound := by
  refine ⟨4, 0, ?_⟩
  filter_upwards [hst.pins, mu_eventually_mem D hst.omega_ne hst.sigma_pos hst.sigma_lt]
    with n hp hm z hz f
  have h0 : 0 ≤ D.mu n z := by
    have := (hm z hz).1; linarith [hst.sigma_pos]
  simpa using SeqData.rop_norm_le_four D hst.gamma_pos.le n (hp z hz) h0 f

end UnforcedLeray.Short.PartIIIb.Concrete
