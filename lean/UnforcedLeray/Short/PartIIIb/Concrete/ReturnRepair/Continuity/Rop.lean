import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_cont_R

/-!
# The leaf `RopCont`: `R_μ` is norm continuous on the window (source 5701-5704, 1675-1677)

Source of record: `the November 2 reference manuscript` (73 pages).

On the window (`μ > -1/4`, pins existing) `bodyReps μ = bodyForm (T_ε(μ))`
(`bodyReps_eq_bodyForm`: uniqueness of body transports), `μ ↦ T_ε(μ) = R^{vec}(μ)P_ε` is norm
continuous (`teps_continuousOn`, holomorphy of `R^{vec}`), `bodyForm` is a fixed sandwich of
`restrictScalars`, and `bodyG` a fixed sandwich.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short.PartIIIb.NearInst

/-- **`RopCont`** on the concrete sequence (source 5701-5704, 1675-1677, 4139-4146). -/
theorem SeqData.ropCont (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    D.RopCont := by
  filter_upwards [mu_eventually_mem D hst.omega_ne hst.sigma_pos hst.sigma_lt, hst.pins]
    with n hn hp
  set L := D.level n
  have hwin : ∀ μ ∈ D.win n, -(1 / 4 : ℝ) < μ := by
    rintro _ ⟨z, hz, rfl⟩
    have := (hn z hz).1
    linarith [hst.sigma_pos]
  have hpin : ∀ μ ∈ D.win n, RegimePins D.Pl D.K L μ := by
    rintro _ ⟨z, hz, rfl⟩
    exact hp z hz
  have hc := cOf_pos L.ν_pos
  have hT := (teps_continuousOn (L.params D.Pl)).mono (fun μ hμ => hwin μ hμ : D.win n ⊆ Ioi _)
  have hres : Continuous fun X : UnforcedLeray.B0220.HSpace (cOf L.ν) UnforcedLeray.B0223.MeridC
      →L[ℂ] UnforcedLeray.B0220.HSpace (cOf L.ν) UnforcedLeray.B0223.MeridC => X.restrictScalars ℝ :=
    (ContinuousLinearMap.restrictScalarsIsometry ℂ _ _ ℝ ℝ).continuous
  have hF : ContinuousOn (fun μ : ℝ => bodyReps D.Pl L μ) (D.win n) := by
    have h2 : ContinuousOn (fun μ : ℝ => Body.bodyForm (cOf L.ν) (Masked.cellPtH_eq _ hc)
        (ct_cellPtInvH _ hc) (UnforcedLeray.Short.PartIIa.Teps (P := (L.params D.Pl).period)
          (L.params D.Pl).ν_pos (L.params D.Pl).ε_pos (L.params D.Pl).c_pos rfl (μ : ℂ)))
        (D.win n) :=
      continuousOn_const.clm_comp ((hres.comp_continuousOn hT).clm_comp continuousOn_const)
    exact h2.congr fun μ hμ => bodyReps_eq_bodyForm D.Pl L (hwin μ hμ) (hpin μ hμ)
  unfold Rop NearInst.bodyG
  exact continuousOn_const.clm_comp (continuousOn_const.clm_comp (hF.clm_comp continuousOn_const))

end UnforcedLeray.Short.PartIIIb.Concrete
