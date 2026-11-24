import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.WardE.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.Assembly
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.OldNorm
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L8

/-!
# `Sub/PartIII-b_C_cont_WE`: Decomposition of `SeqData.wardECont` (`PartIII-b:C/cont/WE`)

Source of record: `the November 2 reference manuscript`
(73 pages), lines 4161-4303 (`subsec:ward`), 5196-5260 (`prop:actual-body`), 5684-5685, 5701-5704,
5918-5920.

This file proves the pin-uniqueness identity `WardEContSub.wardOps_snd_snd_ae` for the third
component of `wardOps`, derives operator-norm Lipschitz continuity
`WardEContSub.wardOps_snd_snd_continuousOn_of` on a subset `W ⊆ [a, b] ⊂ (0, 1/4)` from
`WardELipschitzL` and `WardBgBoundL`, and combines this with `seq_wardBgBoundL`
(`ReturnInst/Ward/Bg/Assembly.lean`) to reduce `SeqData.wardECont` (`PartIII-b:C/cont/WE`) via
`wardECont_of_leaves` to:
* `WardDXSubYoungL2` (`PartIII-b:C/cont/WE/1`),
* `WardD2XSubYoungL2` (`PartIII-b:C/cont/WE/2`),
* `WardDYSubYoungL2` (`PartIII-b:C/cont/WE/3`),
* `WardDXSubYoungSup` (`PartIII-b:C/cont/WE/4`),
together with the open background tasks `BgYoungW2` (`PartIII-b:C/ward/12`) and `BgPresY2B`
(`PartIII-b:C/ward/13`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

namespace WardEContSub

/-! ## 1. Pin uniqueness for the third component of `wardOps` -/

/-- When a Ward triple exists at `(L, μ)`, the third component `(wardOps Pl K L μ).2.2 T` agrees
`srcMeasure (cOf L.ν)`-a.e. with `wardECoef ... T` (taking the canonical `Lp` representatives of
the two gain components of `χ_o T`). -/
theorem wardOps_snd_snd_ae (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) {μ : ℝ}
    (hpin : ∃ t : (LStr Pl K L →L[ℝ] LVel Pl L) × (LStr Pl K L →L[ℝ] LVel Pl L) ×
        (LStr Pl K L →L[ℝ] LSrc L),
      IsWardTriple t.1 t.2.1 t.2.2 L.ε μ K.hχo K.χy L.U L.pres)
    (T : LStr Pl K L) :
    ((wardOps Pl K L μ).2.2 T : Chart → Merid) =ᵐ[srcMeasure (cOf L.ν)]
      wardECoef (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.hχo K.χy L.U L.pres T := by
  have h := Classical.epsilon_spec hpin
  exact (h T _ _ Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl).2.2

/-! ## 2. Operator-norm Lipschitz continuity of `μ ↦ (wardOps Pl K L μ).2.2` -/

/-- Operator-norm continuity of `μ ↦ (wardOps Pl K L μ).2.2` on a subset `W ⊆ [a, b] ⊂ (0, 1/4)`
where the Ward pin holds, from `WardELipschitzL` and `WardBgBoundL`. -/
theorem wardOps_snd_snd_continuousOn_of (hLip : WardELipschitzL)
    (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)
    (hC0 : 0 < K.C0) (hmZ : 0 ≤ K.mZ) (hχy : IsYoungCutoff K.χy)
    {a b M : ℝ} (ha : 0 < a) (hb : b < 1 / 4)
    (hBg : WardBgBoundL L.ε⁻¹ L.ν (cOf L.ν) L.U L.pres M)
    (W : Set ℝ) (hW : W ⊆ Icc a b)
    (hpin : ∀ μ ∈ W, ∃ t : (LStr Pl K L →L[ℝ] LVel Pl L) × (LStr Pl K L →L[ℝ] LVel Pl L) ×
        (LStr Pl K L →L[ℝ] LSrc L),
      IsWardTriple t.1 t.2.1 t.2.2 L.ε μ K.hχo K.χy L.U L.pres) :
    ContinuousOn (fun μ => (wardOps Pl K L μ).2.2) W := by
  intro μ0 hμ0
  have hν : 0 < L.ν := L.ν_pos
  have hR : 0 < L.ε⁻¹ := inv_pos.2 L.ε_pos
  have hc : 0 < cOf L.ν := cOf_pos hν
  have hρ : 0 < L.ρb Pl K := wo_rhoB_pos Pl K L hC0
  have hcmp : WardOldNormLe := wardOldNormLe_of gainMeasureLower
  have hold : ∀ T : LStr Pl K L,
      IsOldL2 (cOf L.ν) L.ν
        (strSum (chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo T)) :=
    fun T => wo_isOldL2_rep hcmp hρ hmZ hν K.hχo T
  obtain ⟨C, hC⟩ := hLip a b L.ν L.ε⁻¹ (cOf L.ν) M K.χy L.U L.pres ha hb hχy hν hR hc hBg
  obtain ⟨C', hC'⟩ := hcmp (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν hρ hmZ hν K.χo K.hχo
  set Lc : ℝ := max C 0 * max C' 0 with hLc
  have hLc0 : 0 ≤ Lc := by positivity
  have hbound : ∀ μ ∈ W,
      ‖(wardOps Pl K L μ).2.2 - (wardOps Pl K L μ0).2.2‖ ≤ Lc * |μ - μ0| := by
    intro μ hμ
    refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hLc0 (abs_nonneg _)) fun T => ?_
    have hae1 := wardOps_snd_snd_ae Pl K L (hpin μ hμ) T
    have hae0 := wardOps_snd_snd_ae Pl K L (hpin μ0 hμ0) T
    have hsub := Lp.coeFn_sub ((wardOps Pl K L μ).2.2 T) ((wardOps Pl K L μ0).2.2 T)
    have hae : (((wardOps Pl K L μ).2.2 - (wardOps Pl K L μ0).2.2) T : Chart → Merid)
        =ᵐ[srcMeasure (cOf L.ν)]
          wardECoef (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.hχo K.χy L.U L.pres T -
            wardECoef (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ0 K.hχo K.χy L.U L.pres T := by
      filter_upwards [hsub, hae1, hae0] with p hp hp1 hp0
      change (((wardOps Pl K L μ).2.2 T - (wardOps Pl K L μ0).2.2 T : LSrc L) : Chart → Merid) p = _
      rw [hp, Pi.sub_apply, hp1, hp0, Pi.sub_apply]
    rw [Lp.norm_def, eLpNorm_congr_ae hae]
    have h1 := hC μ (hW hμ) μ0 (hW hμ0) _ (hold T)
    have h2 := hC' T
    have hle : eLpNorm
          (wardECoef (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.hχo K.χy L.U L.pres T -
            wardECoef (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ0 K.hχo K.χy L.U L.pres T) 2
          (srcMeasure (cOf L.ν)) ≤
        ENNReal.ofReal (Lc * |μ - μ0| * ‖T‖) := by
      calc _ ≤ ENNReal.ofReal (C * |μ - μ0|) *
              eLpNorm (strSum (chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo T)) 2
                (ageμ (cOf L.ν) (-1 / 2)) := h1
        _ ≤ ENNReal.ofReal (max C 0 * |μ - μ0|) *
              ENNReal.ofReal (max C' 0 * ‖T‖) := by
            refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_)
              (h2.trans (ENNReal.ofReal_le_ofReal ?_))
            · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)
            · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
        _ = ENNReal.ofReal (Lc * |μ - μ0| * ‖T‖) := by
            rw [← ENNReal.ofReal_mul (mul_nonneg (le_max_right _ _) (abs_nonneg _))]
            congr 1
            rw [hLc]
            ring
    refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top hle).trans ?_
    rw [ENNReal.toReal_ofReal (by positivity)]
  have hT : Tendsto (fun μ : ℝ => Lc * |μ - μ0|) (𝓝[W] μ0) (𝓝 0) := by
    have hc : Continuous (fun μ : ℝ => Lc * |μ - μ0|) :=
      continuous_const.mul (continuous_id.sub continuous_const).abs
    have hz : Lc * |μ0 - μ0| = 0 := by simp
    rw [← hz]
    exact (hc.tendsto μ0).mono_left nhdsWithin_le_nhds
  exact tendsto_iff_norm_sub_tendsto_zero.2
    (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (eventually_nhdsWithin_of_forall hbound) hT)

end WardEContSub

open WardEContSub

/-! ## 3. Sequence-level assembly of `SeqData.wardECont` -/

/-- **`WardECont`** on the concrete sequence from `WardELipschitzL` and the background leaves
`BgYoungW2` (`PartIII-b:C/ward/12`) and `BgPresY2B` (`PartIII-b:C/ward/13`)
(source 4161-4303, 5196-5260, 5684-5685, 5701-5704, 5918-5920). -/
theorem wardECont_of (hLip : WardELipschitzL) (hY : BgYoungW2) (hP : BgPresY2B)
    (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.WardECont := by
  have hbg := seq_wardBgBoundL D hY hP hst.planar.eigenpair hst.omega_ne hst.m0_pos
    hst.m0_ball hst.C0_pos hst.actual
  filter_upwards [hst.pins, mu_eventually_mem D hst.omega_ne hst.sigma_pos hst.sigma_lt, hbg]
    with n hp hn hBg
  obtain ⟨M, hM⟩ := hBg
  have hχy : IsYoungCutoff D.K.χy :=
    ⟨hst.chiY.smooth, hst.chiY.one, hst.chiY.zero, hst.chiY.range⟩
  have ha : 0 < D.σ₀ / 2 := by linarith [hst.sigma_pos]
  have hb : (D.σ₀ + 1 / 4) / 2 < 1 / 4 := by linarith [hst.sigma_lt]
  have hmZ : 0 ≤ D.K.mZ := by linarith [hst.mZ_gt]
  refine wardOps_snd_snd_continuousOn_of hLip D.Pl D.K (D.level n) hst.C0_pos hmZ hχy
    ha hb hM (D.win n) ?_ ?_
  · rintro _ ⟨z, hz, rfl⟩
    exact hn z hz
  · rintro _ ⟨z, hz, rfl⟩
    exact (hp z hz).ward

/-- Conditional assembly of `SeqData.wardECont` (`PartIII-b:C/cont/WE`) from the four `μ`-Lipschitz
young-support leaves (`WardDXSubYoungL2`, `WardD2XSubYoungL2`, `WardDYSubYoungL2`,
`WardDXSubYoungSup`) and the background leaves (`BgYoungW2`, `BgPresY2B`). -/
theorem wardECont_of_leaves (hX : WardDXSubYoungL2) (hX2 : WardD2XSubYoungL2)
    (hDY : WardDYSubYoungL2) (hsup : WardDXSubYoungSup)
    (hY : BgYoungW2) (hP : BgPresY2B)
    (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.WardECont :=
  wardECont_of (wardELipschitzL_of hX hX2 hDY hsup) hY hP D hst

end UnforcedLeray.Short.PartIIIb.Concrete
end
