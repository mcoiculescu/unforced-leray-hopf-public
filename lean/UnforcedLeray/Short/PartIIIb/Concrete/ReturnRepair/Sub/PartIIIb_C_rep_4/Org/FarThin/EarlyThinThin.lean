import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThin.LateThinThin.Box
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThin.LateThinThin.Kernel
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThin.EarlyThinRepOrg
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepThinOrg.Props

/-!
# `PartIII-b:C/rep/4/1/org/4`: early source, thin source → thin receiver

Source `the November 2 reference manuscript` 5303-5311 (early-source part
`χ_yF_far(1-χ_o)`: young output `s < 1/ν`, source ages `t < 1.5/ν`), 5318-5319 (early source
`g(t) ≤ e^{3γ/(5ν)}`, output `g(s)^{-1} ≤ 1`), 5323-5333 (table, thin source → thin receiver `ε²`,
common `P_νS^k`, factor `e^{3γ/(5ν)}`), 5342-5355 and 5573-5594 (mass estimate, as for the late
output).

`farEarlyThinThin_of_box`: `FarEarlyThinThin` (`Org/FarThinProps.lean`) from the box leaf
`FarThinThinBox` (`Org/FarThin/LateThinThin/Kernel.lean`, shared with the late-output entry) via
the proved kernel `farThinThinKernel_of` (shared `FarBridge`).  Proved here: the region
`χ_yF_far(1-χ_o)(T₁,0) = χ_yF_far((T-χ_oT)₁,0)`, the commutation `M_Uχ_y = χ_yM_U` on the thin
receiver with `|χ_y| ≤ 1`, `g⁻¹ ≤ 1`, and the source gain
`‖((1-χ_o)T)₁‖_{Z₁} ≤ e^{3γ/(5ν)}‖g⁻¹T₁‖` (`ftk_early_source`).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace EarlyThinThin

/-- **The early-source output on the thin receiver at one level** (source 5303-5308, 5318-5319):
the gained thin receiver of `M_Uχ_yF_far(1-χ_o)(T₁,0)` is at most the ungained thin receiver of
`M_UF_far((T-χ_oT)₁,0)`. -/
theorem early_level (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (hχ : IsStreamCutoff K.χy) (hγ : 0 ≤ gRate Pl)
    (hM : ∀ v : LVel Pl L,
      ((multOp Pl K L (youngMul hχ v)).fst : Chart → Ten3) =ᵐ[gainZ1Measure
          (cOf L.ν) K.mZ (gRate Pl) L.ν]
        (fun p => cutFun K.χy L.ν p • ((multOp Pl K L v).fst : Chart → Ten3) p))
    (T : LStr Pl K L) :
    ENNReal.ofReal ‖thinPart (multOp Pl K L (ftEarlyOp Pl K L μ hχ (thinPart T)))‖ ≤
      z1Ung (cOf L.ν) K.mZ
        ((multOp Pl K L ((Sop Pl K L μ - SNop Pl K L μ)
          (thinPart (T - ftOld Pl K L T)))).fst : Chart → Ten3) := by
  set u := (Sop Pl K L μ - SNop Pl K L μ) (thinPart (T - ftOld Pl K L T)) with hu
  have hE : ftEarlyOp Pl K L μ hχ (thinPart T) = youngMul hχ u := by
    rw [hu, map_sub, ← ftk_chiO_thinPart]
    rfl
  rw [hE, lrt_norm_thinPart]
  have c1 := lrt_gainZ1_le_glob zero_le_one
    (fun p => ftk_ginv_le_one hγ L.ν_pos.le p) (multOp Pl K L (youngMul hχ u)).fst
  rw [ENNReal.ofReal_one, one_mul] at c1
  refine c1.trans (lrt_z1Ung_mono ?_)
  have hM' : ∀ᵐ p ∂(z1Measure (cOf L.ν) K.mZ),
      ((multOp Pl K L (youngMul hχ u)).fst : Chart → Ten3) p =
        cutFun K.χy L.ν p • ((multOp Pl K L u).fst : Chart → Ten3) p := by
    rw [← NearInst.ae_gainZ1Measure (cOf L.ν) K.mZ (gRate Pl) L.ν]; exact hM u
  filter_upwards [hM'] with p hp
  rw [hp, norm_smul, Real.norm_eq_abs]
  have hab : |cutFun K.χy L.ν p| ≤ 1 := cutFun_bound_y hχ L.ν p
  calc |cutFun K.χy L.ν p| * ‖((multOp Pl K L u).fst : Chart → Ten3) p‖
      ≤ 1 * ‖((multOp Pl K L u).fst : Chart → Ten3) p‖ :=
        mul_le_mul_of_nonneg_right hab (norm_nonneg _)
    _ = _ := one_mul _

end EarlyThinThin

/-- **`FarEarlyThinThin` from the ungained thin-to-thin far kernel** (source 5303-5311,
5318-5319, 5323-5333, 5342-5355). -/
theorem farEarlyThinThin_of_kernel (Pl : PlanarData) (σ₀ mZ dm dp : ℝ)
    (hK : FarThinThinKernel Pl σ₀ mZ dm dp) : FarEarlyThinThin Pl σ₀ mZ dm dp := by
  obtain ⟨k₀, hk⟩ := hK
  refine ⟨k₀, fun D hPl hσ hmZ hst => ?_⟩
  obtain ⟨C, k, hC, eK⟩ := hk D hPl hσ hmZ hst
  refine ⟨C, k, ?_⟩
  filter_upwards [eK, multYoung dm dp D hst] with n a m
  intro z hz T
  have hε : 0 < (D.level n).ε := (D.level n).ε_pos
  have hν : 0 < (D.level n).ν := (D.level n).ν_pos
  have hγ : 0 ≤ gRate D.Pl := hst.gamma_pos.le
  have c1 := EarlyThinThin.early_level D.Pl D.K (D.level n) (D.mu n z) hst.chiY hγ
    (fun v => (m v).1) T
  have c2 := a z hz (T - ftOld D.Pl D.K (D.level n) T)
  have c3 := ftk_early_source D.Pl D.K (D.level n) hγ T
  set Kc : ℝ := C * (D.level n).ν⁻¹ ^ k * (D.level n).ε ^ (-((k₀ : ℝ) * D.K.b)) *
    (D.level n).ε ^ (2 : ℝ) with hKc
  set E : ℝ := Real.exp (3 * gRate D.Pl / 5 / (D.level n).ν) with hE
  have hK0 : 0 ≤ Kc := by positivity
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have c4 := c1.trans (c2.trans (mul_le_mul' le_rfl c3))
  rw [← ENNReal.ofReal_mul hE0, ← ENNReal.ofReal_mul hK0,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at c4
  calc ‖thinPart (multOp D.Pl D.K (D.level n)
          (ftEarlyOp D.Pl D.K (D.level n) (D.mu n z) hst.chiY (thinPart T)))‖
      ≤ Kc * (E * ‖T.fst‖) := c4
    _ ≤ Kc * (E * ‖T‖) := by
        gcongr
        exact ftk_norm_fst_le T
    _ = C * (D.level n).ν⁻¹ ^ k * (D.level n).ε ^ (-((k₀ : ℝ) * D.K.b)) *
          (D.level n).ε ^ (2 : ℝ) * Real.exp (3 * gRate D.Pl / 5 / (D.level n).ν) * ‖T‖ := by
        rw [hKc, hE]; ring

/-- **`FarEarlyThinThin` from the box leaf** `FarThinThinBox` (source 5303-5311, 5318-5319,
5323-5333, 5342-5355, 5573-5594). -/
theorem farEarlyThinThin_of_box (Pl : PlanarData) (σ₀ mZ dm dp : ℝ)
    (h : FarThinThinBox Pl σ₀ mZ dm dp) : FarEarlyThinThin Pl σ₀ mZ dm dp :=
  farEarlyThinThin_of_kernel Pl σ₀ mZ dm dp (farThinThinKernel_of Pl σ₀ mZ dm dp h)

/-- **`FarEarlyThinThin`** (source 5303-5311, 5318-5319, 5323-5333, 5342-5355, 5573-5594). -/
theorem farEarlyThinThin (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : FarEarlyThinThin Pl σ₀ mZ dm dp :=
  farEarlyThinThin_of_box Pl σ₀ mZ dm dp (farThinThinBox Pl σ₀ mZ dm dp)

end UnforcedLeray.Short.PartIIIb.Concrete
