import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThin.LateThinThin.Box
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThin.LateThinThin.Kernel
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepThinOrg.Props

/-!
# `PartIII-b:C/rep/4/1/org/2`: late output, thin source → thin receiver

Source `the November 2 reference manuscript` 5303-5311 (far mask `s < S`,
`t > e^δs`, `S = ε^{-b}`; late-output part `(1-χ_y)F_far`), 5317-5318 (`g(s)^{-1} ≤ e^{-4γ/(9ν)}`
on late output), 5323-5333 (table, thin source → thin receiver `ε²`, common `P_νS^k`, factor
`|N_ν|e^{-4γ/(9ν)}`), 5342-5355 (age-zero thin-to-thin), 5573-5594 (mass estimate), 5118
(`|N_ν| = e^{γ/ν}ν^{-Re κ}`).

`farLateThinThin`: `FarLateThinThin` (`Org/FarThinProps.lean`) from the ungained thin-to-thin
far kernel (`FarThinThinBox` leaf, `LateThinThin/Kernel.lean`, whose completion from box tensors
`farThinThinKernel_of` is proved by the shared `FarBridge`).  Proved here: the late cut and the
output gain on the thin receiver (`M_U(1-χ_y) = (1-χ_y)M_U`, `g(s)^{-1} ≤ e^{-4γ/(9ν)}` on
`s ≥ 0.8/ν`), the source gain `‖T₁‖_{Z₁} ≤ e^{γ/ν}‖g⁻¹T₁‖` and `e^{γ/ν} ≤ ν^{-k}|N_ν|`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace LateThinThin

/-- The late output on the thin receiver at one level, against the ungained `Z₁` norm
(source 5306-5307, 5317-5318). -/
theorem late_level (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (hχ : IsStreamCutoff K.χy) (hγ : 0 ≤ gRate Pl)
    (hM : ∀ v : LVel Pl L,
      ((multOp Pl K L (youngMul hχ v)).fst : Chart → Ten3) =ᵐ[gainZ1Measure
          (cOf L.ν) K.mZ (gRate Pl) L.ν]
        (fun p => cutFun K.χy L.ν p • ((multOp Pl K L v).fst : Chart → Ten3) p))
    (x : LStr Pl K L) :
    ENNReal.ofReal ‖thinPart (multOp Pl K L (ftLateOp Pl K L μ hχ x))‖ ≤
      ENNReal.ofReal (Real.exp (-(4 * gRate Pl / 9) / L.ν)) *
        z1Ung (cOf L.ν) K.mZ
          ((multOp Pl K L ((Sop Pl K L μ - SNop Pl K L μ) x)).fst : Chart → Ten3) := by
  have hlate : ftLateOp Pl K L μ hχ x =
      (Sop Pl K L μ - SNop Pl K L μ) x - youngMul hχ ((Sop Pl K L μ - SNop Pl K L μ) x) := rfl
  obtain ⟨hsupp, hpt⟩ := lrt_lateCut Pl K L hχ hM ((Sop Pl K L μ - SNop Pl K L μ) x)
  rw [lrt_norm_thinPart, hlate]
  refine (lrt_gainZ1_le (Real.exp_pos _).le (fun p hp => lrt_ginv_late hγ L.ν_pos p hp) _
    hsupp).trans ?_
  gcongr
  exact lrt_z1Ung_mono hpt

end LateThinThin

/-- **`FarLateThinThin` from the ungained thin-to-thin far kernel** (source 5306-5307, 5317-5318,
5323-5333, 5342-5355, 5118). -/
theorem farLateThinThin_of_kernel (Pl : PlanarData) (σ₀ mZ dm dp : ℝ)
    (hK : FarThinThinKernel Pl σ₀ mZ dm dp) : FarLateThinThin Pl σ₀ mZ dm dp := by
  obtain ⟨k₀, hk⟩ := hK
  refine ⟨k₀, fun D hPl hσ hmZ hst => ?_⟩
  obtain ⟨C, k, hC, eK⟩ := hk D hPl hσ hmZ hst
  refine ⟨C, k + ⌈-D.Pl.kappa.re⌉₊, ?_⟩
  filter_upwards [eK, multYoung dm dp D hst,
    retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne] with n a m hle z hz T
  have hν : 0 < (D.level n).ν := (D.level n).ν_pos
  have hε : 0 < (D.level n).ε := (D.level n).ε_pos
  have hγ : 0 ≤ gRate D.Pl := hst.gamma_pos.le
  have c1 := LateThinThin.late_level D.Pl D.K (D.level n) (D.mu n z) hst.chiY hγ
    (fun v => (m v).1) (thinPart T)
  have c2 := a z hz T
  have c3 := LateThinRep.ltr_z1Ung_le_gain (c := cOf (D.level n).ν) (mZ := D.K.mZ) hγ hν T.fst
  set Kc : ℝ := C * (D.level n).ν⁻¹ ^ k * (D.level n).ε ^ (-((k₀ : ℝ) * D.K.b)) *
    (D.level n).ε ^ (2 : ℝ) with hKc
  set E0 : ℝ := Real.exp (-(4 * gRate D.Pl / 9) / (D.level n).ν) with hE0
  have hK0 : 0 ≤ Kc := by positivity
  have hE00 : 0 ≤ E0 := (Real.exp_pos _).le
  have c4 := c1.trans (mul_le_mul_of_nonneg_left (c2.trans (mul_le_mul_of_nonneg_left c3
    zero_le)) zero_le)
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul hK0,
    ← ENNReal.ofReal_mul hE00, ENNReal.ofReal_le_ofReal_iff (by positivity)] at c4
  have hfst : ‖T.fst‖ ≤ ‖T‖ := by
    rw [WithLp.prod_norm_eq_of_L1 T]
    exact le_add_of_nonneg_right (norm_nonneg _)
  have hG := LateThinRep.ltr_exp_le_gauge D.Pl (D.level n) hle.1
  have hN0 : 0 ≤ gaugeN D.Pl (D.level n) := norm_nonneg _
  refine c4.trans ?_
  calc E0 * (Kc * (Real.exp (gRate D.Pl / (D.level n).ν) * ‖T.fst‖))
      ≤ E0 * (Kc * (((D.level n).ν⁻¹ ^ (⌈-D.Pl.kappa.re⌉₊) * gaugeN D.Pl (D.level n)) * ‖T‖)) := by
        gcongr
    _ = _ := by rw [hKc, hE0, pow_add]; ring

/-- **`FarLateThinThin` from the box leaf** `FarThinThinBox` (source 5306-5307, 5317-5318,
5323-5333, 5342-5355, 5573-5594): the kernel from box tensors by the shared far bridge, then the
gains. -/
theorem farLateThinThin_of_box (Pl : PlanarData) (σ₀ mZ dm dp : ℝ)
    (h : FarThinThinBox Pl σ₀ mZ dm dp) : FarLateThinThin Pl σ₀ mZ dm dp :=
  farLateThinThin_of_kernel Pl σ₀ mZ dm dp (farThinThinKernel_of Pl σ₀ mZ dm dp h)

/-- **`FarLateThinThin`** (source 5306-5307, 5317-5318, 5323-5333, 5342-5355, 5573-5594). -/
theorem farLateThinThin (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : FarLateThinThin Pl σ₀ mZ dm dp :=
  farLateThinThin_of_box Pl σ₀ mZ dm dp (farThinThinBox Pl σ₀ mZ dm dp)

end UnforcedLeray.Short.PartIIIb.Concrete
