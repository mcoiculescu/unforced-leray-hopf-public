import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_3.Bound.Lift
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_2.B0.Core
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_2.S

/-!
# The six profile operators applied to `√s · b_raw`, in dilation variables
(`PartIII-b:C/rep/8/2/1/3/b`, helper 4)

Source lines 5036-5045, 5460-5465, 1206-1216.  With `b̂ = rawPhi L` (the raw profile in
`z = (σ,(q,η))`):
`Dρ B = e^σ P₁ b̂`, `Dz B = e^σ ∂_η b̂`, `Dρ Dρ B = e^{3σ/2} P₂P₁ b̂`, `Dz Dρ B = e^{3σ/2} ∂_η P₁ b̂`,
`Dρ Dz B = e^{3σ/2} P₂ ∂_η b̂`, `Dz Dz B = e^{3σ/2} ∂_η∂_η b̂`, evaluated at `φ(z)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.RingFrameD2BoundAux

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Axi
open UnforcedLeray.Short.PartIIIb.Concrete.RingFrameD2FormulaAux (contDiffAt_Drho contDiffAt_Dz)

/-- `rawH = -Gop 0 2 0 1 (-1) ψ̃`. -/
theorem rawH_eq_Gop (L : ReturnLevel) (z : Zc) :
    rawH L z = -(Gop 0 2 0 1 (-1) (trainFpsi L) z) := by
  unfold rawH Gop
  simp only [zero_smul, zero_add, one_mul, smul_eq_mul]
  ring

theorem contDiff_rawH (L : ReturnLevel) : ContDiff ℝ ∞ (rawH L) := by
  have h : rawH L = fun z => -(Gop 0 2 0 1 (-1) (trainFpsi L) z) := funext (rawH_eq_Gop L)
  rw [h]
  exact (contDiff_Gop _ _ _ _ _ (trainFpsi_contDiff L)).neg

/-- The meridional correction `h̃ = H e_z`. -/
def hTil (L : ReturnLevel) : Zc → Merid := fun z => rawH L z • rawE1

theorem contDiff_hTil (L : ReturnLevel) : ContDiff ℝ ∞ (hTil L) :=
  (contDiff_rawH L).smul contDiff_const

theorem contDiff_trainFv (L : ReturnLevel) : ContDiff ℝ ∞ (trainFv L) :=
  contDiff_iff_contDiffAt.2 (trainFv_contDiffAt_ring L)

theorem rawPhi_eq (L : ReturnLevel) : rawPhi L = fun z => trainFv L z + L.ε • hTil L z := by
  funext z
  simp [rawPhi, hTil, smul_smul]

theorem contDiff_rawPhi (L : ReturnLevel) : ContDiff ℝ ∞ (rawPhi L) := by
  rw [rawPhi_eq]
  exact (contDiff_trainFv L).add ((contDiff_hTil L).const_smul L.ε)

theorem lift_B (L : ReturnLevel) (z : Zc) :
    bSqrt (bRaw L) (phi z) = wt (1 / 2) z • rawPhi L z := by
  have hp : 0 < (phi z).1 := Real.exp_pos _
  unfold bSqrt
  rw [bRaw_eq_phi L hp]
  simp only [phi, Real.log_exp, wt]
  rw [exp_half_eq]

theorem contDiffAt_B (L : ReturnLevel) (z : Zc) : ContDiffAt ℝ 2 (bSqrt (bRaw L)) (phi z) :=
  (RingChartRawD2Sub.contDiffOn_bSqrt rawProfileSmooth L).contDiffAt
    ((isOpen_Ioi.prod isOpen_univ).mem_nhds (show phi z ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) from
      ⟨Real.exp_pos _, mem_univ _⟩))

theorem diffAt_B (L : ReturnLevel) (z : Zc) : DifferentiableAt ℝ (bSqrt (bRaw L)) (phi z) :=
  (contDiffAt_B L z).differentiableAt (by norm_num)

theorem diffAt_DrhoB (L : ReturnLevel) (z : Zc) :
    DifferentiableAt ℝ (Drho L.ε (bSqrt (bRaw L))) (phi z) :=
  (contDiffAt_Drho L.ε (Real.exp_pos _) (contDiffAt_B L z)).differentiableAt (by norm_num)

theorem diffAt_DzB (L : ReturnLevel) (z : Zc) :
    DifferentiableAt ℝ (Dz (bSqrt (bRaw L))) (phi z) :=
  (contDiffAt_Dz (Real.exp_pos _) (contDiffAt_B L z)).differentiableAt (by norm_num)

theorem lift_B_fun (L : ReturnLevel) :
    (fun z' => bSqrt (bRaw L) (phi z')) = fun z' => wt (1 / 2) z' • rawPhi L z' :=
  funext (lift_B L)

theorem Drho_B (L : ReturnLevel) (z : Zc) :
    Drho L.ε (bSqrt (bRaw L)) (phi z) = wt 1 z • Pm L.ε 1 (rawPhi L) z := by
  rw [lift_Drho _ (diffAt_B L z), lift_B_fun, Pm_wt _ _ _ (contDiff_rawPhi L)]
  simp only [smul_smul, wt_mul]
  norm_num

theorem Dz_B (L : ReturnLevel) (z : Zc) :
    Dz (bSqrt (bRaw L)) (phi z) = wt 1 z • Zo (rawPhi L) z := by
  rw [lift_Dz (diffAt_B L z), lift_B_fun, Zo_wt _ (contDiff_rawPhi L)]
  simp only [smul_smul, wt_mul]
  norm_num

theorem Drho_B_fun (L : ReturnLevel) :
    (fun z' => Drho L.ε (bSqrt (bRaw L)) (phi z')) = fun z' => wt 1 z' • Pm L.ε 1 (rawPhi L) z' :=
  funext (Drho_B L)

theorem Dz_B_fun (L : ReturnLevel) :
    (fun z' => Dz (bSqrt (bRaw L)) (phi z')) = fun z' => wt 1 z' • Zo (rawPhi L) z' :=
  funext (Dz_B L)

theorem DrhoDrho_B (L : ReturnLevel) (z : Zc) :
    Drho L.ε (Drho L.ε (bSqrt (bRaw L))) (phi z) =
      wt (3 / 2) z • Pm L.ε 2 (Pm L.ε 1 (rawPhi L)) z := by
  rw [lift_Drho _ (diffAt_DrhoB L z), Drho_B_fun,
    Pm_wt _ _ _ (contDiff_Pm _ _ (contDiff_rawPhi L))]
  simp only [smul_smul, wt_mul]
  norm_num

theorem DzDrho_B (L : ReturnLevel) (z : Zc) :
    Dz (Drho L.ε (bSqrt (bRaw L))) (phi z) =
      wt (3 / 2) z • Zo (Pm L.ε 1 (rawPhi L)) z := by
  rw [lift_Dz (diffAt_DrhoB L z), Drho_B_fun,
    Zo_wt _ (contDiff_Pm _ _ (contDiff_rawPhi L))]
  simp only [smul_smul, wt_mul]
  norm_num

theorem DrhoDz_B (L : ReturnLevel) (z : Zc) :
    Drho L.ε (Dz (bSqrt (bRaw L))) (phi z) =
      wt (3 / 2) z • Pm L.ε 2 (Zo (rawPhi L)) z := by
  rw [lift_Drho _ (diffAt_DzB L z), Dz_B_fun,
    Pm_wt _ _ _ (contDiff_Zo (contDiff_rawPhi L))]
  simp only [smul_smul, wt_mul]
  norm_num

theorem DzDz_B (L : ReturnLevel) (z : Zc) :
    Dz (Dz (bSqrt (bRaw L))) (phi z) = wt (3 / 2) z • Zo (Zo (rawPhi L)) z := by
  rw [lift_Dz (diffAt_DzB L z), Dz_B_fun, Zo_wt _ (contDiff_Zo (contDiff_rawPhi L))]
  simp only [smul_smul, wt_mul]
  norm_num

end UnforcedLeray.Short.PartIIIb.Concrete.RingFrameD2BoundAux
