import UnforcedLeray.Short.PartI.Sub.PartI_C05
import UnforcedLeray.Units.B0087
import UnforcedLeray.Lib.Semigroups.SkewExp

/-!


Source of record: `the November 2 reference manuscript`, lines 1038-1046.

Method. `freeLimitGen lam = imMulOp - lam • 1` with `imMulOp = (-2i) • Ω` skew-adjoint
(`B0087.adjoint_imMulOp`). Since the two summands commute,
`exp(B • freeLimitGen lam) = exp(B • imMulOp) * exp((-(B lam)) • 1)`. The first factor has norm
at most `1` (`Infra.norm_exp_skew_le_one`), the second is the scalar `exp(-(B lam))` times the
identity, of norm `exp(-(B Re lam))`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-- **Target `PartI:C05/5`** (source lines 1038-1046): the inviscid free group
`‖exp(B(T - λ))‖ ≤ exp(-Re λ · B)` for `B ≥ 0`. -/
theorem freeLimitExpBound : FreeLimitExpBound := by
  intro lam B hB
  have h1 : ‖NormedSpace.exp ((B : ℂ) • B0087.imMulOp)‖ ≤ 1 :=
    Infra.norm_exp_skew_le_one B0087.adjoint_imMulOp hB
  have hsplit : (B : ℂ) • freeLimitGen lam =
      (B : ℂ) • B0087.imMulOp + (-((B : ℂ) * lam)) • (1 : B0010.XG →L[ℂ] B0010.XG) := by
    unfold freeLimitGen complementT B0087.imMulOp
    module
  have hcomm : Commute ((B : ℂ) • B0087.imMulOp)
      ((-((B : ℂ) * lam)) • (1 : B0010.XG →L[ℂ] B0010.XG)) :=
    ((Commute.one_right _).smul_left _).smul_right _
  have hexp1 : NormedSpace.exp ((-((B : ℂ) * lam)) • (1 : B0010.XG →L[ℂ] B0010.XG)) =
      (Complex.exp (-((B : ℂ) * lam))) • (1 : B0010.XG →L[ℂ] B0010.XG) := by
    rw [← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one,
      ← NormedSpace.algebraMap_exp_comm, Complex.exp_eq_exp_ℂ]
  have hn2 : ‖NormedSpace.exp ((-((B : ℂ) * lam)) • (1 : B0010.XG →L[ℂ] B0010.XG))‖ ≤
      Real.exp (-(lam.re * B)) := by
    have hid : ‖(1 : B0010.XG →L[ℂ] B0010.XG)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have hre : (-((B : ℂ) * lam)).re = -(lam.re * B) := by
      simp [Complex.mul_re]
      ring
    rw [hexp1, norm_smul, Complex.norm_exp, hre]
    exact mul_le_of_le_one_right (by positivity) hid
  have hrad : (NormedSpace.expSeries ℂ (B0010.XG →L[ℂ] B0010.XG)).radius = ⊤ :=
    NormedSpace.expSeries_radius_eq_top ℂ _
  rw [hsplit, NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ) hcomm
    (by rw [hrad]; exact edist_lt_top _ _) (by rw [hrad]; exact edist_lt_top _ _)]
  calc ‖NormedSpace.exp ((B : ℂ) • B0087.imMulOp) *
        NormedSpace.exp ((-((B : ℂ) * lam)) • (1 : B0010.XG →L[ℂ] B0010.XG))‖
      ≤ ‖NormedSpace.exp ((B : ℂ) • B0087.imMulOp)‖ *
        ‖NormedSpace.exp ((-((B : ℂ) * lam)) • (1 : B0010.XG →L[ℂ] B0010.XG))‖ :=
        norm_mul_le _ _
    _ ≤ 1 * Real.exp (-(lam.re * B)) :=
        mul_le_mul h1 hn2 (norm_nonneg _) zero_le_one
    _ = Real.exp (-(lam.re * B)) := one_mul _

end UnforcedLeray.Short.PartI
