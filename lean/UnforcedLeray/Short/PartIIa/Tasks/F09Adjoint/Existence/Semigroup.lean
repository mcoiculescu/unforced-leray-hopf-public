import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F09_1
import UnforcedLeray.Units.B0421.Phase
import UnforcedLeray.Units.B0419
import UnforcedLeray.Lib.Semigroups.Adjoint

/-!
# Part II-a, task `PartII-a:F09/1/1`: the adjoint semigroup bound at `r = 2`

Source `the November 2 reference manuscript` lines 1359-1361, 1403-1413, 1426-1440.

The phase semigroup `phaseT 2 ν` on `Y_2` is packaged as an exponentially bounded strongly
continuous semigroup `B0421.phaseSemigroup` (`M = 1`, `ω = -γ_2 = -1/4`). Its Hilbert adjoint
`Infra.ExpSemigroup.adjoint` (Lib/Semigroups/Adjoint.lean, which proves the strong continuity of
the adjoint family) is then `adjT P ν` definitionally, and the four clauses of
`AdjSemigroupBound` are read off from its fields.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- **Semigroup bound, strong continuity, semigroup law** for `S(t)^*` (lines 1405-1406). -/
theorem adjSemigroupBound : AdjSemigroupBound := by
  intro P _ ν hν
  let S : UnforcedLeray.Infra.ExpSemigroup (Yq P 2) :=
    UnforcedLeray.B0421.phaseSemigroup (P := P) (q := 2) ENNReal.ofNat_ne_top hν.le 1 zero_le_one
      (fun r _ => by
        rw [one_mul]
        exact UnforcedLeray.B0421.norm_freeC_two_le ν r)
  refine ⟨fun t ht => ?_, fun f => S.adjoint.T_cont f, ?_, fun s t hs ht' => ?_⟩
  · have h : ‖adjT P ν t‖ ≤ S.adjoint.M * Real.exp (S.adjoint.ω * t) := S.adjoint.T_le t ht
    have hM : S.adjoint.M = 1 := rfl
    have hω : S.adjoint.ω = -(1 / 4 : ℝ) := by
      show -UnforcedLeray.B0418.gammaExp 2 = -(1 / 4 : ℝ)
      rw [UnforcedLeray.B0419.gammaExp_two]
    rw [hM, hω] at h
    have hexp : -(1 / 4 : ℝ) * t = -t / 4 := by ring
    rw [one_mul, hexp] at h
    exact h
  · exact S.adjoint.T_zero
  · show ContinuousLinearMap.adjoint (S.T (s + t)) =
      (ContinuousLinearMap.adjoint (S.T t)).comp (ContinuousLinearMap.adjoint (S.T s))
    rw [S.T_add s t hs ht', ContinuousLinearMap.adjoint_comp]

end UnforcedLeray.Short.PartIIa
