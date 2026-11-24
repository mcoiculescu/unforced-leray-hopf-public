import UnforcedLeray.Short.PartIIIa.T20_3_NonzeroVelUniform
import UnforcedLeray.Short.PartIIIa.T20_4_VelocityIsBiotSavart
import UnforcedLeray.Short.PartIIIa.T20_5_VelNormEqLp
import UnforcedLeray.Short.PartIIIa.Sub.T20

/-!
# Part III-a, task `PartIII-a:T20/6`: the real Biot-Savart velocity is uniformly bounded

Assembly. Target: `CTE.RealBiotSavartUniform` (`Sub/T20.lean`, unchanged).
Source of record: `the November 2 reference manuscript`, lines 3236-3240.

Proof. Take `C1` from `nonzeroVelUniform m hm` and set `C := C1 + 2`. The velocity
`u := B0583.velocity c ω` is the Biot-Savart velocity (`velocityIsBiotSavart`), its `velNorm` is
its `L²` norm (`velNorm_eq_lp`), and by definition `velocity = velNe(nonzeroPart) + zeroVelLp`,
so the triangle inequality with `nonzeroVelUniform` and `B0583.norm_zeroVelLp_le` gives
`‖u‖ ≤ C1 ‖ω‖ + 2 ‖ω‖`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa.CTE

theorem realBiotSavartUniform : RealBiotSavartUniform := by
  intro m hm
  obtain ⟨C1, hC1nn, hC1⟩ := nonzeroVelUniform m hm
  refine ⟨C1 + 2, by linarith, ?_⟩
  intro c hfact hc1 ω hcirc
  have hm1 : (1 : ℝ) ≤ m := by linarith
  have hm1' : (1 : ℝ) < m := by linarith
  refine ⟨fun x j => (B0583.velocity c hm1 ω hcirc : B0579.Plane → B0581.Vel) x j,
    velocityIsBiotSavart c m hm1' ω hcirc, ?_⟩
  rw [velNorm_eq_lp c (B0583.velocity c hm1 ω hcirc)]
  apply ENNReal.ofReal_le_ofReal
  have h1 := hC1 c hc1 ω hcirc
  have h2 := B0583.norm_zeroVelLp_le c hm1 ω hcirc
  have hsplit : B0583.velocity c hm1 ω hcirc =
      B0581.velNe c (B0581.nonzeroPart c (B0581.ofX c m (by linarith) ω)) +
        B0583.zeroVelLp c hm1 ω hcirc := rfl
  have htri : ‖B0583.velocity c hm1 ω hcirc‖ ≤
      ‖B0581.velNe c (B0581.nonzeroPart c (B0581.ofX c m (by linarith) ω))‖ +
        ‖B0583.zeroVelLp c hm1 ω hcirc‖ := by
    rw [hsplit]
    exact norm_add_le _ _
  calc ‖B0583.velocity c hm1 ω hcirc‖
      ≤ ‖B0581.velNe c (B0581.nonzeroPart c (B0581.ofX c m (by linarith) ω))‖ +
          ‖B0583.zeroVelLp c hm1 ω hcirc‖ := htri
    _ ≤ C1 * ‖ω‖ + 2 * ‖ω‖ := add_le_add h1 h2
    _ = (C1 + 2) * ‖ω‖ := by ring

end UnforcedLeray.Short.IIIa.CTE

end
