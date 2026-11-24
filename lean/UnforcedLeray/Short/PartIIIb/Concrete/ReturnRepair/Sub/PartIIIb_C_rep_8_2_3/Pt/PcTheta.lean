import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.PtOrg

/-!
# `PartIII-b:C/rep/8/2/3/2/10`: the theta factorization `PcTheta`

Source of record: `the November 2 reference manuscript` 4963-4968
(`p_j = -a^{-3} e^{-|x_j|^2/(2a)}`, `a = 1 + nu s`). The summed Gaussian pressure is termwise
`-(a^{-3}) e^{-eta^2/(2a)} e^{-(2a)^{-1}(q - n c)^2}`, and the lattice sum of the second factor is
`IIb.tt c 0 ((2a)^{-1}, q)`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cyl (Plane)

/-- **Theta factorization of the summed Gaussian pressure** (source 4963-4968). -/
theorem pcTheta : PcTheta := by
  intro ν c s hν hc hs z
  have ha : 0 < 1 + ν * s := by nlinarith [mul_nonneg hν.le hs]
  have hterm : ∀ n : ℤ,
      UnforcedLeray.Train.isoP ν s (z.1 - n * c, z.2) =
        (-((1 + ν * s) ^ 3)⁻¹ * Real.exp (-z.2 ^ 2 / (2 * (1 + ν * s)))) *
          UnforcedLeray.Short.IIb.ttTerm c 0 n ((2 * (1 + ν * s))⁻¹, z.1) := by
    intro n
    unfold UnforcedLeray.Train.isoP UnforcedLeray.B0146.isoPressure
      UnforcedLeray.Short.IIb.ttTerm
    simp only [UnforcedLeray.B0113.pExp, UnforcedLeray.B0113.gw,
      UnforcedLeray.B0113.heatWidth, UnforcedLeray.GaussianVortex.radiusSq, pow_zero, one_mul]
    rw [← Real.exp_add, inv_pow]
    have key : -((1 + ν * s)⁻¹ * ((z.1 - n * c) ^ 2 + z.2 ^ 2) / 4) +
        -((1 + ν * s)⁻¹ * ((z.1 - n * c) ^ 2 + z.2 ^ 2) / 4) =
        -(2 * (1 + ν * s))⁻¹ * (z.1 - n * c) ^ 2 + -z.2 ^ 2 / (2 * (1 + ν * s)) := by
      field_simp
      ring
    rw [key, Real.exp_add]
    ring
  unfold UnforcedLeray.Train.pc UnforcedLeray.Gaussian.periodize
    UnforcedLeray.Short.IIb.tt
  rw [tsum_congr hterm, tsum_mul_left]

end UnforcedLeray.Short.PartIIIb.Concrete
