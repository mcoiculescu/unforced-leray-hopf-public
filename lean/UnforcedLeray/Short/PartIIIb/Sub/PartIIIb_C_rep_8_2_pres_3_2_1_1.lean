import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_1_org

/-!
# `liftPSim` (`PartIII-b:C/rep/8/2/pres/3/2/1/1`)

Source of record: `the November 2 reference manuscript`
1217 (`p_raw = (R/r)²p`), 2666-2674 (chart `s = R²/ϱ²`, `q = R log(ϱ/R) + Rτ/2`, `η = Rz/ϱ`).

Pure chart algebra.  With `R = ε⁻¹`, `r = ϱ(e^{τ/2}•y) = e^{τ/2}ϱ(y)`, `z = e^{τ/2}y₃`, `t = e^τ`:
the age coordinate `(R/r)² t = R²/ϱ²`, the log-radius `R log(r/R) = Rτ/2 - (R/2)log(R²/ϱ²)`
(the phase of `Axi.phase`), the transverse coordinate `Rz/r = Ry₃/ϱ`, and the prefactor
`e^τ (R/r)² = R²/ϱ²` is the age.  Hence the similarity profile of the raw pressure at `(τ, y)`
is `s · p(s, (q, η))`, the definition of `liftP`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`liftPSim`**: off the axis the lifted pressure is the similarity profile of the raw pressure
`p_raw = (R/r)²p` at `R = ε⁻¹` (source 1217, 2666-2674). -/
theorem liftPSim (L : ReturnLevel) : LiftPSimAt L := by
  unfold LiftPSimAt
  intro τ y hy
  have hR : 0 < L.ε⁻¹ := inv_pos.2 L.ε_pos
  have hR0 : L.ε⁻¹ ≠ 0 := hR.ne'
  have hϱ : 0 < UnforcedLeray.Axi.ϱ y := UnforcedLeray.Axi.ϱ_pos hy
  have hϱ0 : UnforcedLeray.Axi.ϱ y ≠ 0 := hϱ.ne'
  have hE : 0 < Real.exp (τ / 2) := Real.exp_pos _
  have hE0 : Real.exp (τ / 2) ≠ 0 := hE.ne'
  have hτE : Real.exp τ = Real.exp (τ / 2) ^ 2 := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hϱs : UnforcedLeray.Axi.ϱ (Real.exp (τ / 2) • y) =
      Real.exp (τ / 2) * UnforcedLeray.Axi.ϱ y := by
    rw [UnforcedLeray.Axi.ϱ_smul, abs_of_pos hE]
  have hy2 : (Real.exp (τ / 2) • y) 2 = Real.exp (τ / 2) * y 2 := by
    simp [smul_eq_mul]
  have hA : UnforcedLeray.RingLift.ageCoordinate L.ε⁻¹
      (UnforcedLeray.Axi.ϱ (Real.exp (τ / 2) • y)) (Real.exp τ) =
        UnforcedLeray.Axi.age L.ε⁻¹ y := by
    unfold UnforcedLeray.RingLift.ageCoordinate UnforcedLeray.RingLift.radialScale
      UnforcedLeray.Axi.age
    rw [hϱs, hτE]
    field_simp
  have hQ : UnforcedLeray.RingLift.logRadius L.ε⁻¹
      (UnforcedLeray.Axi.ϱ (Real.exp (τ / 2) • y)) =
        UnforcedLeray.Axi.phase L.ε⁻¹ τ y := by
    unfold UnforcedLeray.RingLift.logRadius UnforcedLeray.Axi.phase UnforcedLeray.Axi.age
    rw [hϱs]
    rw [Real.log_div (mul_ne_zero hE0 hϱ0) hR0, Real.log_mul hE0 hϱ0, Real.log_exp,
      Real.log_div (pow_ne_zero 2 hR0) (pow_ne_zero 2 hϱ0), Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hTr : UnforcedLeray.RingLift.transverseCoordinate L.ε⁻¹
      (UnforcedLeray.Axi.ϱ (Real.exp (τ / 2) • y)) ((Real.exp (τ / 2) • y) 2) =
        UnforcedLeray.Axi.trans L.ε⁻¹ y := by
    unfold UnforcedLeray.RingLift.transverseCoordinate UnforcedLeray.RingLift.radialScale
      UnforcedLeray.Axi.trans
    rw [hϱs, hy2]
    field_simp
  have hcoef : Real.exp (τ / 2) ^ 2 *
      (UnforcedLeray.RingLift.radialScale L.ε⁻¹
        (UnforcedLeray.Axi.ϱ (Real.exp (τ / 2) • y))) ^ 2 =
        UnforcedLeray.Axi.age L.ε⁻¹ y := by
    unfold UnforcedLeray.RingLift.radialScale UnforcedLeray.Axi.age
    rw [hϱs]
    field_simp
  unfold UnforcedLeray.Short.PartIIIb.Concrete.liftP
  simp only [UnforcedLeray.B0190.simProfile, UnforcedLeray.B0185.liftPressure,
    UnforcedLeray.B0185.rawPressure, UnforcedLeray.B0187.scaledLift,
    UnforcedLeray.B0184.cylinderLift, UnforcedLeray.B0184.profileChart,
    UnforcedLeray.B0190.trainProfile, UnforcedLeray.Axi.chart, smul_eq_mul]
  rw [hA, hQ, hTr, ← mul_assoc, hcoef]

end UnforcedLeray.Short.PartIIIb.Concrete
