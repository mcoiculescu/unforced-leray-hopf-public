import UnforcedLeray.Short.PartIIb.Sub.R1
import UnforcedLeray.Lib.Axisymmetric.Cylindrical
import UnforcedLeray.Lib.Axisymmetric.PhysicalChart
import UnforcedLeray.Lib.AxisymmetricB.DSS
import UnforcedLeray.Units.B0185
import UnforcedLeray.Units.B0187

/-!
# Part II-b, task `PartII-b:R1` leaf: the ring residual is axisymmetric without swirl

Target: `UnforcedLeray.Short.IIb.RingResidualAxisymmetric` (`Sub/R1.lean`).

Mathematical content (`StatementsRing.lean`, `physResidualField`, `ringResidual`):
`ringResidual R ν ψ pr τ y = e^{3τ/2} • (A(ϱ(k y), k y₃) • e_r(k y) + B(ϱ(k y), k y₃) • e₃)`
with `k = e^{τ/2}`, `t = e^τ`, where `A, B` are `cylRadialResidual, cylAxialResidual` at time `t`.
Since `ϱ(k y) = k ϱ y`, `(k y)₃ = k y₃` and `e_r(k y) = e_r y` for `k > 0`, the residual is the
meridional lift `Axi.liftMer` of the profile `q ↦ e^{3τ/2} (A(k q₁, k q₂), B(k q₁, k q₂))`,
which is axisymmetric without swirl by `Axi.isAxisymmetricNoSwirl_liftMer`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Short.PartIIa UnforcedLeray.B0185 UnforcedLeray.B0187

theorem ringResidualAxisymmetric_proof : UnforcedLeray.Short.IIb.RingResidualAxisymmetric := by
  unfold RingResidualAxisymmetric
  intro R ν ψ pr τ
  have hk : (0 : ℝ) < Real.exp (τ / 2) := Real.exp_pos _
  have hfun : ringResidual R ν ψ pr τ = Axi.liftMer (fun q : ℝ × ℝ => !₂[
      Real.exp (τ / 2) ^ 3 * cylRadialResidual ν (liftUr R ψ) (liftUz R ψ) (rawPressure R pr)
        (Real.exp (τ / 2) * q.1) (Real.exp (τ / 2) * q.2) (Real.exp τ),
      Real.exp (τ / 2) ^ 3 * cylAxialResidual ν (liftUr R ψ) (liftUz R ψ) (rawPressure R pr)
        (Real.exp (τ / 2) * q.1) (Real.exp (τ / 2) * q.2) (Real.exp τ)]) := by
    funext y
    have h1 : Axi.ϱ (Real.exp (τ / 2) • y) = Real.exp (τ / 2) * Axi.ϱ y := by
      rw [Axi.ϱ_smul, abs_of_pos hk]
    have h2 : (Real.exp (τ / 2) • y) 2 = Real.exp (τ / 2) * y 2 := by
      simp [PiLp.smul_apply, smul_eq_mul]
    have h3 : Axi.eR (Real.exp (τ / 2) • y) = Axi.eR y := Axi.eR_smul hk y
    simp only [ringResidual, physResidualField, Axi.liftMer, Axi.mer, h1, h2, h3]
    simp [smul_add, smul_smul]
  rw [hfun]
  exact Axi.isAxisymmetricNoSwirl_liftMer _

end UnforcedLeray.Short.IIb

end
