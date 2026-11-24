import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.Hess.Defs
import UnforcedLeray.Units.B0424.Tests

/-!
# Pull-back of a test: the Hessian (source 1426-1431, 1379)

Task `PartIII-b:C/ward/12/3/1/2/2/1`.  Hessian analogue of `UnforcedLeray.B0424.sLap_lapTest`:
for `φ(θ, x) = θ⁻¹ ψ(τ₀ + log θ, θ^{-1/2} x)` (zero for `θ ≤ 0`), the single second derivative
`∂_{x_i}∂_{x_j} φ` equals `θ⁻¹ (θ^{-1/2})² (∂_i∂_j ψ)(τ₀ + log θ, θ^{-1/2} x)` for `θ > 0`.
The proof is the template's, with one term instead of the sum over `j`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.Short.PartIIa.Rep
open UnforcedLeray.Parabolic (PS IsSTTest sD2)
open UnforcedLeray.Short.PartIIa (WindowCutoff windowField windowLap winSet)

theorem sD2_lapTest {ψ : PS 3 → ℝ} (hψ : IsSTTest ψ) {τ₀ : ℝ}
    (hψw : tsupport ψ ⊆ Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space)) (i j : Fin 3) (X : ℝ × Space) :
    sD2 i j (UnforcedLeray.B0424.lapTest τ₀ ψ : PS 3 → ℝ) X =
      if 0 < X.1 then
        Real.exp (-Real.log X.1) * Real.exp (-Real.log X.1 / 2) ^ 2 *
          sD2 i j ψ (τ₀ + Real.log X.1, Real.exp (-Real.log X.1 / 2) • X.2)
      else 0 := by
  obtain ⟨δ, -, hδ⟩ := UnforcedLeray.B0424.window_margin hψ.2 hψw
  split_ifs with hX
  · -- on `θ > 0`, `φ` agrees near `X` with the smooth expression `lapCmb`
    set c : ℝ → ℝ := fun θ => Real.exp (-Real.log θ)
    set m : ℝ → ℝ := fun θ => τ₀ + Real.log θ
    set b : ℝ → ℝ := fun θ => Real.exp (-Real.log θ / 2)
    have hopen : IsOpen {p : ℝ × Space | 0 < p.1} := isOpen_lt continuous_const continuous_fst
    have hcd : ∀ p : ℝ × Space, 0 < p.1 →
        DifferentiableAt ℝ (UnforcedLeray.B0424.lapCmb τ₀ ψ) p := fun p hp =>
      (UnforcedLeray.B0424.contDiffAt_lapCmb hψ.1 hp).differentiableAt (by simp)
    have hψd : ∀ Y, DifferentiableAt ℝ ψ Y := fun Y => (hψ.1.differentiable (by simp)) Y
    have hsDψ : ∀ k : Fin 3, ContDiff ℝ ∞ (UnforcedLeray.Parabolic.sD k ψ) := fun k =>
      UnforcedLeray.B0424.contDiff_sD hψ.1 k
    -- first derivative near `X`
    have h1 : ∀ k : Fin 3, UnforcedLeray.Parabolic.sD k (UnforcedLeray.B0424.lapTest τ₀ ψ : PS 3 → ℝ)
        =ᶠ[𝓝 X] UnforcedLeray.B0424.cmb (fun θ => c θ * b θ) m b (UnforcedLeray.Parabolic.sD k ψ) := by
      intro k
      have hev := (UnforcedLeray.B0424.lapTest_eq_lapCmb (τ₀ := τ₀) (ψ := ψ) hX).fderiv (𝕜 := ℝ)
      filter_upwards [hev, hopen.mem_nhds hX] with p hp hp0
      show fderiv ℝ (UnforcedLeray.B0424.lapTest τ₀ ψ) p ((0 : ℝ), coordinateVector k) = _
      rw [hp]
      have := UnforcedLeray.B0424.fderiv_cmb_space (c := c) (m := m) (b := b) (Ψ := ψ)
        (hcd p hp0) (hψd _) (coordinateVector k)
      rw [UnforcedLeray.B0424.lapCmb, this]
      simp only [UnforcedLeray.B0424.cmb]
      rw [← mul_assoc]
      rfl
    have hcb : ∀ k : Fin 3, DifferentiableAt ℝ
        (UnforcedLeray.B0424.cmb (fun θ => c θ * b θ) m b (UnforcedLeray.Parabolic.sD k ψ)) X := by
      intro k
      have hlog : ContDiffAt ℝ ∞ (fun p : ℝ × Space => Real.log p.1) X :=
        (Real.contDiffAt_log.2 hX.ne').comp X contDiffAt_fst
      have hca : ContDiffAt ℝ ∞
          (UnforcedLeray.B0424.cmb (fun θ => c θ * b θ) m b (UnforcedLeray.Parabolic.sD k ψ)) X := by
        unfold UnforcedLeray.B0424.cmb
        refine ((Real.contDiff_exp.contDiffAt.comp X hlog.neg).mul
          (Real.contDiff_exp.contDiffAt.comp X (hlog.neg.div_const 2))).mul
          ((hsDψ k).contDiffAt.comp X ?_)
        exact (contDiffAt_const.add hlog).prodMk
          ((Real.contDiff_exp.contDiffAt.comp X (hlog.neg.div_const 2)).smul contDiffAt_snd)
      exact hca.differentiableAt (by simp)
    show fderiv ℝ (UnforcedLeray.Parabolic.sD j (UnforcedLeray.B0424.lapTest τ₀ ψ : PS 3 → ℝ)) X
      ((0 : ℝ), coordinateVector i) = _
    rw [(h1 j).fderiv_eq,
      UnforcedLeray.B0424.fderiv_cmb_space (hcb j) (((hsDψ j).differentiable (by simp)) _)]
    simp only [c, b, m]
    rw [show sD2 i j ψ (τ₀ + Real.log X.1, Real.exp (-Real.log X.1 / 2) • X.2) =
      fderiv ℝ (UnforcedLeray.Parabolic.sD j ψ) (τ₀ + Real.log X.1, Real.exp (-Real.log X.1 / 2) • X.2)
        ((0 : ℝ), coordinateVector i) from rfl]
    ring
  · have hz := UnforcedLeray.B0424.lapTest_eventually_zero (τ₀ := τ₀) (ψ := ψ) hδ (not_lt.1 hX)
    have h1 : UnforcedLeray.Parabolic.sD j (UnforcedLeray.B0424.lapTest τ₀ ψ : PS 3 → ℝ)
        =ᶠ[𝓝 X] fun _ => (0 : ℝ) := by
      filter_upwards [hz.fderiv (𝕜 := ℝ)] with p hp
      show fderiv ℝ (UnforcedLeray.B0424.lapTest τ₀ ψ) p ((0 : ℝ), coordinateVector j) = 0
      rw [hp]; simp
    show fderiv ℝ (UnforcedLeray.Parabolic.sD j (UnforcedLeray.B0424.lapTest τ₀ ψ : PS 3 → ℝ)) X
      ((0 : ℝ), coordinateVector i) = 0
    rw [h1.fderiv_eq]; simp

end UnforcedLeray.Short.PartIIIb.Concrete
