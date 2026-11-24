import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_1.Point
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.Lam.MellinCont
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymMu

/-!
# Window constants and the amplitude identity for clauses 2-4 of `FlatLimit`
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `ε_n³ = epsCube` on the phase-locked sequence (source 5936-5940). -/
theorem retEps_cube_eq (D : SeqData) (n : ℕ) :
    retEps D.Pl D.σ₀ n ^ 3 = epsCube D.Pl.eigenvalue.re D.Pl.kappa D.σ₀
      (mellinC D.Pl.eigenvalue D.Pl.strainCoupling (planarJ D.Pl) (D.σ₀ : ℂ))
      (retNu D.Pl D.σ₀ n) := by
  have h := NearInst.retEps_cube_mul D.coeff_ne n
  rw [← signedCoeff_eq_mellinC]
  unfold epsCube
  have he : Real.exp (D.Pl.eigenvalue.re / retNu D.Pl D.σ₀ n) *
      Real.exp (-D.Pl.eigenvalue.re / retNu D.Pl D.σ₀ n) = 1 := by
    rw [← Real.exp_add, ← add_div, add_neg_cancel, zero_div, Real.exp_zero]
  calc retEps D.Pl D.σ₀ n ^ 3
      = (retEps D.Pl D.σ₀ n ^ 3 * Real.exp (D.Pl.eigenvalue.re / retNu D.Pl D.σ₀ n)) *
          Real.exp (-D.Pl.eigenvalue.re / retNu D.Pl D.σ₀ n) := by
        rw [mul_assoc, he, mul_one]
    _ = _ := by rw [h]; ring

/-- Continuity of `μ ↦ (1+μ)Γ(μ+5/2) r^{-(μ+5/2)}` for `r > 0`, hence a bound on compacta. -/
theorem gamFac_bound {r : ℝ} (hr : 0 < r) {lo hi : ℝ} (hlo : 0 < lo) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ μ ∈ Icc lo hi, (1 + μ) * gamFac μ r ≤ Cg := by
  have hc : ContinuousOn (fun μ : ℝ => (1 + μ) * gamFac μ r) (Icc lo hi) := by
    intro μ hμ
    have hμ0 : 0 < μ := hlo.trans_le hμ.1
    have h1 : ContinuousAt (fun μ : ℝ => (1 / r) ^ (μ + 5 / 2)) μ :=
      (Real.continuousAt_const_rpow (by positivity)).comp (f := fun μ : ℝ => μ + 5 / 2)
        (continuousAt_id.add continuousAt_const)
    have h2 : ContinuousAt (fun μ : ℝ => Real.Gamma (μ + 5 / 2)) μ := by
      have hd : DifferentiableAt ℝ Real.Gamma (μ + 5 / 2) := by
        apply Real.differentiableAt_Gamma
        intro m
        have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        intro h; linarith
      exact hd.continuousAt.comp (f := fun μ : ℝ => μ + 5 / 2)
        (continuousAt_id.add continuousAt_const)
    exact ((continuousAt_const.add continuousAt_id).mul (h1.mul h2)).continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max C 0, le_max_right _ _, fun μ hμ => ?_⟩
  exact (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hC μ hμ)) |>.trans (le_max_left _ _)

/-- A bound of `‖𝒥(μ)‖` on a compact window in `(-3/2, ∞)`. -/
theorem mellinJ_bound {P : UnforcedLeray.Blueprint.Planar.PlanarData}
    (hP : UnforcedLeray.Blueprint.Planar.IsPlanarReference P) {lo hi : ℝ} (hlo : 0 < lo) :
    ∃ Cj : ℝ, 0 ≤ Cj ∧ ∀ μ ∈ Icc lo hi, ‖P.mellinJ μ‖ ≤ Cj := by
  have hc : ContinuousOn P.mellinJ (Icc lo hi) := fun μ hμ =>
    (planar_continuousAt_mellinJ hP (by linarith [hμ.1])).continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  exact ⟨max C 0, le_max_right _ _, fun μ hμ => (hC μ hμ).trans (le_max_left _ _)⟩

end UnforcedLeray.Short.PartIIIb.Concrete
