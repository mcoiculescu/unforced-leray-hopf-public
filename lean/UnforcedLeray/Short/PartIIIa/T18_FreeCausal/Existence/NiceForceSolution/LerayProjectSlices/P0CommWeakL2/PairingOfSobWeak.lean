import UnforcedLeray.Short.PartIIIa.Sub.T18_2_4_2_10
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.LerayProjectSlices.TestBridge

/-!
# Part III-a, leaf `PartIII-a:T18/2/4/2/10/3`: `Sob.HasWeakDeriv` gives the pairing identities

Target: `PairingOfSobWeak` (`Sub/T18_2_4_2_10.lean`). Source of record:
`the November 2 reference manuscript`, lines 3442-3465.

Proof: the weak-derivative identity against a `Sob` cylinder test is read off componentwise in
`Vec2`, and the test is transported to the `B0579` class by `testBridge`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- For a cylinder test, the `B0579` classical `j`-derivative is the `Sob` directional derivative. -/
private theorem pd_eq_fderiv_cyl {c : ℝ} {φ : ℝ × ℝ → ℝ}
    (hφ : UnforcedLeray.Sob.IsCylTest c φ) (j : Fin 2) (x : ℝ × ℝ) :
    B0579.pd j φ x = fderiv ℝ φ x (UnforcedLeray.Sob.cylDir j) := by
  have hB := (testBridge c φ).1.mpr hφ
  have hd : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
  have h := (testBridge c φ).2 hB x
  fin_cases j
  · exact h.1.trans (UnforcedLeray.Cyl.partialQ_eq_fderiv hd x)
  · exact h.2.trans (UnforcedLeray.Cyl.partialEta_eq_fderiv hd x)

/-- Coordinates commute with the Bochner integral in `Vec2`. -/
private theorem integral_coord {μ : Measure (ℝ × ℝ)}
    {v : ℝ × ℝ → UnforcedLeray.Cyl.Vec2} (hv : Integrable v μ) (i : Fin 2) :
    (∫ x, v x ∂μ) i = ∫ x, v x i ∂μ := by
  have := (EuclideanSpace.proj i : UnforcedLeray.Cyl.Vec2 →L[ℝ] ℝ).integral_comp_comm hv
  simpa using this.symm

theorem pairingOfSobWeak : PairingOfSobWeak := by
  intro c j F G hw i ψ hψ
  have hψ' : UnforcedLeray.Sob.IsCylTest c ψ := (testBridge c ψ).1.mp hψ
  have hadm : (UnforcedLeray.Sob.cylinder c).Adm ψ := hψ'
  have hI1 := hw.int_left ψ hadm
  have hI2 := hw.int_right ψ hadm
  have hid := hw.identity ψ hadm
  have hc := congrArg (fun v : UnforcedLeray.Cyl.Vec2 => v i) hid
  simp only at hc
  rw [integral_coord hI1 i, PiLp.smul_apply, integral_coord hI2 i] at hc
  rw [UnforcedLeray.Cyl.cylinder_μ_eq, UnforcedLeray.Short.IIIa.cellμ_eq] at hc
  simp only [UnforcedLeray.Sob.iterDirDeriv_singleton, smul_eq_mul, List.length_singleton,
    pow_one, neg_one_mul] at hc
  have e1 : ∫ x in B0579.cell c, F x i * B0579.pd j ψ x
      = ∫ x in B0579.cell c, fderiv ℝ ψ x (UnforcedLeray.Sob.cylDir j) * F x i :=
    integral_congr_ae (ae_of_all _ fun x => by simp only [pd_eq_fderiv_cyl hψ' j]; ring)
  have e2 : ∫ x in B0579.cell c, G x i * ψ x = ∫ x in B0579.cell c, ψ x * G x i :=
    integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)
  rw [e1, e2]
  exact hc

end UnforcedLeray.Short.IIIa
