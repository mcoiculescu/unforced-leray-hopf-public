import UnforcedLeray.Short.PartIIIa.Sub.T18_2_4_2_10
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.LerayProjectSlices.TestBridge

/-!
# Part III-a, leaf `PartIII-a:T18/2/4/2/10/2`: pairing identities give `Sob.HasWeakDeriv`

Target: `SobWeakOfPairing` (`Sub/T18_2_4_2_10.lean`). Source of record:
`the November 2 reference manuscript`, lines 3442-3465.

Proof: the integrability clauses come from `L²(cell)` times a cylinder test
(`integrable_test_smul`), the identity is checked componentwise in `Vec2`, and the displayed
`B0579` pairing is transported to the `Sob` test class by `testBridge`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

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

/-- An `L²(cell)` vector field times a cylinder test is integrable on the cell. -/
private theorem integrable_test_smul {c : ℝ} {φ : ℝ × ℝ → ℝ}
    (hφ : UnforcedLeray.Sob.IsCylTest c φ)
    {g : ℝ × ℝ → UnforcedLeray.Cyl.Vec2}
    (hg : MemLp g 2 (UnforcedLeray.Cyl.cellμ c)) :
    Integrable (fun x => φ x • g x) (UnforcedLeray.Cyl.cellμ c) := by
  have hg' : MemLp g 2 (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
      (1 : UnforcedLeray.Sob.Weight (ℝ × ℝ))) := by
    rw [UnforcedLeray.Sob.wμ_one, UnforcedLeray.Cyl.cylinder_μ_eq]
    exact hg
  have h := UnforcedLeray.Sob.integrable_smul_of_memLp (p := 2)
    (UnforcedLeray.Sob.CompactlyBounded.of_adm (D := UnforcedLeray.Sob.cylinder c) hφ) hg'
  rwa [UnforcedLeray.Cyl.cylinder_μ_eq] at h

theorem sobWeakOfPairing : SobWeakOfPairing := by
  intro c j f g hpair
  have hf : MemLp (f : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) 2 (UnforcedLeray.Cyl.cellμ c) :=
    Lp.memLp f
  have hg : MemLp (g : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) 2 (UnforcedLeray.Cyl.cellμ c) :=
    Lp.memLp g
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · have hφ' : UnforcedLeray.Sob.IsCylTest c φ := hφ
    have h := integrable_test_smul (hφ'.dirDeriv (UnforcedLeray.Sob.cylDir j)) hf
    rw [UnforcedLeray.Cyl.cylinder_μ_eq]
    exact h
  · have hφ' : UnforcedLeray.Sob.IsCylTest c φ := hφ
    rw [UnforcedLeray.Cyl.cylinder_μ_eq]
    exact integrable_test_smul hφ' hg
  · have hφ' : UnforcedLeray.Sob.IsCylTest c φ := hφ
    have h1 : Integrable (fun x => UnforcedLeray.Sob.iterDirDeriv [UnforcedLeray.Sob.cylDir j] φ x
        • (f : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x) ((UnforcedLeray.Sob.cylinder c).μ) := by
      have h := integrable_test_smul (hφ'.dirDeriv (UnforcedLeray.Sob.cylDir j)) hf
      rw [UnforcedLeray.Cyl.cylinder_μ_eq]
      exact h
    have h2 : Integrable (fun x => φ x • (g : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x)
        ((UnforcedLeray.Sob.cylinder c).μ) := by
      rw [UnforcedLeray.Cyl.cylinder_μ_eq]
      exact integrable_test_smul hφ' hg
    have hB : B0579.IsCylTest c φ := (testBridge c φ).1.mpr hφ'
    ext i
    have hp := hpair i φ hB
    rw [← UnforcedLeray.Short.IIIa.cellμ_eq] at hp
    rw [integral_coord h1 i, PiLp.smul_apply, integral_coord h2 i]
    rw [UnforcedLeray.Cyl.cylinder_μ_eq]
    simp only [UnforcedLeray.Sob.iterDirDeriv_singleton, PiLp.smul_apply, smul_eq_mul,
      List.length_singleton, pow_one, neg_one_mul]
    have e1 : ∫ x, fderiv ℝ φ x (UnforcedLeray.Sob.cylDir j) *
        (f : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x i ∂(UnforcedLeray.Cyl.cellμ c)
        = ∫ x, (f : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x i * B0579.pd j φ x
          ∂(UnforcedLeray.Cyl.cellμ c) :=
      integral_congr_ae (ae_of_all _ fun x => by simp only [pd_eq_fderiv_cyl hφ' j]; ring)
    have e2 : ∫ x, φ x * (g : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x i ∂(UnforcedLeray.Cyl.cellμ c)
        = ∫ x, (g : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x i * φ x ∂(UnforcedLeray.Cyl.cellμ c) :=
      integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)
    rw [e1, e2]
    exact hp

end UnforcedLeray.Short.IIIa
