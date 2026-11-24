import UnforcedLeray.Short.PartIIb.Sub.G4

/-!
# Part II-b, task `PartII-b:G4/5` (`InletSupBound`): decomposition

Source of record: `the November 2 reference manuscript`, lines 2347-2369 (the
inlet `E_ε`) and 2383-2385 ("`‖E_εα‖_{W^{j,∞}} ≤ 𝒫_{ν,j}|α|`").

Two true source facts about a single frozen inlet column `E_i = p.inlet i τ = N_v e_ε`:
smoothness on all of `ℝ³` (including the axis, where `χ = 1` and `E_i` is the lift of the planar
stream `ϱψ_i`; `ring lift` calculus, cf. `RingAxisSmooth`), and the uniform bound on every fixed
Cartesian derivative, `‖D^j E_i(τ, y)‖ ≤ 𝒫_{ν,j}` (chart-derivative bounds for the ring lift as in
`NvFderivBound`, the weights `s^a` being bounded by `(Σ/ν)^a` on `supp χ`, and the stream bounds
`FrozenStreamBounds`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint UnforcedLeray.PhaseSpace
  UnforcedLeray.B0411 UnforcedLeray.B0412

/-- **Smoothness of each frozen inlet slice** (through the axis). -/
def InletContDiff : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Planar.Profile), 0 < Sig → Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∀ (i : Fin 2) (τ : ℝ), ContDiff ℝ ∞ (p.inlet i τ)

/-- **Uniform Cartesian jet bound for a single inlet column.** -/
def InletJetBound : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Planar.Profile), 0 < Sig → Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∀ j : ℕ, ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∀ (i : Fin 2) (τ : ℝ) (y : Space),
        ‖iteratedFDeriv ℝ j (p.inlet i τ) y‖ ≤ C * (p.ν ^ k)⁻¹

/-- **Conditional assembly**: `InletSupBound` from the two leaves. -/
theorem inletSupBound_of (hA : InletContDiff) (hB : InletJetBound) : InletSupBound := by
  intro Sig lam q hSig hq dm dp hdm j
  obtain ⟨C, k, ν₀, hC, hν₀, hJ⟩ := hB Sig lam q hSig hq dm dp hdm j
  obtain ⟨ν₁, hν₁, hS⟩ := hA Sig lam q hSig hq dm dp hdm
  refine ⟨2 * C, k, min ν₀ ν₁, by positivity, lt_min hν₀ hν₁, ?_⟩
  intro p d hreg hν hSig' hmode α τ y
  have hν0 : p.ν ≤ ν₀ := hν.trans (min_le_left _ _)
  have hν1 : p.ν ≤ ν₁ := hν.trans (min_le_right _ _)
  have hsm := hS p d hreg hν1 hSig' hmode
  have hb := hJ p d hreg hν0 hSig' hmode
  have h0 : ContDiff ℝ ∞ (fun z => α 0 • p.inlet 0 τ z) := (hsm 0 τ).const_smul _
  have h1 : ContDiff ℝ ∞ (fun z => α 1 • p.inlet 1 τ z) := (hsm 1 τ).const_smul _
  have hfun : (fun z => ∑ i : Fin 2, α i • p.inlet i τ z) =
      (fun z => α 0 • p.inlet 0 τ z) + (fun z => α 1 • p.inlet 1 τ z) := by
    funext z; simp [Fin.sum_univ_two]
  rw [hfun, iteratedFDeriv_add_apply (h0.contDiffAt.of_le (by exact_mod_cast le_top))
    (h1.contDiffAt.of_le (by exact_mod_cast le_top))]
  have e0 := iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (i := j) (a := α 0)
    (f := p.inlet 0 τ) (x := y) ((hsm 0 τ).contDiffAt.of_le (by exact_mod_cast le_top))
  have e1 := iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (i := j) (a := α 1)
    (f := p.inlet 1 τ) (x := y) ((hsm 1 τ).contDiffAt.of_le (by exact_mod_cast le_top))
  change ‖iteratedFDeriv ℝ j (α 0 • p.inlet 0 τ) y + iteratedFDeriv ℝ j (α 1 • p.inlet 1 τ) y‖ ≤ _
  rw [e0, e1]
  have a0 : |α 0| ≤ ‖α‖ := by simpa using PiLp.norm_apply_le α 0
  have a1 : |α 1| ≤ ‖α‖ := by simpa using PiLp.norm_apply_le α 1
  have b0 := hb 0 τ y
  have b1 := hb 1 τ y
  have hN : 0 ≤ C * (p.ν ^ k)⁻¹ := (norm_nonneg _).trans b0
  have n0 : ‖α 0 • iteratedFDeriv ℝ j (p.inlet 0 τ) y‖ ≤ ‖α‖ * (C * (p.ν ^ k)⁻¹) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul a0 b0 (norm_nonneg _) (norm_nonneg _)
  have n1 : ‖α 1 • iteratedFDeriv ℝ j (p.inlet 1 τ) y‖ ≤ ‖α‖ * (C * (p.ν ^ k)⁻¹) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul a1 b1 (norm_nonneg _) (norm_nonneg _)
  calc _ ≤ ‖α 0 • iteratedFDeriv ℝ j (p.inlet 0 τ) y‖ + ‖α 1 • iteratedFDeriv ℝ j (p.inlet 1 τ) y‖ :=
        norm_add_le _ _
    _ ≤ 2 * C * (p.ν ^ k)⁻¹ * ‖α‖ := by nlinarith

end UnforcedLeray.Short.IIb
