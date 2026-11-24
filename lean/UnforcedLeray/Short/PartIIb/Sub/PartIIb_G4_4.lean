import UnforcedLeray.Short.PartIIb.Sub.G4

/-!
# Part II-b, task `PartII-b:G4/4` (`InletSourceBound`): decomposition

Source of record: `the November 2 reference manuscript`, lines 2370-2383 (display
`short-bg:affine`, second inequality), with the construction of `E_ε` at 2347-2369.

Two true source facts.

* `InletSourcePtw` (the pointwise, unprojected source): the functional
  `Φ ↦ ⟪L_0ᵗΦ + (∇V_0)ᵀΦ - (V_0·∇)Φ, E_i⟫` on solenoidal phase tests is `phasePair Φ F` for a real
  `𝒪`-symmetric `F ∈ Y_{q₀}` (the source `(L_0 + B_{V_0})E_i`, a smooth field supported in
  `s ≤ Σ/ν`, `E_i` smooth, by `FrozenStreamBounds` and the ring-lift calculus), with weak spatial
  gradients `G_j ∈ Y_{q₀}` and `‖F‖ + Σ‖G_j‖ ≤ 𝒫_ν R^{2/p}` (Jacobian `πR²`, `H_p` norms of the
  chart profiles).
* `LerayForceProj` (SP 2383: `𝔓` bounded on `Y_p`, commuting with `∂_j`): a real `𝒪`-symmetric
  `F ∈ Y_{q₀}` has a projection `g ∈ Y` that agrees with `F` on solenoidal phase tests, with
  `‖g‖ ≤ C‖F‖`, and any weak gradient `G_j` of `F` yields a weak gradient `G'_j` of `g`,
  `‖G'_j‖ ≤ C‖G_j‖`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint UnforcedLeray.PhaseSpace
  UnforcedLeray.B0411 UnforcedLeray.B0412

/-- **The unprojected inlet source** (SP 2370-2383): see the file docstring. -/
def InletSourcePtw : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Planar.Profile), 0 < Sig → Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∀ i : Fin 2, ∃ (F : Yq p.period q0E) (G : Fin 3 → Yq p.period q0E),
        F ∈ realSub p.period q0E ∧ F ∈ Osym p.period q0E ∧
        (∀ Φ, IsSolTest p.period Φ →
          phasePair p.period q0E Φ F =
            pairF p.period (fun x => L0T p.ν Φ x + convT p.raw Φ x) (p.Efun i)) ∧
        (∀ j : Fin 3, HasPtwOp p.period (fun Φ x => -(dy j Φ x))
          (fun x => rep F x.1 x.2) (fun x => rep (G j) x.1 x.2)) ∧
        ‖F‖ + ∑ j : Fin 3, ‖G j‖ ≤ C * (p.ν ^ k)⁻¹ * p.R ^ (2 / bgp)

/-- **Leray projection onto the force space `Y`, commuting with spatial gradients** (SP 2383,
`𝔓` bounded on `Y_p`, `p = 11/4`). -/
def LerayForceProj : Prop :=
  ∃ Cl : ℝ, 0 < Cl ∧ ∀ (P : ℝ) [Fact (0 < P)] (F : Yq P q0E),
    F ∈ realSub P q0E → F ∈ Osym P q0E →
      ∃ g : Yq P q0E, g ∈ forceSpace P ∧
        (∀ Φ, IsSolTest P Φ → phasePair P q0E Φ g = phasePair P q0E Φ F) ∧ ‖g‖ ≤ Cl * ‖F‖ ∧
        ∀ G : Fin 3 → Yq P q0E,
          (∀ j : Fin 3, HasPtwOp P (fun Φ x => -(dy j Φ x))
            (fun x => rep F x.1 x.2) (fun x => rep (G j) x.1 x.2)) →
          ∃ G' : Fin 3 → Yq P q0E,
            (∀ j : Fin 3, HasPtwOp P (fun Φ x => -(dy j Φ x))
              (fun x => rep g x.1 x.2) (fun x => rep (G' j) x.1 x.2)) ∧
            ∀ j : Fin 3, ‖G' j‖ ≤ Cl * ‖G j‖

/-- **Conditional assembly**: `InletSourceBound` from the two leaves. -/
theorem inletSourceBound_of (hA : InletSourcePtw) (hB : LerayForceProj) : InletSourceBound := by
  intro Sig lam q hSig hq dm dp hdm
  obtain ⟨C, k, ν₀, hC, hν₀, hP⟩ := hA Sig lam q hSig hq dm dp hdm
  obtain ⟨Cl, hCl, hL⟩ := hB
  refine ⟨Cl * C, k, ν₀, mul_pos hCl hC, hν₀, ?_⟩
  intro p d hreg hν hSig' hmode i
  obtain ⟨F, G, hFr, hFO, hFid, hFg, hFn⟩ := hP p d hreg hν hSig' hmode i
  obtain ⟨g, hgY, hgid, hgn, hG⟩ := hL p.period F hFr hFO
  obtain ⟨G', hG'1, hG'2⟩ := hG G hFg
  refine ⟨⟨g, hgY⟩, G', fun Φ hΦ => ?_, hG'1, ?_⟩
  · exact (hgid Φ hΦ).trans (hFid Φ hΦ)
  · have h1 : ‖(⟨g, hgY⟩ : p.Y)‖ = ‖g‖ := rfl
    have h2 : ∑ j : Fin 3, ‖G' j‖ ≤ ∑ j : Fin 3, Cl * ‖G j‖ :=
      Finset.sum_le_sum fun j _ => hG'2 j
    rw [h1]
    calc ‖g‖ + ∑ j : Fin 3, ‖G' j‖ ≤ Cl * ‖F‖ + Cl * ∑ j : Fin 3, ‖G j‖ := by
          rw [← Finset.mul_sum] at h2; linarith
      _ = Cl * (‖F‖ + ∑ j : Fin 3, ‖G j‖) := by ring
      _ ≤ Cl * (C * (p.ν ^ k)⁻¹ * p.R ^ (2 / bgp)) := mul_le_mul_of_nonneg_left hFn hCl.le
      _ = Cl * C * (p.ν ^ k)⁻¹ * p.R ^ (2 / bgp) := by ring

end UnforcedLeray.Short.IIb
