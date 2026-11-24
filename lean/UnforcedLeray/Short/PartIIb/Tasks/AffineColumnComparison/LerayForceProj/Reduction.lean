import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_4_2
import UnforcedLeray.Short.PartIIb.Sub.R1_3
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.LerayOnForce.CTranspose
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.LerayOnForce.SolSliceFixed
import UnforcedLeray.Lib.LerayC.WeakDeriv
import UnforcedLeray.Units.B0414.Orthogonal
import UnforcedLeray.Units.B0428.Slice
import UnforcedLeray.Cons.L2.BackgroundConcrete.PhasePairF

/-!
# `PartII-b:G4/4/2/org`: the phase-space Leray operator `LerayYq` (design)

Source of record: `the November 2 reference manuscript` (SP) lines 119-120
(`R_j = ∂_j(-Δ)^{-1/2}`, the Cartesian Leray projection `𝔓 = ℙ = I + R ⊗ R`), 1307-1308 ("the
Leray projection is bounded on `W^{1,p}` by the Euclidean Riesz-transform theorem") and 2370-2383
(display `short-bg:affine`: `‖A_0E_εα + ℙB_{V_0}E_εα‖_{W^{1,Y_p}}`, which uses that `ℙ`, applied
phase by phase, is bounded on `Y_p` and commutes with `∂_j`).

The operator is the existing slice-wise lift `RieszLp.lerayY P q₀ = (lerayC q₀).compLpL q₀ haar`
(`Lib/LerayC/Phase.lean`) of the complex Leray projection `RieszLp.lerayC`
(`Lib/LerayC/Complex.lean`, `𝔓F = 𝔓(Re F) + i 𝔓(Im F)`); no second copy is defined. Five of the
six clauses of `LerayYq` are already proved:

* `‖lerayY‖ ≤ ‖lerayC q₀‖`, independent of the period (`norm_lerayY_le`);
* values in `Y_σ` (`lerayY_mem_Ysigma`, `Sub/R1_3.lean`);
* `⟪Φ, 𝔓F⟫ = ⟪Φ, F⟫` on solenoidal phase tests (`leraySymm_of lerayCTranspose solSliceFixed`);
* `realSub` and `Osym` preserved (`lerayY_mem_realSub`, `lerayY_mem_Osym`).

The remaining clause is the commutation with weak spatial derivatives. `hasPtwOp_dy_iff` turns the
`HasPtwOp`/`rep` form into `HasPhaseOp (fun Φ => -dy j Φ)` on `Y_{q₀}`. The route is: slice the
phase-space identity into the phases (leaves `AeSliceDy`, `AeForallSliceDy`, the `B0428/Slice.lean`
pattern), pass to real and imaginary parts (`WeakDyCOfComp`), apply the real `L^q` commutation
`RieszLp.lerayLp_hasWeakSpatialDerivative` (`weakDyC_lerayC`, proved here), return to complex
components and vector tests (`CompOfWeakDyC`, `TestDyOfComp`), and reassemble the phase-space
identity (`HasPhaseOpDyOfAe`). `lerayYq_of` proves `LerayYq` from the six leaves, which are
proved in `Slices.lean` and `Parts.lean`, so `LerayYq` holds with no hypothesis:
`lerayYq_of aeSliceDy aeForallSliceDy weakDyCOfComp compOfWeakDyC testDyOfComp hasPhaseOpDyOfAe`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.RieszLp
  UnforcedLeray.B0411 UnforcedLeray.B0412

/-! ## Weak derivatives of complex fields on `ℝ³` -/

/-- **`∂ⱼu = g` in `𝒟'(ℝ³)` for `u, g ∈ L^q(ℝ³;ℂ³)`** (SP 1307-1308, 2381), stated on the real
and imaginary parts (`reV`, `imV`) with the library's `HasWeakSpatialDerivative`. -/
def WeakDyC {q : ℝ≥0∞} [Fact (1 ≤ q)] (j : Fin 3) (u g : Lp CVec3 q (volume : Measure Space)) :
    Prop :=
  HasWeakSpatialDerivative j (reV.compLpL q volume u : SpatialField)
      (reV.compLpL q volume g : SpatialField) ∧
    HasWeakSpatialDerivative j (imV.compLpL q volume u : SpatialField)
      (imV.compLpL q volume g : SpatialField)

/-- **The componentwise form of `∂ⱼu = g`**: `∫ (∂ⱼφ) uᵢ = -∫ φ gᵢ` for every real scalar spatial
test `φ` and every component `i`. -/
def CompDyC {q : ℝ≥0∞} [Fact (1 ≤ q)] (j : Fin 3) (u g : Lp CVec3 q (volume : Measure Space)) :
    Prop :=
  ∀ φ : Space → ℝ, IsSpatialTest φ → ∀ i : Fin 3,
    ∫ y, (spatialTestDerivative j φ y : ℂ) * (u y) i = -∫ y, (φ y : ℂ) * (g y) i

/-- **`𝔓` commutes with `∂ⱼ` on `L^q(ℝ³;ℂ³)`** (SP 1307-1308): the real and imaginary parts of
`lerayC u` are `𝔓(Re u)`, `𝔓(Im u)` (`B0414.reV_lerayC`, `B0414.imV_lerayC`), and the real
`L^q` Leray projection maps weak derivatives to weak derivatives
(`RieszLp.lerayLp_hasWeakSpatialDerivative`). -/
theorem weakDyC_lerayC {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq1 : 1 < q) (hq : q ≠ ⊤) {j : Fin 3}
    {u g : Lp CVec3 q (volume : Measure Space)} (h : WeakDyC j u g) :
    WeakDyC j (lerayC q hq1 hq u) (lerayC q hq1 hq g) := by
  unfold WeakDyC at h ⊢
  refine ⟨?_, ?_⟩
  · rw [B0414.reV_lerayC hq1 hq u, B0414.reV_lerayC hq1 hq g]
    exact lerayLp_hasWeakSpatialDerivative hq1 hq h.1
  · rw [B0414.imV_lerayC hq1 hq u, B0414.imV_lerayC hq1 hq g]
    exact lerayLp_hasWeakSpatialDerivative hq1 hq h.2

/-! ## The leaves -/

/-- **Leaf: one test, almost every phase** (SP 2381, slicing the phase-space identity `∂ⱼF = G`
on `Y_q`; proved: `aeSliceDy`, `Slices.lean`). If `∂ⱼF = G` in distributions on `(ℝ/Pℤ) × ℝ³`,
then for every real spatial test `ψ` and component `i`, `⟪(∂ⱼψ)eᵢ, F(τ)⟫ = -⟪ψeᵢ, G(τ)⟫` for
a.e. phase `τ` (product tests `e_n(τ)ψ(y)eᵢ` and Fourier uniqueness, as
`B0428.ae_slice_pair`). -/
def AeSliceDy : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (q : ℝ≥0∞) [Fact (1 ≤ q)] (j : Fin 3) (F G : Yq P q),
    HasPhaseOp (fun Φ => -dy j Φ) F G →
    ∀ (ψ : Space → ℝ) (hψ : IsSpatialTest ψ) (i : Fin 3),
      ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)),
        innerPair q (B0428.sT q (hψ.derivative j) i) (F τ) =
          -innerPair q (B0428.sT q hψ i) (G τ)

/-- **Leaf: a common null set** (`1 < q`; proved: `aeForallSliceDy`, `Slices.lean`). The a.e.
identities of `AeSliceDy` hold simultaneously for all tests off one null set (a countable family
dense for the pairings, in the second-countable `(L^{q'} × L^{q'})³`, as
`B0428.ae_forall_pair`). -/
def AeForallSliceDy : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (q : ℝ≥0∞) [Fact (1 ≤ q)], 1 < q → ∀ (j : Fin 3) (F G : Yq P q),
    (∀ (ψ : Space → ℝ) (hψ : IsSpatialTest ψ) (i : Fin 3),
      ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)),
        innerPair q (B0428.sT q (hψ.derivative j) i) (F τ) =
          -innerPair q (B0428.sT q hψ i) (G τ)) →
    ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)), ∀ (ψ : Space → ℝ) (hψ : IsSpatialTest ψ)
      (i : Fin 3),
        innerPair q (B0428.sT q (hψ.derivative j) i) (F τ) =
          -innerPair q (B0428.sT q hψ i) (G τ)

/-- **Leaf: components to real and imaginary parts** (proved: `weakDyCOfComp`, `Parts.lean`).
The componentwise identity `CompDyC` gives `∂ⱼ Re u = Re g` and `∂ⱼ Im u = Im g`
(`HasWeakSpatialDerivative`). -/
def WeakDyCOfComp : Prop :=
  ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)] (j : Fin 3) (u g : Lp CVec3 q (volume : Measure Space)),
    CompDyC j u g → WeakDyC j u g

/-- **Leaf: real and imaginary parts to components** (the converse of `WeakDyCOfComp`;
proved: `compOfWeakDyC`, `Parts.lean`). -/
def CompOfWeakDyC : Prop :=
  ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)] (j : Fin 3) (u g : Lp CVec3 q (volume : Measure Space)),
    WeakDyC j u g → CompDyC j u g

/-- **Leaf: vector tests** (proved: `testDyOfComp`, `Parts.lean`). The componentwise identity
gives `∫ (∂ⱼψ)·u = -∫ ψ·g` (bilinear `dotL`) for every smooth compactly supported
`ψ : ℝ³ → ℂ³` (split `ψᵢ = Re ψᵢ + i Im ψᵢ` into real spatial tests). -/
def TestDyOfComp : Prop :=
  ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)] (j : Fin 3) (u g : Lp CVec3 q (volume : Measure Space)),
    CompDyC j u g → ∀ ψ : Space → CVec3, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∫ y, dotL (fderiv ℝ ψ y (coordinateVector j)) (u y) = -∫ y, dotL (ψ y) (g y)

/-- **Leaf: from the phases back to the phase space** (proved: `hasPhaseOpDyOfAe`,
`Slices.lean`). If for a.e. phase `τ` the slice identity `∫ (∂ⱼψ)·F(τ) = -∫ ψ·G(τ)` holds for
every smooth compactly supported `ψ : ℝ³ → ℂ³`, then `∂ⱼF = G` in distributions on
`(ℝ/Pℤ) × ℝ³` (each slice `Φ(t, ·)` of a phase test is such a `ψ`, and `dy j Φ (t, ·)` is its
derivative). -/
def HasPhaseOpDyOfAe : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (q : ℝ≥0∞) [Fact (1 ≤ q)] (j : Fin 3) (F G : Yq P q),
    (∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)), ∀ ψ : Space → CVec3, ContDiff ℝ ∞ ψ →
      HasCompactSupport ψ →
        ∫ y, dotL (fderiv ℝ ψ y (coordinateVector j)) ((F τ : Space → CVec3) y) =
          -∫ y, dotL (ψ y) ((G τ : Space → CVec3) y)) →
    HasPhaseOp (fun Φ => -dy j Φ) F G

/-! ## Assembly -/

/-- On `Y_{q₀}`, the pointwise weak-derivative identity `HasPtwOp` for the joint representatives
`rep` is the phase-space identity `HasPhaseOp` (`phasePair_eq_pairF_rep`). -/
theorem hasPtwOp_dy_iff (P : ℝ) [Fact (0 < P)] (j : Fin 3) (F G : Yq P q0E) :
    HasPtwOp P (fun Φ x => -(dy j Φ x)) (fun x => rep F x.1 x.2) (fun x => rep G x.1 x.2) ↔
      HasPhaseOp (fun Φ => -dy j Φ) F G := by
  constructor
  · intro h Φ hΦ
    have e1 : phasePair P q0E (-dy j Φ) F =
        pairF P (fun x => -(dy j Φ x)) (fun x => rep F x.1 x.2) :=
      phasePair_eq_pairF_rep ((hΦ.dy j).neg) F
    show phasePair P q0E (-dy j Φ) F = phasePair P q0E Φ G
    rw [e1, phasePair_eq_pairF_rep hΦ G]
    exact h Φ hΦ
  · intro h Φ hΦ
    have e1 : phasePair P q0E (-dy j Φ) F =
        pairF P (fun x => -(dy j Φ x)) (fun x => rep F x.1 x.2) :=
      phasePair_eq_pairF_rep ((hΦ.dy j).neg) F
    rw [← e1, ← phasePair_eq_pairF_rep hΦ G]
    exact h Φ hΦ

/-- **The weak-derivative commutation on `Y_{q₀}`** (SP 2381, 1307-1308) from the leaves: if
`∂ⱼF = G` in distributions, then `∂ⱼ(𝔓F) = 𝔓G`. -/
theorem lerayY_hasPhaseOp_dy_of (h1 : AeSliceDy) (h2 : AeForallSliceDy) (h3 : WeakDyCOfComp)
    (h4 : CompOfWeakDyC) (h5 : TestDyOfComp) (h6 : HasPhaseOpDyOfAe)
    (P : ℝ) [Fact (0 < P)] (j : Fin 3) (F G : Yq P q0E)
    (h : HasPhaseOp (fun Φ => -dy j Φ) F G) :
    HasPhaseOp (fun Φ => -dy j Φ) (lerayY P q0E one_lt_q0E q0E_ne_top F)
      (lerayY P q0E one_lt_q0E q0E_ne_top G) := by
  have hae := h2 P q0E one_lt_q0E j F G (h1 P q0E j F G h)
  refine h6 P q0E j _ _ ?_
  filter_upwards [hae, coeFn_lerayY (P := P) one_lt_q0E q0E_ne_top F,
    coeFn_lerayY (P := P) one_lt_q0E q0E_ne_top G] with τ hτ hF hG
  have hc : CompDyC j (F τ) (G τ) := by
    intro φ hφ i
    have e := hτ φ hφ i
    rw [B0428.sT, B0428.sT,
      innerPair_spatialTest (hφ.derivative j).smooth (hφ.derivative j).compact i (F τ),
      innerPair_spatialTest hφ.smooth hφ.compact i (G τ)] at e
    exact e
  have hw := weakDyC_lerayC one_lt_q0E q0E_ne_top (h3 q0E j _ _ hc)
  rw [hF, hG]
  exact h5 q0E j _ _ (h4 q0E j _ _ hw)

/-- **`LerayYq` from the six leaves**, with `T = lerayY P q₀` and `Cl = ‖lerayC q₀‖ + 1`. -/
theorem lerayYq_of (h1 : AeSliceDy) (h2 : AeForallSliceDy) (h3 : WeakDyCOfComp)
    (h4 : CompOfWeakDyC) (h5 : TestDyOfComp) (h6 : HasPhaseOpDyOfAe) : LerayYq := by
  refine ⟨‖lerayC q0E one_lt_q0E q0E_ne_top‖ + 1, by positivity, fun P _ => ?_⟩
  refine ⟨lerayY P q0E one_lt_q0E q0E_ne_top, ?_, fun F => lerayY_mem_Ysigma P F,
    fun Φ hΦ F => leraySymm_of lerayCTranspose solSliceFixed P Φ F hΦ,
    fun F hF => lerayY_mem_realSub P F hF, fun F hF => lerayY_mem_Osym P F hF, ?_⟩
  · exact (norm_lerayY_le one_lt_q0E q0E_ne_top).trans (le_add_of_nonneg_right zero_le_one)
  · intro F G j hFG
    rw [hasPtwOp_dy_iff] at hFG ⊢
    exact lerayY_hasPhaseOp_dy_of h1 h2 h3 h4 h5 h6 P j F G hFG

#print axioms weakDyC_lerayC
#print axioms hasPtwOp_dy_iff
#print axioms lerayY_hasPhaseOp_dy_of
#print axioms lerayYq_of

end UnforcedLeray.Short.IIb
