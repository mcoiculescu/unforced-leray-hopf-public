import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Defs

/-!
# Part III-a, `PartIII-a:T21/2/2/2/1`: `MovingAdjointEq` from five leaves

Source `the November 2 reference manuscript` (SP), lines 2854-2865
(`eq:short-causal-moving`), 2919-2921 (`D^#`), 3052-3058 (adjoint localized interaction), 3060,
with the train bounds of SP 270-288 and 2866-2873.

Leaves:
* `AdjRangeAge`: the reverse age lies in `(t, s)` for `ζ ∈ (0, Δz)`.
* `PhysAdjClassical`: the physical classical adjoint equation, in the form "the residual
  `κ = ∂_rφ + νΔφ + v·∇φ` is an adjoint interaction of `φ(r)` and lies in `X_{-m,c}`", for
  `ν ≤ 1` and a train with the time-local bounds `LadTrainBdd` on every `[0, S]`.
* `MovingSubstitution`: the pointwise chain rule `Φ(ζ,y) = a⁻¹φ(r(ζ),√a y)` (`dr/dζ = -a²`).
* `InteractionRescale`: rescaling `y = x/√a` maps adjoint interactions of cell `c` to those of cell
  `c/√a` (test `ψ(·/√a)`, kernel velocity `√a u(·/√a)`).
* `InteractionUnique`: two `X_{-m,d}` adjoint interactions of the same `Φ` agree a.e. on the cell.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.E0

open UnforcedLeray.Short.IIIa

/-- The physical residual `κ(r, x) = ∂_rφ + νΔφ + v·∇φ` of the adjoint equation
`-∂_rφ = νΔφ + v·∇φ - K^T(φ∇E)` (SP 3060, classical form of `IsAdjointFlow.weak`). -/
def physKappa {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (φ : ℝ → ℝ × ℝ → ℂ)
    (r : ℝ) (x : ℝ × ℝ) : ℂ :=
  deriv (fun r' => φ r' x) r + (ν : ℂ) * lapCx (φ r) x +
    ((tr.v r x 0 : ℝ) : ℂ) * pdCx 0 (φ r) x + ((tr.v r x 1 : ℝ) : ℂ) * pdCx 1 (φ r) x

/-- **Leaf 0.** For `ζ ∈ (0, Δz)` the reverse age `revAge ν s ζ` lies in `(t, s)` (the map
`z ↦ z/(1-νz)` is increasing and `z(r) = z_s - ζ ∈ (z_t, z_s)`; SP 2857). -/
def AdjRangeAge : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ t s : ℝ, 0 ≤ t → t < s → ∀ ζ ∈ Ioo 0 (deltaZ ν t s),
    revAge ν s ζ ∈ Ioo t s

/-- **Leaf 1 (physical classical adjoint equation; SP 3060, 3052-3058).** From
`IsAdjointFlow.weak` and `timeIntegrable` (FTC for `r ↦ ∫ φ(r) ψ`), the joint smoothness of `φ` on
`[t, s)`, and integration by parts on the `c`-periodic cell (`div v = 0` from the train):
for `r ∈ (t, s)` the residual `κ(r)` lies in `X_{-m,c}` and is the adjoint interaction of `φ(r)`
with `E = Ec tr r`: `∫ κ ψ = ∫ φ (K_cψ)·∇E` for all tests `ψ` with kernel velocity.
The train hypotheses are those of `MovingAdjointEq`: `ν ≤ 1`, so `c = ν^{-2} ≥ 1` (the
`X_{-m,c}` bound of `κ`), and the time-local bounds `LadTrainBdd tr m S C` on every `[0, S]`
(SP 270-288, 2866-2873; the continuity of `r ↦ ∫ φ(r) (K_cψ)·∇E(r)` in the FTC step). They hold
for BUC trains with `ν` small (`ladTrainBddAll`). -/
def PhysAdjClassical (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ),
    0 ≤ t → t < s → ∀ (g : ℝ × ℝ → ℂ) (φ : ℝ → ℝ × ℝ → ℂ),
      IsAdjointFlow ν (ν ^ (-2 : ℝ)) m tr t s g φ → ν ≤ 1 →
      (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) → ∀ r ∈ Ioo t s,
        MemLp (physKappa tr φ r) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ∧
        IsAdjInteraction (ν ^ (-2 : ℝ)) (UnforcedLeray.B0238.Ec tr r) (φ r) (physKappa tr φ r)

/-- **Leaf 2 (moving substitution; SP 2854-2865, 2919-2921, 3060).** Pure calculus: with
`Φ(ζ, y) = a⁻¹ φ(r(ζ), √a y)`, `r = revAge ν s ζ`, `a = 1+νr`, `dr/dζ = -a²`, `θ⁻¹ = νa`,
`ΔΦ = (Δφ)(√a y)`, `∇Φ = a^{-1/2}(∇φ)(√a y)`:
`∂_ζΦ(ζ,y) = θ⁻¹ D^#Φ + V·∇Φ - χ₀`, `χ₀(y) = a κ(r, √a y)`, for every `y`. -/
def MovingSubstitution (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ),
    0 ≤ t → t < s → ∀ (g : ℝ × ℝ → ℂ) (φ : ℝ → ℝ × ℝ → ℂ),
      IsAdjointFlow ν (ν ^ (-2 : ℝ)) m tr t s g φ →
      ∀ ζ ∈ Ioo 0 (deltaZ ν t s), ∀ y : ℝ × ℝ,
        HasDerivAt (fun ζ' => revPhi ν φ s ζ' y)
          ((((revTheta ν s ζ)⁻¹ : ℝ) : ℂ) * dSharp (revPhi ν φ s ζ) y +
            transCx (movingTrainV tr (revAge ν s ζ)) (revPhi ν φ s ζ) y -
            ((clockA ν (revAge ν s ζ) : ℝ) : ℂ) *
              physKappa tr φ (revAge ν s ζ)
                (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1,
                  Real.sqrt (clockA ν (revAge ν s ζ)) * y.2)) ζ

/-- **Leaf 3 (rescaling of adjoint interactions; SP 3052-3058).** For `c, a > 0`: if `χ ∈ X_{-m,c}`
is an adjoint interaction of `Φ` with `E` on the cell `c`, then `a χ(√a ·) ∈ X_{-m,c/√a}` is an
adjoint interaction of `a⁻¹Φ(√a ·)` with `a² E(√a ·)` on the cell `c/√a` (test
`ψ̃(x) = ψ(x/√a)`, kernel velocity `ũ(x) = √a u(x/√a)`; the mean shear and `L²` condition scale
the same way; the density `⟨x⟩^{-2m}` is comparable under `x ↦ √a x`). -/
def InteractionRescale : Prop :=
  ∀ (m c a : ℝ), 0 < c → 0 < a → ∀ (E : ℝ × ℝ → ℝ) (Φ χ : ℝ × ℝ → ℂ),
    MemLp χ 2 (B0579.cellMeasure c (-m)) → IsAdjInteraction c E Φ χ →
    MemLp (fun y : ℝ × ℝ => (a : ℂ) * χ (Real.sqrt a * y.1, Real.sqrt a * y.2)) 2
        (B0579.cellMeasure (cellLen c a) (-m)) ∧
    IsAdjInteraction (cellLen c a)
      (fun y : ℝ × ℝ => a ^ 2 * E (Real.sqrt a * y.1, Real.sqrt a * y.2))
      (fun y : ℝ × ℝ => ((a⁻¹ : ℝ) : ℂ) * Φ (Real.sqrt a * y.1, Real.sqrt a * y.2))
      (fun y : ℝ × ℝ => (a : ℂ) * χ (Real.sqrt a * y.1, Real.sqrt a * y.2))

/-- **Leaf 4 (uniqueness of the adjoint interaction; SP 3052-3058).** If `χ, χ' ∈ X_{-m,d}` are
both adjoint interactions of `Φ` with `E` on the cell `d > 0`, then `χ = χ'` a.e. on the cell.
Proof: the difference `δ` satisfies `∫ δ ψ = 0` for every `d`-periodic test `ψ` with compact
transversal support, each of which has a kernel Biot-Savart velocity (existence of `K_dψ` for every
circulation: Fourier/Green kernel), then the fundamental lemma on the open cell via periodic
extension. -/
def InteractionUnique : Prop :=
  ∀ (m d : ℝ), 0 < d → ∀ (E : ℝ × ℝ → ℝ) (Φ χ χ' : ℝ × ℝ → ℂ),
    MemLp χ 2 (B0579.cellMeasure d (-m)) → MemLp χ' 2 (B0579.cellMeasure d (-m)) →
    IsAdjInteraction d E Φ χ → IsAdjInteraction d E Φ χ' →
    ∀ᵐ y ∂(volume.restrict (B0579.cell d)), χ y = χ' y

/-- `MovingAdjointEq` from the five leaves. -/
theorem movingAdjointEq_of (m : ℝ) (h0 : AdjRangeAge) (h1 : PhysAdjClassical m)
    (h2 : MovingSubstitution m) (h3 : InteractionRescale) (h4 : InteractionUnique) :
    MovingAdjointEq m := by
  intro ν hν tr t s ht hts g φ hφ hν1 hB ζ hζ χ hχ hχI
  have hr := h0 ν hν t s ht hts ζ hζ
  obtain ⟨hk1, hk2⟩ := h1 ν hν tr t s ht hts g φ hφ hν1 hB _ hr
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have ha : 0 < clockA ν (revAge ν s ζ) := by
    have : 0 ≤ revAge ν s ζ := ht.trans hr.1.le
    unfold clockA; nlinarith
  obtain ⟨hk3, hk4⟩ := h3 m _ _ hc ha _ _ _ hk1 hk2
  have hU := h4 m _ (by
      unfold revCell cellLen
      exact div_pos hc (Real.sqrt_pos.2 ha)) _ _ _ _ hχ hk3 hχI hk4
  filter_upwards [hU] with y hy
  rw [hy]
  exact h2 ν hν tr t s ht hts g φ hφ ζ hζ y

end UnforcedLeray.Short.IIIa.E0
