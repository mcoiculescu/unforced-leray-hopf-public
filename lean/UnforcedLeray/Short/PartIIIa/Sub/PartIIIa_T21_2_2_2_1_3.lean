import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_1

/-!
# Part III-a, `PartIII-a:T21/2/2/2/1/3`: `InteractionRescale` from seven leaves

Source `the November 2 reference manuscript` (SP),
lines 3052-3058 (adjoint localized interaction), 2875-2896 (kernel Biot-Savart velocity).

Write `s = √a`, `cellLen c a = c/s`.  A test `ψ̃` of the cell `c/s` with kernel velocity `ũ` is
transported to the test `ψ(x) = ψ̃(x/s)` of the cell `c` with kernel velocity `u(x) = s ũ(x/s)`
(`curl u (x) = ψ̃(x/s)`, `div u = 0`; the circulation is `Γ = a Γ̃`, and
`meanShear c Γ x = s · meanShear (c/s) Γ̃ (x/s)`).  The adjoint-interaction identity for
`(E, Φ, χ)` on the cell `c` then gives that for `(a²E(s·), a⁻¹Φ(s·), aχ(s·))` on the cell `c/s`
by the change of variables `x = s y` (`d y = a⁻¹ d x`).

Leaves (all true, each a change of variables):
* `RescaleMemLp`: the weighted `L²` clause (the density `⟨y⟩^{-2m}` at `y = x/s` is comparable to
  `⟨x⟩^{-2m}`, ratio in `[min 1 (1/a), max 1 (1/a)]`);
* `RescaleTest`: `ψ̃` test of the cell `c/s` ⟹ `ψ̃(·/s)` test of the cell `c`;
* `RescaleKernelL2`, `RescaleKernelDiv`, `RescaleKernelCurl`: the three clauses of
  `IsKernelBiotSavart` for `(ψ̃(·/s), s ũ(·/s))` on the cell `c`;
* `RescaleLHS`, `RescaleRHS`: the two integrals of `IsAdjInteraction`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.E0

open UnforcedLeray.Short.IIIa

/-- **Leaf (weighted `L²` clause; SP 3052-3058).** -/
def RescaleMemLp : Prop :=
  ∀ (m c a : ℝ), 0 < c → 0 < a → ∀ χ : ℝ × ℝ → ℂ,
    MemLp χ 2 (B0579.cellMeasure c (-m)) →
    MemLp (fun y : ℝ × ℝ => (a : ℂ) * χ (Real.sqrt a * y.1, Real.sqrt a * y.2)) 2
        (B0579.cellMeasure (cellLen c a) (-m))

/-- **Leaf (tests; SP 3052-3058).** `ψ̃(x/s)` is `c`-periodic, smooth and band-supported. -/
def RescaleTest : Prop :=
  ∀ (c a : ℝ), 0 < c → 0 < a → ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest (cellLen c a) ψ →
    B0579.IsCylTest c (fun x : ℝ × ℝ => ψ (x.1 / Real.sqrt a, x.2 / Real.sqrt a))

/-- **Leaf (kernel velocity, `L²` clause; SP 2875-2896).** The circulation `Γ = a Γ̃`
(`∫_{C_c} ψ̃(x/s) dx = a ∫_{C_{c/s}} ψ̃`) and
`meanShear c Γ x j = s · meanShear (c/s) Γ̃ (x/s) j`; `L²(C_c)` of `x ↦ s f(x/s)` from `L²(C_{c/s})`
of `f` by `integral_cell_scale`-type change of variables (`sqrt_smul_cell`). -/
def RescaleKernelL2 : Prop :=
  ∀ (c a : ℝ), 0 < c → 0 < a → ∀ (ψ : ℝ × ℝ → ℝ) (u : ℝ × ℝ → Fin 2 → ℝ),
    (∀ j, MemLp (fun x => u x j - meanShear (cellLen c a) (∫ y in B0579.cell (cellLen c a), ψ y) x j)
      2 (volume.restrict (B0579.cell (cellLen c a)))) →
    ∀ j, MemLp (fun x : ℝ × ℝ => Real.sqrt a * u (x.1 / Real.sqrt a, x.2 / Real.sqrt a) j -
        meanShear c (∫ y in B0579.cell c, ψ (y.1 / Real.sqrt a, y.2 / Real.sqrt a)) x j)
      2 (volume.restrict (B0579.cell c))

/-- **Leaf (kernel velocity, divergence clause).** For a test `φ` of the cell `c`,
`φ̃(y) = φ(s y)` is a test of the cell `c/s`, `∂_kφ̃(y) = s (∂_kφ)(s y)`, and
`∫_{C_c} G = a ∫_{C_{c/s}} G(s ·)` (`integral_cell_scale`). -/
def RescaleKernelDiv : Prop :=
  ∀ (c a : ℝ), 0 < c → 0 < a → ∀ u : ℝ × ℝ → Fin 2 → ℝ,
    (∀ φ, B0579.IsCylTest (cellLen c a) φ →
      ∫ x in B0579.cell (cellLen c a), (u x 0 * B0579.pd 0 φ x + u x 1 * B0579.pd 1 φ x) = 0) →
    ∀ φ, B0579.IsCylTest c φ →
      ∫ x in B0579.cell c, (Real.sqrt a * u (x.1 / Real.sqrt a, x.2 / Real.sqrt a) 0 * B0579.pd 0 φ x +
        Real.sqrt a * u (x.1 / Real.sqrt a, x.2 / Real.sqrt a) 1 * B0579.pd 1 φ x) = 0

/-- **Leaf (kernel velocity, curl clause).** Same change of variables as `RescaleKernelDiv`. -/
def RescaleKernelCurl : Prop :=
  ∀ (c a : ℝ), 0 < c → 0 < a → ∀ (ψ : ℝ × ℝ → ℝ) (u : ℝ × ℝ → Fin 2 → ℝ),
    (∀ φ, B0579.IsCylTest (cellLen c a) φ → ∫ x in B0579.cell (cellLen c a), ψ x * φ x =
      ∫ x in B0579.cell (cellLen c a), (u x 0 * B0579.pd 1 φ x - u x 1 * B0579.pd 0 φ x)) →
    ∀ φ, B0579.IsCylTest c φ →
      ∫ x in B0579.cell c, ψ (x.1 / Real.sqrt a, x.2 / Real.sqrt a) * φ x =
      ∫ x in B0579.cell c, (Real.sqrt a * u (x.1 / Real.sqrt a, x.2 / Real.sqrt a) 0 * B0579.pd 1 φ x -
        Real.sqrt a * u (x.1 / Real.sqrt a, x.2 / Real.sqrt a) 1 * B0579.pd 0 φ x)

/-- **Leaf (left side of the adjoint identity).** `∫_{C_{c/s}} aχ(s y) ψ̃(y) dy =
∫_{C_c} χ(x) ψ̃(x/s) dx` (`integral_cell_scale` for the complex integrand `G(x) = χ(x) ψ̃(x/s)`). -/
def RescaleLHS : Prop :=
  ∀ (c a : ℝ), 0 < c → 0 < a → ∀ (χ : ℝ × ℝ → ℂ) (ψ : ℝ × ℝ → ℝ),
    ∫ y in B0579.cell (cellLen c a),
        (a : ℂ) * χ (Real.sqrt a * y.1, Real.sqrt a * y.2) * (ψ y : ℂ) =
      ∫ x in B0579.cell c, χ x * (ψ (x.1 / Real.sqrt a, x.2 / Real.sqrt a) : ℂ)

/-- **Leaf (right side of the adjoint identity).** With `Ẽ(y) = a²E(s y)`, `∂_kẼ(y) =
a² s (∂_kE)(s y)` (for every `E`: both sides are `0` where `E` is not differentiable), so
`∫_{C_{c/s}} a⁻¹Φ(s y)(ũ·∇Ẽ)(y) dy = ∫_{C_c} Φ (s ũ(·/s))·∇E`. -/
def RescaleRHS : Prop :=
  ∀ (c a : ℝ), 0 < c → 0 < a → ∀ (E : ℝ × ℝ → ℝ) (Φ : ℝ × ℝ → ℂ) (u : ℝ × ℝ → Fin 2 → ℝ),
    ∫ y in B0579.cell (cellLen c a),
        ((a⁻¹ : ℝ) : ℂ) * Φ (Real.sqrt a * y.1, Real.sqrt a * y.2) *
          ((u y 0 * B0579.pd 0 (fun y : ℝ × ℝ => a ^ 2 * E (Real.sqrt a * y.1, Real.sqrt a * y.2)) y +
            u y 1 * B0579.pd 1 (fun y : ℝ × ℝ => a ^ 2 * E (Real.sqrt a * y.1, Real.sqrt a * y.2)) y : ℝ) : ℂ) =
      ∫ x in B0579.cell c, Φ x *
        (((Real.sqrt a * u (x.1 / Real.sqrt a, x.2 / Real.sqrt a) 0) * B0579.pd 0 E x +
          (Real.sqrt a * u (x.1 / Real.sqrt a, x.2 / Real.sqrt a) 1) * B0579.pd 1 E x : ℝ) : ℂ)

/-- `InteractionRescale` from the seven leaves. -/
theorem interactionRescale_of (h0 : RescaleMemLp) (h1 : RescaleTest) (h2 : RescaleKernelL2)
    (h3 : RescaleKernelDiv) (h4 : RescaleKernelCurl) (h5 : RescaleLHS) (h6 : RescaleRHS) :
    InteractionRescale := by
  intro m c a hc ha E Φ χ hχ hI
  refine ⟨h0 m c a hc ha χ hχ, ?_⟩
  intro ψ u hT hK
  obtain ⟨hK1, hK2, hK3⟩ := hK
  have hKt : IsKernelBiotSavart c (fun x : ℝ × ℝ => ψ (x.1 / Real.sqrt a, x.2 / Real.sqrt a))
      (fun x j => Real.sqrt a * u (x.1 / Real.sqrt a, x.2 / Real.sqrt a) j) :=
    ⟨h2 c a hc ha ψ u hK1, h3 c a hc ha u hK2, h4 c a hc ha ψ u hK3⟩
  have h := hI _ _ (h1 c a hc ha ψ hT) hKt
  rw [← h5 c a hc ha χ ψ, ← h6 c a hc ha E Φ u] at h
  exact h

end UnforcedLeray.Short.IIIa.E0
