import UnforcedLeray.Short.PartIIb.Sub.T11

/-!
# Part II-b, leaf `PartII-b:T11/2` (`FlatDualConstancy`): reduction to three leaves (conditional)

Source of record: `the November 2 reference manuscript`, the flat equation
(SP 1923-1927) and the duality argument described in `Sub/T11.lean` (step 2).

For a flat response `b` to `0` in `H_r` and a heat solution `H` put
`F(σ) = σ^μ ∫ b(σ)·∇^⊥H(s-σ) d(dq dη/c)` (`dualF`).  Three leaves:

* `DualFLocInt` (`T11/2/1`): `F` is locally integrable on `(0, s)` (Hölder: `b ∈ L^r` of
  `s^{r/2-5/2}ds ⊗ cell`, derivatives of `H` in `L^{r'}` of `[τ₁,τ₂] × cell × ℝ`);
* `DualFTestZero` (`T11/2/2`, uses `FlatEqCellStream`, `T11/1`): `∫ χ'(σ)F(σ)dσ = 0` for every
  `χ ∈ C_c^∞(0,s)` (test the cell-stream identity with `ψ = Re/Im(χ σ^{μ-1}) φ_L(η) H(s-σ)`, let
  `L → ∞`);
* `DuBoisReymond` (`T11/2/3`): a locally integrable `F` on `(0,s)` with `∫ χ'F = 0` for all
  `χ ∈ C_c^∞(0,s)` is a.e. constant.

Proved here: `flatDualConstancy_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- `F(σ) = σ^μ ∫ b(σ)·∇^⊥(H(s-σ,·)) d(dq dη/c)` (SP 1923-1927, duality pairing). -/
def dualF (c : ℝ) (μ : ℂ) (b : CProf) (H : Coord → ℝ) (s : ℝ) (σ : ℝ) : ℂ :=
  ((σ : ℝ) : ℂ) ^ μ * ∫ p, ∑ i : Fin 2, b (σ, p) i *
      ((perpGrad (fun z => H (s - σ, z)) p i : ℝ) : ℂ) ∂(Cyl.avgμ c)

/-- **Leaf `PartII-b:T11/2/1`**: `dualF` is locally integrable on `(0, s)`.  Proof: on
`[a, a'] ⊂ (0,s)`, `|F(σ)| ≤ σ^{Re μ} ‖b(σ)‖_{L^r(cell×ℝ)} ‖∇^⊥H(s-σ)‖_{L^{r'}(cell×ℝ)}`; Hölder in
`σ` with `b ∈ L^r(s^{r/2-5/2}ds ⊗ cell)` and `HeatSol.deriv_memLp` with `n = 1`,
`[τ₁, τ₂] = [s-a', s-a]`.  Measurability of `F` by Fubini (`b` strongly measurable, `H` smooth
on `τ > 0`). -/
def DualFLocInt : Prop :=
  ∀ (c r ν : ℝ) (μ : ℂ) (b : CProf) (H : Coord → ℝ) (s : ℝ),
    0 < c → 0 < ν → 1 < r → 0 < s → InHr c r b → IsFlatResponse ν μ 0 b →
    HeatSol c ν (r / (r - 1)) H →
    LocallyIntegrableOn (dualF c μ b H s) (Ioo (0 : ℝ) s) volume

/-- **Leaf `PartII-b:T11/2/2`** (uses `FlatEqCellStream`; SP 1923-1927): for every
`χ ∈ C_c^∞(0,s)`, `∫_{(0,s)} χ'(σ) F(σ) dσ = 0`.  Proof: `a(σ) = χ(σ)σ^{μ-1}`,
`g(σ) = H(s-σ)` satisfies `g_σ + νΔg = 0`, so `(μ-1)ψ - σψ_σ - νσΔψ = -χ'(σ)σ^μ g` for `ψ = a g`;
test `FlatEqCellStream` with `Re(a) φ_L g` and `Im(a) φ_L g` (`φ_L(η) = φ(η/L)`), the
cutoff-commutator terms are `O(1/L)` by Hölder (`‖b‖_{L^r}`, `‖∂^α H‖_{L^{r'}}`, `|α| ≤ 3`), and
`flatTranspose (∇^⊥ψ) = ∇^⊥ (Tψ)` up to those terms. -/
def DualFTestZero : Prop :=
  FlatEqCellStream →
  ∀ (c r ν : ℝ) (μ : ℂ) (b : CProf) (H : Coord → ℝ) (s : ℝ),
    0 < c → 0 < ν → 1 < r → 0 < s → InHr c r b → IsFlatResponse ν μ 0 b →
    HeatSol c ν (r / (r - 1)) H →
    ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ Ioo (0 : ℝ) s →
      ∫ σ in Ioo (0 : ℝ) s, ((deriv χ σ : ℝ) : ℂ) * dualF c μ b H s σ = 0

/-- **Leaf `PartII-b:T11/2/3`** (du Bois-Reymond lemma; pure real analysis): a locally integrable
`F : ℝ → ℂ` on `(0, s)` with `∫ χ' F = 0` for all `χ ∈ C_c^∞(0,s)` is a.e. constant on `(0,s)`.
Mathlib: `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`
(`Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`) applied to `F - avg`, after writing
every test `χ₀` with `∫ χ₀ = 0` as `χ'` (primitive of a compactly supported mean-zero smooth
function). -/
def DuBoisReymond : Prop :=
  ∀ (s : ℝ) (F : ℝ → ℂ), 0 < s → LocallyIntegrableOn F (Ioo (0 : ℝ) s) volume →
    (∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ Ioo (0 : ℝ) s →
      ∫ σ in Ioo (0 : ℝ) s, ((deriv χ σ : ℝ) : ℂ) * F σ = 0) →
    ∃ κ : ℂ, ∀ᵐ σ : ℝ ∂(volume.restrict (Ioo (0 : ℝ) s)), F σ = κ

/-- `FlatDualConstancy` from its three leaves (and `FlatEqCellStream`, `T11/1`). -/
theorem flatDualConstancy_of (hcs : FlatEqCellStream) (h1 : DualFLocInt) (h2 : DualFTestZero)
    (h3 : DuBoisReymond) : FlatDualConstancy := by
  intro c r ν μ b H s hc hν hr hs hb hfl hH
  obtain ⟨κ, hκ⟩ := h3 s (dualF c μ b H s) hs (h1 c r ν μ b H s hc hν hr hs hb hfl hH)
    (fun χ hχ hcs' hsupp => h2 hcs c r ν μ b H s hc hν hr hs hb hfl hH χ hχ hcs' hsupp)
  exact ⟨κ, hκ⟩

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.flatDualConstancy_of
