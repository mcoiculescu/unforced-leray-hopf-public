import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_3

/-!
# `PartIII-a:T21/2/7/2/3/1`: the derivative of the cut energy, decomposed

Source: `the November 2 reference manuscript` (SP) lines 3060-3067.

`CutE1Deriv` is split into three true leaves:

* `CutE1DerivUnder` (calculus): differentiate `cutE1` under the integral on the band
  `supp χ_R`, using `∂_ρ∂_kψ = ∂_k∂_ρψ` (symmetry of mixed partials on the open strip);
* `LadDtRegular`: `∂_ρψ(ρ)` is smooth in `x` and `c`-periodic;
* `CutIBP` (integration by parts in `x_k`, no seam term: the weight takes equal values at `q = ±c/2`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

/-- **Leaf A (SP 3060-3064).** Differentiation of the cut energy under the integral sign:
`d/dρ Σ_k ∫ χ_R²⟨x⟩^{-2m}|∂_kψ(ρ)|² = Σ_k ∫ χ_R²⟨x⟩^{-2m} 2 Re(conj(∂_kψ(ρ)) ∂_k∂_ρψ(ρ))`.
Proof: `(r, x) ↦ ∂_kψ(r)(x)` is jointly smooth (`jointSmooth_pdCx`), the mixed partial symmetry
(`ContDiffAt.isSymmSndFDerivAt` on the open set `Ioo t s ×ˢ univ`) gives
`∂_r ∂_kψ(r)(x) = ∂_k(ladDt ψ r)(x)`; the integrand vanishes for `x.2² ≥ 2R²` (`ladCutProps`),
so the domination is by a constant times the indicator of a compact box
(`hasDerivAt_integral_of_dominated_loc_of_deriv_le`). -/
def CutE1DerivUnder : Prop :=
  ∀ (c m R t s : ℝ) (ψ : ℝ → ℝ × ℝ → ℂ), 0 < c → 0 < R →
    ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t s ×ˢ univ) →
    ∀ ρ ∈ Ioo t s,
      HasDerivAt (fun r => cutE1 c m R (ψ r))
        (∑ k : Fin 2, ∫ x in B0579.cell c, ladCut R x ^ 2 *
          (B0579.jb x ^ (-m) * (2 * ((starRingEnd ℂ) (pdCx k (ψ ρ) x) *
            pdCx k (ladDt ψ ρ) x).re))) ρ

/-- **Leaf B (SP 3060-3067).** `∂_ρψ(ρ)` is smooth in `x` (it is the `(1, 0)`-component of
`fderivWithin` of the jointly smooth `ψ`) and `c`-periodic (derivative in `ρ` of the periodicity
identity `ψ r (x.1 + c, x.2) = ψ r x`). -/
def LadDtRegular : Prop :=
  ∀ (c t s : ℝ) (ψ : ℝ → ℝ × ℝ → ℂ),
    ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t s ×ˢ univ) →
    (∀ r ∈ Ico t s, ∀ x : ℝ × ℝ, ψ r (x.1 + c, x.2) = ψ r x) →
    ∀ ρ ∈ Ioo t s, ContDiff ℝ ∞ (ladDt ψ ρ) ∧
      ∀ x : ℝ × ℝ, ladDt ψ ρ (x.1 + c, x.2) = ladDt ψ ρ x

/-- **Leaf C (SP 3060-3067): the integration by parts.** For smooth `c`-periodic `Φ`, `F` and `R > 0`:
`Σ_k ∫_{cell} χ_R²⟨x⟩^{-2m} 2 Re(conj(∂_kΦ) ∂_kF) = cutRate c m R Φ F`. Proof: with
`G k x = χ_R²⟨x⟩^{-2m} Re(conj(∂_kΦ) F)`, `∫_cell ∂_k G_k = 0` (`k = 1`:
`UnforcedLeray.Cyl.integral_cell_deriv_eta`, `Lib/Cylinder/IBP.lean:152`, compact support in `η`;
`k = 0`: `Cyl.integral_cell_deriv_q`, `IBP.lean:125`, the seam terms cancel because `∂_0Φ`, `F` are
`c`-periodic, `χ_R` depends on `η` only and `⟨(±c/2, η)⟩` is one value). Product rule
`∂_kG_k = ∂_k(χ_R²⟨x⟩^{-2m}) Re(conj ∂_kΦ F) + χ_R²⟨x⟩^{-2m} (Re(conj ∂_k∂_kΦ F) + Re(conj ∂_kΦ ∂_kF))`,
and `ΔΦ = Σ_k ∂_k∂_kΦ`. Note `Cyl.cell c` uses `Ico (-c/2) (c/2)` and `B0579.cell c` uses
`Ico (-(c/2)) (c/2)` (`neg_div`). The weight `⟨x⟩^{-2m}` is not periodic, so `cellDivZero` does
not apply. -/
def CutIBP : Prop :=
  ∀ (c m R : ℝ) (Φ F : ℝ × ℝ → ℂ), 0 < c → 0 < R → ContDiff ℝ ∞ Φ → ContDiff ℝ ∞ F →
    (∀ x : ℝ × ℝ, Φ (x.1 + c, x.2) = Φ x) → (∀ x : ℝ × ℝ, F (x.1 + c, x.2) = F x) →
    ∑ k : Fin 2, ∫ x in B0579.cell c, ladCut R x ^ 2 *
        (B0579.jb x ^ (-m) * (2 * ((starRingEnd ℂ) (pdCx k Φ x) * pdCx k F x).re)) =
      cutRate c m R Φ F

/-- `CutE1Deriv` from its three leaves. -/
theorem cutE1Deriv_of (hA : CutE1DerivUnder) (hB : LadDtRegular) (hC : CutIBP) : CutE1Deriv := by
  intro c m R t s ψ hc hR hj hper ρ hρ
  have h := hA c m R t s ψ hc hR hj ρ hρ
  obtain ⟨hF, hFper⟩ := hB c t s ψ hj hper ρ hρ
  have hΦ : ContDiff ℝ ∞ (ψ ρ) := adjContDiff_slice hj (Ioo_subset_Ico_self hρ)
  rw [hC c m R (ψ ρ) (ladDt ψ ρ) hc hR hΦ hF (hper ρ (Ioo_subset_Ico_self hρ)) hFper] at h
  exact h

end UnforcedLeray.Short.IIIa
