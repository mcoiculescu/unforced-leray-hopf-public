import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_of

/-!
# `FlatSolPair` from two chart facts (decomposition of `PartIII-b:C/flatset/col/7/1/1/2/6/1/1/3`)

Source `the November 2 reference manuscript`
1650-1656.  An element of `solenoidalHC 0 c` is H-orthogonal to every generator `cgrad 0 Φ`
(`inner_cgrad_eq_zero_of_mem'`, proved).  Two open chart facts:

* `FlatProductTest` : `Φ = χ(s) s^{3/2} ψ(q,η)` is a profile test with `cgrad 0 Φ ∈ L²(H)`;
* `FlatSlicePairing`: for such `Φ`, `⟨cgrad 0 Φ, h⟩_H = 0` forces `∫ χ(s) divPairing c b ψ s ds = 0`
  (the `s^{-3/2}` weight cancels against `s^{3/2}`; Fubini on `(0,∞) × cell`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- Orthogonality of `solenoidalHC 0 c` to a single profile-test generator (proved). -/
theorem inner_cgrad_eq_zero_of_mem' {c : ℝ} (Φ : UnforcedLeray.B0226.ProfileTest c)
    (hu : MemLp (UnforcedLeray.Short.PartIIa.cgrad 0 Φ.1) 2
      (UnforcedLeray.B0220.measureH c))
    {h : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC}
    (hh : h ∈ UnforcedLeray.Short.PartIIa.solenoidalHC 0 c) :
    inner ℂ (hu.toLp (UnforcedLeray.Short.PartIIa.cgrad 0 Φ.1)) h = (0 : ℂ) := by
  rw [UnforcedLeray.Short.PartIIa.solenoidalHC, Submodule.mem_orthogonal] at hh
  exact hh _ (Submodule.subset_span ⟨Φ, hu, rfl⟩)

/-- Product test (source 1650-1656): for `χ ∈ C_c^∞((0,∞))` and a cylinder test `ψ`,
`Φ(s,q,η) = χ(s) s^{3/2} ψ(q,η)` is a profile test (smooth across `s = 0` since `tsupport χ ⊆ (0,∞)`;
`q`-periodic and `η`-banded by `IsCylTest`) and `cgrad 0 Φ ∈ L²(measureH c)`. -/
def FlatProductTest : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (χ : ℝ → ℝ), ContDiff ℝ ∞ χ → HasCompactSupport χ →
    tsupport χ ⊆ Ioi (0 : ℝ) → ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ →
      ∃ Φ : UnforcedLeray.B0226.ProfileTest c,
        (∀ p : UnforcedLeray.B0220.Profile,
          Φ.1 p = χ p.1 * p.1 ^ (3 / 2 : ℝ) * ψ (p.2.1, p.2.2)) ∧
        MemLp (UnforcedLeray.Short.PartIIa.cgrad 0 Φ.1) 2 (UnforcedLeray.B0220.measureH c)

/-- Chart pairing (source 1650-1656): for `Φ = χ s^{3/2} ψ`, `h` the lift of `f` and `b` a smooth
representative of `f`, `⟨cgrad 0 Φ, h⟩_H = ∫ χ(s) divPairing c b ψ s ds` (up to the cell
normalisation constant; stated as the transfer of vanishing).  Uses `cellPtH_eq`, `ageμ`/`measureH`
weights, `integral_prod` on `(0,∞) × cell`, and `Cyl.cell c = B0579.cell c`. -/
def FlatSlicePairing : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (f : Hsp c) (h : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC)
    (b : Chart → Fin 2 → ℂ) (χ : ℝ → ℝ) (ψ : ℝ × ℝ → ℝ),
    ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ Ioi (0 : ℝ) → B0579.IsCylTest c ψ →
    SmoothRep c b →
    ∀ (Φ : UnforcedLeray.B0226.ProfileTest c)
      (hu : MemLp (UnforcedLeray.Short.PartIIa.cgrad 0 Φ.1) 2 (UnforcedLeray.B0220.measureH c)),
    (∀ p : UnforcedLeray.B0220.Profile, Φ.1 p = χ p.1 * p.1 ^ (3 / 2 : ℝ) * ψ (p.2.1, p.2.2)) →
    (h : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
        =ᵐ[UnforcedLeray.B0220.measureH c] (fun p => NearInst.merC (f (NearInst.cellPt c p))) →
    b =ᵐ[ageμ c (-3 / 2)] NearInst.velC f →
    inner ℂ (hu.toLp (UnforcedLeray.Short.PartIIa.cgrad 0 Φ.1)) h = (0 : ℂ) →
      ∫ s, χ s • divPairing c b ψ s = 0

theorem flatSolPair_of (hT : FlatProductTest) (hS : FlatSlicePairing) : FlatSolPair := by
  intro c hc f h hh hmem b hb hbe χ h1 h2 h3 ψ hψ
  obtain ⟨Φ, hΦ, hu⟩ := hT c hc χ h1 h2 h3 ψ hψ
  exact hS c hc f h b χ ψ h1 h2 h3 hψ hb Φ hu hΦ hh hbe
    (inner_cgrad_eq_zero_of_mem' Φ hu hmem)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
