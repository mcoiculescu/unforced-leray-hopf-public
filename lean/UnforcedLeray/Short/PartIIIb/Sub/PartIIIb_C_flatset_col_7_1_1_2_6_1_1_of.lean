import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_of

/-!
# `SFCDivWeak` from three source facts (decomposition of `PartIII-b:C/flatset/col/7/1/1/2/6/1/1`)

Source `the November 2 reference manuscript`
1650-1656: `R₀ = (μ - A₀)⁻¹ P₀` has range in the Leray-projected subspace `solenoidalHC 0 c`, which is
H-orthogonal to `cgrad 0 (χ ⊗ ψ)`; unpacking this on the chart gives the weak slice divergence.

* `FlatLift`      : every `f ∈ Hsp c` has an `HSpace c MeridC` representative on the chart;
* `FlatResSol`    : the flat resolvent `B0225.R0` (after `P₀`) lands in `solenoidalHC 0 c`
                    (source 1655-1656: `A₀` commutes with the flat Leray projection);
* `FlatSolPair`   : chart dictionary: an element of `solenoidalHC 0 c` representing `f` is
                    H-orthogonal to `cgrad 0 (χ ⊗ ψ)`, i.e. `∫ χ(s) divPairing c b ψ s ds = 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- Chart lift `Hsp c → HSpace c MeridC` (`NearInst.merC ∘ f ∘ NearInst.cellPt c`; the
`ageμ c (-3/2)` weight on the chart equals `measureH c` on the profile cell). -/
def FlatLift : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ f : Hsp c, ∃ f' : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC,
    (f' : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
      =ᵐ[UnforcedLeray.B0220.measureH c] (fun p => NearInst.merC (f (NearInst.cellPt c p)))

/-- Source 1650-1656: `R₀ = (μ - A₀)⁻¹P₀` maps into the flat solenoidal subspace
(the range of `P₀` is invariant under `A₀`, hence under its resolvent). -/
def FlatResSol : Prop :=
  ∀ (c ν : ℝ) (hc : 0 < c) (μ : ℂ), 0 < ν → 0 < μ.re + 1 / 4 →
    ∀ f : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC,
      UnforcedLeray.Short.PartIIa.T0flat hc ν μ f ∈ UnforcedLeray.Short.PartIIa.solenoidalHC 0 c

/-- Chart dictionary (source 1650-1656): `h ∈ solenoidalHC 0 c` representing the chart field
`f ∈ Hsp c`, and `b` a smooth representative of `f`, give `∫ χ(s) divPairing c b ψ s ds = 0`
for `χ ∈ C_c^∞((0,∞))` and cylinder tests `ψ` (test `Φ = χ ⊗ ψ`, `cgrad 0 Φ = (D₀Φ, ∂_ηΦ)`,
Fubini on the cell with weight `s^{-3/2}`). -/
def FlatSolPair : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (f : Hsp c) (h : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC),
    (h : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
        =ᵐ[UnforcedLeray.B0220.measureH c] (fun p => NearInst.merC (f (NearInst.cellPt c p))) →
    h ∈ UnforcedLeray.Short.PartIIa.solenoidalHC 0 c →
    ∀ b : Chart → Fin 2 → ℂ, SmoothRep c b → b =ᵐ[ageμ c (-3 / 2)] NearInst.velC f →
      ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ Ioi (0 : ℝ) →
        ∀ ψ, B0579.IsCylTest c ψ → ∫ s, χ s • divPairing c b ψ s = 0

theorem sfcDivWeak_of (hL : FlatLift) (hR : FlatResSol) (hP : FlatSolPair) : SFCDivWeak := by
  intro c ν μ hc R0 g hctx b hb hbe χ h1 h2 h3 ψ hψ
  obtain ⟨hν, hμ, hT, -⟩ := hctx
  obtain ⟨g', hg'⟩ := hL c hc g
  have hμ' : 0 < ((μ : ℂ)).re + 1 / 4 := by simpa using hμ
  have hmem' : UnforcedLeray.Short.PartIIa.T0flat hc ν (μ : ℂ) g'
      ∈ UnforcedLeray.Short.PartIIa.solenoidalHC 0 c := hR c ν hc (μ : ℂ) hν hμ' g'
  have hrep := hT g g' hg'
  exact hP c hc (R0 g) _ hrep hmem' b hb hbe χ h1 h2 h3 ψ hψ

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
