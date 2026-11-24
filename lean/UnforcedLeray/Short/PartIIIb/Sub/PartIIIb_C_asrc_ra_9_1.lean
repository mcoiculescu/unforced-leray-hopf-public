import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9

/-!
# `PartIII-b:C/asrc/ra/9/1` : decomposition of `rAGeoD` (source 5034-5039, 4979-4980)

`RAGeoPieceBound` splits into (i) the support / measurability part (`GeoPieceMeas`) and (ii) the
cell `L²` bound (`GeoPieceL2`, the ring-chart remainder `ε s G` of source 5034-5039, normalized
cell norm `≤ P_ν M(A)(s^{3/2}+s^{5/2})`).  `raGeoPieceBound_of` recombines them.
Source of record: `the November 2 reference manuscript` (73 pages).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest Params)

/-- Support and measurability part of `RAGeoPieceBound` (source 5034-5039: `A^y = 0` for
`s > 1.1/ν`, sections continuous off the lattice sums). -/
def GeoPieceMeas (as : ℝ) (χf : ℝ → ℝ) (g : Params → ℝ → (ℝ → Mat3) → Chart → Merid) : Prop :=
  IsSourceCutoffC χf → ∀ K : Set ℝ, IsCompact K → K ⊆ Ioo 0 (1 / 4) → ∀ dm dp : ℝ, 0 < dm →
    ∃ ν₀ : ℝ, 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ μ ∈ K, ∀ A : ℝ → Mat3, IsAffElem as A →
        AEStronglyMeasurable (g p μ A) (srcMeasure p.c) ∧
        (∀ s : ℝ, (11 / 10) / p.ν < s → ∀ x : ℝ × ℝ, g p μ A (s, x) = 0) ∧
        (∀ s : ℝ, 0 < s →
          AEStronglyMeasurable (fun x : ℝ × ℝ => g p μ A (s, x)) (UnforcedLeray.Cyl.avgμ p.c))

/-- The cell `L²` bound part of `RAGeoPieceBound` (source 5034-5039, Gaussian summation). -/
def GeoPieceL2 (as : ℝ) (χf : ℝ → ℝ) (g : Params → ℝ → (ℝ → Mat3) → Chart → Merid) : Prop :=
  IsSourceCutoffC χf → ∀ K : Set ℝ, IsCompact K → K ⊆ Ioo 0 (1 / 4) → ∀ dm dp : ℝ, 0 < dm →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ μ ∈ K, ∀ A : ℝ → Mat3, IsAffElem as A →
        ∀ s : ℝ, 0 < s → s ≤ (11 / 10) / p.ν →
          ∫⁻ x, ENNReal.ofReal (‖g p μ A (s, x)‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ p.c)
            ≤ ENNReal.ofReal ((C * p.ν⁻¹ ^ k * p.ε * affM p.ν χf A *
                (s ^ (5 / 2 : ℝ) + s ^ (7 / 2 : ℝ))) ^ 2)

theorem raGeoPieceBound_of {as : ℝ} {χf : ℝ → ℝ}
    {g : Params → ℝ → (ℝ → Mat3) → Chart → Merid}
    (hM : GeoPieceMeas as χf g) (hL : GeoPieceL2 as χf g) : RAGeoPieceBound as χf g := by
  intro hχ K hK hKs dm dp hdm
  obtain ⟨ν₁, h1, H1⟩ := hM hχ K hK hKs dm dp hdm
  obtain ⟨C, k, ν₂, h2, H2⟩ := hL hχ K hK hKs dm dp hdm
  refine ⟨C, k, min ν₁ ν₂, lt_min h1 h2, fun p d hreg hν μ hμ A hA => ?_⟩
  obtain ⟨a, b, c⟩ := H1 p d hreg (hν.trans (min_le_left _ _)) μ hμ A hA
  exact ⟨a, b, c, H2 p d hreg (hν.trans (min_le_right _ _)) μ hμ A hA⟩

/-- **Lemma 1** (measurability and support of the `D_μ` piece). -/
def GeoDMeas (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  GeoPieceMeas as χf (fun p μ A => geoDPiece p μ χf A)

/-- **Lemma 2** (cell `L²` bound of the `D_μ` ring-chart remainder, source 5034-5039). -/
def GeoDL2 (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  GeoPieceL2 as χf (fun p μ A => geoDPiece p μ χf A)

theorem rAGeoD_of (as : ℝ) (χf : ℝ → ℝ) (h1 : GeoDMeas as χf) (h2 : GeoDL2 as χf) :
    RAGeoDLeaf as χf :=
  raGeoPieceBound_of h1 h2

end UnforcedLeray.Short.PartIIIb.Concrete
