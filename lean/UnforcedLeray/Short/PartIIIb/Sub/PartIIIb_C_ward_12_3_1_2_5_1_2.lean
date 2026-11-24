import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellBoundedConvection

/-!
# `PartIII-b:C/ward/12/3/1/2/5/1/2` (decomposition): `InletIBPIdentity`

Source `the November 2 reference manuscript`
lines 2385-2387 (inlet integration by parts), 1206-1222 (bounds on `raw`), 5283-5295 (the inlet
column `E_i`, smooth and `period`-periodic).

For `ψ = ∂_jΦ` a phase test: `⟨L₀ᵗψ,E⟩ = ⟨ψ,L₀E⟩` (`InletL0Transpose`); by the bounded
solenoidal convection identity `⟨convT raw ψ,E⟩ = -⟨(E·∇)ψ,raw⟩ - ⟨(raw·∇)ψ,E⟩`
(`InletBackgroundBounds`), and `div E = div raw = 0` gives `-⟨(E·∇)ψ,raw⟩ = ⟨ψ,(E·∇)raw⟩`
(`InletAdvTranspose1`), `-⟨(raw·∇)ψ,E⟩ = ⟨ψ,(raw·∇)E⟩` (`InletAdvTranspose2`); the pairing with
`inletSrc` splits (`InletPairSplit`), and `y_j`-integration by parts (`InletYIBP`) gives `inletFn`.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.PhaseSpace MeasureTheory Set
open UnforcedLeray.Cons.C03.Concrete (Params IsSolTest pairF convT advT rep)
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Field regularity** (1206-1222, 5283-5295): `E_i` and `raw` are jointly smooth, `E_i` is
`period`-periodic in the phase, and both are pointwise solenoidal in `y`. -/
def InletFieldRegular : Prop := GERegime fun p _ _ =>
  ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => UnforcedLeray.B0412.realC (p.raw x.1 x.2)) ∧
  (∀ x, ∑ k : Fin 3, dy k (fun x : ℝ × UnforcedLeray.Space =>
      UnforcedLeray.B0412.realC (p.raw x.1 x.2)) x k = 0) ∧
  ∀ i : Fin 2, ContDiff ℝ ∞ (p.Efun i) ∧ (∀ x : ℝ × UnforcedLeray.Space, p.Efun i (x.1 + p.period, x.2) = p.Efun i x) ∧
    (∀ x, ∑ k : Fin 3, dy k (p.Efun i) x k = 0)

/-- **Bounded backgrounds** (1206-1222, 5283-5295): `raw` and `inlet i` are bounded backgrounds
(`UnforcedLeray.Blueprint.IsBoundedBackground`) and `inlet i τ` is solenoidal. -/
def InletBackgroundBounds : Prop := GERegime fun p _ _ =>
  UnforcedLeray.Blueprint.IsBoundedBackground p.raw ∧ ∀ i : Fin 2,
    UnforcedLeray.Blueprint.IsBoundedBackground (p.inlet i) ∧
      ∀ τ, UnforcedLeray.IsSolenoidal (p.inlet i τ)

/-- **`L₀ᵗ` is the transpose of `L₀`** against `E_i` (smooth, periodic; compact `y`-support of
the test; via `ibpAdjoint_proved` with `μ = 0`). -/
def InletL0Transpose : Prop := GERegime fun p _ _ =>
  ∀ (i : Fin 2) (ψ : ℝ × UnforcedLeray.Space → CVec3), IsPhaseTest p.period ψ →
    pairF p.period (UnforcedLeray.B0411.L0T p.ν ψ) (p.Efun i) =
      pairF p.period ψ (UnforcedLeray.B0411.L0 p.ν (p.Efun i))

/-- **Transport transposition 1** (`div E_i = 0`, `y`-integration by parts, compact support):
`⟨(E·∇)ψ, raw⟩ = -⟨ψ, (E·∇)raw⟩`. -/
def InletAdvTranspose1 : Prop := GERegime fun p _ _ =>
  ∀ (i : Fin 2) (ψ : ℝ × UnforcedLeray.Space → CVec3), IsPhaseTest p.period ψ →
    pairF p.period (advT (p.Efun i) ψ)
        (fun x => UnforcedLeray.B0412.realC (p.raw x.1 x.2)) =
      -pairF p.period ψ (gradAlong p.raw (p.Efun i))

/-- **Transport transposition 2** (`div raw = 0`, `y`-integration by parts, compact support):
`⟨(raw·∇)ψ, E⟩ = -⟨ψ, (raw·∇)E⟩`. -/
def InletAdvTranspose2 : Prop := GERegime fun p _ _ =>
  ∀ (i : Fin 2) (ψ : ℝ × UnforcedLeray.Space → CVec3), IsPhaseTest p.period ψ →
    pairF p.period
        (advT (fun x => UnforcedLeray.B0412.realC (p.raw x.1 x.2)) ψ) (p.Efun i) =
      -pairF p.period ψ
        (advT (fun x => UnforcedLeray.B0412.realC (p.raw x.1 x.2)) (p.Efun i))

/-- **Linearity of the pairing** with the (smooth) pieces of `inletSrc`: a phase test `ψ` is
compactly `y`-supported and the three pieces are continuous, so all pairings converge. -/
def InletPairSplit : Prop := GERegime fun p _ _ =>
  ∀ (i : Fin 2) (ψ : ℝ × UnforcedLeray.Space → CVec3), IsPhaseTest p.period ψ →
    pairF p.period ψ (inletSrc p i) =
      pairF p.period ψ (UnforcedLeray.B0411.L0 p.ν (p.Efun i)) +
      pairF p.period ψ
        (advT (fun x => UnforcedLeray.B0412.realC (p.raw x.1 x.2)) (p.Efun i)) +
      pairF p.period ψ (gradAlong p.raw (p.Efun i))

/-- **`y_j`-integration by parts** (no boundary terms: compact `y`-support of `Φ`; `inletSrc`
smooth): `⟨∂_jΦ, inletSrc⟩ = ⟨Φ, -∂_j inletSrc⟩ = ⟨Φ, inletFn⟩`. -/
def InletYIBP : Prop := GERegime fun p _ _ =>
  ∀ (i : Fin 2) (j : Fin 3) (Φ : ℝ × UnforcedLeray.Space → CVec3), IsPhaseTest p.period Φ →
    pairF p.period (dy j Φ) (inletSrc p i) = pairF p.period Φ (inletFn p i j)

theorem inletIBPIdentity_of (h0 : InletBackgroundBounds) (h1 : InletL0Transpose)
    (h2 : InletAdvTranspose1) (h3 : InletAdvTranspose2) (h4 : InletPairSplit)
    (h5 : InletYIBP) : InletIBPIdentity := by
  intro lam q hq dm dp hdm
  obtain ⟨ν₀, hν₀, H0⟩ := h0 lam q hq dm dp hdm
  obtain ⟨ν₁, hν₁, H1⟩ := h1 lam q hq dm dp hdm
  obtain ⟨ν₂, hν₂, H2⟩ := h2 lam q hq dm dp hdm
  obtain ⟨ν₃, hν₃, H3⟩ := h3 lam q hq dm dp hdm
  obtain ⟨ν₄, hν₄, H4⟩ := h4 lam q hq dm dp hdm
  obtain ⟨ν₅, hν₅, H5⟩ := h5 lam q hq dm dp hdm
  refine ⟨min ν₀ (min ν₁ (min ν₂ (min ν₃ (min ν₄ ν₅)))), lt_min hν₀ (lt_min hν₁ (lt_min hν₂
    (lt_min hν₃ (lt_min hν₄ hν₅)))), fun p d hreg hν hm z g hg i j _ Φ hΦ => ?_⟩
  have hν' : p.ν ≤ ν₀ := hν.trans (min_le_left _ _)
  have hν1 : p.ν ≤ ν₁ := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν2 : p.ν ≤ ν₂ := hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    (min_le_left _ _)))
  have hν3 : p.ν ≤ ν₃ := hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))))
  have hν4 : p.ν ≤ ν₄ := hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have hν5 : p.ν ≤ ν₅ := hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
  obtain ⟨hraw, hE⟩ := H0 p d hreg hν' hm z g hg
  have hψ : IsPhaseTest p.period (dy j Φ) := hΦ.1.dy j
  have hconv := UnforcedLeray.Cons.C03.Concrete.pairF_convT_boundedSolenoidal_convection_identity
    (P := p.period) hψ hraw (hE i).1 (hE i).2
  have e1 := H1 p d hreg hν1 hm z g hg i (dy j Φ) hψ
  have e2 := H2 p d hreg hν2 hm z g hg i (dy j Φ) hψ
  have e3 := H3 p d hreg hν3 hm z g hg i (dy j Φ) hψ
  have e4 := H4 p d hreg hν4 hm z g hg i (dy j Φ) hψ
  have e5 := H5 p d hreg hν5 hm z g hg i j Φ hΦ.1
  have hconv' : pairF p.period (convT p.raw (dy j Φ)) (p.Efun i) +
      pairF p.period (advT (p.Efun i) (dy j Φ))
        (fun x => UnforcedLeray.B0412.realC (p.raw x.1 x.2)) +
      pairF p.period (advT (fun x => UnforcedLeray.B0412.realC (p.raw x.1 x.2)) (dy j Φ))
        (p.Efun i) = 0 := hconv
  rw [e1]
  linear_combination hconv' - e2 - e3 - e4 + e5

end UnforcedLeray.Short.PartIIIb.Concrete
