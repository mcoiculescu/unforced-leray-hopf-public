import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Basic

/-!
# `TepsWeakSol` decomposed (task `PartIII-b:C/near/pins/3`)

Source `the November 2 reference manuscript`: 1675-1677 (`T_ε = (μ - A_ε)⁻¹P_ε`),
1339-1362 (free Cartesian equation `L = 𝒯 - νΔ - 1/2`), 4139-4146 (`D_μ`, `R_μ`).

`T_ε = RepsVec ∘ PepsC` (`PartIIa.Teps`).  The target splits into the Leray part (`PepsC h'` has a
real chart form `wk`, which is weakly solenoidal, and agrees with `f` on solenoidal tests) and the
resolvent part (`RepsVec z` solves the weak equation against `z` on every solenoidal test, and is
weakly solenoidal when `z` is).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)

/-- `h ∈ H` has real chart form `f` (the representation hypothesis of `TepsWeakSol`). -/
def ChartRep (c : ℝ) (h : HSpace c MeridC) (f : Chart → Merid) : Prop :=
  (h : Profile → MeridC) =ᵐ[measureH c] (fun q => merC (f (cellPt c q)))

/-- **Real form of the Leray image** (source 1675-1676, 1686-1689): `P_ε` is the conjugated real
Cartesian Leray projection, so it preserves real chart forms. -/
def PepsRealForm : Prop :=
  ∀ (p : Params) (f : Chart → Merid) (h' : HSpace p.c MeridC), ChartRep p.c h' f →
    ∃ wk : Chart → Merid,
      ChartRep p.c (UnforcedLeray.Short.PartIIa.PepsC p.ε p.c h') wk

/-- **The Leray image is weakly solenoidal** (source 1675-1677; `B0226.Peps_eq_starProjection`:
`P_ε` is the projection onto the orthogonal complement of the lifted gradients). -/
def PepsSolenoidal : Prop :=
  ∀ (p : Params) (z : HSpace p.c MeridC) (wk : Chart → Merid),
    ChartRep p.c (UnforcedLeray.Short.PartIIa.PepsC p.ε p.c z) wk →
      IsWeakSolenoidal (2 * p.ε * p.c) (velPhys p.ε⁻¹ p.c wk)

/-- **`ℙ` is invisible on solenoidal tests** (source 1675-1677, 4139-4146): `P_ε h'` and `h'` have
the same pairing with every solenoidal phase test. -/
def PepsLerayInvisible : Prop :=
  ∀ (p : Params) (f : Chart → Merid) (h' : HSpace p.c MeridC) (wk : Chart → Merid),
    ChartRep p.c h' f → ChartRep p.c (UnforcedLeray.Short.PartIIa.PepsC p.ε p.c h') wk →
      ∀ Φ : ℝ × Space → CVec3, IsSolTest (2 * p.ε * p.c) Φ →
        pairF (2 * p.ε * p.c) Φ (velPhys p.ε⁻¹ p.c wk) =
          pairF (2 * p.ε * p.c) Φ (velPhys p.ε⁻¹ p.c f)

/-- **Weak resolvent equation** (source 1339-1362, 1675-1677, 4139-4146): the lift of
`R_ε^vec(μ) z` satisfies `⟨D_μᵗΦ, 𝒩_v w⟩ = ⟨Φ, 𝒩_v z⟩` on every solenoidal phase test
(`J_RepsVec`, `RepsVec_right`, outer generator identity, `liftVec` ↔ `velPhys` dictionary). -/
def RepsVecEquation : Prop :=
  ∀ (p : Params) (μ : ℝ), p.period ≤ 1 → -(1 / 4) < μ → ∀ (γ : ℝ) (z : HSpace p.c MeridC)
    (wz : Chart → Merid) (w : VelG p.c γ p.ν),
    ChartRep p.c z wz →
    ChartRep p.c (UnforcedLeray.B0223.RepsVec (P := p.period) p.ν_pos p.ε_pos p.c_pos rfl
      (μ : ℂ) z) (w : Chart → Merid) →
    ∀ Φ : ℝ × Space → CVec3, IsSolTest (2 * p.ε * p.c) Φ →
      pairF (2 * p.ε * p.c) (fun x => L0T p.ν Φ x + (μ : ℂ) • Φ x) (velPhys p.ε⁻¹ p.c w) =
        pairF (2 * p.ε * p.c) Φ (velPhys p.ε⁻¹ p.c wz)

/-- **The resolvent preserves weak solenoidality** (the heat-OU semigroup acts componentwise and
commutes with `∇`; source 1339-1362, 4139-4146). -/
def RepsVecSolenoidal : Prop :=
  ∀ (p : Params) (μ : ℝ), p.period ≤ 1 → -(1 / 4) < μ → ∀ (γ : ℝ) (z : HSpace p.c MeridC)
    (wz : Chart → Merid) (w : VelG p.c γ p.ν),
    ChartRep p.c z wz →
    ChartRep p.c (UnforcedLeray.B0223.RepsVec (P := p.period) p.ν_pos p.ε_pos p.c_pos rfl
      (μ : ℂ) z) (w : Chart → Merid) →
    IsWeakSolenoidal (2 * p.ε * p.c) (velPhys p.ε⁻¹ p.c wz) →
      IsWeakSolenoidal (2 * p.ε * p.c) (velPhys p.ε⁻¹ p.c w)

theorem tepsWeakSol_of (h1 : PepsRealForm) (h2 : PepsSolenoidal) (h3 : PepsLerayInvisible)
    (h4 : RepsVecEquation) (h5 : RepsVecSolenoidal) : TepsWeakSol := by
  intro p μ hP hμ γ f h' w hf hw
  obtain ⟨wk, hwk⟩ := h1 p f h' hf
  have hw' : ChartRep p.c (UnforcedLeray.B0223.RepsVec (P := p.period) p.ν_pos p.ε_pos p.c_pos
      rfl (μ : ℂ) (UnforcedLeray.Short.PartIIa.PepsC p.ε p.c h')) (w : Chart → Merid) := hw
  refine ⟨h5 p μ hP hμ γ _ wk w hwk hw' (h2 p h' wk hwk), fun Φ hΦ => ?_⟩
  rw [h4 p μ hP hμ γ _ wk w hwk hw' Φ hΦ]
  exact h3 p f h' wk hf hwk Φ hΦ

end UnforcedLeray.Short.PartIIIb.NearInst
