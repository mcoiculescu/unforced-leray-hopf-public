import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3.Defs

/-!
# `BodyColumnWeak` from six source facts (organizer task `PartIII-b:C/flatset/col/7/3/org`)

Source of record `the November 2 reference manuscript`: 1650-1656
(`T₀ = (μ - A₀)⁻¹P₀`, `A₀ = -S + νsΔ`), 1684-1689 (flat equation, pairing).

With `h' = merC ∘ h ∘ cellPt` and `ζ = s^{1/2}Φ` (`zetaPhi Φ`, a divergence-free test of `H`):
`T₀flat h' = R₀(μ)P₀h'` and `⟨R₀(μ)P₀h', (μ - A₀*)ζ⟩_H = ⟨P₀h', ζ⟩_H = ⟨h', ζ⟩_H`
(`P₀ ζ = ζ`, `P₀` self-adjoint), while the left side minus `⟨h', ζ⟩_H` is the space-time integral
`∫ forcedIntegrand` (weights `s^{-3/2}`, `h = s f`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate InnerProductSpace

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.IIIa (IsFlatTest)
open UnforcedLeray.Short.PartIIa (IsMeridTest PepsC T0flat solenoidalHC)

/-- **Complex lift** (source 1641-1646): every `h ∈ Hsp c` has a representative `h' ∈ H` with
`h' = merC ∘ h ∘ cellPt` a.e. (`NearInst.Body.cplxH_ae` with `cpcH_eq`). -/
def CplxLift : Prop :=
  ∀ c : ℝ, 0 < c → ∀ h : Hsp c, ∃ h' : HSpace c MeridC,
    (h' : Profile → MeridC) =ᵐ[measureH c] fun p => NearInst.merC (h (NearInst.cellPt c p))

/-- **Transpose identity of the causal resolvent** (source 1650-1656, `B0225.R0` is the Laplace
transform of `T₀`, `B0224.T0adj_apply_ae`): for a smooth test `ζ`,
`⟨R₀(μ)g, (μ - A₀*)ζ⟩_H = ⟨g, ζ⟩_H`.  Route: `⟨T₀(t)g, ζ⟩ = ⟨g, T₀(t)*ζ⟩` has `t`-derivative
`⟨T₀(t)g, A₀*ζ⟩` (differentiate `e^{-t/2}e^{νs(eᵗ-1)Δ}ζ(seᵗ)`), integrate by parts against
`e^{-μt}` (`‖T₀(t)‖ = e^{-t/4}`, `Re μ + 1/4 > 0`). -/
def R0TransposeIdentity : Prop :=
  ∀ (c ν μ : ℝ) (hc : 0 < c), 0 < ν → 0 < μ + 1 / 4 → ∀ (g : HSpace c MeridC)
    (ζ : Profile → MeridC), IsMeridTest c ζ →
    pairH c (UnforcedLeray.B0225.R0 hc ν (μ : ℂ) g : Profile → MeridC) (resolventTest ν μ ζ) =
      pairH c (g : Profile → MeridC) ζ

/-- `s^{1/2}Φ` is a smooth `c`-periodic profile supported in an age band (`Φ` vanishes for
`s < s₁`, `s₁ > 0`, so `√s` is smooth on the support). -/
def ZetaPhiMeridTest : Prop :=
  ∀ c : ℝ, 0 < c → ∀ Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ, IsFlatTest c Φ → IsMeridTest c (zetaPhi Φ)

/-- `s^{1/2}Φ` is a class of `H` lying in the exact solenoidal subspace `solenoidalHC 0 c`: it is
orthogonal to `cgrad 0 ψ = (∂_qψ, ∂_ηψ)` for every profile test `ψ`, since
`⟨ζ_Φ, cgrad ψ⟩_H = ∫ s^{-1}(Φ·∇ψ) ds dq dη = 0` (`div Φ(s) = 0`, integrate by parts in the
cell, `q`-periodicity, compact `η`-support). -/
def ZetaPhiSolenoidal : Prop :=
  ∀ c : ℝ, 0 < c → ∀ Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ, IsFlatTest c Φ →
    ∃ ζ' : HSpace c MeridC, ζ' ∈ solenoidalHC 0 c ∧
      (ζ' : Profile → MeridC) =ᵐ[measureH c] zetaPhi Φ

/-- **Integrability of the tested integrand** (weights unwound: `ζ_Φ`, `(μ - A₀*)ζ_Φ` are bounded,
supported in `s ∈ [s₁, s₂]`, `|η| ≤ L`; `b`, `f = h/s` are `L²` there). -/
def WeakPairIntegrable : Prop :=
  ∀ (c ν μ : ℝ), 0 < c → ∀ Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ, IsFlatTest c Φ →
    ∀ (f : Chart → Fin 2 → ℂ) (h vR : Hsp c) (h' B : HSpace c MeridC),
      (h' : Profile → MeridC) =ᵐ[measureH c] (fun p => NearInst.merC (h (NearInst.cellPt c p))) →
      (B : Profile → MeridC) =ᵐ[measureH c] (fun p => NearInst.merC (vR (NearInst.cellPt c p))) →
      (∀ᵐ p ∂(ageμ c (-3 / 2)), ∀ i, NearInst.velC h p i = (p.1 : ℂ) * f p i) →
      IntegrableOn (forcedIntegrand ν (μ : ℂ) (fun _ _ _ => 0) f (NearInst.velC vR) Φ)
        (Ioi (0 : ℝ) ×ˢ B0579.cell c)

/-- **Weight unwinding** (source 1684-1689; `IIb.ageμ_eq_withDensity`, `s^{-3/2}ds`; `cellPt`
change of variables `CellPtH`): the space-time integral of `forcedIntegrand` equals
`⟨B, (μ - A₀*)ζ_Φ⟩_H - ⟨h', ζ_Φ⟩_H`, because
`(μ - A₀*)ζ_Φ = s^{1/2}(μΦ - sΦ_s - νsΔΦ)`, `s^{-3/2}s^{1/2} = s^{-1}`, and `h = s f`. -/
def WeakPairValue : Prop :=
  ∀ (c ν μ : ℝ), 0 < c → ∀ Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ, IsFlatTest c Φ →
    ∀ (f : Chart → Fin 2 → ℂ) (h vR : Hsp c) (h' B : HSpace c MeridC),
      (h' : Profile → MeridC) =ᵐ[measureH c] (fun p => NearInst.merC (h (NearInst.cellPt c p))) →
      (B : Profile → MeridC) =ᵐ[measureH c] (fun p => NearInst.merC (vR (NearInst.cellPt c p))) →
      (∀ᵐ p ∂(ageμ c (-3 / 2)), ∀ i, NearInst.velC h p i = (p.1 : ℂ) * f p i) →
      ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
          forcedIntegrand ν (μ : ℂ) (fun _ _ _ => 0) f (NearInst.velC vR) Φ p =
        pairH c (B : Profile → MeridC) (resolventTest ν μ (zetaPhi Φ)) -
          pairH c (h' : Profile → MeridC) (zetaPhi Φ)

/-- `⟨u, w⟩_H = ⟪ζ', u⟫` for `ζ' = w` a.e. -/
theorem pairH_eq_inner {c : ℝ} (u ζ' : HSpace c MeridC) {w : Profile → MeridC}
    (hw : (ζ' : Profile → MeridC) =ᵐ[measureH c] w) :
    pairH c (u : Profile → MeridC) w = inner ℂ ζ' u := by
  rw [MeasureTheory.L2.inner_def]
  unfold pairH
  refine integral_congr_ae ?_
  filter_upwards [hw] with p hp
  rw [hp]

theorem bodyColumnWeak_of (hL : CplxLift) (hT : R0TransposeIdentity) (hM : ZetaPhiMeridTest)
    (hS : ZetaPhiSolenoidal) (hI : WeakPairIntegrable) (hV : WeakPairValue) :
    BodyColumnWeak := by
  intro c ν μ hc hν hμ R0 hR h f hhf Φ hΦ
  obtain ⟨h', hh'⟩ := hL c hc h
  have hB := hR h h' hh'
  refine ⟨hI c ν μ hc Φ hΦ f h (R0 h) h' _ hh' hB hhf, ?_⟩
  rw [hV c ν μ hc Φ hΦ f h (R0 h) h' _ hh' hB hhf]
  obtain ⟨ζ', hζmem, hζae⟩ := hS c hc Φ hΦ
  have hBdef : T0flat hc ν (μ : ℂ) h' =
      UnforcedLeray.B0225.R0 hc ν (μ : ℂ) (PepsC 0 c h') := rfl
  rw [hBdef, hT c ν μ hc hν hμ (PepsC 0 c h') (zetaPhi Φ) (hM c hc Φ hΦ),
    pairH_eq_inner _ ζ' hζae, pairH_eq_inner _ ζ' hζae, sub_eq_zero]
  unfold PepsC
  rw [← Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.2 hζmem]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
