import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_4
import UnforcedLeray.Cons.L2.BackgroundConcrete.PhasePairF

/-!
# Part II-b, task `PartII-b:G4/4/1` (`InletSourcePtw`): decomposition

Source of record: `the November 2 reference manuscript`, lines 2370-2383.

`InletSourcePtw` is split into one analytic core, stated for pointwise fields on `ℝ × ℝ³`
(`InletSourceFields`), and three packaging leaves which turn pointwise fields into elements of
`Y_{q₀}` (`YqOfFields`, `YqRealSymm`, `YqOSymm`).  The ae-congruence of the pairing is proved here.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint UnforcedLeray.PhaseSpace
  UnforcedLeray.B0411 UnforcedLeray.B0412

/-- `W` is a jointly measurable representative of `F ∈ Y_q` (as `B0424.IsRep`). -/
structure HasRep {P : ℝ} [Fact (0 < P)] (F : Yq P q0E) (W : ℝ × Space → CVec3) : Prop where
  meas : AEStronglyMeasurable W volume
  slice : ∀ᵐ τ : ℝ, (fun y => W (τ, y)) =ᵐ[volume] (F (τ : AddCircle P) : Space → CVec3)

/-- **Analytic core** (SP 2370-2383): the unprojected inlet source `(L_0 + B_{V_0})E_i`, as a
pointwise field `Fp` on `ℝ × ℝ³` (smooth, supported in `s ≤ Σ/ν`, by `FrozenStreamBounds` and the
ring-lift calculus), with weak gradients `Gp j`: `IsInYr` for exponent `p = 11/4`, the identity with
`pairF` on solenoidal phase tests (integration by parts, `Params.OrdRel` inlet part), `𝒪`-symmetry
and realness pointwise, and `‖Fp‖ + ∑ⱼ‖Gp j‖ ≤ C ν^{-k} R^{2/p}` (Jacobian `πR²`, `phaseLpNorm_NvC`,
`NvFderivBound`). -/
def InletSourceFields : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Planar.Profile), 0 < Sig → Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∀ i : Fin 2, ∃ (Fp : ℝ × Space → CVec3) (Gp : Fin 3 → ℝ × Space → CVec3),
        IsInYr p.period bgp Fp ∧ (∀ j, IsInYr p.period bgp (Gp j)) ∧
        (∀ x, ∃ r : Space, Fp x = realC r) ∧
        (∀ g : Space ≃ₗᵢ[ℝ] Space, UnforcedLeray.FixesAxis g → ∀ τ y,
          gC g (Fp (τ, g.symm y)) = Fp (τ, y)) ∧
        (∀ Φ, IsSolTest p.period Φ →
          pairF p.period (fun x => L0T p.ν Φ x + convT p.raw Φ x) (p.Efun i) =
            pairF p.period Φ Fp) ∧
        (∀ j : Fin 3, HasPtwOp p.period (fun Φ x => -(dy j Φ x)) Fp (Gp j)) ∧
        (phaseLpNorm p.period bgp Fp).toReal +
            ∑ j : Fin 3, (phaseLpNorm p.period bgp (Gp j)).toReal ≤
          C * (p.ν ^ k)⁻¹ * p.R ^ (2 / bgp)

/-- **Packaging leaf**: a field in `Y_p` (`p = 11/4 = q₀`) is represented by an element of
`Y_{q₀}` with the same norm (Fubini isometry `Y_q ≃ L^q(ℝ/Pℤ × ℝ³)`, `B0424`/`B0449`). -/
def YqOfFields : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (W : ℝ × Space → CVec3), IsInYr P bgp W →
    ∃ F : Yq P q0E, HasRep F W ∧ ‖F‖ = (phaseLpNorm P bgp W).toReal

/-- **Packaging leaf**: an element of `Y_{q₀}` represented by a pointwise real field is in
`realSub` (pair with a real phase test: the integrand is real). -/
def YqRealSymm : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (F : Yq P q0E) (W : ℝ × Space → CVec3), HasRep F W →
    (∀ x, ∃ r : Space, W x = realC r) → F ∈ realSub P q0E

/-- **Packaging leaf**: an element of `Y_{q₀}` represented by a pointwise `𝒪`-invariant field is
in `Osym` (`isOInvariant_iff`, `B0412/Action.lean`). -/
def YqOSymm : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (F : Yq P q0E) (W : ℝ × Space → CVec3), HasRep F W →
    (∀ g : Space ≃ₗᵢ[ℝ] Space, UnforcedLeray.FixesAxis g → ∀ τ y,
      gC g (W (τ, g.symm y)) = W (τ, y)) → F ∈ Osym P q0E

/-- The pairing against a representative depends only on the a.e. class. -/
theorem pairF_rep_eq (P : ℝ) [Fact (0 < P)] (F : Yq P q0E) (W : ℝ × Space → CVec3)
    (hW : HasRep F W) (Φ : ℝ × Space → CVec3) :
    pairF P Φ (fun x => rep F x.1 x.2) = pairF P Φ W := by
  unfold pairF phaseInt
  congr 1
  have h1 : ∀ᵐ τ : ℝ, (fun y => W (τ, y)) =ᵐ[volume] (F (τ : AddCircle P) : Space → CVec3) :=
    hW.slice
  have h2 : ∀ᵐ τ : ℝ, ∫ y, dotL (Φ (τ, y)) (rep F τ y) = ∫ y, dotL (Φ (τ, y)) (W (τ, y)) := by
    filter_upwards [h1] with τ hτ
    apply integral_congr_ae
    filter_upwards [hτ, rep_slice F τ] with y hy1 hy2
    rw [← hy1] at hy2
    rw [hy2]
  exact setIntegral_congr_ae measurableSet_Ioc (by
    filter_upwards [h2] with τ hτ _ using hτ)

/-- **Conditional assembly** of `InletSourcePtw`. -/
theorem inletSourcePtw_of (h1 : InletSourceFields) (h2 : YqOfFields) (h3 : YqRealSymm)
    (h4 : YqOSymm) : InletSourcePtw := by
  intro Sig lam q hSig hq dm dp hdm
  obtain ⟨C, k, ν₀, hC, hν₀, hP⟩ := h1 Sig lam q hSig hq dm dp hdm
  refine ⟨C, k, ν₀, hC, hν₀, ?_⟩
  intro p d hreg hν hSig' hmode i
  obtain ⟨Fp, Gp, hFp, hGp, hreal, hO, hid, hgr, hn⟩ := hP p d hreg hν hSig' hmode i
  obtain ⟨F, hFrep, hFn⟩ := h2 p.period Fp hFp
  have hG : ∀ j, ∃ G : Yq p.period q0E, HasRep G (Gp j) ∧
      ‖G‖ = (phaseLpNorm p.period bgp (Gp j)).toReal := fun j => h2 p.period (Gp j) (hGp j)
  choose G hGrep hGn using hG
  refine ⟨F, G, h3 p.period F Fp hFrep hreal, h4 p.period F Fp hFrep hO, ?_, ?_, ?_⟩
  · intro Φ hΦ
    rw [phasePair_eq_pairF_rep hΦ.1 F, pairF_rep_eq p.period F Fp hFrep, ← hid Φ hΦ]
  · intro j Φ hΦ
    rw [pairF_rep_eq p.period F Fp hFrep, pairF_rep_eq p.period (G j) (Gp j) (hGrep j)]
    exact hgr j Φ hΦ
  · rw [hFn]
    simpa [hGn] using hn

end UnforcedLeray.Short.IIb
