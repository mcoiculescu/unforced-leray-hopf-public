import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_4_1

/-!
# Part II-b, task `PartII-b:G4/4/1/1` (`InletSourceFields`): concrete fields and decomposition

Source of record: `the November 2 reference manuscript`, lines 2355-2383
(`short-bg:affine`, second inequality: the complete unprojected source
`(L_0 + B_{V_0}) E_i` of the inlet column, `E_i = Params.Efun i`, `V_0 = Params.raw`).

`inletSourceF p i` is the source written out pointwise, `inletSourceG p i j` its spatial
derivative; the statement `InletSourceFields` is then proved from six pieces.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint UnforcedLeray.PhaseSpace
  UnforcedLeray.B0411 UnforcedLeray.B0412

/-- **The unprojected inlet source** `(L_0 + B_{V_0}) E_i` as a pointwise field (SP 2370-2383):
`L_0 E = ∂_τ E - ½ y·∇E - νΔE - ½E` (`T_0 = ∂_τ - ½ y·∇`, `L_0 = T_0 - νΔ - ½`) and
`B_V E = V·∇E + (E·∇)V` with `V = p.raw`, `E = p.Efun i`. -/
def inletSourceF (p : Params) (i : Fin 2) : ℝ × Space → CVec3 := fun x =>
  dτ (p.Efun i) x - (1 / 2 : ℝ) • radialT (p.Efun i) x - p.ν • lapT (p.Efun i) x
    - (1 / 2 : ℝ) • p.Efun i x
    + advT p.Ufun (p.Efun i) x
    + realC (fderiv ℝ (p.raw x.1) x.2 (p.inlet i x.1 x.2))

/-- The spatial derivative `∂_{y_j}` of the inlet source. -/
def inletSourceG (p : Params) (i : Fin 2) (j : Fin 3) : ℝ × Space → CVec3 :=
  dy j (inletSourceF p i)

/-- Template for a statement on every inlet of every parameter in the regime, for small `ν`. -/
def InletPiece (Q : Params → Fin 2 → Prop) : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Planar.Profile), 0 < Sig → Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∀ i : Fin 2, Q p i

/-- **Joint smoothness of the inlet** `(τ, y) ↦ E_i(τ, y)` (SP 2347-2369: `E_i` is the ring lift
of the smooth cutoff stream, smooth through the axis; slices: `InletContDiff`). -/
def InletJointSmooth : Prop :=
  InletPiece fun p i => ContDiff ℝ ∞ (fun x : ℝ × Space => p.inlet i x.1 x.2)

/-- **Joint smoothness of `U_raw`** (SP 1214-ff, ring lift of the smooth train; slices:
`RawContDiff`). -/
def RawJointSmooth : Prop :=
  InletPiece fun p _ => ContDiff ℝ ∞ (fun x : ℝ × Space => p.raw x.1 x.2)

/-- **`U_raw` is divergence free** (it is the ring lift of a stream; SP 1214-ff). -/
def RawDivFree : Prop :=
  InletPiece fun p _ => ∀ (τ : ℝ) (y : Space),
    ∑ k : Fin 3, fderiv ℝ (p.raw τ) y (EuclideanSpace.single k 1) k = 0

/-- **Reality and `𝒪`-symmetry of the source** (SP 2370-2383: `E_i` is a real field, `Nv` ring
lift is covariant under the axis-fixing isometries, as are `L_0`, `V_0·∇`, `(·∇)V_0`). -/
def InletSourceRealO : Prop :=
  InletPiece fun p i =>
    (∀ x, ∃ r : Space, inletSourceF p i x = realC r) ∧
    ∀ g : Space ≃ₗᵢ[ℝ] Space, UnforcedLeray.FixesAxis g → ∀ τ y,
      gC g (inletSourceF p i (τ, g.symm y)) = inletSourceF p i (τ, y)

/-- **Integration by parts** (SP 2370-2383): for a solenoidal phase test `Φ` (compact support in
`τ, y`; integration by parts in `τ` and `y`, `div V_0 = 0`),
`⟪L_0ᵗΦ + (∇V_0)ᵀΦ - (V_0·∇)Φ, E_i⟫ = ⟪Φ, (L_0 + B_{V_0})E_i⟫`. -/
def InletSourceIBP : Prop :=
  InletPiece fun p i => ∀ Φ, IsSolTest p.period Φ →
    pairF p.period (fun x => L0T p.ν Φ x + convT p.raw Φ x) (p.Efun i) =
      pairF p.period Φ (inletSourceF p i)

/-- **The spatial derivative is the weak gradient** (SP 2370-2383: smoothness of the source and
integration by parts against phase tests). -/
def InletSourceGradPtw : Prop :=
  InletPiece fun p i => ∀ j : Fin 3,
    HasPtwOp p.period (fun Φ x => -(dy j Φ x)) (inletSourceF p i) (inletSourceG p i j)

/-- **Periodicity and measurability** of the source and its gradients (periodic in `τ` by
`Params.inletProfile_periodic`; measurable by continuity). -/
def InletSourcePerMeas : Prop :=
  InletPiece fun p i =>
    ((∀ᵐ x : ℝ × Space, inletSourceF p i (x.1 + p.period, x.2) = inletSourceF p i x) ∧
      AEStronglyMeasurable (inletSourceF p i) volume) ∧
    ∀ j : Fin 3,
      (∀ᵐ x : ℝ × Space, inletSourceG p i j (x.1 + p.period, x.2) = inletSourceG p i j x) ∧
        AEStronglyMeasurable (inletSourceG p i j) volume

/-- **Finiteness and the polynomial bound** (SP 2355-2383: `FrozenStreamBounds`, `phaseLpNorm_NvC`
(Jacobian `πR²`), `NvFderivBound`): the norms are finite and
`‖F‖ + ∑ⱼ ‖Gⱼ‖ ≤ C ν^{-k} R^{2/p}`. -/
def InletSourceFieldBound : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Planar.Profile), 0 < Sig → Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∀ i : Fin 2,
        phaseLpNorm p.period bgp (inletSourceF p i) < ⊤ ∧
        (∀ j : Fin 3, phaseLpNorm p.period bgp (inletSourceG p i j) < ⊤) ∧
        (phaseLpNorm p.period bgp (inletSourceF p i)).toReal +
            ∑ j : Fin 3, (phaseLpNorm p.period bgp (inletSourceG p i j)).toReal ≤
          C * (p.ν ^ k)⁻¹ * p.R ^ (2 / bgp)

/-- **Conditional assembly** of `InletSourceFields` from the concrete pieces. -/
theorem inletSourceFields_of (hR : InletSourceRealO) (hI : InletSourceIBP)
    (hG : InletSourceGradPtw) (hM : InletSourcePerMeas) (hB : InletSourceFieldBound) :
    InletSourceFields := by
  intro Sig lam q hSig hq dm dp hdm
  obtain ⟨ν₁, h1, H1⟩ := hR Sig lam q hSig hq dm dp hdm
  obtain ⟨ν₂, h2, H2⟩ := hI Sig lam q hSig hq dm dp hdm
  obtain ⟨ν₃, h3, H3⟩ := hG Sig lam q hSig hq dm dp hdm
  obtain ⟨ν₄, h4, H4⟩ := hM Sig lam q hSig hq dm dp hdm
  obtain ⟨C, k, ν₅, hC, h5, H5⟩ := hB Sig lam q hSig hq dm dp hdm
  refine ⟨C, k, min ν₁ (min ν₂ (min ν₃ (min ν₄ ν₅))), hC,
    lt_min h1 (lt_min h2 (lt_min h3 (lt_min h4 h5))), ?_⟩
  intro p d hreg hν hSig' hmode i
  have e1 : p.ν ≤ ν₁ := hν.trans (min_le_left _ _)
  have e2 : p.ν ≤ ν₂ := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have e3 : p.ν ≤ ν₃ :=
    hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have e4 : p.ν ≤ ν₄ :=
    hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have e5 : p.ν ≤ ν₅ :=
    hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))
  obtain ⟨hre, hO⟩ := H1 p d hreg e1 hSig' hmode i
  have hid := H2 p d hreg e2 hSig' hmode i
  have hgr := H3 p d hreg e3 hSig' hmode i
  obtain ⟨⟨hpF, hmF⟩, hGm⟩ := H4 p d hreg e4 hSig' hmode i
  obtain ⟨hfF, hfG, hbd⟩ := H5 p d hreg e5 hSig' hmode i
  exact ⟨inletSourceF p i, inletSourceG p i, ⟨hpF, hmF, hfF⟩,
    fun j => ⟨(hGm j).1, (hGm j).2, hfG j⟩, hre, hO, hid, hgr, hbd⟩

end UnforcedLeray.Short.IIb
