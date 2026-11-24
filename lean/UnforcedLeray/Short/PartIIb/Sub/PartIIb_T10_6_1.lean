import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_6

/-!
# `PartII-b:T10/6/1` (`DriftNoSwirl`): decomposition

Source of record: `the November 2 reference manuscript`
lines 1912-1915 (`𝒯(√s b) = √s (S + 1/2) b`, the drift of a lift is a no-swirl field).

Rotation-invariance argument: `g ∈ 𝒪` acts on phase fields by `(gΦ)(t,y) = gC g (Φ(t, g⁻¹y))`.
It preserves phase tests, commutes with `driftT`, preserves `pairF`, and fixes `NvC R b` a.e.
Hence `g d₀` and `d₀` pair equally with every phase test, so they agree a.e. (phase tests
separate points of `Y_r`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

/-- The action of an isometry `g` on phase fields: `(g·Φ)(t,y) = g Φ(t, g⁻¹ y)` (tex 113). -/
def gAct (g : Space ≃ₗᵢ[ℝ] Space) (Φ : ℝ × Space → CVec3) : ℝ × Space → CVec3 :=
  fun x => B0412.gC g (Φ (x.1, g.symm x.2))

/-- `g⁻¹ (g Φ) = Φ`: `gC g⁻¹ ∘ gC g = id` (orthogonality: `gEntry g⁻¹ i j = gEntry g j i`;
`Units/B0412/Action.lean`, `gC_apply`). -/
def GActInv : Prop :=
  ∀ (g : Space ≃ₗᵢ[ℝ] Space) (Φ : ℝ × Space → CVec3), gAct g.symm (gAct g Φ) = Φ

/-- `g·` preserves phase tests (smoothness, compact support in `y`, `P`-periodicity in `t` are
preserved by the linear isometry `y ↦ g⁻¹y` and the constant linear map `gC g`; SP 1912-1915). -/
def GActPhaseTest : Prop :=
  ∀ (P : ℝ) (g : Space ≃ₗᵢ[ℝ] Space) (Φ : ℝ × Space → CVec3),
    IsPhaseTest P Φ → IsPhaseTest P (gAct g Φ)

/-- `g·` commutes with `driftT = -∂_τ + ½ y·∇_y + 3/2` (`Lib/PhaseSpace/Ops.lean:46`): chain rule,
`y·∇` is rotation invariant since `g` is linear isometric. For phase tests `Φ`. -/
def GActDrift : Prop :=
  ∀ (P : ℝ) (g : Space ≃ₗᵢ[ℝ] Space) (Φ : ℝ × Space → CVec3),
    IsPhaseTest P Φ → driftT (gAct g Φ) = gAct g (driftT Φ)

/-- `⟪gΦ, g u⟫ = ⟪Φ, u⟫`: `y ↦ g y` preserves Lebesgue measure (`LinearIsometryEquiv.measurePreserving`),
and `dotL (gC g a) (gC g b) = dotL a b` (orthogonality, bilinear form). Unconditional (Bochner
integrals; both sides vanish together if non-integrable). -/
def GActPair : Prop :=
  ∀ (P : ℝ) (g : Space ≃ₗᵢ[ℝ] Space) (Φ u : ℝ × Space → CVec3),
    pairF P (gAct g Φ) (gAct g u) = pairF P Φ u

/-- `NvC R b` is `g`-invariant a.e. for `g ∈ 𝒪` (`g e₃ = e₃`): `Nv R b τ (g y) = g (Nv R b τ y)`
via `ϱ_map`, `eR_map`, `mer_map` and chart invariance (`Lib/AxisymmetricB/Average.lean`, `Lift.lean`;
`Cons/L2/PencilConcrete/Meridional.lean` `ringChart_fixesAxis`, `FixesAxis`), then
`B0412.gC_realC` on real and imaginary parts of `b`. -/
def NvCInvariant : Prop :=
  ∀ (R : ℝ) (b : CProf) (g : Space ≃ₗᵢ[ℝ] Space),
    g (EuclideanSpace.single 2 1) = EuclideanSpace.single 2 1 →
      gAct g (NvC R b) =ᵐ[volume] NvC R b

/-- `g·` preserves `Y_r` (`P > 0`): measurability (composition with the measure preserving
equivalence `(t,y) ↦ (t, g⁻¹y)`), periodicity, and `‖gC g v‖ = ‖v‖` (`gC` is unitary on `ℂ³`), so
`phaseLpNorm` is unchanged. -/
def GActInYr : Prop :=
  ∀ (P r : ℝ) (g : Space ≃ₗᵢ[ℝ] Space) (f : ℝ × Space → CVec3),
    0 < P → IsInYr P r f → IsInYr P r (gAct g f)

/-- **Phase tests separate points of `Y_r`**: for `P > 0`, `1 < r`, `e₁, e₂ ∈ Y_r` with
`⟪Φ, e₁⟫ = ⟪Φ, e₂⟫` for all phase tests `Φ`, `e₁ = e₂` a.e.
(`B0411.eq_zero_of_forall_phasePair`, `Units/B0411/Separation.lean:286`, stated for the Lebesgue-class
`Yq P q`; convert `e₁ - e₂ ∈ Y_r` to `Yq P (ofReal r)` via `phasePair`/`pairF` agreement.) -/
def PhaseFundamental : Prop :=
  ∀ (P r : ℝ) (e₁ e₂ : ℝ × Space → CVec3), 0 < P → 1 < r → IsInYr P r e₁ → IsInYr P r e₂ →
    (∀ Φ, IsPhaseTest P Φ → pairF P Φ e₁ = pairF P Φ e₂) → e₁ =ᵐ[volume] e₂

/-- `pairF` only sees the a.e. class of the field. -/
theorem pairF_congr_ae (P : ℝ) (Φ : ℝ × Space → CVec3) {u v : ℝ × Space → CVec3}
    (h : u =ᵐ[volume] v) : pairF P Φ u = pairF P Φ v := by
  unfold pairF phaseInt
  congr 1
  have h' : ∀ᵐ x : ℝ × Space ∂(volume.prod volume), u x = v x := by
    rwa [← Measure.volume_eq_prod]
  have h2 := Measure.ae_ae_of_ae_prod h'
  refine setIntegral_congr_ae measurableSet_Ioc ?_
  filter_upwards [h2] with t ht _
  refine integral_congr_ae ?_
  filter_upwards [ht] with y hy
  simp only [hy]

theorem driftNoSwirl_of (h1 : GActPhaseTest) (h2 : GActDrift) (h3 : GActPair) (h4 : GActInv)
    (h5 : NvCInvariant) (h6 : GActInYr) (h7 : PhaseFundamental) : DriftNoSwirl := by
  intro c ε r b₀ d₀ hc hε hr hb hd hop g hg
  have hg' : g.symm (EuclideanSpace.single 2 1) = EuclideanSpace.single 2 1 := by
    rw [LinearIsometryEquiv.symm_apply_eq]; exact hg.symm
  have hP : 0 < 2 * ε * c := by positivity
  change gAct g d₀ =ᵐ[volume] d₀
  refine h7 (2 * ε * c) r _ _ hP hr (h6 _ r g d₀ hP hd) hd ?_
  intro Φ hΦ
  have hΨ : IsPhaseTest (2 * ε * c) (gAct g.symm Φ) := h1 _ g.symm Φ hΦ
  have hgg : gAct g (gAct g.symm Φ) = Φ := by
    have := h4 g.symm Φ
    rwa [LinearIsometryEquiv.symm_symm] at this
  have hgg2 : ∀ A : ℝ × Space → CVec3, gAct g (gAct g.symm A) = A := by
    intro A
    have := h4 g.symm A
    rwa [LinearIsometryEquiv.symm_symm] at this
  calc pairF (2 * ε * c) Φ (gAct g d₀)
      = pairF (2 * ε * c) (gAct g (gAct g.symm Φ)) (gAct g d₀) := by rw [hgg]
    _ = pairF (2 * ε * c) (gAct g.symm Φ) d₀ := h3 _ g _ _
    _ = pairF (2 * ε * c) (driftT (gAct g.symm Φ)) (NvC ε⁻¹ b₀) := (hop _ hΨ).symm
    _ = pairF (2 * ε * c) (gAct g.symm (driftT Φ)) (NvC ε⁻¹ b₀) := by
        rw [h2 _ g.symm Φ hΦ]
    _ = pairF (2 * ε * c) (gAct g (gAct g.symm (driftT Φ))) (gAct g (NvC ε⁻¹ b₀)) :=
        (h3 _ g _ _).symm
    _ = pairF (2 * ε * c) (driftT Φ) (gAct g (NvC ε⁻¹ b₀)) := by rw [hgg2]
    _ = pairF (2 * ε * c) (driftT Φ) (NvC ε⁻¹ b₀) :=
        pairF_congr_ae _ _ (h5 ε⁻¹ b₀ g hg)
    _ = pairF (2 * ε * c) Φ d₀ := hop Φ hΦ

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.driftNoSwirl_of
