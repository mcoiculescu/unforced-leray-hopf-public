import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.PairCLM

/-!
# `OuterTestDeriv` decomposed (task `PartIII-b:C/near/pins/3/4/2/3/2`)

Source `the November 2 reference manuscript`
lines 1339-1362 (free equation `L = 𝒯 - νΔ - 1/2`), 3346-3352 (outer semigroup `S_ε`),
4139-4146 (`D_μ = L₀ + μ`).

`S_ε(t) = e^{-t/4} dilN(e^{t/2}) e^{νε²(e^t-1)Δ_x} transC t` (`B0223.Sop`).  Its transpose for the
bilinear pairing `⟪·,·⟫ = outerPair` is
`S_ε(t)ᵗ = e^{-t/4} transC(-t) e^{νε²(e^t-1)Δ_x} dilN(e^{-t/2})` (`outerTransp`), i.e.
`S_ε(t)ᵗΨ(y,σ) = e^{-t} [e^{νε²(e^t-1)Δ} Ψ(e^{-t/2}·,σ+t)](y)` (3350-3352).
Leaves:
* transposition of the three factors (`OuterPairTransC`, `OuterPairDilN`, `OuterPairHeatC`),
  giving `⟪Ψ, S(t)w⟫ = ⟪S(t)ᵗΨ, w⟫` (`outerTransposePair_of`);
* `OuterTransposeDeriv`: `d/dt S(t)ᵗΨ = S(t)ᵗΨ'` in `X` for a smooth phase test, where `Ψ'` is the
  scaled `Gᵗ Ψ`, `Gᵗ = νε²Δ_x - x·∇/2 - 1 + ∂_τ` (the transpose of
  `G = νε²Δ_x + x·∇/2 + 1/2 - ∂_τ`);
* `OuterScaling`: under `x = εy`, `Gᵗ (Φ(τ, x/ε)) = (-L₀ᵗΦ)(τ, x/ε)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- The outer space `X = L²(dx dτ; ℂ³)` on the `τ`-period `P`. -/
abbrev XC (P : ℝ) [Fact (0 < P)] : Type :=
  UnforcedLeray.B0223.X UnforcedLeray.B0223.SpaceC P

/-- **The transpose `S_ε(t)ᵗ` of the outer semigroup** (source 3346-3352), `h = νε²`:
`e^{-t/4} transC(-t) e^{h(e^t-1)Δ_x} dilN(e^{-t/2})`; on functions
`Ψ ↦ e^{-t} [e^{h(e^t-1)Δ} Ψ(e^{-t/2}·, ·+t)]`. -/
def outerTransp {P : ℝ} [Fact (0 < P)] (h t : ℝ) (Ψ : XC P) : XC P :=
  ((Real.exp (-t / 4) : ℝ) : ℂ) •
    UnforcedLeray.B0223.transC (E := UnforcedLeray.B0223.SpaceC) (-t)
      (UnforcedLeray.B0223.heatC (E := UnforcedLeray.B0223.SpaceC) (h * (Real.exp t - 1))
        (UnforcedLeray.B0223.dilN (E := UnforcedLeray.B0223.SpaceC) (Real.exp (t / 2))⁻¹ Ψ))

/-- The scaled test `ψ(τ, x) = Φ(τ, x/ε)` (source 1339-1362, `x = εy`). -/
def scaledFn (p : Params) (Φ : ℝ × Space → CVec3) : ℝ × Space → CVec3 :=
  fun q => Φ (q.1, p.ε⁻¹ • q.2)

/-- The transposed outer generator `Gᵗψ = νε²Δ_xψ - ½ x·∇ψ - ψ + ∂_τψ`
(`G = νε²Δ_x + x·∇/2 + 1/2 - ∂_τ`, `div x = 3`; source 3346-3352). -/
def outerGenT (p : Params) (ψ : ℝ × Space → CVec3) : ℝ × Space → CVec3 :=
  fun q => (p.ν * p.ε ^ 2) • lapT ψ q - (1 / 2 : ℝ) • radialT ψ q - ψ q + dτ ψ q

/-- `Ψ ∈ X` represents `ψ` a.e. on the cell (`τ` periodic variable in `(0,P]`). -/
def OuterRepFn (p : Params) (ψ : ℝ × Space → CVec3) (Ψ : XC p.period) : Prop :=
  (Ψ : UnforcedLeray.B0223.PSpace p.period → UnforcedLeray.B0223.SpaceC) =ᵐ[volume]
    fun z => ψ ((UnforcedLeray.B0223.toCell p.period z).2,
      (UnforcedLeray.B0223.toCell p.period z).1)

/-- Transposition of the phase translation (unitary, measure-preserving shift; 3354). -/
def OuterPairTransC : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (t : ℝ) (Ψ w : XC P),
    outerPair Ψ (UnforcedLeray.B0223.transC (E := UnforcedLeray.B0223.SpaceC) t w) =
      outerPair (UnforcedLeray.B0223.transC (E := UnforcedLeray.B0223.SpaceC) (-t) Ψ) w

/-- Transposition of the normalized dilation `dilN a F = a^{3/2} F(a·, ·)`, `a > 0`
(change of variables `y = a x`; 3350-3352). -/
def OuterPairDilN : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (a : ℝ), 0 < a → ∀ (Ψ w : XC P),
    outerPair Ψ (UnforcedLeray.B0223.dilN (E := UnforcedLeray.B0223.SpaceC) a w) =
      outerPair (UnforcedLeray.B0223.dilN (E := UnforcedLeray.B0223.SpaceC) a⁻¹ Ψ) w

/-- Symmetry of the spatial heat semigroup (even Gaussian kernel, Fubini; 3350-3352). -/
def OuterPairHeatC : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (θ : ℝ) (Ψ w : XC P),
    outerPair Ψ (UnforcedLeray.B0223.heatC (E := UnforcedLeray.B0223.SpaceC) θ w) =
      outerPair (UnforcedLeray.B0223.heatC (E := UnforcedLeray.B0223.SpaceC) θ Ψ) w

/-- **Transposition of `S_ε(t)`** (source 3346-3352): `⟪Ψ, S(t) w⟫ = ⟪S(t)ᵗΨ, w⟫`, `t > 0`. -/
def OuterTransposePair : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (ν ε : ℝ) (hν : 0 < ν) (t : ℝ), 0 < t → ∀ (Ψ w : XC P),
    outerPair Ψ ((UnforcedLeray.B0223.outerS (E := UnforcedLeray.B0223.SpaceC) (P := P) hν ε).T t
      w) = outerPair (outerTransp (ν * ε ^ 2) t Ψ) w

/-- **Strong `t`-derivative of the transposed semigroup on a scaled test** (source 1339-1362,
3346-3352, 4139-4146): for a smooth phase test `Φ`, `Ψ` the scaled `Φ(τ, x/ε)` and `Ψ'` the scaled
`Gᵗ` of it, `d/dt S(t)ᵗΨ = S(t)ᵗΨ'` in `X` for `t > 0`. -/
def OuterTransposeDeriv : Prop :=
  ∀ (p : Params) (Φ : ℝ × Space → CVec3), IsPhaseTest p.period Φ →
    ∀ Ψ Ψ' : XC p.period, OuterRep p Φ Ψ → OuterRepFn p (outerGenT p (scaledFn p Φ)) Ψ' →
      ∀ t : ℝ, 0 < t →
        HasDerivAt (fun s => outerTransp (p.ν * p.ε ^ 2) s Ψ)
          (outerTransp (p.ν * p.ε ^ 2) t Ψ') t

/-- **Scaling identity** (`x = εy`: `νε²Δ_x = νΔ_y`, `x·∇_x = y·∇_y`; source 1339-1362, 4139-4146;
`L0T` in `Units/B0411/Operators.lean:54`): `Gᵗ(Φ(τ, x/ε)) = (-L₀ᵗΦ)(τ, x/ε)`. -/
def OuterScaling : Prop :=
  ∀ (p : Params) (Φ : ℝ × Space → CVec3), IsPhaseTest p.period Φ →
    outerGenT p (scaledFn p Φ) = scaledFn p (fun x => -(L0T p.ν Φ x))

/-- `Q ↦ ⟪Q, w⟫` as a continuous `ℂ`-linear functional. -/
def outerPairL {P : ℝ} [Fact (0 < P)] (w : XC P) : XC P →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun Q => outerPair Q w
      map_add' := fun a b => outerPair_add_left a b w
      map_smul' := fun k a => by
        rw [outerPair_smul_left, RingHom.id_apply, smul_eq_mul] }
    (‖dotL‖ * ‖w‖) fun Q => by
      show ‖outerPair Q w‖ ≤ _
      calc ‖outerPair Q w‖ ≤ ‖dotL‖ * (‖Q‖ * ‖w‖) := outerPair_norm_le Q w
        _ = (‖dotL‖ * ‖w‖) * ‖Q‖ := by ring

theorem outerPairL_apply {P : ℝ} [Fact (0 < P)] (w Q : XC P) :
    outerPairL w Q = outerPair Q w := rfl

theorem outerTransposePair_of (h1 : OuterPairTransC) (h2 : OuterPairDilN)
    (h3 : OuterPairHeatC) : OuterTransposePair := by
  intro P _ ν ε hν t ht Ψ w
  rw [UnforcedLeray.B0223.outerS_T, UnforcedLeray.B0223.Sop_apply, outerPair_smul,
    h2 P _ (Real.exp_pos _) Ψ _, h3, h1, outerTransp, outerPair_smul_left]

theorem outerTestDeriv_of (hA : OuterTransposePair) (hB : OuterTransposeDeriv)
    (hC : OuterScaling) : OuterTestDeriv := by
  intro p Φ hΦ Ψ Ψ' hΨ hΨ' w t ht
  have : Fact (0 < p.period) := ⟨p.period_pos⟩
  have hΨ'G : OuterRepFn p (outerGenT p (scaledFn p Φ)) Ψ' := by
    unfold OuterRep at hΨ'
    unfold OuterRepFn
    rw [hC p Φ hΦ]
    exact hΨ'
  have hd := hB p Φ hΦ Ψ Ψ' hΨ hΨ'G t ht
  have hl := ((outerPairL w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hd
  have hev : (fun s => outerPair Ψ ((UnforcedLeray.B0223.outerS
      (E := UnforcedLeray.B0223.SpaceC) (P := p.period) p.ν_pos p.ε).T s w)) =ᶠ[𝓝 t]
      ((outerPairL w).restrictScalars ℝ ∘ fun s => outerTransp (p.ν * p.ε ^ 2) s Ψ) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact hA p.period p.ν p.ε p.ν_pos s hs Ψ w
  have := hl.congr_of_eventuallyEq hev
  have e := hA p.period p.ν p.ε p.ν_pos t ht Ψ' w
  rw [e]
  exact this

end UnforcedLeray.Short.PartIIIb.NearInst
