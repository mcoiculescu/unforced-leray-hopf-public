import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_4

/-!
# `GenAdjointPair` decomposed (task `PartIII-b:C/near/pins/3/4/2`)

Source `the November 2 reference manuscript`
lines 1339-1362 (free equation `L = 𝒯 - νΔ - 1/2`), 3346-3352 (outer semigroup `S_ε`),
4139-4146 (`D_μ = L₀ + μ`), 2683-2689 (lift dictionary).

The outer transpose of the generator `G = νε²Δ_x + x·∇/2 + 1/2 - ∂_τ` is, under `x = εy`,
`Gᵗ Ψ = -(L₀ᵗΦ)(τ, x/ε)` for `Ψ(x,τ) = Φ(τ, x/ε)`.  Three leaves:
* `ChartDecomp`: every `g ∈ H` is `g₁ + i g₂` with `g₁, g₂` having real chart forms;
* `OuterDict`: for a smooth periodic phase test `Φ` the scaled field `Ψ(x,τ) = Φ(τ, x/ε)` lies in
  `X = L²(dx dτ; ℂ³)` and pairs with `liftVec u` as `κ · pairF Φ (velPhys f)` (change of variables,
  constant `κ ≠ 0` independent of `Φ`, `u`);
* `OuterGen`: `⟪D_μᵗΨ, x⟫ = ⟪Ψ, μx - y⟫` on the graph of `S_ε` (integration by parts, using the
  `t`-derivative of `S_formula`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)

/-- The bilinear (non-conjugated) `L²(dx dτ)` pairing of two outer fields. -/
def outerPair {P : ℝ} [Fact (0 < P)] (Ψ F : UnforcedLeray.B0223.X UnforcedLeray.B0223.SpaceC P) :
    ℂ :=
  ∫ z, dotL (Ψ z) (F z)


theorem outerPair_integrable {P : ℝ} [Fact (0 < P)]
    (Q F : UnforcedLeray.B0223.X UnforcedLeray.B0223.SpaceC P) :
    Integrable (fun z => dotL (Q z) (F z)) := by
  have hQ := (Lp.memLp Q).norm
  have hF := (Lp.memLp F).norm
  have h := (hQ.integrable_mul hF).const_mul ‖dotL‖
  refine h.mono' ?_ ?_
  · exact (dotL.aestronglyMeasurable_comp₂ (Lp.aestronglyMeasurable Q)
      (Lp.aestronglyMeasurable F))
  · refine Filter.Eventually.of_forall fun z => ?_
    calc ‖dotL (Q z) (F z)‖ ≤ ‖dotL (Q z)‖ * ‖F z‖ := (dotL (Q z)).le_opNorm _
      _ ≤ (‖dotL‖ * ‖Q z‖) * ‖F z‖ :=
          mul_le_mul_of_nonneg_right (dotL.le_opNorm _) (norm_nonneg _)
      _ = ‖dotL‖ * (‖Q z‖ * ‖F z‖) := by ring

theorem outerPair_add {P : ℝ} [Fact (0 < P)]
    (Q a b : UnforcedLeray.B0223.X UnforcedLeray.B0223.SpaceC P) :
    outerPair Q (a + b) = outerPair Q a + outerPair Q b := by
  unfold outerPair
  rw [← integral_add (outerPair_integrable Q a) (outerPair_integrable Q b)]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_add a b] with z hz
  rw [hz, Pi.add_apply, map_add]

theorem outerPair_smul {P : ℝ} [Fact (0 < P)] (k : ℂ)
    (Q a : UnforcedLeray.B0223.X UnforcedLeray.B0223.SpaceC P) :
    outerPair Q (k • a) = k * outerPair Q a := by
  unfold outerPair
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_smul k a] with z hz
  rw [hz, Pi.smul_apply, map_smul, smul_eq_mul]

theorem outerPair_sub {P : ℝ} [Fact (0 < P)]
    (Q a b : UnforcedLeray.B0223.X UnforcedLeray.B0223.SpaceC P) :
    outerPair Q (a - b) = outerPair Q a - outerPair Q b := by
  have : a - b = a + (-1 : ℂ) • b := by simp [sub_eq_add_neg]
  rw [this, outerPair_add, outerPair_smul]; ring

/-- `Ψ ∈ X` is the scaled test `Ψ(x,τ) = Φ(τ, x/ε)` a.e. (periodic variable `τ ∈ (0, P]`). -/
def OuterRep (p : Params) (Φ : ℝ × Space → CVec3)
    (Ψ : UnforcedLeray.B0223.X UnforcedLeray.B0223.SpaceC p.period) : Prop :=
  (Ψ : UnforcedLeray.B0223.PSpace p.period → UnforcedLeray.B0223.SpaceC) =ᵐ[volume]
    fun z => Φ ((UnforcedLeray.B0223.toCell p.period z).2,
      p.ε⁻¹ • (UnforcedLeray.B0223.toCell p.period z).1)

/-- **Leaf 0** (real/imaginary parts of a meridional profile): every `g ∈ H` is `g₁ + i g₂` with
`g₁, g₂` of real chart form (source 1675-1676: `H` is the complexification of the real
meridional space). -/
def ChartDecomp : Prop :=
  ∀ (p : Params) (g : HSpace p.c MeridC), ∃ (g₁ g₂ : HSpace p.c MeridC) (f₁ f₂ : Chart → Merid),
    ChartRep p.c g₁ f₁ ∧ ChartRep p.c g₂ f₂ ∧ g = g₁ + Complex.I • g₂

/-- **Leaf 1 (lift dictionary)** (source 2683-2689; `B0223.coeFn_liftVec`): there is a constant
`κ ≠ 0` (the Jacobian `ε³` and normalisations) such that for every smooth periodic phase test `Φ`
the scaled field `Ψ(x,τ) = Φ(τ,x/ε)` lies in `X`, and
`⟪Ψ, lift u⟫ = κ · pairF Φ (velPhys f)` whenever `u` has real chart form `f`. -/
def OuterDict : Prop :=
  ∀ p : Params, ∃ κ : ℂ, κ ≠ 0 ∧ ∀ Φ : ℝ × Space → CVec3, IsPhaseTest p.period Φ →
    ∃ Ψ : UnforcedLeray.B0223.X UnforcedLeray.B0223.SpaceC p.period, OuterRep p Φ Ψ ∧
      ∀ (u : HSpace p.c MeridC) (f : Chart → Merid), ChartRep p.c u f →
        outerPair Ψ (UnforcedLeray.B0223.liftVec (P := p.period) p.ε_pos p.c_pos rfl u) =
          κ * pairF p.period Φ (velPhys p.ε⁻¹ p.c f)

/-- **Leaf 2 (weak generator identity)** (source 1339-1362, 3346-3352): if `Ψ, ΨD` are the scaled
tests of `Φ` and of `L₀ᵗΦ + μΦ`, then for `(x, y)` in the graph of the outer semigroup generator
`⟪ΨD, x⟫ = ⟪Ψ, μ x - y⟫`.  (Integration by parts for
`νε²Δ_x + x·∇/2 + 1/2 - ∂_τ`, with `Gᵗ Ψ = -(L₀ᵗΦ)(τ,x/ε)`, against the derivative
`d/dt S(t)x = S(t)y` of the orbit and `S(t)ᵗ → 1` strongly.) -/
def OuterGen : Prop :=
  ∀ (p : Params) (μ : ℝ) (Φ : ℝ × Space → CVec3), IsPhaseTest p.period Φ →
    ∀ Ψ ΨD : UnforcedLeray.B0223.X UnforcedLeray.B0223.SpaceC p.period,
      OuterRep p Φ Ψ → OuterRep p (fun x => L0T p.ν Φ x + (μ : ℂ) • Φ x) ΨD →
      ∀ x y : UnforcedLeray.B0223.X UnforcedLeray.B0223.SpaceC p.period,
        UnforcedLeray.B0223.IsGenPair
          (UnforcedLeray.B0223.outerS (E := UnforcedLeray.B0223.SpaceC) (P := p.period)
            p.ν_pos p.ε) x y →
        outerPair ΨD x = outerPair Ψ ((μ : ℂ) • x - y)

theorem genAdjointPair_of (h0 : ChartDecomp) (h1 : OuterDict) (h2 : OuterGen) :
    GenAdjointPair := by
  intro p μ Φ hΦ ℓΦ ℓD hΦ' hD' u Au hgen
  have hΦp : IsPhaseTest p.period Φ := hΦ.1
  have hDp : IsPhaseTest p.period (fun x => L0T p.ν Φ x + (μ : ℂ) • Φ x) :=
    (isPhaseTest_L0T hΦp p.ν).add (hΦp.const_smul (μ : ℂ))
  obtain ⟨κ, hκ, hdict⟩ := h1 p
  obtain ⟨Ψ, hΨ, hΨd⟩ := hdict Φ hΦp
  obtain ⟨ΨD, hΨD, hΨDd⟩ := hdict _ hDp
  set J := UnforcedLeray.B0223.liftVec (P := p.period) p.ε_pos p.c_pos rfl with hJ
  have hlin : ∀ (Q : UnforcedLeray.B0223.X UnforcedLeray.B0223.SpaceC p.period)
      (ℓ : HSpace p.c MeridC →L[ℂ] ℂ) (T : ℝ × Space → CVec3),
      (∀ (u : HSpace p.c MeridC) (f : Chart → Merid), ChartRep p.c u f →
        outerPair Q (J u) = κ * pairF p.period T (velPhys p.ε⁻¹ p.c f)) →
      (∀ (g : HSpace p.c MeridC) (f : Chart → Merid), ChartRep p.c g f →
        ℓ g = pairF p.period T (velPhys p.ε⁻¹ p.c f)) →
      ∀ g : HSpace p.c MeridC, outerPair Q (J g) = κ * ℓ g := by
    intro Q ℓ T hQ hℓ g
    obtain ⟨g₁, g₂, f₁, f₂, h₁, h₂, rfl⟩ := h0 p g
    have hop : ∀ (a b : HSpace p.c MeridC),
        outerPair Q (J (a + Complex.I • b)) = outerPair Q (J a) + Complex.I * outerPair Q (J b) := by
      intro a b
      rw [map_add, map_smul, outerPair_add, outerPair_smul]
    rw [hop, map_add, map_smul, hQ _ _ h₁, hQ _ _ h₂, hℓ _ _ h₁, hℓ _ _ h₂]
    simp only [smul_eq_mul]
    ring
  have hA := hlin Ψ ℓΦ Φ hΨd hΦ'
  have hB := hlin ΨD ℓD _ hΨDd hD'
  have key := h2 p μ Φ hΦp Ψ ΨD hΨ hΨD (J u) (J Au) hgen
  have e1 := hB u
  rw [key, outerPair_sub, outerPair_smul, hA u, hA Au] at e1
  have e2 : κ * ℓD u = κ * ℓΦ ((μ : ℂ) • u - Au) := by
    rw [map_sub, map_smul, smul_eq_mul]
    linear_combination -e1
  exact mul_left_cancel₀ hκ e2

end UnforcedLeray.Short.PartIIIb.NearInst
