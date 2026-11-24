import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_4_2

/-!
# `OuterGen` decomposed (task `PartIII-b:C/near/pins/3/4/2/3`)

Source `the November 2 reference manuscript`
lines 1339-1362 (free equation `L = 𝒯 - νΔ - 1/2`), 3346-3352 (outer semigroup `S_ε`),
4139-4146 (`D_μ = L₀ + μ`).

Leaves:
* `OuterPairCLM`: `F ↦ ⟪Ψ, F⟫` is a continuous `ℂ`-linear functional on `X` (Cauchy-Schwarz);
* `OuterTestDeriv`: for the scaled test `Ψ` of a phase test `Φ` and `Ψ'` the scaled test of
  `-L₀ᵗΦ` (`= Gᵗ Ψ`, scaling `x = εy`), `d/dt ⟪Ψ, S(t) w⟫ = ⟪Ψ', S(t) w⟫` for every `w ∈ X`, `t > 0`.
The assembly (`IsGenPair` + uniqueness of derivatives + strong continuity at `0`) is
`outerGen_of`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- `F ↦ ⟪Ψ, F⟫` (bilinear `L²` pairing) is a bounded `ℂ`-linear functional on `X`
(`‖⟪Ψ,F⟫‖ ≤ ‖dotL‖ ‖Ψ‖ ‖F‖`, Cauchy-Schwarz with `outerPair_integrable`). -/
def OuterPairCLM : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (Ψ : UnforcedLeray.B0223.X UnforcedLeray.B0223.SpaceC P),
    ∃ ℓ : UnforcedLeray.B0223.X UnforcedLeray.B0223.SpaceC P →L[ℂ] ℂ,
      ∀ F, ℓ F = outerPair Ψ F

/-- **Weak `t`-derivative of the outer semigroup against a scaled test** (source 1339-1362,
3346-3352, 4139-4146): `S = S_ε` has formula `S(t) = e^{-t/4} dil heat trans`
(`B0223.S_formula`), whose transpose acts on tests by the heat kernel, dilation and phase
translation; with `x = εy` (`νε²Δ_x = νΔ_y`, `x·∇_x = y·∇_y`) one finds
`d/dt S(t)ᵗΨ = S(t)ᵗ GᵗΨ`, `GᵗΨ = -(L₀ᵗΦ)(τ, x/ε)`.  Equivalently, for every `w ∈ X`,
`d/dt ⟪Ψ, S(t) w⟫ = ⟪Ψ', S(t) w⟫` for `t > 0`, `Ψ'` the scaled test of `-L₀ᵗΦ`. -/
def OuterTestDeriv : Prop :=
  ∀ (p : Params) (Φ : ℝ × Space → CVec3), IsPhaseTest p.period Φ →
    ∀ Ψ Ψ' : UnforcedLeray.B0223.X UnforcedLeray.B0223.SpaceC p.period,
      OuterRep p Φ Ψ → OuterRep p (fun x => -(L0T p.ν Φ x)) Ψ' →
      ∀ (w : UnforcedLeray.B0223.X UnforcedLeray.B0223.SpaceC p.period) (t : ℝ), 0 < t →
        HasDerivAt (fun s => outerPair Ψ
            ((UnforcedLeray.B0223.outerS (E := UnforcedLeray.B0223.SpaceC) (P := p.period)
              p.ν_pos p.ε).T s w))
          (outerPair Ψ'
            ((UnforcedLeray.B0223.outerS (E := UnforcedLeray.B0223.SpaceC) (P := p.period)
              p.ν_pos p.ε).T t w)) t

theorem outerPair_add_left {P : ℝ} [Fact (0 < P)]
    (a b F : UnforcedLeray.B0223.X UnforcedLeray.B0223.SpaceC P) :
    outerPair (a + b) F = outerPair a F + outerPair b F := by
  unfold outerPair
  rw [← integral_add (outerPair_integrable a F) (outerPair_integrable b F)]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_add a b] with z hz
  rw [hz, Pi.add_apply, map_add, ContinuousLinearMap.add_apply]

theorem outerPair_smul_left {P : ℝ} [Fact (0 < P)] (k : ℂ)
    (a F : UnforcedLeray.B0223.X UnforcedLeray.B0223.SpaceC P) :
    outerPair (k • a) F = k * outerPair a F := by
  unfold outerPair
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_smul k a] with z hz
  rw [hz, Pi.smul_apply, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem outerPair_sub_left {P : ℝ} [Fact (0 < P)]
    (a b F : UnforcedLeray.B0223.X UnforcedLeray.B0223.SpaceC P) :
    outerPair (a - b) F = outerPair a F - outerPair b F := by
  have : a - b = a + (-1 : ℂ) • b := by simp [sub_eq_add_neg]
  rw [this, outerPair_add_left, outerPair_smul_left]; ring

theorem outerGen_of (h1 : OuterPairCLM) (h2 : OuterTestDeriv) : OuterGen := by
  intro p μ Φ hΦ Ψ ΨD hΨ hΨD x y hxy
  have : Fact (0 < p.period) := ⟨p.period_pos⟩
  set S := UnforcedLeray.B0223.outerS (E := UnforcedLeray.B0223.SpaceC) (P := p.period)
    p.ν_pos p.ε with hS
  set Ψ' : UnforcedLeray.B0223.X UnforcedLeray.B0223.SpaceC p.period := (μ : ℂ) • Ψ - ΨD
    with hΨ'
  have hΨ'rep : OuterRep p (fun x => -(L0T p.ν Φ x)) Ψ' := by
    unfold OuterRep at *
    filter_upwards [hΨ, hΨD, Lp.coeFn_sub ((μ : ℂ) • Ψ) ΨD, Lp.coeFn_smul (μ : ℂ) Ψ]
      with z h1 h2 h3 h4
    rw [hΨ', h3, Pi.sub_apply, h4, Pi.smul_apply, h1, h2]
    abel
  have hΨD' : ΨD = (μ : ℂ) • Ψ - Ψ' := by rw [hΨ']; abel
  obtain ⟨ℓ, hℓ⟩ := h1 p.period Ψ
  obtain ⟨ℓ', hℓ'⟩ := h1 p.period Ψ'
  -- the two derivatives agree for t > 0
  have heq : ∀ t : ℝ, 0 < t → ℓ (S.T t y) = ℓ' (S.T t x) := by
    intro t ht
    have d1 : HasDerivAt (fun s => ℓ (S.T s x)) (ℓ (S.T t y)) t := by
      have := ((ℓ.restrictScalars ℝ).hasFDerivAt (x := S.T t x)).comp_hasDerivAt t (hxy t ht)
      exact this
    have d2 := h2 p Φ hΦ Ψ Ψ' hΨ hΨ'rep x t ht
    simp only [← hℓ, ← hℓ'] at d2
    exact d1.unique d2
  -- strong continuity at 0
  have hc : ContinuousWithinAt (fun s => ℓ (S.T s y) - ℓ' (S.T s x)) (Ici 0) 0 :=
    ((ℓ.continuous.comp_continuousOn (S.T_cont y)).sub
      (ℓ'.continuous.comp_continuousOn (S.T_cont x))) 0 (mem_Ici.2 le_rfl)
  have hc' := hc.mono (Ioi_subset_Ici_self (a := (0 : ℝ)))
  have hlim : Tendsto (fun s => ℓ (S.T s y) - ℓ' (S.T s x)) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [heq s hs, sub_self]
  have h0 := tendsto_nhds_unique hc' hlim
  simp only [S.T_zero_apply, sub_eq_zero] at h0
  rw [hΨD', outerPair_sub_left, outerPair_smul_left, outerPair_sub, outerPair_smul,
    ← hℓ' x, ← h0, hℓ y]

end UnforcedLeray.Short.PartIIIb.NearInst
