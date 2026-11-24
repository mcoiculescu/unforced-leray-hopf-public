import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2_1_1

/-!
# Decomposition of `t0adjGradPres`

Source `the November 2 reference manuscript`
1640-1656.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.B0220 (HSpace measureH Profile QPeriodic)

/-- Smooth `q`-periodic profiles supported in a band `s ≥ s0 > 0` (no compactness in `η`) with
`Ψ` and the gradient `(D_0Ψ, ∂_ηΨ)` in `L²(measureH c)`: the class of Gaussian-decaying profiles
produced by the heat flow applied to a profile test (source 1650-1656). -/
def GaussGradProfile (c : ℝ) (Ψ : Profile → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ ∧ QPeriodic c Ψ ∧
  (∃ s0 s1 : ℝ, 0 < s0 ∧ ∀ p : Profile, Ψ p ≠ 0 → p.1 ∈ Icc s0 s1) ∧
  MemLp Ψ 2 (measureH c) ∧ MemLp (UnforcedLeray.Short.PartIIa.cgrad 0 Ψ) 2 (measureH c)

/-- **(N1)** (source 1650-1654: `heat(∇Φ) = ∇(heat Φ)`, dilation in `s`): `T0(t)*` of the gradient
class of a profile test is the gradient class of a Gaussian-decaying profile. Proof route:
`B0224.T0adj_apply_ae`; heat is constant coefficient in `(q,η)` so commutes with `∂_q, ∂_η`
(`Heat.hasDerivAt_heatConv_dir`); for `ν ≤ 0` `planeHeat_of_nonpos` makes `T0adj` a pure
`s`-dilation. -/
def T0adjGradGauss : Prop :=
  ∀ (c ν : ℝ) (hc : 0 < c) (t : ℝ), 0 < t →
    ∀ (Φ : UnforcedLeray.B0226.ProfileTest c)
      (h : MemLp (UnforcedLeray.Short.PartIIa.cgrad 0 Φ.1) 2 (measureH c)),
      ∃ (Ψ : Profile → ℝ) (hΨ : GaussGradProfile c Ψ),
        UnforcedLeray.B0224.T0adj hc ν t (h.toLp _) = hΨ.2.2.2.2.toLp _

/-- **(N2)** (source 1655-1656): the gradient class of a Gaussian-decaying profile lies in the
`H`-closure of the span of profile-test gradients (Gaussian cut-off in `η`, periodicity kept;
`‖Ψ χ_R'‖_{L²} ≤ R⁻¹ ‖Ψ‖_{L²}` and `χ_R ∇Ψ → ∇Ψ`). -/
def GaussGradInClosure : Prop :=
  ∀ (c : ℝ) (Ψ : Profile → ℝ) (hΨ : GaussGradProfile c Ψ),
    hΨ.2.2.2.2.toLp _ ∈
      (Submodule.span ℂ {g : HSpace c UnforcedLeray.B0223.MeridC | ∃ Φ : UnforcedLeray.B0226.ProfileTest c,
        ∃ _ : MemLp (UnforcedLeray.Short.PartIIa.cgrad 0 Φ.1) 2 (measureH c),
          g = (‹MemLp (UnforcedLeray.Short.PartIIa.cgrad 0 Φ.1) 2 (measureH c)›).toLp _}).topologicalClosure

theorem t0adjGradPres_of (h1 : T0adjGradGauss) (h2 : GaussGradInClosure) : T0adjGradPres := by
  intro c ν hc t ht Φ h
  obtain ⟨Ψ, hΨ, he⟩ := h1 c ν hc t ht Φ h
  rw [he]
  unfold UnforcedLeray.Short.PartIIa.solenoidalHC
  rw [Submodule.orthogonal_orthogonal_eq_closure]
  exact h2 c Ψ hΨ

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
