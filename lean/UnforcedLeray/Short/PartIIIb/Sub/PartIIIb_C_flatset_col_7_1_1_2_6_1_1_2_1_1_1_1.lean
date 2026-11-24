import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2_1_1_1

/-!
# Decomposition of `T0adjGradGauss` (N1)

Source `the November 2 reference manuscript`
1640-1656: `T0(t)*` of the gradient class of a profile test is the gradient class of
`Ψ = e^{-t/2} e^{ν s (e^t-1) Δ_{q,η}} Φ(e^t s, ·)`, which is smooth, periodic, band-supported in `s`
and has Gaussian-decaying (square-integrable) `Ψ` and gradient.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.B0220 (HSpace measureH Profile QPeriodic)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.B0226 (ProfileTest IsProfileTest)

/-- The profile `Ψ(s, q, η) = e^{-t/2} (e^{θ(s) Δ_{q,η}} Φ(e^t s, ·))(q, η)`, `θ(s) = ν s (e^t - 1)`
(source 1650-1654). -/
def t0gPsi (ν t : ℝ) (Φ : Profile → ℝ) : Profile → ℝ := fun p =>
  Real.exp (-t / 2) * UnforcedLeray.B0224.planeHeat (ν * p.1 * (Real.exp t - 1))
    (fun z => Φ (Real.exp t * p.1, z)) p.2

/-- `Ψ` is smooth jointly in `(s, q, η)` (for `ν ≤ 0` a pure dilation; for `ν > 0` the heat time
`θ(s) > 0` on the support `s > 0`, and `Ψ = 0` for `s` small). -/
def T0gSmooth : Prop :=
  ∀ (c ν t : ℝ), 0 < c → ∀ (Φ : Profile → ℝ), IsProfileTest c Φ → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (t0gPsi ν t Φ)

/-- `Ψ` is `c`-periodic in `q` (heat commutes with the `q`-translation by `c`). -/
def T0gPeriodic : Prop :=
  ∀ (c ν t : ℝ) (Φ : Profile → ℝ), IsProfileTest c Φ → QPeriodic c (t0gPsi ν t Φ)

/-- `Ψ` vanishes unless `s` lies in a compact subinterval of `(0, ∞)`: `Φ(e^t s, ·)` is supported in
`s ∈ [s0 e^{-t}, s1 e^{-t}]` and the heat of `0` is `0`. -/
def T0gBand : Prop :=
  ∀ (c ν t : ℝ) (Φ : Profile → ℝ), IsProfileTest c Φ →
    ∃ s0 s1 : ℝ, 0 < s0 ∧ ∀ p : Profile, t0gPsi ν t Φ p ≠ 0 → p.1 ∈ Icc s0 s1

/-- The gradient of a profile test is continuous, `c`-periodic and supported in a band
`s ∈ [s0, s1]`, `|η| ≤ L` with `s0 > 0` (a derivative vanishes off the topological support). -/
def T0gCgradBand : Prop :=
  ∀ (c : ℝ) (Φ : Profile → ℝ), IsProfileTest c Φ →
    Continuous (UnforcedLeray.Short.PartIIa.cgrad 0 Φ) ∧
    QPeriodic c (UnforcedLeray.Short.PartIIa.cgrad 0 Φ) ∧
    ∃ s0 s1 L : ℝ, 0 < s0 ∧ ∀ p : Profile, UnforcedLeray.Short.PartIIa.cgrad 0 Φ p ≠ 0 →
      p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L

/-- Heat commutes with `∂_q`, `∂_η` and the `s`-dilation does not touch them (source 1650-1654):
the gradient `(D_0 Ψ, ∂_η Ψ)` is the heat flow of the dilated gradient of `Φ`. -/
def T0gGrad : Prop :=
  ∀ (c ν t : ℝ), 0 < c → ∀ (Φ : Profile → ℝ), IsProfileTest c Φ → ∀ p : Profile,
    UnforcedLeray.Short.PartIIa.cgrad 0 (t0gPsi ν t Φ) p =
      Real.exp (-t / 2) • UnforcedLeray.B0224.planeHeat (ν * p.1 * (Real.exp t - 1))
        (fun z => UnforcedLeray.Short.PartIIa.cgrad 0 Φ (Real.exp t * p.1, z)) p.2

/-- Square integrability (Gaussian tail in `η`, bounded in the `s`-band): for a continuous `G`
supported in a band `s ∈ [s0, s1]`, `|η| ≤ L` and `c`-periodic in `q`, the dilated heat flow is in `L²(measureH c)`
(`‖e^{θΔ} u‖_{L²_η} ≤ ‖u‖_{L²_η}`, finite weight on the band). -/
def T0gMem : Prop :=
  ∀ (c ν t : ℝ), 0 < c → ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (G : Profile → E), Continuous G → QPeriodic c G →
    (∃ s0 s1 L : ℝ, 0 < s0 ∧ ∀ p : Profile, G p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) →
    MemLp (fun p : Profile => Real.exp (-t / 2) • UnforcedLeray.B0224.planeHeat
      (ν * p.1 * (Real.exp t - 1)) (fun z => G (Real.exp t * p.1, z)) p.2) 2 (measureH c)

/-- The heat expression only depends on the `measureH c`-class of the section, for a periodic
reference `g` (Fubini in `s`, `reduceIoc` preserves null sets, `planeHeat` is an integral). -/
def T0gAe : Prop :=
  ∀ (c ν t : ℝ), 0 < c → ∀ (g : Profile → MeridC), QPeriodic c g → ∀ f : Profile → MeridC,
    f =ᵐ[measureH c] g → ∀ᵐ p ∂(measureH c),
      UnforcedLeray.B0224.planeHeat (ν * p.1 * (Real.exp t - 1))
        (fun z => UnforcedLeray.B0220.periodize c f (Real.exp t * p.1, z)) p.2 =
      UnforcedLeray.B0224.planeHeat (ν * p.1 * (Real.exp t - 1))
        (fun z => g (Real.exp t * p.1, z)) p.2

theorem t0adjGradGauss_of (h1 : T0gSmooth) (h2 : T0gPeriodic) (h3 : T0gBand)
    (h4 : T0gGrad) (h5 : T0gMem) (h6 : T0gAe) (h7 : T0gCgradBand) : T0adjGradGauss := by
  intro c ν hc t ht Φ h
  have hΦ : IsProfileTest c Φ.1 := Φ.2
  obtain ⟨hcont, hper, hband⟩ := h7 c Φ.1 hΦ
  have hmΨ : MemLp (t0gPsi ν t Φ.1) 2 (measureH c) := by
    have hsm : Continuous (fun p : Profile => (Φ.1 p)) := hΦ.smooth.continuous
    obtain ⟨s0, s1, L, hs0, hb⟩ := hΦ.band
    have := h5 c ν t hc ℝ Φ.1 hsm hΦ.periodic ⟨s0, s1, L, hs0, fun p hp => hb p hp⟩
    unfold t0gPsi; simpa using this
  have hmG : MemLp (UnforcedLeray.Short.PartIIa.cgrad 0 (t0gPsi ν t Φ.1)) 2 (measureH c) := by
    have := h5 c ν t hc MeridC _ hcont hper hband
    have hfun : UnforcedLeray.Short.PartIIa.cgrad 0 (t0gPsi ν t Φ.1) = fun p : Profile =>
        Real.exp (-t / 2) • UnforcedLeray.B0224.planeHeat (ν * p.1 * (Real.exp t - 1))
          (fun z => UnforcedLeray.Short.PartIIa.cgrad 0 Φ.1 (Real.exp t * p.1, z)) p.2 :=
      funext (h4 c ν t hc Φ.1 hΦ)
    rw [hfun]; exact this
  obtain ⟨s0, s1, hs0, hb⟩ := h3 c ν t Φ.1 hΦ
  have hΨ : GaussGradProfile c (t0gPsi ν t Φ.1) :=
    ⟨h1 c ν t hc Φ.1 hΦ, h2 c ν t Φ.1 hΦ, ⟨s0, s1, hs0, hb⟩, hmΨ, hmG⟩
  refine ⟨t0gPsi ν t Φ.1, hΨ, ?_⟩
  apply MeasureTheory.Lp.ext
  have hA := UnforcedLeray.B0224.T0adj_apply_ae hc ν t (h.toLp _)
  have hf : ((h.toLp _ : HSpace c MeridC) : Profile → MeridC) =ᵐ[measureH c]
      UnforcedLeray.Short.PartIIa.cgrad 0 Φ.1 := MemLp.coeFn_toLp h
  have hB := h6 c ν t hc _ hper _ hf
  have hC : (hΨ.2.2.2.2.toLp _ : Profile → MeridC) =ᵐ[measureH c]
      UnforcedLeray.Short.PartIIa.cgrad 0 (t0gPsi ν t Φ.1) := MemLp.coeFn_toLp _
  filter_upwards [hA, hB, hC] with p hpA hpB hpC
  rw [hpA, hpC, h4 c ν t hc Φ.1 hΦ p]
  simp only [hpB]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
