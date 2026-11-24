import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_proj2

/-!
# `PepsC0Slices` from three slice-wise facts (audit decomposition of task
`PartIII-b:C/flatset/col/7/1/1/2/4/2/3/2`)

Source `the November 2 reference manuscript`
1650-1656, 1676 (`P₀` is the `ε = 0` member: the ordinary planar cylinder Leray projection, slice by
slice).  With `W := Ψ` as an element of `L²(measureH c)`: `W ∈ solenoidalHC 0 c` and `f' - W ⟂
solenoidalHC 0 c`, so `W = PepsC 0 c f'`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (P0C)

/-- The hypotheses of `PepsC0Slices` on `(f', Φ, Ψ)`. -/
def SliceHyp (c : ℝ) (f' : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC)
    (Φ Ψ : Chart → Fin 2 → ℂ) : Prop :=
  (∀ i, Measurable fun p => Φ p i) ∧ (∀ i, Measurable fun p => Ψ p i) ∧
    (∀ s q η, Φ (s, (q + c, η)) = Φ (s, (q, η))) ∧
    (∀ s q η, Ψ (s, (q + c, η)) = Ψ (s, (q, η))) ∧
    ((f' : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
      =ᵐ[UnforcedLeray.B0220.measureH c] (fun p => toMC (Φ p))) ∧
    (∀ σ : ℝ, 0 < σ →
      (fun y => Ψ (σ, y)) =ᵐ[UnforcedLeray.Cyl.cellμ c] P0C c (fun y => Φ (σ, y)))

/-- **(i) `L²` membership of the slice projection** (source 1650-1656, 1676).  Tonelli on
`s^(-3/2) ds × cell`: for a.e. `σ` the slice `Φ_σ` is `L²` on the cell (`f' ∈ L²`; periodicity moves
`(0,c]` to `[-c/2,c/2)`), and `∫_cell |P0C Φ_σ|² ≤ ∫_cell |Φ_σ|²` (`IIIa.ce_contract`,
`IIIa.ce_vnorm_P0C`); `Ψ_σ = P0C Φ_σ` a.e. on the cell. -/
def PepsC0SliceL2 : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (f' : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC)
    (Φ Ψ : Chart → Fin 2 → ℂ), SliceHyp c f' Φ Ψ →
    MemLp (fun p => toMC (Ψ p)) 2 (UnforcedLeray.B0220.measureH c)

/-- **(ii) `Ψ` is exactly solenoidal** (source 1650-1656, 1676).  For a test `Φt` of
`solenoidalHC`'s spanning family, `⟨cgrad 0 Φt, Ψ⟩ = ∫ σ^(-3/2) (slice integral) dσ` by Fubini, and
each slice integral vanishes by `IIIa.p0DivFreeC` (`Φt(σ,·)` is a `B0579.IsCylTest`). -/
def PepsC0SliceSolenoidal : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (f' : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC)
    (Φ Ψ : Chart → Fin 2 → ℂ) (_ : SliceHyp c f' Φ Ψ)
    (hmem : MemLp (fun p => toMC (Ψ p)) 2 (UnforcedLeray.B0220.measureH c)),
    hmem.toLp _ ∈ UnforcedLeray.Short.PartIIa.solenoidalHC 0 c

/-- **(iii) The residual `f' - Ψ` is orthogonal to the exact solenoidal subspace** (source 1650-1656,
1676).  For `b ∈ solenoidalHC 0 c`, testing with `χ(s) s^(3/2) ψ(q,η)` (countable dense family of
cylinder tests) shows the slices `b_σ` weakly divergence free for a.e. `σ`; each slice pairing of
`Φ_σ - P0C Φ_σ` with `b_σ` vanishes (`IIIa.p0OrthC`, `Cyl.inner_P0_comm`, `Cyl.P0_eq_self`);
integrate in `σ`. -/
def PepsC0SliceOrth : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (f' : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC)
    (Φ Ψ : Chart → Fin 2 → ℂ) (_ : SliceHyp c f' Φ Ψ)
    (hmem : MemLp (fun p => toMC (Ψ p)) 2 (UnforcedLeray.B0220.measureH c)),
    ∀ b ∈ UnforcedLeray.Short.PartIIa.solenoidalHC 0 c,
      inner ℂ (f' - hmem.toLp _) b = 0

theorem pepsC0Slices_of (h1 : PepsC0SliceL2) (h2 : PepsC0SliceSolenoidal)
    (h3 : PepsC0SliceOrth) : PepsC0Slices := by
  intro c hc f' Φ Ψ hΦm hΨm hΦp hΨp hf hΨ
  have hH : SliceHyp c f' Φ Ψ := ⟨hΦm, hΨm, hΦp, hΨp, hf, hΨ⟩
  have hmem := h1 c hc f' Φ Ψ hH
  have hW := h2 c hc f' Φ Ψ hH hmem
  have hO := h3 c hc f' Φ Ψ hH hmem
  have hP : UnforcedLeray.Short.PartIIa.PepsC 0 c f' = hmem.toLp _ :=
    Submodule.eq_starProjection_of_mem_of_inner_eq_zero hW hO
  have hcoe := hmem.coeFn_toLp
  rw [hP]
  exact hcoe

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
