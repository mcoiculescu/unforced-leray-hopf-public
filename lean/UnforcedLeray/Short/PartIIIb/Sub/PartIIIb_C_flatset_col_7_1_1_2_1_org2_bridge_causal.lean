import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1_org2_bridge

/-!
# `BridgeCausal` from four leaves

Source `the November 2 reference manuscript`
1650-1656, 1684-1689.  The recentred driving `G` is bounded and supported in `s ∈ [s0,s1]`, so it
has an `H_g` representative `Gh`; `P₀ f' = M_s Gh`; `B0225.R0_Ms_ae_causalHeat` gives
`R₀ (M_s Gh) = causalHeat Gh`; and `causalHeat Gh = duhamel G` by slicing (Fubini) and
`q`-periodicity.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- `H_g`-representative of the recentred driving.  `G` alone is only bounded (no decay in `η`),
so membership in `H_g` comes from the hypothesis `P₀ f' = s • G` with `P₀ f' ∈ H`
(`M_s : H_g → H` is surjective; `Gh := M_s⁻¹ (P₀ f')`). -/
def CausalGhRep : Prop :=
  ∀ (c : ℝ) (_hc : 0 < c) (G : Chart → Fin 2 → ℝ), IsDriving c G →
    ∀ f' : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC,
      ((UnforcedLeray.Short.PartIIa.PepsC 0 c f' : UnforcedLeray.B0220.HSpace c
          UnforcedLeray.B0223.MeridC) : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
        =ᵐ[UnforcedLeray.B0220.measureH c]
        (fun p => WithLp.toLp 2 (fun i : Fin 2 => ((p.1 * G (NearInst.cellPt c p) i : ℝ) : ℂ))) →
    ∃ Gh : UnforcedLeray.B0220.HgSpace c UnforcedLeray.B0223.MeridC,
      (Gh : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
        =ᵐ[UnforcedLeray.B0220.measureHg c]
        fun p => WithLp.toLp 2 (fun i : Fin 2 => ((G (NearInst.cellPt c p) i : ℝ) : ℂ))

/-- `P₀ f' = M_s Gh` in `H` (`coeFn_Ms`, `Lp.ext_ae`; transfer of the a.e. identity from
`measureHg` to `measureH`, both being `withDensity` of the cell measure with a.e. positive
densities). -/
def CausalMsEq : Prop :=
  ∀ (c : ℝ) (_hc : 0 < c) (G : Chart → Fin 2 → ℝ),
    ∀ Gh : UnforcedLeray.B0220.HgSpace c UnforcedLeray.B0223.MeridC,
      ((Gh : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
        =ᵐ[UnforcedLeray.B0220.measureHg c]
        fun p => WithLp.toLp 2 (fun i : Fin 2 => ((G (NearInst.cellPt c p) i : ℝ) : ℂ))) →
      ∀ f' : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC,
        ((UnforcedLeray.Short.PartIIa.PepsC 0 c f' : UnforcedLeray.B0220.HSpace c
          UnforcedLeray.B0223.MeridC) : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
        =ᵐ[UnforcedLeray.B0220.measureH c]
        (fun p => WithLp.toLp 2 (fun i : Fin 2 => ((p.1 * G (NearInst.cellPt c p) i : ℝ) : ℂ))) →
      UnforcedLeray.Short.PartIIa.PepsC 0 c f' =
        UnforcedLeray.B0220.Ms c UnforcedLeray.B0223.MeridC Gh

/-- Fubini slicing from the `measureHg` identity: for a.e. `σ > 0` and a.e. `z`,
`periodize Gh (σ,z) = G (σ,z)` (`periodize` and `G` are `c`-periodic in `q`). -/
def CausalSliceAe : Prop :=
  ∀ (c : ℝ) (_hc : 0 < c) (G : Chart → Fin 2 → ℝ), IsDriving c G →
    ∀ Gh : UnforcedLeray.B0220.HgSpace c UnforcedLeray.B0223.MeridC,
      ((Gh : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
        =ᵐ[UnforcedLeray.B0220.measureHg c]
        fun p => WithLp.toLp 2 (fun i : Fin 2 => ((G (NearInst.cellPt c p) i : ℝ) : ℂ))) →
      ∀ i : Fin 2, ∀ᵐ σ ∂(volume.restrict (Ioi (0 : ℝ))), ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)),
        UnforcedLeray.B0220.periodize c (⇑Gh) (σ, z) i = (G (σ, z) i : ℂ)

/-- `causalHeat Gh = duhamel G` `measureH`-a.e. (planeHeat depends only on the a.e. class of its
input for `θ > 0`; `θ = ν (s - σ) = 0` only at `σ = s`; periodicity in `q` identifies `p` with
`cellPt c p`). -/
def CausalEqDuhamel : Prop :=
  ∀ (c ν μ : ℝ) (_hc : 0 < c) (_hν : 0 < ν) (G : Chart → Fin 2 → ℝ), IsDriving c G →
    ∀ Gh : UnforcedLeray.B0220.HgSpace c UnforcedLeray.B0223.MeridC,
      (∀ i : Fin 2, ∀ᵐ σ ∂(volume.restrict (Ioi (0 : ℝ))), ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)),
        UnforcedLeray.B0220.periodize c (⇑Gh) (σ, z) i = (G (σ, z) i : ℂ)) →
      UnforcedLeray.B0225.causalHeat c ν (μ : ℂ) (⇑Gh) =ᵐ[UnforcedLeray.B0220.measureH c]
        (fun p => WithLp.toLp 2 (fun i : Fin 2 => duhamel ν μ G (NearInst.cellPt c p) i))

theorem bridgeCausal_of (h1 : CausalGhRep) (h2 : CausalMsEq) (h3 : CausalSliceAe)
    (h4 : CausalEqDuhamel) : BridgeCausal := by
  intro c ν μ hc G hν hμ hG f' hP
  obtain ⟨Gh, hGh⟩ := h1 c hc G hG f' hP
  have e1 := h2 c hc G Gh hGh f' hP
  have e2 := UnforcedLeray.B0225.R0_Ms_ae_causalHeat (E := UnforcedLeray.B0223.MeridC) hc ν
    (μ := (μ : ℂ)) (by simpa using hμ) Gh
  have e3 := h4 c ν μ hc hν G hG Gh (h3 c hc G hG Gh hGh)
  rw [e1]
  exact e2.trans e3

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
