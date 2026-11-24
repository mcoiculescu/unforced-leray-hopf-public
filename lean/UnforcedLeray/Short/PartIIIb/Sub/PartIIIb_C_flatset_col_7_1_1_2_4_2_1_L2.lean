import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_1_L2.Slices
import UnforcedLeray.Short.PartIIIb.NearInst.Body.Defs
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.CellPtInvH

/-!
# `sfcDuhamelLift`: the Duhamel identity for any lift (decomposition of
`PartIII-b:C/flatset/col/7/1/1/2/4/2/1/2`)

Source `the November 2 reference manuscript` 1650-1656, 1684-1689.
For a lift `f'` of `g` (`SFCLift g f'`), `T₀flat f' = R₀ P₀ f'` is the transport of `R₀ g`
(`IsBodyTransport`); `P₀ f' = M_s G` (`Ms_surjective`); `B0225.R0_Ms_ae_causalHeat` gives
`R₀ M_s G = causalHeat G`; `G = s⁻¹ P₀ f' = sfcGp` a.e.; the causal heat depends only on the
periodic slices, and is `cellPt`-invariant; finally the ageμ-a.e. statement is transported from
`measureH` through `cellPtInv` (`cellPtInvH_eq`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem cellPt_cellPtInv' {c : ℝ} (x : UnforcedLeray.B0220.Profile)
    (hx : x.2.1 ∈ Ico (-c / 2) (c / 2)) :
    NearInst.cellPt c (NearInst.Masked.cellPtInv c x) = x := by
  obtain ⟨s, q, η⟩ := x
  obtain ⟨hq1, hq2⟩ := hx
  unfold NearInst.cellPt NearInst.Masked.cellPtInv
  by_cases hq : 0 < q
  · have h1 : (if 0 < q then q else q + c) = q := if_pos hq
    simp only [h1, if_pos hq2]
  · have h1 : (if 0 < q then q else q + c) = q + c := if_neg hq
    have h2 : ¬ (q + c < c / 2) := by linarith
    simp only [h1, if_neg h2]
    simp

theorem sfcDuhamelLift : SFCDuhamelLift := by
  unfold SFCDuhamelLift
  intro c ν μ hc R0 g hctx f' hf'
  unfold ClassicalCtx at hctx
  obtain ⟨hν, hμ, hBT, _⟩ := hctx
  -- transport of the body operator
  have hT := hBT g f' hf'
  -- the lift of the flat projection `P₀ f' = M_s G`
  obtain ⟨G, hG⟩ := UnforcedLeray.B0220.Ms_surjective (E := UnforcedLeray.B0223.MeridC) c
    (UnforcedLeray.Short.PartIIa.PepsC 0 c f')
  have hμ' : 0 < (μ : ℂ).re + 1 / 4 := by simpa using hμ
  have hR := UnforcedLeray.B0225.R0_Ms_ae_causalHeat hc ν hμ' G
  rw [hG] at hR
  -- `G = s⁻¹ P₀ f'` a.e. on the cell
  have hGae : (G : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) =ᵐ[
      UnforcedLeray.B0220.measureH c] sfcGp hc f' := by
    have h1 : ∀ᵐ p ∂UnforcedLeray.B0220.measureH c,
        (UnforcedLeray.Short.PartIIa.PepsC 0 c f' : UnforcedLeray.B0220.Profile →
          UnforcedLeray.B0223.MeridC) p = p.1 • (G : UnforcedLeray.B0220.Profile →
          UnforcedLeray.B0223.MeridC) p := by
      filter_upwards [UnforcedLeray.B0220.coeFn_Ms c G] with p hp
      rw [hG] at hp
      exact hp
    filter_upwards [h1, UnforcedLeray.B0220.ae_cell_measureH c] with p hp hcell
    have hp1 : (0 : ℝ) < p.1 := hcell.1
    unfold sfcGp
    have hne : ((p.1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp1.ne'
    rw [hp, ← Complex.coe_smul, smul_smul, inv_mul_cancel₀ hne, one_smul]
  -- causal heat of `G` and of `sfcGp` agree a.e. on the cell
  have hslice := ae_slices_of_measureH hc hGae
  have hCH : ∀ᵐ p ∂UnforcedLeray.B0220.measureH c,
      UnforcedLeray.B0225.causalHeat c ν (μ : ℂ) (G : UnforcedLeray.B0220.Profile →
        UnforcedLeray.B0223.MeridC) p =
        UnforcedLeray.B0225.causalHeat c ν (μ : ℂ) (sfcGp hc f') p := by
    filter_upwards [UnforcedLeray.B0220.ae_cell_measureH c] with p hcell
    exact causalHeat_congr_of_slices (μ : ℂ) hν hslice p hcell.1
  -- the velocity identity on the cell, as an identity on `measureH`
  have hQ : ∀ᵐ p ∂UnforcedLeray.B0220.measureH c, ∀ i : Fin 2,
      NearInst.velC (R0 g) (NearInst.cellPt c p) i =
        UnforcedLeray.B0225.causalHeat c ν (μ : ℂ) (sfcGp hc f') (NearInst.cellPt c p) i := by
    filter_upwards [hT, hR, hCH] with p h1 h2 h3
    have hm : NearInst.merC (R0 g (NearInst.cellPt c p)) =
        UnforcedLeray.B0225.causalHeat c ν (μ : ℂ) (G : UnforcedLeray.B0220.Profile →
          UnforcedLeray.B0223.MeridC) p := by
      rw [← h1]
      exact h2
    intro i
    have e1 : UnforcedLeray.B0225.causalHeat c ν (μ : ℂ) (sfcGp hc f')
        (NearInst.cellPt c p) = UnforcedLeray.B0225.causalHeat c ν (μ : ℂ) (G :
          UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) p := by
      rw [causalHeat_cellPt hc ν (μ : ℂ), h3]
    rw [e1, ← hm]
    rfl
  -- transport from `measureH` to `ageμ c (-3/2)` through `cellPtInv`
  have hAE : ∀ᵐ x ∂(Axi.ageμ c (-3 / 2)), ∀ i : Fin 2,
      NearInst.velC (R0 g) x i =
        UnforcedLeray.B0225.causalHeat c ν (μ : ℂ) (sfcGp hc f') x i := by
    have hmap : Measure.map (NearInst.Masked.cellPtInv c) (Axi.ageμ c (-3 / 2)) =
        ENNReal.ofReal c⁻¹ • UnforcedLeray.B0220.measureH c :=
      NearInst.Masked.cellPtInvH_eq c hc
    have hy : ∀ᵐ y ∂(Measure.map (NearInst.Masked.cellPtInv c) (Axi.ageμ c (-3 / 2))),
        ∀ i : Fin 2, NearInst.velC (R0 g) (NearInst.cellPt c y) i =
          UnforcedLeray.B0225.causalHeat c ν (μ : ℂ) (sfcGp hc f') (NearInst.cellPt c y) i := by
      rw [hmap]
      exact Measure.ae_smul_measure hQ _
    have hx := ae_of_ae_map (NearInst.Masked.measurable_cellPtInv c).aemeasurable hy
    filter_upwards [hx, Axi.ae_ageμ_mem hc (-3 / 2)] with x hx1 hx2
    have hxc : x.2.1 ∈ Ico (-c / 2) (c / 2) := hx2.2.1
    rw [cellPt_cellPtInv' x hxc] at hx1
    exact hx1
  exact hAE

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
