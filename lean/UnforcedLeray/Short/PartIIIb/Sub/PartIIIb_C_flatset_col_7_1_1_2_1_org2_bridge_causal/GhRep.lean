import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1_org2_bridge_causal

/-!
# `causalGhRep`: `H_g`-representative of the driving

Source `the November 2 reference manuscript`
1650-1656, 1684-1689.  `P₀ f' = s • G` lies in `H`, and `M_s : H_g → H` is onto
(`Ms_surjective`); `Gh := M_s⁻¹ (P₀ f')` is a representative of `G` for `s^{1/2} ds dq dη`.
(The unconditional statement is false: `IsDriving` has no `η`-decay, so `G` need not be in `H_g`.)
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- Transfer of an a.e. property from `measureH c` to `measureHg c`. -/
theorem ae_measureHg_of_ae_measureH_causalGh {c : ℝ}
    {P : UnforcedLeray.B0220.Profile → Prop}
    (h : ∀ᵐ p ∂UnforcedLeray.B0220.measureH c, P p) :
    ∀ᵐ p ∂UnforcedLeray.B0220.measureHg c, P p := by
  have hW : Measurable UnforcedLeray.B0220.weightHg := by
    unfold UnforcedLeray.B0220.weightHg
    fun_prop
  have hWH : Measurable UnforcedLeray.B0220.weightH := by
    unfold UnforcedLeray.B0220.weightH
    fun_prop
  have hcellM : MeasurableSet (UnforcedLeray.B0220.cell c) :=
    measurableSet_Ioi.prod (measurableSet_Ioc.prod MeasurableSet.univ)
  unfold UnforcedLeray.B0220.measureH at h
  unfold UnforcedLeray.B0220.measureHg
  rw [ae_withDensity_iff hWH] at h
  rw [ae_withDensity_iff hW]
  unfold UnforcedLeray.B0220.cellMeasure at h ⊢
  filter_upwards [h, ae_restrict_mem hcellM] with p hp hpc
  intro _
  apply hp
  have hpos : 0 < p.1 := hpc.1
  exact ne_of_gt (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hpos _))

theorem causalGhRep : CausalGhRep := by
  intro c _hc G _hG f' hP
  obtain ⟨Gh, hGh⟩ := UnforcedLeray.B0220.Ms_surjective (E := UnforcedLeray.B0223.MeridC) c
    (UnforcedLeray.Short.PartIIa.PepsC 0 c f')
  refine ⟨Gh, ae_measureHg_of_ae_measureH_causalGh ?_⟩
  filter_upwards [UnforcedLeray.B0220.coeFn_Ms c Gh, hP, UnforcedLeray.B0220.ae_cell_measureH c]
    with p hp1 hp2 hp3
  have hs : 0 < p.1 := hp3.1
  rw [hGh] at hp1
  have h3 : p.1 • (Gh : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) p
      = p.1 • WithLp.toLp 2 (fun i : Fin 2 => ((G (NearInst.cellPt c p) i : ℝ) : ℂ)) := by
    rw [← hp1, hp2, ← WithLp.toLp_smul]
    congr 1
    funext i
    simp [Complex.real_smul]
  exact smul_right_injective _ hs.ne' h3
end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
