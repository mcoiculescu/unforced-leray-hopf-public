import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1_org2_bridge_causal

/-!
# `causalMsEq`: `P₀ f' = M_s Gh` in `H`

Source `the November 2 reference manuscript` 1650-1656. The `measureHg` a.e.
identity transfers to `measureH` (both are `withDensity` of the cell measure, with densities
positive on the cell), and `coeFn_Ms` gives `Ms Gh = s • Gh` a.e.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- Transfer of an a.e. property from `measureHg c` to `measureH c` (same cell, densities
`s^{1/2}` and `s^{-3/2}` both positive on the cell). -/
theorem ae_measureH_of_ae_measureHg_causalMs {c : ℝ}
    {P : UnforcedLeray.B0220.Profile → Prop}
    (h : ∀ᵐ p ∂UnforcedLeray.B0220.measureHg c, P p) :
    ∀ᵐ p ∂UnforcedLeray.B0220.measureH c, P p := by
  have hW : Measurable UnforcedLeray.B0220.weightHg := by
    unfold UnforcedLeray.B0220.weightHg
    fun_prop
  have hWH : Measurable UnforcedLeray.B0220.weightH := by
    unfold UnforcedLeray.B0220.weightH
    fun_prop
  have hcellM : MeasurableSet (UnforcedLeray.B0220.cell c) :=
    measurableSet_Ioi.prod (measurableSet_Ioc.prod MeasurableSet.univ)
  unfold UnforcedLeray.B0220.measureHg at h
  unfold UnforcedLeray.B0220.measureH
  rw [ae_withDensity_iff hW] at h
  rw [ae_withDensity_iff hWH]
  unfold UnforcedLeray.B0220.cellMeasure at h ⊢
  filter_upwards [h, ae_restrict_mem hcellM] with p hp hpc
  intro _
  apply hp
  have hpos : 0 < p.1 := hpc.1
  exact ne_of_gt (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hpos _))

theorem causalMsEq : CausalMsEq := by
  intro c hc G Gh hGh f' hP
  apply Lp.ext
  have hGa : ∀ᵐ p ∂UnforcedLeray.B0220.measureH c,
      (Gh : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) p
        = WithLp.toLp 2 (fun i : Fin 2 => ((G (NearInst.cellPt c p) i : ℝ) : ℂ)) :=
    ae_measureH_of_ae_measureHg_causalMs hGh
  filter_upwards [hP, UnforcedLeray.B0220.coeFn_Ms c Gh, hGa]
    with p hp1 hp2 hp3
  rw [hp2, hp3, hp1, ← WithLp.toLp_smul]
  congr 1
  funext i
  simp [Complex.real_smul]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
