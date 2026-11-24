import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_1.AdjDerivOf
import UnforcedLeray.Units.B0224.Operators

/-!
# Representatives of `T₀(s)*` (source `shorter-proof-2026-11-02.tex` 1650-1656)

Mirrors `B0224.coeFn_T0adj`, with the representative `φ` of the `H`-class `f` in place of `f`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace
open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- **Representatives of `T₀(s)*`** (source 1650-1656). -/
theorem t0adj_rep_ae : T0adjRepAE := by
  intro c ν hc s f φ hφ hfφ
  have hf := Lp.stronglyMeasurable f
  have h1 := Lp.coeFn_smul (Real.exp (-s / 2))
    ((UnforcedLeray.B0224.heatH hc (UnforcedLeray.B0224.measurable_heatTimeAdj ν s) ∘L
      UnforcedLeray.B0224.dilH (Real.exp_pos s)) f)
  refine h1.trans ?_
  have h2a := UnforcedLeray.B0224.coeFn_heatH hc
    (UnforcedLeray.B0224.measurable_heatTimeAdj ν s) (UnforcedLeray.B0224.dilH (Real.exp_pos s) f)
  have hdil : (UnforcedLeray.B0224.dilH (Real.exp_pos s) f : Profile → MeridC)
      =ᵐ[measureH c] UnforcedLeray.B0224.dil (Real.exp s) φ :=
    (UnforcedLeray.B0224.coeFn_dilH (Real.exp_pos s) f).trans
      (UnforcedLeray.B0224.dil_congr_ae (Real.exp_pos s) hf hφ hfφ)
  have h2b := UnforcedLeray.B0224.fiberHeat_congr_ae hc
    (UnforcedLeray.B0224.measurable_heatTimeAdj ν s) (Lp.stronglyMeasurable _)
    (UnforcedLeray.B0224.stronglyMeasurable_dil _ hφ) hdil
  filter_upwards [h2a, h2b] with p hpa hpb
  rw [Pi.smul_apply, ContinuousLinearMap.comp_apply, hpa, hpb]
  simp only [UnforcedLeray.B0224.fiberHeat, UnforcedLeray.B0224.dil,
    UnforcedLeray.B0220.periodize, UnforcedLeray.B0224.heatTimeAdj, t0adjFormula]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
