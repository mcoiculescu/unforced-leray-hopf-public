import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_2_1_5
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_3_Comb.S1a

/-!
# `gkerMajIntegrable` (`PartIII-b:C/rep/2/6/3/2/1/5/7`)

Source `shorter-proof-2026-11-02.tex` 3603-3626, 3800-3807, 4171-4200.
This is the `hgI` step of `gkerIntegrable` (`S1a.lean`): the `h`-majorant `gkerMaj` is
integrable on `Ioi 0 × Space` for every base time `t₀`, from `sepGapMajorantIntegrable`
(`sepMajorant` integrable on `sepRho` at `n = 0`), its measurability (`gkerMaj_measurable`) and
the finiteness of the lintegral (`gkerMaj_lintegral_lt_top`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gkerMajIntegrable : GkerMajIntegrable := by
  intro μ P rOut T hμ hP hT hS t₀
  have hM : Integrable (sepMajorant μ T t₀ 0) sepRho :=
    sepGapMajorantIntegrable μ P rOut T hμ hP hT hS t₀ 0 (by norm_num)
  exact ⟨(gkerMaj_measurable μ P rOut T hT t₀).aestronglyMeasurable,
    gkerMaj_lintegral_lt_top μ P rOut T hT t₀ hM⟩

end UnforcedLeray.Short.PartIIIb.Concrete
