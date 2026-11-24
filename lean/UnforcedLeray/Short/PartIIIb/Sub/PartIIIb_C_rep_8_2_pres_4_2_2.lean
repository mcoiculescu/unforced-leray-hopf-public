import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2

/-!
# `ν_n ≤ 1` and `ρ_n ≥ 0` for large `n` (task `PartIII-b:C/rep/8/2/pres/4/2/2`)

Source `the November 2 reference manuscript`
2701-2706 (`ρ_b = P_ν ε^{3/11} e^{m₀/ν}`), 5926-5950 (the phase-locked `ν_n → 0`).

`ν_n = retNu D.Pl D.σ₀ n` tends to `0` (`retNu_tendsto`, which needs `Im λ ≠ 0`, from
`RepairStanding.omega_ne`), so `ν_n < 1` eventually.  The repair quantity
`rhoRep K L = ε^{3/11} e^{m₀/ν}` is a product of a real power of a positive `ε` and an
exponential, hence nonnegative at every level.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem nuLeOneRhoNonneg (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    NuLeOneRhoNonneg D := by
  have hlim : Tendsto (retNu D.Pl D.σ₀) atTop (nhds 0) :=
    retNu_tendsto D.σ₀ hst.omega_ne
  filter_upwards [hlim.eventually (gt_mem_nhds zero_lt_one)] with n hn
  refine ⟨le_of_lt hn, ?_⟩
  exact mul_nonneg (Real.rpow_nonneg (D.level n).ε_pos.le _) (Real.exp_pos _).le

end UnforcedLeray.Short.PartIIIb.Concrete
