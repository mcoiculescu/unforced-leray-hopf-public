import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1_2_3_1
import UnforcedLeray.Short.PartIIIa.Clock.LongAssemble.L4
import UnforcedLeray.Short.PartIIIa.Clock.LongAssemble.H1

/-!


Source of record: `the November 2 reference manuscript`, lines 2836-2860 and
2982-2989 (`eq:short-causal-scales`).

Target: `TFKDatumNorm m` (defined in `Sub/PartIII-b_C_asrc_kflat_1_2_3_1.lean`, unchanged).

Proof: with the fixed clock `a = clockA ν (11/10/ν) ≥ 1`, the scaling bound
`IIIa.xNorm_JscaleInv_le` (`L4.lean`, `‖J_a⁻¹ g‖_{X_{m,c/√a}} ≤ a^{3/2} ‖g‖_{X_{m,c}}` for
`1 ≤ a`, `0 ≤ m`) applied to `g = xFn w`, together with `‖xFn w‖_{X_{m,c}} = ‖w‖`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open FlatSettingInst

/-- The weighted norm of the planar function of `w ∈ X_{m,c}` is the norm of `w`. -/
theorem xNorm_xFn_eq {c m : ℝ} [Fact (1 < m)] (w : Xmc c m) :
    UnforcedLeray.Short.IIIa.xNorm c m (xFn w) = ENNReal.ofReal ‖w‖ := by
  have h1 : ‖w‖ = ‖(w : XAmb c m)‖ := (Submodule.coe_norm w).symm
  rw [h1, Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_lt_top (w : XAmb c m)).ne]
  unfold UnforcedLeray.Short.IIIa.xNorm
  rfl

/-- **`tfkDatumNorm`** (source 2836-2860, 2982-2989): the datum norm comparison at the fixed clock
`a = clockA ν (11/10/ν)`. -/
theorem tfkDatumNorm (m : ℝ) [Fact (1 < m)] : TFKDatumNorm m := by
  intro ν hν c hc _hfact
  have hs : 0 ≤ 11 / 10 / ν := by positivity
  have ha1 : 1 ≤ UnforcedLeray.Short.IIIa.clockA ν (11 / 10 / ν) :=
    UnforcedLeray.Short.IIIa.one_le_clockA hν.le hs
  have h1m : 1 < m := Fact.out
  have hm0 : 0 ≤ m := by linarith
  refine ⟨UnforcedLeray.Short.IIIa.clockA ν (11 / 10 / ν) ^ ((3 : ℝ) / 2), ?_, fun w => ?_⟩
  · exact Real.rpow_nonneg (by linarith) _
  · have hb := UnforcedLeray.Short.IIIa.xNorm_JscaleInv_le c m _ hm0 ha1 (xFn w) (xFn_memLp w)
    rw [xNorm_xFn_eq] at hb
    refine hb.trans (le_of_eq ?_)
    exact (ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith) _)).symm

end UnforcedLeray.Short.PartIIIb.Concrete
