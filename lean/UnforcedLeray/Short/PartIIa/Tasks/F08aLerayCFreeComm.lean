import UnforcedLeray.Short.PartIIa.Sub.F08
import UnforcedLeray.Units.B0418.Operator
import UnforcedLeray.Units.B0421.FreeC
import UnforcedLeray.Lib.LerayC.Complex
import UnforcedLeray.Lib.LerayC.Transfer
import UnforcedLeray.Lib.LerayC.Dilate
import UnforcedLeray.Lib.HeatR3B.FreeLp

/-!
# Part II-a, task `PartII-a:F08/1`: the complex Leray projection commutes with `S_ν(r)`

Source `the November 2 reference manuscript` lines 1498-1500. Plan:
(a) `lerayC = cx (lerayLp)` (the complexification of the real Leray projection);
(b) the real Leray projection commutes with the free semigroup `S_ν(r)`, because
`S_ν(r) = e^{r/2} · (dilation by e^{r/2}) ∘ (heat at time ν(e^r-1))` on `L^p(ℝ³;ℝ³)`
(`Heat.freeEvolutionLp_rep_heatLp`), and the Leray projection commutes with both factors
(`lerayLp_dilate_apply`, `lerayLp_heat`);
(c) `cx` is multiplicative (`cx_comp`), so the complex commutation follows.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace UnforcedLeray.Short.PartIIa

/-- (a) The complex Leray projection is the complexification of the real one. -/
theorem lerayC_eq_cx_F08 (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ⊤) :
    UnforcedLeray.RieszLp.lerayC p hp1 hp =
      UnforcedLeray.B0421.cx (UnforcedLeray.RieszLp.lerayLp p hp1 hp) := by
  ext1 F
  exact (UnforcedLeray.RieszLp.lerayC_apply hp1 hp F).trans
    (UnforcedLeray.B0421.cx_apply _ F).symm

/-- (b) The real Leray projection commutes with the real free semigroup. -/
theorem lerayLp_freeSemigroup_F08 (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ⊤)
    (ν r : ℝ) :
    (UnforcedLeray.RieszLp.lerayLp p hp1 hp).comp
        (UnforcedLeray.B0418.freeSemigroupLp hp ν r) =
      (UnforcedLeray.B0418.freeSemigroupLp hp ν r).comp
        (UnforcedLeray.RieszLp.lerayLp p hp1 hp) := by
  set b : ℝ := Real.exp (r / 2) with hbdef
  have hb : 0 < b := Real.exp_pos _
  set θ : ℝ := ν * (Real.exp r - 1) with hθdef
  -- `S_ν(r) v = b · D_b (H_θ v)` in `L^p`
  have hS : ∀ v : Lp Space p (volume : Measure Space),
      UnforcedLeray.B0418.freeSemigroupLp hp ν r v =
        b • UnforcedLeray.RieszLp.dilateLp p hp hb.ne'
          (UnforcedLeray.Heat.heatLp (AddMonoidHom.id Space) continuous_id θ v) := by
    intro v
    apply Lp.ext
    filter_upwards [UnforcedLeray.Heat.freeEvolutionLp_rep_heatLp hp ν r v,
      Lp.coeFn_smul b (UnforcedLeray.RieszLp.dilateLp p hp hb.ne'
        (UnforcedLeray.Heat.heatLp (AddMonoidHom.id Space) continuous_id θ v)),
      UnforcedLeray.RieszLp.coeFn_dilateLp hp hb.ne'
        (UnforcedLeray.Heat.heatLp (AddMonoidHom.id Space) continuous_id θ v)] with y h1 h2 h3
    simp only [Pi.smul_apply] at h1 h2 h3 ⊢
    rw [h1, h2, h3]
  have hD : ∀ w : Lp Space p (volume : Measure Space),
      UnforcedLeray.RieszLp.lerayLp p hp1 hp
          (UnforcedLeray.RieszLp.dilateLp p hp hb.ne' w) =
        UnforcedLeray.RieszLp.dilateLp p hp hb.ne'
          (UnforcedLeray.RieszLp.lerayLp p hp1 hp w) :=
    fun w => UnforcedLeray.RieszLp.lerayLp_dilate_apply hp1 hp hb w
  have hH : ∀ w : Lp Space p (volume : Measure Space),
      UnforcedLeray.RieszLp.lerayLp p hp1 hp
          (UnforcedLeray.Heat.heatLp (AddMonoidHom.id Space) continuous_id θ w) =
        UnforcedLeray.Heat.heatLp (AddMonoidHom.id Space) continuous_id θ
          (UnforcedLeray.RieszLp.lerayLp p hp1 hp w) :=
    fun w => DFunLike.congr_fun (UnforcedLeray.RieszLp.lerayLp_heat hp1 hp θ) w
  ext1 u
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hS, hS, map_smul,
    hD, hH]

/-- **`PartII-a:F08/1`** (source 1498-1500): the complex Leray projection commutes with the
free similarity semigroup `S_ν(r)` on `L^p(ℝ³;ℂ³)`. -/
theorem lerayCFreeComm_proof : LerayCFreeComm := by
  intro p _ hp1 hp ν r
  rw [UnforcedLeray.B0421.freeC, lerayC_eq_cx_F08 p hp1 hp]
  rw [← UnforcedLeray.B0421.cx_comp, ← UnforcedLeray.B0421.cx_comp,
    lerayLp_freeSemigroup_F08 p hp1 hp ν r]

end UnforcedLeray.Short.PartIIa
