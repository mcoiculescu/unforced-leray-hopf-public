import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8_3_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8_5

/-!
# `PartIII-b:C/asrc/ra/8/3/3` : `RTrainMeas` from `HpAC2` and `C¹` of `Σ_jV_j`

Source: `the November 2 reference manuscript`
5023-5028, 4978.  For `s > 0`, `x ↦ rTrain` is continuous: `hpA` is `C²` in `x` (`HpAC2`), the
train is smooth (`IsTrain.smooth_v`), and `vsum = Σ_jV_j` is `C¹` (leaf `VsumC1`: Gaussian lattice
sum of smooth maps with locally uniformly summable derivatives, source 4978).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (Params)

/-- **Leaf: `Σ_jV_j` is `C¹` for `s > 0`** (source 4978: "the sums and their required derivatives
converge by Gaussian decay"; `V_j = a⁻²e^{-|x_j|²/(4a)}Jx_j`, `a = 1 + νs ≥ 1`, locally uniform
Gaussian bounds of `V_j, DV_j` via `gp_fderiv_Vj_norm`; use `contDiffOn_tsum_shift`, task `ra/5/1`,
or `hasFDerivAt_tsum_of_isPreconnected`). -/
def VsumC1 : Prop :=
  ∀ ν s : ℝ, 0 < ν → 0 < s → ContDiff ℝ 1 (vsum ν s)

theorem trainPl_contDiff_slice {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {s : ℝ}
    (hs : 0 < s) : ContDiff ℝ 1 (trainPl tr s) := by
  have h1 := trainPl_contDiffOn tr
  have hc : ContDiff ℝ 1 (fun x : ℝ × ℝ => ((s, x) : ℝ × (ℝ × ℝ))) :=
    contDiff_const.prodMk contDiff_id
  have := h1.comp hc.contDiffOn (s := univ) (fun x _ => by simp [hs])
  simpa [contDiffOn_univ, Function.comp_def] using this

theorem rTrain_continuous (as : ℝ) (χf : ℝ → ℝ) (hH : HpAC2 as χf) (hV : VsumC1)
    (hχ : IsSourceCutoffC χf) {ν c : ℝ} (hν : 0 < ν) (tr : UnforcedLeray.B0140.TrainSol ν c)
    {A : ℝ → Mat3} (hA : IsAffElem as A) {s : ℝ} (hs : 0 < s) :
    Continuous (rTrain χf tr A s) := by
  have hh := hpA_contDiff_slice as χf hH hχ hν hA hs
  have hg : ContDiff ℝ 1 (fun y => trainPl tr s y - vsum ν s y) :=
    (trainPl_contDiff_slice tr hs).sub (hV ν s hν hs)
  have hD1 : Continuous (fderiv ℝ (hpA ν χf A s)) := hh.continuous_fderiv (by norm_num)
  have hD2 : Continuous (fderiv ℝ (fun y => trainPl tr s y - vsum ν s y)) :=
    hg.continuous_fderiv one_ne_zero
  unfold rTrain
  exact (hD1.clm_apply hg.continuous).add (hD2.clm_apply hh.continuous)

theorem rTrainMeas_of (as : ℝ) (χf : ℝ → ℝ) (hH : HpAC2 as χf) (hV : VsumC1) :
    RTrainMeas as χf := by
  intro hχ p d dm dp hreg A hA s hs
  have hc := rTrain_continuous as χf hH hV hχ p.ν_pos p.train hA hs
  have : Continuous (fun x => ENNReal.ofReal (‖toMer (rTrain χf p.train A s x)‖ ^ 2)) :=
    ENNReal.continuous_ofReal.comp ((toMer_continuous.comp hc).norm.pow 2)
  exact this.measurable.aemeasurable

end UnforcedLeray.Short.PartIIIb.Concrete
