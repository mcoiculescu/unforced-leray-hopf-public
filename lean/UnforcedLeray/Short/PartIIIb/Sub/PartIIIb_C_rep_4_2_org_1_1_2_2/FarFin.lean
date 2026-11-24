import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_4_2_org_1_1_2_2.Far
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.SepYoungRep.Inv.SrcFinite.RepairSepBridgeAE
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_1.ThinMass

/-!
# `PartIII-b:C/rep/4/2/org/1/1/2/2/far/1`: `sepThinSrcFinite`

Source `the November 2 reference manuscript`
3596-3626, 4155-4174, 5169-5176, 5573-5584.

The thin analogue of `sepOldSrcFinite`: the separated representative of the old thin source is the
cut source `oldCutSrc` of the chart representative `G = (χ_o(T₁,0)).fst`.  Its
`L²_τL^{22/19}_y` norm is finite by Hölder in the physical variable `y` with the weight
`W² = (1+(η/√(1+s))²)^{m_Z}` (`m_Z > 3/2`), the phase integral of the squared lift
(`chartPhaseLIntegral`, `ageWeightShift`) being the `Z_1` norm, and the dual integral
`∫_{s>a} s^{-5/2}(1+s)^{1/2} ds ∫ (1+x²)^{-11 m_Z/8} dx < ∞` (the thin mass tail).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace ThinFin

/-- **Hölder at one phase** (`1/r = 1/2 + 1/q'`, `r = 22/19`): for a positive weight `w`,
`(∫_A u^r)^{2/r} ≤ (∫_A w^{-11/8})^{8/11} ∫ w u²`. -/
theorem holder_phase (A : Set Space) (hA : MeasurableSet A) (w : Space → ℝ)
    (hw : ∀ y, 0 < w y) (hwm : Measurable w) (u : Space → ℝ≥0∞) (hu : Measurable u) :
    (∫⁻ y, (A.indicator u y) ^ (22 / 19 : ℝ)) ^ (19 / 11 : ℝ) ≤
      (∫⁻ y, A.indicator (fun y => ENNReal.ofReal (w y ^ (-(11 / 8 : ℝ)))) y) ^ (8 / 11 : ℝ) *
        ∫⁻ y, ENNReal.ofReal (w y) * u y ^ (2 : ℝ) := by
  have hpq : (19 / 8 : ℝ).HolderConjugate (19 / 11 : ℝ) := by
    rw [Real.holderConjugate_iff]
    constructor <;> norm_num
  set f : Space → ℝ≥0∞ := fun y => A.indicator (fun y => ENNReal.ofReal (w y ^ (-(11 / 19 : ℝ)))) y
    with hf
  set g : Space → ℝ≥0∞ := fun y => ENNReal.ofReal (w y ^ (11 / 19 : ℝ)) * u y ^ (22 / 19 : ℝ)
    with hg
  have hwr : ∀ e : ℝ, Measurable fun y => w y ^ e := fun e => hwm.pow_const e
  have hfm : Measurable f :=
    (Measurable.indicator (ENNReal.measurable_ofReal.comp (hwr _)) hA)
  have hgm : Measurable g :=
    (ENNReal.measurable_ofReal.comp (hwr _)).mul (hu.pow_const _)
  have hfg : ∀ y, A.indicator u y ^ (22 / 19 : ℝ) = f y * g y := by
    intro y
    by_cases hy : y ∈ A
    · simp only [hf, hg, Set.indicator_of_mem hy]
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg (hw y).le _),
        ← Real.rpow_add (hw y)]
      norm_num
    · simp only [hf, hg, Set.indicator_of_notMem hy]
      simp
  have hfq : ∀ y, f y ^ (19 / 8 : ℝ) =
      A.indicator (fun y => ENNReal.ofReal (w y ^ (-(11 / 8 : ℝ)))) y := by
    intro y
    by_cases hy : y ∈ A
    · simp only [hf, Set.indicator_of_mem hy]
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (hw y).le _) (by norm_num),
        ← Real.rpow_mul (hw y).le]
      norm_num
    · simp only [hf, Set.indicator_of_notMem hy]
      simp
  have hgp : ∀ y, g y ^ (19 / 11 : ℝ) = ENNReal.ofReal (w y) * u y ^ (2 : ℝ) := by
    intro y
    simp only [hg]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (hw y).le _) (by norm_num),
      ← Real.rpow_mul (hw y).le, ← ENNReal.rpow_mul]
    norm_num
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume : Measure Space) hpq hfm.aemeasurable
    hgm.aemeasurable
  have e1 : ∫⁻ y, (f * g) y = ∫⁻ y, (A.indicator u y) ^ (22 / 19 : ℝ) :=
    lintegral_congr fun y => (hfg y).symm
  have e2 : ∫⁻ y, f y ^ (19 / 8 : ℝ) =
      ∫⁻ y, A.indicator (fun y => ENNReal.ofReal (w y ^ (-(11 / 8 : ℝ)))) y :=
    lintegral_congr hfq
  have e3 : ∫⁻ y, g y ^ (19 / 11 : ℝ) = ∫⁻ y, ENNReal.ofReal (w y) * u y ^ (2 : ℝ) :=
    lintegral_congr hgp
  rw [e1, e2, e3] at hH
  have hr : (∫⁻ y, (A.indicator u y) ^ (22 / 19 : ℝ)) ^ (19 / 11 : ℝ) ≤
      ((∫⁻ y, A.indicator (fun y => ENNReal.ofReal (w y ^ (-(11 / 8 : ℝ)))) y) ^ (1 / (19 / 8 : ℝ)) *
        (∫⁻ y, ENNReal.ofReal (w y) * u y ^ (2 : ℝ)) ^ (1 / (19 / 11 : ℝ))) ^ (19 / 11 : ℝ) :=
    ENNReal.rpow_le_rpow hH (by norm_num)
  refine hr.trans (le_of_eq ?_)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  norm_num

/-- The squared transverse weight `W² = (1+(η/√(1+s))²)^{m_Z}` as a function of `(s, η)`. -/
def wfun (mZ s η : ℝ) : ℝ := (1 + (η / Real.sqrt (1 + s)) ^ 2) ^ mZ

theorem wfun_pos (mZ s η : ℝ) : 0 < wfun mZ s η :=
  Real.rpow_pos_of_pos (by positivity) _

theorem measurable_wfun (mZ : ℝ) : Measurable fun p : ℝ × ℝ => wfun mZ p.1 p.2 := by
  unfold wfun
  have h1 : Measurable fun p : ℝ × ℝ => Real.sqrt (1 + p.1) :=
    (measurable_const.add measurable_fst).sqrt
  exact (measurable_const.add ((measurable_snd.div h1).pow_const 2)).pow_const mZ

/-- **The dual integral is finite** (source 5573-5584: transverse integral
`∫ W^{-11/4} dη = (1+s)^{1/2} I`, then the tail `∫_a^∞ s^{-5/2}(1+s)^{1/2} ds`). -/
theorem dual_lt_top {R mZ a : ℝ} (hR : 0 < R) (ha : 0 < a) (hm : 4 / 11 < mZ) :
    ∫⁻ y : Space, {y : Space | a < age R y}.indicator
      (fun y => ENNReal.ofReal (wfun mZ (age R y) (trans R y) ^ (-(11 / 8 : ℝ)))) y < ⊤ := by
  set g : ℝ × ℝ → ℝ≥0∞ := fun p =>
    if a < p.1 then ENNReal.ofReal (wfun mZ p.1 p.2 ^ (-(11 / 8 : ℝ))) else 0 with hgdef
  have hgm : Measurable g :=
    Measurable.ite (measurableSet_lt measurable_const measurable_fst)
      (ENNReal.measurable_ofReal.comp ((measurable_wfun mZ).pow_const _)) measurable_const
  have hcongr : ∀ y : Space, {y : Space | a < age R y}.indicator
      (fun y => ENNReal.ofReal (wfun mZ (age R y) (trans R y) ^ (-(11 / 8 : ℝ)))) y =
        g (age R y, trans R y) := by
    intro y
    by_cases hy : a < age R y
    · simp [hgdef, hy]
    · simp [hgdef, hy]
  rw [lintegral_congr hcongr, lintegral_ringChart hR g hgm]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  have hH : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (p.1 ^ (-(5 / 2 : ℝ))) * g p :=
    (ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)).mul hgm
  rw [Measure.volume_eq_prod ℝ ℝ, setLIntegral_prod_univ _ hH]
  set I : ℝ≥0∞ := ∫⁻ x : ℝ, ENNReal.ofReal ((1 + x ^ 2) ^ (-(11 * mZ / 8))) with hI
  have hIlt : I < ⊤ := lintegral_I_lt_top (by linarith)
  have hinner : ∀ s ∈ Ioi (0 : ℝ), ∫⁻ η, ENNReal.ofReal (s ^ (-(5 / 2 : ℝ))) * g (s, η) =
      (Ioi a).indicator (fun s => I * ENNReal.ofReal (s ^ (-5 / 2 : ℝ) * Real.sqrt (1 + s))) s := by
    intro s hs
    have hs0 : (0 : ℝ) < s := hs
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    by_cases has : a < s
    · rw [Set.indicator_of_mem (show s ∈ Ioi a from has)]
      have hk : 0 < Real.sqrt (1 + s) := Real.sqrt_pos.2 (by linarith)
      have hg' : ∀ η : ℝ, g (s, η) =
          ENNReal.ofReal ((1 + (η / Real.sqrt (1 + s)) ^ 2) ^ (-(11 * mZ / 8))) := by
        intro η
        simp only [hgdef, has, ite_true]
        congr 1
        unfold wfun
        rw [← Real.rpow_mul (by positivity)]
        congr 1
        ring
      rw [lintegral_congr hg', lintegral_scale_rpow hk, ← mul_assoc,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg hs0.le _)]
      rw [show (-(5 / 2 : ℝ)) = -5 / 2 by norm_num, mul_comm]
    · rw [Set.indicator_of_notMem (show s ∉ Ioi a from has)]
      simp [hgdef, has]
  refine lt_of_le_of_lt (le_of_eq (setLIntegral_congr_fun measurableSet_Ioi hinner)) ?_
  rw [lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    Set.inter_eq_left.2 (Ioi_subset_Ioi ha.le), lintegral_const_mul' _ _ hIlt.ne]
  exact ENNReal.mul_lt_top hIlt (lt_of_le_of_lt (lintegral_tail_bound ha)
    (ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩))

/-- **Pointwise bound of the cut old source** (source 2683, 4161-4166): the cut source is bounded by
`s |G(chartOf)|` on the set `a < s`, `a = R²/(2r²)` (the disk `|z'| ≤ r` is `s ≥ R²/r²`). -/
theorem srcNorm_le (R c r : ℝ) (hR : 0 < R) (hr : 0 < r) (G : Chart → Ten3) (τ : ℝ) (y : Space) :
    IIIa.srcNorm (oldCutSrc R c r G) τ y ≤
      {y : Space | R ^ 2 / r ^ 2 / 2 < age R y}.indicator
        (fun y => ENNReal.ofReal (age R y) * ‖G (NearInst.chartOf R c y τ)‖ₑ) y := by
  unfold IIIa.srcNorm oldCutSrc
  by_cases h : NearInst.hRad y ≤ r
  · rw [if_pos h]
    have hF := cartLiftFrobBound R c G τ y
    have hage : (NearInst.chartOf R c y τ).1 = age R y := rfl
    rw [hage] at hF
    have hs : 0 ≤ age R y := by unfold age; positivity
    by_cases hy : R ^ 2 / r ^ 2 / 2 < age R y
    · rw [Set.indicator_of_mem (show y ∈ {y : Space | R ^ 2 / r ^ 2 / 2 < age R y} from hy)]
      calc ENNReal.ofReal (IIIa.tensorNorm (oldPhys R c G τ y))
          ≤ ENNReal.ofReal (age R y * ‖G (NearInst.chartOf R c y τ)‖) :=
            ENNReal.ofReal_le_ofReal hF
        _ = _ := by rw [ENNReal.ofReal_mul hs, ofReal_norm]
    · have hz : ϱ y = 0 := by
        by_contra hne
        have hpos : 0 < ϱ y := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hne)
        apply hy
        have h1 : R ^ 2 / r ^ 2 ≤ age R y := by
          unfold age
          exact div_le_div_of_nonneg_left (sq_nonneg R) (pow_pos hpos 2)
            (pow_le_pow_left₀ hpos.le h 2)
        have h2 : 0 < R ^ 2 / r ^ 2 := by positivity
        linarith
      have h0 : age R y = 0 := by unfold age; rw [hz]; simp
      rw [h0, zero_mul] at hF
      rw [Set.indicator_of_notMem (show y ∉ {y : Space | R ^ 2 / r ^ 2 / 2 < age R y} from hy)]
      exact le_of_eq (ENNReal.ofReal_eq_zero.2 hF)
  · rw [if_neg h]
    simp [IIIa.tensorNorm]

/-- **Finiteness of the `L²_τ L^{22/19}_y` norm of the cut old thin source** (source 3596-3626,
5169-5176, 5573-5584). -/
theorem thinCore {R c r mZ : ℝ} (hR : 0 < R) (hc : 0 < c) (hr : 0 < r) (hm : 4 / 11 < mZ)
    (G : Chart → Ten3) (hG : Measurable G)
    (hJ : ∫⁻ p, ‖G p‖ₑ ^ 2 ∂(z1Measure c mZ) < ⊤) :
    IIIa.ltauLq (2 * c / R) (22 / 19) (IIIa.srcNorm (oldCutSrc R c r G)) < ⊤ := by
  have hP0 : 0 < 2 * c / R := div_pos (mul_pos two_pos hc) hR
  set a : ℝ := R ^ 2 / r ^ 2 / 2 with ha_def
  have ha : 0 < a := by positivity
  set A : Set Space := {y : Space | a < age R y} with hA
  have hAm : MeasurableSet A := measurableSet_lt measurable_const (measurable_age R)
  set w : Space → ℝ := fun y => wfun mZ (age R y) (Axi.trans R y) with hw
  have hwpos : ∀ y, 0 < w y := fun y => wfun_pos _ _ _
  have hwm : Measurable w :=
    (measurable_wfun mZ).comp ((measurable_age R).prodMk (measurable_trans R))
  set u : ℝ → Space → ℝ≥0∞ := fun τ y =>
    ENNReal.ofReal (age R y) * ‖G (NearInst.chartOf R c y τ)‖ₑ with hu
  have hum : ∀ τ, Measurable (u τ) := by
    intro τ
    exact (ENNReal.measurable_ofReal.comp (measurable_age R)).mul
      (hG.comp ((oldCut_measurable_chartOf R c).comp
        (measurable_const.prodMk measurable_id))).enorm
  set K : ℝ≥0∞ := ∫⁻ y, A.indicator (fun y => ENNReal.ofReal (w y ^ (-(11 / 8 : ℝ)))) y with hK
  have hKlt : K < ⊤ := dual_lt_top hR ha hm
  set F : Chart → ℝ≥0∞ := fun p => ENNReal.ofReal (p.1 ^ 2) *
    (ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2) * ‖G p‖ₑ ^ 2) with hF
  have hWm : Measurable fun p : Chart =>
      ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2) :=
    ((NearInst.transWeight_measurable mZ).pow_const 2).ennreal_ofReal
  have hGm2 : Measurable fun p : Chart => ‖G p‖ₑ ^ 2 := hG.enorm.pow_const 2
  have hfm : Measurable fun p : Chart =>
      ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2) * ‖G p‖ₑ ^ 2 :=
    hWm.mul hGm2
  have hFm : Measurable F := ((measurable_fst.pow_const 2).ennreal_ofReal).mul hfm
  have hwF : ∀ τ y, ENNReal.ofReal (w y) * u τ y ^ (2 : ℝ) = F (NearInst.chartOf R c y τ) := by
    intro τ y
    have hwt : UnforcedLeray.Short.IIIa.transWeight mZ (NearInst.chartOf R c y τ) ^ 2 = w y :=
      transWeight_sq_eq mZ (NearInst.chartOf R c y τ).1 (NearInst.chartOf R c y τ).2.1
        (NearInst.chartOf R c y τ).2.2
    have hs : 0 ≤ age R y := by unfold age; positivity
    have hage : (NearInst.chartOf R c y τ).1 = age R y := rfl
    simp only [hF, hu, hwt, hage]
    rw [ENNReal.rpow_two, mul_pow, ENNReal.ofReal_pow hs]
    ring
  have hpt : ∀ τ : ℝ, (∫⁻ y, IIIa.srcNorm (oldCutSrc R c r G) τ y ^ (22 / 19 : ℝ)) ^
      (2 / (22 / 19) : ℝ) ≤ K ^ (8 / 11 : ℝ) * ∫⁻ y, F (NearInst.chartOf R c y τ) := by
    intro τ
    have e : (2 / (22 / 19) : ℝ) = 19 / 11 := by norm_num
    rw [e]
    calc (∫⁻ y, IIIa.srcNorm (oldCutSrc R c r G) τ y ^ (22 / 19 : ℝ)) ^ (19 / 11 : ℝ)
        ≤ (∫⁻ y, (A.indicator (u τ) y) ^ (22 / 19 : ℝ)) ^ (19 / 11 : ℝ) := by
          refine ENNReal.rpow_le_rpow (lintegral_mono fun y => ?_) (by norm_num)
          exact ENNReal.rpow_le_rpow (srcNorm_le R c r hR hr G τ y) (by norm_num)
      _ ≤ K ^ (8 / 11 : ℝ) * ∫⁻ y, ENNReal.ofReal (w y) * u τ y ^ (2 : ℝ) :=
          holder_phase A hAm w hwpos hwm (u τ) (hum τ)
      _ = _ := by
          congr 1
          exact lintegral_congr fun y => hwF τ y
  unfold IIIa.ltauLq
  refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
  have hmain := chartPhaseLIntegral R c hR hc F hFm
  have hshift : ∫⁻ p, F p ∂(ageμ c (-5 / 2)) =
      ∫⁻ p, ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2) * ‖G p‖ₑ ^ 2
        ∂(ageμ c (-1 / 2)) :=
    ageWeightShift c hc _ hfm
  have hz1 : ∫⁻ p, ‖G p‖ₑ ^ 2 ∂(z1Measure c mZ) =
      ∫⁻ p, ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2) * ‖G p‖ₑ ^ 2
        ∂(ageμ c (-1 / 2)) := by
    unfold z1Measure
    rw [lintegral_withDensity_eq_lintegral_mul _ hWm hGm2]
    rfl
  rw [hshift, ← hz1] at hmain
  have hfin : ENNReal.ofReal (2 * c / R) * ENNReal.ofReal (Real.pi * R ^ 2) *
      ∫⁻ p, ‖G p‖ₑ ^ 2 ∂(z1Measure c mZ) < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top) hJ
  have hbound : ∫⁻ τ in Ioc 0 (2 * c / R), (∫⁻ y, IIIa.srcNorm (oldCutSrc R c r G) τ y ^
      (22 / 19 : ℝ)) ^ (2 / (22 / 19) : ℝ) ≤
      K ^ (8 / 11 : ℝ) * (ENNReal.ofReal (2 * c / R) * ENNReal.ofReal (Real.pi * R ^ 2) *
        ∫⁻ p, ‖G p‖ₑ ^ 2 ∂(z1Measure c mZ)) := by
    calc _ ≤ ∫⁻ τ in Ioc 0 (2 * c / R), K ^ (8 / 11 : ℝ) * ∫⁻ y, F (NearInst.chartOf R c y τ) :=
          lintegral_mono fun τ => hpt τ
      _ = K ^ (8 / 11 : ℝ) * ∫⁻ τ in Ioc 0 (2 * c / R), ∫⁻ y, F (NearInst.chartOf R c y τ) :=
          lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hKlt.ne)
      _ = _ := by rw [hmain]
  refine (ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (ENNReal.ofReal_pos.2 hP0)) ?_).ne
  exact lt_of_le_of_lt hbound (ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hKlt.ne) hfin)

end ThinFin

/-- The `Z_1` measure is dominated by the gain-weighted one (`g⁻² ≥ e^{-2|γ|/ν}`). -/
theorem z1_le_gain (c mZ γ ν : ℝ) (hν : 0 < ν) (f : Chart → ℝ≥0∞) (hf : Measurable f) :
    ENNReal.ofReal (Real.exp (-(2 * |γ| / ν))) * ∫⁻ p, f p ∂(z1Measure c mZ) ≤
      ∫⁻ p, f p ∂(gainZ1Measure c mZ γ ν) := by
  have hG : Measurable (fun p : Chart => ENNReal.ofReal (ginv γ ν p ^ 2)) :=
    ((NearInst.ginv_measurable' γ ν).pow_const 2).ennreal_ofReal
  unfold gainZ1Measure
  rw [lintegral_withDensity_eq_lintegral_mul _ hG hf, ← lintegral_const_mul _ hf]
  refine lintegral_mono fun p => ?_
  simp only [Pi.mul_apply]
  exact mul_le_mul_of_nonneg_right
    (ENNReal.ofReal_le_ofReal (l8_ginv_sq_ge γ ν hν p)) zero_le

/-- **The separated cut source of a measurable chart tensor vanishing for `ν s ≤ 6/5`** (source
4155-4171, 2684-2703; the proof of `thinSepBridge` with the explicit source). -/
theorem thinCutFacts (c ν ε : ℝ) (hc : 0 < c) (hν : 0 < ν) (hε : 0 < ε) (g : Chart → Ten3)
    (hgm : Measurable g)
    (hchart : ∀ᵐ p ∂(ageμ c (-1 / 2)), (ν * p.1 ≤ 6 / 5 → g p = 0)) :
    IIIa.IsSepSource (2 * ε * c) (ε⁻¹ * Real.sqrt (5 * ν / 6))
        (oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) g) ∧
      (∀ᵐ x : ℝ × Space ∂volume, oldPhys ε⁻¹ c g x.1 x.2 =
        oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) g x.1 x.2) ∧
      (∀ (μ : ℂ) (y : Space) (τ : ℝ), IIIa.sepW ν μ (oldPhys ε⁻¹ c g) y τ =
        IIIa.sepW ν μ (oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) g) y τ) := by
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have hpull := chartOfNullPullback ε⁻¹ c hR hc _ (ae_iff.1 hchart)
  have hagree : ∀ᵐ x : ℝ × Space ∂volume, oldPhys ε⁻¹ c g x.1 x.2 =
      oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) g x.1 x.2 := by
    filter_upwards [hpull] with x hx
    simp only [Set.mem_setOf_eq, not_not] at hx
    unfold oldCutSrc
    split_ifs with hz
    · rfl
    · have h0r : 0 ≤ ε⁻¹ * Real.sqrt (5 * ν / 6) := by positivity
      have hlt := not_le.1 hz
      have hpos : 0 < NearInst.hRad x.2 := lt_of_le_of_lt h0r hlt
      have hsq : (ε⁻¹ * Real.sqrt (5 * ν / 6)) ^ 2 = ε⁻¹ ^ 2 * (5 * ν / 6) := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
      have hlt2 : (ε⁻¹ * Real.sqrt (5 * ν / 6)) ^ 2 < NearInst.hRad x.2 ^ 2 := by
        nlinarith
      have hs : ν * (NearInst.chartOf ε⁻¹ c x.2 x.1).1 ≤ 6 / 5 := by
        show ν * (ε⁻¹ ^ 2 / NearInst.hRad x.2 ^ 2) ≤ 6 / 5
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith
      have hG0 := hx hs
      simp only [oldPhys, NearInst.cartLift, hG0, rb_nsSym_zero, smul_zero, Matrix.mul_zero,
        Matrix.zero_mul]
  have hP : 2 * ε * c = 2 * c / ε⁻¹ := by rw [div_inv_eq_mul]; ring
  have hper : ∀ τ z, oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) g (τ + 2 * c / ε⁻¹) z =
      oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) g τ z := by
    intro τ z
    unfold oldCutSrc
    rw [oldPhysPeriodic ε⁻¹ c g τ z]
  have hper2 : ∀ τ z, oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) g (τ + 2 * ε * c) z =
      oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) g τ z := by
    intro τ z
    rw [hP]
    exact hper τ z
  have hsupp : ∀ τ z, ε⁻¹ * Real.sqrt (5 * ν / 6) < Real.sqrt (z 0 ^ 2 + z 1 ^ 2) →
      oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) g τ z = 0 := by
    intro τ z hz
    have hz' : ¬ NearInst.hRad z ≤ ε⁻¹ * Real.sqrt (5 * ν / 6) := not_le.2 hz
    unfold oldCutSrc
    simp only [hz', ite_false]
  exact ⟨{ measurable := oldCutMeasurable ε⁻¹ c _ g hgm
           periodic := hper2
           support := hsupp }, hagree,
    fun μ y τ => sepWCongrAE ν μ _ _ hagree y τ⟩

theorem sepThinSrcFiniteAt (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (hC0 : 0 < K.C0) (hmZ : 3 / 2 < K.mZ) (T : LStr Pl K L) (g₁ g₂ : Chart → Ten3)
    (hg : IsRep Pl K L (oldThin Pl K L T) g₁ g₂) :
    ∃ T' : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ, SepRepOf L μ (g₁ + g₂) T' := by
  have hν : 0 < L.ν := L.ν_pos
  have hε : 0 < L.ε := L.ε_pos
  have hR : 0 < L.ε⁻¹ := inv_pos.2 hε
  have hc : 0 < cOf L.ν := cOf_pos hν
  have hρ : 0 < L.ρb Pl K := by
    show 0 < UnforcedLeray.Short.IIb.rhoB (L.params Pl) K.m0 K.C0 K.k0
    unfold UnforcedLeray.Short.IIb.rhoB
    have h1 : 0 < ((L.params Pl).ν ^ K.k0)⁻¹ := inv_pos.2 (pow_pos (L.params Pl).ν_pos _)
    have h2 : 0 < (L.params Pl).ε ^ (3 / 11 : ℝ) := Real.rpow_pos_of_pos (L.params Pl).ε_pos _
    have h3 : 0 < Real.exp (K.m0 / (L.params Pl).ν) := Real.exp_pos _
    exact mul_pos (mul_pos (mul_pos hC0 h1) h3) h2
  set M := thinPart T with hM
  set X := chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo M with hX
  set G : Chart → Ten3 := (X.fst : Chart → Ten3) with hGdef
  have hGm : Measurable G := l9_lp_meas X.fst
  have hMsnd : M.snd = 0 := by simp [hM, thinPart]
  have a1 := (chiOStrApply (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.χo K.hχo M).1
  have a2 := (chiOStrApply (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.χo K.hχo M).2
  -- the second component vanishes
  have hae := wo_rep_ae hρ K.hχo M hg.1 hg.2
  rw [← hX] at a1 a2 hae
  have hsnd0 : ((X.snd : Lp (α := Chart) Ten3 2 _) : Chart → Ten3) =ᵐ[ageμ (cOf L.ν) (-1 / 2)]
      (0 : Chart → Ten3) := by
    have h0 : ((X.snd : Lp (α := Chart) Ten3 2 _) : Chart → Ten3)
        =ᵐ[gainHTMeasure (cOf L.ν) (L.ρb Pl K) (gRate Pl) L.ν] (0 : Chart → Ten3) := by
      filter_upwards [a2, Lp.coeFn_zero Ten3 2
        (gainHTMeasure (cOf L.ν) (L.ρb Pl K) (gRate Pl) L.ν)] with p e e0
      rw [e, hMsnd, e0]
      simp
    rw [NearInst.ae_gainHTMeasure, NearInst.ae_htRhoMeasure hρ] at h0
    exact h0
  have hsum : g₁ + g₂ =ᵐ[ageμ (cOf L.ν) (-1 / 2)] G := by
    filter_upwards [hae, hsnd0] with p h1 h2
    rw [h1]
    simp [strSum, hGdef, h2]
  have hchart : ∀ᵐ p ∂(ageμ (cOf L.ν) (-1 / 2)), (L.ν * p.1 ≤ 6 / 5 → G p = 0) := by
    have a1' := a1
    rw [NearInst.ae_gainZ1Measure, NearInst.ae_z1Measure] at a1'
    filter_upwards [a1'] with p e
    intro hp
    have h0 : cutFun K.χo L.ν p = 0 := K.hχo.zero _ hp
    simp only [hGdef, e, Pi.smul_apply', h0, zero_smul]
  -- the finite `Z_1` moment of `G`
  have hJ : ∫⁻ p, ‖G p‖ₑ ^ 2 ∂(z1Measure (cOf L.ν) K.mZ) < ⊤ := by
    have hmeas : Measurable fun p : Chart => ‖G p‖ₑ ^ 2 := hGm.enorm.pow_const 2
    refine l9_lt_top_of_ofReal_mul (Real.exp_pos (-(2 * |gRate Pl| / L.ν))) ?_
    exact lt_of_le_of_lt (z1_le_gain _ _ _ _ hν _ hmeas) (l9_lp_lint X.fst)
  obtain ⟨hsep, hagree, hresp⟩ := thinCutFacts (cOf L.ν) L.ν L.ε hc hν hε G hGm hchart
  -- the separated representative and the Ward identity
  have hnull := ae_iff.1 hsum
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null hnull
  have hsepw : ∀ (μ' : ℂ) (τ : ℝ) (y : Space),
      UnforcedLeray.Short.IIIa.sepW L.ν μ' (oldPhys L.ε⁻¹ (cOf L.ν) (g₁ + g₂)) y τ =
        UnforcedLeray.Short.IIIa.sepW L.ν μ'
          (oldCutSrc L.ε⁻¹ (cOf L.ν) (L.ε⁻¹ * Real.sqrt (5 * L.ν / 6)) G) y τ := by
    intro μ' τ y
    rw [WardX0Congr.sepW_congr L.ν μ' hR hc (g₁ + g₂) _ N hNm hN0 hsub τ y]
    exact hresp μ' y τ
  have hpull := chartOfNullPullback L.ε⁻¹ (cOf L.ν) hR hc _ hnull
  have hphys : ∀ᵐ x : ℝ × Space, oldPhys L.ε⁻¹ (cOf L.ν) (g₁ + g₂) x.1 x.2 =
      oldPhys L.ε⁻¹ (cOf L.ν) G x.1 x.2 := by
    filter_upwards [hpull] with x hx
    have hx' : (g₁ + g₂) (NearInst.chartOf L.ε⁻¹ (cOf L.ν) x.2 x.1) =
        G (NearInst.chartOf L.ε⁻¹ (cOf L.ν) x.2 x.1) := not_not.1 hx
    simp only [oldPhys, NearInst.cartLift, hx']
  refine ⟨oldCutSrc L.ε⁻¹ (cOf L.ν) (L.ε⁻¹ * Real.sqrt (5 * L.ν / 6)) G, hsep, ?_,
    fun τ y => ?_, ?_⟩
  · filter_upwards [hagree, hphys] with x h1 h2
    rw [← h1, h2]
  · simp only [wardW, sepWre, hsepw]
  · have hP : 2 * L.ε * cOf L.ν = 2 * cOf L.ν / L.ε⁻¹ := by rw [div_inv_eq_mul]; ring
    rw [hP]
    have hr : 0 < L.ε⁻¹ * Real.sqrt (5 * L.ν / 6) :=
      mul_pos hR (Real.sqrt_pos.2 (by positivity))
    exact ThinFin.thinCore hR hc hr (by linarith) G hGm hJ


/-- **A finite separated representative of an old thin source** (source 3596-3626, 4155-4171,
5573-5584). -/
theorem sepThinSrcFinite (dm dp : ℝ) : SepThinSrcFinite dm dp := by
  intro D hst
  refine Filter.Eventually.of_forall fun n z _ T g₁ g₂ hg => ?_
  exact sepThinSrcFiniteAt D.Pl D.K (D.level n) (D.mu n z) hst.C0_pos hst.mZ_gt T g₁ g₂ hg

end UnforcedLeray.Short.PartIIIb.Concrete
