import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_org
import UnforcedLeray.Units.B0224.Semigroup
import UnforcedLeray.Units.B0224.FiberHeat

/-!
# Helpers for `SFCDuhamelLift`: congruence and periodicity of `causalHeat`
(decomposition of `PartIII-b:C/flatset/col/7/1/1/2/4/2/1/2`)

* `planeι_measurePreserving` : the `(q, η)`-embedding carries Lebesgue measure to Lebesgue measure.
* `planeHeat_congr_pt` : for `θ > 0`, the heat of `u` at a point depends only on the a.e.-class of `u`.
* `causalHeat_congr_of_slices` : `causalHeat` depends only on the `σ`-slices of `periodize`, a.e.
* `causalHeat_cellPt` : `causalHeat` is invariant under the recentring `cellPt c`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open UnforcedLeray.Gaussian (Euc)

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem planeι_measurePreserving :
    MeasurePreserving (UnforcedLeray.B0224.planeι : Euc 2 → ℝ × ℝ) volume volume := by
  have h1 := (PiLp.volume_preserving_ofLp (Fin 2))
  have h2 := (MeasureTheory.volume_preserving_finTwoArrow ℝ)
  exact h2.comp h1

theorem planeHeat_congr_pt {θ : ℝ} (hθ : 0 < θ) {u v : ℝ × ℝ → UnforcedLeray.B0223.MeridC}
    (huv : u =ᵐ[volume] v) (x : ℝ × ℝ) :
    UnforcedLeray.B0224.planeHeat θ u x = UnforcedLeray.B0224.planeHeat θ v x := by
  rw [UnforcedLeray.B0224.planeHeat_of_pos hθ, UnforcedLeray.B0224.planeHeat_of_pos hθ]
  refine integral_congr_ae ?_
  have hm : MeasurePreserving (fun y : Euc 2 => x - UnforcedLeray.B0224.planeι y) volume volume :=
    (Measure.measurePreserving_sub_left volume x).comp planeι_measurePreserving
  filter_upwards [hm.quasiMeasurePreserving.ae huv] with y hy
  simp only [hy]

theorem causalHeat_congr_of_slices {c ν : ℝ} (μ : ℂ) (hν : 0 < ν)
    {F H : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC}
    (hS : ∀ᵐ σ : ℝ, 0 < σ → ∀ᵐ z : ℝ × ℝ,
      UnforcedLeray.B0220.periodize c F (σ, z) = UnforcedLeray.B0220.periodize c H (σ, z))
    (p : UnforcedLeray.B0220.Profile) (hp : 0 < p.1) :
    UnforcedLeray.B0225.causalHeat c ν μ F p = UnforcedLeray.B0225.causalHeat c ν μ H p := by
  unfold UnforcedLeray.B0225.causalHeat
  have hne : ∀ᵐ σ : ℝ, σ ≠ p.1 := (Set.countable_singleton p.1).ae_notMem volume
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hS, hne] with σ hσ hne' hmem
  rw [Set.uIoc_of_le hp.le] at hmem
  have hlt : σ < p.1 := lt_of_le_of_ne hmem.2 hne'
  have hθ : 0 < ν * (p.1 - σ) := mul_pos hν (sub_pos.2 hlt)
  have hu : (fun z => UnforcedLeray.B0220.periodize c F (σ, z)) =ᵐ[volume]
      (fun z => UnforcedLeray.B0220.periodize c H (σ, z)) := by
    filter_upwards [hσ hmem.1] with z hz
    exact hz
  rw [planeHeat_congr_pt hθ hu p.2]

theorem causalHeat_cellPt {c : ℝ} (hc : 0 < c) (ν : ℝ) (μ : ℂ)
    (F : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
    (p : UnforcedLeray.B0220.Profile) :
    UnforcedLeray.B0225.causalHeat c ν μ F (NearInst.cellPt c p) =
      UnforcedLeray.B0225.causalHeat c ν μ F p := by
  unfold UnforcedLeray.B0225.causalHeat
  refine intervalIntegral.integral_congr (fun σ _ => ?_)
  show ((σ / p.1 : ℝ) : ℂ) ^ μ • UnforcedLeray.B0224.planeHeat (ν * (p.1 - σ))
      (fun z => UnforcedLeray.B0220.periodize c F (σ, z)) (NearInst.cellPt c p).2 =
    ((σ / p.1 : ℝ) : ℂ) ^ μ • UnforcedLeray.B0224.planeHeat (ν * (p.1 - σ))
      (fun z => UnforcedLeray.B0220.periodize c F (σ, z)) p.2
  congr 1
  have hper := UnforcedLeray.B0224.isPeriodic_planeHeat (c := c) (θ := ν * (p.1 - σ))
    (UnforcedLeray.B0224.isPeriodic_periodize_slice hc F σ)
  by_cases h : p.2.1 < c / 2
  · have e : (NearInst.cellPt c p).2 = p.2 := by
      simp [NearInst.cellPt, h]
    rw [e]
  · have e : (NearInst.cellPt c p).2 = (p.2.1 - c, p.2.2) := by
      simp [NearInst.cellPt, h]
    rw [e]
    have := hper (p.2.1 - c, p.2.2)
    simp only [sub_add_cancel] at this
    exact this.symm

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
