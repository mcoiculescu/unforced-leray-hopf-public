import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_3_1_2_2

/-!
# `AeLimitH` (source 1650-1656, 1684-1689): a.e. identification of the pointwise limit

Route as in `TrainB.exists_scalarH2_bcf_representative` (`Lib/TrainB/WeakEmbedding.lean:599`):
the `W.value` of the smooth approximants converges in `L²`, so a subsequence converges a.e.;
comparing with the pointwise limit `z` gives `z = value y` a.e. on the cell.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Cyl (Vec2 Plane)

theorem aeLimitH_proof : AeLimitH := by
  intro c hc k y u hu z hz hlim
  let V := UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
    (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec2 k 2
  let μ := UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
    (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))
  have hmeasEq : μ = UnforcedLeray.Cyl.cellμ c := by
    show UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) = UnforcedLeray.Cyl.cellμ c
    rw [UnforcedLeray.Cyl.wμ_ρwW]
    simp [UnforcedLeray.Cyl.wμ]
  have hLp : Tendsto (fun n => V (UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := Vec2)
      (k := k) (p := 2) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc (u n) (hu n)))
      atTop (𝓝 (V y)) :=
    (V.continuous.tendsto y).comp hlim
  have hmeasure := MeasureTheory.tendstoInMeasure_of_tendsto_Lp hLp
  obtain ⟨ns, hns, hconv⟩ := hmeasure.exists_seq_tendsto_ae
  have hrep : ∀ n, (V (UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := Vec2) (k := k) (p := 2)
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc (u n) (hu n)) : Plane → Vec2) =ᵐ[μ] u n :=
    fun n => UnforcedLeray.Sob.W.value_ofCylSmooth (c := c)
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Vec2) (k := k) (p := 2)
      hc (u n) (hu n)
  have hall : ∀ᵐ x ∂μ, ∀ i, (V (UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := Vec2)
      (k := k) (p := 2) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc (u (ns i)) (hu (ns i))) :
      Plane → Vec2) x = u (ns i) x := by
    rw [ae_all_iff]
    exact fun i => hrep (ns i)
  rw [← hmeasEq]
  filter_upwards [hconv, hall] with x hx hx2
  have hz' : Tendsto (fun i => u (ns i) x) atTop (𝓝 (z x)) := (hz x).comp hns.tendsto_atTop
  have heq : (fun i => u (ns i) x) = fun i => (V (UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ)
      (F := Vec2) (k := k) (p := 2) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc (u (ns i))
      (hu (ns i))) : Plane → Vec2) x := funext fun i => (hx2 i).symm
  have hV : Tendsto (fun i => u (ns i) x) atTop (𝓝 ((V y : Plane → Vec2) x)) := by
    rw [heq]
    exact hx
  exact tendsto_nhds_unique hz' hV

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
