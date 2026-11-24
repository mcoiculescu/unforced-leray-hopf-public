import UnforcedLeray.Short.PartIIb.Tasks.NvCNorm

/-!
# `PartII-b:T08/3` helpers: null-set congruences for `hNorm` and `pairF ∘ NvC`
(SP 1902-1906).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal
open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

theorem hNorm_congr_of_null {c r : ℝ} (hc : 0 < c) (b b' : CProf) (M : Set Coord)
    (hM : MeasurableSet M) (hM0 : volume M = 0)
    (hbb' : ∀ x : Coord, 0 < x.1 → x ∉ M → b x = b' x) : hNorm c r b = hNorm c r b' := by
  unfold hNorm
  refine eLpNorm_congr_ae ?_
  have hn : Axi.ageμ c (r / 2 - 5 / 2) M = 0 := ageμ_null_of_volume_null hc hM hM0
  filter_upwards [Axi.ae_ageμ_mem hc (r / 2 - 5 / 2),
    measure_eq_zero_iff_ae_notMem.1 hn] with p hp hpM
  exact hbb' p hp.1 hpM

theorem pairF_NvC_congr (R P : ℝ) (hR : 0 < R) (Φ : ℝ × Space → CVec3) (b b' : CProf)
    (M : Set Coord) (hbb' : ∀ x : Coord, 0 < x.1 → x ∉ M → b x = b' x)
    (hNull : ∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) P)), ∀ᵐ y : Space, Axi.chart R τ y ∉ M) :
    pairF P Φ (NvC R b) = pairF P Φ (NvC R b') := by
  unfold pairF phaseInt
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hNull] with τ hτ
  refine integral_congr_ae ?_
  filter_upwards [hτ, Axi.ae_not_mem_axis] with y hy hax
  have hpos : 0 < (Axi.chart R τ y).1 := Axi.age_pos hR.ne' hax
  have key : b (Axi.chart R τ y) = b' (Axi.chart R τ y) := hbb' _ hpos hy
  simp only [NvC, Axi.Nv, key]

end UnforcedLeray.Short.IIb
