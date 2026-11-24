import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_7_6_1.L2.Jets
import UnforcedLeray.Short.PartIIb.Tasks.DriftNvC.Smooth.SmoothPt.NicePhaseTest

/-!
# Locality of the ring lift

Source `the November 2 reference manuscript`
lines 2385-2387 (the profile vanishes for `s ≥ T`): `Nv R b τ = 0` near the axis and on `{age > T}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray

theorem nv_eventually_zero {R T : ℝ} (hR : 0 < R) {b : ℝ × (ℝ × ℝ) → Axi.Merid}
    (hb : ∀ m : ℝ × (ℝ × ℝ), T ≤ m.1 → b m = 0) {y : Space}
    (hy : y ∈ Axi.axis ∨ T < Axi.age R y) :
    ∀ᶠ y' in 𝓝 y, ∀ τ : ℝ, Axi.Nv R b τ y' = 0 := by
  set S : ℝ := |T| + 1 with hS
  have hSpos : 0 < S := by positivity
  set δ : ℝ := R / √S with hδ
  have hδpos : 0 < δ := div_pos hR (Real.sqrt_pos.2 hSpos)
  have hzero : ∀ y' : Space, Axi.ϱ y' < δ → ∀ τ, Axi.Nv R b τ y' = 0 := by
    intro y' hq τ
    by_cases h0 : Axi.ϱ y' = 0
    · have : Axi.age R y' = 0 := by simp [Axi.age, h0]
      simp [Axi.Nv, this]
    · have hpos : 0 < Axi.ϱ y' := lt_of_le_of_ne (Axi.ϱ_nonneg _) (Ne.symm h0)
      have hsq : Axi.ϱ y' * √S < R := (lt_div_iff₀ (Real.sqrt_pos.2 hSpos)).1 hq
      have hS' : S < Axi.age R y' := by
        unfold Axi.age
        rw [lt_div_iff₀ (by positivity)]
        have h2 : (Axi.ϱ y' * √S) ^ 2 < R ^ 2 := pow_lt_pow_left₀ hsq (by positivity) (by norm_num)
        have : (Axi.ϱ y' * √S) ^ 2 = Axi.ϱ y' ^ 2 * S := by rw [mul_pow, Real.sq_sqrt hSpos.le]
        nlinarith
      have hs1 : T ≤ (Axi.chart R τ y').1 := by
        show T ≤ Axi.age R y'
        have : T ≤ |T| := le_abs_self _
        linarith
      simp [Axi.Nv, hb _ hs1]
  have hzero2 : ∀ y' : Space, y' ∉ Axi.axis → T < Axi.age R y' → ∀ τ, Axi.Nv R b τ y' = 0 := by
    intro y' _ hT τ
    have hs1 : T ≤ (Axi.chart R τ y').1 := hT.le
    simp [Axi.Nv, hb _ hs1]
  by_cases hax : y ∈ Axi.axis
  · have hopen : IsOpen {y' : Space | Axi.ϱ y' < δ} :=
      isOpen_lt Axi.continuous_ϱ continuous_const
    have hmem : y ∈ {y' : Space | Axi.ϱ y' < δ} := by
      show Axi.ϱ y < δ
      rw [(Axi.mem_axis_iff y).1 hax]; exact hδpos
    filter_upwards [hopen.mem_nhds hmem] with y' hq using hzero y' hq
  · have hT : T < Axi.age R y := hy.resolve_left hax
    have hopen : IsOpen (Axi.axisᶜ ∩ Axi.age R ⁻¹' Ioi T) :=
      (IIb.ChartJetsAux.contDiffOn_age R).continuousOn.isOpen_inter_preimage
        Axi.isOpen_compl_axis isOpen_Ioi
    filter_upwards [hopen.mem_nhds ⟨hax, hT⟩] with y' hq using hzero2 y' hq.1 hq.2

end UnforcedLeray.Short.PartIIIb.Concrete
