import UnforcedLeray.Short.PartIIb.Sub.T07

/-!
# Part II-b, task `PartII-b:T07/8`: the ring chart pulls a periodic null set back to a null set

Source of record: `the November 2 reference manuscript`, lines 1902-1906
(the complex lift norm identity); the target is the Prop `ChartNullPullback` of
`Short/PartII-b/Sub/T07.lean`.

Proof sketch: `G := 1_M` is measurable and `c`-periodic in `q`. The phase-average identity
`Axi.phaseAvg_ringChart` gives `(ofReal P)⁻¹ ∫⁻_{(0,P]} ∫⁻_y G(chart R τ y) = ofReal (π R²) * J`,
where `J` integrates `G` against the measure `ageμ`-weighted cell; `J = 0` because `M` is
Lebesgue-null. Hence the iterated integral vanishes, so for a.e. `τ` the inner integral vanishes,
and then for a.e. `y` the integrand `G(chart R τ y)` vanishes, i.e. `chart R τ y ∉ M`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

/-- **`PartII-b:T07/8`**: the ring chart pulls a `c`-periodic Lebesgue-null measurable set back
to a null set of `(τ, y)`: for a.e. `τ ∈ (0, P]` and a.e. `y`, `chart R τ y ∉ M`. -/
theorem chartNullPullback : UnforcedLeray.Short.IIb.ChartNullPullback := by
  intro R c P hR hc hP M hM hM0 hMper
  -- the indicator `G = 1_M`, measurable and `c`-periodic in `q`
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ × (ℝ × ℝ) → ℝ≥0∞, G = M.indicator (fun _ => (1 : ℝ≥0∞)) :=
    ⟨_, rfl⟩
  have hG : Measurable G := by
    rw [hGdef]
    exact measurable_const.indicator hM
  have hGper : ∀ s q η, G (s, (q + c, η)) = G (s, (q, η)) := by
    intro s q η
    have hiff := hMper s q η
    rw [hGdef]
    by_cases h : (s, (q, η)) ∈ M
    · have h' : (s, (q + c, η)) ∈ M := hiff.2 h
      rw [Set.indicator_of_mem h, Set.indicator_of_mem h']
    · have h' : (s, (q + c, η)) ∉ M := fun h'' => h (hiff.1 h'')
      rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']
  -- the phase average of `G` over `(0, P]` equals `πR²` times a `ageμ`-type integral of `G`
  have hphase := Axi.phaseAvg_ringChart hR hc hP G hG hGper
  -- that integral vanishes: `G = 0` almost everywhere on the cell, since `M` is null
  have hJ : ∫⁻ p in Ioi (0 : ℝ) ×ˢ Axi.qCell c,
      ENNReal.ofReal (c⁻¹ * p.1 ^ (-(5 / 2 : ℝ))) * G p = 0 := by
    rw [lintegral_congr_ae (g := fun _ => 0)]
    · simp
    · filter_upwards [ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hM0)] with p hp
      simp [hGdef, Set.indicator_of_notMem hp]
  rw [hJ, mul_zero] at hphase
  -- so the iterated integral over `(0, P]` vanishes
  have hI : ∫⁻ τ in Ioc (0 : ℝ) P, ∫⁻ y : Space, G (Axi.chart R τ y) = 0 := by
    rcases mul_eq_zero.1 hphase with h | h
    · exact absurd h (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top)
    · exact h
  -- measurability of the integrand `(τ, y) ↦ G(chart R τ y)`
  have hFm : Measurable fun x : ℝ × Space => G (Axi.chart R x.1 x.2) :=
    hG.comp (((Axi.measurable_age R).comp measurable_snd).prodMk
      ((Axi.measurable_phase R).prodMk ((Axi.measurable_trans R).comp measurable_snd)))
  have hτm : Measurable fun τ : ℝ => ∫⁻ y : Space, G (Axi.chart R τ y) :=
    hFm.lintegral_prod_right'
  -- for a.e. `τ`, the inner integral vanishes
  have hτ0 : ∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) P)), ∫⁻ y : Space, G (Axi.chart R τ y) = 0 :=
    (lintegral_eq_zero_iff' hτm.aemeasurable).1 hI
  filter_upwards [hτ0] with τ hτ
  -- then, for a.e. `y`, `G(chart R τ y) = 0`
  have hτy : Measurable fun y : Space => ((τ, y) : ℝ × Space) :=
    measurable_prodMk_left (x := τ)
  have hFτ : Measurable ((fun x : ℝ × Space => G (Axi.chart R x.1 x.2)) ∘
      (fun y : Space => ((τ, y) : ℝ × Space))) := hFm.comp hτy
  have hy0 := (lintegral_eq_zero_iff' hFτ.aemeasurable).1 hτ
  filter_upwards [hy0] with y hy
  have hy' : G (Axi.chart R τ y) = 0 := hy
  intro hmem
  rw [hGdef, Set.indicator_of_mem hmem] at hy'
  exact one_ne_zero hy'

end UnforcedLeray.Short.IIb
