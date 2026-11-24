import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_10_2.H4

/-!
# Helpers for `wardStreamCorrYoungL2_proved` (5): Tonelli for the radial integral of `sepDom`

Source of record: `the November 2 reference manuscript` (73 pages), 3687-3697.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem w2_measurable_pt (z0 : ℝ) : Measurable (fun ρ : ℝ => (!₂[ρ, 0, z0] : Space)) := by
  have : Measurable (fun ρ : ℝ => (![ρ, 0, z0] : Fin 3 → ℝ)) := by
    refine measurable_pi_lambda _ fun i => ?_
    fin_cases i <;> simp <;> fun_prop
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp this

/-- Tonelli: the radial integral of the dilation integral with the order-four kernel is bounded by
the dilation integral with the cylinder majorant. -/
theorem w2_tonelli {r0 D r2 : ℝ} (hr0 : 0 ≤ r0) (hD : 0 < D) (a : ℝ)
    {g : ℝ → Space → ℝ≥0∞} (hgm : Measurable (Function.uncurry g))
    (hsupp : ∀ τ z, r0 < ϱ z → g τ z = 0) (τ : ℝ) {y : Space} (hy : ϱ y ≤ r2) {r : ℝ}
    (hr : r0 + D ≤ r) :
    ∫⁻ ρ in Ioi r, ENNReal.ofReal ρ * w2Dom (IIIa.sepKd 0 D) a g τ (!₂[ρ, 0, y 2] : Space) ≤
      w2Dom (w2k r0 D (r2 + r0)) a g τ y := by
  set H : ℝ → ℝ → Space → ℝ≥0∞ := fun ρ l z => ENNReal.ofReal ρ * (ENNReal.ofReal (l ^ a) *
      (IIIa.sepKd 0 D ((!₂[ρ, 0, y 2] : Space) - l • z) * g (τ + 2 * Real.log l) z)) with hH
  have hHm : Measurable (fun p : (ℝ × ℝ) × Space => H p.1.1 p.1.2 p.2) := by
    have e1 : Measurable (fun p : (ℝ × ℝ) × Space => ENNReal.ofReal p.1.1) :=
      ENNReal.measurable_ofReal.comp (measurable_fst.comp measurable_fst)
    have e2 : Measurable (fun p : (ℝ × ℝ) × Space => ENNReal.ofReal (p.1.2 ^ a)) :=
      ENNReal.measurable_ofReal.comp ((measurable_snd.comp measurable_fst).pow_const a)
    have e3 : Measurable (fun p : (ℝ × ℝ) × Space =>
        IIIa.sepKd 0 D ((!₂[p.1.1, 0, y 2] : Space) - p.1.2 • p.2)) := by
      refine (IIIa.measurable_sepKd 0 D).comp ?_
      exact ((w2_measurable_pt (y 2)).comp (measurable_fst.comp measurable_fst)).sub
        ((measurable_snd.comp measurable_fst).smul measurable_snd)
    have e4 : Measurable (fun p : (ℝ × ℝ) × Space => g (τ + 2 * Real.log p.1.2) p.2) := by
      have : Measurable (fun p : (ℝ × ℝ) × Space => (τ + 2 * Real.log p.1.2, p.2)) :=
        (measurable_const.add (measurable_const.mul
          (Real.measurable_log.comp (measurable_snd.comp measurable_fst)))).prodMk measurable_snd
      exact hgm.comp this
    exact e1.mul (e2.mul (e3.mul e4))
  -- step 1: rewrite as iterated integrals
  have h1 : ∀ ρ, ENNReal.ofReal ρ * w2Dom (IIIa.sepKd 0 D) a g τ (!₂[ρ, 0, y 2] : Space) =
      ∫⁻ l in Ioo (0 : ℝ) 1, ∫⁻ z : Space, H ρ l z := by
    intro ρ
    unfold w2Dom
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun l => ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  simp_rw [h1]
  have hinner : Measurable (fun p : ℝ × ℝ => ∫⁻ z : Space, H p.1 p.2 z) :=
    Measurable.lintegral_prod_right (f := fun (p : ℝ × ℝ) (z : Space) => H p.1 p.2 z) hHm
  rw [lintegral_lintegral_swap (hinner.aemeasurable)]
  unfold w2Dom
  refine setLIntegral_mono' measurableSet_Ioo fun l hl => ?_
  have hl0 : 0 < l := hl.1
  -- swap ρ and z for fixed l
  have hHm2 : Measurable (fun p : ℝ × Space => H p.1 l p.2) :=
    hHm.comp (measurable_fst.prodMk measurable_const |>.prodMk measurable_snd)
  rw [lintegral_lintegral_swap hHm2.aemeasurable]
  have hgl : Measurable (g (τ + 2 * Real.log l)) :=
    hgm.comp (measurable_const.prodMk measurable_id)
  calc ∫⁻ z : Space, ∫⁻ ρ in Ioi r, H ρ l z
      ≤ ∫⁻ z : Space, ENNReal.ofReal (l ^ a) *
          (w2k r0 D (r2 + r0) (y - l • z) * g (τ + 2 * Real.log l) z) := by
        refine lintegral_mono fun z => ?_
        by_cases hz : r0 < ϱ z
        · have : g (τ + 2 * Real.log l) z = 0 := hsupp _ _ hz
          simp only [hH, this, mul_zero, lintegral_zero, zero_le]
        · have hz' : ϱ z ≤ r0 := not_lt.1 hz
          have hk := w2_radial_kernel hr0 hD hl0 hl.2 hy hz' hr
          have hmeasρ : Measurable (fun ρ : ℝ => ENNReal.ofReal ρ *
              IIIa.sepKd 0 D ((!₂[ρ, 0, y 2] : Space) - l • z)) :=
            ENNReal.measurable_ofReal.mul ((IIIa.measurable_sepKd 0 D).comp
              ((w2_measurable_pt (y 2)).sub_const _))
          calc ∫⁻ ρ in Ioi r, H ρ l z
              = ∫⁻ ρ in Ioi r, (ENNReal.ofReal (l ^ a) * g (τ + 2 * Real.log l) z) *
                  (ENNReal.ofReal ρ * IIIa.sepKd 0 D ((!₂[ρ, 0, y 2] : Space) - l • z)) :=
                lintegral_congr fun ρ => by simp only [hH]; ring
            _ = (ENNReal.ofReal (l ^ a) * g (τ + 2 * Real.log l) z) *
                  ∫⁻ ρ in Ioi r, ENNReal.ofReal ρ *
                    IIIa.sepKd 0 D ((!₂[ρ, 0, y 2] : Space) - l • z) :=
                lintegral_const_mul _ hmeasρ
            _ ≤ (ENNReal.ofReal (l ^ a) * g (τ + 2 * Real.log l) z) *
                  w2k r0 D (r2 + r0) (y - l • z) := by gcongr
            _ = ENNReal.ofReal (l ^ a) * (w2k r0 D (r2 + r0) (y - l • z) *
                  g (τ + 2 * Real.log l) z) := by ring
    _ = _ := by
        rw [lintegral_const_mul']
        exact ENNReal.ofReal_ne_top

end UnforcedLeray.Short.PartIIIb.Concrete
end
