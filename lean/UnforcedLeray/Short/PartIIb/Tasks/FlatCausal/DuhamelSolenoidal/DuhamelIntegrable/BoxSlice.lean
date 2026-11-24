import UnforcedLeray.Short.PartIIb.Sub.T12_6_2
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelSolenoidal.DuhamelIntegrable.PeriodicBoxBound
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelSolenoidal.DuhamelIntegrable.FlatHeatAEMeas
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelSolenoidal.DuhamelIntegrable.BoxSliceS
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.SliceAe

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

/-- Pointwise-in-`t` box bound for one good slice `g = G(t, ·)`. The `z`-integral is bounded by
`FlatHeatBoxBound` (constant `C0`), the `s`-integral by `BoxSliceS` (constant `K`), and the
integrand vanishes unless `t < s`. Tonelli is replaced by `lintegral_prod_le`, which needs no
measurability. -/
theorem boxSlice_pt (ν c r R σ H : ℝ) (μ : ℂ) (G : CProf) (t : ℝ)
    (hν : 0 < ν) (ht : 0 < t) (C0 K : ℝ)
    (hC : ∀ (θ : ℝ) (g : ℝ × ℝ → CMerid), 0 < θ → (∀ᵐ z : ℝ × ℝ, g (z.1 + c, z.2) = g z) →
      AEStronglyMeasurable g volume →
      ∫⁻ z in Icc (-R) R ×ˢ Icc (-R) R, ‖flatHeat θ g z‖ₑ ≤
        ENNReal.ofReal C0 * eLpNorm g (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c))
    (hg : DeqSliceGood c r (fun z => G (t, z)))
    (hS : t < H → ∫⁻ s in Icc σ H ∩ Ioi t, ENNReal.ofReal ((t / s) ^ μ.re) ≤
      ENNReal.ofReal (K * t ^ μ.re)) :
    ∫⁻ x in Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-R) R), ENNReal.ofReal (boxIntegrand ν μ G t x) ≤
      ENNReal.ofReal (max C0 0 * max K 0) *
        Set.indicator (Ioo (0 : ℝ) H)
          (fun t : ℝ => ENNReal.ofReal (t ^ (μ.re - 1)) *
            eLpNorm (fun z : ℝ × ℝ => G (t, z)) (ENNReal.ofReal r)
              (UnforcedLeray.Cyl.avgμ c)) t := by
  have hN : eLpNorm (fun z : ℝ × ℝ => G (t, z)) (ENNReal.ofReal r)
      (UnforcedLeray.Cyl.avgμ c) < ⊤ := hg.2.2
  have hD : ENNReal.ofReal (t⁻¹) * ENNReal.ofReal (max C0 0) *
      eLpNorm (fun z : ℝ × ℝ => G (t, z)) (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hN.ne
  -- pointwise bound on each `s`-slice
  have hin : ∀ s ∈ Icc σ H,
      ∫⁻ z in Icc (-R) R ×ˢ Icc (-R) R, ENNReal.ofReal (boxIntegrand ν μ G t (s, z)) ≤
        (Ioi t).indicator (fun s : ℝ => ENNReal.ofReal ((t / s) ^ μ.re) *
          (ENNReal.ofReal (t⁻¹) * ENNReal.ofReal (max C0 0) *
            eLpNorm (fun z : ℝ × ℝ => G (t, z)) (ENNReal.ofReal r)
              (UnforcedLeray.Cyl.avgμ c))) s := by
    intro s _hs
    by_cases hts : t < s
    · have hsp : 0 < s := ht.trans hts
      have hθ : 0 < ν * (s - t) := mul_pos hν (sub_pos.2 hts)
      have hp0 : 0 ≤ (t / s) ^ μ.re * t⁻¹ :=
        mul_nonneg (Real.rpow_nonneg (div_pos ht hsp).le _) (inv_nonneg.2 ht.le)
      have hval : ∀ z : ℝ × ℝ, ENNReal.ofReal (boxIntegrand ν μ G t (s, z)) =
          ENNReal.ofReal ((t / s) ^ μ.re * t⁻¹) *
            ‖flatHeat (ν * (s - t)) (fun w => G (t, w)) z‖ₑ := by
        intro z
        dsimp only [boxIntegrand]
        rw [if_pos (show 0 < t ∧ t < s from ⟨ht, hts⟩),
          Complex.norm_cpow_eq_rpow_re_of_pos (div_pos ht hsp) μ, ← ofReal_norm,
          ← ENNReal.ofReal_mul hp0]
      have hint : ∫⁻ z in Icc (-R) R ×ˢ Icc (-R) R, ENNReal.ofReal (boxIntegrand ν μ G t (s, z)) ≤
          ENNReal.ofReal ((t / s) ^ μ.re) *
            (ENNReal.ofReal (t⁻¹) * ENNReal.ofReal (max C0 0) *
              eLpNorm (fun z : ℝ × ℝ => G (t, z)) (ENNReal.ofReal r)
                (UnforcedLeray.Cyl.avgμ c)) := by
        calc ∫⁻ z in Icc (-R) R ×ˢ Icc (-R) R, ENNReal.ofReal (boxIntegrand ν μ G t (s, z))
            = ∫⁻ z in Icc (-R) R ×ˢ Icc (-R) R,
                ENNReal.ofReal ((t / s) ^ μ.re * t⁻¹) *
                  ‖flatHeat (ν * (s - t)) (fun w => G (t, w)) z‖ₑ :=
              lintegral_congr (fun z => hval z)
          _ = ENNReal.ofReal ((t / s) ^ μ.re * t⁻¹) *
                ∫⁻ z in Icc (-R) R ×ˢ Icc (-R) R, ‖flatHeat (ν * (s - t)) (fun w => G (t, w)) z‖ₑ :=
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
          _ ≤ ENNReal.ofReal ((t / s) ^ μ.re * t⁻¹) *
                (ENNReal.ofReal C0 *
                  eLpNorm (fun z : ℝ × ℝ => G (t, z)) (ENNReal.ofReal r)
                    (UnforcedLeray.Cyl.avgμ c)) :=
              by gcongr; exact hC _ _ hθ hg.1 hg.2.1
          _ ≤ ENNReal.ofReal ((t / s) ^ μ.re * t⁻¹) *
                (ENNReal.ofReal (max C0 0) *
                  eLpNorm (fun z : ℝ × ℝ => G (t, z)) (ENNReal.ofReal r)
                    (UnforcedLeray.Cyl.avgμ c)) :=
              by gcongr; exact le_max_left C0 0
          _ = ENNReal.ofReal ((t / s) ^ μ.re) *
                (ENNReal.ofReal (t⁻¹) * ENNReal.ofReal (max C0 0) *
                  eLpNorm (fun z : ℝ × ℝ => G (t, z)) (ENNReal.ofReal r)
                    (UnforcedLeray.Cyl.avgμ c)) := by
              rw [ENNReal.ofReal_mul (Real.rpow_nonneg (div_pos ht hsp).le _)]
              ring
      rw [Set.indicator_of_mem (show s ∈ Ioi t from hts)]
      exact hint
    · have h0 : ∀ z : ℝ × ℝ, ENNReal.ofReal (boxIntegrand ν μ G t (s, z)) = 0 := by
        intro z
        dsimp only [boxIntegrand]
        rw [if_neg (show ¬(0 < t ∧ t < s) from fun h => hts h.2)]
        simp
      exact le_trans (le_of_eq ((lintegral_congr h0).trans lintegral_zero)) zero_le
  -- Tonelli-type inequality (no measurability needed)
  have hvol : (volume : Measure (ℝ × (ℝ × ℝ))).restrict
      (Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-R) R)) =
      (volume.restrict (Icc σ H)).prod (volume.restrict (Icc (-R) R ×ˢ Icc (-R) R)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  have hchain : ∫⁻ x in Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-R) R), ENNReal.ofReal (boxIntegrand ν μ G t x)
      ≤ ∫⁻ s in Icc σ H, (Ioi t).indicator (fun s : ℝ => ENNReal.ofReal ((t / s) ^ μ.re) *
          (ENNReal.ofReal (t⁻¹) * ENNReal.ofReal (max C0 0) *
            eLpNorm (fun z : ℝ × ℝ => G (t, z)) (ENNReal.ofReal r)
              (UnforcedLeray.Cyl.avgμ c))) s := by
    rw [hvol]
    calc ∫⁻ x, ENNReal.ofReal (boxIntegrand ν μ G t x)
          ∂((volume.restrict (Icc σ H)).prod (volume.restrict (Icc (-R) R ×ˢ Icc (-R) R)))
        ≤ ∫⁻ s in Icc σ H, ∫⁻ z in Icc (-R) R ×ˢ Icc (-R) R,
            ENNReal.ofReal (boxIntegrand ν μ G t (s, z)) := lintegral_prod_le _
      _ ≤ _ := setLIntegral_mono' measurableSet_Icc (fun s hs => hin s hs)
  -- the `s`-integral
  have hRHS : ∫⁻ s in Icc σ H, (Ioi t).indicator (fun s : ℝ => ENNReal.ofReal ((t / s) ^ μ.re) *
          (ENNReal.ofReal (t⁻¹) * ENNReal.ofReal (max C0 0) *
            eLpNorm (fun z : ℝ × ℝ => G (t, z)) (ENNReal.ofReal r)
              (UnforcedLeray.Cyl.avgμ c))) s ≤
      ENNReal.ofReal (max K 0 * t ^ μ.re) *
        (ENNReal.ofReal (t⁻¹) * ENNReal.ofReal (max C0 0) *
          eLpNorm (fun z : ℝ × ℝ => G (t, z)) (ENNReal.ofReal r)
            (UnforcedLeray.Cyl.avgμ c)) := by
    rw [setLIntegral_indicator measurableSet_Ioi, Set.inter_comm]
    by_cases htH : t < H
    · rw [lintegral_mul_const' _ _ hD]
      have hS' := le_trans (hS htH) (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (le_max_left K 0) (Real.rpow_nonneg ht.le _)))
      gcongr
    · have hempty : Icc σ H ∩ Ioi t = ∅ :=
        Set.eq_empty_of_forall_notMem (fun x hx => by
          have h1 : x ≤ t := le_trans hx.1.2 (not_lt.1 htH)
          exact (not_lt.2 h1) hx.2)
      rw [hempty]
      simp
  -- final assembly
  by_cases htH : t < H
  · have hkey : ENNReal.ofReal (t ^ μ.re) * ENNReal.ofReal (t⁻¹) = ENNReal.ofReal (t ^ (μ.re - 1)) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), Real.rpow_sub_one ht.ne', div_eq_mul_inv,
        mul_comm]
    rw [Set.indicator_of_mem (show t ∈ Ioo (0 : ℝ) H from ⟨ht, htH⟩)]
    refine le_trans hchain (le_trans hRHS (le_of_eq ?_))
    rw [ENNReal.ofReal_mul (le_max_right K 0), ENNReal.ofReal_mul (le_max_right C0 0)]
    calc ENNReal.ofReal (max K 0) * ENNReal.ofReal (t ^ μ.re) *
          (ENNReal.ofReal (t⁻¹) * ENNReal.ofReal (max C0 0) *
            eLpNorm (fun z : ℝ × ℝ => G (t, z)) (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c))
        = ENNReal.ofReal (max C0 0) * ENNReal.ofReal (max K 0) *
            ((ENNReal.ofReal (t ^ μ.re) * ENNReal.ofReal (t⁻¹)) *
              eLpNorm (fun z : ℝ × ℝ => G (t, z)) (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c)) := by
          ring
      _ = ENNReal.ofReal (max C0 0) * ENNReal.ofReal (max K 0) *
            (ENNReal.ofReal (t ^ (μ.re - 1)) *
              eLpNorm (fun z : ℝ × ℝ => G (t, z)) (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c)) := by
          rw [hkey]
  · have hempty : Icc σ H ∩ Ioi t = ∅ :=
      Set.eq_empty_of_forall_notMem (fun x hx => (not_lt.2 (le_trans hx.1.2 (not_lt.1 htH))) hx.2)
    have hz : ∫⁻ s in Icc σ H, (Ioi t).indicator (fun s : ℝ => ENNReal.ofReal ((t / s) ^ μ.re) *
          (ENNReal.ofReal (t⁻¹) * ENNReal.ofReal (max C0 0) *
            eLpNorm (fun z : ℝ × ℝ => G (t, z)) (ENNReal.ofReal r)
              (UnforcedLeray.Cyl.avgμ c))) s = 0 := by
      rw [setLIntegral_indicator measurableSet_Ioi, Set.inter_comm, hempty]
      simp
    rw [Set.indicator_of_notMem (show t ∉ Ioo (0 : ℝ) H from fun h => htH h.2), mul_zero]
    exact le_trans hchain (le_of_eq hz)

theorem boxSlice : UnforcedLeray.Short.IIb.BoxSlice := by
  unfold UnforcedLeray.Short.IIb.BoxSlice
  intro r hr1 hr3 μ hμ ν c hν hc G hG σ H R hσ
  obtain ⟨C0, hC0⟩ := flatHeatBoxBound_of periodicBoxBound flatHeatAEMeas r c R hr1.le hc
  obtain ⟨K, hK⟩ := boxSliceS μ.re σ H hσ
  refine ⟨max C0 0 * max K 0, ?_⟩
  filter_upwards [deqSliceAe c r G hc hr1 hG, ae_restrict_mem measurableSet_Ioi] with t ht htpos
  exact boxSlice_pt ν c r R σ H μ G t hν htpos C0 K
    (fun θ g hθ hper hae => hC0 θ g hθ hper hae) ht (fun htH => hK t htpos htH)

end UnforcedLeray.Short.IIb
