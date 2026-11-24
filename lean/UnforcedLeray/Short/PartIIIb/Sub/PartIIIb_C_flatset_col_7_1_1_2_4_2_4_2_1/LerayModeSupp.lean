import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.FlatLerayDefs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.CoefSmoothBand

/-!
# `LerayModeSupp` (organize task `PartIII-b:C/flatset/col/7/1/1/2/4/2/4/2/1/1/12`)

Source of record `the November 2 reference manuscript`
lines 1650-1656 and 1684-1689 (age band): the solenoidal mode coefficients `(-∂_η ψ_n, i k_n ψ_n)`
vanish below the age band of the test `f`. The potential `ψ_n` is a Green convolution of data
supported in the band `s0 ≤ s ≤ s1` (`CoefSmoothBand`), so `ψ_n` vanishes on `{s < s0}`, hence so
does its `η`-derivative (it is locally zero there).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FlatLeray

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.Short.PartIIa

theorem lerayModeSupp : LerayModeSupp := by
  intro c hc f hf
  obtain ⟨s0, s1, L, hs0, hb⟩ := coefSmoothBand c hc f hf
  refine ⟨s0, hs0, fun n x hx => ?_⟩
  by_cases hn : n = 0
  · simp [lerayMode, hn]
  · obtain ⟨ha, hb', hBa, hBb⟩ := hb n
    have hk : nzk c n ≠ 0 := by
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      exact div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hn') hc.ne'
    have hB2 := nzmsH2_band (k := nzk c n) hBa hBb
    -- the potential vanishes on the open half-space `{s < s0}`
    have hz : ∀ y : ℝ × ℝ, y.1 < s0 → psiN c f n y = 0 := by
      intro y hy
      unfold psiN
      exact nzConv_eq_zero (k := nzk c n) (s0 := s0) (s1 := s1)
        (h := nzmsH2 (nzk c n) (coefR c f n) (coefZ c f n))
        (fun z hz' => (hB2 z hz').1)
        (fun hmem => absurd (Set.mem_Icc.1 hmem).1 (not_le.2 hy))
    have hev : psiN c f n =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
      have hopen : IsOpen {y : ℝ × ℝ | y.1 < s0} := isOpen_lt continuous_fst continuous_const
      filter_upwards [IsOpen.mem_nhds hopen (show x ∈ {y : ℝ × ℝ | y.1 < s0} from hx)] with y hy
      exact hz y hy
    have h1 : dEta2 (psiN c f n) x = 0 := by
      unfold dEta2
      rw [hev.fderiv_eq]
      simp
    have h2 : psiN c f n x = 0 := hz x hx
    unfold lerayMode
    rw [if_neg hn, h1, h2]
    ext i
    fin_cases i <;> simp

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FlatLeray
