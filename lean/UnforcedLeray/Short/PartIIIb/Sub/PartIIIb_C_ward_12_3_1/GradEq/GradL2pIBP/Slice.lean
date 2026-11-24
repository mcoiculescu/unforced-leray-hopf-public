import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GradL2pIBP
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GradL2pIBP.Slice.Cut
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GradL2pIBP.Slice.Main

/-!
# The slice inequality `GradL2pSlice` (source 2531, 1515-1531, 1415-1424)

Cutoff integration by parts (`GradSlice.slice_cut`, spatial cutoffs `GradSlice.exists_cutoff`),
then Fatou in the cutoff radius.  `p = q₀ = 11/4`, `s = 2p-2 = 7/2`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open MeasureTheory Set Filter Topology
open scoped ENNReal

/-- Finiteness of `∫|g|^{2p-1}` for `g ∈ L^p` bounded. -/
theorem gradSlice_J_lt_top (g : UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3) (K : ℝ)
    (hK : ∀ y, ‖g y‖ ≤ K) (hg : MemLp g UnforcedLeray.B0412.q0E volume) :
    ∫⁻ y, ENNReal.ofReal (‖g y‖ ^ ((7 / 2 : ℝ) + 1)) ≠ ∞ := by
  have hq : UnforcedLeray.B0412.q0E.toReal = 11 / 4 := UnforcedLeray.B0412.q0E_toReal
  have hne0 : UnforcedLeray.B0412.q0E ≠ 0 := by
    intro h; rw [h] at hq; norm_num at hq
  have hlt := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hne0
    UnforcedLeray.B0412.q0E_ne_top hg.2
  rw [hq] at hlt
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  have hpt : ∀ y, ENNReal.ofReal (‖g y‖ ^ ((7 / 2 : ℝ) + 1)) ≤
      ENNReal.ofReal (K ^ (7 / 4 : ℝ)) * ‖g y‖ₑ ^ (11 / 4 : ℝ) := by
    intro y
    have e1 : ‖g y‖ ^ ((7 / 2 : ℝ) + 1) = ‖g y‖ ^ (7 / 4 : ℝ) * ‖g y‖ ^ (11 / 4 : ℝ) := by
      rw [← Real.rpow_add' (norm_nonneg _) (by norm_num)]; norm_num
    have e2 : ‖g y‖ₑ ^ (11 / 4 : ℝ) = ENNReal.ofReal (‖g y‖ ^ (11 / 4 : ℝ)) := by
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
    rw [e1, e2, ← ENNReal.ofReal_mul (Real.rpow_nonneg hK0 _)]
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (norm_nonneg _) (hK y) (by norm_num))
      (Real.rpow_nonneg (norm_nonneg _) _)
  refine ne_of_lt ((lintegral_mono hpt).trans_lt ?_)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hlt

/-- **Slice inequality** `GradL2pSlice`. -/
theorem gradL2pSlice : GradL2pSlice := by
  intro M j w g h hM sm hg hh
  obtain ⟨C, hC0, χ, hχ1, hχcs, hχbd, hχlim, hχder⟩ := GradSlice.exists_cutoff
  obtain ⟨K, hK⟩ := sm.g_bdd
  have hq : UnforcedLeray.B0412.q0E.toReal = 11 / 4 := UnforcedLeray.B0412.q0E_toReal
  have hw1 : ContDiff ℝ 1 w := sm.w_smooth.of_le (by exact_mod_cast le_top)
  have hg1 : ContDiff ℝ 1 g := sm.g_smooth.of_le (by exact_mod_cast le_top)
  have hJ := gradSlice_J_lt_top g K hK hg
  have hgc : Continuous g := hg1.continuous
  have hhc : Continuous h := by
    have : h = fun y => fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ)) :=
      funext fun y => (sm.h_eq y).symm
    rw [this]; exact (hg1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  set I := ∫⁻ y, ENNReal.ofReal (‖g y‖ ^ (7 / 2 : ℝ) * ‖h y‖) with hI
  set J := ∫⁻ y, ENNReal.ofReal (‖g y‖ ^ ((7 / 2 : ℝ) + 1)) with hJdef
  have hn : ∀ n : ℕ, ∫⁻ y, ENNReal.ofReal (χ n y * ‖g y‖ ^ ((7 / 2 : ℝ) + 2)) ≤
      ENNReal.ofReal (((7 / 2 : ℝ) + 1) * M) * I +
      ENNReal.ofReal (C * (1 / ((n : ℝ) + 1)) * M) * J := by
    intro n
    refine GradSlice.slice_cut (by norm_num : (1 : ℝ) < 7 / 2) hM (EuclideanSpace.single j (1 : ℝ))
      hw1 hg1 sm.w_le sm.g_eq sm.h_eq (hχ1 n) (hχcs n) (fun y => (hχbd n y).1)
      (fun y => (hχbd n y).2) (c := C * (1 / ((n : ℝ) + 1))) ?_
    intro y
    refine (hχder n y _).trans ?_
    simp only [EuclideanSpace.norm_single, norm_one, mul_one]
    rw [mul_one_div]
  have e1 : 2 * UnforcedLeray.B0412.q0E.toReal = (7 / 2 : ℝ) + 2 := by rw [hq]; norm_num
  have e2 : 2 * UnforcedLeray.B0412.q0E.toReal - 2 = (7 / 2 : ℝ) := by rw [hq]; norm_num
  have e3 : 2 * UnforcedLeray.B0412.q0E.toReal - 1 = (7 / 2 : ℝ) + 1 := by rw [hq]; norm_num
  rw [e2, e3, e1]
  have hpt : ∀ y, liminf (fun n : ℕ => ENNReal.ofReal (χ n y * ‖g y‖ ^ ((7 / 2 : ℝ) + 2))) atTop
      = ENNReal.ofReal (‖g y‖ ^ ((7 / 2 : ℝ) + 2)) := by
    intro y
    apply Tendsto.liminf_eq
    have := ENNReal.tendsto_ofReal ((hχlim y).mul_const (‖g y‖ ^ ((7 / 2 : ℝ) + 2)))
    simpa using this
  have hb : Tendsto (fun n : ℕ => ENNReal.ofReal (C * (1 / ((n : ℝ) + 1)) * M) * J) atTop
      (nhds 0) := by
    have h0 : Tendsto (fun n : ℕ => C * (1 / ((n : ℝ) + 1)) * M) atTop (nhds 0) := by
      have := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C).mul_const M
      simpa using this
    have h1 := ENNReal.tendsto_ofReal h0
    rw [ENNReal.ofReal_zero] at h1
    have := ENNReal.Tendsto.mul_const h1 (Or.inr hJ)
    simpa using this
  calc ∫⁻ y, ENNReal.ofReal (‖g y‖ ^ ((7 / 2 : ℝ) + 2))
      = ∫⁻ y, liminf (fun n : ℕ => ENNReal.ofReal (χ n y * ‖g y‖ ^ ((7 / 2 : ℝ) + 2))) atTop :=
        lintegral_congr fun y => (hpt y).symm
    _ ≤ liminf (fun n : ℕ => ∫⁻ y, ENNReal.ofReal (χ n y * ‖g y‖ ^ ((7 / 2 : ℝ) + 2))) atTop :=
        lintegral_liminf_le fun n =>
          (((hχ1 n).continuous.mul (hgc.norm.rpow_const (fun _ => Or.inr (by norm_num)))).measurable
            ).ennreal_ofReal
    _ ≤ liminf (fun n : ℕ => ENNReal.ofReal (((7 / 2 : ℝ) + 1) * M) * I +
          ENNReal.ofReal (C * (1 / ((n : ℝ) + 1)) * M) * J) atTop :=
        Filter.liminf_le_liminf (Eventually.of_forall hn)
    _ = ENNReal.ofReal (((7 / 2 : ℝ) + 1) * M) * I := by
        apply Tendsto.liminf_eq
        simpa using (tendsto_const_nhds (x := ENNReal.ofReal (((7 / 2 : ℝ) + 1) * M) * I)).add hb

end UnforcedLeray.Short.PartIIIb.Concrete
