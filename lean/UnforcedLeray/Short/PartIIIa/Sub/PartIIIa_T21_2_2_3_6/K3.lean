import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6.Unique

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace CellUniqueAux

/-- Periodization of `g` with period `d` in the first variable. -/
def per (d : ℝ) (g : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℝ := ∑' n : ℤ, g (x.1 + (n : ℝ) * d, x.2)

theorem per_periodic (d : ℝ) (g : ℝ × ℝ → ℝ) (x : ℝ × ℝ) :
    per d g (x.1 + d, x.2) = per d g x := by
  unfold per
  refine (tsum_congr fun n => ?_).trans
    (Equiv.tsum_eq (Equiv.addRight (1 : ℤ)) (fun n : ℤ => g (x.1 + (n : ℝ) * d, x.2)))
  show g (x.1 + d + (n : ℝ) * d, x.2) = g (x.1 + (((n + 1 : ℤ)) : ℝ) * d, x.2)
  congr 1
  push_cast
  ring_nf

theorem per_band {d C : ℝ} {g : ℝ × ℝ → ℝ} (hg : ∀ y : ℝ × ℝ, C < |y.2| → g y = 0)
    (x : ℝ × ℝ) (hx : C < |x.2|) : per d g x = 0 := by
  unfold per
  have h0 : ∀ n : ℤ, g (x.1 + (n : ℝ) * d, x.2) = 0 := fun n => hg _ hx
  simp [h0]

theorem per_eq_self {d : ℝ} (hd : 0 < d) {g : ℝ × ℝ → ℝ}
    (hz : ∀ y : ℝ × ℝ, y.1 ∉ Ioo (-(d / 2)) (d / 2) → g y = 0)
    {x : ℝ × ℝ} (hx : x.1 ∈ Ico (-(d / 2)) (d / 2)) : per d g x = g x := by
  unfold per
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    apply hz
    obtain ⟨h1, h2⟩ := hx
    intro hmem
    dsimp only at hmem
    obtain ⟨m1, m2⟩ := hmem
    rcases lt_or_gt_of_ne hn with h | h
    · have hn1 : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
      have key : (n : ℝ) * d ≤ -d := by nlinarith
      linarith
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
      have key : d ≤ (n : ℝ) * d := by nlinarith
      linarith

theorem per_contDiff {d : ℝ} (hd : 0 < d) {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) : ContDiff ℝ ∞ (per d g) := by
  rw [contDiff_iff_contDiffAt]
  intro x0
  obtain ⟨A, hA⟩ := hc.isCompact.exists_bound_of_continuousOn
    (continuous_fst.continuousOn (s := tsupport g))
  obtain ⟨N, hN⟩ := exists_nat_ge ((A + |x0.1| + 1) / d)
  have hN' : A + |x0.1| + 1 ≤ (N : ℝ) * d := by
    rw [div_le_iff₀ hd] at hN
    linarith
  have hloc : ∀ x ∈ Metric.ball x0 1,
      per d g x = ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), g (x.1 + (n : ℝ) * d, x.2) := by
    intro x hx
    unfold per
    apply tsum_eq_sum
    intro n hn
    by_contra hne
    have hmem : (x.1 + (n : ℝ) * d, x.2) ∈ tsupport g := subset_tsupport _ hne
    have hb := hA _ hmem
    have hy : |x.1 + (n : ℝ) * d| ≤ A := by simpa [Real.norm_eq_abs] using hb
    have hx1 : |x.1 - x0.1| < 1 := by
      have h := Metric.mem_ball.1 hx
      rw [Prod.dist_eq] at h
      have h' : dist x.1 x0.1 < 1 := lt_of_le_of_lt (le_max_left _ _) h
      rwa [Real.dist_eq] at h'
    have hy' := abs_le.1 hy
    have hx1' := abs_lt.1 hx1
    have hnd : |(n : ℝ) * d| ≤ A + |x0.1| + 1 := by
      rw [abs_le]
      constructor
      · linarith [neg_abs_le x0.1, le_abs_self x0.1, abs_nonneg x0.1]
      · linarith [neg_abs_le x0.1, le_abs_self x0.1, neg_le_abs x0.1, abs_nonneg x0.1]
    have hnd2 : |(n : ℝ)| * d ≤ (N : ℝ) * d := by
      have e : |(n : ℝ) * d| = |(n : ℝ)| * d := by rw [abs_mul, abs_of_pos hd]
      linarith
    have hn' : |(n : ℝ)| ≤ (N : ℝ) := le_of_mul_le_mul_right hnd2 hd
    obtain ⟨j1, j2⟩ := abs_le.1 hn'
    exact hn (Finset.mem_Icc.2 ⟨by exact_mod_cast j1, by exact_mod_cast j2⟩)
  have hsm : ContDiff ℝ ∞ (fun x : ℝ × ℝ => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      g (x.1 + (n : ℝ) * d, x.2)) := by
    refine ContDiff.sum fun n _ => ?_
    exact hg.comp ((contDiff_fst.add contDiff_const).prodMk contDiff_snd)
  refine ContDiffAt.congr_of_eventuallyEq hsm.contDiffAt ?_
  filter_upwards [Metric.ball_mem_nhds x0 one_pos] with x hx
  exact hloc x hx

end CellUniqueAux

theorem cellUnique : UnforcedLeray.Short.IIIa.AdjE1.CellUnique := by
  intro d f hd hf hf0
  set U : Set (ℝ × ℝ) := Ioo (-(d / 2)) (d / 2) ×ˢ (univ : Set ℝ) with hU
  have hUo : IsOpen U := isOpen_Ioo.prod isOpen_univ
  have hUcell : U ⊆ UnforcedLeray.B0579.cell d := fun x hx =>
    ⟨⟨le_of_lt (Set.mem_prod.1 hx).1.1, (Set.mem_prod.1 hx).1.2⟩, Set.mem_univ _⟩
  have hloc : LocallyIntegrableOn f U := by
    intro x _hx
    refine ⟨U ∩ {y : ℝ × ℝ | |y.2| < |x.2| + 1}, inter_mem_nhdsWithin U ?_, ?_⟩
    · exact (isOpen_lt (by fun_prop) (by fun_prop)).mem_nhds
        (by show |x.2| < |x.2| + 1; linarith)
    · exact (hf (|x.2| + 1)).mono_set (fun y hy => ⟨hUcell hy.1, le_of_lt (show |y.2| < |x.2| + 1 from hy.2)⟩)
  have hA : ∀ g : ℝ × ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ U →
      ∫ y, g y • f y = 0 := by
    intro g hg hc hsub
    have hz : ∀ y : ℝ × ℝ, y.1 ∉ Ioo (-(d / 2)) (d / 2) → g y = 0 := by
      intro y hy
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      exact hy (Set.mem_prod.1 (hsub hmem)).1
    have hzero_out : ∀ y : ℝ × ℝ, y ∉ UnforcedLeray.B0579.cell d → g y • f y = 0 := by
      intro y hy
      have : g y = 0 := hz y (fun h => hy ⟨⟨le_of_lt h.1 , h.2⟩, Set.mem_univ _⟩)
      simp [this]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero_out]
    obtain ⟨C, hC⟩ := hc.isCompact.exists_bound_of_continuousOn
      (continuous_snd.continuousOn (s := tsupport g))
    have hgC : ∀ y : ℝ × ℝ, C < |y.2| → g y = 0 := by
      intro y hy
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      have h1 : |y.2| ≤ C := by simpa [Real.norm_eq_abs] using hC y hmem
      linarith
    have hP := hf0 (CellUniqueAux.per d g)
      { smooth := CellUniqueAux.per_contDiff hd hg hc
        periodic := fun x => CellUniqueAux.per_periodic d g x
        band := ⟨C, fun x hx => CellUniqueAux.per_band hgC x hx⟩ }
    have hcongr : ∫ x in UnforcedLeray.B0579.cell d, g x • f x =
        ∫ x in UnforcedLeray.B0579.cell d, f x * ((CellUniqueAux.per d g x : ℝ) : ℂ) := by
      refine setIntegral_congr_fun (UnforcedLeray.B0579.measurableSet_cell d) (fun x hx => ?_)
      rw [CellUniqueAux.per_eq_self hd hz (Set.mem_prod.1 hx).1, Complex.real_smul, mul_comm]
    rw [hcongr]
    exact hP
  have hae := IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hUo hloc hA
  have hnull : volume (UnforcedLeray.B0579.cell d \ U) = 0 := by
    apply measure_mono_null (t := ({-(d / 2)} : Set ℝ) ×ˢ (univ : Set ℝ))
    · rintro ⟨a, b⟩ hx
      obtain ⟨hc, hn⟩ := hx
      have hc1 : -(d / 2) ≤ a ∧ a < d / 2 := Set.mem_prod.1 hc |>.1
      have ha : a = -(d / 2) := by
        by_contra hne
        apply hn
        exact Set.mem_prod.2 ⟨⟨lt_of_le_of_ne hc1.1 (Ne.symm hne), hc1.2⟩, Set.mem_univ _⟩
      exact Set.mem_prod.2 ⟨ha, Set.mem_univ _⟩
    · rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]
  have hae2 : UnforcedLeray.B0579.cell d =ᵐ[volume] U := by
    rw [ae_eq_set]
    refine ⟨hnull, ?_⟩
    rw [Set.sdiff_eq_empty.2 hUcell, measure_empty]
  have hae' : ∀ᵐ x ∂(volume.restrict U), f x = 0 :=
    (ae_restrict_iff' hUo.measurableSet).2 hae
  rw [Measure.restrict_congr_set hae2]
  exact hae'
