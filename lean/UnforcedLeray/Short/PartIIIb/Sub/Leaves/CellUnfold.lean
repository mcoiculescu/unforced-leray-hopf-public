import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_9_3

/-!
# `PartIII-b:C/inst/9/3` leaf 2: unfolding the lattice sum over the centred cell (source 5063-5079)

The statement `FAcCellUnfold` quantifies over arbitrary nonnegative `f`. Mathlib's `lintegral` is an
inner integral (a supremum over measurable minorants), and for non-measurable `f` the sum over the
lattice shifts cannot be controlled by `∫⁻ f` (inner integrals are superadditive, not subadditive).
The proof below is the measurable version: it needs `Measurable f`, which every use site satisfies
(`fAcG a` is continuous). See the report for the proposed statement change.

Proof: `avgμ c = c⁻¹ • cellμ c`; `lintegral_tsum` on the shifts; each cell integral is moved to the
whole plane by translation (`lintegral_add_right_eq_self`), and the translated cells `cell - jc·e₁`
are pairwise disjoint, so `∑_j 1_{cell - jc}(u) ≤ 1` pointwise.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Measurable version of the cell unfolding (`FAcCellUnfold` with `Measurable f` added). -/
theorem fAcCellUnfold_meas : ∀ (c : ℝ) (f : ℝ × ℝ → ℝ), 0 < c → Measurable f →
    (∀ y, 0 ≤ f y) →
    ∫⁻ x, ENNReal.ofReal (∑' j : ℤ, f (x.1 - j * c, x.2)) ∂(UnforcedLeray.Cyl.avgμ c)
      ≤ ENNReal.ofReal c⁻¹ * ∫⁻ y, ENNReal.ofReal (f y) ∂volume := by
  intro c f hc hfm hf0
  have hFm : Measurable (fun y : ℝ × ℝ => ENNReal.ofReal (f y)) := hfm.ennreal_ofReal
  have hshift : ∀ j : ℤ, Measurable (fun x : ℝ × ℝ => ENNReal.ofReal (f (x.1 - j * c, x.2))) :=
    fun j => hFm.comp ((measurable_fst.sub_const _).prodMk measurable_snd)
  -- pointwise: ofReal of a tsum is at most the tsum of ofReal
  have hofTsum : ∀ g : ℤ → ℝ, (∀ j, 0 ≤ g j) →
      ENNReal.ofReal (∑' j, g j) ≤ ∑' j, ENNReal.ofReal (g j) := by
    intro g hg
    by_cases hs : Summable g
    · rw [ENNReal.ofReal_tsum_of_nonneg hg hs]
    · rw [tsum_eq_zero_of_not_summable hs, ENNReal.ofReal_zero]
      exact zero_le
  -- the translated indicator functions
  obtain ⟨φ, hφdef⟩ : ∃ φ : ℤ → ℝ × ℝ → ENNReal,
      φ = fun (j : ℤ) (u : ℝ × ℝ) => (UnforcedLeray.Cyl.cell c).indicator
        (fun x : ℝ × ℝ => ENNReal.ofReal (f (x.1 - (j : ℝ) * c, x.2)))
        (u + ((j : ℝ) * c, 0)) := ⟨_, rfl⟩
  have hφeq : ∀ (j : ℤ) (u : ℝ × ℝ), φ j u =
      if u.1 + (j : ℝ) * c ∈ Ico (-c / 2) (c / 2) then ENNReal.ofReal (f u) else 0 := by
    intro j u
    rw [hφdef]
    by_cases h : u.1 + (j : ℝ) * c ∈ Ico (-c / 2) (c / 2)
    · have hm : (u + ((j : ℝ) * c, 0)) ∈ UnforcedLeray.Cyl.cell c := ⟨h, mem_univ _⟩
      have he : ((u + ((j : ℝ) * c, 0)).1 - (j : ℝ) * c, (u + ((j : ℝ) * c, 0)).2) = u := by
        simp
      simp only
      rw [Set.indicator_of_mem hm, if_pos h, he]
    · have hm : (u + ((j : ℝ) * c, 0)) ∉ UnforcedLeray.Cyl.cell c := fun hm' => h hm'.1
      simp only
      rw [Set.indicator_of_notMem hm, if_neg h]
  have hφm : ∀ j : ℤ, Measurable (φ j) := by
    intro j
    rw [hφdef]
    exact ((hshift j).indicator (UnforcedLeray.Cyl.measurableSet_cell c)).comp
      (measurable_add_const _)
  have hmem : ∀ (j : ℤ) (u : ℝ × ℝ), φ j u ≠ 0 → u.1 + (j : ℝ) * c ∈ Ico (-c / 2) (c / 2) := by
    intro j u h
    rw [hφeq] at h
    by_contra hn
    exact h (if_neg hn)
  have hφle : ∀ (j : ℤ) (u : ℝ × ℝ), φ j u ≤ ENNReal.ofReal (f u) := by
    intro j u
    rw [hφeq]
    split_ifs
    · exact le_rfl
    · exact zero_le
  have huniq : ∀ (j j' : ℤ) (u : ℝ × ℝ), φ j u ≠ 0 → φ j' u ≠ 0 → j = j' := by
    intro j j' u h1 h2
    obtain ⟨a1, a2⟩ := mem_Ico.mp (hmem j u h1)
    obtain ⟨b1, b2⟩ := mem_Ico.mp (hmem j' u h2)
    have hlt : ((j : ℝ) - j') * c < c := by linarith
    have hgt : -c < ((j : ℝ) - j') * c := by linarith
    have hlt' : ((j : ℝ) - j') < 1 := by
      by_contra h
      push_neg at h
      nlinarith [mul_le_mul_of_nonneg_right h hc.le]
    have hgt' : -1 < ((j : ℝ) - j') := by
      by_contra h
      push_neg at h
      nlinarith [mul_le_mul_of_nonneg_right h hc.le]
    have i1 : j - j' < 1 := by
      have : ((j - j' : ℤ) : ℝ) < 1 := by push_cast; linarith
      exact_mod_cast this
    have i2 : -1 < j - j' := by
      have : (-1 : ℝ) < ((j - j' : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    omega
  have hpw : ∀ u : ℝ × ℝ, ∑' j : ℤ, φ j u ≤ ENNReal.ofReal (f u) := by
    intro u
    by_cases h : ∃ j0 : ℤ, φ j0 u ≠ 0
    · obtain ⟨j0, hj0⟩ := h
      have hs : ∀ j, j ≠ j0 → φ j u = 0 := by
        intro j hj
        by_contra hne
        exact hj (huniq j j0 u hne hj0)
      rw [tsum_eq_single j0 hs]
      exact hφle j0 u
    · push_neg at h
      simp [h]
  -- the cell integrals of the shifts, moved to the plane
  have hkey : ∑' j : ℤ, ∫⁻ x in UnforcedLeray.Cyl.cell c,
      ENNReal.ofReal (f (x.1 - j * c, x.2)) ≤ ∫⁻ y, ENNReal.ofReal (f y) ∂volume := by
    calc ∑' j : ℤ, ∫⁻ x in UnforcedLeray.Cyl.cell c, ENNReal.ofReal (f (x.1 - j * c, x.2))
        = ∑' j : ℤ, ∫⁻ u, φ j u := by
          refine tsum_congr fun j => ?_
          rw [← lintegral_indicator (UnforcedLeray.Cyl.measurableSet_cell c)]
          rw [hφdef]
          exact (lintegral_add_right_eq_self
            (fun x => (UnforcedLeray.Cyl.cell c).indicator
              (fun x => ENNReal.ofReal (f (x.1 - j * c, x.2))) x) ((j : ℝ) * c, 0)).symm
      _ = ∫⁻ u, ∑' j : ℤ, φ j u := (lintegral_tsum fun j => (hφm j).aemeasurable).symm
      _ ≤ ∫⁻ y, ENNReal.ofReal (f y) ∂volume := lintegral_mono fun u => hpw u
  calc ∫⁻ x, ENNReal.ofReal (∑' j : ℤ, f (x.1 - j * c, x.2)) ∂(UnforcedLeray.Cyl.avgμ c)
      ≤ ∫⁻ x, ∑' j : ℤ, ENNReal.ofReal (f (x.1 - j * c, x.2)) ∂(UnforcedLeray.Cyl.avgμ c) :=
        lintegral_mono fun x => hofTsum _ fun j => hf0 _
    _ = ∑' j : ℤ, ∫⁻ x, ENNReal.ofReal (f (x.1 - j * c, x.2)) ∂(UnforcedLeray.Cyl.avgμ c) :=
        lintegral_tsum fun j => (hshift j).aemeasurable
    _ = ∑' j : ℤ, ENNReal.ofReal c⁻¹ * ∫⁻ x in UnforcedLeray.Cyl.cell c,
          ENNReal.ofReal (f (x.1 - j * c, x.2)) :=
        tsum_congr fun j => UnforcedLeray.Cyl.lintegral_avgμ _
    _ = ENNReal.ofReal c⁻¹ * ∑' j : ℤ, ∫⁻ x in UnforcedLeray.Cyl.cell c,
          ENNReal.ofReal (f (x.1 - j * c, x.2)) := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal c⁻¹ * ∫⁻ y, ENNReal.ofReal (f y) ∂volume := by gcongr

theorem fAcCellUnfold : FAcCellUnfold := fAcCellUnfold_meas

end UnforcedLeray.Short.PartIIIb.Concrete
