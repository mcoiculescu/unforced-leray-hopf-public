import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_5_5_7_1

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

theorem mollPerzProps_proof : UnforcedLeray.Short.IIb.MollPerzProps := by
  intro c M hc h hh hzero
  -- finite support on bounded q-windows
  have hfin : ∀ R : ℝ, ∃ N : ℕ, ∀ x : Coord, |x.2.1| ≤ R →
      moPerz c h x = ∑ k ∈ Finset.Icc (-(N : ℤ)) N, h (x.1, (x.2.1 + (k : ℝ) * c, x.2.2)) := by
    intro R
    obtain ⟨N, hN⟩ := exists_nat_ge ((R + c) / c)
    have hNc : R + c ≤ (N : ℝ) * c := (div_le_iff₀ hc).mp hN
    refine ⟨N, fun x hx => ?_⟩
    have hbounds : -R ≤ x.2.1 ∧ x.2.1 ≤ R := abs_le.mp hx
    unfold moPerz
    apply finsum_eq_sum_of_support_subset
    intro k hk
    rw [Finset.mem_coe, Finset.mem_Icc]
    by_contra hcon
    apply hk
    have hcases : (N : ℤ) < k ∨ k < -(N : ℤ) := by omega
    apply hzero
    intro hmem
    have hq : -c ≤ x.2.1 + (k : ℝ) * c ∧ x.2.1 + (k : ℝ) * c ≤ c := ⟨hmem.2.1.1, hmem.2.1.2⟩
    rcases hcases with h1 | h1
    · have h1' : (N : ℤ) + 1 ≤ k := h1
      have h2 : ((N : ℤ) : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast h1'
      push_cast at h2
      have h3 : ((N : ℝ) + 1) * c ≤ (k : ℝ) * c := mul_le_mul_of_nonneg_right h2 hc.le
      nlinarith [hq.2, hbounds.1, hNc, h3]
    · have h1' : k + 1 ≤ -(N : ℤ) := h1
      have h2 : (k : ℝ) + 1 ≤ -(N : ℝ) := by exact_mod_cast h1'
      have h3 : (k : ℝ) * c ≤ (-(N : ℝ) - 1) * c :=
        mul_le_mul_of_nonneg_right (by linarith) hc.le
      nlinarith [hq.1, hbounds.2, hNc, h3]
  -- continuity
  have hcont : Continuous (moPerz c h) := by
    refine continuous_iff_continuousAt.2 fun x0 => ?_
    obtain ⟨N, hN⟩ := hfin (|x0.2.1| + 1)
    have hopen : {x : Coord | |x.2.1| < |x0.2.1| + 1} ∈ 𝓝 x0 :=
      (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by show |x0.2.1| < |x0.2.1| + 1; linarith)
    have hg : ContinuousAt (fun x : Coord => ∑ k ∈ Finset.Icc (-(N : ℤ)) N,
        h (x.1, (x.2.1 + (k : ℝ) * c, x.2.2))) x0 :=
      (continuous_finsetSum _ fun k _ => hh.comp (by fun_prop)).continuousAt
    refine hg.congr ?_
    filter_upwards [hopen] with x hx
    exact (hN x (le_of_lt hx)).symm
  -- periodicity
  have hper : ∀ x : Coord, moPerz c h (qShift c x) = moPerz c h x := by
    intro x
    have hfun : ∀ k : ℤ, h (x.1, (x.2.1 + c + (k : ℝ) * c, x.2.2))
        = h (x.1, (x.2.1 + (((k + 1 : ℤ)) : ℝ) * c, x.2.2)) :=
      fun k => congrArg h (Prod.ext rfl (Prod.ext (by push_cast; ring) rfl))
    calc moPerz c h (qShift c x)
        = ∑ᶠ k : ℤ, h (x.1, (x.2.1 + c + (k : ℝ) * c, x.2.2)) := rfl
      _ = ∑ᶠ k : ℤ, h (x.1, (x.2.1 + (((k + 1 : ℤ)) : ℝ) * c, x.2.2)) := finsum_congr hfun
      _ = ∑ᶠ k : ℤ, h (x.1, (x.2.1 + (k : ℝ) * c, x.2.2)) :=
          finsum_comp_equiv (Equiv.addRight (1 : ℤ))
            (f := fun k : ℤ => h (x.1, (x.2.1 + (k : ℝ) * c, x.2.2)))
      _ = moPerz c h x := rfl
  -- integer shifts in q
  have hsh : ∀ (m : ℤ) (x : Coord),
      moPerz c h (x.1, (x.2.1 + (m : ℝ) * c, x.2.2)) = moPerz c h x := by
    intro m
    induction m using Int.induction_on with
    | zero => intro x; simp
    | succ i ih =>
      intro x
      have e : (x.1, (x.2.1 + (((i + 1 : ℤ)) : ℝ) * c, x.2.2))
          = qShift c (x.1, (x.2.1 + (i : ℝ) * c, x.2.2)) :=
        Prod.ext rfl (Prod.ext (by unfold qShift; push_cast; ring) rfl)
      rw [e, hper]
      exact ih x
    | pred i ih =>
      intro x
      have e : qShift c (x.1, (x.2.1 + (((-(i : ℤ) - 1 : ℤ)) : ℝ) * c, x.2.2))
          = (x.1, (x.2.1 + (((-(i : ℤ) : ℤ)) : ℝ) * c, x.2.2)) :=
        Prod.ext rfl (Prod.ext (by unfold qShift; push_cast; ring) rfl)
      rw [← hper, e]
      exact ih x
  -- vanishing for large s or eta
  have hvan : ∀ x : Coord, M + 1 < |x.1| ∨ M + 1 < |x.2.2| → moPerz c h x = 0 := by
    intro x hx
    have hzt : ∀ k : ℤ, h (x.1, (x.2.1 + (k : ℝ) * c, x.2.2)) = 0 := by
      intro k
      apply hzero
      intro hmem
      have h1 : -M - 1 ≤ x.1 := hmem.1.1
      have h2 : x.1 ≤ M + 1 := hmem.1.2
      have h3 : -M - 1 ≤ x.2.2 := hmem.2.2.1
      have h4 : x.2.2 ≤ M + 1 := hmem.2.2.2
      rcases hx with hx | hx
      · rcases lt_abs.mp hx with hx' | hx' <;> linarith
      · rcases lt_abs.mp hx with hx' | hx' <;> linarith
    unfold moPerz
    simp [hzt]
  refine ⟨hcont, hper, ?_, hvan⟩
  -- boundedness
  have hK : IsCompact (Icc (-M - 1) (M + 1) ×ˢ (Icc (-c / 2) (c / 2) ×ˢ Icc (-M - 1) (M + 1))) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C 0, fun x => ?_⟩
  by_cases hx : |x.1| ≤ M + 1 ∧ |x.2.2| ≤ M + 1
  · obtain ⟨m, hm1, hm2⟩ : ∃ m : ℤ, (m : ℝ) ≤ (x.2.1 + c / 2) / c ∧
        (x.2.1 + c / 2) / c < (m : ℝ) + 1 :=
      ⟨⌊(x.2.1 + c / 2) / c⌋, Int.floor_le _, Int.lt_floor_add_one _⟩
    have htc : (x.2.1 + c / 2) / c * c = x.2.1 + c / 2 := div_mul_cancel₀ _ hc.ne'
    have h1c : (m : ℝ) * c ≤ (x.2.1 + c / 2) / c * c := mul_le_mul_of_nonneg_right hm1 hc.le
    have h2c : (x.2.1 + c / 2) / c * c < (m : ℝ) * c + c := by
      have := mul_lt_mul_of_pos_right hm2 hc
      rw [add_mul, one_mul] at this
      exact this
    have hmem : (x.1, (x.2.1 + ((-m : ℤ) : ℝ) * c, x.2.2)) ∈
        Icc (-M - 1) (M + 1) ×ˢ (Icc (-c / 2) (c / 2) ×ˢ Icc (-M - 1) (M + 1)) := by
      have hA1 : -M - 1 ≤ x.1 := by linarith [(abs_le.mp hx.1).1]
      have hA2 : x.1 ≤ M + 1 := (abs_le.mp hx.1).2
      have hB1 : -M - 1 ≤ x.2.2 := by linarith [(abs_le.mp hx.2).1]
      have hB2 : x.2.2 ≤ M + 1 := (abs_le.mp hx.2).2
      push_cast
      refine ⟨⟨hA1, hA2⟩, ⟨⟨?_, ?_⟩, ⟨hB1, hB2⟩⟩⟩
      · linarith
      · linarith
    rw [← hsh (-m) x]
    exact le_trans (hC _ hmem) (le_max_left _ _)
  · have h0 : moPerz c h x = 0 := by
      apply hvan
      rcases not_and_or.mp hx with h' | h'
      · left; exact not_le.mp h'
      · right; exact not_le.mp h'
    rw [h0, norm_zero]
    exact le_max_right _ _

end UnforcedLeray.Short.IIb

end
