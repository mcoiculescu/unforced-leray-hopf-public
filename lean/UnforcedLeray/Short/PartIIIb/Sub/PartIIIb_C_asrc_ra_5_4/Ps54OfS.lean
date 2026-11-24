import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4

/-!
# `PartIII-b:C/asrc/ra/5/4` task 3 : a function of `s` alone is in `PS54`

Source of record: `the November 2 reference manuscript` lines 4963-4981, 4978.
For `g(s, x) = h(s)` with `h` of class `C^n` on `s > 0`: the derivative of order `m ≤ n` of
`h ∘ fst` at `(s, x)` is the derivative of `h` at `s` composed with the projection `fst`, whose
norm is at most one.  The derivatives of `h` of order `≤ n` are bounded on the compact slab
`[s₀, s₁] ⊆ (0, ∞)`, giving the polynomial bound with `N = 0`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem ps54_of_s {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) (h : ℝ → E) (hh : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) h (Ioi (0 : ℝ))) : PS54 n (fun p : ℝ × (ℝ × ℝ) => h p.1) := by
  have hT : IsOpen ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) ⁻¹' Ioi (0 : ℝ)) :=
    isOpen_Ioi.preimage (ContinuousLinearMap.continuous _)
  have hU : UniqueDiffOn ℝ (Ioi (0 : ℝ)) := isOpen_Ioi.uniqueDiffOn
  have hUT : UniqueDiffOn ℝ ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) ⁻¹' Ioi (0 : ℝ)) := hT.uniqueDiffOn
  refine ⟨hh.comp contDiff_fst.contDiffOn (fun p hp => hp.1), ?_⟩
  intro s0 s1 hs0 hs01
  have hb : ∀ m : ℕ, ∃ Cm : ℝ, 0 ≤ Cm ∧ (m ≤ n → ∀ s ∈ Icc s0 s1, ‖iteratedFDeriv ℝ m h s‖ ≤ Cm) := by
    intro m
    by_cases hm : m ≤ n
    · have hc : ContinuousOn (iteratedFDeriv ℝ m h) (Icc s0 s1) :=
        (ContinuousOn.continuousOn_iteratedFDeriv hh isOpen_Ioi (by exact_mod_cast hm)).mono
          (fun s hs => lt_of_lt_of_le hs0 hs.1)
      obtain ⟨C, hC⟩ := (isCompact_Icc.image_of_continuousOn hc.norm).bddAbove
      have hC' : ∀ s ∈ Icc s0 s1, ‖iteratedFDeriv ℝ m h s‖ ≤ C := fun s hs =>
        hC (Set.mem_image_of_mem _ hs)
      exact ⟨max C 0, le_max_right _ _, fun _ s hs => (hC' s hs).trans (le_max_left _ _)⟩
    · exact ⟨0, le_rfl, fun h' => absurd h' hm⟩
  choose Cm hCm0 hCm using hb
  refine ⟨∑ m ∈ Finset.range (n + 1), Cm m, 0, Finset.sum_nonneg (fun m _ => hCm0 m), ?_⟩
  intro m hm s hs x
  have hsp : 0 < s := lt_of_lt_of_le hs0 hs.1
  have hmemT : (s, x) ∈ (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) ⁻¹' Ioi (0 : ℝ) := hsp
  have hmemU : (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) (s, x) ∈ Ioi (0 : ℝ) := hsp
  have hcomp := ContinuousLinearMap.iteratedFDerivWithin_comp_right
    (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) hh hU hUT hmemU (i := m) (by exact_mod_cast hm)
  have e0 : iteratedFDeriv ℝ m (fun p : ℝ × (ℝ × ℝ) => h p.1) (s, x) =
      iteratedFDerivWithin ℝ m (h ∘ ⇑(ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)))
        ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) ⁻¹' Ioi (0 : ℝ)) (s, x) :=
    (iteratedFDerivWithin_of_isOpen (f := fun p : ℝ × (ℝ × ℝ) => h p.1) m hT hmemT).symm
  have e1 : iteratedFDerivWithin ℝ m h (Ioi (0 : ℝ)) (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) (s, x))
      = iteratedFDeriv ℝ m h s :=
    iteratedFDerivWithin_of_isOpen (f := h) m isOpen_Ioi hsp
  rw [e0, hcomp, e1]
  have hn : ‖(iteratedFDeriv ℝ m h s).compContinuousLinearMap (fun _ => ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))‖
      ≤ ‖iteratedFDeriv ℝ m h s‖ := by
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have hp : ∏ _i : Fin m, ‖ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)‖ ≤ 1 :=
      Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => ContinuousLinearMap.norm_fst_le ℝ ℝ (ℝ × ℝ))
    nlinarith [norm_nonneg (iteratedFDeriv ℝ m h s)]
  refine hn.trans ?_
  rw [pow_zero, mul_one]
  have hle : ‖iteratedFDeriv ℝ m h s‖ ≤ Cm m := hCm m hm s hs
  exact hle.trans (Finset.single_le_sum (f := Cm) (fun k _ => hCm0 k) (Finset.mem_range.2 (by omega)))

end UnforcedLeray.Short.PartIIIb.Concrete
