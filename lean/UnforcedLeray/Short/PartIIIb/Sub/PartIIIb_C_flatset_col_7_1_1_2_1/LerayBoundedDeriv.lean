import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayDefs

/-!
# `BoundedDerivBand` (task `PartIII-b:C/flatset/col/7/1/1/2/1/org2/leray/11`)

A smooth chart function, `c`-periodic in `q`, supported in a compact `(s, η)` band, has all
iterated derivatives bounded.  Route: the iterated derivative is `q`-periodic (shift by integer
multiples of the period), so the sup is attained on the compact box `[s₀,s₁] × [0,c] × [-L,L]`;
outside the band the function vanishes near the point, so its derivatives vanish there.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- Iterated derivatives of a `q`-periodic smooth chart function are invariant under integer
shifts of the `q`-variable. -/
theorem iteratedFDeriv_shift_period {c : ℝ} {f : Chart → ℝ}
    (hper : ∀ s q η, f (s, (q + c, η)) = f (s, (q, η))) (m : ℤ) (n : ℕ) (x : Chart) :
    iteratedFDeriv ℝ n f (x + (0, ((m : ℝ) * c, (0 : ℝ)))) = iteratedFDeriv ℝ n f x := by
  have hfun : (fun z : Chart => f (z + (0, ((m : ℝ) * c, (0 : ℝ))))) = f := by
    funext z
    obtain ⟨s, q, η⟩ := z
    have hq : Function.Periodic (fun q : ℝ => f (s, (q, η))) c := fun q => hper s q η
    have h := hq.int_mul m q
    simp only [Prod.mk_add_mk, add_zero]
    exact h
  have h := iteratedFDeriv_comp_add_right (𝕜 := ℝ) n (0, ((m : ℝ) * c, (0 : ℝ))) x (f := f)
  rw [hfun] at h
  exact h.symm

/-- The bounded-derivative leaf. -/
theorem boundedDerivBand : BoundedDerivBand := by
  intro c hc f hf hper hband n
  obtain ⟨s0, s1, L, hsupp⟩ := hband
  have hKc : IsCompact (Icc s0 s1 ×ˢ (Icc 0 c ×ˢ Icc (-L) L)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hcont : Continuous fun x => iteratedFDeriv ℝ n f x :=
    hf.continuous_iteratedFDeriv (by simp)
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C 0, fun p => ?_⟩
  set m : ℤ := ⌊p.2.1 / c⌋ with hm
  set p' : Chart := (p.1, (p.2.1 - (m : ℝ) * c, p.2.2)) with hp'
  have hpp : p' + (0, ((m : ℝ) * c, (0 : ℝ))) = p := by
    simp only [hp', Prod.mk_add_mk, add_zero]
    ext <;> simp
  have hshift : iteratedFDeriv ℝ n f p = iteratedFDeriv ℝ n f p' := by
    rw [← hpp, iteratedFDeriv_shift_period hper m n p']
  have h1 : (m : ℝ) ≤ p.2.1 / c := Int.floor_le _
  have h2 : p.2.1 / c < (m : ℝ) + 1 := Int.lt_floor_add_one _
  have h1' : (m : ℝ) * c ≤ p.2.1 := (le_div_iff₀ hc).mp h1
  have h2' : p.2.1 < ((m : ℝ) + 1) * c := (div_lt_iff₀ hc).mp h2
  rw [hshift]
  by_cases hin : p'.1 ∈ Icc s0 s1 ∧ |p'.2.2| ≤ L
  · have hmem : p' ∈ Icc s0 s1 ×ˢ (Icc 0 c ×ˢ Icc (-L) L) := by
      refine ⟨hin.1, ⟨?_, ?_⟩, abs_le.mp hin.2⟩
      · show 0 ≤ p.2.1 - (m : ℝ) * c
        linarith
      · show p.2.1 - (m : ℝ) * c ≤ c
        nlinarith
    exact le_trans (hC p' hmem) (le_max_left _ _)
  · have hclosed : IsClosed {x : Chart | x.1 ∈ Icc s0 s1 ∧ |x.2.2| ≤ L} :=
      (isClosed_Icc.preimage continuous_fst).inter
        (isClosed_le (continuous_abs.comp (continuous_snd.comp continuous_snd)) continuous_const)
    have hopen := hclosed.isOpen_compl
    have hzero : f =ᶠ[𝓝 p'] fun _ => (0 : ℝ) := by
      filter_upwards [hopen.mem_nhds hin] with x hx
      by_contra hne
      exact hx (hsupp x hne)
    have hz := (hzero.iteratedFDeriv ℝ n).eq_of_nhds
    rw [hz]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [iteratedFDeriv_const_of_ne (Nat.pos_iff_ne_zero.mp hn)]
      simp

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
