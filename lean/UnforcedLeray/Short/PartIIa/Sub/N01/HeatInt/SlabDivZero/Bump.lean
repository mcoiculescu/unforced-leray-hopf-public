import UnforcedLeray.Units.B0226.Defs

/-!
# `PartII-a:N01/9/1/2/4/1/a`: a periodic bump test with prescribed cell values

Source `the November 2 reference manuscript`
lines 1650-1658, 1684-1689, 3379-3383, 3426-3430.  A smooth compactly supported `G` on the
profile space whose support lies in the cell box `s > 0`, `0 < q < c` is extended to a
`c`-periodic test `Φ` (a `ProfileTest c`) with `Φ = G` on the box.  The extension is the
`q`-periodization `Φ(s,q,η) = ∑_{k∈ℤ} G(s, q + k c, η)`, which is a finite sum locally, since
`G` has compact support.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.B0220 (Profile QPeriodic)
open UnforcedLeray.B0226 (IsProfileTest ProfileTest)

/-- The `q`-periodization `∑_{k∈ℤ} G(s, q + k c, η)` (finitely many nonzero terms). -/
def periodQ (c : ℝ) (G : Profile → ℝ) (p : Profile) : ℝ :=
  ∑ᶠ k : ℤ, G (p.1, p.2.1 + (k : ℝ) * c, p.2.2)

theorem contDiff_shiftQ (c : ℝ) (k : ℤ) :
    ContDiff ℝ ∞ (fun p : Profile => (p.1, p.2.1 + (k : ℝ) * c, p.2.2)) := by
  fun_prop

theorem periodQ_periodic {c : ℝ} (G : Profile → ℝ) (p : Profile) :
    periodQ c G (p.1, p.2.1 + c, p.2.2) = periodQ c G p := by
  show (∑ᶠ k : ℤ, G (p.1, (p.2.1 + c) + (k : ℝ) * c, p.2.2)) = ∑ᶠ k : ℤ, G (p.1, p.2.1 + (k : ℝ) * c, p.2.2)
  calc ∑ᶠ k : ℤ, G (p.1, (p.2.1 + c) + (k : ℝ) * c, p.2.2)
      = ∑ᶠ k : ℤ, G (p.1, p.2.1 + (((Equiv.addRight (1 : ℤ) k : ℤ)) : ℝ) * c, p.2.2) :=
        finsum_congr fun k => by
          rw [show (p.2.1 + c) + (k : ℝ) * c = p.2.1 + (((Equiv.addRight (1 : ℤ) k : ℤ)) : ℝ) * c by
            simp only [Equiv.coe_addRight]; push_cast; ring]
    _ = ∑ᶠ k : ℤ, G (p.1, p.2.1 + (k : ℝ) * c, p.2.2) :=
        finsum_comp_equiv (Equiv.addRight (1 : ℤ))
          (f := fun k : ℤ => G (p.1, p.2.1 + (k : ℝ) * c, p.2.2))

theorem periodQ_smooth {c : ℝ} (hc : 0 < c) (G : Profile → ℝ) (hG : ContDiff ℝ ∞ G)
    {C : ℝ} (hC : ∀ x ∈ tsupport G, ‖x.2.1‖ ≤ C) :
    ContDiff ℝ ∞ (periodQ c G) := by
  rw [contDiff_iff_contDiffAt]
  intro p0
  have hU : ∀ᶠ p in 𝓝 p0, p.2.1 ∈ Ioo (p0.2.1 - 1) (p0.2.1 + 1) := by
    have hq : Continuous (fun p : Profile => p.2.1) := continuous_fst.comp continuous_snd
    exact hq.continuousAt.eventually_mem
      (Ioo_mem_nhds (by show p0.2.1 - 1 < p0.2.1; linarith) (by show p0.2.1 < p0.2.1 + 1; linarith))
  have hEq : periodQ c G =ᶠ[𝓝 p0] fun p : Profile =>
      ∑ k ∈ Finset.Icc ⌈(-C - p0.2.1 - 1) / c⌉ ⌊(C - p0.2.1 + 1) / c⌋,
        G (p.1, p.2.1 + (k : ℝ) * c, p.2.2) := by
    filter_upwards [hU] with p hp
    unfold periodQ
    apply finsum_eq_sum_of_support_subset
    intro k hk
    have hk' : G (p.1, p.2.1 + (k : ℝ) * c, p.2.2) ≠ 0 := hk
    have hmem : (p.1, p.2.1 + (k : ℝ) * c, p.2.2) ∈ tsupport G :=
      subset_tsupport G (Function.mem_support.mpr hk')
    have hb := hC _ hmem
    rw [Real.norm_eq_abs, abs_le] at hb
    obtain ⟨hb1, hb2⟩ := hb
    dsimp only at hb1 hb2
    have hp1 := hp.1
    have hp2 := hp.2
    simp only [Finset.mem_coe, Finset.mem_Icc]
    constructor
    · apply Int.ceil_le.mpr
      rw [div_le_iff₀ hc]
      linarith
    · apply Int.le_floor.mpr
      rw [le_div_iff₀ hc]
      linarith
  have hsum : ContDiff ℝ ∞ (fun p : Profile => ∑ k ∈ Finset.Icc ⌈(-C - p0.2.1 - 1) / c⌉
      ⌊(C - p0.2.1 + 1) / c⌋, G (p.1, p.2.1 + (k : ℝ) * c, p.2.2)) :=
    ContDiff.sum fun k _ => hG.comp (contDiff_shiftQ c k)
  exact hsum.contDiffAt.congr_of_eventuallyEq hEq

/-- **(S6)** The periodic bump: a smooth compactly supported cell function extends to a
`c`-periodic profile test which agrees with it on the cell box. -/
theorem periodicBumpTest (c : ℝ) (hc : 0 < c) (G : UnforcedLeray.B0220.Profile → ℝ) (hG : ContDiff ℝ ∞ G) (hcs : HasCompactSupport G) (hsub : tsupport G ⊆ (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) c ×ˢ (Set.univ : Set ℝ)))) : ∃ Φ : UnforcedLeray.B0226.ProfileTest c, ∀ p ∈ (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) c ×ˢ (Set.univ : Set ℝ))), Φ.1 p = G p := by
  have hK : IsCompact (tsupport G) := hcs.isCompact
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (f := fun x : Profile => x.2.1) (continuous_fst.comp continuous_snd).continuousOn
  obtain ⟨Lb, hLb⟩ := hK.exists_bound_of_continuousOn
    (f := fun x : Profile => x.2.2) (continuous_snd.comp continuous_snd).continuousOn
  obtain ⟨Cs, hCs⟩ := hK.exists_bound_of_continuousOn
    (f := fun x : Profile => x.1) continuous_fst.continuousOn
  have hpos : ∀ x ∈ tsupport G, 0 < x.1 := fun x hx => (hsub hx).1
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    (f := fun x : Profile => x.1⁻¹)
    (continuous_fst.continuousOn.inv₀ fun x hx => (hpos x hx).ne')
  set Mb : ℝ := |M| + 1 with hMb_def
  have hMb : 0 < Mb := by positivity
  have hs0 : 0 < 1 / Mb := by positivity
  have key : ∀ p : Profile, periodQ c G p ≠ 0 →
      ∃ k : ℤ, (p.1, p.2.1 + (k : ℝ) * c, p.2.2) ∈ tsupport G := by
    intro p hp
    by_contra h
    push Not at h
    apply hp
    unfold periodQ
    apply finsum_eq_zero_of_forall_eq_zero
    intro k
    by_contra hne
    exact h k (subset_tsupport G hne)
  refine ⟨⟨periodQ c G, ⟨periodQ_smooth hc G hG hC, fun p => periodQ_periodic (c := c) G p, ?_⟩⟩, ?_⟩
  · refine ⟨1 / Mb, Cs, Lb, hs0, fun p hp => ?_⟩
    obtain ⟨k, hk⟩ := key p hp
    have h1 : ‖(p.1)⁻¹‖ ≤ M := hM (p.1, p.2.1 + (k : ℝ) * c, p.2.2) hk
    have h2 : ‖p.1‖ ≤ Cs := hCs (p.1, p.2.1 + (k : ℝ) * c, p.2.2) hk
    have h3 : ‖p.2.2‖ ≤ Lb := hLb (p.1, p.2.1 + (k : ℝ) * c, p.2.2) hk
    have hxpos : 0 < p.1 := hpos (p.1, p.2.1 + (k : ℝ) * c, p.2.2) hk
    rw [Real.norm_eq_abs] at h1 h2 h3
    have hinv : (p.1)⁻¹ ≤ Mb := by
      have := le_abs_self ((p.1)⁻¹)
      have := le_abs_self M
      linarith
    have hlow : 1 / Mb ≤ p.1 := by
      rw [div_le_iff₀ hMb]
      have e : p.1 * (p.1)⁻¹ = 1 := mul_inv_cancel₀ hxpos.ne'
      have := mul_le_mul_of_nonneg_left hinv hxpos.le
      linarith
    have hup : p.1 ≤ Cs := le_trans (le_abs_self _) h2
    exact ⟨⟨hlow, hup⟩, h3⟩
  · intro p hp
    have hq0 : 0 < p.2.1 := hp.2.1.1
    have hqc : p.2.1 < c := hp.2.1.2
    show periodQ c G p = G p
    unfold periodQ
    rw [finsum_eq_single _ 0]
    · simp
    · intro k hk
      by_contra hne
      have hmem := hsub (subset_tsupport G hne)
      have hq1 : 0 < p.2.1 + (k : ℝ) * c := hmem.2.1.1
      have hq2 : p.2.1 + (k : ℝ) * c < c := hmem.2.1.2
      rcases lt_or_gt_of_ne hk with h | h
      · have hk1 : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
        nlinarith
      · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
        nlinarith

end UnforcedLeray.Short.PartIIa.N01
