import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_6

/-!
# `PeriodizeIsTensorTest` (source 1678, `the November 2 reference manuscript`)

The `q`-periodization of a smooth band-supported function with `q`-support in `(a, b) ⊂ (0, c)`
is a tensor test.  Smoothness: at a point `(s, q, η)` either `q ∉ cℤ` (then near the point the
periodization is a translate of `g` in `q`), or `q = m c` (then the periodization vanishes on a
neighbourhood, since `reduceIoc c` of points within `δ = min a (c - b)` of `cℤ` avoids `(a, b)`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.B0220

theorem periodizeIsTensorTest : PeriodizeIsTensorTest := by
  intro c hc g hg hband hq
  obtain ⟨s0, s1, L, hs0, hL⟩ := hband
  obtain ⟨a, b, ha, hab, hbc, hqb⟩ := hq
  have hper : Function.Periodic (reduceIoc c) c := fun q => reduceIoc_add hc q
  have hδ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ a ∧ δ ≤ c - b :=
    ⟨min a (c - b), lt_min ha (by linarith), min_le_left _ _, min_le_right _ _⟩
  obtain ⟨δ, hδpos, hδa, hδc⟩ := hδ
  have hsmooth : ContDiff ℝ ∞ (periodize c g) := by
    refine contDiff_iff_contDiffAt.2 fun p => ?_
    obtain ⟨s, q, η⟩ := p
    by_cases hm : ∃ m : ℤ, q = (m : ℝ) * c
    · -- case (ii): `q ∈ cℤ`, the periodization vanishes near `q`
      obtain ⟨m, rfl⟩ := hm
      have hzero : ∀ x : Profile, -δ < x.2.1 - (m : ℝ) * c → x.2.1 - (m : ℝ) * c < δ →
          periodize c g x = 0 := by
        intro x hx1 hx2
        have hnot : reduceIoc c (x.2.1 - (m : ℝ) * c) ∉ Ioo a b := by
          rcases lt_or_ge 0 (x.2.1 - (m : ℝ) * c) with hy0 | hy0
          · have hz : reduceIoc c (x.2.1 - (m : ℝ) * c) = x.2.1 - (m : ℝ) * c :=
              reduceIoc_of_mem hc ⟨hy0, by linarith⟩
            rw [hz]
            intro h
            linarith [h.1]
          · have hz : reduceIoc c (x.2.1 - (m : ℝ) * c) = x.2.1 - (m : ℝ) * c + c := by
              rw [← reduceIoc_add hc (x.2.1 - (m : ℝ) * c)]
              exact reduceIoc_of_mem hc ⟨by linarith, by linarith⟩
            rw [hz]
            intro h
            linarith [h.2]
        have hsh : reduceIoc c x.2.1 = reduceIoc c (x.2.1 - (m : ℝ) * c) := by
          rw [hper.sub_int_mul_eq]
        show g (x.1, reduceIoc c x.2.1, x.2.2) = 0
        rw [hsh]
        by_contra hne
        exact hnot (hqb _ hne)
      have hf : Continuous (fun x : Profile => x.2.1 - (m : ℝ) * c) := by fun_prop
      have hopen : IsOpen {x : Profile | -δ < x.2.1 - (m : ℝ) * c ∧ x.2.1 - (m : ℝ) * c < δ} :=
        (isOpen_lt continuous_const hf).inter (isOpen_lt hf continuous_const)
      have hpmem : ((s, (m : ℝ) * c, η) : Profile) ∈
          {x : Profile | -δ < x.2.1 - (m : ℝ) * c ∧ x.2.1 - (m : ℝ) * c < δ} := by
        show -δ < (m : ℝ) * c - (m : ℝ) * c ∧ (m : ℝ) * c - (m : ℝ) * c < δ
        constructor <;> linarith
      have h0 : ContDiffAt ℝ ∞ (fun _ : Profile => (0 : UnforcedLeray.Short.PartIIa.TensorVal)) (s, (m : ℝ) * c, η) :=
        contDiffAt_const
      exact h0.congr_of_eventuallyEq (by
        filter_upwards [hopen.mem_nhds hpmem] with x hx
        exact hzero x hx.1 hx.2)
    · -- case (i): `q ∉ cℤ`, near `q` the periodization is a translate of `g`
      have hfl : ((⌊q / c⌋ : ℤ) : ℝ) ≤ q / c := Int.floor_le _
      have hlt : q / c < ((⌊q / c⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
      have hne : ((⌊q / c⌋ : ℤ) : ℝ) ≠ q / c := fun h =>
        hm ⟨⌊q / c⌋, by rw [eq_div_iff hc.ne'] at h; linarith⟩
      have hlt' : ((⌊q / c⌋ : ℤ) : ℝ) < q / c := lt_of_le_of_ne hfl hne
      obtain ⟨m, hm1, hm2⟩ : ∃ m : ℤ, (m : ℝ) * c < q ∧ q < ((m : ℝ) + 1) * c :=
        ⟨⌊q / c⌋, (lt_div_iff₀ hc).1 hlt', (div_lt_iff₀ hc).1 hlt⟩
      have hceil : ∀ x : ℝ, (m : ℝ) * c < x → x < ((m : ℝ) + 1) * c →
          reduceIoc c x = x - (m : ℝ) * c := by
        intro x h1 h2
        have hceq : ⌈x / c⌉ = m + 1 := by
          rw [Int.ceil_eq_iff]
          push_cast
          constructor
          · rw [lt_div_iff₀ hc]
            have e : ((m : ℝ) + 1 - 1) * c = (m : ℝ) * c := by ring
            linarith [h1, e]
          · rw [div_le_iff₀ hc]
            linarith [h2]
        unfold reduceIoc
        rw [hceq]
        push_cast
        ring
      have hc1 : Continuous (fun x : Profile => (m : ℝ) * c) := continuous_const
      have hc2 : Continuous (fun x : Profile => x.2.1) := by fun_prop
      have hc3 : Continuous (fun x : Profile => ((m : ℝ) + 1) * c) := continuous_const
      have hU : IsOpen {x : Profile | (m : ℝ) * c < x.2.1 ∧ x.2.1 < ((m : ℝ) + 1) * c} :=
        (isOpen_lt hc1 hc2).inter (isOpen_lt hc2 hc3)
      have hpU : ((s, q, η) : Profile) ∈
          {x : Profile | (m : ℝ) * c < x.2.1 ∧ x.2.1 < ((m : ℝ) + 1) * c} :=
        ⟨hm1, hm2⟩
      have hφ : ContDiff ℝ ∞ (fun x : Profile => (x.1, x.2.1 - (m : ℝ) * c, x.2.2)) := by
        fun_prop
      have hG : ContDiff ℝ ∞ (fun x : Profile => g (x.1, x.2.1 - (m : ℝ) * c, x.2.2)) :=
        hg.comp hφ
      refine hG.contDiffAt.congr_of_eventuallyEq ?_
      filter_upwards [hU.mem_nhds hpU] with x hx
      show g (x.1, reduceIoc c x.2.1, x.2.2) = g (x.1, x.2.1 - (m : ℝ) * c, x.2.2)
      rw [hceil x.2.1 hx.1 hx.2]
  refine ⟨hsmooth, qPeriodic_periodize hc g, ⟨s0, s1, L, hs0, fun p hp => hL (p.1, reduceIoc c p.2.1, p.2.2) hp⟩⟩

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
