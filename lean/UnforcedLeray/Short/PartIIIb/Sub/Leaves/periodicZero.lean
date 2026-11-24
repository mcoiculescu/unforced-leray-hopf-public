import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1_1

/-!
# `periodicZero`: periodic zero lemma

Source `the November 2 reference manuscript` lines 1334-1337, 1351-1362, 1470-1480.
Compactly supported smooth tests in one period (periodized by `PhaseTrace.perT`) give
`F = 0` a.e. on `(0,P)`; the period shifts and a countable covering of `ℝ` then give `F = 0` a.e.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Almost-everywhere `P`-periodicity of `F` gives it for all integer multiples of `P`. -/
theorem ae_shift_int_of_period {P : ℝ} {F : ℝ → ℂ} (hper : ∀ᵐ t : ℝ, F (t + P) = F t)
    (k : ℤ) : ∀ᵐ t : ℝ, F (t + (k : ℝ) * P) = F t := by
  have hcomp : ∀ (c : ℝ) {p : ℝ → Prop}, (∀ᵐ u : ℝ, p u) → ∀ᵐ t : ℝ, p (t + c) :=
    fun c p h => (measurePreserving_add_right volume c).quasiMeasurePreserving.ae h
  refine Int.induction_on k ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun t => by simp
  · intro n ih
    have h2 := hcomp (((n : ℤ) : ℝ) * P) hper
    filter_upwards [ih, h2] with t h1 h3
    have e : t + (((n : ℤ) + 1 : ℤ) : ℝ) * P = t + ((n : ℤ) : ℝ) * P + P := by push_cast; ring
    rw [e, h3, h1]
  · intro n ih
    have h1 := hcomp (-P) ih
    have h2 := hcomp (-P) hper
    filter_upwards [h1, h2] with t e1 e2
    have e3 : t + -P + P = t := by ring
    rw [e3] at e2
    have e4 : t + (((-(n : ℤ) - 1 : ℤ)) : ℝ) * P = t + -P + (((-(n : ℤ)) : ℤ) : ℝ) * P := by
      push_cast; ring
    rw [e4, e1, e2]



theorem periodicZero : PeriodicZero := by
  intro P hP F hloc hper hyp
  -- Step 1: `F = 0` a.e. on `(0, P)`, by periodized smooth tests (Fubini-free unfolding)
  have hQ0 : ∀ᵐ x : ℝ, x ∈ Ioo (0 : ℝ) P → F x = 0 := by
    refine IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero isOpen_Ioo
      (hloc.locallyIntegrableOn _) ?_
    intro g hg hgc hgU
    set G : ℝ × Space → ℂ := fun p => ((g p.1 : ℝ) : ℂ) with hGdef
    have hGs : ContDiff ℝ ∞ G :=
      Complex.ofRealCLM.contDiff.comp (hg.comp contDiff_fst)
    have hTS : UnforcedLeray.PhaseTrace.TimeSupp 0 P G := by
      intro τ y hτ
      have hz : g τ = 0 := image_eq_zero_of_notMem_tsupport
        (fun ht => hτ (Ioo_subset_Icc_self (hgU ht)))
      simp [hGdef, hz]
    have hφs : ContDiff ℝ ∞ (fun t : ℝ => UnforcedLeray.PhaseTrace.perT P G (t, 0)) :=
      (UnforcedLeray.PhaseTrace.contDiff_perT hP hTS hGs).comp
        (contDiff_id.prodMk contDiff_const)
    have hφp : ∀ t : ℝ, (fun t : ℝ => UnforcedLeray.PhaseTrace.perT P G (t, 0)) (t + P)
        = (fun t : ℝ => UnforcedLeray.PhaseTrace.perT P G (t, 0)) t :=
      fun t => UnforcedLeray.PhaseTrace.perT_periodic P G t 0
    have hI := hyp _ hφs hφp
    have hpt : ∀ x ∈ Ioc (0 : ℝ) P,
        UnforcedLeray.PhaseTrace.perT P G (x, 0) = ((g x : ℝ) : ℂ) := by
      intro x hx
      unfold UnforcedLeray.PhaseTrace.perT
      rw [finsum_eq_single (fun k : ℤ => G (x + (k : ℝ) * P, 0)) 0 ?_]
      · simp [hGdef]
      · intro k hk
        have hnot : x + (k : ℝ) * P ∉ tsupport g := fun ht => by
          obtain ⟨h1, h2⟩ := hgU ht
          obtain ⟨hx1, hx2⟩ := hx
          rcases lt_or_gt_of_ne hk with hk1 | hk1
          · have hk' : (k : ℝ) ≤ -1 := by exact_mod_cast (by omega : k ≤ -1)
            nlinarith [mul_le_mul_of_nonneg_right hk' hP.le]
          · have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : (1 : ℤ) ≤ k)
            nlinarith [mul_le_mul_of_nonneg_right hk' hP.le]
        simp only [hGdef]
        rw [image_eq_zero_of_notMem_tsupport hnot]
        simp
    have hrhs : ∫ x in Ioc (0 : ℝ) P, ((g x : ℝ) : ℂ) * F x = 0 := by
      rw [← hI]
      refine setIntegral_congr_fun measurableSet_Ioc ?_
      intro x hx
      show ((g x : ℝ) : ℂ) * F x = UnforcedLeray.PhaseTrace.perT P G (x, 0) * F x
      rw [hpt x hx]
    have hint : ∫ x, g x • F x = ∫ x in Ioc (0 : ℝ) P, ((g x : ℝ) : ℂ) * F x := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (f := fun x => g x • F x) ?_]
      · refine setIntegral_congr_fun measurableSet_Ioc (fun x _ => ?_)
        show g x • F x = ((g x : ℝ) : ℂ) * F x
        rw [Complex.real_smul]
      · intro x hx
        have hz : g x = 0 := image_eq_zero_of_notMem_tsupport
          (fun ht => hx (Ioo_subset_Ioc_self (hgU ht)))
        simp [hz]
    rw [hint, hrhs]
  -- Step 2: the null set `W = {x ∈ (0,P]: F x ≠ 0}`
  have hW : volume {x : ℝ | x ∈ Ioc (0 : ℝ) P ∧ F x ≠ 0} = 0 := by
    have h1 : volume {x : ℝ | x ∈ Ioo (0 : ℝ) P ∧ F x ≠ 0} = 0 := by
      refine measure_mono_null ?_ (ae_iff.mp hQ0)
      intro x hx
      simp only [mem_setOf_eq] at hx ⊢
      intro h
      exact hx.2 (h hx.1)
    refine measure_mono_null (fun x hx => ?_) (measure_union_null h1 (measure_singleton P))
    by_cases hxP : x = P
    · exact Or.inr (by simp [hxP])
    · exact Or.inl ⟨⟨hx.1.1, lt_of_le_of_ne hx.1.2 hxP⟩, hx.2⟩
  -- Step 3: covering by the translates of the null sets
  have hcover : {t : ℝ | F t ≠ 0} ⊆ ⋃ k : ℤ,
      ((fun t : ℝ => t + -((k : ℝ) * P)) ⁻¹' {r : ℝ | F (r + (k : ℝ) * P) ≠ F r}
        ∪ (fun t : ℝ => t + -((k : ℝ) * P)) ⁻¹' {x : ℝ | x ∈ Ioc (0 : ℝ) P ∧ F x ≠ 0}) := by
    intro t ht
    simp only [mem_setOf_eq] at ht
    have hx1 : t / P ≤ ((⌈t / P⌉ : ℤ) : ℝ) := Int.le_ceil _
    have hx2 : ((⌈t / P⌉ : ℤ) : ℝ) < t / P + 1 := Int.ceil_lt_add_one _
    have hkcast : (((⌈t / P⌉ - 1 : ℤ)) : ℝ) = ((⌈t / P⌉ : ℤ) : ℝ) - 1 := by push_cast; ring
    have key : t + -((((⌈t / P⌉ - 1 : ℤ)) : ℝ) * P) = P * (t / P - ((⌈t / P⌉ : ℤ) : ℝ) + 1) := by
      rw [hkcast]; field_simp; ring
    have hr0 : 0 < t + -((((⌈t / P⌉ - 1 : ℤ)) : ℝ) * P) := by
      rw [key]; exact mul_pos hP (by linarith)
    have hrP : t + -((((⌈t / P⌉ - 1 : ℤ)) : ℝ) * P) ≤ P := by
      rw [key]; nlinarith
    have hrt : t + -((((⌈t / P⌉ - 1 : ℤ)) : ℝ) * P) + (((⌈t / P⌉ - 1 : ℤ)) : ℝ) * P = t := by ring
    refine Set.mem_iUnion.mpr ⟨⌈t / P⌉ - 1, ?_⟩
    by_cases hF : F (t + -((((⌈t / P⌉ - 1 : ℤ)) : ℝ) * P) + (((⌈t / P⌉ - 1 : ℤ)) : ℝ) * P)
        = F (t + -((((⌈t / P⌉ - 1 : ℤ)) : ℝ) * P))
    · refine Or.inr ?_
      show t + -((((⌈t / P⌉ - 1 : ℤ)) : ℝ) * P) ∈ {x : ℝ | x ∈ Ioc (0 : ℝ) P ∧ F x ≠ 0}
      refine ⟨⟨hr0, hrP⟩, ?_⟩
      rw [hrt] at hF
      rw [← hF]
      exact ht
    · refine Or.inl ?_
      show t + -((((⌈t / P⌉ - 1 : ℤ)) : ℝ) * P) ∈ {r : ℝ | F (r + (((⌈t / P⌉ - 1 : ℤ)) : ℝ) * P) ≠ F r}
      exact hF
  -- Step 4: conclude
  have hnull : volume {t : ℝ | F t ≠ 0} = 0 := by
    refine measure_mono_null hcover ?_
    refine measure_iUnion_null fun k => measure_union_null ?_ ?_
    · rw [measure_preimage_add_right]
      exact ae_iff.mp (ae_shift_int_of_period hper k)
    · rw [measure_preimage_add_right]
      exact hW
  refine ae_iff.mpr ?_
  simpa using hnull

end UnforcedLeray.Short.PartIIIb.Concrete
