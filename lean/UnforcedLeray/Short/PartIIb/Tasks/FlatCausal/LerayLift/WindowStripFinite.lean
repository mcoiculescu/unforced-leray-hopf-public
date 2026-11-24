import UnforcedLeray.Short.PartIIb.Sub.T12_2_5

/-!
# Part II-b, task `PartII-b:T12/2/5/4` (`WindowStripFinite`)

Source of record: `the November 2 reference manuscript`, lines 1901-1903 (`H_r`) and
1923-1926 (`P_0` at each age). Target: `LerayLiftSub.WindowStripFinite` (`Sub/T12_2_5.lean`).

Proof: a `q`-translate by `n c` (`n : ℤ`) preserves Lebesgue measure and, by integer periodicity of
`G`, the integrand `‖G‖ₑ^r`. Hence each translate of the window `[a,b] × cell c` carries the same
integral. The strip `[a,b] × [-Q,Q] × ℝ` is covered by finitely many such translates
(`n = ⌊(q + c/2)/c⌋`), and the sub-additivity of the lower Lebesgue integral gives the bound.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

/-- The translation `q ↦ q + t` on the chart `(s, (q, η))` preserves Lebesgue measure. -/
private lemma coord_shift_mp (t : ℝ) :
    MeasurePreserving (fun x : Coord => (x.1, (x.2.1 + t, x.2.2))) volume volume := by
  have h1 : MeasurePreserving (fun z : ℝ × ℝ => (z.1 + t, z.2)) volume volume :=
    UnforcedLeray.Cyl.measurePreserving_shift t
  exact (MeasurePreserving.id (volume : Measure ℝ)).prod h1

/-- Integer translates in `q` of a `c`-periodic profile are equal to the profile. -/
private lemma G_int_periodic (c : ℝ) (G : CProf)
    (hG : ∀ (s : ℝ) (z : ℝ × ℝ), G (s, (z.1 + c, z.2)) = G (s, z)) (n : ℤ) (x : Coord) :
    G (x.1, (x.2.1 + (n : ℝ) * c, x.2.2)) = G x := by
  have hP : UnforcedLeray.Cyl.IsPeriodic c (fun z : ℝ × ℝ => G (x.1, z)) := fun z => hG x.1 z
  have h := hP.add_int_mul n x.2
  simpa using h

/-- Each integer `q`-translate of the window has the same integral as the cell window. -/
private lemma window_shift (c r : ℝ) (G : CProf) (hmeas : StronglyMeasurable G)
    (hG : ∀ (s : ℝ) (z : ℝ × ℝ), G (s, (z.1 + c, z.2)) = G (s, z)) (a b : ℝ) (n : ℤ) :
    ∫⁻ x in Icc a b ×ˢ (Ico (-c / 2 + n * c) (c / 2 + n * c) ×ˢ (univ : Set ℝ)), ‖G x‖ₑ ^ r
      = ∫⁻ x in Icc a b ×ˢ UnforcedLeray.Cyl.cell c, ‖G x‖ₑ ^ r := by
  have hf : Measurable (fun x : Coord => ‖G x‖ₑ ^ r) := hmeas.measurable.enorm.pow_const r
  have hMP := coord_shift_mp (((-n : ℤ) : ℝ) * c)
  have hcell : MeasurableSet (Icc a b ×ˢ UnforcedLeray.Cyl.cell c) :=
    measurableSet_Icc.prod (measurableSet_Ico.prod MeasurableSet.univ)
  have hpre : (fun x : Coord => (x.1, (x.2.1 + ((-n : ℤ) : ℝ) * c, x.2.2))) ⁻¹'
      (Icc a b ×ˢ UnforcedLeray.Cyl.cell c)
      = Icc a b ×ˢ (Ico (-c / 2 + n * c) (c / 2 + n * c) ×ˢ (univ : Set ℝ)) := by
    ext x
    simp only [mem_preimage, mem_prod, mem_Ico, mem_univ, and_true, UnforcedLeray.Cyl.cell]
    apply and_congr_right
    intro _
    push_cast
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have key := hMP.setLIntegral_comp_preimage hcell hf
  rw [hpre] at key
  simp only [G_int_periodic c G hG (-n)] at key
  exact key

theorem windowStripFinite_proof : UnforcedLeray.Short.IIb.LerayLiftSub.WindowStripFinite := by
  intro c r G hc hmeas hG a b hfin Q
  obtain ⟨N, hN⟩ := exists_nat_gt ((|Q| + c) / c)
  have hNc : |Q| + c < (N : ℝ) * c := (div_lt_iff₀ hc).1 hN
  have hsub : Icc a b ×ˢ (Icc (-Q) Q ×ˢ (univ : Set ℝ)) ⊆
      ⋃ i : ↥(Finset.Icc (-(N : ℤ)) (N : ℤ)),
        Icc a b ×ˢ (Ico (-c / 2 + (i : ℤ) * c) (c / 2 + (i : ℤ) * c) ×ˢ (univ : Set ℝ)) := by
    intro x hx
    obtain ⟨hs, hq⟩ := hx
    obtain ⟨hq, -⟩ := hq
    obtain ⟨hq1, hq2⟩ := hq
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t * c = x.2.1 + c / 2 := ⟨(x.2.1 + c / 2) / c, div_mul_cancel₀ _ hc.ne'⟩
    have hqa : x.2.1 ≤ |Q| := le_trans hq2 (le_abs_self Q)
    have hqb : -|Q| ≤ x.2.1 := le_trans (neg_le_neg (le_abs_self Q)) hq1
    have htN : t < N := by
      have h : t * c < (N : ℝ) * c := by rw [ht]; linarith
      exact lt_of_mul_lt_mul_right h hc.le
    have htN' : -(N : ℝ) < t := by
      have h : -(N : ℝ) * c < t * c := by rw [ht]; linarith
      exact lt_of_mul_lt_mul_right h hc.le
    have hfl1 : ((⌊t⌋ : ℤ) : ℝ) ≤ t := Int.floor_le t
    have hfl2 : t < ((⌊t⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one t
    have hnN : ⌊t⌋ ≤ (N : ℤ) := by
      have h : ((⌊t⌋ : ℤ) : ℝ) < (N : ℝ) := lt_of_le_of_lt hfl1 htN
      have h' : ⌊t⌋ < (N : ℤ) := by exact_mod_cast h
      omega
    have hNn : -(N : ℤ) ≤ ⌊t⌋ := by
      have h' : ((-(N : ℤ) - 1 : ℤ) : ℝ) < ((⌊t⌋ : ℤ) : ℝ) := by push_cast; linarith
      have h'' : (-(N : ℤ) - 1) < ⌊t⌋ := by exact_mod_cast h'
      omega
    have hA : ((⌊t⌋ : ℤ) : ℝ) * c ≤ t * c := mul_le_mul_of_nonneg_right hfl1 hc.le
    have hB : t * c < (((⌊t⌋ : ℤ) : ℝ) + 1) * c := mul_lt_mul_of_pos_right hfl2 hc
    refine Set.mem_iUnion.2 ⟨⟨⌊t⌋, Finset.mem_Icc.2 ⟨hNn, hnN⟩⟩, ?_⟩
    dsimp only
    exact ⟨hs, ⟨by linarith, by linarith⟩, trivial⟩
  refine lt_of_le_of_lt (lintegral_mono_set hsub) ?_
  refine lt_of_le_of_lt (lintegral_iUnion_le _ _) ?_
  rw [tsum_fintype]
  refine ENNReal.sum_lt_top.2 (fun i _ => ?_)
  rw [window_shift c r G hmeas hG a b i.1]
  exact hfin

end UnforcedLeray.Short.IIb
