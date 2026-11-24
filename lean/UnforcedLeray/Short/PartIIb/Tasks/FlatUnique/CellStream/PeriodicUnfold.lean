import UnforcedLeray.Short.PartIIb.Sub.T11_1

/-!
# Part II-b, leaf `PartII-b:T11/1/3`: periodic unfolding on the chart `Coord`

Target: `CoordPeriodicUnfold` (`Sub/T11_1.lean`). Source of record:
`the November 2 reference manuscript`, lines 1921-1938, where the periodization of
cutoffs over translates of the cell is used silently (the cylinder heat estimate "applying the
Euclidean estimate to a cutoff of `N` repeated cells").

Proof (translation argument; no everywhere-periodic representative is needed):

1. The strips `T_n = qShift(-n c)⁻¹' (univ ×ˢ cell c)` partition `Coord`, so
   `∫ F = Σ_n ∫_{T_n} F` for `F = h(q) G` (`integral_iUnion`).
2. Each strip integral is a translate of the cell integral (`measurePreserving_qShift`):
   `∫_{T_n} F = ∫_{univ × cell} F(qShift(n c) y) dy`.
3. `G(qShift(n c) y) = G y` for a.e. `y` (integer shifts of an a.e. periodicity), so the
   `n`-th piece equals `∫_{univ × cell} h(q + n c) G`.
4. `h` has compact support, so only a finite window `|n| ≤ N` meets the cell, and
   `Σ_n h(q + n c) = P` (the hypothesis, reindexed `n ↦ -n`) gives the total `P ∫_{univ×cell} G`.

Integrability: `G` is integrable on every box `[σ,H] × [-R,R] × [-L,L]`, `h` is bounded and
supported in `|q| ≤ A`, so `h G` is integrable on a box and vanishes off it. `G` is integrable on
`univ × cell` because it vanishes off `σ ≤ s ≤ H`, `|η| ≤ L`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Function

namespace UnforcedLeray.Short.IIb

/-! ## Measure-preserving `q`-shifts on `Coord` -/

/-- The shift `q ↦ q + s` preserves Lebesgue measure on `Coord`. -/
theorem puc_measurePreserving_qShift (s : ℝ) :
    MeasurePreserving (qShift s) (volume : Measure Coord) (volume : Measure Coord) := by
  have hA : MeasurePreserving (Prod.map (fun t : ℝ => t + s) (id : ℝ → ℝ))
      (volume : Measure (ℝ × ℝ)) (volume : Measure (ℝ × ℝ)) :=
    (measurePreserving_add_right volume s).prod (MeasurePreserving.id volume)
  have hB : MeasurePreserving (Prod.map (id : ℝ → ℝ) (Prod.map (fun t : ℝ => t + s) (id : ℝ → ℝ)))
      (volume : Measure Coord) (volume : Measure Coord) :=
    (MeasurePreserving.id volume).prod hA
  exact hB

theorem puc_measurable_qShift (s : ℝ) : Measurable (qShift s) :=
  measurable_fst.prodMk ((measurable_snd.fst.add_const s).prodMk measurable_snd.snd)

theorem puc_qShift_qShift (s t : ℝ) (x : Coord) : qShift s (qShift t x) = qShift (s + t) x := by
  show (x.1, ((x.2.1 + t) + s, x.2.2)) = (x.1, (x.2.1 + (s + t), x.2.2))
  rw [add_assoc, add_comm t s]

theorem puc_qShift_zero (x : Coord) : qShift 0 x = x := by
  simp [qShift]

theorem puc_qShift_inv (s : ℝ) (x : Coord) : qShift s (qShift (-s) x) = x := by
  have hz : s + -s = 0 := by ring
  rw [puc_qShift_qShift, hz, puc_qShift_zero]

theorem puc_qShift_neg_inv (s : ℝ) (x : Coord) : qShift (-s) (qShift s x) = x := by
  have hz : -s + s = 0 := by ring
  rw [puc_qShift_qShift, hz, puc_qShift_zero]

theorem puc_qShift_measurableEmbedding (m : ℝ) : MeasurableEmbedding (qShift m) := by
  refine MeasurableEmbedding.of_measurable_inverse (puc_measurable_qShift m) ?_
    (puc_measurable_qShift (-m)) (fun x => puc_qShift_neg_inv m x)
  have hr : Set.range (qShift m) = univ :=
    Set.range_eq_univ.2 (fun y => ⟨qShift (-m) y, puc_qShift_inv m y⟩)
  rw [hr]
  exact MeasurableSet.univ

/-- Change of variables for a set integral along a `q`-shift. -/
theorem puc_setIntegral_qShift (m : ℝ) (S : Set Coord) (F : Coord → ℂ) :
    ∫ x in qShift m ⁻¹' S, F x = ∫ y in S, F (qShift (-m) y) := by
  have h := (puc_measurePreserving_qShift m).setIntegral_preimage_emb
    (puc_qShift_measurableEmbedding m) (fun y => F (qShift (-m) y)) S
  simp only [puc_qShift_neg_inv] at h
  exact h

/-! ## Almost-everywhere integer shifts of `G : Coord → ℂ` -/

theorem puc_ae_shift_add {G : Coord → ℂ} {s t : ℝ} (hs : ∀ᵐ x : Coord, G (qShift s x) = G x)
    (ht : ∀ᵐ x : Coord, G (qShift t x) = G x) : ∀ᵐ x : Coord, G (qShift (s + t) x) = G x := by
  have h : ∀ᵐ x : Coord, G (qShift s (qShift t x)) = G (qShift t x) :=
    (puc_measurePreserving_qShift t).quasiMeasurePreserving.ae hs
  filter_upwards [h, ht] with x hx1 hx2
  rw [← puc_qShift_qShift]
  exact hx1.trans hx2

theorem puc_ae_shift_neg {G : Coord → ℂ} {s : ℝ} (hs : ∀ᵐ x : Coord, G (qShift s x) = G x) :
    ∀ᵐ x : Coord, G (qShift (-s) x) = G x := by
  have h : ∀ᵐ x : Coord, G (qShift s (qShift (-s) x)) = G (qShift (-s) x) :=
    (puc_measurePreserving_qShift (-s)).quasiMeasurePreserving.ae hs
  filter_upwards [h] with x hx
  rw [puc_qShift_inv] at hx
  exact hx.symm

theorem puc_ae_shift_int {G : Coord → ℂ} {c : ℝ} (hper : ∀ᵐ x : Coord, G (qShift c x) = G x)
    (k : ℤ) : ∀ᵐ x : Coord, G (qShift ((k : ℝ) * c) x) = G x := by
  refine Int.induction_on k ?_ ?_ ?_
  · filter_upwards with x
    simp [qShift]
  · intro n ih
    have e : ((((n : ℤ) + 1 : ℤ)) : ℝ) * c = ((n : ℤ) : ℝ) * c + c := by
      push_cast
      ring
    rw [e]
    exact puc_ae_shift_add ih hper
  · intro n ih
    have e : (((-(n : ℤ) - 1 : ℤ)) : ℝ) * c = ((-(n : ℤ) : ℤ) : ℝ) * c + -c := by
      push_cast
      ring
    rw [e]
    exact puc_ae_shift_add ih (puc_ae_shift_neg hper)

/-! ## The strips `T_n` -/

/-- The strip `T_n = {x | x.2.1 - n c ∈ [-c/2, c/2)}` (all `s` and all `η`). -/
def pucStrip (c : ℝ) (n : ℤ) : Set Coord :=
  qShift (-((n : ℝ) * c)) ⁻¹' (univ ×ˢ Cyl.cell c)

theorem puc_mem_strip_iff {c : ℝ} {n : ℤ} {x : Coord} :
    x ∈ pucStrip c n ↔ -c / 2 ≤ x.2.1 + -((n : ℝ) * c) ∧ x.2.1 + -((n : ℝ) * c) < c / 2 := by
  simp only [pucStrip, Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and, Cyl.mem_cell,
    qShift]

theorem puc_measurableSet_strip (c : ℝ) (n : ℤ) : MeasurableSet (pucStrip c n) :=
  puc_measurable_qShift _ (MeasurableSet.prod MeasurableSet.univ (Cyl.measurableSet_cell c))

theorem puc_pairwise_disjoint {c : ℝ} (hc : 0 < c) : Pairwise (Disjoint on pucStrip c) := by
  intro n m hnm
  show Disjoint (pucStrip c n) (pucStrip c m)
  rw [Set.disjoint_left]
  intro x hxn hxm
  obtain ⟨hn1, hn2⟩ := puc_mem_strip_iff.1 hxn
  obtain ⟨hm1, hm2⟩ := puc_mem_strip_iff.1 hxm
  have e : ((m : ℝ) - n) * c = (m : ℝ) * c - (n : ℝ) * c := by ring
  have h3 : ((m : ℝ) - n) < 1 :=
    lt_of_mul_lt_mul_right (by rw [e, one_mul]; linarith) hc.le
  have h4 : (-1 : ℝ) < (m : ℝ) - n :=
    lt_of_mul_lt_mul_right (by rw [e, neg_one_mul]; linarith) hc.le
  have h5 : m - n < 1 := by
    have : ((m - n : ℤ) : ℝ) < 1 := by push_cast; linarith
    exact_mod_cast this
  have h6 : -1 < m - n := by
    have : (-1 : ℝ) < ((m - n : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  exact hnm (by omega)

theorem puc_iUnion_strip {c : ℝ} (hc : 0 < c) : (⋃ n : ℤ, pucStrip c n) = univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  have h1 : ((⌊(x.2.1 + c / 2) / c⌋ : ℤ) : ℝ) ≤ (x.2.1 + c / 2) / c := Int.floor_le _
  have h2 : (x.2.1 + c / 2) / c < ((⌊(x.2.1 + c / 2) / c⌋ : ℤ) : ℝ) + 1 :=
    Int.lt_floor_add_one _
  rw [le_div_iff₀ hc] at h1
  rw [div_lt_iff₀ hc, add_mul, one_mul] at h2
  exact Set.mem_iUnion.2 ⟨⌊(x.2.1 + c / 2) / c⌋, puc_mem_strip_iff.2 ⟨by linarith, by linarith⟩⟩

/-- A strip integral is a cell integral of the translated integrand. -/
theorem puc_setIntegral_strip (F : Coord → ℂ) (c : ℝ) (n : ℤ) :
    ∫ x in pucStrip c n, F x = ∫ y in univ ×ˢ Cyl.cell c, F (qShift ((n : ℝ) * c) y) := by
  rw [pucStrip, puc_setIntegral_qShift, neg_neg]

/-- For `q` in the cell `[-c/2, c/2)` and `n` outside the window `[-N, N]`, the shifted point
`q + n c` lies outside `[-A, A]`. -/
theorem puc_big_shift {A c q : ℝ} {N n : ℤ} (hc : 0 < c) (hN : (A + c) / c < (N : ℝ))
    (hq1 : -c / 2 ≤ q) (hq2 : q < c / 2) (hn : n ∉ Finset.Icc (-N) N) :
    A < |q + (n : ℝ) * c| := by
  have hAc : A + c < (N : ℝ) * c := (div_lt_iff₀ hc).1 hN
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
  rcases hn with hn | hn
  · have hn' : (n : ℝ) < -(N : ℝ) := by exact_mod_cast hn
    have h3 : (n : ℝ) * c < -((N : ℝ) * c) := by
      have := mul_lt_mul_of_pos_right hn' hc
      rwa [neg_mul] at this
    exact lt_of_lt_of_le (by linarith) (neg_le_abs _)
  · have hn' : (N : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have h3 : (N : ℝ) * c < (n : ℝ) * c := mul_lt_mul_of_pos_right hn' hc
    exact lt_of_lt_of_le (by linarith) (le_abs_self _)

/-! ## The main theorem -/

/-- **Leaf `PartII-b:T11/1/3`** (periodic unfolding on `Coord`). -/
theorem coordPeriodicUnfold : UnforcedLeray.Short.IIb.CoordPeriodicUnfold := by
  intro c h P G σ H L hc hcont hcs hsum hper hvan hbox
  -- `h` vanishes for `|q| > A`
  obtain ⟨A, hA⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hcs.isCompact.isBounded
  have hA0 : ∀ q : ℝ, A < |q| → h q = 0 := by
    intro q hq
    by_contra hne
    have hmem : q ∈ tsupport h := subset_tsupport h hne
    have hball := hA hmem
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hball
    linarith
  obtain ⟨M, hM⟩ := hcont.bounded_above_of_compact_support hcs
  obtain ⟨R, hAR, hcR⟩ : ∃ R : ℝ, A ≤ R ∧ c ≤ R :=
    ⟨|A| + c, by linarith [le_abs_self A], by linarith [abs_nonneg A]⟩
  -- the integrand `h(q) G` is integrable and vanishes off the box
  have hfc : Continuous (fun x : Coord => ((h x.2.1 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hcont.comp continuous_snd.fst)
  have hbd : ∀ x : Coord, ‖((h x.2.1 : ℝ) : ℂ)‖ ≤ M := fun x => by
    rw [Complex.norm_real]
    exact hM _
  have hFK : IntegrableOn (fun x : Coord => ((h x.2.1 : ℝ) : ℂ) * G x)
      (Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-L) L)) volume :=
    Integrable.bdd_mul (hbox R) hfc.aestronglyMeasurable (Filter.Eventually.of_forall hbd)
  have hsupp : Function.support (fun x : Coord => ((h x.2.1 : ℝ) : ℂ) * G x) ⊆
      Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-L) L) := by
    intro x hx
    have hF0 : ((h x.2.1 : ℝ) : ℂ) * G x ≠ 0 := hx
    have hh : h x.2.1 ≠ 0 := fun h0 => hF0 (by rw [h0]; simp)
    have hG : G x ≠ 0 := fun g0 => hF0 (by rw [g0]; simp)
    have hq : |x.2.1| ≤ A := by
      by_contra hlt
      push_neg at hlt
      exact hh (hA0 _ hlt)
    have hs : ¬ (x.1 < σ ∨ H < x.1 ∨ L < |x.2.2|) := fun hc' => hG (hvan x hc')
    push_neg at hs
    obtain ⟨hs1, hs2, hs3⟩ := hs
    obtain ⟨hq1, hq2⟩ := abs_le.1 hq
    obtain ⟨hl1, hl2⟩ := abs_le.1 hs3
    exact ⟨⟨hs1, hs2⟩, ⟨⟨by linarith, by linarith⟩, ⟨hl1, hl2⟩⟩⟩
  have hFint : Integrable (fun x : Coord => ((h x.2.1 : ℝ) : ℂ) * G x) volume :=
    (integrableOn_iff_integrable_of_support_subset hsupp).1 hFK
  -- `G` is integrable on the cell slab `univ × cell c`
  have hGS : IntegrableOn G (univ ×ˢ Cyl.cell c) volume := by
    refine IntegrableOn.of_forall_sdiff_eq_zero (hbox R)
      (MeasurableSet.prod MeasurableSet.univ (Cyl.measurableSet_cell c)) ?_
    intro x hx
    obtain ⟨hxS, hxK⟩ := hx
    obtain ⟨hq1, hq2⟩ := Cyl.mem_cell.1 hxS.2
    apply hvan x
    by_contra hcon
    push_neg at hcon
    obtain ⟨hl1, hl2⟩ := abs_le.1 hcon.2.2
    apply hxK
    exact ⟨⟨hcon.1, hcon.2.1⟩, ⟨⟨by linarith, by linarith⟩, ⟨hl1, hl2⟩⟩⟩
  -- the window of strips that can meet the support of `h`
  obtain ⟨N, hN⟩ := exists_int_gt ((A + c) / c)
  -- `Σ_n h(q + n c) = P`
  have hsum' : ∀ q : ℝ, HasSum (fun n : ℤ => h (q + (n : ℝ) * c)) P := by
    intro q
    have e : (fun n : ℤ => h (q + (n : ℝ) * c)) =
        (fun n : ℤ => h (q - (n : ℝ) * c)) ∘ (Equiv.neg ℤ) := by
      funext n
      simp [neg_mul, sub_neg_eq_add]
    rw [e]
    exact (Equiv.neg ℤ).hasSum_iff.2 (hsum q)
  have hwin : ∀ q : ℝ, -c / 2 ≤ q → q < c / 2 →
      ∑ n ∈ Finset.Icc (-N) N, h (q + (n : ℝ) * c) = P := by
    intro q hq1 hq2
    have hz : ∀ n ∉ Finset.Icc (-N) N, h (q + (n : ℝ) * c) = 0 := fun n hn =>
      hA0 _ (puc_big_shift hc hN hq1 hq2 hn)
    have e1 := tsum_eq_sum (L := SummationFilter.unconditional ℤ)
      (f := fun n : ℤ => h (q + (n : ℝ) * c)) hz
    exact e1.symm.trans (hsum' q).tsum_eq
  -- one strip integral equals the cell integral of `h(q + n c) G`
  have hterm : ∀ n : ℤ, ∫ x in pucStrip c n, ((h x.2.1 : ℝ) : ℂ) * G x =
      ∫ y in univ ×ˢ Cyl.cell c, ((h (y.2.1 + (n : ℝ) * c) : ℝ) : ℂ) * G y := by
    intro n
    rw [puc_setIntegral_strip (fun x : Coord => ((h x.2.1 : ℝ) : ℂ) * G x) c n]
    refine setIntegral_congr_ae (MeasurableSet.prod MeasurableSet.univ (Cyl.measurableSet_cell c))
      ?_
    filter_upwards [puc_ae_shift_int hper n] with y hy
    intro _
    show ((h (y.2.1 + (n : ℝ) * c) : ℝ) : ℂ) * G (qShift ((n : ℝ) * c) y) =
      ((h (y.2.1 + (n : ℝ) * c) : ℝ) : ℂ) * G y
    rw [hy]
  have hintegrable : ∀ n : ℤ, IntegrableOn
      (fun y : Coord => ((h (y.2.1 + (n : ℝ) * c) : ℝ) : ℂ) * G y) (univ ×ˢ Cyl.cell c) volume := by
    intro n
    have hcont_n : Continuous (fun y : Coord => ((h (y.2.1 + (n : ℝ) * c) : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (hcont.comp (continuous_snd.fst.add continuous_const))
    have hbd_n : ∀ y : Coord, ‖((h (y.2.1 + (n : ℝ) * c) : ℝ) : ℂ)‖ ≤ M := fun y => by
      rw [Complex.norm_real]
      exact hM _
    exact Integrable.bdd_mul hGS hcont_n.aestronglyMeasurable (Filter.Eventually.of_forall hbd_n)
  -- strips outside the window contribute nothing
  have hzero : ∀ n ∉ Finset.Icc (-N) N,
      ∫ x in pucStrip c n, ((h x.2.1 : ℝ) : ℂ) * G x = 0 := by
    intro n hn
    rw [hterm n]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro y hy
    have hq := Cyl.mem_cell.1 hy.2
    rw [hA0 _ (puc_big_shift hc hN hq.1 hq.2 hn)]
    simp
  -- the strip decomposition
  have hsplit : ∫ x, ((h x.2.1 : ℝ) : ℂ) * G x =
      ∑' n : ℤ, ∫ x in pucStrip c n, ((h x.2.1 : ℝ) : ℂ) * G x := by
    have hU : IntegrableOn (fun x : Coord => ((h x.2.1 : ℝ) : ℂ) * G x)
        (⋃ n : ℤ, pucStrip c n) volume := by
      rw [puc_iUnion_strip hc]
      exact hFint.integrableOn
    have h1 := integral_iUnion (fun n => puc_measurableSet_strip c n)
      (puc_pairwise_disjoint hc) hU
    rw [puc_iUnion_strip hc, setIntegral_univ] at h1
    exact h1
  -- assemble the total
  have hfinal : ∫ x, ((h x.2.1 : ℝ) : ℂ) * G x = (P : ℂ) * ∫ x in univ ×ˢ Cyl.cell c, G x := by
    rw [hsplit, tsum_eq_sum (L := SummationFilter.unconditional ℤ)
      (f := fun n : ℤ => ∫ x in pucStrip c n, ((h x.2.1 : ℝ) : ℂ) * G x)
      (s := Finset.Icc (-N) N) hzero]
    simp only [hterm]
    rw [← integral_finsetSum _ (fun n _ => hintegrable n), ← integral_const_mul]
    refine setIntegral_congr_fun (MeasurableSet.prod MeasurableSet.univ (Cyl.measurableSet_cell c))
      ?_
    intro y hy
    have hq := Cyl.mem_cell.1 hy.2
    have hsumy : ∑ n ∈ Finset.Icc (-N) N, ((h (y.2.1 + (n : ℝ) * c) : ℝ) : ℂ) = (P : ℂ) := by
      exact_mod_cast hwin y.2.1 hq.1 hq.2
    show (∑ n ∈ Finset.Icc (-N) N, ((h (y.2.1 + (n : ℝ) * c) : ℝ) : ℂ) * G y) = (P : ℂ) * G y
    rw [← Finset.sum_mul, hsumy]
  exact ⟨hFint, hGS, hfinal⟩

end UnforcedLeray.Short.IIb
