import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.TransportBound.BoundA.Helpers

/-!
# Part I, task `PartI:T08/7/2/2`: `JTBoundA`

Source: `the November 2 reference manuscript` lines 352-358.

`∂_w (V·∇)f_k` is the Leibniz sum over the splittings `wacSplits w` (`jai_expand`). The splitting
with empty `V`-part gives `⟨D^j f, (V·∇) D^j f⟩ = 0` (`ba_top_zero`, `div V = 0`); each other one is
`∂_a V_m ∂_b f_k` with `1 ≤ |a| ≤ j`, bounded by `M_{|a|} √J_{j+1-|a|} √J_j` (`ba_term_bound`).
There are at most `2^j · 2 · 2^j · 2` such terms.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

theorem ba_int_list_sum {μ : Measure Plane} {α : Type*} (G : α → Plane → ℝ) :
    ∀ L : List α, (∀ p ∈ L, Integrable (G p) μ) →
      ∫ z, (L.map (fun p => G p z)).sum ∂μ = (L.map (fun p => ∫ z, G p z ∂μ)).sum
  | [], _ => by simp
  | p :: L, h => by
    simp only [List.map_cons, List.sum_cons]
    rw [integral_add (h p (by simp)) (jai_list_integrable G L fun q hq => h q (by simp [hq])),
      ba_int_list_sum G L fun q hq => h q (by simp [hq])]

theorem ba_single_le {c : ℝ} {f : Plane → Vec} (hf : CellSmoothL2 c f) (w : List Bool)
    (k : Fin 2) :
    ∫ z in Cyl.cell c, wordComp w f k z * wordComp w f k z ≤ jetEnergy c w.length f := by
  have hint : ∀ (w' : List Bool) (k' : Fin 2),
      Integrable (fun z => wordComp w' f k' z * wordComp w' f k' z) (Cyl.cellμ c) :=
    fun w' k' => (hf.2.2 w' k').integrable_mul (hf.2.2 w' k')
  unfold jetEnergy jetPair
  refine integral_mono (hint w k) ?_ fun z => ?_
  · exact integrable_finsetSum _ fun w' _ => integrable_finsetSum _ fun k' _ => hint w' k'
  · have hw : w ∈ wordsOfLength w.length := ForcingIBP.mem_wordsOfLength_iff'.2 rfl
    calc wordComp w f k z * wordComp w f k z
        ≤ ∑ k' : Fin 2, wordComp w f k' z * wordComp w f k' z :=
          Finset.single_le_sum (f := fun k' => wordComp w f k' z * wordComp w f k' z)
            (fun i _ => mul_self_nonneg _) (Finset.mem_univ k)
      _ ≤ ∑ w' ∈ wordsOfLength w.length, ∑ k' : Fin 2,
            wordComp w' f k' z * wordComp w' f k' z :=
          Finset.single_le_sum
            (f := fun w' => ∑ k' : Fin 2, wordComp w' f k' z * wordComp w' f k' z)
            (fun i _ => Finset.sum_nonneg fun k' _ => mul_self_nonneg _) hw

theorem ba_wordComp_append_true (w : List Bool) {F : Plane → ℝ} (hF : ContDiff ℝ ∞ F) :
    B0151.derivWord (w ++ [true]) F = Cyl.partialQ (B0151.derivWord w F) := by
  rw [vjl_derivWord_append]
  exact (ForcingIBP.derivWord_comm w F hF).1

theorem ba_wordComp_append_false (w : List Bool) {F : Plane → ℝ} (hF : ContDiff ℝ ∞ F) :
    B0151.derivWord (w ++ [false]) F = Cyl.partialEta (B0151.derivWord w F) := by
  rw [vjl_derivWord_append]
  exact (ForcingIBP.derivWord_comm w F hF).2

theorem ba_card_words (l : ℕ) : (wordsOfLength l).card ≤ 2 ^ l := by
  unfold wordsOfLength
  refine Finset.card_image_le.trans ?_
  simp

theorem jtBoundA_proof : UnforcedLeray.Short.PartI.JTBoundA := by
  intro j
  refine ⟨4 * (2 ^ j * 2 ^ j), by positivity, ?_⟩
  intro c V f G M H
  obtain ⟨hc, hV, hVp, hVd, hf, hfd, hfb, hG, hM⟩ := H
  have hc0 : 0 < c := by linarith
  have hfs : ContDiff ℝ ∞ f := hf.1
  have hM0 : ∀ i, 0 ≤ M i := fun i =>
    le_trans (abs_nonneg _) (by simpa using hM (List.replicate i true) 0 (0, 0))
  have bV : ∀ (w : List Bool) (k : Fin 2), ∃ M' : ℝ, ∀ z : Plane, |wordComp w V k z| ≤ M' :=
    fun w k => ⟨M w.length, hM w k⟩
  set B : ℝ := ∑ i ∈ Finset.Icc 1 (j + 1),
    M i * Real.sqrt (jetEnergy c (j + 1 - i) f) * Real.sqrt (jetEnergy c j f) with hB
  have hBnn : 0 ≤ B := Finset.sum_nonneg fun i _ => by have := hM0 i; positivity
  -- the bound for one word and one component
  have hwk : ∀ w : List Bool, w.length = j → ∀ k : Fin 2,
      Integrable (fun z => wordComp w f k z * wordComp w (advB V f) k z) (Cyl.cellμ c) ∧
      |∫ z in Cyl.cell c, wordComp w f k z * wordComp w (advB V f) k z| ≤
        2 ^ j * (2 * B) := by
    intro w hw k
    let Tt : List Bool × List Bool → Plane → ℝ := fun p z =>
      wordComp w f k z * (wordComp p.1 V 0 z * wordComp (p.2 ++ [true]) f k z)
    let Tf : List Bool × List Bool → Plane → ℝ := fun p z =>
      wordComp w f k z * (wordComp p.1 V 1 z * wordComp (p.2 ++ [false]) f k z)
    have hexp : ∀ z, wordComp w f k z * wordComp w (advB V f) k z =
        ((wacSplits w).map (fun p => Tt p z + Tf p z)).sum := by
      intro z
      rw [jai_expand V f hV hfs w k z, jai_list_mul]
      refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
      simp only [Tt, Tf]
      ring
    have iT : ∀ p, Integrable (Tt p) (Cyl.cellμ c) := fun p =>
      jai_int3 (μ := Cyl.cellμ c) (wordComp w f k) (fun z => wordComp p.1 V 0 z)
        (fun z => wordComp (p.2 ++ [true]) f k z) (hf.2.2 w k)
        (contDiff_wordComp hV p.1 0).continuous.aestronglyMeasurable
        (contDiff_wordComp hfs _ k).continuous.aestronglyMeasurable
        (Or.inr ⟨hf.2.2 _ k, M p.1.length, hM p.1 0⟩)
    have iF : ∀ p, Integrable (Tf p) (Cyl.cellμ c) := fun p =>
      jai_int3 (μ := Cyl.cellμ c) (wordComp w f k) (fun z => wordComp p.1 V 1 z)
        (fun z => wordComp (p.2 ++ [false]) f k z) (hf.2.2 w k)
        (contDiff_wordComp hV p.1 1).continuous.aestronglyMeasurable
        (contDiff_wordComp hfs _ k).continuous.aestronglyMeasurable
        (Or.inr ⟨hf.2.2 _ k, M p.1.length, hM p.1 1⟩)
    have funEq : (fun z => wordComp w f k z * wordComp w (advB V f) k z) =
        fun z => ((wacSplits w).map (fun p => Tt p z + Tf p z)).sum := funext hexp
    have hint : Integrable (fun z => wordComp w f k z * wordComp w (advB V f) k z)
        (Cyl.cellμ c) := by
      rw [funEq]
      exact jai_list_integrable (fun p z => Tt p z + Tf p z) (wacSplits w)
        fun p _ => (iT p).add (iF p)
    refine ⟨hint, ?_⟩
    have hval : ∫ z in Cyl.cell c, wordComp w f k z * wordComp w (advB V f) k z =
        ((wacSplits w).map (fun p => ∫ z in Cyl.cell c, (Tt p z + Tf p z))).sum := by
      have := ba_int_list_sum (μ := Cyl.cellμ c) (fun p z => Tt p z + Tf p z) (wacSplits w)
        fun p _ => (iT p).add (iF p)
      rw [funEq]
      exact this
    set Φ : List Bool × List Bool → ℝ := fun p => ∫ z in Cyl.cell c, (Tt p z + Tf p z) with hΦ
    rw [hval]
    change |((wacSplits w).map Φ).sum| ≤ _
    rw [wac_split_sum w Φ]
    -- the top term vanishes
    have hG : ContDiff ℝ ∞ (wordComp w f k) := contDiff_wordComp hfs w k
    have hGp : Cyl.IsPeriodic c (wordComp w f k) :=
      ForcingIBP.per_derivWord w _ (hf.2.1.fun_comp (fun x => x k))
    have hFk : ContDiff ℝ ∞ (fun x => f x k) := contDiff_comp_coord hfs k
    have hQ : wordComp (w ++ [true]) f k = Cyl.partialQ (wordComp w f k) :=
      ba_wordComp_append_true w hFk
    have hE : wordComp (w ++ [false]) f k = Cyl.partialEta (wordComp w f k) :=
      ba_wordComp_append_false w hFk
    have htop0 := ba_top_zero hc0 hV hVp hVd bV hG hGp (hf.2.2 w k)
      (by rw [← hQ]; exact hf.2.2 _ k) (by rw [← hE]; exact hf.2.2 _ k)
    have htop : ((wacSplits w).map (fun p => if p.1 = [] then Φ p else 0)).sum = 0 := by
      have hc1 : ((wacSplits w).map (fun p => if p.1 = [] then Φ p else 0)).sum =
          ((wacSplits w).map (fun p => if p.1 = [] then
            (∫ z in Cyl.cell c, wordComp w f k z * (V z 0 * wordComp (p.2 ++ [true]) f k z +
              V z 1 * wordComp (p.2 ++ [false]) f k z)) else 0)).sum := by
        refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
        by_cases hp : p.1 = []
        · simp only [hp, ite_true]
          refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          have e0 : wordComp [] V 0 z = V z 0 := rfl
          have e1 : wordComp [] V 1 z = V z 1 := rfl
          simp only [Tt, Tf, hp, e0, e1]
          ring
        · simp [hp]
      rw [hc1, wac_filter_sum (fun u => ∫ z in Cyl.cell c, wordComp w f k z *
        (V z 0 * wordComp (u ++ [true]) f k z + V z 1 * wordComp (u ++ [false]) f k z)) w]
      rw [hQ, hE]
      exact htop0
    rw [htop, zero_add]
    -- the other terms
    have hterm : ∀ p ∈ wacSplits w, p.1 ≠ [] → ∀ (m : Fin 2) (β : Bool),
        |∫ z in Cyl.cell c, wordComp w f k z * (wordComp p.1 V m z *
          wordComp (p.2 ++ [β]) f k z)| ≤ B := by
      intro p hp hne m β
      have hl := wac_splits_len_sum w p hp
      have hlen1 : 1 ≤ p.1.length := List.length_pos_iff.2 hne
      have h1 := ba_term_bound hV hf (M p.1.length) p.1 w (p.2 ++ [β]) m k (hM p.1 m)
      have hb : (p.2 ++ [β]).length = j + 1 - p.1.length := by
        simp only [List.length_append, List.length_singleton]
        omega
      have s1 : ∫ z in Cyl.cell c, wordComp (p.2 ++ [β]) f k z * wordComp (p.2 ++ [β]) f k z ≤
          jetEnergy c (j + 1 - p.1.length) f := by
        have := ba_single_le hf (p.2 ++ [β]) k
        rwa [hb] at this
      have s2 : ∫ z in Cyl.cell c, wordComp w f k z * wordComp w f k z ≤ jetEnergy c j f := by
        have := ba_single_le hf w k
        rwa [hw] at this
      calc _ ≤ M p.1.length * (Real.sqrt (∫ z in Cyl.cell c, wordComp (p.2 ++ [β]) f k z *
              wordComp (p.2 ++ [β]) f k z) *
            Real.sqrt (∫ z in Cyl.cell c, wordComp w f k z * wordComp w f k z)) := h1
        _ ≤ M p.1.length * (Real.sqrt (jetEnergy c (j + 1 - p.1.length) f) *
            Real.sqrt (jetEnergy c j f)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul (Real.sqrt_le_sqrt s1) (Real.sqrt_le_sqrt s2)
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (hM0 _)
        _ = M p.1.length * Real.sqrt (jetEnergy c (j + 1 - p.1.length) f) *
            Real.sqrt (jetEnergy c j f) := by ring
        _ ≤ B := Finset.single_le_sum
            (f := fun i => M i * Real.sqrt (jetEnergy c (j + 1 - i) f) *
              Real.sqrt (jetEnergy c j f))
            (fun i _ => by have := hM0 i; positivity)
            (Finset.mem_Icc.2 ⟨hlen1, by omega⟩)
    have hphi : ∀ p ∈ wacSplits w,
        |(if p.1 = [] then (0 : ℝ) else Φ p)| ≤ 2 * B := by
      intro p hp
      by_cases hne : p.1 = []
      · simp only [hne, ite_true, abs_zero]; linarith
      · simp only [hne, ite_false]
        have e : Φ p = (∫ z in Cyl.cell c, Tt p z) + ∫ z in Cyl.cell c, Tf p z :=
          integral_add (iT p) (iF p)
        rw [e]
        have a1 := hterm p hp hne 0 true
        have a2 := hterm p hp hne 1 false
        calc _ ≤ |∫ z in Cyl.cell c, Tt p z| + |∫ z in Cyl.cell c, Tf p z| := abs_add_le _ _
          _ ≤ B + B := add_le_add a1 a2
          _ = 2 * B := by ring
    have hsum := wac_sum_bound (fun p => if p.1 = [] then (0 : ℝ) else Φ p) (2 * B)
      (by linarith) (wacSplits w) hphi
    rw [wac_splits_length, hw] at hsum
    simpa using hsum
  -- assemble over words and components
  have hW : ∀ w ∈ wordsOfLength j, ∀ k : Fin 2, w.length = j := fun w hw _ =>
    ForcingIBP.mem_wordsOfLength_iff'.1 hw
  have hI : ∀ w ∈ wordsOfLength j, Integrable (fun z => ∑ k : Fin 2,
      wordComp w f k z * wordComp w (advB V f) k z) (Cyl.cellμ c) := fun w hw =>
    integrable_finsetSum _ fun k _ => (hwk w (hW w hw 0) k).1
  have e1 : jetPair c j f (advB V f) = ∑ w ∈ wordsOfLength j, ∑ k : Fin 2,
      ∫ z in Cyl.cell c, wordComp w f k z * wordComp w (advB V f) k z := by
    unfold jetPair
    have step1 : ∫ z in Cyl.cell c, ∑ w ∈ wordsOfLength j, ∑ k : Fin 2,
        wordComp w f k z * wordComp w (advB V f) k z =
        ∑ w ∈ wordsOfLength j, ∫ z in Cyl.cell c, ∑ k : Fin 2,
          wordComp w f k z * wordComp w (advB V f) k z :=
      integral_finsetSum _ hI
    rw [step1]
    refine Finset.sum_congr rfl fun w hw => ?_
    exact integral_finsetSum _ fun k _ => (hwk w (hW w hw 0) k).1
  rw [e1]
  calc |∑ w ∈ wordsOfLength j, ∑ k : Fin 2,
        ∫ z in Cyl.cell c, wordComp w f k z * wordComp w (advB V f) k z|
      ≤ ∑ w ∈ wordsOfLength j, |∑ k : Fin 2,
        ∫ z in Cyl.cell c, wordComp w f k z * wordComp w (advB V f) k z| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ w ∈ wordsOfLength j, ∑ k : Fin 2,
        |∫ z in Cyl.cell c, wordComp w f k z * wordComp w (advB V f) k z| :=
        Finset.sum_le_sum fun w _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ w ∈ wordsOfLength j, ∑ k : Fin 2, (2 ^ j * (2 * B)) :=
        Finset.sum_le_sum fun w hw => Finset.sum_le_sum fun k _ => (hwk w (hW w hw 0) k).2
    _ = ((wordsOfLength j).card : ℝ) * (2 * (2 ^ j * (2 * B))) := by
        simp [Finset.sum_const]
    _ ≤ 2 ^ j * (2 * (2 ^ j * (2 * B))) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast ba_card_words j
    _ = 4 * (2 ^ j * 2 ^ j) * B := by ring

end UnforcedLeray.Short.PartI
