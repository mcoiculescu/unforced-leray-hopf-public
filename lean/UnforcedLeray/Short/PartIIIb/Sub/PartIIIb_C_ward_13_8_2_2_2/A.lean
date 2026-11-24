import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_8_2_2_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_8_2_2.L1

/-!
# `PartIII-b:C/ward/13/8/2/2/2/1`: abstract chaining of Poincare inequalities

Source `the November 2 reference manuscript`
117-118, 2641-2642. Route: for a fixed smooth `p`, the piece means `m_i` satisfy
`(m_i - m_j)^2 vol(K_i cap K_j) <= 2 int_{K_i}(p-m_i)^2 + 2 int_{K_j}(p-m_j)^2`, a walk induction
on the connected positive-overlap graph bounds `(m_j - m_0)^2` by a multiple of `E = int_ann |grad p|^2`,
and the cover bound `int_ann f <= sum_i int_{K_i} f` finishes.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete.AnnPoinSub.Chain

lemma ac_ann_compact : IsCompact ann := by
  apply IsCompact.of_isClosed_subset (isCompact_closedBall (0 : UnforcedLeray.Space) 4)
  · exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  · intro y hy
    rw [mem_closedBall_zero_iff]
    exact hy.2

lemma ac_integrable {f : UnforcedLeray.Space → ℝ} (hf : Continuous f)
    {T : Set UnforcedLeray.Space} (hT : T ⊆ ann) : IntegrableOn f T :=
  ((hf.continuousOn.integrableOn_compact ac_ann_compact)).mono_set hT

lemma ac_finite {T : Set UnforcedLeray.Space} (hT : T ⊆ ann) : volume T ≠ ⊤ :=
  ne_top_of_le_ne_top ((ac_ann_compact.measure_lt_top (μ := volume))).ne (measure_mono hT)

lemma ac_set_le {S T : Set UnforcedLeray.Space} {f : UnforcedLeray.Space → ℝ} (hST : S ⊆ T)
    (hf : IntegrableOn f T) (hf0 : ∀ y, 0 ≤ f y) :
    ∫ y in S, f y ≤ ∫ y in T, f y :=
  setIntegral_mono_set hf (Filter.Eventually.of_forall hf0)
    (Filter.Eventually.of_forall fun _ hz => hST hz)

/-- Cover bound: `int_ann f <= sum_i int_{K_i} f` for nonnegative continuous `f`. -/
lemma ac_cover_le {ι : Type} [Fintype ι] (K : ι → Set UnforcedLeray.Space)
    (hKm : ∀ i, MeasurableSet (K i)) (hKs : ∀ i, K i ⊆ ann) (hcov : ann ⊆ ⋃ i, K i)
    (f : UnforcedLeray.Space → ℝ) (hf : Continuous f) (hf0 : ∀ y, 0 ≤ f y) :
    ∫ y in ann, f y ≤ ∑ i, ∫ y in K i, f y := by
  have hint : IntegrableOn f ann := ac_integrable hf subset_rfl
  have hF : ∀ i, IntegrableOn ((K i).indicator f) ann := fun i => hint.indicator (hKm i)
  have hannm : MeasurableSet ann := ac_ann_compact.measurableSet
  calc ∫ y in ann, f y ≤ ∫ y in ann, ∑ i, (K i).indicator f y := by
        apply setIntegral_mono_on hint (integrable_finset_sum _ (fun i _ => hF i)) hannm
        intro y hy
        obtain ⟨i, hi⟩ := mem_iUnion.1 (hcov hy)
        rw [← indicator_of_mem hi f]
        exact Finset.single_le_sum (f := fun j => (K j).indicator f y)
          (fun j _ => indicator_nonneg (fun z _ => hf0 z) y) (Finset.mem_univ i)
    _ = ∑ i, ∫ y in ann, (K i).indicator f y :=
        integral_finsetSum _ (fun i _ => hF i)
    _ = ∑ i, ∫ y in K i, f y := by
        apply Finset.sum_congr rfl
        intro i _
        rw [setIntegral_indicator (hKm i), inter_eq_right.2 (hKs i)]

/-- Walk induction on a graph: edge bounds propagate along walks, with constants uniform in `m`, `E`. -/
lemma ac_walk_bound {ι : Type} (G : SimpleGraph ι) (B : ι → ι → ℝ) :
    ∀ (u v : ι) (w : G.Walk u v), ∃ A : ℝ, ∀ (m : ι → ℝ) (E : ℝ),
      (∀ a b, G.Adj a b → (m a - m b) ^ 2 ≤ B a b * E) → (m v - m u) ^ 2 ≤ A * E := by
  intro u v w
  induction w with
  | nil => exact ⟨0, fun m E _ => by simp⟩
  | @cons a b c hab w ih =>
    obtain ⟨A', hA'⟩ := ih
    refine ⟨2 * A' + 2 * B a b, fun m E hE => ?_⟩
    have e1 := hE a b hab
    have e2 := hA' m E hE
    nlinarith [sq_nonneg (m c - 2 * m b + m a)]

/-- Edge bound: `(m_i - m_j)^2 vol(K_i cap K_j) <= (2 C_i + 2 C_j) E`. -/
lemma ac_edge {ι : Type} (K : ι → Set UnforcedLeray.Space)
    (hKm : ∀ i, MeasurableSet (K i)) (hKs : ∀ i, K i ⊆ ann)
    (Cp : ι → ℝ) (p : UnforcedLeray.Space → ℝ) (hp : ContDiff ℝ 1 p) (m : ι → ℝ) (E : ℝ)
    (hmE : ∀ i, ∫ y in K i, (p y - m i) ^ 2 ≤ Cp i * E) (i j : ι)
    (hV : 0 < (volume (K i ∩ K j)).toReal) :
    (m i - m j) ^ 2 ≤ ((2 * Cp i + 2 * Cp j) / (volume (K i ∩ K j)).toReal) * E := by
  have hSm : MeasurableSet (K i ∩ K j) := (hKm i).inter (hKm j)
  have hSi : K i ∩ K j ⊆ K i := inter_subset_left
  have hSj : K i ∩ K j ⊆ K j := inter_subset_right
  have hSfin : volume (K i ∩ K j) ≠ ⊤ := ac_finite (hSi.trans (hKs i))
  have hci : Continuous fun y => (p y - m i) ^ 2 := (hp.continuous.sub continuous_const).pow 2
  have hcj : Continuous fun y => (p y - m j) ^ 2 := (hp.continuous.sub continuous_const).pow 2
  have hIi : IntegrableOn (fun y => (p y - m i) ^ 2) (K i ∩ K j) :=
    ac_integrable hci (hSi.trans (hKs i))
  have hIj : IntegrableOn (fun y => (p y - m j) ^ 2) (K i ∩ K j) :=
    ac_integrable hcj (hSj.trans (hKs j))
  have hmain : ∫ y in K i ∩ K j, (m i - m j) ^ 2 ≤
      ∫ y in K i ∩ K j, (2 * (p y - m i) ^ 2 + 2 * (p y - m j) ^ 2) := by
    apply setIntegral_mono_on (integrableOn_const hSfin) ((hIi.const_mul 2).add (hIj.const_mul 2))
      hSm
    intro y _
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (p y - m i + (p y - m j))]
  have hRHS : ∫ y in K i ∩ K j, (2 * (p y - m i) ^ 2 + 2 * (p y - m j) ^ 2) =
      2 * (∫ y in K i ∩ K j, (p y - m i) ^ 2) + 2 * (∫ y in K i ∩ K j, (p y - m j) ^ 2) := by
    rw [integral_add (hIi.const_mul 2) (hIj.const_mul 2), integral_const_mul, integral_const_mul]
  have hLHS : ∫ y in K i ∩ K j, (m i - m j) ^ 2 = (m i - m j) ^ 2 * (volume (K i ∩ K j)).toReal := by
    rw [setIntegral_const, smul_eq_mul, mul_comm]
    rfl
  have hi' : ∫ y in K i ∩ K j, (p y - m i) ^ 2 ≤ Cp i * E :=
    (ac_set_le hSi (ac_integrable hci (hKs i)) (fun y => sq_nonneg _)).trans (hmE i)
  have hj' : ∫ y in K i ∩ K j, (p y - m j) ^ 2 ≤ Cp j * E :=
    (ac_set_le hSj (ac_integrable hcj (hKs j)) (fun y => sq_nonneg _)).trans (hmE j)
  have key : (m i - m j) ^ 2 * (volume (K i ∩ K j)).toReal ≤ 2 * (Cp i * E) + 2 * (Cp j * E) := by
    have := hmain
    rw [hLHS, hRHS] at this
    linarith
  have e : (2 * Cp i + 2 * Cp j) * E = 2 * (Cp i * E) + 2 * (Cp j * E) := by ring
  rw [div_mul_eq_mul_div, le_div_iff₀ hV, e]
  exact key

theorem abstractChain : UnforcedLeray.Short.PartIIIb.Concrete.AnnPoinSub.Chain.AbstractChain := by
  intro ι _ K hK hcov hconn
  unfold PoincOn
  have hKm : ∀ i, MeasurableSet (K i) := fun i => (hK i).1
  have hKs : ∀ i, K i ⊆ ann := fun i => (hK i).2.1
  have hP : ∀ i, ∃ C : ℝ, ∀ p : UnforcedLeray.Space → ℝ, ContDiff ℝ 1 p → ∃ m : ℝ,
      ∫ y in K i, (p y - m) ^ 2 ≤ C * ∫ y in K i, ‖physGrad p y‖ ^ 2 := fun i => (hK i).2.2
  choose Cc hCc using hP
  obtain ⟨Cp, hCp0, hCp⟩ : ∃ Cp : ι → ℝ, (∀ i, 0 ≤ Cp i) ∧ ∀ i (p : UnforcedLeray.Space → ℝ),
      ContDiff ℝ 1 p → ∃ m : ℝ,
      ∫ y in K i, (p y - m) ^ 2 ≤ Cp i * ∫ y in K i, ‖physGrad p y‖ ^ 2 := by
    refine ⟨fun i => max (Cc i) 0, fun i => le_max_right _ _, fun i p hp => ?_⟩
    obtain ⟨m, hm⟩ := hCc i p hp
    refine ⟨m, hm.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)⟩
    exact setIntegral_nonneg (hKm i) (fun y _ => by positivity)
  set G : SimpleGraph ι := SimpleGraph.fromRel fun i j => 0 < (volume (K i ∩ K j)).toReal with hG
  obtain ⟨i0⟩ := hconn.nonempty
  obtain ⟨B, hB⟩ : ∃ B : ι → ι → ℝ, ∀ a b,
      B a b = (2 * Cp a + 2 * Cp b) / (volume (K a ∩ K b)).toReal :=
    ⟨fun a b => (2 * Cp a + 2 * Cp b) / (volume (K a ∩ K b)).toReal, fun _ _ => rfl⟩
  have hAi : ∀ i, ∃ A : ℝ, ∀ (m : ι → ℝ) (E : ℝ),
      (∀ a b, G.Adj a b → (m a - m b) ^ 2 ≤ B a b * E) → (m i - m i0) ^ 2 ≤ A * E := by
    intro i
    obtain ⟨w⟩ := hconn.preconnected i0 i
    exact ac_walk_bound G B i0 i w
  choose A hA using hAi
  refine ⟨∑ i, (2 * Cp i + 2 * volume.real (K i) * A i), ?_⟩
  intro p hp
  choose M hM using fun i => hCp i p hp
  have hE0 : 0 ≤ ∫ y in ann, ‖physGrad p y‖ ^ 2 :=
    setIntegral_nonneg ac_ann_compact.measurableSet (fun y _ => by positivity)
  set E := ∫ y in ann, ‖physGrad p y‖ ^ 2 with hE
  have hgc : Continuous fun y => ‖physGrad p y‖ ^ 2 :=
    ((UnforcedLeray.Short.PartIIIb.Concrete.AnnPoinSub.CP.continuous_physGrad hp).norm).pow 2
  have hGE : ∀ i, ∫ y in K i, ‖physGrad p y‖ ^ 2 ≤ E := fun i =>
    ac_set_le (hKs i) (ac_integrable hgc subset_rfl) (fun y => by positivity)
  have hmE : ∀ i, ∫ y in K i, (p y - M i) ^ 2 ≤ Cp i * E := fun i =>
    (hM i).trans (mul_le_mul_of_nonneg_left (hGE i) (hCp0 i))
  have hedge : ∀ a b, G.Adj a b → (M a - M b) ^ 2 ≤ B a b * E := by
    intro a b hab
    simp only [hG, SimpleGraph.fromRel_adj] at hab
    have hV : 0 < (volume (K a ∩ K b)).toReal := by
      rcases hab.2 with h | h
      · exact h
      · rwa [Set.inter_comm] at h
    rw [hB]
    exact ac_edge K hKm hKs Cp p hp M E hmE a b hV
  have hpiece : ∀ i, ∫ y in K i, (p y - M i0) ^ 2 ≤ (2 * Cp i + 2 * volume.real (K i) * A i) * E := by
    intro i
    have hci : Continuous fun y => (p y - M i) ^ 2 := (hp.continuous.sub continuous_const).pow 2
    have hmono : ∫ y in K i, (p y - M i0) ^ 2 ≤
        ∫ y in K i, (2 * (p y - M i) ^ 2 + 2 * (M i - M i0) ^ 2) := by
      have hint2 : IntegrableOn (fun y => 2 * (p y - M i) ^ 2 + 2 * (M i - M i0) ^ 2) (K i) :=
        ((ac_integrable hci (hKs i)).const_mul 2).add
          (integrableOn_const (C := 2 * (M i - M i0) ^ 2) (ac_finite (hKs i)))
      apply setIntegral_mono_on (ac_integrable
          ((hp.continuous.sub continuous_const).pow 2) (hKs i)) hint2 (hKm i)
      intro y _
      show (p y - M i0) ^ 2 ≤ 2 * (p y - M i) ^ 2 + 2 * (M i - M i0) ^ 2
      nlinarith [sq_nonneg (p y - 2 * M i + M i0)]
    have hRHS : ∫ y in K i, (2 * (p y - M i) ^ 2 + 2 * (M i - M i0) ^ 2) =
        2 * (∫ y in K i, (p y - M i) ^ 2) + 2 * volume.real (K i) * (M i - M i0) ^ 2 := by
      rw [integral_add ((ac_integrable hci (hKs i)).const_mul 2)
        (integrableOn_const (ac_finite (hKs i))), integral_const_mul, setIntegral_const, smul_eq_mul]
      ring
    have hA' : (M i - M i0) ^ 2 ≤ A i * E := hA i M E hedge
    have hV0 : 0 ≤ volume.real (K i) := measureReal_nonneg
    have h2 : 2 * volume.real (K i) * (M i - M i0) ^ 2 ≤ 2 * volume.real (K i) * (A i * E) := by
      have := mul_le_mul_of_nonneg_left hA' (by positivity : (0:ℝ) ≤ 2 * volume.real (K i))
      linarith
    have e : (2 * Cp i + 2 * volume.real (K i) * A i) * E =
        2 * (Cp i * E) + 2 * volume.real (K i) * (A i * E) := by ring
    rw [e]
    linarith [hmono, hRHS, hmE i, h2]
  refine ⟨M i0, ?_⟩
  calc ∫ y in ann, (p y - M i0) ^ 2 ≤ ∑ i, ∫ y in K i, (p y - M i0) ^ 2 :=
        ac_cover_le K hKm hKs hcov _ ((hp.continuous.sub continuous_const).pow 2) (fun y => sq_nonneg _)
    _ ≤ ∑ i, (2 * Cp i + 2 * volume.real (K i) * A i) * E :=
        Finset.sum_le_sum (fun i _ => hpiece i)
    _ = (∑ i, (2 * Cp i + 2 * volume.real (K i) * A i)) * E := (Finset.sum_mul _ _ _).symm

end UnforcedLeray.Short.PartIIIb.Concrete.AnnPoinSub.Chain
