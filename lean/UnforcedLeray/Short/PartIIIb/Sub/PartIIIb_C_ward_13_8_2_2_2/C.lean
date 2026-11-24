import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_8_2_2_2

/-!
# `PartIII-b:C/ward/13/8/2/2/2/3`: geometry of the six conical pieces

Source `the November 2 reference manuscript`
117-118, 2641-2642. Pieces `cone k σ`: measurable, inside `ann`, covering `ann` (some coordinate
satisfies `|y_k| >= |y|/2`), and the positive-overlap graph on `Fin 3 × Bool` is connected.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.Concrete.AnnPoinSub.Chain

lemma sgn_mul_self (σ : Bool) :
    (if σ then (1:ℝ) else -1) * (if σ then (1:ℝ) else -1) = 1 := by
  cases σ <;> norm_num

lemma norm_sq_three (y : UnforcedLeray.Space) : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp [Real.norm_eq_abs, sq_abs]

lemma cone_measurable (k : Fin 3) (σ : Bool) : MeasurableSet (cone k σ) := by
  unfold cone
  have hyk : Continuous fun y : UnforcedLeray.Space => y k := by fun_prop
  refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)
  · exact measurableSet_le measurable_const measurable_norm
  · exact measurableSet_le measurable_norm measurable_const
  · exact measurableSet_le measurable_norm (by fun_prop)

lemma exists_axis (y : UnforcedLeray.Space) (h1 : 1 ≤ ‖y‖) :
    ∃ k : Fin 3, ‖y‖ ^ 2 ≤ 4 * (y k) ^ 2 := by
  have hsq := norm_sq_three y
  by_contra hcon
  push_neg at hcon
  have a0 := hcon 0
  have a1 := hcon 1
  have a2 := hcon 2
  nlinarith [sq_nonneg ‖y‖]

lemma mem_cone_of_axis (k : Fin 3) (y : UnforcedLeray.Space) (h1 : 1 ≤ ‖y‖) (h4 : ‖y‖ ≤ 4)
    (hk : ‖y‖ ^ 2 ≤ 4 * (y k) ^ 2) : ∃ σ : Bool, y ∈ cone k σ := by
  have hn := norm_nonneg y
  by_cases hp : 0 ≤ y k
  · refine ⟨true, ?_⟩
    simp only [cone, Set.mem_setOf_eq, if_true]
    refine ⟨h1, h4, ?_⟩
    nlinarith
  · refine ⟨false, ?_⟩
    simp only [cone, Set.mem_setOf_eq, Bool.false_eq_true, if_false]
    refine ⟨h1, h4, ?_⟩
    nlinarith

lemma ann_subset_cones : ann ⊆ ⋃ i : Fin 3 × Bool, cone i.1 i.2 := by
  intro y hy
  obtain ⟨h1, h4⟩ := hy
  obtain ⟨k, hk⟩ := exists_axis y h1
  obtain ⟨σ, hσ⟩ := mem_cone_of_axis k y h1 h4 hk
  exact mem_iUnion.2 ⟨(k, σ), hσ⟩

lemma norm_sq_two_axes (k j : Fin 3) (hkj : k ≠ j) (a b : ℝ) :
    ‖EuclideanSpace.single k a + EuclideanSpace.single j b‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [norm_add_sq_real, EuclideanSpace.norm_single, EuclideanSpace.norm_single,
    EuclideanSpace.inner_single_left]
  simp [EuclideanSpace.single_apply, hkj, Real.norm_eq_abs, sq_abs]

lemma overlap_pos (k j : Fin 3) (σ τ : Bool) (hkj : k ≠ j) :
    0 < (volume (cone k σ ∩ cone j τ)).toReal := by
  have hs := sgn_mul_self σ
  have ht := sgn_mul_self τ
  set s : ℝ := if σ then (1:ℝ) else -1 with hs_def
  set t : ℝ := if τ then (1:ℝ) else -1 with ht_def
  set p : UnforcedLeray.Space :=
    EuclideanSpace.single k (2 * s) + EuclideanSpace.single j (2 * t) with hp_def
  have hpn : ‖p‖ ^ 2 = 8 := by
    rw [hp_def, norm_sq_two_axes k j hkj]
    linear_combination 4 * hs + 4 * ht
  have hpk : p k = 2 * s := by
    simp [hp_def, EuclideanSpace.single_apply, hkj]
  have hpj : p j = 2 * t := by
    simp [hp_def, EuclideanSpace.single_apply, hkj.symm]
  have hsk : 2 * (s * p k) = 4 := by
    rw [hpk]; linear_combination 4 * hs
  have htj : 2 * (t * p j) = 4 := by
    rw [hpj]; linear_combination 4 * ht
  have hyk : Continuous fun y : UnforcedLeray.Space => y k := by fun_prop
  have hyj : Continuous fun y : UnforcedLeray.Space => y j := by fun_prop
  have hU_open : IsOpen {y : UnforcedLeray.Space |
      1 < ‖y‖ ∧ ‖y‖ < 4 ∧ ‖y‖ < 2 * (s * y k) ∧ ‖y‖ < 2 * (t * y j)} := by
    have h1 : IsOpen {y : UnforcedLeray.Space | 1 < ‖y‖} := isOpen_lt continuous_const continuous_norm
    have h2 : IsOpen {y : UnforcedLeray.Space | ‖y‖ < 4} := isOpen_lt continuous_norm continuous_const
    have h3 : IsOpen {y : UnforcedLeray.Space | ‖y‖ < 2 * (s * y k)} :=
      isOpen_lt continuous_norm (continuous_const.mul (continuous_const.mul hyk))
    have h4 : IsOpen {y : UnforcedLeray.Space | ‖y‖ < 2 * (t * y j)} :=
      isOpen_lt continuous_norm (continuous_const.mul (continuous_const.mul hyj))
    exact h1.inter (h2.inter (h3.inter h4))
  have hpt : p ∈ {y : UnforcedLeray.Space |
      1 < ‖y‖ ∧ ‖y‖ < 4 ∧ ‖y‖ < 2 * (s * y k) ∧ ‖y‖ < 2 * (t * y j)} := by
    have hn := norm_nonneg p
    refine ⟨?_, ?_, ?_, ?_⟩
    · nlinarith
    · nlinarith
    · rw [hsk]; nlinarith
    · rw [htj]; nlinarith
  have hsub : {y : UnforcedLeray.Space |
      1 < ‖y‖ ∧ ‖y‖ < 4 ∧ ‖y‖ < 2 * (s * y k) ∧ ‖y‖ < 2 * (t * y j)} ⊆
      cone k σ ∩ cone j τ := by
    intro y hy
    exact ⟨⟨hy.1.le, hy.2.1.le, hy.2.2.1.le⟩, ⟨hy.1.le, hy.2.1.le, hy.2.2.2.le⟩⟩
  have hpos : 0 < volume {y : UnforcedLeray.Space |
      1 < ‖y‖ ∧ ‖y‖ < 4 ∧ ‖y‖ < 2 * (s * y k) ∧ ‖y‖ < 2 * (t * y j)} :=
    hU_open.measure_pos volume ⟨p, hpt⟩
  have hfin : volume (cone k σ ∩ cone j τ) ≠ ⊤ := by
    apply ne_top_of_le_ne_top
      ((isCompact_closedBall (0 : UnforcedLeray.Space) 4).measure_lt_top (μ := volume)).ne
    apply measure_mono
    intro y hy
    rw [mem_closedBall_zero_iff]
    exact hy.1.2.1
  have hle := measure_mono (μ := volume) hsub
  have hpos' : 0 < volume (cone k σ ∩ cone j τ) := lt_of_lt_of_le hpos hle
  exact ENNReal.toReal_pos hpos'.ne' hfin

lemma adj_of_axes (k j : Fin 3) (σ τ : Bool) (hkj : k ≠ j) :
    (SimpleGraph.fromRel fun i j : Fin 3 × Bool =>
      0 < (volume (cone i.1 i.2 ∩ cone j.1 j.2)).toReal).Adj (k, σ) (j, τ) := by
  rw [SimpleGraph.fromRel_adj]
  exact ⟨fun h => hkj (congrArg Prod.fst h), Or.inl (overlap_pos k j σ τ hkj)⟩

lemma cone_graph_connected : (SimpleGraph.fromRel fun i j : Fin 3 × Bool =>
      0 < (volume (cone i.1 i.2 ∩ cone j.1 j.2)).toReal).Connected := by
  have hreach : ∀ u : Fin 3 × Bool, (SimpleGraph.fromRel fun i j : Fin 3 × Bool =>
      0 < (volume (cone i.1 i.2 ∩ cone j.1 j.2)).toReal).Reachable (0, true) u := by
    rintro ⟨k, σ⟩
    by_cases hk : k = 0
    · subst hk
      cases σ
      · exact (adj_of_axes 0 1 true true (by decide)).reachable.trans
          (adj_of_axes 1 0 true false (by decide)).reachable
      · exact SimpleGraph.Reachable.refl _
    · exact (adj_of_axes 0 k true σ (Ne.symm hk)).reachable
  have : Nonempty (Fin 3 × Bool) := ⟨(0, true)⟩
  exact ⟨fun u v => (hreach u).symm.trans (hreach v)⟩

theorem coneGeometry : UnforcedLeray.Short.PartIIIb.Concrete.AnnPoinSub.Chain.ConeGeometry := by
  unfold ConeGeometry
  exact ⟨fun i => ⟨cone_measurable i.1 i.2, fun y hy => ⟨hy.1, hy.2.1⟩⟩,
    ann_subset_cones, cone_graph_connected⟩

end UnforcedLeray.Short.PartIIIb.Concrete.AnnPoinSub.Chain
