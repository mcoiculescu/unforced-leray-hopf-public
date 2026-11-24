import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.PairCont
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.ProductRule.PairCont

/-!
# Continuity of a parametric cell integral (SP 3074-3075, `PartIII-a:T21/2/3/1/5/3/1`)

The integrand `F p · T p` is split as `(F p - F p₀) T p + F p₀ (T p - T p₀)`. The first term is
bounded by the `L²` distance of `F p` to `F p₀` times the uniform `L²` bound of `T p` (which is
supported in the compact box `|η| ≤ L` of the cell); the second tends to `0` by dominated
convergence, using pointwise continuity of `T` and the box dominator.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace GCont1Aux

lemma cellMeasure_zero (c : ℝ) : B0579.cellMeasure c 0 = volume.restrict (B0579.cell c) := by
  unfold B0579.cellMeasure
  have h : (fun x : ℝ × ℝ => ((B0579.density 0 x : NNReal) : ENNReal)) = 1 := by
    funext x
    simp [B0579.density]
  rw [h, withDensity_one]

/-- Hölder for the unweighted cell measure (`PairContAux.holder` with `m = 0`). -/
lemma holder0 {c : ℝ} {F G : ℝ × ℝ → ℂ} (hF : MemLp F 2 (B0579.cellMeasure c 0))
    (hG : MemLp G 2 (B0579.cellMeasure c 0)) :
    IntegrableOn (fun x => F x * G x) (B0579.cell c) ∧
      ‖∫ x in B0579.cell c, F x * G x‖ ≤
        (eLpNorm F 2 (B0579.cellMeasure c 0)).toReal *
          (eLpNorm G 2 (B0579.cellMeasure c 0)).toReal := by
  have h := PairContAux.holder (m := 0) hF (by rw [neg_zero]; exact hG)
  rw [neg_zero] at h
  exact h

lemma T_zero_off_box {c L : ℝ} {S : Set (ℝ × ℝ)} {T : ℝ × ℝ → ℝ × ℝ → ℂ}
    (hsupp : ∀ p ∈ S, ∀ x : ℝ × ℝ, L < |x.2| → T p x = 0) {p : ℝ × ℝ} (hp : p ∈ S)
    {x : ℝ × ℝ} (hx : x ∈ B0579.cell c) (hxK : x ∉ B0579.box c L) : T p x = 0 := by
  apply hsupp p hp x
  by_contra h
  exact hxK (B0579.mem_box_of_mem_cell hx (not_lt.1 h))

lemma T_cont {S : Set (ℝ × ℝ)} {T : ℝ × ℝ → ℝ × ℝ → ℂ}
    (hT : ContinuousOn (fun z : (ℝ × ℝ) × (ℝ × ℝ) => T z.1 z.2) (S ×ˢ Set.univ))
    {p : ℝ × ℝ} (hp : p ∈ S) : Continuous (T p) := by
  have h1 : ContinuousOn (fun x : ℝ × ℝ => T p x) univ :=
    hT.comp (continuous_const.prodMk continuous_id).continuousOn (fun x _ => ⟨hp, mem_univ x⟩)
  exact continuousOn_univ.1 h1

lemma memLp_T {c L M : ℝ} {S : Set (ℝ × ℝ)} {T : ℝ × ℝ → ℝ × ℝ → ℂ}
    (hsupp : ∀ p ∈ S, ∀ x : ℝ × ℝ, L < |x.2| → T p x = 0)
    (hbdd : ∀ p ∈ S, ∀ x : ℝ × ℝ, ‖T p x‖ ≤ M)
    (hT : ContinuousOn (fun z : (ℝ × ℝ) × (ℝ × ℝ) => T z.1 z.2) (S ×ˢ Set.univ))
    {p : ℝ × ℝ} (hp : p ∈ S) (hM : 0 ≤ M) :
    MemLp (T p) 2 (B0579.cellMeasure c 0) := by
  have hfin : B0579.cellMeasure c 0 (B0579.box c L) < ⊤ :=
    LadPRPairAux.cellMeasure_lt_top (B0579.isCompact_box c L)
  have hb : eLpNorm (T p) 2 (B0579.cellMeasure c 0) ≤
      ENNReal.ofReal M * (B0579.cellMeasure c 0 (B0579.box c L)) ^ (2⁻¹ : ℝ) :=
    LadPRPairAux.eLpNorm_le_of_bdd (B0579.isCompact_box c L) hM
      (fun x hx hxK => T_zero_off_box hsupp hp hx hxK) (fun x _ => hbdd p hp x)
  refine ⟨(T_cont hT hp).aestronglyMeasurable, ?_⟩
  exact lt_of_le_of_lt hb (lt_top_iff_ne_top.2
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hfin.ne)))

lemma toReal_T_le {c L M : ℝ} {S : Set (ℝ × ℝ)} {T : ℝ × ℝ → ℝ × ℝ → ℂ}
    (hsupp : ∀ p ∈ S, ∀ x : ℝ × ℝ, L < |x.2| → T p x = 0)
    (hbdd : ∀ p ∈ S, ∀ x : ℝ × ℝ, ‖T p x‖ ≤ M)
    (hT : ContinuousOn (fun z : (ℝ × ℝ) × (ℝ × ℝ) => T z.1 z.2) (S ×ˢ Set.univ))
    {p : ℝ × ℝ} (hp : p ∈ S) (hM : 0 ≤ M) :
    (eLpNorm (T p) 2 (B0579.cellMeasure c 0)).toReal ≤
      M * ((B0579.cellMeasure c 0 (B0579.box c L)).toReal) ^ (2⁻¹ : ℝ) := by
  have hfin : B0579.cellMeasure c 0 (B0579.box c L) < ⊤ :=
    LadPRPairAux.cellMeasure_lt_top (B0579.isCompact_box c L)
  have hb : eLpNorm (T p) 2 (B0579.cellMeasure c 0) ≤
      ENNReal.ofReal M * (B0579.cellMeasure c 0 (B0579.box c L)) ^ (2⁻¹ : ℝ) :=
    LadPRPairAux.eLpNorm_le_of_bdd (B0579.isCompact_box c L) hM
      (fun x hx hxK => T_zero_off_box hsupp hp hx hxK) (fun x _ => hbdd p hp x)
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hfin.ne)) hb
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM, ← ENNReal.toReal_rpow] at h
  exact h

end GCont1Aux

open GCont1Aux in
/-- Continuity of the parametric cell integral `p ↦ ∫_{C_c} F p · T p` on `S`. -/
theorem cell_integral_mul_continuousOn (c L M : ℝ) (S : Set (ℝ × ℝ)) (F T : ℝ × ℝ → ℝ × ℝ → ℂ) (hF : ∀ p ∈ S, MeasureTheory.MemLp (F p) 2 (MeasureTheory.volume.restrict (B0579.cell c))) (hFc : ∀ p0 ∈ S, Filter.Tendsto (fun p => MeasureTheory.eLpNorm (F p - F p0) 2 (MeasureTheory.volume.restrict (B0579.cell c))) (nhdsWithin p0 S) (nhds 0)) (hT : ContinuousOn (fun z : (ℝ × ℝ) × (ℝ × ℝ) => T z.1 z.2) (S ×ˢ Set.univ)) (hsupp : ∀ p ∈ S, ∀ x : ℝ × ℝ, L < |x.2| → T p x = 0) (hbdd : ∀ p ∈ S, ∀ x : ℝ × ℝ, ‖T p x‖ ≤ M) : ContinuousOn (fun p => ∫ x in B0579.cell c, F p x * T p x) S := by
  intro p0 hp0
  have hM : 0 ≤ M := (norm_nonneg _).trans (hbdd p0 hp0 0)
  have hKc : IsCompact (B0579.box c L) := B0579.isCompact_box c L
  have hfin : B0579.cellMeasure c 0 (B0579.box c L) < ⊤ :=
    LadPRPairAux.cellMeasure_lt_top hKc
  set A : ℝ := M * ((B0579.cellMeasure c 0 (B0579.box c L)).toReal) ^ (2⁻¹ : ℝ) with hA
  have hF0 : ∀ p ∈ S, MemLp (F p) 2 (B0579.cellMeasure c 0) := fun p hp => by
    rw [cellMeasure_zero]; exact hF p hp
  have hT0 : ∀ p ∈ S, MemLp (T p) 2 (B0579.cellMeasure c 0) := fun p hp =>
    memLp_T hsupp hbdd hT hp hM
  have hTb : ∀ p ∈ S, (eLpNorm (T p) 2 (B0579.cellMeasure c 0)).toReal ≤ A := fun p hp =>
    toReal_T_le hsupp hbdd hT hp hM
  -- `L²` continuity of `F` in the first slot, as a real function
  have hFc0 : Tendsto (fun p => (eLpNorm (F p - F p0) 2 (B0579.cellMeasure c 0)).toReal)
      (𝓝[S] p0) (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hFc p0 hp0)
    rw [ENNReal.toReal_zero] at h
    rw [cellMeasure_zero]
    exact h
  -- pointwise continuity of `T` along `S`
  have hTx : ∀ x : ℝ × ℝ, Tendsto (fun p => T p x) (𝓝[S] p0) (𝓝 (T p0 x)) := by
    intro x
    have h1 := hT.continuousWithinAt (x := (p0, x)) ⟨hp0, mem_univ x⟩
    have h2 : Tendsto (fun p : ℝ × ℝ => (p, x)) (𝓝[S] p0) (𝓝[S ×ˢ univ] (p0, x)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact (((continuous_id.prodMk continuous_const : Continuous fun p : ℝ × ℝ => (p, x))).tendsto p0).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with p hp using ⟨hp, mem_univ x⟩
    exact h1.tendsto.comp h2
  -- the cell integral of the difference
  have hind : MemLp (fun x => (B0579.box c L).indicator (fun _ => (1 : ℂ)) x) 2
      (B0579.cellMeasure c 0) :=
    memLp_indicator_const 2 hKc.isClosed.measurableSet (1 : ℂ) (Or.inr hfin.ne)
  have hdomint : Integrable (fun x => F p0 x * (B0579.box c L).indicator (fun _ => (1 : ℂ)) x)
      (volume.restrict (B0579.cell c)) := (holder0 (hF0 p0 hp0) hind).1
  have hbd : ∀ p ∈ S, ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
      ‖F p0 x * (T p x - T p0 x)‖ ≤
        2 * M * ‖F p0 x * (B0579.box c L).indicator (fun _ => (1 : ℂ)) x‖ := by
    intro p hp
    filter_upwards [ae_restrict_mem (B0579.measurableSet_cell c)] with x hx
    by_cases hxK : x ∈ B0579.box c L
    · have h1 : ‖T p x - T p0 x‖ ≤ 2 * M := by
        have := norm_sub_le (T p x) (T p0 x)
        linarith [hbdd p hp x, hbdd p0 hp0 x]
      simp only [Set.indicator_of_mem hxK, mul_one, norm_mul]
      calc ‖F p0 x‖ * ‖T p x - T p0 x‖ ≤ ‖F p0 x‖ * (2 * M) :=
            mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ = 2 * M * ‖F p0 x‖ := by ring
    · simp [T_zero_off_box hsupp hp hx hxK, T_zero_off_box hsupp hp0 hx hxK,
        Set.indicator_of_notMem hxK]
  have hterm2 : Tendsto (fun p => ∫ x in B0579.cell c, F p0 x * (T p x - T p0 x))
      (𝓝[S] p0) (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence
      (μ := volume.restrict (B0579.cell c))
      (F := fun p x => F p0 x * (T p x - T p0 x)) (f := fun _ => (0 : ℂ))
      (fun x => 2 * M * ‖F p0 x * (B0579.box c L).indicator (fun _ => (1 : ℂ)) x‖)
      (eventually_nhdsWithin_of_forall fun p hp =>
        ((hF p0 hp0).1.mul ((T_cont hT hp).sub (T_cont hT hp0)).aestronglyMeasurable))
      (eventually_nhdsWithin_of_forall fun p hp => hbd p hp)
      ((hdomint.norm).const_mul (2 * M))
      (Eventually.of_forall fun x => by
        have h1 := hTx x
        have h2 : Tendsto (fun p => F p0 x * (T p x - T p0 x)) (𝓝[S] p0)
            (𝓝 (F p0 x * (T p0 x - T p0 x))) :=
          (h1.sub tendsto_const_nhds).const_mul (F p0 x)
        simpa using h2)
    simpa using h
  have hterm1 : Tendsto (fun p => ∫ x in B0579.cell c, (F p x - F p0 x) * T p x)
      (𝓝[S] p0) (𝓝 0) := by
    have hg : Tendsto (fun p => (eLpNorm (F p - F p0) 2 (B0579.cellMeasure c 0)).toReal * A)
        (𝓝[S] p0) (𝓝 0) := by
      have h := hFc0.mul_const A
      simpa using h
    refine squeeze_zero_norm' ?_ hg
    filter_upwards [self_mem_nhdsWithin] with p hp
    have h := holder0 ((hF0 p hp).sub (hF0 p0 hp0)) (hT0 p hp)
    calc ‖∫ x in B0579.cell c, (F p x - F p0 x) * T p x‖
        ≤ (eLpNorm (F p - F p0) 2 (B0579.cellMeasure c 0)).toReal *
            (eLpNorm (T p) 2 (B0579.cellMeasure c 0)).toReal := h.2
      _ ≤ (eLpNorm (F p - F p0) 2 (B0579.cellMeasure c 0)).toReal * A :=
            mul_le_mul_of_nonneg_left (hTb p hp) ENNReal.toReal_nonneg
  have hsum : Tendsto (fun p => (∫ x in B0579.cell c, F p x * T p x) -
      ∫ x in B0579.cell c, F p0 x * T p0 x) (𝓝[S] p0) (𝓝 0) := by
    have h := hterm1.add hterm2
    rw [add_zero] at h
    refine Tendsto.congr' ?_ h
    filter_upwards [self_mem_nhdsWithin] with p hp
    have i1 := (holder0 ((hF0 p hp).sub (hF0 p0 hp0)) (hT0 p hp)).1
    have i2 := (holder0 (hF0 p0 hp0) ((hT0 p hp).sub (hT0 p0 hp0))).1
    have i3 := (holder0 (hF0 p hp) (hT0 p hp)).1
    have i4 := (holder0 (hF0 p0 hp0) (hT0 p0 hp0)).1
    simp only [Pi.sub_apply] at i1 i2
    rw [← integral_add i1 i2, ← integral_sub i3 i4]
    congr 1
    funext x
    ring
  exact tendsto_sub_nhds_zero_iff.1 hsum
