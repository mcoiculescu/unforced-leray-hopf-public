import UnforcedLeray.Short.PartIIb.Tasks.GlobalEnergy.Continuation.HorizonGluing.EarlyTrace

/-!
# `PartII-b:F7/2/2`: Meridional Horizon Gluing (`MeridionalHorizonGluing`)

Source of record: `the November 2 reference manuscript` (SP), lines 2213–2217 and
2289–2295 (`LinearGlue.MeridionalHorizonGluing`).

Combines:
1. `HorizonGluingAux.exists_early_horizon_rep` (`HorizonGluing/EarlyTrace.lean`), which extracts a
   strongly measurable, everywhere `p.c`-periodic `C((0, T]; H¹_σ(C_c))` representative
   `(z₁, zq₁, zη₁)` of `(z_eb, zq_eb, zη_eb)` on `(0, T]` with an `IsCylH1Slice` horizon trace at
   `s = T`; and
2. a smooth three-way partition of unity `etaL + theta + etaR = 1` in `s` around `s = T`, using
   continuity of the glued `L²(C_c)` slice path across `s = T` (`z₂(T) = z₁(T)` in `H¹(C_c)`) and
   vanishing mean `∫_{T - ε}^{T + ε} theta'(s) ds = 0` to cancel the horizon seam term and produce
   `IsGlobalMeridionalCorrection` on `(0, ∞)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff RealInnerProductSpace

namespace UnforcedLeray.Short.IIb.HorizonGluingAux

open UnforcedLeray.Cons.C03.Concrete
open UnforcedLeray.Short.IIb
open UnforcedLeray.Short.IIIa

/-! ### 1. Measurability, periodicity, and local `H¹(C_c)` bounds for `glueAtHorizon` -/

private lemma stronglyMeasurable_glue (T : ℝ) {w₁ w₂ : CProf}
    (hw₁ : StronglyMeasurable w₁) (hw₂ : StronglyMeasurable w₂) :
    StronglyMeasurable (glueAtHorizon T w₁ w₂) := by
  have heq : glueAtHorizon T w₁ w₂ = Set.piecewise {x : Coord | x.1 ≤ T} w₁ w₂ := by
    funext x; simp [glueAtHorizon, Set.piecewise]
  rw [heq]
  exact StronglyMeasurable.piecewise (measurableSet_le measurable_fst measurable_const) hw₁ hw₂

private lemma qPeriodic_glue (c T : ℝ) {w₁ w₂ : CProf}
    (hw₁ : ∀ x : Coord, w₁ (qShift c x) = w₁ x)
    (hw₂ : ∀ᵐ x : Coord, T < x.1 → w₂ (qShift c x) = w₂ x) :
    QPeriodic c (glueAtHorizon T w₁ w₂) := by
  refine QPerHalf.of_ae_imp ?_
  filter_upwards [hw₂] with x hx₂ _hp
  by_cases hx : x.1 ≤ T
  · simp [glueAtHorizon, hx, hw₁ x]
  · simp [glueAtHorizon, hx, hx₂ (not_le.1 hx)]

private lemma sliceMeas {w : CProf} (hw : StronglyMeasurable w) (s : ℝ) :
    StronglyMeasurable (fun y : B0579.Plane => w (s, y)) :=
  hw.comp_measurable (measurable_const.prodMk measurable_id)

private lemma compMeas {α : Type*} [MeasurableSpace α] {w : α → CMerid}
    (hw : StronglyMeasurable w) (i : Fin 2) :
    StronglyMeasurable (fun x => w x i) :=
  (EuclideanSpace.proj (𝕜 := ℂ) i).continuous.comp_stronglyMeasurable hw

private lemma cylSliceL2_sub_symm (c : ℝ) (u v : B0579.Plane → CMerid) :
    cylSliceL2 c (fun y => u y - v y) = cylSliceL2 c (fun y => v y - u y) :=
  eLpNorm_congr_norm_ae (Eventually.of_forall fun y => norm_sub_rev (u y) (v y))

private lemma cylSliceH1_sub_symm (c : ℝ)
    (u uq uη v vq vη : B0579.Plane → CMerid) :
    cylSliceH1 c (fun y => u y - v y) (fun y => uq y - vq y) (fun y => uη y - vη y) =
      cylSliceH1 c (fun y => v y - u y) (fun y => vq y - uq y) (fun y => vη y - uη y) := by
  simp only [cylSliceH1, cylSliceL2_sub_symm c u v,
    cylSliceL2_sub_symm c uq vq, cylSliceL2_sub_symm c uη vη]

private lemma cylSliceL2_le_add_sub (c : ℝ) {u v : B0579.Plane → CMerid}
    (hu : StronglyMeasurable u) (hv : StronglyMeasurable v) :
    cylSliceL2 c u ≤ cylSliceL2 c v + cylSliceL2 c (fun y => u y - v y) := by
  have heq : u = v + (u - v) := by funext y; simp
  have h := eLpNorm_add_le (μ := volume.restrict (B0579.cell c)) (p := 2)
    hv.aestronglyMeasurable (hu.sub hv).aestronglyMeasurable (by norm_num)
  rw [← heq] at h
  exact h

private lemma add6_rearrange (a b c d e f : ℝ≥0∞) :
    (a + b) + (c + d) + (e + f) = (a + c + e) + (b + d + f) := by
  simp only [add_left_comm, add_comm]

private lemma sliceH1Norm_le_add_cylSliceH1 (c : ℝ) {u uq uη v vq vη : CProf}
    (hu : StronglyMeasurable u) (huq : StronglyMeasurable uq) (huη : StronglyMeasurable uη)
    (hv : StronglyMeasurable v) (hvq : StronglyMeasurable vq) (hvη : StronglyMeasurable vη)
    (s t : ℝ) :
    sliceH1Norm c u uq uη s ≤ sliceH1Norm c v vq vη t +
      cylSliceH1 c (fun y => u (s, y) - v (t, y))
        (fun y => uq (s, y) - vq (t, y)) (fun y => uη (s, y) - vη (t, y)) := by
  have h1 := cylSliceL2_le_add_sub c (sliceMeas hu s) (sliceMeas hv t)
  have h2 := cylSliceL2_le_add_sub c (sliceMeas huq s) (sliceMeas hvq t)
  have h3 := cylSliceL2_le_add_sub c (sliceMeas huη s) (sliceMeas hvη t)
  exact (add_le_add (add_le_add h1 h2) h3).trans_eq (add6_rearrange _ _ _ _ _ _)

private lemma exists_tail_sliceH1Norm_bound {c T M : ℝ} (hM : 0 ≤ M)
    {z₁ zq₁ zη₁ z₂ zq₂ zη₂ : CProf}
    (hz₁ : StronglyMeasurable z₁) (hzq₁ : StronglyMeasurable zq₁) (hzη₁ : StronglyMeasurable zη₁)
    (hz₂ : StronglyMeasurable z₂) (hzq₂ : StronglyMeasurable zq₂) (hzη₂ : StronglyMeasurable zη₂)
    (hT₁ : sliceH1Norm c z₁ zq₁ zη₁ T ≤ ENNReal.ofReal (3 * M))
    (hmatch : cylSliceH1 c (fun y => z₂ (T, y) - z₁ (T, y))
      (fun y => zq₂ (T, y) - zq₁ (T, y)) (fun y => zη₂ (T, y) - zη₁ (T, y)) = 0)
    (hcont₂ : ∀ s : ℝ, T ≤ s →
      Tendsto (fun s' => cylSliceH1 c
        (fun y => z₂ (s', y) - z₂ (s, y))
        (fun y => zq₂ (s', y) - zq₂ (s, y))
        (fun y => zη₂ (s', y) - zη₂ (s, y))) (𝓝[Ici T] s) (𝓝 0))
    {b : ℝ} (hb : T ≤ b) :
    ∃ M₂ : ℝ, 0 ≤ M₂ ∧ ∀ s ∈ Icc T b, sliceH1Norm c z₂ zq₂ zη₂ s ≤ ENNReal.ofReal M₂ := by
  have hT₂ : sliceH1Norm c z₂ zq₂ zη₂ T ≤ ENNReal.ofReal (3 * M) := by
    have hle := sliceH1Norm_le_add_cylSliceH1 c hz₂ hzq₂ hzη₂ hz₁ hzq₁ hzη₁ T T
    rw [hmatch, add_zero] at hle
    exact hle.trans hT₁
  let S : Set ℝ := {s : ℝ | s ∈ Icc T b ∧
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r ∈ Icc T s, sliceH1Norm c z₂ zq₂ zη₂ r ≤ ENNReal.ofReal K}
  have hT_S : T ∈ S := ⟨⟨le_rfl, hb⟩, 3 * M, by positivity, fun r hr => by
    rw [le_antisymm hr.2 hr.1]; exact hT₂⟩
  have hS_bdd : BddAbove S := ⟨b, fun s hs => hs.1.2⟩
  set sStar := sSup S
  have hsStar_T : T ≤ sStar := le_csSup hS_bdd hT_S
  have hsStar_b : sStar ≤ b := csSup_le ⟨T, hT_S⟩ fun s hs => hs.1.2
  have hnear := (ENNReal.tendsto_nhds_zero.1 (hcont₂ sStar hsStar_T))
    (ENNReal.ofReal 1) (by simp)
  obtain ⟨U, hU_nhds, hU_sub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hnear
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hU_nhds
  obtain ⟨s₁, hs₁_S, hs₁_gt⟩ :=
    exists_lt_of_lt_csSup ⟨T, hT_S⟩ (sub_lt_self sStar (half_pos hδ))
  have hs₁_le : s₁ ≤ sStar := le_csSup hS_bdd hs₁_S
  obtain ⟨hs₁_cc, K₁, hK₁_nn, hK₁⟩ := hs₁_S
  have hs₁_ball : s₁ ∈ Metric.ball sStar δ := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith, by linarith⟩
  have hd_s₁ : cylSliceH1 c (fun y => z₂ (s₁, y) - z₂ (sStar, y))
      (fun y => zq₂ (s₁, y) - zq₂ (sStar, y))
      (fun y => zη₂ (s₁, y) - zη₂ (sStar, y)) ≤ ENNReal.ofReal 1 :=
    hU_sub ⟨hball hs₁_ball, hs₁_cc.1⟩
  have hsStar_bound : sliceH1Norm c z₂ zq₂ zη₂ sStar ≤ ENNReal.ofReal (K₁ + 1) := by
    calc sliceH1Norm c z₂ zq₂ zη₂ sStar
        ≤ sliceH1Norm c z₂ zq₂ zη₂ s₁ +
            cylSliceH1 c (fun y => z₂ (sStar, y) - z₂ (s₁, y))
              (fun y => zq₂ (sStar, y) - zq₂ (s₁, y))
              (fun y => zη₂ (sStar, y) - zη₂ (s₁, y)) :=
          sliceH1Norm_le_add_cylSliceH1 c hz₂ hzq₂ hzη₂ hz₂ hzq₂ hzη₂ sStar s₁
      _ = sliceH1Norm c z₂ zq₂ zη₂ s₁ +
            cylSliceH1 c (fun y => z₂ (s₁, y) - z₂ (sStar, y))
              (fun y => zq₂ (s₁, y) - zq₂ (sStar, y))
              (fun y => zη₂ (s₁, y) - zη₂ (sStar, y)) := by
          rw [cylSliceH1_sub_symm]
      _ ≤ ENNReal.ofReal K₁ + ENNReal.ofReal 1 :=
          add_le_add (hK₁ s₁ ⟨hs₁_cc.1, le_rfl⟩) hd_s₁
      _ = ENNReal.ofReal (K₁ + 1) := (ENNReal.ofReal_add hK₁_nn zero_le_one).symm
  set s₂ := min b (sStar + δ / 2)
  have hs₂_S : s₂ ∈ S := by
    refine ⟨⟨le_min hb (by linarith), min_le_left _ _⟩, K₁ + 2, by positivity, fun r hr => ?_⟩
    by_cases hr₁ : r ≤ s₁
    · exact (hK₁ r ⟨hr.1, hr₁⟩).trans (ENNReal.ofReal_le_ofReal (by linarith))
    · have hr_gt : s₁ < r := not_le.1 hr₁
      have hr_le : r ≤ sStar + δ / 2 := hr.2.trans (min_le_right _ _)
      have hr_ball : r ∈ Metric.ball sStar δ := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        exact ⟨by linarith, by linarith⟩
      have hd_r : cylSliceH1 c (fun y => z₂ (r, y) - z₂ (sStar, y))
          (fun y => zq₂ (r, y) - zq₂ (sStar, y))
          (fun y => zη₂ (r, y) - zη₂ (sStar, y)) ≤ ENNReal.ofReal 1 :=
        hU_sub ⟨hball hr_ball, hr.1⟩
      calc sliceH1Norm c z₂ zq₂ zη₂ r
          ≤ sliceH1Norm c z₂ zq₂ zη₂ sStar +
              cylSliceH1 c (fun y => z₂ (r, y) - z₂ (sStar, y))
                (fun y => zq₂ (r, y) - zq₂ (sStar, y))
                (fun y => zη₂ (r, y) - zη₂ (sStar, y)) :=
            sliceH1Norm_le_add_cylSliceH1 c hz₂ hzq₂ hzη₂ hz₂ hzq₂ hzη₂ r sStar
        _ ≤ ENNReal.ofReal (K₁ + 1) + ENNReal.ofReal 1 := add_le_add hsStar_bound hd_r
        _ = ENNReal.ofReal (K₁ + 2) := by
            rw [← ENNReal.ofReal_add (by positivity) zero_le_one]; ring_nf
  have hs₂_le : s₂ ≤ sStar := le_csSup hS_bdd hs₂_S
  have hb_le_sStar : b ≤ sStar := by
    rcases min_le_iff.1 hs₂_le with h | h
    · exact h
    · linarith
  have hs₂_eq_b : s₂ = b := min_eq_left (by linarith)
  have hb_S : b ∈ S := hs₂_eq_b ▸ hs₂_S
  exact hb_S.2

private lemma exists_glued_sliceH1Norm_bound {c T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M)
    {z₁ zq₁ zη₁ z₂ zq₂ zη₂ : CProf}
    (hz₁ : StronglyMeasurable z₁) (hzq₁ : StronglyMeasurable zq₁) (hzη₁ : StronglyMeasurable zη₁)
    (hz₂ : StronglyMeasurable z₂) (hzq₂ : StronglyMeasurable zq₂) (hzη₂ : StronglyMeasurable zη₂)
    (hbdd₁ : ∀ s ∈ Ioc 0 T, sliceH1Norm c z₁ zq₁ zη₁ s ≤ ENNReal.ofReal (3 * M))
    (hmatch : cylSliceH1 c (fun y => z₂ (T, y) - z₁ (T, y))
      (fun y => zq₂ (T, y) - zq₁ (T, y)) (fun y => zη₂ (T, y) - zη₁ (T, y)) = 0)
    (hcont₂ : ∀ s : ℝ, T ≤ s →
      Tendsto (fun s' => cylSliceH1 c
        (fun y => z₂ (s', y) - z₂ (s, y))
        (fun y => zq₂ (s', y) - zq₂ (s, y))
        (fun y => zη₂ (s', y) - zη₂ (s, y))) (𝓝[Ici T] s) (𝓝 0))
    {a b : ℝ} (ha : 0 < a) (_hab : a ≤ b) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Icc a b,
      sliceH1Norm c (glueAtHorizon T z₁ z₂)
        (glueAtHorizon T zq₁ zq₂) (glueAtHorizon T zη₁ zη₂) s ≤ ENNReal.ofReal K := by
  obtain ⟨M₂, _hM₂_nn, hM₂⟩ := exists_tail_sliceH1Norm_bound hM hz₁ hzq₁ hzη₁ hz₂ hzq₂ hzη₂
    (hbdd₁ T ⟨hT, le_rfl⟩) hmatch hcont₂ (le_max_left T b)
  refine ⟨max (3 * M) M₂, le_trans (by positivity) (le_max_left _ _), fun s hs => ?_⟩
  by_cases hsT : s ≤ T
  · have h_eq : sliceH1Norm c (glueAtHorizon T z₁ z₂)
        (glueAtHorizon T zq₁ zq₂) (glueAtHorizon T zη₁ zη₂) s = sliceH1Norm c z₁ zq₁ zη₁ s := by
      simp [sliceH1Norm, glueAtHorizon, hsT]
    rw [h_eq]
    exact (hbdd₁ s ⟨lt_of_lt_of_le ha hs.1, hsT⟩).trans
      (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  · have hgt : T < s := not_le.1 hsT
    have h_eq : sliceH1Norm c (glueAtHorizon T z₁ z₂)
        (glueAtHorizon T zq₁ zq₂) (glueAtHorizon T zη₁ zη₂) s = sliceH1Norm c z₂ zq₂ zη₂ s := by
      simp [sliceH1Norm, glueAtHorizon, hsT]
    rw [h_eq]
    exact (hM₂ s ⟨hgt.le, hs.2.trans (le_max_right T b)⟩).trans
      (ENNReal.ofReal_le_ofReal (le_max_right _ _))

/-! ### 2. Two-sided `L²(C_c)` continuity at `s = T` and seam pairing continuity -/

private lemma ofReal_norm_cprofToLMH_sub {c : ℝ} {u v : CProf} {s t : ℝ}
    (hu : MemLp (fun y => u (s, y)) 2 (volume.restrict (B0579.cell c)))
    (hv : MemLp (fun y => v (t, y)) 2 (volume.restrict (B0579.cell c))) :
    ENNReal.ofReal ‖cprofToLMH c u s - cprofToLMH c v t‖ =
      cylSliceL2 c (fun y => u (s, y) - v (t, y)) := by
  symm
  refine cylSliceL2_eq_ofReal_norm ?_
  filter_upwards [cprofToLMH_ae_of_memLp hu, cprofToLMH_ae_of_memLp hv,
    Lp.coeFn_sub (cprofToLMH c u s) (cprofToLMH c v t)] with y hyu hyv hsub
  rw [hsub, Pi.sub_apply, hyu, hyv, lmToCMerid_sub, lmToCMerid_cmeridToLM, lmToCMerid_cmeridToLM]

private lemma memLp_z_of_sliceH1Norm_lt_top {c : ℝ} {z zq zη : CProf}
    (hz : StronglyMeasurable z) {s : ℝ} (hfin : sliceH1Norm c z zq zη s < ⊤) :
    MemLp (fun y => z (s, y)) 2 (volume.restrict (B0579.cell c)) :=
  ⟨(sliceMeas hz s).aestronglyMeasurable,
    ((le_add_of_nonneg_right zero_le).trans (le_add_of_nonneg_right zero_le)).trans_lt hfin⟩

private lemma continuousAt_cprofToLMH_glue {c T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M)
    {z₁ zq₁ zη₁ z₂ zq₂ zη₂ : CProf}
    (hz₁ : StronglyMeasurable z₁) (hzq₁ : StronglyMeasurable zq₁) (hzη₁ : StronglyMeasurable zη₁)
    (hz₂ : StronglyMeasurable z₂) (hzq₂ : StronglyMeasurable zq₂) (hzη₂ : StronglyMeasurable zη₂)
    (hbdd₁ : ∀ s ∈ Ioc 0 T, sliceH1Norm c z₁ zq₁ zη₁ s ≤ ENNReal.ofReal (3 * M))
    (hcont₁ : ∀ s ∈ Ioc 0 T,
      Tendsto (fun s' => cylSliceH1 c
        (fun y => z₁ (s', y) - z₁ (s, y))
        (fun y => zq₁ (s', y) - zq₁ (s, y))
        (fun y => zη₁ (s', y) - zη₁ (s, y))) (𝓝[Ioc 0 T] s) (𝓝 0))
    (hmatch : cylSliceH1 c (fun y => z₂ (T, y) - z₁ (T, y))
      (fun y => zq₂ (T, y) - zq₁ (T, y)) (fun y => zη₂ (T, y) - zη₁ (T, y)) = 0)
    (hcont₂ : ∀ s : ℝ, T ≤ s →
      Tendsto (fun s' => cylSliceH1 c
        (fun y => z₂ (s', y) - z₂ (s, y))
        (fun y => zq₂ (s', y) - zq₂ (s, y))
        (fun y => zη₂ (s', y) - zη₂ (s, y))) (𝓝[Ici T] s) (𝓝 0)) :
    ContinuousAt (cprofToLMH c (glueAtHorizon T z₁ z₂)) T := by
  set Z := glueAtHorizon T z₁ z₂
  set Zq := glueAtHorizon T zq₁ zq₂
  set Zη := glueAtHorizon T zη₁ zη₂
  have hZ_sm : StronglyMeasurable Z := stronglyMeasurable_glue T hz₁ hz₂
  obtain ⟨K, _hK_nn, hK⟩ := exists_glued_sliceH1Norm_bound hT hM hz₁ hzq₁ hzη₁ hz₂ hzq₂ hzη₂
    hbdd₁ hmatch hcont₂ (a := T / 2) (b := T + 1) (half_pos hT) (by linarith)
  have hZ_mem : ∀ s ∈ Icc (T / 2) (T + 1),
      MemLp (fun y => Z (s, y)) 2 (volume.restrict (B0579.cell c)) := fun s hs =>
    memLp_z_of_sliceH1Norm_lt_top hZ_sm ((hK s hs).trans_lt ENNReal.ofReal_lt_top)
  have hT_cc : T ∈ Icc (T / 2) (T + 1) := ⟨by linarith, by linarith⟩
  have hmatch_z : cylSliceL2 c (fun y => z₂ (T, y) - z₁ (T, y)) = 0 := by
    refine le_antisymm ?_ zero_le
    rw [← hmatch]
    exact (le_add_of_nonneg_right zero_le).trans (le_add_of_nonneg_right zero_le)
  rw [continuousAt_iff_continuous_left_right]
  refine ⟨?_, ?_⟩
  · rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
    have hmem_Iic : Icc (T / 2) T ∈ 𝓝[Iic T] T :=
      Filter.mem_of_superset
        (inter_mem (nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds (half_lt_self hT))) self_mem_nhdsWithin)
        fun s hs => ⟨hs.1.le, hs.2⟩
    have hsub_Ioc : Icc (T / 2) T ⊆ Ioc 0 T := fun s hs => ⟨lt_of_lt_of_le (half_pos hT) hs.1, hs.2⟩
    have henn : Tendsto (fun s' => ENNReal.ofReal ‖cprofToLMH c Z s' - cprofToLMH c Z T‖)
        (𝓝[Iic T] T) (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        ((hcont₁ T ⟨hT, le_rfl⟩).mono_left
          (nhdsWithin_le_iff.2 (Filter.mem_of_superset hmem_Iic hsub_Ioc)))
        (Eventually.of_forall fun _ => zero_le) ?_
      filter_upwards [hmem_Iic] with s' hs'
      have hs'_cc : s' ∈ Icc (T / 2) (T + 1) := ⟨hs'.1, hs'.2.trans (by linarith)⟩
      rw [ofReal_norm_cprofToLMH_sub (hZ_mem s' hs'_cc) (hZ_mem T hT_cc)]
      have heq_s' : (fun y => Z (s', y) - Z (T, y)) = fun y => z₁ (s', y) - z₁ (T, y) := by
        funext y; simp [Z, glueAtHorizon, hs'.2]
      rw [heq_s']
      exact (le_add_of_nonneg_right zero_le).trans (le_add_of_nonneg_right zero_le)
    have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp henn
    rw [ENNReal.toReal_zero] at hreal
    exact hreal.congr fun s' => ENNReal.toReal_ofReal (norm_nonneg _)
  · rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
    have hmem_Ici : Icc T (T + 1) ∈ 𝓝[Ici T] T :=
      Filter.mem_of_superset
        (inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (isOpen_Iio.mem_nhds (lt_add_one T))))
        fun s hs => ⟨hs.1, hs.2.le⟩
    have henn : Tendsto (fun s' => ENNReal.ofReal ‖cprofToLMH c Z s' - cprofToLMH c Z T‖)
        (𝓝[Ici T] T) (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (hcont₂ T le_rfl) (Eventually.of_forall fun _ => zero_le) ?_
      filter_upwards [hmem_Ici] with s' hs'
      have hs'_cc : s' ∈ Icc (T / 2) (T + 1) := ⟨(by linarith : T / 2 ≤ T).trans hs'.1, hs'.2⟩
      rw [ofReal_norm_cprofToLMH_sub (hZ_mem s' hs'_cc) (hZ_mem T hT_cc)]
      by_cases hTs' : s' ≤ T
      · have h_eq : s' = T := le_antisymm hTs' hs'.1
        subst h_eq
        simp [cylSliceL2]
      · have heq_s' : (fun y => Z (s', y) - Z (T, y)) = fun y => z₂ (s', y) - z₁ (T, y) := by
          funext y; simp [Z, glueAtHorizon, hTs']
        rw [heq_s']
        have htri : cylSliceL2 c (fun y => z₂ (s', y) - z₁ (T, y)) ≤
            cylSliceL2 c (fun y => z₂ (s', y) - z₂ (T, y)) +
              cylSliceL2 c (fun y => z₂ (T, y) - z₁ (T, y)) := by
          have hsum : (fun y => z₂ (s', y) - z₁ (T, y)) =
              (fun y => z₂ (s', y) - z₂ (T, y)) + (fun y => z₂ (T, y) - z₁ (T, y)) := by
            funext y; simp
          unfold cylSliceL2
          rw [hsum]
          exact eLpNorm_add_le
            ((sliceMeas hz₂ s').sub (sliceMeas hz₂ T)).aestronglyMeasurable
            ((sliceMeas hz₂ T).sub (sliceMeas hz₁ T)).aestronglyMeasurable (by norm_num)
        rw [hmatch_z, add_zero] at htri
        exact htri.trans
          ((le_add_of_nonneg_right zero_le).trans (le_add_of_nonneg_right zero_le))
    have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp henn
    rw [ENNReal.toReal_zero] at hreal
    exact hreal.congr fun s' => ENNReal.toReal_ofReal (norm_nonneg _)

private lemma norm_toLMH_vecRe_sub_sq' {c : ℝ} {φ₁ φ₂ : ℝ × ℝ → Fin 2 → ℝ}
    (h1 : ∀ i : Fin 2, MemLp (fun y => φ₁ y i) 2 (volume.restrict (B0579.cell c)))
    (h2 : ∀ i : Fin 2, MemLp (fun y => φ₂ y i) 2 (volume.restrict (B0579.cell c))) :
    ‖toLMH (vecRe φ₁) (vecRe_cellL2 h1) - toLMH (vecRe φ₂) (vecRe_cellL2 h2)‖ ^ 2 =
      ∫ y in B0579.cell c, ∑ i : Fin 2, (φ₁ y i - φ₂ y i) ^ 2 := by
  have hsub : ∀ i : Fin 2, MemLp (fun y => φ₁ y i - φ₂ y i) 2 (volume.restrict (B0579.cell c)) :=
    fun i => (h1 i).sub (h2 i)
  have heq : toLMH (vecRe φ₁) (vecRe_cellL2 h1) - toLMH (vecRe φ₂) (vecRe_cellL2 h2) =
      toLMH (vecRe fun y i => φ₁ y i - φ₂ y i) (vecRe_cellL2 hsub) := by
    apply Lp.ext_iff.2
    filter_upwards [Lp.coeFn_sub (toLMH (vecRe φ₁) (vecRe_cellL2 h1))
        (toLMH (vecRe φ₂) (vecRe_cellL2 h2)),
      toLMH_ae (vecRe_cellL2 h1), toLMH_ae (vecRe_cellL2 h2),
      toLMH_ae (vecRe_cellL2 hsub)] with y hys hy1 hy2 hy3
    rw [hys, Pi.sub_apply, hy1, hy2, hy3, ← lmReal_sub]
    congr 1; ext i; simp [vecRe]
  rw [heq, norm_toLMH_sq]
  refine integral_congr_ae (ae_of_all _ fun y => Finset.sum_congr rfl fun i _ => ?_)
  dsimp [vecRe]
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

private lemma norm_toLMH_vecIm_sub_sq' {c : ℝ} {φ₁ φ₂ : ℝ × ℝ → Fin 2 → ℝ}
    (h1 : ∀ i : Fin 2, MemLp (fun y => φ₁ y i) 2 (volume.restrict (B0579.cell c)))
    (h2 : ∀ i : Fin 2, MemLp (fun y => φ₂ y i) 2 (volume.restrict (B0579.cell c))) :
    ‖toLMH (vecIm φ₁) (vecIm_cellL2 h1) - toLMH (vecIm φ₂) (vecIm_cellL2 h2)‖ ^ 2 =
      ∫ y in B0579.cell c, ∑ i : Fin 2, (φ₁ y i - φ₂ y i) ^ 2 := by
  have hsub : ∀ i : Fin 2, MemLp (fun y => φ₁ y i - φ₂ y i) 2 (volume.restrict (B0579.cell c)) :=
    fun i => (h1 i).sub (h2 i)
  have heq : toLMH (vecIm φ₁) (vecIm_cellL2 h1) - toLMH (vecIm φ₂) (vecIm_cellL2 h2) =
      toLMH (vecIm fun y i => φ₁ y i - φ₂ y i) (vecIm_cellL2 hsub) := by
    apply Lp.ext_iff.2
    filter_upwards [Lp.coeFn_sub (toLMH (vecIm φ₁) (vecIm_cellL2 h1))
        (toLMH (vecIm φ₂) (vecIm_cellL2 h2)),
      toLMH_ae (vecIm_cellL2 h1), toLMH_ae (vecIm_cellL2 h2),
      toLMH_ae (vecIm_cellL2 hsub)] with y hys hy1 hy2 hy3
    rw [hys, Pi.sub_apply, hy1, hy2, hy3, ← lmReal_sub]
    congr 1; ext i; dsimp [vecIm]; push_cast; ring
  rw [heq, norm_toLMH_sq]
  refine integral_congr_ae (ae_of_all _ fun y => Finset.sum_congr rfl fun i _ => ?_)
  dsimp [vecIm]
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]

private lemma tendsto_qPeriodize_sq_cell {c T : ℝ} (hc : 0 < c)
    {Ψ : Coord → Fin 2 → ℝ} (hΨ : IsPlanarSolTest Ψ) :
    Tendsto (fun s => ∫ y in B0579.cell c,
        ∑ i : Fin 2, (TailPeriodizeAux.qPeriodize c (fun x => Ψ x i) s y -
          TailPeriodizeAux.qPeriodize c (fun x => Ψ x i) T y) ^ 2)
      (𝓝 T) (𝓝 0) := by
  obtain ⟨_a0, _b0, R0, _ha0, _hab0, hR0, hbox0⟩ := TailPeriodizeAux.coordTest_box (hΨ.smooth 0)
  obtain ⟨_a1, _b1, R1, _ha1, _hab1, _hR1, hbox1⟩ := TailPeriodizeAux.coordTest_box (hΨ.smooth 1)
  set R := max R0 R1
  have hR_pos : 0 < R := lt_of_lt_of_le hR0 (le_max_left _ _)
  have hΨ_zero : ∀ (i : Fin 2) (x : Coord), (R < |x.2.1| ∨ R < |x.2.2|) → Ψ x i = 0 := by
    intro i x hx
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases hi with rfl | rfl
    · refine (hbox0 x (Or.inr ?_)).1
      rcases hx with hq | hη
      · exact Or.inl ((le_max_left R0 R1).trans_lt hq)
      · exact Or.inr ((le_max_left R0 R1).trans_lt hη)
    · refine (hbox1 x (Or.inr ?_)).1
      rcases hx with hq | hη
      · exact Or.inl ((le_max_right R0 R1).trans_lt hq)
      · exact Or.inr ((le_max_right R0 R1).trans_lt hη)
  obtain ⟨N, hN⟩ := exists_nat_gt ((c / 2 + R) / c + 1)
  let S : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  have hfin_eq : ∀ (s : ℝ) (y : B0579.Plane) (i : Fin 2), y ∈ B0579.cell c →
      TailPeriodizeAux.qPeriodize c (fun x => Ψ x i) s y =
        ∑ k ∈ S, Ψ (s, (y.1 + (k : ℝ) * c, y.2)) i := by
    intro s y i hy
    have hy1 : |y.1| ≤ c / 2 := abs_le.2 ⟨hy.1.1, hy.1.2.le⟩
    refine tsum_eq_sum fun k hk => hΨ_zero i _ (Or.inl ?_)
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hk
    have hk_abs : (N : ℝ) + 1 ≤ |(k : ℝ)| := by
      have hk_int : (N : ℤ) + 1 ≤ |k| := by
        rcases hk with hk | hk
        · rw [abs_of_neg (by omega)]; omega
        · rw [abs_of_nonneg (by omega)]; omega
      have hk_r : ((N : ℤ) + 1 : ℝ) ≤ (|k| : ℝ) := by exact_mod_cast hk_int
      simpa [Int.cast_abs] using hk_r
    have h1 : c / 2 + R + c < ((N : ℝ) + 1) * c := by
      have hm := mul_lt_mul_of_pos_right hN hc
      have hdiv : ((c / 2 + R) / c + 1) * c = c / 2 + R + c := by field_simp [hc.ne']
      linarith
    have h2 : ((N : ℝ) + 1) * c ≤ |(k : ℝ)| * c := mul_le_mul_of_nonneg_right hk_abs hc.le
    have h3 : |(k : ℝ)| * c - |y.1| ≤ |y.1 + (k : ℝ) * c| := by
      have hsub := abs_sub_abs_le_abs_add ((k : ℝ) * c) y.1
      rw [add_comm, abs_mul, abs_of_pos hc] at hsub
      linarith
    linarith
  have hzero_η : ∀ (s : ℝ) (y : B0579.Plane) (i : Fin 2), R < |y.2| →
      TailPeriodizeAux.qPeriodize c (fun x => Ψ x i) s y = 0 := by
    intro s y i hη
    unfold TailPeriodizeAux.qPeriodize
    have h0 : (fun k : ℤ => Ψ (s, (y.1 + (k : ℝ) * c, y.2)) i) = fun _ => 0 :=
      funext fun k => hΨ_zero i _ (Or.inr hη)
    rw [h0, tsum_zero]
  set cellR : Set B0579.Plane := Ico (-(c / 2)) (c / 2) ×ˢ Icc (-R) R
  have hcellR_meas : MeasurableSet cellR := measurableSet_Ico.prod measurableSet_Icc
  have hcellR_sub : cellR ⊆ B0579.cell c := prod_mono Subset.rfl (subset_univ _)
  have hcellR_fin : volume cellR < ⊤ := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, Real.volume_Icc]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have huc0 : UniformContinuous (fun x => Ψ x 0) :=
    (hΨ.smooth 0).compact.uniformContinuous_of_continuous (hΨ.smooth 0).smooth.continuous
  have huc1 : UniformContinuous (fun x => Ψ x 1) :=
    (hΨ.smooth 1).compact.uniformContinuous_of_continuous (hΨ.smooth 1).smooth.continuous
  rw [Metric.tendsto_nhds]
  intro ε hε
  set Kcard : ℝ := (S.card : ℝ) + 1
  have hKcard_pos : 0 < Kcard := by dsimp [Kcard]; positivity
  set Vreal : ℝ := volume.real cellR + 1
  have hVreal_pos : 0 < Vreal := add_pos_of_nonneg_of_pos measureReal_nonneg one_pos
  set δ := Real.sqrt (ε / (4 * Kcard ^ 2 * Vreal))
  have hδ : 0 < δ := Real.sqrt_pos.2 (by positivity)
  obtain ⟨η0, hη0, hball0⟩ := Metric.uniformContinuous_iff.1 huc0 δ hδ
  obtain ⟨η1, hη1, hball1⟩ := Metric.uniformContinuous_iff.1 huc1 δ hδ
  refine Metric.eventually_nhds_iff.2 ⟨min η0 η1, lt_min hη0 hη1, fun s hs => ?_⟩
  have hdist_coord : ∀ w : B0579.Plane, dist ((s, w) : Coord) (T, w) = dist s T := fun w => by
    rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
  have hdiff_pt : ∀ y ∈ B0579.cell c, ∀ i : Fin 2,
      |TailPeriodizeAux.qPeriodize c (fun x => Ψ x i) s y -
        TailPeriodizeAux.qPeriodize c (fun x => Ψ x i) T y| ≤ Kcard * δ := by
    intro y hy i
    rw [hfin_eq s y i hy, hfin_eq T y i hy, ← Finset.sum_sub_distrib]
    calc |∑ k ∈ S, (Ψ (s, (y.1 + (k : ℝ) * c, y.2)) i - Ψ (T, (y.1 + (k : ℝ) * c, y.2)) i)|
        ≤ ∑ k ∈ S, |Ψ (s, (y.1 + (k : ℝ) * c, y.2)) i - Ψ (T, (y.1 + (k : ℝ) * c, y.2)) i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ S, δ := Finset.sum_le_sum fun k _ => by
          rw [← Real.dist_eq]
          have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
          rcases hi with rfl | rfl
          · exact (hball0 (by rw [hdist_coord]; exact hs.trans_le (min_le_left _ _))).le
          · exact (hball1 (by rw [hdist_coord]; exact hs.trans_le (min_le_right _ _))).le
      _ = (S.card : ℝ) * δ := by simp
      _ ≤ Kcard * δ := mul_le_mul_of_nonneg_right (by dsimp [Kcard]; linarith) hδ.le
  have hint_cell : IntegrableOn
      (fun y => ∑ i : Fin 2, (TailPeriodizeAux.qPeriodize c (fun x => Ψ x i) s y -
        TailPeriodizeAux.qPeriodize c (fun x => Ψ x i) T y) ^ 2)
      (B0579.cell c) volume := by
    refine integrable_finsetSum _ fun i _ => ?_
    have hm1 := B0583.memLp_cellVol_of_isCylTest
      (TailPeriodizeAux.isCylTest_qPeriodize hc (hΨ.smooth i) s)
    have hm2 := B0583.memLp_cellVol_of_isCylTest
      (TailPeriodizeAux.isCylTest_qPeriodize hc (hΨ.smooth i) T)
    simpa [pow_two] using (hm1.sub hm2).integrable_sq
  have heq_cellR : (∫ y in B0579.cell c,
        ∑ i : Fin 2, (TailPeriodizeAux.qPeriodize c (fun x => Ψ x i) s y -
          TailPeriodizeAux.qPeriodize c (fun x => Ψ x i) T y) ^ 2) =
      ∫ y in cellR,
        ∑ i : Fin 2, (TailPeriodizeAux.qPeriodize c (fun x => Ψ x i) s y -
          TailPeriodizeAux.qPeriodize c (fun x => Ψ x i) T y) ^ 2 := by
    refine MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (B0579.measurableSet_cell c) hcellR_sub ?_
    intro y ⟨hy_cell, hy_not⟩
    have hnot_η : y.2 ∉ Icc (-R) R := fun hη => hy_not ⟨hy_cell.1, hη⟩
    have hη_gt : R < |y.2| := by
      by_contra hle; push Not at hle; exact hnot_η (abs_le.1 hle)
    simp [hzero_η s y 0 hη_gt, hzero_η T y 0 hη_gt,
      hzero_η s y 1 hη_gt, hzero_η T y 1 hη_gt]
  have hnn : 0 ≤ ∫ y in cellR,
      ∑ i : Fin 2, (TailPeriodizeAux.qPeriodize c (fun x => Ψ x i) s y -
        TailPeriodizeAux.qPeriodize c (fun x => Ψ x i) T y) ^ 2 :=
    setIntegral_nonneg hcellR_meas fun y _ => Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [Real.dist_eq, sub_zero, heq_cellR, abs_of_nonneg hnn]
  have hconst_int : IntegrableOn (fun _ : B0579.Plane => 2 * (Kcard * δ) ^ 2) cellR volume :=
    integrableOn_const hcellR_fin.ne
  have hle_int : (∫ y in cellR,
        ∑ i : Fin 2, (TailPeriodizeAux.qPeriodize c (fun x => Ψ x i) s y -
          TailPeriodizeAux.qPeriodize c (fun x => Ψ x i) T y) ^ 2) ≤
      ∫ _y in cellR, (2 * (Kcard * δ) ^ 2) := by
    refine setIntegral_mono_on (hint_cell.mono_set hcellR_sub) hconst_int hcellR_meas fun y hy => ?_
    have h0 := hdiff_pt y (hcellR_sub hy) 0
    have h1 := hdiff_pt y (hcellR_sub hy) 1
    have hsq0 : (TailPeriodizeAux.qPeriodize c (fun x => Ψ x 0) s y -
        TailPeriodizeAux.qPeriodize c (fun x => Ψ x 0) T y) ^ 2 ≤ (Kcard * δ) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h0 2
    have hsq1 : (TailPeriodizeAux.qPeriodize c (fun x => Ψ x 1) s y -
        TailPeriodizeAux.qPeriodize c (fun x => Ψ x 1) T y) ^ 2 ≤ (Kcard * δ) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [Fin.sum_univ_two]
    linarith
  have hrhs_val : (∫ _y in cellR, (2 * (Kcard * δ) ^ 2)) < ε := by
    rw [setIntegral_const, smul_eq_mul]
    have hδ_sq : δ ^ 2 = ε / (4 * Kcard ^ 2 * Vreal) :=
      Real.sq_sqrt (by positivity)
    have hcalc : 2 * (Kcard * δ) ^ 2 = ε / (2 * Vreal) := by
      rw [mul_pow, hδ_sq]
      field_simp [hKcard_pos.ne', hVreal_pos.ne']
      ring
    rw [hcalc]
    have hv_lt : volume.real cellR < Vreal := by dsimp [Vreal]; linarith
    calc volume.real cellR * (ε / (2 * Vreal))
        ≤ Vreal * (ε / (2 * Vreal)) :=
          mul_le_mul_of_nonneg_right hv_lt.le (by positivity)
      _ = ε / 2 := by field_simp [hVreal_pos.ne']
      _ < ε := half_lt_self hε
  exact hle_int.trans_lt hrhs_val

private lemma tendsto_inner_lmH {c T : ℝ} {A B : ℝ → LMH c}
    (hA : Tendsto A (𝓝 T) (𝓝 (A T))) (hB : Tendsto B (𝓝 T) (𝓝 (B T))) :
    Tendsto (fun s => ⟪A s, B s⟫) (𝓝 T) (𝓝 ⟪A T, B T⟫) := by
  have hAn := tendsto_iff_norm_sub_tendsto_zero.1 hA
  have hBn := tendsto_iff_norm_sub_tendsto_zero.1 hB
  have hmaj : Tendsto (fun s =>
      ‖A s - A T‖ * ‖B s - B T‖ + ‖A s - A T‖ * ‖B T‖ + ‖A T‖ * ‖B s - B T‖)
      (𝓝 T) (𝓝 0) := by
    simpa using ((hAn.mul hBn).add (hAn.mul_const ‖B T‖)).add (hBn.const_mul ‖A T‖)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun s => ?_) hmaj
  have hid : ⟪A s, B s⟫ - ⟪A T, B T⟫ =
      ⟪A s - A T, B s - B T⟫ + ⟪A s - A T, B T⟫ + ⟪A T, B s - B T⟫ := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, inner_sub_left]
    ring
  rw [hid, Real.norm_eq_abs]
  calc |⟪A s - A T, B s - B T⟫ + ⟪A s - A T, B T⟫ + ⟪A T, B s - B T⟫|
      ≤ |⟪A s - A T, B s - B T⟫ + ⟪A s - A T, B T⟫| + |⟪A T, B s - B T⟫| := abs_add_le _ _
    _ ≤ |⟪A s - A T, B s - B T⟫| + |⟪A s - A T, B T⟫| + |⟪A T, B s - B T⟫| :=
        add_le_add_left (abs_add_le _ _) _
    _ ≤ ‖A s - A T‖ * ‖B s - B T‖ + ‖A s - A T‖ * ‖B T‖ + ‖A T‖ * ‖B s - B T‖ :=
        add_le_add (add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _))
          (abs_real_inner_le_norm _ _)

private lemma continuousAt_seamPairing {c T M : ℝ} (hc : 0 < c) (hT : 0 < T) (hM : 0 ≤ M)
    {z₁ zq₁ zη₁ z₂ zq₂ zη₂ : CProf}
    (hz₁ : StronglyMeasurable z₁) (hzq₁ : StronglyMeasurable zq₁) (hzη₁ : StronglyMeasurable zη₁)
    (hz₂ : StronglyMeasurable z₂) (hzq₂ : StronglyMeasurable zq₂) (hzη₂ : StronglyMeasurable zη₂)
    (hbdd₁ : ∀ s ∈ Ioc 0 T, sliceH1Norm c z₁ zq₁ zη₁ s ≤ ENNReal.ofReal (3 * M))
    (hcont₁ : ∀ s ∈ Ioc 0 T,
      Tendsto (fun s' => cylSliceH1 c
        (fun y => z₁ (s', y) - z₁ (s, y))
        (fun y => zq₁ (s', y) - zq₁ (s, y))
        (fun y => zη₁ (s', y) - zη₁ (s, y))) (𝓝[Ioc 0 T] s) (𝓝 0))
    (hmatch : cylSliceH1 c (fun y => z₂ (T, y) - z₁ (T, y))
      (fun y => zq₂ (T, y) - zq₁ (T, y)) (fun y => zη₂ (T, y) - zη₁ (T, y)) = 0)
    (hcont₂ : ∀ s : ℝ, T ≤ s →
      Tendsto (fun s' => cylSliceH1 c
        (fun y => z₂ (s', y) - z₂ (s, y))
        (fun y => zq₂ (s', y) - zq₂ (s, y))
        (fun y => zη₂ (s', y) - zη₂ (s, y))) (𝓝[Ici T] s) (𝓝 0))
    {Ψ : Coord → Fin 2 → ℝ} (hΨ : IsPlanarSolTest Ψ) :
    ContinuousAt (fun s : ℝ => ∑ i : Fin 2, ∫ y in B0579.cell c,
      glueAtHorizon T z₁ z₂ (s, y) i *
        (TailPeriodizeAux.qPeriodize c (fun x => Ψ x i) s y : ℂ)) T := by
  set Z := glueAtHorizon T z₁ z₂
  have hZ_sm : StronglyMeasurable Z := stronglyMeasurable_glue T hz₁ hz₂
  obtain ⟨K, _hK_nn, hK⟩ := exists_glued_sliceH1Norm_bound hT hM hz₁ hzq₁ hzη₁ hz₂ hzq₂ hzη₂
    hbdd₁ hmatch hcont₂ (a := T / 2) (b := T + 1) (half_pos hT) (by linarith)
  have hZ_mem : ∀ s ∈ Icc (T / 2) (T + 1),
      MemLp (fun y => Z (s, y)) 2 (volume.restrict (B0579.cell c)) := fun s hs =>
    memLp_z_of_sliceH1Norm_lt_top hZ_sm ((hK s hs).trans_lt ENNReal.ofReal_lt_top)
  let Q : ℝ → B0579.Plane → Fin 2 → ℝ :=
    fun s y i => TailPeriodizeAux.qPeriodize c (fun x => Ψ x i) s y
  have hQ_mem : ∀ s : ℝ, ∀ i : Fin 2,
      MemLp (fun y => Q s y i) 2 (volume.restrict (B0579.cell c)) :=
    fun s i => B0583.memLp_cellVol_of_isCylTest
      (TailPeriodizeAux.isCylTest_qPeriodize hc (hΨ.smooth i) s)
  let ARe : ℝ → LMH c := fun s => toLMH (vecRe (Q s)) (vecRe_cellL2 (hQ_mem s))
  let AIm : ℝ → LMH c := fun s => toLMH (vecIm (Q s)) (vecIm_cellL2 (hQ_mem s))
  have hsq_tend := tendsto_qPeriodize_sq_cell (T := T) hc hΨ
  have hsqrt_tend : Tendsto (fun s => Real.sqrt (∫ y in B0579.cell c,
        ∑ i : Fin 2, (Q s y i - Q T y i) ^ 2)) (𝓝 T) (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hsq_tend
    rwa [Real.sqrt_zero] at h
  have hARe_tend : Tendsto ARe (𝓝 T) (𝓝 (ARe T)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine hsqrt_tend.congr fun s => ?_
    rw [← norm_toLMH_vecRe_sub_sq' (hQ_mem s) (hQ_mem T), Real.sqrt_sq (norm_nonneg _)]
  have hAIm_tend : Tendsto AIm (𝓝 T) (𝓝 (AIm T)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine hsqrt_tend.congr fun s => ?_
    rw [← norm_toLMH_vecIm_sub_sq' (hQ_mem s) (hQ_mem T), Real.sqrt_sq (norm_nonneg _)]
  have hZ_cont := continuousAt_cprofToLMH_glue hT hM hz₁ hzq₁ hzη₁ hz₂ hzq₂ hzη₂
    hbdd₁ hcont₁ hmatch hcont₂
  have hnhds_cc : Icc (T / 2) (T + 1) ∈ 𝓝 T :=
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds ⟨half_lt_self hT, lt_add_one T⟩) Ioo_subset_Icc_self
  set P : ℝ → ℂ := fun s => ∑ i : Fin 2, ∫ y in B0579.cell c, Z (s, y) i * (Q s y i : ℂ)
  have hT_cc : T ∈ Icc (T / 2) (T + 1) := ⟨by linarith, by linarith⟩
  have hre_tend : Tendsto (fun s => (P s).re) (𝓝 T) (𝓝 (P T).re) := by
    rw [re_cell_pair_eq_inner (hZ_mem T hT_cc) (hQ_mem T)]
    refine (tendsto_inner_lmH hARe_tend hZ_cont).congr' ?_
    filter_upwards [hnhds_cc] with s hs
    exact (re_cell_pair_eq_inner (hZ_mem s hs) (hQ_mem s)).symm
  have him_tend : Tendsto (fun s => (P s).im) (𝓝 T) (𝓝 (P T).im) := by
    rw [im_cell_pair_eq_inner (hZ_mem T hT_cc) (hQ_mem T)]
    refine (tendsto_inner_lmH hAIm_tend hZ_cont).congr' ?_
    filter_upwards [hnhds_cc] with s hs
    exact (im_cell_pair_eq_inner (hZ_mem s hs) (hQ_mem s)).symm
  have hcomb := (Complex.continuous_ofReal.tendsto _ |>.comp hre_tend).add
    ((Complex.continuous_ofReal.tendsto _ |>.comp him_tend).mul_const Complex.I)
  have hP_tend : Tendsto P (𝓝 T) (𝓝 (P T)) := by
    rw [← Complex.re_add_im (P T)]
    exact hcomb.congr fun s => Complex.re_add_im (P s)
  exact hP_tend

/-! ### 3. Smooth three-way time partition of unity around `s = T` -/

private def b0Bump : ContDiffBump (0 : ℝ) :=
  ⟨1 / 2, 1, by norm_num, by norm_num⟩

private def theta (T ε s : ℝ) : ℝ :=
  b0Bump ((s - T) / ε)

private def etaL (T ε s : ℝ) : ℝ :=
  if s ≤ T then 1 - theta T ε s else 0

private def etaR (T ε s : ℝ) : ℝ :=
  if s ≤ T then 0 else 1 - theta T ε s

private lemma etaL_add_theta_add_etaR (T ε s : ℝ) :
    etaL T ε s + theta T ε s + etaR T ε s = 1 := by
  by_cases hs : s ≤ T <;> simp [etaL, etaR, hs]

private lemma theta_nonneg (T ε s : ℝ) : 0 ≤ theta T ε s :=
  b0Bump.nonneg

private lemma theta_le_one (T ε s : ℝ) : theta T ε s ≤ 1 :=
  b0Bump.le_one

private lemma abs_theta_le_one (T ε s : ℝ) : |theta T ε s| ≤ 1 :=
  abs_le.2 ⟨by linarith [theta_nonneg T ε s], theta_le_one T ε s⟩

private lemma theta_eq_one_of_abs_le {T ε s : ℝ} (hε : 0 < ε) (h : |s - T| ≤ ε / 2) :
    theta T ε s = 1 := by
  apply b0Bump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_div, abs_of_pos hε]
  change |s - T| / ε ≤ 1 / 2
  rw [div_le_iff₀ hε]
  linarith

private lemma theta_eq_zero_of_le_abs {T ε s : ℝ} (hε : 0 < ε) (h : ε ≤ |s - T|) :
    theta T ε s = 0 := by
  apply b0Bump.zero_of_le_dist
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hε]
  change (1 : ℝ) ≤ |s - T| / ε
  rwa [le_div_iff₀ hε, one_mul]

private lemma contDiff_b0Bump : ContDiff ℝ ∞ b0Bump :=
  b0Bump.contDiff

private lemma contDiff_theta {T ε : ℝ} (_hε : 0 < ε) : ContDiff ℝ ∞ (theta T ε) :=
  contDiff_b0Bump.comp ((contDiff_id.sub contDiff_const).div_const ε)

private lemma contDiff_etaL {T ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ∞ (etaL T ε) := by
  rw [contDiff_iff_contDiffAt]
  intro s₀
  by_cases hs₀ : s₀ < T + ε / 2
  · refine (((contDiff_const (c := (1 : ℝ))).sub
        (contDiff_theta (T := T) hε)).contDiffAt).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Iio.mem_nhds hs₀] with s hs
    by_cases hle : s ≤ T
    · simp [etaL, hle]
    · have hgt : T < s := not_le.1 hle
      have habs : |s - T| ≤ ε / 2 := abs_le.2 ⟨by linarith, by linarith [mem_Iio.1 hs]⟩
      simp [etaL, hle, theta_eq_one_of_abs_le hε habs]
  · have hgt : T < s₀ := by linarith
    refine (contDiff_const (c := (0 : ℝ)).contDiffAt).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioi.mem_nhds hgt] with s hs
    have hnle : ¬s ≤ T := not_le.2 hs
    simp [etaL, hnle]

private lemma contDiff_etaR {T ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ∞ (etaR T ε) := by
  rw [contDiff_iff_contDiffAt]
  intro s₀
  by_cases hs₀ : T - ε / 2 < s₀
  · refine (((contDiff_const (c := (1 : ℝ))).sub
        (contDiff_theta (T := T) hε)).contDiffAt).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioi.mem_nhds hs₀] with s hs
    by_cases hle : s ≤ T
    · have habs : |s - T| ≤ ε / 2 := abs_le.2 ⟨by linarith [mem_Ioi.1 hs], by linarith⟩
      simp [etaR, hle, theta_eq_one_of_abs_le hε habs]
    · simp [etaR, hle]
  · have hlt : s₀ < T := by linarith
    refine (contDiff_const (c := (0 : ℝ)).contDiffAt).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Iio.mem_nhds hlt] with s hs
    have hle : s ≤ T := (mem_Iio.1 hs).le
    simp [etaR, hle]

private lemma hasDerivAt_theta {T ε : ℝ} (_hε : 0 < ε) (s : ℝ) :
    HasDerivAt (theta T ε) (deriv b0Bump ((s - T) / ε) * ε⁻¹) s := by
  have h1 : HasDerivAt (fun r : ℝ => (r - T) / ε) ε⁻¹ s := by
    simpa [div_eq_mul_inv] using ((hasDerivAt_id s).sub_const T).mul_const ε⁻¹
  have h2 : HasDerivAt b0Bump (deriv b0Bump ((s - T) / ε)) ((s - T) / ε) :=
    (contDiff_b0Bump.differentiable (by simp) _).hasDerivAt
  exact h2.comp s h1

private lemma deriv_theta_eq {T ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    deriv (theta T ε) s = deriv b0Bump ((s - T) / ε) * ε⁻¹ :=
  (hasDerivAt_theta hε s).deriv

private lemma deriv_theta_eq_zero_of_lt_abs {T ε s : ℝ} (hε : 0 < ε) (h : ε < |s - T|) :
    deriv (theta T ε) s = 0 := by
  have hopen : IsOpen {r : ℝ | ε < |r - T|} :=
    isOpen_lt continuous_const (continuous_id.sub continuous_const).abs
  have hev : theta T ε =ᶠ[𝓝 s] 0 :=
    Filter.eventually_of_mem (hopen.mem_nhds h) fun r hr =>
      theta_eq_zero_of_le_abs hε (le_of_lt hr)
  simpa using hev.deriv_eq

private lemma exists_deriv_b0Bump_bound :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ u : ℝ, |deriv b0Bump u| ≤ Cb := by
  have hcont : Continuous (deriv b0Bump) := contDiff_b0Bump.continuous_deriv (by simp)
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-1 : ℝ) 1) hcont.continuousOn
  refine ⟨max 0 C₀, le_max_left 0 C₀, fun u => ?_⟩
  by_cases hu : u ∈ Icc (-1 : ℝ) 1
  · exact (Real.norm_eq_abs (deriv b0Bump u) ▸ hC₀ u hu).trans (le_max_right 0 C₀)
  · have hgt : 1 < |u| := by
      by_contra hle; push Not at hle; exact hu (abs_le.1 hle)
    have hopen : IsOpen {r : ℝ | 1 < |r|} := isOpen_lt continuous_const continuous_id.abs
    have hev : (b0Bump : ℝ → ℝ) =ᶠ[𝓝 u] 0 :=
      Filter.eventually_of_mem (hopen.mem_nhds hgt) fun r hr => by
        apply b0Bump.zero_of_le_dist
        rw [Real.dist_eq, sub_zero]
        exact le_of_lt hr
    have hd0 : deriv b0Bump u = 0 := by simpa using hev.deriv_eq
    rw [hd0, abs_zero]
    exact le_max_left 0 C₀

private lemma integral_Icc_deriv_theta_eq_zero {T ε : ℝ} (hε : 0 < ε) :
    ∫ s in Icc (T - ε) (T + ε), ((deriv (theta T ε) s : ℝ) : ℂ) = 0 := by
  have hle : T - ε ≤ T + ε := by linarith
  have hcont_d : Continuous (deriv (theta T ε)) :=
    (contDiff_theta hε).continuous_deriv (by simp)
  have hint_iv : IntervalIntegrable (deriv (theta T ε)) volume (T - ε) (T + ε) :=
    hcont_d.intervalIntegrable _ _
  have hftc : ∫ s in (T - ε)..(T + ε), deriv (theta T ε) s =
      theta T ε (T + ε) - theta T ε (T - ε) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => (contDiff_theta hε |>.differentiable (by simp) s).hasDerivAt) hint_iv
  have h_end1 : theta T ε (T + ε) = 0 :=
    theta_eq_zero_of_le_abs hε (by rw [add_sub_cancel_left, abs_of_pos hε])
  have h_end2 : theta T ε (T - ε) = 0 :=
    theta_eq_zero_of_le_abs hε (by rw [sub_sub_cancel_left, abs_neg, abs_of_pos hε])
  rw [h_end1, h_end2, sub_self, intervalIntegral.integral_of_le hle,
    setIntegral_congr_set Ioc_ae_eq_Icc] at hftc
  have hint_d : IntegrableOn (deriv (theta T ε)) (Icc (T - ε) (T + ε)) volume :=
    hcont_d.integrableOn_Icc
  have hc := Complex.ofRealCLM.integral_comp_comm hint_d
  simp only [Complex.ofRealCLM_apply] at hc
  rw [hc, hftc, Complex.ofReal_zero]

/-! ### 4. Time-cutoff multiplication on `IsCoordTest` and `IsPlanarSolTest` -/

private lemma isCoordTest_time_mul {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η)
    {φ : Coord → ℝ} (hφ : IsCoordTest φ) :
    IsCoordTest (fun x : Coord => η x.1 * φ x) :=
  ⟨(hη.comp contDiff_fst).mul hφ.smooth, hφ.compact.mul_left,
    tsupport_mul_subset_right.trans hφ.supp⟩

private lemma tsupport_etaL_mul_subset {T ε : ℝ} (hε : 0 < ε)
    {φ : Coord → ℝ} (hφ : IsCoordTest φ) :
    tsupport (fun x : Coord => etaL T ε x.1 * φ x) ⊆ Ioo 0 T ×ˢ univ := by
  intro x hx
  have hx_pos : 0 < x.1 := (hφ.supp (tsupport_mul_subset_right hx)).1
  have hx_lt : x.1 < T := by
    by_contra hge
    have hgt : T - ε / 4 < x.1 := by linarith
    have hopen : IsOpen {y : Coord | T - ε / 4 < y.1} :=
      isOpen_lt continuous_const continuous_fst
    have hev : (fun y : Coord => etaL T ε y.1 * φ y) =ᶠ[𝓝 x] 0 := by
      filter_upwards [hopen.mem_nhds hgt] with y hy
      change T - ε / 4 < y.1 at hy
      have hy0 : etaL T ε y.1 = 0 := by
        by_cases hle : y.1 ≤ T
        · have habs : |y.1 - T| ≤ ε / 2 := abs_le.2 ⟨by linarith, by linarith⟩
          simp [etaL, hle, theta_eq_one_of_abs_le hε habs]
        · simp [etaL, hle]
      simp [hy0]
    exact (notMem_tsupport_iff_eventuallyEq.2 hev) hx
  exact ⟨⟨hx_pos, hx_lt⟩, trivial⟩

private lemma tsupport_etaR_mul_subset {T ε : ℝ} (hε : 0 < ε) (φ : Coord → ℝ) :
    tsupport (fun x : Coord => etaR T ε x.1 * φ x) ⊆ Ioi T ×ˢ univ := by
  intro x hx
  refine ⟨?_, trivial⟩
  by_contra hle
  rw [mem_Ioi, not_lt] at hle
  have hlt : x.1 < T + ε / 4 := by linarith
  have hopen : IsOpen {y : Coord | y.1 < T + ε / 4} :=
    isOpen_lt continuous_fst continuous_const
  have hev : (fun y : Coord => etaR T ε y.1 * φ y) =ᶠ[𝓝 x] 0 := by
    filter_upwards [hopen.mem_nhds hlt] with y hy
    change y.1 < T + ε / 4 at hy
    have hy0 : etaR T ε y.1 = 0 := by
      by_cases hyle : y.1 ≤ T
      · simp [etaR, hyle]
      · have habs : |y.1 - T| ≤ ε / 2 := abs_le.2 ⟨by linarith, by linarith⟩
        simp [etaR, hyle, theta_eq_one_of_abs_le hε habs]
    simp [hy0]
  exact (notMem_tsupport_iff_eventuallyEq.2 hev) hx

private lemma hasFDerivAt_time_comp {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η) (x : Coord) :
    HasFDerivAt (fun y : Coord => η y.1)
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (deriv η x.1)).comp
        (ContinuousLinearMap.fst ℝ ℝ B0579.Plane)) x :=
  ((hη.differentiable (by simp) x.1).hasDerivAt.hasFDerivAt).comp x
    (ContinuousLinearMap.fst ℝ ℝ B0579.Plane).hasFDerivAt

private lemma cpd_time_mul_zero {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η)
    {φ : Coord → ℝ} (hφ : ContDiff ℝ ∞ φ) (x : Coord) :
    cpd 0 (fun y : Coord => η y.1 * φ y) x = deriv η x.1 * φ x + η x.1 * cpd 0 φ x := by
  have h1 := hasFDerivAt_time_comp hη x
  have h2 := (hφ.differentiable (by simp) x).hasFDerivAt
  have hm := (h1.mul h2).fderiv
  unfold cpd
  change (fderiv ℝ ((fun y : Coord => η y.1) * φ) x) (cdir 0) = _
  rw [hm]
  simp [cdir]
  ring

private lemma cpd_time_mul_succ {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η)
    {φ : Coord → ℝ} (hφ : ContDiff ℝ ∞ φ) (j : Fin 2) (x : Coord) :
    cpd j.succ (fun y : Coord => η y.1 * φ y) x = η x.1 * cpd j.succ φ x := by
  have h1 := hasFDerivAt_time_comp hη x
  have h2 := (hφ.differentiable (by simp) x).hasFDerivAt
  have hm := (h1.mul h2).fderiv
  have hfst0 : (cdir j.succ).1 = 0 := by fin_cases j <;> rfl
  unfold cpd
  change (fderiv ℝ ((fun y : Coord => η y.1) * φ) x) (cdir j.succ) = _
  rw [hm]
  simp [hfst0]

private lemma coordTranspose_time_mul {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η)
    {φ : Coord → ℝ} (hφ : ContDiff ℝ ∞ φ) (j : Fin 2) (x : Coord) :
    coordTranspose (![vQ0, vEta] j) dZero (fun y => η y.1 * φ y) x =
      η x.1 * coordTranspose (![vQ0, vEta] j) dZero φ x := by
  rw [TailPeriodizeAux.coordTranspose_vQ0_vEta j _ x,
    TailPeriodizeAux.coordTranspose_vQ0_vEta j φ x,
    cpd_time_mul_succ hη hφ j x]
  ring

private lemma isPlanarSolTest_time_mul {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η)
    {Ψ : Coord → Fin 2 → ℝ} (hΨ : IsPlanarSolTest Ψ) :
    IsPlanarSolTest (fun x i => η x.1 * Ψ x i) := by
  refine ⟨fun i => isCoordTest_time_mul hη (hΨ.smooth i), fun x => ?_⟩
  have h0 := cpd_time_mul_succ hη (hΨ.smooth 0).smooth 0 x
  have h1 := cpd_time_mul_succ hη (hΨ.smooth 1).smooth 1 x
  change cpd (Fin.succ 0) (fun y => η y.1 * Ψ y 0) x +
    cpd (Fin.succ 1) (fun y => η y.1 * Ψ y 1) x = 0
  rw [h0, h1, ← mul_add]
  change η x.1 * (cpd 1 (fun y => Ψ y 0) x + cpd 2 (fun y => Ψ y 1) x) = 0
  rw [hΨ.div_free x, mul_zero]

private lemma meridTranspose_time_mul (ν : ℝ) {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η)
    {Ψ : Coord → Fin 2 → ℝ} (hΨ : IsPlanarSolTest Ψ) (x : Coord) (i : Fin 2) :
    meridTranspose ν (fun y k => η y.1 * Ψ y k) x i =
      (η x.1 : ℂ) * meridTranspose ν Ψ x i - ((deriv η x.1 * Ψ x i : ℝ) : ℂ) := by
  have hs := (hΨ.smooth i).smooth
  have hs1 : ContDiff ℝ ∞ (fun y => cpd 1 (fun z => Ψ z i) y) :=
    (planarTest_isCoordTest_partial (hΨ.smooth i) (cdir 1)).smooth
  have hs2 : ContDiff ℝ ∞ (fun y => cpd 2 (fun z => Ψ z i) y) :=
    (planarTest_isCoordTest_partial (hΨ.smooth i) (cdir 2)).smooth
  have hd0 := cpd_time_mul_zero hη hs x
  have hd1_fun : (fun y => cpd 1 (fun z => η z.1 * Ψ z i) y) =
      fun y => η y.1 * cpd 1 (fun z => Ψ z i) y :=
    funext fun y => cpd_time_mul_succ hη hs 0 y
  have hd2_fun : (fun y => cpd 2 (fun z => η z.1 * Ψ z i) y) =
      fun y => η y.1 * cpd 2 (fun z => Ψ z i) y :=
    funext fun y => cpd_time_mul_succ hη hs 1 y
  have hd11 : cpd 1 (fun y => cpd 1 (fun z => η z.1 * Ψ z i) y) x =
      η x.1 * cpd 1 (fun y => cpd 1 (fun z => Ψ z i) y) x := by
    rw [hd1_fun]; exact cpd_time_mul_succ hη hs1 0 x
  have hd22 : cpd 2 (fun y => cpd 2 (fun z => η z.1 * Ψ z i) y) x =
      η x.1 * cpd 2 (fun y => cpd 2 (fun z => Ψ z i) y) x := by
    rw [hd2_fun]; exact cpd_time_mul_succ hη hs2 1 x
  unfold meridTranspose
  rw [hd0, hd11, hd22]
  push_cast
  ring

private lemma tsupport_cpd2_zero {φ : Coord → ℝ} {S : Set ℝ}
    (hsupp : tsupport φ ⊆ S ×ˢ univ) (d d' : Fin 3) {x : Coord} (hx : x.1 ∉ S) :
    cpd d φ x = 0 ∧ cpd d' (cpd d φ) x = 0 := by
  have hnot : x ∉ tsupport φ := fun hm => hx (hsupp hm).1
  have hev : φ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 hnot
  have h1 : cpd d φ x = 0 := by simp [cpd, hev.fderiv_eq]
  obtain ⟨U, hU0, hU_open, hxU⟩ := eventually_nhds_iff.1 hev
  have hev_d : cpd d φ =ᶠ[𝓝 x] 0 := by
    refine Filter.eventually_of_mem (hU_open.mem_nhds hxU) fun y hyU => ?_
    have hy : φ =ᶠ[𝓝 y] 0 := Filter.eventually_of_mem (hU_open.mem_nhds hyU) hU0
    simp [cpd, hy.fderiv_eq]
  exact ⟨h1, by simp [cpd, hev_d.fderiv_eq]⟩

/-! ### 5. Global `Coord` integrability, DCT vanishing, and horizon seam limit -/

private lemma integrable_coord_of_sliceBound {c a b R K : ℝ}
    (hc : 0 < c) (ha : 0 < a) (hab : a ≤ b) (hR : 0 < R)
    {W : CProf} (hW_sm : StronglyMeasurable W) (hW_per : QPeriodic c W)
    (hW_bdd : ∀ s ∈ Icc a b, cylSliceL2 c (fun y => W (s, y)) ≤ ENNReal.ofReal K)
    (i : Fin 2) {α : Coord → ℝ} (hα_cont : Continuous α)
    (hα_supp : ∀ x : Coord, (x.1 ∉ Icc a b ∨ R < |x.2.1| ∨ R < |x.2.2|) → α x = 0) :
    Integrable (fun x : Coord => W x i * (α x : ℂ)) volume ∧
      IntegrableOn (fun x : Coord => W x i * (TailPeriodizeAux.qPeriodize c α x.1 x.2 : ℂ))
        (Icc a b ×ˢ B0579.cell c) volume ∧
      ∫ x : Coord, W x i * (α x : ℂ) =
        ∫ s in Icc a b, ∫ z in B0579.cell c,
          W (s, z) i * (TailPeriodizeAux.qPeriodize c α s z : ℂ) := by
  have hu_meas : AEStronglyMeasurable (fun x : Coord => W x i) volume :=
    (compMeas hW_sm i).aestronglyMeasurable
  have hu_per : ∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}),
      W (qShift c x) i = W x i := by
    rw [ae_restrict_iff' (measurableSet_lt measurable_const measurable_fst)]
    exact (QPerHalf.ae_imp hW_per).mono fun x hx hp => congrArg (fun v => v i) (hx hp)
  have hu_loc : (∫⁻ s in Icc a b,
      eLpNorm (fun z => W (s, z) i) 2 (volume.restrict (B0579.cell c))) < ⊤ := by
    have hvol_ab : volume (Icc a b) < ⊤ := by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
    calc ∫⁻ s in Icc a b, eLpNorm (fun z => W (s, z) i) 2 (volume.restrict (B0579.cell c))
        ≤ ∫⁻ s in Icc a b, cylSliceL2 c (fun y => W (s, y)) :=
          lintegral_mono fun s => eLpNorm_mono fun y => PiLp.norm_apply_le (W (s, y)) i
      _ ≤ ∫⁻ _s in Icc a b, ENNReal.ofReal K :=
          lintegral_mono_ae ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall hW_bdd))
      _ = ENNReal.ofReal K * volume (Icc a b) := by simp
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hvol_ab
  exact TailPeriodizeAux.integrable_and_integral_coord_eq_cell_qPeriodize
    hc ha hab hR hu_meas hu_per hu_loc hα_cont hα_supp

private lemma integrable_coord_mul_isCoordTest {c : ℝ} (hc : 0 < c)
    {W : CProf} (hW_sm : StronglyMeasurable W) (hW_per : QPeriodic c W)
    (hW_loc : ∀ {a b : ℝ}, 0 < a → a ≤ b →
      ∃ K : ℝ, ∀ s ∈ Icc a b, cylSliceL2 c (fun y => W (s, y)) ≤ ENNReal.ofReal K)
    (i : Fin 2) {α : Coord → ℝ} (hα : IsCoordTest α) :
    Integrable (fun x : Coord => W x i * (α x : ℂ)) volume := by
  obtain ⟨a, b, R, ha, hab, hR, hbox⟩ := TailPeriodizeAux.coordTest_box hα
  obtain ⟨K, hK⟩ := hW_loc ha hab
  exact (integrable_coord_of_sliceBound hc ha hab hR hW_sm hW_per hK i
    hα.smooth.continuous fun x hx => (hbox x hx).1).1

private lemma integrable_source_mul_isCoordTest {c T : ℝ} (hc : 0 < c)
    {g gq gη : CProf} (hg : IsCylSourceH1 c g gq gη)
    (hg_early : (∫⁻ s in Ioc 0 T, sliceH1Norm c g gq gη s) < ⊤)
    (hg_tail : (∫⁻ s in Ioi T, sliceH1Norm c g gq gη s) < ⊤)
    (i : Fin 2) {α : Coord → ℝ} (hα : IsCoordTest α) :
    Integrable (fun x : Coord => g x i * (α x : ℂ)) volume := by
  obtain ⟨a, b, R, ha, hab, hR, hbox⟩ := TailPeriodizeAux.coordTest_box hα
  have hu_meas : AEStronglyMeasurable (fun x : Coord => g x i) volume :=
    (compMeas hg.sm_g i).aestronglyMeasurable
  have hu_per : ∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}),
      g (qShift c x) i = g x i := by
    rw [ae_restrict_iff' (measurableSet_lt measurable_const measurable_fst)]
    exact (QPerHalf.ae_imp hg.periodic_g).mono fun x hx hp => congrArg (fun v => v i) (hx hp)
  have hsub_union : Icc a b ⊆ Ioc 0 T ∪ Ioi T := fun s hs => by
    by_cases hsT : s ≤ T
    · exact Or.inl ⟨lt_of_lt_of_le ha hs.1, hsT⟩
    · exact Or.inr (not_le.1 hsT)
  have hu_loc : (∫⁻ s in Icc a b,
      eLpNorm (fun z => g (s, z) i) 2 (volume.restrict (B0579.cell c))) < ⊤ := by
    calc ∫⁻ s in Icc a b, eLpNorm (fun z => g (s, z) i) 2 (volume.restrict (B0579.cell c))
        ≤ ∫⁻ s in Icc a b, sliceH1Norm c g gq gη s :=
          lintegral_mono fun s =>
            (eLpNorm_mono fun y => PiLp.norm_apply_le (g (s, y)) i).trans
              ((le_add_of_nonneg_right zero_le).trans (le_add_of_nonneg_right zero_le))
      _ ≤ ∫⁻ s in Ioc 0 T ∪ Ioi T, sliceH1Norm c g gq gη s := lintegral_mono_set hsub_union
      _ ≤ (∫⁻ s in Ioc 0 T, sliceH1Norm c g gq gη s) +
            (∫⁻ s in Ioi T, sliceH1Norm c g gq gη s) := lintegral_union_le _ _ _
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨hg_early, hg_tail⟩
  exact (TailPeriodizeAux.integrable_and_integral_coord_eq_cell_qPeriodize
    hc ha hab hR hu_meas hu_per hu_loc hα.smooth.continuous fun x hx => (hbox x hx).1).1

private lemma tendsto_integral_theta_mul_zero (T : ℝ) {εn : ℕ → ℝ}
    (hεn_pos : ∀ n, 0 < εn n) (hεn_tend : Tendsto εn atTop (𝓝 0))
    {F : Coord → ℂ} (hF : Integrable F volume) :
    Tendsto (fun n => ∫ x : Coord, (theta T (εn n) x.1 : ℂ) * F x) atTop (𝓝 0) := by
  have hnull : volume {x : Coord | x.1 = T} = 0 := by
    have heq_set : {x : Coord | x.1 = T} = ({T} : Set ℝ) ×ˢ (univ : Set B0579.Plane) := by
      ext x; simp
    rw [heq_set, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]
  have hae_ne : ∀ᵐ x : Coord ∂volume, x.1 ≠ T := by
    rw [ae_iff]; simpa using hnull
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun x : Coord => (theta T (εn n) x.1 : ℂ) * F x) volume := fun n =>
    ((Complex.continuous_ofReal.comp
      ((contDiff_theta (hεn_pos n)).continuous.comp continuous_fst)).aestronglyMeasurable).mul
      hF.aestronglyMeasurable
  have hle : ∀ n : ℕ, ∀ᵐ x : Coord ∂volume,
      ‖(theta T (εn n) x.1 : ℂ) * F x‖ ≤ ‖F x‖ := fun n =>
    ae_of_all _ fun x => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (abs_theta_le_one T (εn n) x.1)
  have hpt : ∀ᵐ x : Coord ∂volume,
      Tendsto (fun n => (theta T (εn n) x.1 : ℂ) * F x) atTop (𝓝 0) := by
    filter_upwards [hae_ne] with x hx
    have hpos : 0 < |x.1 - T| := abs_pos.2 (sub_ne_zero.2 hx)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [(tendsto_order.1 hεn_tend).2 |x.1 - T| hpos] with n hn
    simp [theta_eq_zero_of_le_abs (hεn_pos n) hn.le]
  have hlim := tendsto_integral_of_dominated_convergence (fun x => ‖F x‖) hmeas hF.norm hle hpt
  simpa using hlim

private lemma tendsto_seam_integral_zero {c T M : ℝ} (hc : 0 < c) (hT : 0 < T) (hM : 0 ≤ M)
    {z₁ zq₁ zη₁ z₂ zq₂ zη₂ : CProf}
    (hz₁ : StronglyMeasurable z₁) (hzq₁ : StronglyMeasurable zq₁) (hzη₁ : StronglyMeasurable zη₁)
    (hz₂ : StronglyMeasurable z₂) (hzq₂ : StronglyMeasurable zq₂) (hzη₂ : StronglyMeasurable zη₂)
    (hZ_per : QPeriodic c (glueAtHorizon T z₁ z₂))
    (hbdd₁ : ∀ s ∈ Ioc 0 T, sliceH1Norm c z₁ zq₁ zη₁ s ≤ ENNReal.ofReal (3 * M))
    (hcont₁ : ∀ s ∈ Ioc 0 T,
      Tendsto (fun s' => cylSliceH1 c
        (fun y => z₁ (s', y) - z₁ (s, y))
        (fun y => zq₁ (s', y) - zq₁ (s, y))
        (fun y => zη₁ (s', y) - zη₁ (s, y))) (𝓝[Ioc 0 T] s) (𝓝 0))
    (hmatch : cylSliceH1 c (fun y => z₂ (T, y) - z₁ (T, y))
      (fun y => zq₂ (T, y) - zq₁ (T, y)) (fun y => zη₂ (T, y) - zη₁ (T, y)) = 0)
    (hcont₂ : ∀ s : ℝ, T ≤ s →
      Tendsto (fun s' => cylSliceH1 c
        (fun y => z₂ (s', y) - z₂ (s, y))
        (fun y => zq₂ (s', y) - zq₂ (s, y))
        (fun y => zη₂ (s', y) - zη₂ (s, y))) (𝓝[Ici T] s) (𝓝 0))
    {εn : ℕ → ℝ} (hεn_pos : ∀ n, 0 < εn n) (hεn_le : ∀ n, εn n ≤ T / 2)
    (hεn_tend : Tendsto εn atTop (𝓝 0))
    {Ψ : Coord → Fin 2 → ℝ} (hΨ : IsPlanarSolTest Ψ) :
    Tendsto (fun n => ∫ x : Coord, ∑ i : Fin 2,
      glueAtHorizon T z₁ z₂ x i * ((deriv (theta T (εn n)) x.1 * Ψ x i : ℝ) : ℂ))
      atTop (𝓝 0) := by
  set Z := glueAtHorizon T z₁ z₂
  have hZ_sm : StronglyMeasurable Z := stronglyMeasurable_glue T hz₁ hz₂
  obtain ⟨_a0, _b0, R0, _ha0, _hab0, hR0, hbox0⟩ := TailPeriodizeAux.coordTest_box (hΨ.smooth 0)
  obtain ⟨_a1, _b1, R1, _ha1, _hab1, _hR1, hbox1⟩ := TailPeriodizeAux.coordTest_box (hΨ.smooth 1)
  set R := max R0 R1
  have hR_pos : 0 < R := lt_of_lt_of_le hR0 (le_max_left _ _)
  have hΨ_box : ∀ (i : Fin 2) (x : Coord), (R < |x.2.1| ∨ R < |x.2.2|) → Ψ x i = 0 := by
    intro i x hx
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases hi with rfl | rfl
    · refine (hbox0 x (Or.inr ?_)).1
      rcases hx with hq | hη
      · exact Or.inl ((le_max_left R0 R1).trans_lt hq)
      · exact Or.inr ((le_max_left R0 R1).trans_lt hη)
    · refine (hbox1 x (Or.inr ?_)).1
      rcases hx with hq | hη
      · exact Or.inl ((le_max_right R0 R1).trans_lt hq)
      · exact Or.inr ((le_max_right R0 R1).trans_lt hη)
  obtain ⟨Cb, hCb_nn, hCb⟩ := exists_deriv_b0Bump_bound
  set P : ℝ → ℂ := fun s => ∑ i : Fin 2, ∫ y in B0579.cell c,
    Z (s, y) i * (TailPeriodizeAux.qPeriodize c (fun x => Ψ x i) s y : ℂ)
  have hP_cont : ContinuousAt P T :=
    continuousAt_seamPairing hc hT hM hz₁ hzq₁ hzη₁ hz₂ hzq₂ hzη₂
      hbdd₁ hcont₁ hmatch hcont₂ hΨ
  -- Unfold each `n`-th coordinate integral into the 1D seam integral on `[T - εn n, T + εn n]`
  have hseam_eq : ∀ n : ℕ,
      IntegrableOn (fun s => ((deriv (theta T (εn n)) s : ℝ) : ℂ) * (P s - P T))
        (Icc (T - εn n) (T + εn n)) volume ∧
      (∫ x : Coord, ∑ i : Fin 2, Z x i * ((deriv (theta T (εn n)) x.1 * Ψ x i : ℝ) : ℂ)) =
        ∫ s in Icc (T - εn n) (T + εn n),
          ((deriv (theta T (εn n)) s : ℝ) : ℂ) * (P s - P T) := by
    intro n
    set a := T - εn n
    set b := T + εn n
    have ha_pos : 0 < a := by linarith [hεn_le n]
    have hab : a ≤ b := by linarith [hεn_pos n]
    obtain ⟨K, _hK_nn, hK⟩ := exists_glued_sliceH1Norm_bound hT hM hz₁ hzq₁ hzη₁ hz₂ hzq₂ hzη₂
      hbdd₁ hmatch hcont₂ ha_pos hab
    have hZ_bdd : ∀ s ∈ Icc a b, cylSliceL2 c (fun y => Z (s, y)) ≤ ENNReal.ofReal K :=
      fun s hs => ((le_add_of_nonneg_right zero_le).trans
        (le_add_of_nonneg_right zero_le)).trans (hK s hs)
    let αi : Fin 2 → Coord → ℝ := fun i x => deriv (theta T (εn n)) x.1 * Ψ x i
    have hα_cont : ∀ i : Fin 2, Continuous (αi i) := fun i =>
      (((contDiff_theta (hεn_pos n)).continuous_deriv (by simp)).comp continuous_fst).mul
        (hΨ.smooth i).smooth.continuous
    have hα_supp : ∀ i : Fin 2, ∀ x : Coord,
        (x.1 ∉ Icc a b ∨ R < |x.2.1| ∨ R < |x.2.2|) → αi i x = 0 := by
      intro i x hx
      rcases hx with hx_ab | hq | hη
      · have hgt : εn n < |x.1 - T| := by
          by_contra hle; push Not at hle
          obtain ⟨h1, h2⟩ := abs_le.1 hle
          exact hx_ab ⟨by dsimp [a]; linarith, by dsimp [b]; linarith⟩
        simp [αi, deriv_theta_eq_zero_of_lt_abs (hεn_pos n) hgt]
      · simp [αi, hΨ_box i x (Or.inl hq)]
      · simp [αi, hΨ_box i x (Or.inr hη)]
    have hper_α : ∀ (i : Fin 2) (s : ℝ) (y : B0579.Plane),
        TailPeriodizeAux.qPeriodize c (αi i) s y =
          deriv (theta T (εn n)) s * TailPeriodizeAux.qPeriodize c (fun x => Ψ x i) s y :=
      fun _ _ _ => by dsimp only [TailPeriodizeAux.qPeriodize, αi]; exact tsum_mul_left
    have hcoord_i : ∀ i : Fin 2,
        Integrable (fun x : Coord => Z x i * (αi i x : ℂ)) volume ∧
        IntegrableOn (fun s : ℝ => ((deriv (theta T (εn n)) s : ℝ) : ℂ) *
          ∫ y in B0579.cell c,
            Z (s, y) i * (TailPeriodizeAux.qPeriodize c (fun x => Ψ x i) s y : ℂ))
          (Icc a b) volume ∧
        (∫ x : Coord, Z x i * (αi i x : ℂ)) =
          ∫ s in Icc a b, ((deriv (theta T (εn n)) s : ℝ) : ℂ) *
            ∫ y in B0579.cell c,
              Z (s, y) i * (TailPeriodizeAux.qPeriodize c (fun x => Ψ x i) s y : ℂ) := by
      intro i
      obtain ⟨hI_c, hI_p, heq_i⟩ := integrable_coord_of_sliceBound
        hc ha_pos hab hR_pos hZ_sm hZ_per hZ_bdd i (hα_cont i) (hα_supp i)
      have hI_prod : Integrable
          (fun x : ℝ × B0579.Plane => Z x i * (TailPeriodizeAux.qPeriodize c (αi i) x.1 x.2 : ℂ))
          ((volume.restrict (Icc a b)).prod (volume.restrict (B0579.cell c))) := by
        rwa [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hI_p
      have hI_slice := hI_prod.integral_prod_left
      have hslice_fun : (fun s : ℝ => ∫ y in B0579.cell c,
            Z (s, y) i * (TailPeriodizeAux.qPeriodize c (αi i) s y : ℂ)) =
          fun s : ℝ => ((deriv (theta T (εn n)) s : ℝ) : ℂ) *
            ∫ y in B0579.cell c,
              Z (s, y) i * (TailPeriodizeAux.qPeriodize c (fun x => Ψ x i) s y : ℂ) := by
        funext s
        simp_rw [hper_α i s, Complex.ofReal_mul, ← mul_assoc,
          mul_comm (Z (s, _) i) ((deriv (theta T (εn n)) s : ℝ) : ℂ), mul_assoc]
        exact integral_const_mul _ _
      rw [hslice_fun] at hI_slice heq_i
      exact ⟨hI_c, hI_slice, heq_i⟩
    have hI_P : IntegrableOn
        (fun s => ((deriv (theta T (εn n)) s : ℝ) : ℂ) * P s) (Icc a b) volume := by
      have hsum := (hcoord_i 0).2.1.add (hcoord_i 1).2.1
      refine hsum.congr_fun (fun s _ => ?_) measurableSet_Icc
      dsimp [P]
      rw [Fin.sum_univ_two, mul_add]
    have hI_PT : IntegrableOn (fun s => ((deriv (theta T (εn n)) s : ℝ) : ℂ) * P T)
        (Icc a b) volume := by
      have hd_cont : Continuous (fun s : ℝ => ((deriv (theta T (εn n)) s : ℝ) : ℂ) * P T) :=
        (Complex.continuous_ofReal.comp
          ((contDiff_theta (hεn_pos n)).continuous_deriv (by simp))).mul continuous_const
      exact hd_cont.integrableOn_Icc
    have hPT_zero : ∫ s in Icc a b, ((deriv (theta T (εn n)) s : ℝ) : ℂ) * P T = 0 := by
      rw [integral_mul_const, integral_Icc_deriv_theta_eq_zero (hεn_pos n), zero_mul]
    have hI_sub : IntegrableOn
        (fun s => ((deriv (theta T (εn n)) s : ℝ) : ℂ) * (P s - P T)) (Icc a b) volume :=
      (hI_P.sub hI_PT).congr_fun (fun s _ => (mul_sub _ _ _).symm) measurableSet_Icc
    refine ⟨hI_sub, ?_⟩
    rw [integral_finsetSum _ fun i _ => (hcoord_i i).1, Fin.sum_univ_two,
      (hcoord_i 0).2.2, (hcoord_i 1).2.2, ← integral_add (hcoord_i 0).2.1 (hcoord_i 1).2.1]
    have hlhs : (∫ s in Icc a b,
          (((deriv (theta T (εn n)) s : ℝ) : ℂ) *
              (∫ y in B0579.cell c,
                Z (s, y) 0 * (TailPeriodizeAux.qPeriodize c (fun x => Ψ x 0) s y : ℂ)) +
            ((deriv (theta T (εn n)) s : ℝ) : ℂ) *
              (∫ y in B0579.cell c,
                Z (s, y) 1 * (TailPeriodizeAux.qPeriodize c (fun x => Ψ x 1) s y : ℂ)))) =
        ∫ s in Icc a b, ((deriv (theta T (εn n)) s : ℝ) : ℂ) * P s := by
      refine setIntegral_congr_fun measurableSet_Icc fun s _ => ?_
      dsimp [P]; rw [Fin.sum_univ_two, mul_add]
    rw [hlhs, ← sub_zero (∫ s in Icc a b, ((deriv (theta T (εn n)) s : ℝ) : ℂ) * P s),
      ← hPT_zero, ← integral_sub hI_P hI_PT]
    refine setIntegral_congr_fun measurableSet_Icc fun s _ => ?_
    ring
  -- Estimate the 1D seam integral using `|deriv (theta T ε) s| ≤ Cb * ε⁻¹` and `ContinuousAt P T`
  rw [Metric.tendsto_nhds]
  intro ε hε
  set C1 : ℝ := 2 * Cb + 1
  have hC1_pos : 0 < C1 := by dsimp [C1]; positivity
  obtain ⟨η, hη, hP_ball⟩ := Metric.continuousAt_iff.1 hP_cont (ε / (2 * C1)) (by positivity)
  refine Filter.eventually_of_mem ((tendsto_order.1 hεn_tend).2 η hη) fun n hn_lt => ?_
  change εn n < η at hn_lt
  rw [dist_zero_right, (hseam_eq n).2]
  have hconst_int : IntegrableOn
      (fun _ : ℝ => Cb * (εn n)⁻¹ * (ε / (2 * C1))) (Icc (T - εn n) (T + εn n)) volume :=
    integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hnorm_le : ∀ s ∈ Icc (T - εn n) (T + εn n),
      ‖((deriv (theta T (εn n)) s : ℝ) : ℂ) * (P s - P T)‖ ≤
        Cb * (εn n)⁻¹ * (ε / (2 * C1)) := by
    intro s hs
    have hs_dist : dist s T < η := by
      rw [Real.dist_eq, abs_lt]
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hPs : ‖P s - P T‖ ≤ ε / (2 * C1) := (dist_eq_norm (P s) (P T) ▸ hP_ball hs_dist).le
    have hds : ‖((deriv (theta T (εn n)) s : ℝ) : ℂ)‖ ≤ Cb * (εn n)⁻¹ := by
      rw [Complex.norm_real, Real.norm_eq_abs, deriv_theta_eq (hεn_pos n) s, abs_mul,
        abs_inv, abs_of_pos (hεn_pos n)]
      exact mul_le_mul_of_nonneg_right (hCb _) (inv_nonneg.2 (hεn_pos n).le)
    rw [norm_mul]
    exact mul_le_mul hds hPs (norm_nonneg _) (mul_nonneg hCb_nn (inv_nonneg.2 (hεn_pos n).le))
  have hI_sub_norm : IntegrableOn
      (fun s => ‖((deriv (theta T (εn n)) s : ℝ) : ℂ) * (P s - P T)‖)
      (Icc (T - εn n) (T + εn n)) volume := Integrable.norm (hseam_eq n).1
  calc ‖∫ s in Icc (T - εn n) (T + εn n),
          ((deriv (theta T (εn n)) s : ℝ) : ℂ) * (P s - P T)‖
      ≤ ∫ s in Icc (T - εn n) (T + εn n),
          ‖((deriv (theta T (εn n)) s : ℝ) : ℂ) * (P s - P T)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ _s in Icc (T - εn n) (T + εn n), (Cb * (εn n)⁻¹ * (ε / (2 * C1))) :=
        setIntegral_mono_on hI_sub_norm hconst_int measurableSet_Icc hnorm_le
    _ = (2 * Cb) * (ε / (2 * C1)) := by
        rw [setIntegral_const, smul_eq_mul, measureReal_def, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith [hεn_pos n])]
        have hlen : T + εn n - (T - εn n) = 2 * εn n := by ring
        rw [hlen]
        field_simp [(hεn_pos n).ne']
    _ ≤ C1 * (ε / (2 * C1)) :=
        mul_le_mul_of_nonneg_right (by dsimp [C1]; linarith) (by positivity)
    _ = ε / 2 := by field_simp [hC1_pos.ne']
    _ < ε := half_lt_self hε

/-! ### 6. Entrance `L²(cell)` curl trace transfer on `(0, T)` -/

private lemma cellMeasure_zero' (c : ℝ) :
    B0579.cellMeasure c 0 = volume.restrict (B0579.cell c) := by
  unfold B0579.cellMeasure
  have h1 : (fun x => (B0579.density 0 x : ℝ≥0∞)) = fun _ => 1 := by
    funext x; simp [B0579.density]
  rw [h1]; exact withDensity_one

private lemma eLpNorm_two_sub_le' {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} {m m' e : X → E}
    (hm : AEStronglyMeasurable m μ) (hm' : AEStronglyMeasurable m' μ) :
    eLpNorm (m - e) 2 μ ≤ eLpNorm (m' - e) 2 μ + eLpNorm (m - m') 2 μ := by
  have two : (2 : ℝ≥0∞).toReal = 2 := rfl
  have key : ∀ f : X → E, eLpNorm f 2 μ = (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    intro f
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), two]
  rw [key, key, key]
  obtain ⟨g, hg, hgle, hint⟩ :=
    exists_measurable_le_lintegral_eq μ (fun x => ‖(m - e) x‖ₑ ^ (2 : ℝ))
  set d : X → ℝ≥0∞ := fun x => ‖(m - m') x‖ₑ
  have hdm : AEMeasurable d μ := (hm.sub hm').enorm
  let k : X → ℝ≥0∞ := fun x => g x ^ (1 / (2 : ℝ))
  have hk : Measurable k := hg.pow_const _
  have hk2 : ∀ x, k x ^ (2 : ℝ) = g x := by
    intro x; simp only [k]; rw [← ENNReal.rpow_mul]; norm_num
  have hkle : ∀ x, k x ≤ ‖(m - e) x‖ₑ := by
    intro x
    have := ENNReal.rpow_le_rpow (hgle x) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    refine this.trans (le_of_eq ?_)
    rw [← ENNReal.rpow_mul]; norm_num
  have hk' : ∀ x, k x - d x ≤ ‖(m' - e) x‖ₑ := by
    intro x
    rw [tsub_le_iff_right]
    refine (hkle x).trans ?_
    have : (m - e) x = (m' - e) x + (m - m') x := by simp
    rw [this]; exact enorm_add_le _ _
  have hkd : AEMeasurable (k - d) μ := hk.aemeasurable.sub hdm
  rw [hint]
  calc (∫⁻ a, g a ∂μ) ^ (1 / (2 : ℝ)) = (∫⁻ a, k a ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
        simp_rw [hk2]
    _ ≤ (∫⁻ a, ((k - d) + d) a ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
        refine ENNReal.rpow_le_rpow (lintegral_mono fun a => ?_) (by norm_num)
        exact ENNReal.rpow_le_rpow (by simpa using (le_tsub_add : k a ≤ k a - d a + d a))
          (by norm_num)
    _ ≤ (∫⁻ a, (k - d) a ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) +
          (∫⁻ a, d a ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) :=
        ENNReal.lintegral_Lp_add_le hkd hdm (by norm_num)
    _ ≤ _ := by
        gcongr with a
        exact hk' a

private lemma ae_Ioc_le_of_ae_Ioo_and_cont' {T : ℝ} {G : ℝ → ℝ≥0∞} {B : ℝ≥0∞}
    (hgood : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ioo 0 T → G s ≤ B)
    (hcont : ∀ s ∈ Ioc 0 T, ∀ ε : ℝ≥0∞, ε ≠ 0 → ∀ᶠ s' in 𝓝[Ioc 0 T] s, G s ≤ G s' + ε) :
    ∀ s ∈ Ioc 0 T, G s ≤ B := by
  intro s hs
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have h1 := hcont s hs ε (by simpa using hε.ne')
  obtain ⟨U, hU_nhds, hU_sub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 h1
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hU_nhds
  set a₀ : ℝ := max 0 (s - δ)
  have ha₀_lt : a₀ < s := max_lt hs.1 (by linarith)
  have hV_pos : 0 < volume (Ioo a₀ s) :=
    isOpen_Ioo.measure_pos volume ⟨(a₀ + s) / 2, by linarith, by linarith⟩
  have hN : volume {s' : ℝ | ¬(s' ∈ Ioo 0 T → G s' ≤ B)} = 0 := ae_iff.1 hgood
  obtain ⟨s', hs'V, hs'N⟩ : ∃ s' ∈ Ioo a₀ s, s' ∉ {s' : ℝ | ¬(s' ∈ Ioo 0 T → G s' ≤ B)} := by
    by_contra hcon
    have hsub : Ioo a₀ s ⊆ {s' : ℝ | ¬(s' ∈ Ioo 0 T → G s' ≤ B)} := fun x hxV => by
      by_contra hx
      exact hcon ⟨x, hxV, hx⟩
    exact hV_pos.ne' (measure_mono_null hsub hN)
  have hs'_pos : 0 < s' := (le_max_left 0 (s - δ)).trans_lt hs'V.1
  have hs'_ltT : s' < T := hs'V.2.trans_le hs.2
  have hs'_Ioo : s' ∈ Ioo 0 T := ⟨hs'_pos, hs'_ltT⟩
  have hs'_Ioc : s' ∈ Ioc 0 T := ⟨hs'_pos, hs'_ltT.le⟩
  have hs'_ball : s' ∈ Metric.ball s δ := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    have hle : s - δ ≤ a₀ := le_max_right 0 (s - δ)
    exact ⟨by linarith [hs'V.1], by linarith [hs'V.2]⟩
  have hG_s' : G s' ≤ B := by
    by_contra hh
    exact hs'N (fun h' => hh (h' hs'_Ioo))
  exact (hU_sub ⟨hball hs'_ball, hs'_Ioc⟩).trans (add_le_add_left hG_s' _)

private lemma initial_curl_glue {c T : ℝ} (hT : 0 < T)
    {z₁ zq₁ zη₁ zq₂ zη₂ zq_eb zη_eb : CProf}
    (hzq₁ : StronglyMeasurable zq₁) (hzη₁ : StronglyMeasurable zη₁)
    (hzq₂ : StronglyMeasurable zq₂) (hzη₂ : StronglyMeasurable zη₂)
    (hcont₁ : ∀ s ∈ Ioc 0 T,
      Tendsto (fun s' => cylSliceH1 c
        (fun y => z₁ (s', y) - z₁ (s, y))
        (fun y => zq₁ (s', y) - zq₁ (s, y))
        (fun y => zη₁ (s', y) - zη₁ (s, y))) (𝓝[Ioc 0 T] s) (𝓝 0))
    (haq : ∀ᵐ x : Coord, x.1 ∈ Ioo 0 T → zq₁ x = zq_eb x)
    (haη : ∀ᵐ x : Coord, x.1 ∈ Ioo 0 T → zη₁ x = zη_eb x)
    (ent : B0579.Plane → ℝ)
    (h0 : Tendsto (fun s => eLpNorm (fun x => profCurl zq_eb zη_eb (s, x) - ((ent x : ℝ) : ℂ)) 2
      (B0579.cellMeasure c 0)) (𝓝[Ioi 0] 0) (𝓝 0)) :
    Tendsto (fun s => eLpNorm
        (fun x => profCurl (glueAtHorizon T zq₁ zq₂) (glueAtHorizon T zη₁ zη₂) (s, x) -
          ((ent x : ℝ) : ℂ))
        2 (B0579.cellMeasure c 0))
      (𝓝[Ioi 0] 0) (𝓝 0) := by
  set Zq := glueAtHorizon T zq₁ zq₂
  set Zη := glueAtHorizon T zη₁ zη₂
  have hZq : StronglyMeasurable Zq := stronglyMeasurable_glue T hzq₁ hzq₂
  have hZη : StronglyMeasurable Zη := stronglyMeasurable_glue T hzη₁ hzη₂
  have haq' : ∀ᵐ x : Coord, x.1 ∈ Ioo 0 T → Zq x = zq_eb x :=
    haq.mono fun x hx hm => by simp [Zq, glueAtHorizon, hm.2.le, hx hm]
  have haη' : ∀ᵐ x : Coord, x.1 ∈ Ioo 0 T → Zη x = zη_eb x :=
    haη.mono fun x hx hm => by simp [Zη, glueAtHorizon, hm.2.le, hx hm]
  have hslice_ae : ∀ {u v : CProf}, (∀ᵐ x : Coord, x.1 ∈ Ioo 0 T → u x = v x) →
      ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ioo 0 T →
        (fun y => u (s, y)) =ᵐ[volume.restrict (B0579.cell c)] (fun y => v (s, y)) := by
    intro u v h
    filter_upwards [Measure.ae_ae_of_ae_prod h] with s hs hsT
    exact ae_restrict_of_ae (hs.mono fun y hy => hy hsT)
  have hcurl_le : ∀ s s' : ℝ,
      eLpNorm (fun x => profCurl Zq Zη (s, x) - ((ent x : ℝ) : ℂ)) 2 (B0579.cellMeasure c 0) ≤
        eLpNorm (fun x => profCurl Zq Zη (s', x) - ((ent x : ℝ) : ℂ)) 2 (B0579.cellMeasure c 0) +
          (cylSliceL2 c (fun y => Zq (s', y) - Zq (s, y)) +
            cylSliceL2 c (fun y => Zη (s', y) - Zη (s, y))) := by
    intro s s'
    rw [cellMeasure_zero']
    set μ : Measure B0579.Plane := volume.restrict (B0579.cell c)
    let m : B0579.Plane → ℂ := fun x => profCurl Zq Zη (s, x)
    let m' : B0579.Plane → ℂ := fun x => profCurl Zq Zη (s', x)
    let e : B0579.Plane → ℂ := fun x => ((ent x : ℝ) : ℂ)
    have hm : StronglyMeasurable m :=
      (compMeas (sliceMeas hZq s) 1).sub (compMeas (sliceMeas hZη s) 0)
    have hm' : StronglyMeasurable m' :=
      (compMeas (sliceMeas hZq s') 1).sub (compMeas (sliceMeas hZη s') 0)
    refine (eLpNorm_two_sub_le' (μ := μ) (e := e)
      hm.aestronglyMeasurable hm'.aestronglyMeasurable).trans (add_le_add_right ?_ _)
    let Dq : B0579.Plane → CMerid := fun y => Zq (s', y) - Zq (s, y)
    let Dη : B0579.Plane → CMerid := fun y => Zη (s', y) - Zη (s, y)
    have hDq : StronglyMeasurable Dq := (sliceMeas hZq s').sub (sliceMeas hZq s)
    have hDη : StronglyMeasurable Dη := (sliceMeas hZη s').sub (sliceMeas hZη s)
    have hb : ∀ x, ‖(m - m') x‖ ≤ ‖‖Dq x‖ + ‖Dη x‖‖ := by
      intro x
      have e1 : (m - m') x = -(Dq x 1) + Dη x 0 := by
        simp [m, m', Dq, Dη, profCurl]; ring
      rw [e1, Real.norm_of_nonneg (by positivity)]
      refine (norm_add_le _ _).trans ?_
      rw [norm_neg]
      exact add_le_add (PiLp.norm_apply_le _ _) (PiLp.norm_apply_le _ _)
    calc eLpNorm (m - m') 2 μ ≤ eLpNorm (fun x => ‖Dq x‖ + ‖Dη x‖) 2 μ := eLpNorm_mono hb
      _ ≤ eLpNorm (fun x => ‖Dq x‖) 2 μ + eLpNorm (fun x => ‖Dη x‖) 2 μ :=
          eLpNorm_add_le hDq.norm.aestronglyMeasurable hDη.norm.aestronglyMeasurable (by norm_num)
      _ = cylSliceL2 c (fun y => Zq (s', y) - Zq (s, y)) +
            cylSliceL2 c (fun y => Zη (s', y) - Zη (s, y)) := by
          simp only [cylSliceL2, eLpNorm_norm]; rfl
  rw [ENNReal.tendsto_nhds_zero] at h0 ⊢
  intro ε hε
  obtain ⟨δ₀, hδ₀, hsub⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.1 (h0 (ε / 2) (ENNReal.half_pos hε.ne'))
  set δ : ℝ := min T δ₀
  have hδ : 0 < δ := lt_min hT hδ₀
  set φ : ℝ → ℝ≥0∞ := fun s =>
    eLpNorm (fun x => profCurl Zq Zη (s, x) - ((ent x : ℝ) : ℂ)) 2 (B0579.cellMeasure c 0)
  have key : ∀ s ∈ Ioc 0 δ, φ s ≤ ε / 2 := by
    refine ae_Ioc_le_of_ae_Ioo_and_cont' ?_ ?_
    · filter_upwards [hslice_ae haq', hslice_ae haη'] with s e1 e2 hs
      have hsT : s ∈ Ioo 0 T := ⟨hs.1, hs.2.trans_le (min_le_left _ _)⟩
      have hsδ₀ : s ∈ Ioo 0 δ₀ := ⟨hs.1, hs.2.trans_le (min_le_right _ _)⟩
      have heq : φ s = eLpNorm (fun x => profCurl zq_eb zη_eb (s, x) - ((ent x : ℝ) : ℂ)) 2
          (B0579.cellMeasure c 0) := by
        dsimp [φ]
        rw [cellMeasure_zero']
        refine eLpNorm_congr_ae ?_
        filter_upwards [e1 hsT, e2 hsT] with x x1 x2
        simp [profCurl, x1, x2]
      rw [heq]
      exact hsub hsδ₀
    · intro s hs ε' hε'
      have hsT : s ∈ Ioc 0 T := ⟨hs.1, hs.2.trans (min_le_left _ _)⟩
      have hmono_nhds : 𝓝[Ioc 0 δ] s ≤ 𝓝[Ioc 0 T] s :=
        nhdsWithin_mono s (Ioc_subset_Ioc_right (min_le_left _ _))
      have hsum : Tendsto (fun s' =>
          cylSliceL2 c (fun y => Zq (s', y) - Zq (s, y)) +
            cylSliceL2 c (fun y => Zη (s', y) - Zη (s, y))) (𝓝[Ioc 0 δ] s) (𝓝 0) := by
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
          ((hcont₁ s hsT).mono_left hmono_nhds) (Eventually.of_forall fun _ => zero_le) ?_
        filter_upwards [self_mem_nhdsWithin] with s' hs'
        have hs'_le : s' ≤ T := hs'.2.trans (min_le_left _ _)
        have h1 : (fun y => Zq (s', y) - Zq (s, y)) = fun y => zq₁ (s', y) - zq₁ (s, y) := by
          funext y; simp [Zq, glueAtHorizon, hs'_le, hsT.2]
        have h2 : (fun y => Zη (s', y) - Zη (s, y)) = fun y => zη₁ (s', y) - zη₁ (s, y) := by
          funext y; simp [Zη, glueAtHorizon, hs'_le, hsT.2]
        rw [h1, h2]
        unfold cylSliceH1
        rw [add_assoc]
        exact le_add_of_nonneg_left zero_le
      have hnear := (ENNReal.tendsto_nhds_zero.1 hsum) ε' (pos_iff_ne_zero.2 hε')
      filter_upwards [hnear] with s' hs'
      exact (hcurl_le s s').trans (add_le_add_right hs' _)
  filter_upwards [Ioo_mem_nhdsGT hδ] with s hs
  exact (key s ⟨hs.1, hs.2.le⟩).trans ENNReal.half_le_self

/-! ### 7. Assembly of `IsGlobalMeridionalCorrection` across the horizon `s = T` -/

private lemma isGlobalMeridionalCorrection_glue {p : Params} {d dm dp T M : ℝ} {α : E2}
    (hbg : BgRegime p d dm dp) (hT : 0 < T) (hM : 0 ≤ M)
    {g gq gη z_eb zq_eb zη_eb z₁ zq₁ zη₁ z₂ zq₂ zη₂ : CProf}
    (hg : IsCylSourceH1 p.c g gq gη)
    (hg_early : (∫⁻ s in Ioc 0 T, sliceH1Norm p.c g gq gη s) < ⊤)
    (hg_tail : (∫⁻ s in Ioi T, sliceH1Norm p.c g gq gη s) < ⊤)
    (heb : IsMeridionalCorrectionOn p T g z_eb zq_eb zη_eb α)
    (hz₁_sm : StronglyMeasurable z₁) (hzq₁_sm : StronglyMeasurable zq₁)
    (hzη₁_sm : StronglyMeasurable zη₁)
    (hper_all : ∀ x : Coord,
      z₁ (qShift p.c x) = z₁ x ∧ zq₁ (qShift p.c x) = zq₁ x ∧ zη₁ (qShift p.c x) = zη₁ x)
    (hae_eb : ∀ᵐ x : Coord, x.1 ∈ Ioo 0 T →
      z₁ x = z_eb x ∧ zq₁ x = zq_eb x ∧ zη₁ x = zη_eb x)
    (hcont₁ : ∀ s ∈ Ioc 0 T,
      Tendsto (fun s' => cylSliceH1 p.c
        (fun y => z₁ (s', y) - z₁ (s, y))
        (fun y => zq₁ (s', y) - zq₁ (s, y))
        (fun y => zη₁ (s', y) - zη₁ (s, y))) (𝓝[Ioc 0 T] s) (𝓝 0))
    (hbdd₁ : ∀ s ∈ Ioc 0 T, sliceH1Norm p.c z₁ zq₁ zη₁ s ≤ ENNReal.ofReal (3 * M))
    (h_wq₁ : ∀ i : Fin 2, ∀ φ, IsCoordTest φ → tsupport φ ⊆ Ioo 0 T ×ˢ univ →
      Integrable (fun x => z₁ x i * (coordTranspose vQ0 dZero φ x : ℂ)) ∧
        Integrable (fun x => zq₁ x i * (φ x : ℂ)) ∧
        ∫ x, zq₁ x i * (φ x : ℂ) = ∫ x, z₁ x i * (coordTranspose vQ0 dZero φ x : ℂ))
    (h_wη₁ : ∀ i : Fin 2, ∀ φ, IsCoordTest φ → tsupport φ ⊆ Ioo 0 T ×ˢ univ →
      Integrable (fun x => z₁ x i * (coordTranspose vEta dZero φ x : ℂ)) ∧
        Integrable (fun x => zη₁ x i * (φ x : ℂ)) ∧
        ∫ x, zη₁ x i * (φ x : ℂ) = ∫ x, z₁ x i * (coordTranspose vEta dZero φ x : ℂ))
    (h_sol₁ : ∀ φ, IsCoordTest φ → tsupport φ ⊆ Ioo 0 T ×ˢ univ →
      Integrable (fun x => z₁ x 0 * (cpd 1 φ x : ℂ) + z₁ x 1 * (cpd 2 φ x : ℂ)) ∧
        ∫ x, (z₁ x 0 * (cpd 1 φ x : ℂ) + z₁ x 1 * (cpd 2 φ x : ℂ)) = 0)
    (h_eq₁ : ∀ Ψ, IsPlanarSolTest Ψ → (∀ i, tsupport (fun x => Ψ x i) ⊆ Ioo 0 T ×ˢ univ) →
      Integrable (fun x => ∑ i : Fin 2, z₁ x i * meridTranspose p.ν Ψ x i) ∧
        Integrable (cdot (flatBv p.train z₁ zq₁ zη₁) Ψ) ∧
        Integrable (cdot g Ψ) ∧
        ∫ x, (∑ i : Fin 2, z₁ x i * meridTranspose p.ν Ψ x i +
            cdot (flatBv p.train z₁ zq₁ zη₁) Ψ x) =
          ∫ x, cdot g Ψ x)
    (hz₂_sm : StronglyMeasurable z₂) (hzq₂_sm : StronglyMeasurable zq₂)
    (hzη₂_sm : StronglyMeasurable zη₂)
    (hmatch : cylSliceH1 p.c (fun y => z₂ (T, y) - z₁ (T, y))
      (fun y => zq₂ (T, y) - zq₁ (T, y)) (fun y => zη₂ (T, y) - zη₁ (T, y)) = 0)
    (h₂ : IsTailMeridionalSolution p T g z₂ zq₂ zη₂)
    (hcont₂ : ∀ s : ℝ, T ≤ s →
      Tendsto (fun s' => cylSliceH1 p.c
        (fun y => z₂ (s', y) - z₂ (s, y))
        (fun y => zq₂ (s', y) - zq₂ (s, y))
        (fun y => zη₂ (s', y) - zη₂ (s, y))) (𝓝[Ici T] s) (𝓝 0)) :
    IsGlobalMeridionalCorrection p g
      (glueAtHorizon T z₁ z₂) (glueAtHorizon T zq₁ zq₂) (glueAtHorizon T zη₁ zη₂) α := by
  have hc : 0 < p.c := p.c_pos
  set Z := glueAtHorizon T z₁ z₂
  set Zq := glueAtHorizon T zq₁ zq₂
  set Zη := glueAtHorizon T zη₁ zη₂
  have hZ_sm : StronglyMeasurable Z := stronglyMeasurable_glue T hz₁_sm hz₂_sm
  have hZq_sm : StronglyMeasurable Zq := stronglyMeasurable_glue T hzq₁_sm hzq₂_sm
  have hZη_sm : StronglyMeasurable Zη := stronglyMeasurable_glue T hzη₁_sm hzη₂_sm
  have hZ_per : QPeriodic p.c Z :=
    qPeriodic_glue p.c T (fun x => (hper_all x).1) (h₂.periodic.mono fun x hx hp => (hx hp).1)
  have hZq_per : QPeriodic p.c Zq :=
    qPeriodic_glue p.c T (fun x => (hper_all x).2.1) (h₂.periodic.mono fun x hx hp => (hx hp).2.1)
  have hZη_per : QPeriodic p.c Zη :=
    qPeriodic_glue p.c T (fun x => (hper_all x).2.2) (h₂.periodic.mono fun x hx hp => (hx hp).2.2)
  have hZ_loc : ∀ {a b : ℝ}, 0 < a → a ≤ b →
      ∃ K : ℝ, ∀ s ∈ Icc a b, cylSliceL2 p.c (fun y => Z (s, y)) ≤ ENNReal.ofReal K := by
    intro a b ha hab
    obtain ⟨K, _, hK⟩ := exists_glued_sliceH1Norm_bound hT hM hz₁_sm hzq₁_sm hzη₁_sm
      hz₂_sm hzq₂_sm hzη₂_sm hbdd₁ hmatch hcont₂ ha hab
    exact ⟨K, fun s hs => ((le_add_of_nonneg_right zero_le).trans
      (le_add_of_nonneg_right zero_le)).trans (hK s hs)⟩
  have hZq_loc : ∀ {a b : ℝ}, 0 < a → a ≤ b →
      ∃ K : ℝ, ∀ s ∈ Icc a b, cylSliceL2 p.c (fun y => Zq (s, y)) ≤ ENNReal.ofReal K := by
    intro a b ha hab
    obtain ⟨K, _, hK⟩ := exists_glued_sliceH1Norm_bound hT hM hz₁_sm hzq₁_sm hzη₁_sm
      hz₂_sm hzq₂_sm hzη₂_sm hbdd₁ hmatch hcont₂ ha hab
    exact ⟨K, fun s hs => ((le_add_of_nonneg_left zero_le).trans
      (le_add_of_nonneg_right zero_le)).trans (hK s hs)⟩
  have hZη_loc : ∀ {a b : ℝ}, 0 < a → a ≤ b →
      ∃ K : ℝ, ∀ s ∈ Icc a b, cylSliceL2 p.c (fun y => Zη (s, y)) ≤ ENNReal.ofReal K := by
    intro a b ha hab
    obtain ⟨K, _, hK⟩ := exists_glued_sliceH1Norm_bound hT hM hz₁_sm hzq₁_sm hzη₁_sm
      hz₂_sm hzq₂_sm hzη₂_sm hbdd₁ hmatch hcont₂ ha hab
    exact ⟨K, fun s hs => (le_add_of_nonneg_left zero_le).trans (hK s hs)⟩
  have hint_Z : ∀ (i : Fin 2) {φ : Coord → ℝ}, IsCoordTest φ →
      Integrable (fun x => Z x i * (φ x : ℂ)) volume := by
    intro i φ hφ
    exact integrable_coord_mul_isCoordTest hc hZ_sm hZ_per hZ_loc i hφ
  have hint_Zq : ∀ (i : Fin 2) {φ : Coord → ℝ}, IsCoordTest φ →
      Integrable (fun x => Zq x i * (φ x : ℂ)) volume := by
    intro i φ hφ
    exact integrable_coord_mul_isCoordTest hc hZq_sm hZq_per hZq_loc i hφ
  have hint_Zη : ∀ (i : Fin 2) {φ : Coord → ℝ}, IsCoordTest φ →
      Integrable (fun x => Zη x i * (φ x : ℂ)) volume := by
    intro i φ hφ
    exact integrable_coord_mul_isCoordTest hc hZη_sm hZη_per hZη_loc i hφ
  have hint_Bv : ∀ (i : Fin 2) {φ : Coord → ℝ}, IsCoordTest φ →
      Integrable (fun x => flatBv p.train Z Zq Zη x i * (φ x : ℂ)) volume := by
    intro i φ hφ
    obtain ⟨a, b, R, ha, hab, hR, hbox⟩ := TailPeriodizeAux.coordTest_box hφ
    set B := max T (b + 1)
    have hB_pos : 0 < B := lt_of_lt_of_le hT (le_max_left _ _)
    obtain ⟨C_tr, hC_tr, hb_le⟩ := exists_bCut_sliceL2_bound hbg hB_pos Z Zq Zη hZ_sm hZq_sm hZη_sm
    obtain ⟨K, hK_nn, hK⟩ := exists_glued_sliceH1Norm_bound hT hM hz₁_sm hzq₁_sm hzη₁_sm
      hz₂_sm hzq₂_sm hzη₂_sm hbdd₁ hmatch hcont₂ ha hab
    have hB_bdd : ∀ s ∈ Icc a b,
        cylSliceL2 p.c (fun y => bCut p B Z Zq Zη (s, y)) ≤ ENNReal.ofReal (C_tr * K) := by
      intro s hs
      have hs_oc : s ∈ Ioc 0 B :=
        ⟨lt_of_lt_of_le ha hs.1, (hs.2.trans (lt_add_one b).le).trans (le_max_right T (b + 1))⟩
      calc cylSliceL2 p.c (fun y => bCut p B Z Zq Zη (s, y))
          ≤ ENNReal.ofReal C_tr * sliceH1Norm p.c Z Zq Zη s := hb_le s hs_oc
        _ ≤ ENNReal.ofReal C_tr * ENNReal.ofReal K := by gcongr; exact hK s hs
        _ = ENNReal.ofReal (C_tr * K) := (ENNReal.ofReal_mul hC_tr).symm
    have hI_cut := (integrable_coord_of_sliceBound hc ha hab hR
      (stronglyMeasurable_bCut p B hZ_sm hZq_sm hZη_sm)
      (qPeriodic_bCut p B hZ_per hZq_per hZη_per)
      hB_bdd i hφ.smooth.continuous fun x hx => (hbox x hx).1).1
    refine hI_cut.congr (ae_of_all _ fun x => ?_)
    by_cases hx : x.1 ∈ Icc a b
    · have hx_oc : x.1 ∈ Ioc 0 B :=
        ⟨lt_of_lt_of_le ha hx.1, (hx.2.trans (lt_add_one b).le).trans (le_max_right T (b + 1))⟩
      simp [bCut, hx_oc]
    · simp [(hbox x (Or.inl hx)).1]
  have hint_g : ∀ (i : Fin 2) {φ : Coord → ℝ}, IsCoordTest φ →
      Integrable (fun x => g x i * (φ x : ℂ)) volume := by
    intro i φ hφ
    exact integrable_source_mul_isCoordTest hc hg hg_early hg_tail i hφ
  -- Cutoff scale sequence `εn n → 0`
  let εn : ℕ → ℝ := fun n => min (T / 2) 1 / ((n : ℝ) + 2)
  have hεn_pos : ∀ n, 0 < εn n := fun n =>
    div_pos (lt_min (half_pos hT) one_pos) (by positivity)
  have hεn_le : ∀ n, εn n ≤ T / 2 := fun n => by
    dsimp [εn]
    calc min (T / 2) 1 / ((n : ℝ) + 2)
        ≤ min (T / 2) 1 / 1 :=
          div_le_div_of_nonneg_left (le_min (half_pos hT).le zero_le_one) one_pos (by linarith)
      _ ≤ T / 2 := by rw [div_one]; exact min_le_left _ _
  have hεn_tend : Tendsto εn atTop (𝓝 0) := by
    have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    simpa [εn, div_eq_mul_inv] using hinv.const_mul (min (T / 2) 1)
  -- Unified helper for `HasWeakVec` (`weak_q` and `weak_eta`)
  have hweak_glue : ∀ (j : Fin 2) (Zd zd₁ zd₂ : CProf),
      (Zd = glueAtHorizon T zd₁ zd₂) →
      (∀ (i : Fin 2) {φ : Coord → ℝ}, IsCoordTest φ →
        Integrable (fun x => Zd x i * (φ x : ℂ)) volume) →
      (∀ i : Fin 2, ∀ φ, IsCoordTest φ → tsupport φ ⊆ Ioo 0 T ×ˢ univ →
        ∫ x, zd₁ x i * (φ x : ℂ) =
          ∫ x, z₁ x i * (coordTranspose (![vQ0, vEta] j) dZero φ x : ℂ)) →
      (∀ i : Fin 2, ∀ φ, IsCoordTest φ → tsupport φ ⊆ Ioi T ×ˢ univ →
        ∫ x, zd₂ x i * (φ x : ℂ) =
          ∫ x, z₂ x i * (coordTranspose (![vQ0, vEta] j) dZero φ x : ℂ)) →
      HasWeakVec (![vQ0, vEta] j) dZero Z Zd := by
    intro j Zd zd₁ zd₂ hZd hint_Zd hw₁ hw₂ i
    have htr_test : ∀ {φ : Coord → ℝ}, IsCoordTest φ →
        IsCoordTest (coordTranspose (![vQ0, vEta] j) dZero φ) := fun {φ} hφ => by
      have heq_tr : coordTranspose (![vQ0, vEta] j) dZero φ = fun x => -cpd j.succ φ x :=
        funext fun x => TailPeriodizeAux.coordTranspose_vQ0_vEta j φ x
      rw [heq_tr]
      exact planarTest_isCoordTest_neg (planarTest_isCoordTest_partial hφ (cdir j.succ))
    refine ⟨fun φ hφ => ⟨hint_Z i (htr_test hφ), hint_Zd i hφ⟩, fun φ hφ => ?_⟩
    have hI_lhs := hint_Zd i hφ
    have hI_rhs := hint_Z i (htr_test hφ)
    have hdiff_zero : ∀ n : ℕ,
        (∫ x, Zd x i * (φ x : ℂ)) -
          (∫ x, Z x i * (coordTranspose (![vQ0, vEta] j) dZero φ x : ℂ)) =
        (∫ x, (theta T (εn n) x.1 : ℂ) * (Zd x i * (φ x : ℂ))) -
          (∫ x, (theta T (εn n) x.1 : ℂ) *
            (Z x i * (coordTranspose (![vQ0, vEta] j) dZero φ x : ℂ))) := by
      intro n
      let φL : Coord → ℝ := fun x => etaL T (εn n) x.1 * φ x
      let φM : Coord → ℝ := fun x => theta T (εn n) x.1 * φ x
      let φR : Coord → ℝ := fun x => etaR T (εn n) x.1 * φ x
      have hφL : IsCoordTest φL := isCoordTest_time_mul (contDiff_etaL (hεn_pos n)) hφ
      have hφM : IsCoordTest φM := isCoordTest_time_mul (contDiff_theta (hεn_pos n)) hφ
      have hφR : IsCoordTest φR := isCoordTest_time_mul (contDiff_etaR (hεn_pos n)) hφ
      have hsuppL := tsupport_etaL_mul_subset (T := T) (hεn_pos n) hφ
      have hsuppR := tsupport_etaR_mul_subset (T := T) (hεn_pos n) φ
      have hsum_φ : ∀ x, φ x = φL x + φM x + φR x := fun x => by
        dsimp [φL, φM, φR]
        rw [← add_mul, ← add_mul, etaL_add_theta_add_etaR, one_mul]
      have hsum_tr : ∀ x, coordTranspose (![vQ0, vEta] j) dZero φ x =
          coordTranspose (![vQ0, vEta] j) dZero φL x +
            coordTranspose (![vQ0, vEta] j) dZero φM x +
            coordTranspose (![vQ0, vEta] j) dZero φR x := fun x => by
        rw [coordTranspose_time_mul (contDiff_etaL (hεn_pos n)) hφ.smooth j x,
          coordTranspose_time_mul (contDiff_theta (hεn_pos n)) hφ.smooth j x,
          coordTranspose_time_mul (contDiff_etaR (hεn_pos n)) hφ.smooth j x,
          ← add_mul, ← add_mul, etaL_add_theta_add_etaR, one_mul]
      have hL_eq : (∫ x, Zd x i * (φL x : ℂ)) =
          ∫ x, Z x i * (coordTranspose (![vQ0, vEta] j) dZero φL x : ℂ) := by
        have e1 : (fun x => Zd x i * (φL x : ℂ)) = fun x => zd₁ x i * (φL x : ℂ) := by
          funext x
          by_cases hle : x.1 ≤ T
          · simp [hZd, glueAtHorizon, hle]
          · have hm : x.1 ∉ Ioo 0 T := fun h => hle h.2.le
            have h0 : φL x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hm (hsuppL h).1)
            simp [h0]
        have e2 : (fun x => Z x i * (coordTranspose (![vQ0, vEta] j) dZero φL x : ℂ)) =
            fun x => z₁ x i * (coordTranspose (![vQ0, vEta] j) dZero φL x : ℂ) := by
          funext x
          by_cases hle : x.1 ≤ T
          · simp [Z, glueAtHorizon, hle]
          · have hm : x.1 ∉ Ioo 0 T := fun h => hle h.2.le
            rw [TailPeriodizeAux.coordTranspose_vQ0_vEta j φL x,
              (tsupport_cpd2_zero hsuppL j.succ j.succ hm).1]
            simp
        rw [e1, e2, hw₁ i φL hφL hsuppL]
      have hR_eq : (∫ x, Zd x i * (φR x : ℂ)) =
          ∫ x, Z x i * (coordTranspose (![vQ0, vEta] j) dZero φR x : ℂ) := by
        have e1 : (fun x => Zd x i * (φR x : ℂ)) = fun x => zd₂ x i * (φR x : ℂ) := by
          funext x
          by_cases hle : x.1 ≤ T
          · have hm : x.1 ∉ Ioi T := not_lt.2 hle
            have h0 : φR x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hm (hsuppR h).1)
            simp [h0]
          · simp [hZd, glueAtHorizon, hle]
        have e2 : (fun x => Z x i * (coordTranspose (![vQ0, vEta] j) dZero φR x : ℂ)) =
            fun x => z₂ x i * (coordTranspose (![vQ0, vEta] j) dZero φR x : ℂ) := by
          funext x
          by_cases hle : x.1 ≤ T
          · have hm : x.1 ∉ Ioi T := not_lt.2 hle
            rw [TailPeriodizeAux.coordTranspose_vQ0_vEta j φR x,
              (tsupport_cpd2_zero hsuppR j.succ j.succ hm).1]
            simp
          · simp [Z, glueAtHorizon, hle]
        rw [e1, e2, hw₂ i φR hφR hsuppR]
      have ilL := hint_Zd i hφL
      have ilM := hint_Zd i hφM
      have ilR := hint_Zd i hφR
      have ilLM : Integrable (fun x => Zd x i * (φL x : ℂ) + Zd x i * (φM x : ℂ)) volume :=
        ilL.add ilM
      have irL := hint_Z i (htr_test hφL)
      have irM := hint_Z i (htr_test hφM)
      have irR := hint_Z i (htr_test hφR)
      have irLM : Integrable (fun x => Z x i * (coordTranspose (![vQ0, vEta] j) dZero φL x : ℂ) +
          Z x i * (coordTranspose (![vQ0, vEta] j) dZero φM x : ℂ)) volume := irL.add irM
      have hl_split : (∫ x, Zd x i * (φ x : ℂ)) =
          (∫ x, Zd x i * (φL x : ℂ)) + (∫ x, Zd x i * (φM x : ℂ)) +
            (∫ x, Zd x i * (φR x : ℂ)) := by
        have hfun : (fun x => Zd x i * (φ x : ℂ)) =
            fun x => (Zd x i * (φL x : ℂ) + Zd x i * (φM x : ℂ)) + Zd x i * (φR x : ℂ) := by
          funext x; rw [hsum_φ x]; push_cast; ring
        rw [hfun, integral_add ilLM ilR, integral_add ilL ilM]
      have hr_split : (∫ x, Z x i * (coordTranspose (![vQ0, vEta] j) dZero φ x : ℂ)) =
          (∫ x, Z x i * (coordTranspose (![vQ0, vEta] j) dZero φL x : ℂ)) +
            (∫ x, Z x i * (coordTranspose (![vQ0, vEta] j) dZero φM x : ℂ)) +
            (∫ x, Z x i * (coordTranspose (![vQ0, vEta] j) dZero φR x : ℂ)) := by
        have hfun : (fun x => Z x i * (coordTranspose (![vQ0, vEta] j) dZero φ x : ℂ)) =
            fun x => (Z x i * (coordTranspose (![vQ0, vEta] j) dZero φL x : ℂ) +
              Z x i * (coordTranspose (![vQ0, vEta] j) dZero φM x : ℂ)) +
              Z x i * (coordTranspose (![vQ0, vEta] j) dZero φR x : ℂ) := by
          funext x; rw [hsum_tr x]; push_cast; ring
        rw [hfun, integral_add irLM irR, integral_add irL irM]
      have hm1 : (∫ x, Zd x i * (φM x : ℂ)) =
          ∫ x, (theta T (εn n) x.1 : ℂ) * (Zd x i * (φ x : ℂ)) := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        dsimp [φM]; push_cast; ring
      have hm2 : (∫ x, Z x i * (coordTranspose (![vQ0, vEta] j) dZero φM x : ℂ)) =
          ∫ x, (theta T (εn n) x.1 : ℂ) *
            (Z x i * (coordTranspose (![vQ0, vEta] j) dZero φ x : ℂ)) := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        dsimp [φM]
        rw [coordTranspose_time_mul (contDiff_theta (hεn_pos n)) hφ.smooth j x]
        push_cast; ring
      rw [hl_split, hr_split, hL_eq, hR_eq, hm1, hm2]
      ring
    have ht1 := tendsto_integral_theta_mul_zero T hεn_pos hεn_tend hI_lhs
    have ht2 := tendsto_integral_theta_mul_zero T hεn_pos hεn_tend hI_rhs
    have ht_diff : Tendsto (fun _ : ℕ =>
        (∫ x, Zd x i * (φ x : ℂ)) -
          (∫ x, Z x i * (coordTranspose (![vQ0, vEta] j) dZero φ x : ℂ))) atTop (𝓝 0) := by
      have h0 : Tendsto (fun n =>
          (∫ x, (theta T (εn n) x.1 : ℂ) * (Zd x i * (φ x : ℂ))) -
            (∫ x, (theta T (εn n) x.1 : ℂ) *
              (Z x i * (coordTranspose (![vQ0, vEta] j) dZero φ x : ℂ))))
          atTop (𝓝 (0 - 0)) := ht1.sub ht2
      rw [sub_self] at h0
      exact h0.congr fun n => (hdiff_zero n).symm
    exact sub_eq_zero.1 (tendsto_nhds_unique tendsto_const_nhds ht_diff)
  refine {
    periodic := hZ_per
    weak_q := hweak_glue 0 Zq zq₁ zq₂ rfl hint_Zq
      (fun i φ hφ hs => (h_wq₁ i φ hφ hs).2.2) (fun i φ hφ hs => (h₂.weak_q i φ hφ hs).2.2)
    weak_eta := hweak_glue 1 Zη zη₁ zη₂ rfl hint_Zη
      (fun i φ hφ hs => (h_wη₁ i φ hφ hs).2.2) (fun i φ hφ hs => (h₂.weak_eta i φ hφ hs).2.2)
    solenoidal := fun φ hφ => by
      have i0 := hint_Z 0 (planarTest_isCoordTest_partial hφ (cdir 1))
      have i1 := hint_Z 1 (planarTest_isCoordTest_partial hφ (cdir 2))
      change Integrable (fun x => Z x 0 * (cpd 1 φ x : ℂ)) volume at i0
      change Integrable (fun x => Z x 1 * (cpd 2 φ x : ℂ)) volume at i1
      have i01 : Integrable (fun x => Z x 0 * (cpd 1 φ x : ℂ) + Z x 1 * (cpd 2 φ x : ℂ)) volume :=
        i0.add i1
      refine ⟨i01, ?_⟩
      have hsol_n : ∀ n : ℕ,
          (∫ x, (Z x 0 * (cpd 1 φ x : ℂ) + Z x 1 * (cpd 2 φ x : ℂ))) =
            ∫ x, (theta T (εn n) x.1 : ℂ) *
              (Z x 0 * (cpd 1 φ x : ℂ) + Z x 1 * (cpd 2 φ x : ℂ)) := by
        intro n
        let φL : Coord → ℝ := fun x => etaL T (εn n) x.1 * φ x
        let φM : Coord → ℝ := fun x => theta T (εn n) x.1 * φ x
        let φR : Coord → ℝ := fun x => etaR T (εn n) x.1 * φ x
        have hφL : IsCoordTest φL := isCoordTest_time_mul (contDiff_etaL (hεn_pos n)) hφ
        have hφM : IsCoordTest φM := isCoordTest_time_mul (contDiff_theta (hεn_pos n)) hφ
        have hφR : IsCoordTest φR := isCoordTest_time_mul (contDiff_etaR (hεn_pos n)) hφ
        have hsuppL := tsupport_etaL_mul_subset (T := T) (hεn_pos n) hφ
        have hsuppR := tsupport_etaR_mul_subset (T := T) (hεn_pos n) φ
        have hL0 : ∫ x, (Z x 0 * (cpd 1 φL x : ℂ) + Z x 1 * (cpd 2 φL x : ℂ)) = 0 := by
          have heq : (fun x => Z x 0 * (cpd 1 φL x : ℂ) + Z x 1 * (cpd 2 φL x : ℂ)) =
              fun x => z₁ x 0 * (cpd 1 φL x : ℂ) + z₁ x 1 * (cpd 2 φL x : ℂ) := by
            funext x
            by_cases hle : x.1 ≤ T
            · simp [Z, glueAtHorizon, hle]
            · have hm : x.1 ∉ Ioo 0 T := fun h => hle h.2.le
              dsimp only [φL]
              simp [(tsupport_cpd2_zero hsuppL 1 1 hm).1, (tsupport_cpd2_zero hsuppL 2 2 hm).1]
          rw [heq, (h_sol₁ φL hφL hsuppL).2]
        have hR0 : ∫ x, (Z x 0 * (cpd 1 φR x : ℂ) + Z x 1 * (cpd 2 φR x : ℂ)) = 0 := by
          have heq : (fun x => Z x 0 * (cpd 1 φR x : ℂ) + Z x 1 * (cpd 2 φR x : ℂ)) =
              fun x => z₂ x 0 * (cpd 1 φR x : ℂ) + z₂ x 1 * (cpd 2 φR x : ℂ) := by
            funext x
            by_cases hle : x.1 ≤ T
            · have hm : x.1 ∉ Ioi T := not_lt.2 hle
              dsimp only [φR]
              simp [(tsupport_cpd2_zero hsuppR 1 1 hm).1, (tsupport_cpd2_zero hsuppR 2 2 hm).1]
            · simp [Z, glueAtHorizon, hle]
          rw [heq, (h₂.solenoidal φR hφR hsuppR).2]
        have sL : Integrable (fun x => Z x 0 * (cpd 1 φL x : ℂ) + Z x 1 * (cpd 2 φL x : ℂ)) :=
          (hint_Z 0 (planarTest_isCoordTest_partial hφL (cdir 1))).add
            (hint_Z 1 (planarTest_isCoordTest_partial hφL (cdir 2)))
        have sM : Integrable (fun x => Z x 0 * (cpd 1 φM x : ℂ) + Z x 1 * (cpd 2 φM x : ℂ)) :=
          (hint_Z 0 (planarTest_isCoordTest_partial hφM (cdir 1))).add
            (hint_Z 1 (planarTest_isCoordTest_partial hφM (cdir 2)))
        have sR : Integrable (fun x => Z x 0 * (cpd 1 φR x : ℂ) + Z x 1 * (cpd 2 φR x : ℂ)) :=
          (hint_Z 0 (planarTest_isCoordTest_partial hφR (cdir 1))).add
            (hint_Z 1 (planarTest_isCoordTest_partial hφR (cdir 2)))
        have sLM : Integrable (fun x =>
            (Z x 0 * (cpd 1 φL x : ℂ) + Z x 1 * (cpd 2 φL x : ℂ)) +
              (Z x 0 * (cpd 1 φM x : ℂ) + Z x 1 * (cpd 2 φM x : ℂ))) := sL.add sM
        have hfun : (fun x => Z x 0 * (cpd 1 φ x : ℂ) + Z x 1 * (cpd 2 φ x : ℂ)) =
            fun x => ((Z x 0 * (cpd 1 φL x : ℂ) + Z x 1 * (cpd 2 φL x : ℂ)) +
              (Z x 0 * (cpd 1 φM x : ℂ) + Z x 1 * (cpd 2 φM x : ℂ))) +
              (Z x 0 * (cpd 1 φR x : ℂ) + Z x 1 * (cpd 2 φR x : ℂ)) := by
          funext x
          have hc1L := cpd_time_mul_succ (contDiff_etaL (T := T) (hεn_pos n)) hφ.smooth 0 x
          have hc1M := cpd_time_mul_succ (contDiff_theta (T := T) (hεn_pos n)) hφ.smooth 0 x
          have hc1R := cpd_time_mul_succ (contDiff_etaR (T := T) (hεn_pos n)) hφ.smooth 0 x
          have hc2L := cpd_time_mul_succ (contDiff_etaL (T := T) (hεn_pos n)) hφ.smooth 1 x
          have hc2M := cpd_time_mul_succ (contDiff_theta (T := T) (hεn_pos n)) hφ.smooth 1 x
          have hc2R := cpd_time_mul_succ (contDiff_etaR (T := T) (hεn_pos n)) hφ.smooth 1 x
          dsimp only [φL, φM, φR]
          rw [show (1 : Fin 3) = Fin.succ 0 from rfl, show (2 : Fin 3) = Fin.succ 1 from rfl,
            hc1L, hc1M, hc1R, hc2L, hc2M, hc2R]
          have h1 := etaL_add_theta_add_etaR T (εn n) x.1
          have h1c : (etaL T (εn n) x.1 : ℂ) + (theta T (εn n) x.1 : ℂ) +
              (etaR T (εn n) x.1 : ℂ) = 1 := by exact_mod_cast h1
          push_cast
          calc Z x 0 * (cpd 1 φ x : ℂ) + Z x 1 * (cpd 2 φ x : ℂ)
              = ((etaL T (εn n) x.1 : ℂ) + (theta T (εn n) x.1 : ℂ) +
                  (etaR T (εn n) x.1 : ℂ)) *
                  (Z x 0 * (cpd 1 φ x : ℂ) + Z x 1 * (cpd 2 φ x : ℂ)) := by
                rw [h1c, one_mul]
            _ = _ := by ring
        rw [hfun, integral_add sLM sR, integral_add sL sM, hL0, hR0, zero_add, add_zero]
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        have hc1M := cpd_time_mul_succ (contDiff_theta (T := T) (hεn_pos n)) hφ.smooth 0 x
        have hc2M := cpd_time_mul_succ (contDiff_theta (T := T) (hεn_pos n)) hφ.smooth 1 x
        dsimp only [φM]
        rw [show (1 : Fin 3) = Fin.succ 0 from rfl, show (2 : Fin 3) = Fin.succ 1 from rfl,
          hc1M, hc2M]
        push_cast; ring
      have ht := (tendsto_integral_theta_mul_zero T hεn_pos hεn_tend i01).congr
        fun n => (hsol_n n).symm
      exact tendsto_nhds_unique tendsto_const_nhds ht
    equation := fun Ψ hΨ => by
      have hint_tr_any : ∀ {Φ : Coord → Fin 2 → ℝ}, IsPlanarSolTest Φ →
          Integrable (fun x => ∑ i : Fin 2, Z x i * meridTranspose p.ν Φ x i) volume := by
        intro Φ hΦ
        refine integrable_finsetSum _ fun i _ => ?_
        have id0 : Integrable (fun x => Z x i * (cpd 0 (fun y => Φ y i) x : ℂ)) :=
          hint_Z i (planarTest_isCoordTest_partial (hΦ.smooth i) (cdir 0))
        have id11 : Integrable
            (fun x => Z x i * (cpd 1 (fun y => cpd 1 (fun z => Φ z i) y) x : ℂ)) :=
          hint_Z i (planarTest_isCoordTest_partial
            (planarTest_isCoordTest_partial (hΦ.smooth i) (cdir 1)) (cdir 1))
        have id22 : Integrable
            (fun x => Z x i * (cpd 2 (fun y => cpd 2 (fun z => Φ z i) y) x : ℂ)) :=
          hint_Z i (planarTest_isCoordTest_partial
            (planarTest_isCoordTest_partial (hΦ.smooth i) (cdir 2)) (cdir 2))
        have hcomb := (id0.neg).sub (((id11.add id22)).const_mul (p.ν : ℂ))
        refine hcomb.congr (ae_of_all _ fun x => ?_)
        dsimp [meridTranspose]
        push_cast; ring
      have hint_Bv_any : ∀ {Φ : Coord → Fin 2 → ℝ}, IsPlanarSolTest Φ →
          Integrable (cdot (flatBv p.train Z Zq Zη) Φ) volume :=
        fun hΦ => integrable_finsetSum _ fun i _ => hint_Bv i (hΦ.smooth i)
      have hint_g_any : ∀ {Φ : Coord → Fin 2 → ℝ}, IsPlanarSolTest Φ →
          Integrable (cdot g Φ) volume :=
        fun hΦ => integrable_finsetSum _ fun i _ => hint_g i (hΦ.smooth i)
      have hIz := hint_tr_any hΨ
      have hIb := hint_Bv_any hΨ
      have hIg := hint_g_any hΨ
      have hIzb : Integrable (fun x => ∑ i : Fin 2, Z x i * meridTranspose p.ν Ψ x i +
          cdot (flatBv p.train Z Zq Zη) Ψ x) volume := hIz.add hIb
      refine ⟨hIz, hIb, hIg, ?_⟩
      -- Decompose `Ψ = ΨL + ΨM + ΨR` at scale `εn n`
      set F_rem : Coord → ℂ := fun x =>
        (∑ i : Fin 2, Z x i * meridTranspose p.ν Ψ x i +
          cdot (flatBv p.train Z Zq Zη) Ψ x) - cdot g Ψ x
      have hIF_rem : Integrable F_rem volume := hIzb.sub hIg
      have heq_n : ∀ n : ℕ,
          (∫ x, (∑ i : Fin 2, Z x i * meridTranspose p.ν Ψ x i +
              cdot (flatBv p.train Z Zq Zη) Ψ x)) - (∫ x, cdot g Ψ x) =
            (∫ x, (theta T (εn n) x.1 : ℂ) * F_rem x) -
              (∫ x, ∑ i : Fin 2,
                Z x i * ((deriv (theta T (εn n)) x.1 * Ψ x i : ℝ) : ℂ)) := by
        intro n
        let ΨL : Coord → Fin 2 → ℝ := fun x i => etaL T (εn n) x.1 * Ψ x i
        let ΨM : Coord → Fin 2 → ℝ := fun x i => theta T (εn n) x.1 * Ψ x i
        let ΨR : Coord → Fin 2 → ℝ := fun x i => etaR T (εn n) x.1 * Ψ x i
        have hΨL : IsPlanarSolTest ΨL :=
          isPlanarSolTest_time_mul (contDiff_etaL (hεn_pos n)) hΨ
        have hΨM : IsPlanarSolTest ΨM :=
          isPlanarSolTest_time_mul (contDiff_theta (hεn_pos n)) hΨ
        have hΨR : IsPlanarSolTest ΨR :=
          isPlanarSolTest_time_mul (contDiff_etaR (hεn_pos n)) hΨ
        have hsuppL : ∀ i, tsupport (fun x => ΨL x i) ⊆ Ioo 0 T ×ˢ univ :=
          fun i => tsupport_etaL_mul_subset (T := T) (hεn_pos n) (hΨ.smooth i)
        have hsuppR : ∀ i, tsupport (fun x => ΨR x i) ⊆ Ioi T ×ˢ univ :=
          fun i => tsupport_etaR_mul_subset (T := T) (hεn_pos n) (fun x => Ψ x i)
        have hL_eq : ∫ x, (∑ i : Fin 2, Z x i * meridTranspose p.ν ΨL x i +
            cdot (flatBv p.train Z Zq Zη) ΨL x) = ∫ x, cdot g ΨL x := by
          have heq_lhs : (fun x => ∑ i : Fin 2, Z x i * meridTranspose p.ν ΨL x i +
              cdot (flatBv p.train Z Zq Zη) ΨL x) =
              fun x => ∑ i : Fin 2, z₁ x i * meridTranspose p.ν ΨL x i +
                cdot (flatBv p.train z₁ zq₁ zη₁) ΨL x := by
            funext x
            by_cases hle : x.1 ≤ T
            · simp [Z, Zq, Zη, cdot, flatBv, glueAtHorizon, hle]
            · have hm : x.1 ∉ Ioo 0 T := fun h => hle h.2.le
              have hm0 : ∀ i : Fin 2, meridTranspose p.ν ΨL x i = 0 := fun i => by
                simp [meridTranspose, (tsupport_cpd2_zero (hsuppL i) 0 0 hm).1,
                  (tsupport_cpd2_zero (hsuppL i) 1 1 hm).2,
                  (tsupport_cpd2_zero (hsuppL i) 2 2 hm).2]
              have h0 : ∀ i : Fin 2, ΨL x i = 0 := fun i =>
                image_eq_zero_of_notMem_tsupport (f := fun y => ΨL y i)
                  (fun h => hm (hsuppL i h).1)
              simp [cdot, hm0, h0]
          rw [heq_lhs, (h_eq₁ ΨL hΨL hsuppL).2.2.2]
        have hR_eq : ∫ x, (∑ i : Fin 2, Z x i * meridTranspose p.ν ΨR x i +
            cdot (flatBv p.train Z Zq Zη) ΨR x) = ∫ x, cdot g ΨR x := by
          have heq_lhs : (fun x => ∑ i : Fin 2, Z x i * meridTranspose p.ν ΨR x i +
              cdot (flatBv p.train Z Zq Zη) ΨR x) =
              fun x => ∑ i : Fin 2, z₂ x i * meridTranspose p.ν ΨR x i +
                cdot (flatBv p.train z₂ zq₂ zη₂) ΨR x := by
            funext x
            by_cases hle : x.1 ≤ T
            · have hm : x.1 ∉ Ioi T := not_lt.2 hle
              have hm0 : ∀ i : Fin 2, meridTranspose p.ν ΨR x i = 0 := fun i => by
                simp [meridTranspose, (tsupport_cpd2_zero (hsuppR i) 0 0 hm).1,
                  (tsupport_cpd2_zero (hsuppR i) 1 1 hm).2,
                  (tsupport_cpd2_zero (hsuppR i) 2 2 hm).2]
              have h0 : ∀ i : Fin 2, ΨR x i = 0 := fun i =>
                image_eq_zero_of_notMem_tsupport (f := fun y => ΨR y i)
                  (fun h => hm (hsuppR i h).1)
              simp [cdot, hm0, h0]
            · simp [Z, Zq, Zη, cdot, flatBv, glueAtHorizon, hle]
          rw [heq_lhs, (h₂.equation ΨR hΨR hsuppR).2.2.2]
        -- Pointwise partition identity `LHS(Ψ) - RHS(Ψ) = (LHS - RHS)(ΨL) + (LHS - RHS)(ΨM) + (LHS - RHS)(ΨR)`
        let lhsF (Φ : Coord → Fin 2 → ℝ) (x : Coord) : ℂ :=
          ∑ i : Fin 2, Z x i * meridTranspose p.ν Φ x i + cdot (flatBv p.train Z Zq Zη) Φ x
        let remF (Φ : Coord → Fin 2 → ℝ) (x : Coord) : ℂ := lhsF Φ x - cdot g Φ x
        have iL_lhs : Integrable (lhsF ΨL) volume := (hint_tr_any hΨL).add (hint_Bv_any hΨL)
        have iM_lhs : Integrable (lhsF ΨM) volume := (hint_tr_any hΨM).add (hint_Bv_any hΨM)
        have iR_lhs : Integrable (lhsF ΨR) volume := (hint_tr_any hΨR).add (hint_Bv_any hΨR)
        have iL_rhs : Integrable (cdot g ΨL) volume := hint_g_any hΨL
        have iM_rhs : Integrable (cdot g ΨM) volume := hint_g_any hΨM
        have iR_rhs : Integrable (cdot g ΨR) volume := hint_g_any hΨR
        have iL : Integrable (remF ΨL) volume := iL_lhs.sub iL_rhs
        have iM : Integrable (remF ΨM) volume := iM_lhs.sub iM_rhs
        have iR : Integrable (remF ΨR) volume := iR_lhs.sub iR_rhs
        have iLM : Integrable (fun x => remF ΨL x + remF ΨM x) volume := iL.add iM
        have hpt_split : (fun x : Coord =>
            (∑ i : Fin 2, Z x i * meridTranspose p.ν Ψ x i +
              cdot (flatBv p.train Z Zq Zη) Ψ x) - cdot g Ψ x) =
            fun x : Coord => (remF ΨL x + remF ΨM x) + remF ΨR x := by
          funext x
          dsimp only [remF, lhsF, ΨL, ΨM, ΨR]
          have h1 := etaL_add_theta_add_etaR T (εn n) x.1
          have hd_sum : deriv (etaL T (εn n)) x.1 + deriv (theta T (εn n)) x.1 +
              deriv (etaR T (εn n)) x.1 = 0 := by
            have hdL := ((contDiff_etaL (T := T) (hεn_pos n)).differentiable (by simp) x.1).hasDerivAt
            have hdM := ((contDiff_theta (T := T) (hεn_pos n)).differentiable (by simp) x.1).hasDerivAt
            have hdR := ((contDiff_etaR (T := T) (hεn_pos n)).differentiable (by simp) x.1).hasDerivAt
            have hsum_d : HasDerivAt (fun _ : ℝ => (1 : ℝ))
                (deriv (etaL T (εn n)) x.1 + deriv (theta T (εn n)) x.1 +
                  deriv (etaR T (εn n)) x.1) x.1 :=
              ((hdL.add hdM).add hdR).congr_of_eventuallyEq
                (Eventually.of_forall fun s => (etaL_add_theta_add_etaR T (εn n) s).symm)
            exact hsum_d.unique (hasDerivAt_const x.1 (1 : ℝ))
          have h1c : (etaL T (εn n) x.1 : ℂ) + (theta T (εn n) x.1 : ℂ) +
              (etaR T (εn n) x.1 : ℂ) = 1 := by exact_mod_cast h1
          have hdc : ((deriv (etaL T (εn n)) x.1 : ℝ) : ℂ) +
              ((deriv (theta T (εn n)) x.1 : ℝ) : ℂ) +
              ((deriv (etaR T (εn n)) x.1 : ℝ) : ℂ) = 0 := by exact_mod_cast hd_sum
          simp only [Fin.sum_univ_two, cdot,
            meridTranspose_time_mul p.ν (contDiff_etaL (T := T) (hεn_pos n)) hΨ x,
            meridTranspose_time_mul p.ν (contDiff_theta (T := T) (hεn_pos n)) hΨ x,
            meridTranspose_time_mul p.ν (contDiff_etaR (T := T) (hεn_pos n)) hΨ x]
          push_cast
          calc ((Z x 0 * meridTranspose p.ν Ψ x 0 + Z x 1 * meridTranspose p.ν Ψ x 1 +
                  (flatBv p.train Z Zq Zη x 0 * (Ψ x 0 : ℂ) +
                    flatBv p.train Z Zq Zη x 1 * (Ψ x 1 : ℂ))) -
                (g x 0 * (Ψ x 0 : ℂ) + g x 1 * (Ψ x 1 : ℂ)))
              = ((etaL T (εn n) x.1 : ℂ) + (theta T (εn n) x.1 : ℂ) +
                  (etaR T (εn n) x.1 : ℂ)) *
                  ((Z x 0 * meridTranspose p.ν Ψ x 0 + Z x 1 * meridTranspose p.ν Ψ x 1 +
                    (flatBv p.train Z Zq Zη x 0 * (Ψ x 0 : ℂ) +
                      flatBv p.train Z Zq Zη x 1 * (Ψ x 1 : ℂ))) -
                  (g x 0 * (Ψ x 0 : ℂ) + g x 1 * (Ψ x 1 : ℂ))) -
                (((deriv (etaL T (εn n)) x.1 : ℝ) : ℂ) +
                  ((deriv (theta T (εn n)) x.1 : ℝ) : ℂ) +
                  ((deriv (etaR T (εn n)) x.1 : ℝ) : ℂ)) *
                  (Z x 0 * (Ψ x 0 : ℂ) + Z x 1 * (Ψ x 1 : ℂ)) := by
                rw [h1c, hdc, one_mul, zero_mul, sub_zero]
            _ = _ := by ring
        have hremL0 : ∫ x, remF ΨL x = 0 := by
          rw [show remF ΨL = fun x => lhsF ΨL x - cdot g ΨL x from rfl,
            integral_sub iL_lhs iL_rhs, show lhsF ΨL = _ from rfl, hL_eq, sub_self]
        have hremR0 : ∫ x, remF ΨR x = 0 := by
          rw [show remF ΨR = fun x => lhsF ΨR x - cdot g ΨR x from rfl,
            integral_sub iR_lhs iR_rhs, show lhsF ΨR = _ from rfl, hR_eq, sub_self]
        rw [← integral_sub hIzb hIg, hpt_split, integral_add iLM iR, integral_add iL iM,
          hremL0, hremR0, zero_add, add_zero]
        -- Expand the middle `ΨM` integral into `theta * F_rem - seam`
        have iM_rem : Integrable (fun x => (theta T (εn n) x.1 : ℂ) * F_rem x) volume := by
          have hmeas : AEStronglyMeasurable
              (fun x : Coord => (theta T (εn n) x.1 : ℂ) * F_rem x) volume :=
            ((Complex.continuous_ofReal.comp
              ((contDiff_theta (hεn_pos n)).continuous.comp continuous_fst)).aestronglyMeasurable).mul
              hIF_rem.aestronglyMeasurable
          refine hIF_rem.mono hmeas (ae_of_all _ fun x => ?_)
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_of_le_one_left (norm_nonneg _) (abs_theta_le_one T (εn n) x.1)
        have iM_seam : Integrable (fun x => ∑ i : Fin 2,
            Z x i * ((deriv (theta T (εn n)) x.1 * Ψ x i : ℝ) : ℂ)) volume := by
          refine integrable_finsetSum _ fun i _ => ?_
          have htest_d : IsCoordTest (fun x => deriv (theta T (εn n)) x.1 * Ψ x i) :=
            isCoordTest_time_mul (contDiff_infty_iff_deriv.mp (contDiff_theta (hεn_pos n))).2
              (hΨ.smooth i)
          exact hint_Z i htest_d
        have hM_pt : remF ΨM =
            fun x => (theta T (εn n) x.1 : ℂ) * F_rem x -
              ∑ i : Fin 2, Z x i * ((deriv (theta T (εn n)) x.1 * Ψ x i : ℝ) : ℂ) := by
          funext x
          dsimp only [remF, lhsF, F_rem, ΨM]
          simp only [Fin.sum_univ_two, cdot,
            meridTranspose_time_mul p.ν (contDiff_theta (T := T) (hεn_pos n)) hΨ x]
          push_cast; ring
        rw [hM_pt, integral_sub iM_rem iM_seam]
      have ht_rem := tendsto_integral_theta_mul_zero T hεn_pos hεn_tend hIF_rem
      have ht_seam := tendsto_seam_integral_zero hc hT hM hz₁_sm hzq₁_sm hzη₁_sm
        hz₂_sm hzq₂_sm hzη₂_sm hZ_per hbdd₁ hcont₁ hmatch hcont₂
        hεn_pos hεn_le hεn_tend hΨ
      have ht_zero : Tendsto (fun _ : ℕ =>
          (∫ x, (∑ i : Fin 2, Z x i * meridTranspose p.ν Ψ x i +
              cdot (flatBv p.train Z Zq Zη) Ψ x)) - (∫ x, cdot g Ψ x)) atTop (𝓝 0) := by
        have h0 : Tendsto (fun n =>
            (∫ x, (theta T (εn n) x.1 : ℂ) * F_rem x) -
              (∫ x, ∑ i : Fin 2,
                Z x i * ((deriv (theta T (εn n)) x.1 * Ψ x i : ℝ) : ℂ)))
            atTop (𝓝 (0 - 0)) := ht_rem.sub ht_seam
        rw [sub_self] at h0
        exact h0.congr fun n => (heq_n n).symm
      exact sub_eq_zero.1 (tendsto_nhds_unique tendsto_const_nhds ht_zero)
    initial_curl := initial_curl_glue hT hzq₁_sm hzη₁_sm hzq₂_sm hzη₂_sm hcont₁
      (hae_eb.mono fun x hx hm => (hx hm).2.1)
      (hae_eb.mono fun x hx hm => (hx hm).2.2)
      (entranceVorticityComb p α) heb.initial_curl
  }

end UnforcedLeray.Short.IIb.HorizonGluingAux

namespace UnforcedLeray.Short.IIb

/-- Proof of `MeridionalHorizonGluing` (`PartII-b:F7/2/2`, SP 2213–2217, 2289–2295). -/
theorem meridionalHorizonGluing_proof : UnforcedLeray.Short.IIb.MeridionalHorizonGluing := by
  intro p d dm dp T M α hbg hT hM g gq gη z_eb zq_eb zη_eb hg hg_early heb hbdd
  obtain ⟨z₁, zq₁, zη₁, hz₁_sm, hzq₁_sm, hzη₁_sm, hper_all, hz₁_per, hzq₁_per, hzη₁_per,
    hae_eb, hcont₁, hslice_T, hbdd₁, h_wq₁, h_wη₁, h_sol₁, h_eq₁⟩ :=
    HorizonGluingAux.exists_early_horizon_rep hbg hT hM hg hg_early heb hbdd
  refine ⟨z₁, zq₁, zη₁, hz₁_sm, hzq₁_sm, hzη₁_sm, hz₁_per, hzq₁_per, hzη₁_per,
    hae_eb, hcont₁, hslice_T, ?_⟩
  intro z₂ zq₂ zη₂ hz₂_sm hzq₂_sm hzη₂_sm hg_tail hmatch h₂ hcont₂
  exact HorizonGluingAux.isGlobalMeridionalCorrection_glue hbg hT hM hg hg_early hg_tail heb
    hz₁_sm hzq₁_sm hzη₁_sm hper_all hae_eb hcont₁ hbdd₁ h_wq₁ h_wη₁ h_sol₁ h_eq₁
    hz₂_sm hzq₂_sm hzη₂_sm hmatch h₂ hcont₂

end UnforcedLeray.Short.IIb

end
