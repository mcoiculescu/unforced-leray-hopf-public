import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity.BodyFlatLocalH1.FlatBodyAgeDerivLocal.FlatBodyCutLaplacianLocal.CylHeat

/-!
# Helpers for `PartII-a:N05/2/2/1`: from the cylinder estimate back to the cell

Source: `the November 2 reference manuscript`, lines 1794-1799 ("periodic extension
over many cells followed by division by their number gives constants independent of the number
of cells").

* `cylHeat_hyps`: `u_i`, `f_i` are `q`-periodic, measurable and square integrable for
  `cylMeasL c` (the hypotheses of the cylinder heat estimate).
* `eLpNorm_cyl_sq_eq`, `eLpNorm_cell_sq_le`: the cell norm and the cylinder norm agree up to the
  factor `c` (exactly for periodic fields vanishing at `s ≤ 0`, as an inequality for a.e.
  periodic ones).
* `cell_rel`: if `D` is the weak `∂_j²` of `u_i` on `ℝ × ℝ²`, then on the cell
  `∫ a D = ∫ (∂_j² a) w_i` for every smooth periodic test `a` supported in `[σ, H1]`, where
  `u_i = w_i` (test `qCut · a`, periodization `perT (qCut · a) = a`, and `integral_qCut_mul`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa.FBCLL

open UnforcedLeray.B0220 (HSpace measureH Profile cellMeasure cell periodize QPeriodic
  periodize_of_mem)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.PartIIa (IsMeridTest pdS pdQ pdEta)
open UnforcedLeray.Short.IIb (Coord cpd cdir qShift)

theorem qShift_eq_add (c : ℝ) (x : Coord) : qShift c x = x + qv c := (add_qv_eq x c).symm

theorem measurable_periodize' (c : ℝ) {f : Profile → MeridC} (hf : Measurable f) :
    Measurable (periodize c f) := by
  unfold periodize
  exact hf.comp (measurable_fst.prodMk
    (((UnforcedLeray.B0220.measurable_reduceIoc c).comp (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd)))

theorem measurable_comp_apply {f : Coord → MeridC} (hf : Measurable f) (i : Fin 2) :
    Measurable fun x => f x i :=
  (EuclideanSpace.proj i : MeridC →L[ℂ] ℂ).continuous.measurable.comp hf

theorem measurable_uCut (c σ H1 : ℝ) {W : Profile → MeridC} (hW : Measurable W) (i : Fin 2) :
    Measurable (uCut c σ H1 W i) :=
  (Complex.measurable_ofReal.comp ((measurable_timeCut σ H1).comp measurable_fst)).mul
    (measurable_comp_apply (measurable_periodize' c hW) i)

theorem measurable_fCut (c σ H1 : ℝ) (μ : ℂ) {W G : Profile → MeridC} (hW : Measurable W)
    (hG : Measurable G) (i : Fin 2) : Measurable (fCut c σ H1 μ W G i) := by
  have h1 : Measurable fun x : Coord => ((timeCut σ H1 x.1 * x.1⁻¹ : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp
      (((measurable_timeCut σ H1).comp measurable_fst).mul (measurable_fst.inv))
  have h2 : Measurable fun x : Coord => ((deriv (timeCut σ H1) x.1 : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp ((continuous_deriv_timeCut σ H1).measurable.comp measurable_fst)
  exact (h1.mul ((measurable_comp_apply (measurable_periodize' c hG) i).sub
    (measurable_const.mul (measurable_comp_apply (measurable_periodize' c hW) i)))).add
      (h2.mul (measurable_comp_apply (measurable_periodize' c hW) i))

/-! ### Cell norm against cylinder norm -/

/-- For a periodic `F` vanishing at `s ≤ 0`: `‖F‖²_{cyl} = c⁻¹ ‖F‖²_{cell}`. -/
theorem eLpNorm_cyl_sq_eq {c : ℝ} (hc : 0 < c) {F : Coord → ℂ}
    (hper : ∀ x, F (x + qv c) = F x) (hpos : ∀ x : Coord, x.1 ≤ 0 → F x = 0) :
    eLpNorm F 2 (cylMeasL c) ^ (2 : ℝ) =
      ENNReal.ofReal c⁻¹ * eLpNorm F 2 (cellMeasure c) ^ (2 : ℝ) := by
  rw [eLpNorm_two_rpow_two, eLpNorm_two_rpow_two]
  exact lintegral_cylMeas_eq_cell hc (Eventually.of_forall fun x => by simp only [hper x])
    (fun x hx => by simp [hpos x hx])

/-- For an a.e. periodic `D`: `‖D‖²_{cell} ≤ c ‖D‖²_{cyl}`. -/
theorem eLpNorm_cell_sq_le {c : ℝ} (hc : 0 < c) {D : Coord → ℂ} (hper : QPeriodicSL c D) :
    eLpNorm D 2 (cellMeasure c) ^ (2 : ℝ) ≤
      ENNReal.ofReal c * eLpNorm D 2 (cylMeasL c) ^ (2 : ℝ) := by
  rw [eLpNorm_two_rpow_two, eLpNorm_two_rpow_two]
  refine lintegral_cell_le_cylMeas hc ?_
  filter_upwards [hper] with x hx
  rw [← qShift_eq_add, hx]

theorem eLpNorm_lt_top_of_sq {α : Type*} [MeasurableSpace α] {μ : Measure α} {E : Type*}
    [NormedAddCommGroup E] {f : α → E} (h : eLpNorm f 2 μ ^ (2 : ℝ) < ⊤) : eLpNorm f 2 μ < ⊤ := by
  by_contra hne
  rw [not_lt, top_le_iff] at hne
  rw [hne, ENNReal.top_rpow_of_pos (by norm_num)] at h
  exact lt_irrefl _ h

/-- The hypotheses of the cylinder heat estimate for `u_i`, `f_i`. -/
theorem cylHeat_hyps {c σ H1 : ℝ} (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1) (μ : ℂ)
    (V G : HSpace c MeridC) (i : Fin 2) :
    QPeriodicSL c (uCut c σ H1 (V : Profile → MeridC) i) ∧
      QPeriodicSL c (fCut c σ H1 μ (V : Profile → MeridC) (G : Profile → MeridC) i) ∧
      AEStronglyMeasurable (uCut c σ H1 (V : Profile → MeridC) i) volume ∧
      AEStronglyMeasurable (fCut c σ H1 μ (V : Profile → MeridC) (G : Profile → MeridC) i)
        volume ∧
      eLpNorm (uCut c σ H1 (V : Profile → MeridC) i) (ENNReal.ofReal 2) (cylMeasL c) < ⊤ ∧
      eLpNorm (fCut c σ H1 μ (V : Profile → MeridC) (G : Profile → MeridC) i)
        (ENNReal.ofReal 2) (cylMeasL c) < ⊤ := by
  have hH : 0 < H1 := lt_of_lt_of_le hσ hσH
  have hV : Measurable (V : Profile → MeridC) := (Lp.stronglyMeasurable V).measurable
  have hG : Measurable (G : Profile → MeridC) := (Lp.stronglyMeasurable G).measurable
  have h2 : ENNReal.ofReal 2 = 2 := by norm_num
  rw [h2]
  refine ⟨Eventually.of_forall fun x => by rw [qShift_eq_add, uCut_periodic hc],
    Eventually.of_forall fun x => by rw [qShift_eq_add, fCut_periodic hc],
    (measurable_uCut c σ H1 hV i).aestronglyMeasurable,
    (measurable_fCut c σ H1 μ hV hG i).aestronglyMeasurable, ?_, ?_⟩
  · refine eLpNorm_lt_top_of_sq ?_
    rw [eLpNorm_cyl_sq_eq hc (uCut_periodic hc _ i) fun x hx =>
      uCut_zero (c := c) (x := x) hσ hH _ i fun h => by linarith [h.1]]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (memLp_uCut hc hσ hH V i).2.ne)
  · refine eLpNorm_lt_top_of_sq ?_
    rw [eLpNorm_cyl_sq_eq hc (fCut_periodic hc μ _ _ i) fun x hx =>
      fCut_zero (c := c) (x := x) hσ hH μ _ _ i fun h => by linarith [h.1]]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (memLp_fCut hc hσ hσH hH μ V G i).2.ne)

/-! ### The weak second derivatives on the cell -/

/-- The weak `∂_j²` of `u_i` on `ℝ × ℝ²` is, on the cell, the weak `∂_j²` of `w_i` against
periodic tests supported in `[σ, H1]`; the pairing is integrable. -/
theorem cell_rel {c σ H1 : ℝ} (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1) (V : HSpace c MeridC)
    (i j : Fin 2) {D : Coord → ℂ} (hDper : QPeriodicSL c D) (hDm : AEStronglyMeasurable D volume)
    (hDfin : eLpNorm D 2 (cylMeasL c) < ⊤)
    (hweak : ∀ φ : Coord → ℝ, IsSTTestCoordL φ →
      ∫ x, uCut c σ H1 (V : Profile → MeridC) i x * (cpd j.succ (fun y => cpd j.succ φ y) x : ℂ) =
        ∫ x, D x * (φ x : ℂ))
    {a : Profile → ℝ} (has : ContDiff ℝ ∞ a) (hper : QPeriodic c a) {L : ℝ}
    (hband : ∀ p, a p ≠ 0 → p.1 ∈ Icc σ H1 ∧ |p.2.2| ≤ L) :
    Integrable (fun x => (a x : ℂ) * D x) (cellMeasure c) ∧
      ∫ x, (a x : ℂ) * D x ∂(cellMeasure c) =
        ∫ x, ((cpd j.succ (fun y => cpd j.succ a y) x : ℝ) : ℂ) * V x i ∂(cellMeasure c) := by
  have hH : 0 < H1 := lt_of_lt_of_le hσ hσH
  have haper : ∀ x : Coord, a (x + qv c) = a x := fun x => by rw [add_qv_eq]; exact hper x
  -- the compactly supported test `φ = qCut · a`
  set φ : Coord → ℝ := fun x => qCut c x.2.1 * a x with hφdef
  have hφs : ContDiff ℝ ∞ φ :=
    ((qCut_contDiff c).comp (contDiff_fst.comp contDiff_snd)).mul has
  set K : Set Coord := Icc σ H1 ×ˢ (Icc (-c) c ×ˢ Icc (-L) L) with hKdef
  have hKc : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hφk : HasCompactSupport φ := by
    refine HasCompactSupport.intro hKc fun x hx => ?_
    by_cases hq : x.2.1 ∈ Ioc (-c) c
    · have ha : a x = 0 := by
        by_contra h
        obtain ⟨h1, h2⟩ := hband x h
        exact hx ⟨h1, Ioc_subset_Icc_self hq, abs_le.1 h2⟩
      simp [hφdef, ha]
    · simp [hφdef, qCut_eq_zero_of_not_mem hc hq]
  have hφ : IsSTTestCoordL φ := ⟨hφs, hφk⟩
  have hw := hweak φ hφ
  -- the left side unfolds onto the cell
  have hpos_u : ∀ x : Coord, x.1 ≤ 0 → uCut c σ H1 (V : Profile → MeridC) i x = 0 := fun x hx =>
    uCut_zero (c := c) (x := x) hσ hH _ i fun h => by linarith [h.1]
  have hloc_u : LocallyIntegrable (uCut c σ H1 (V : Profile → MeridC) i) volume :=
    locInt_of_band hc (by linarith : (0 : ℝ) < σ / 2) (uCut_periodic hc _ i)
      (fun x hx => uCut_zero (c := c) hσ hH _ i hx) (memLp_uCut hc hσ hH V i)
  have hd1 : ContDiff ℝ ∞ (fun y => cpd j.succ φ y) := cpd_contDiff hφs j.succ
  have hd2 : ContDiff ℝ ∞ (fun x => cpd j.succ (fun y => cpd j.succ φ y) x) :=
    cpd_contDiff hd1 j.succ
  have hk2 : HasCompactSupport (fun x => cpd j.succ (fun y => cpd j.succ φ y) x) :=
    cpd_hasCompactSupport (cpd_hasCompactSupport hφk j.succ) j.succ
  rw [integral_mul_test_eq_cell hc (uCut_periodic hc _ i) hpos_u hloc_u hd2.continuous hk2] at hw
  have hperT : perT c (fun x => cpd j.succ (fun y => cpd j.succ φ y) x) =
      fun x => cpd j.succ (fun y => cpd j.succ a y) x := by
    rw [← cpd_perT hc hd1 (cpd_hasCompactSupport hφk j.succ) j.succ]
    have h1 : (fun y => cpd j.succ (perT c φ) y) = perT c (fun y => cpd j.succ φ y) :=
      cpd_perT hc hφs hφk j.succ
    rw [← h1, perT_qCut_mul hc haper]
  rw [hperT] at hw
  -- the band of `∂_j² a` lies in `[σ, H1]`, where `θ = 1`
  have hband2 : ∀ p, cpd j.succ (fun y => cpd j.succ a y) p ≠ 0 →
      p.1 ∈ Icc σ H1 ∧ |p.2.2| ≤ L :=
    band_fderiv (band_fderiv hband _) _
  have hL : ∫ x in cell c, uCut c σ H1 (V : Profile → MeridC) i x *
      ((cpd j.succ (fun y => cpd j.succ a y) x : ℝ) : ℂ) =
      ∫ x, ((cpd j.succ (fun y => cpd j.succ a y) x : ℝ) : ℂ) * V x i ∂(cellMeasure c) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_mem_cell c] with x hx
    simp only [uCut, periodize_of_mem hc _ hx]
    by_cases h0 : cpd j.succ (fun y => cpd j.succ a y) x = 0
    · simp [h0]
    · obtain ⟨⟨h1, h2⟩, -⟩ := hband2 x h0
      rw [timeCut_one hσ hH h1 h2]
      push_cast
      ring
  rw [hL] at hw
  -- the right side: `integral_qCut_mul`
  set K' : Set Coord := Icc σ H1 ×ˢ (Ioc (-c) c ×ˢ Icc (-L) L) with hK'def
  have hK'm : MeasurableSet K' :=
    measurableSet_Icc.prod (measurableSet_Ioc.prod measurableSet_Icc)
  have hK'fin : volume K' < ⊤ :=
    lt_of_le_of_lt (measure_mono (fun x hx => ⟨hx.1, Ioc_subset_Icc_self hx.2.1, hx.2.2⟩ :
      K' ⊆ K)) hKc.measure_lt_top
  haveI : IsFiniteMeasure (volume.restrict K') := isFiniteMeasure_restrict.2 hK'fin.ne
  have hK'sub : K' ⊆ Ioi 0 ×ˢ (Ioc (-c) c ×ˢ univ) := fun x hx =>
    ⟨lt_of_lt_of_le hσ hx.1.1, hx.2.1, trivial⟩
  -- `D` is square integrable on two cells
  have hDper' : ∀ᵐ x : Coord, ‖D (x + qv c)‖ₑ ^ (2 : ℝ) = ‖D x‖ₑ ^ (2 : ℝ) := by
    filter_upwards [hDper] with x hx
    rw [← qShift_eq_add, hx]
  have hD2 : ∫⁻ x in Ioi 0 ×ˢ (Ioc (-c) c ×ˢ univ), ‖D x‖ₑ ^ (2 : ℝ) < ⊤ := by
    rw [lintegral_two_cells (G := fun x => ‖D x‖ₑ ^ (2 : ℝ)) hc hDper' measurableSet_Ioi]
    have h1 := lintegral_cell_le_cylMeas (G := fun x => ‖D x‖ₑ ^ (2 : ℝ)) hc hDper'
    have h2 : ∫⁻ x, ‖D x‖ₑ ^ (2 : ℝ) ∂(cylMeasL c) < ⊤ := by
      rw [← eLpNorm_two_rpow_two]
      exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hDfin.ne
    refine ENNReal.mul_lt_top (by norm_num) (lt_of_le_of_lt h1 ?_)
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top h2
  have hDK : MemLp D 2 (volume.restrict K') := by
    refine memLp_two_of_lintegral hDm.restrict ?_
    exact lt_of_le_of_lt (lintegral_mono_set hK'sub) hD2
  have hDKi : IntegrableOn D K' := hDK.integrable (by norm_num)
  obtain ⟨A, hA⟩ := hKc.exists_bound_of_continuousOn has.continuous.continuousOn
  have haK : IntegrableOn (fun x => (a x : ℂ) * D x) K' := by
    refine hDKi.bdd_mul (c := A) (Complex.continuous_ofReal.comp has.continuous).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hK'm] with x hx
    rw [Complex.norm_real]
    exact hA x ⟨hx.1, Ioc_subset_Icc_self hx.2.1, hx.2.2⟩
  have hzero : ∀ x ∈ (Ioi 0 ×ˢ (Ioc (-c) c ×ˢ univ)) \ K', (a x : ℂ) * D x = 0 := by
    intro x hx
    have ha : a x = 0 := by
      by_contra h
      obtain ⟨h1, h2⟩ := hband x h
      exact hx.2 ⟨h1, hx.1.2.1, abs_le.1 h2⟩
    simp [ha]
  have haTwo : IntegrableOn (fun x => (a x : ℂ) * D x) (Ioi 0 ×ˢ (Ioc (-c) c ×ˢ univ)) :=
    haK.of_forall_diff_eq_zero (measurableSet_Ioi.prod (measurableSet_Ioc.prod MeasurableSet.univ))
      hzero
  have hR : ∫ x, D x * (φ x : ℂ) = ∫ x, (a x : ℂ) * D x ∂(cellMeasure c) := by
    have hperG : ∀ᵐ x : Coord, (a (x + qv c) : ℂ) * D (x + qv c) = (a x : ℂ) * D x := by
      filter_upwards [hDper] with x hx
      rw [← qShift_eq_add, hx, qShift_eq_add, haper]
    have hposG : ∀ x : Coord, x.1 ≤ 0 → (a x : ℂ) * D x = 0 := by
      intro x hx
      have ha : a x = 0 := by
        by_contra h
        obtain ⟨⟨h1, -⟩, -⟩ := hband x h
        linarith
      simp [ha]
    have := integral_qCut_mul hc hperG hposG haTwo
    rw [show ∫ x, (a x : ℂ) * D x ∂(cellMeasure c) = ∫ x in cell c, (a x : ℂ) * D x from rfl,
      ← this]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hφdef]
    push_cast
    ring
  rw [hR] at hw
  refine ⟨haTwo.mono_set fun x hx => ⟨hx.1, ⟨by linarith [hx.2.1.1], hx.2.1.2⟩, trivial⟩, ?_⟩
  exact hw.symm

end UnforcedLeray.Short.PartIIa.FBCLL
