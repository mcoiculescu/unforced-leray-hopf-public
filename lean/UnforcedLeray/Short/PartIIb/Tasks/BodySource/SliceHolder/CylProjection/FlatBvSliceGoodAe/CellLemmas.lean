import UnforcedLeray.Short.PartIIb.Tasks.BodySource.SliceHolder.CylProjection.FlatBvSliceGoodAe.Needed
import UnforcedLeray.Short.PartIIIa.Clock.Existence.UnitHeatWeak.FluxDuhamel.CellInt

/-!
# Cell lemmas for `PartII-b:F5/2/2/2` (`FlatBvSliceGoodAe`)

Proves the sub-statements (S2) `IntegrableOnCellOfXm` (`X_m ⊂ L¹(cell)` for `m > 1`) and (S3)
`ZeroCirculationOfWeak` (zero cell integral of `∂_q u₁ - ∂_η u₀` for `u₀ ∈ L²(cell)`, by the
cylinder tests `χ(η / R)`, `R → ∞`) of `FlatBvSliceGoodAe/Needed.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb.FlatBvSliceGoodAeNeeded

open UnforcedLeray

/-! ## (S2) `X_m ⊂ L¹(cell)` -/

theorem integrableOn_cell_of_xm {c m : ℝ} (hm : 1 < m) {w : B0579.Plane → ℂ}
    (hw : AEStronglyMeasurable w (volume.restrict (B0579.cell c)))
    (hfin : eLpNorm w 2 (B0579.cellMeasure c m) < ⊤) : IntegrableOn w (B0579.cell c) := by
  have h1 : MemLp (fun x => B0579.jb x ^ (m / 2) * ‖w x‖) 2 (volume.restrict (B0579.cell c)) := by
    refine ⟨(B0579.continuous_jb_rpow (m / 2)).aestronglyMeasurable.mul hw.norm, ?_⟩
    rw [← B0579.eLpNorm_cellMeasure c m (fun x => ‖w x‖), eLpNorm_norm]
    exact hfin
  have h2 : MemLp (fun x => B0579.jb x ^ (-(m / 2))) 2 (volume.restrict (B0579.cell c)) := by
    have hmeas : AEStronglyMeasurable (fun x => B0579.jb x ^ (-(m / 2)))
        (volume.restrict (B0579.cell c)) :=
      (B0579.continuous_jb_rpow (-(m / 2))).aestronglyMeasurable
    refine (memLp_two_iff_integrable_sq hmeas).2 ?_
    refine (UnforcedLeray.Short.IIIa.Exist.integrableOn_jb_rpow_neg_cell (c := c) m hm.le).congr
      (Eventually.of_forall fun x => ?_)
    simp only
    rw [← Real.rpow_natCast, ← Real.rpow_mul (B0579.jb_pos x).le]
    norm_num
  have h3 : Integrable (fun x => B0579.jb x ^ (-(m / 2)) * (B0579.jb x ^ (m / 2) * ‖w x‖))
      (volume.restrict (B0579.cell c)) := h2.integrable_mul h1
  have h4 : Integrable (fun x => ‖w x‖) (volume.restrict (B0579.cell c)) := by
    refine h3.congr (Eventually.of_forall fun x => ?_)
    simp only
    have hj := B0579.jb_pos x
    rw [← mul_assoc, ← Real.rpow_add hj]
    simp
  exact (integrable_norm_iff hw).1 h4

theorem integrableOnCellOfXm_proof : IntegrableOnCellOfXm :=
  fun _c _m hm _w hw hfin => integrableOn_cell_of_xm hm hw hfin

/-! ## (S3) Zero cell circulation -/

/-- The cutoff `χ`: smooth, `1` on `[-1, 1]`, `0` for `|t| ≥ 2`, values in `[0, 1]`. -/
def cutBump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- `ψ_R(q, η) = χ(η / R)`. -/
def cutR (R : ℝ) (x : B0579.Plane) : ℝ := cutBump (x.2 / R)

theorem cutBump_zero_of_two_le {t : ℝ} (ht : 2 ≤ |t|) : cutBump t = 0 :=
  cutBump.zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact ht)

theorem cutBump_one_of_le_one {t : ℝ} (ht : |t| ≤ 1) : cutBump t = 1 :=
  cutBump.one_of_mem_closedBall (by rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]; exact ht)

theorem cutR_isCylTest (c : ℝ) {R : ℝ} (hR : 0 < R) : B0579.IsCylTest c (cutR R) where
  smooth := cutBump.contDiff.comp (contDiff_snd.div_const R)
  periodic _ := rfl
  band := ⟨2 * R, fun x hx => by
    refine cutBump_zero_of_two_le ?_
    rw [abs_div, abs_of_pos hR, le_div_iff₀ hR]
    exact hx.le⟩

theorem hasDerivAt_cut (R t : ℝ) :
    HasDerivAt (fun t : ℝ => cutBump (t / R)) (deriv cutBump (t / R) * (1 / R)) t := by
  have h1 : HasDerivAt (fun t : ℝ => t / R) (1 / R) t := (hasDerivAt_id' t).div_const R
  have h2 : HasDerivAt (cutBump : ℝ → ℝ) (deriv cutBump (t / R)) (t / R) :=
    ((cutBump.contDiff (n := 1)).differentiable one_ne_zero (t / R)).hasDerivAt
  exact HasDerivAt.comp (h₂ := (cutBump : ℝ → ℝ)) (h := fun t : ℝ => t / R) t h2 h1

theorem pd_cutR (R : ℝ) (j : Fin 2) (x : B0579.Plane) :
    B0579.pd j (cutR R) x = deriv cutBump (x.2 / R) * (1 / R) * (B0579.dir j).2 := by
  have hF : HasFDerivAt (cutR R)
      ((deriv cutBump (x.2 / R) * (1 / R)) • ContinuousLinearMap.snd ℝ ℝ ℝ) x :=
    (hasDerivAt_cut R x.2).comp_hasFDerivAt x (hasFDerivAt_snd (p := x))
  simp only [B0579.pd, hF.fderiv, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.coe_snd', smul_eq_mul]

theorem pd0_cutR (R : ℝ) (x : B0579.Plane) : B0579.pd 0 (cutR R) x = 0 := by
  rw [pd_cutR]; simp [B0579.dir]

theorem pd1_cutR (R : ℝ) (x : B0579.Plane) :
    B0579.pd 1 (cutR R) x = deriv cutBump (x.2 / R) * (1 / R) := by
  rw [pd_cutR]; simp [B0579.dir]

theorem deriv_cutBump_eq_zero {t : ℝ} (ht : 2 < |t|) : deriv cutBump t = 0 := by
  have hU : IsOpen {s : ℝ | 2 < |s|} := isOpen_lt continuous_const continuous_abs
  have hev : (cutBump : ℝ → ℝ) =ᶠ[𝓝 t] fun _ => (0 : ℝ) :=
    Filter.eventually_of_mem (hU.mem_nhds ht) fun s hs => cutBump_zero_of_two_le (le_of_lt hs)
  rw [hev.deriv_eq]
  simp

theorem exists_bound_deriv_cutBump : ∃ K : ℝ, 0 ≤ K ∧ ∀ t, |deriv cutBump t| ≤ K := by
  obtain ⟨K, hK⟩ := ((cutBump.contDiff (n := 1)).continuous_deriv le_rfl).bounded_above_of_compact_support
    cutBump.hasCompactSupport.deriv
  exact ⟨max K 0, le_max_right _ _, fun t => (hK t).trans (le_max_left _ _)⟩

/-- The band set `{|η| ≤ 2R}` has cell measure `4 c R`. -/
theorem cell_band_measure {c R : ℝ} (hc : 0 < c) (hR : 0 < R) :
    (volume.restrict (B0579.cell c)) {x : B0579.Plane | |x.2| ≤ 2 * R} =
      ENNReal.ofReal (c * (4 * R)) := by
  have hS : MeasurableSet {x : B0579.Plane | |x.2| ≤ 2 * R} :=
    measurableSet_le (continuous_abs.comp continuous_snd).measurable measurable_const
  rw [Measure.restrict_apply hS]
  have hset : {x : B0579.Plane | |x.2| ≤ 2 * R} ∩ B0579.cell c =
      Ico (-(c / 2)) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R) := by
    ext x
    simp only [B0579.cell, mem_inter_iff, mem_setOf_eq, mem_prod, mem_univ, and_true,
      mem_Icc, abs_le]
    tauto
  rw [hset, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, Real.volume_Icc,
    ← ENNReal.ofReal_mul (by linarith)]
  congr 1
  ring

theorem zeroCirculation_of_weak {c : ℝ} (hc : 0 < c) {u0 u1 a b : B0579.Plane → ℂ}
    (hu0 : MemLp u0 2 (volume.restrict (B0579.cell c)))
    (ha : IIIa.HasWeakCellDerivC c 0 u1 a) (hb : IIIa.HasWeakCellDerivC c 1 u0 b)
    (hab : IntegrableOn (fun z => a z - b z) (B0579.cell c)) :
    ∫ z in B0579.cell c, (a z - b z) = 0 := by
  obtain ⟨K, hK0, hK⟩ := exists_bound_deriv_cutBump
  -- the pairing identity
  have hid : ∀ R : ℝ, 0 < R → ∫ z in B0579.cell c, (a z - b z) * (cutR R z : ℂ) =
      ∫ z in B0579.cell c, u0 z * (B0579.pd 1 (cutR R) z : ℂ) := by
    intro R hR
    have hT := cutR_isCylTest c hR
    have hai2 := (ha.1 _ hT).2
    have hbi2 := (hb.1 _ hT).2
    have ha2 := ha.2 _ hT
    have hb2 := hb.2 _ hT
    simp only [pd0_cutR, Complex.ofReal_zero, mul_zero, integral_zero] at ha2
    have e1 : ∫ z in B0579.cell c, (a z - b z) * (cutR R z : ℂ) =
        (∫ z in B0579.cell c, a z * (cutR R z : ℂ)) -
          ∫ z in B0579.cell c, b z * (cutR R z : ℂ) := by
      rw [← integral_sub hai2 hbi2]
      congr 1
      ext z
      ring
    rw [e1, hb2]
    linear_combination ha2
  -- the boundary term is `O(R^{-1/2})`
  set A : ℝ := (∫ z in B0579.cell c, ‖u0 z‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) with hA
  have hbd : ∀ R : ℝ, 0 < R →
      ‖∫ z in B0579.cell c, u0 z * (B0579.pd 1 (cutR R) z : ℂ)‖ ≤
        K / R * (A * Real.sqrt (c * (4 * R))) := by
    intro R hR
    set S : Set B0579.Plane := {x : B0579.Plane | |x.2| ≤ 2 * R} with hSdef
    have hS : MeasurableSet S :=
      measurableSet_le (continuous_abs.comp continuous_snd).measurable measurable_const
    have hμS : (volume.restrict (B0579.cell c)) S = ENNReal.ofReal (c * (4 * R)) :=
      cell_band_measure hc hR
    have hind2 : MemLp (S.indicator (fun _ => (1 : ℝ))) 2 (volume.restrict (B0579.cell c)) := by
      refine (memLp_indicator_iff_restrict hS).2 ?_
      have : IsFiniteMeasure ((volume.restrict (B0579.cell c)).restrict S) :=
        isFiniteMeasure_restrict.2 (by rw [hμS]; exact ENNReal.ofReal_ne_top)
      exact memLp_const 1
    have hnu0 : MemLp (fun z => ‖u0 z‖) 2 (volume.restrict (B0579.cell c)) := hu0.norm
    have hint : Integrable (fun z => ‖u0 z‖ * S.indicator (fun _ => (1 : ℝ)) z)
        (volume.restrict (B0579.cell c)) := hnu0.integrable_mul hind2
    have hpt : ∀ z, ‖u0 z * (B0579.pd 1 (cutR R) z : ℂ)‖ ≤
        K / R * (‖u0 z‖ * S.indicator (fun _ => (1 : ℝ)) z) := by
      intro z
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, pd1_cutR]
      by_cases hz : z ∈ S
      · rw [indicator_of_mem hz, mul_one, abs_mul, abs_of_pos (one_div_pos.2 hR)]
        have := hK (z.2 / R)
        calc ‖u0 z‖ * (|deriv cutBump (z.2 / R)| * (1 / R)) ≤ ‖u0 z‖ * (K * (1 / R)) := by
              gcongr
          _ = K / R * ‖u0 z‖ := by ring
      · rw [indicator_of_notMem hz, mul_zero, mul_zero]
        have hz' : 2 < |z.2 / R| := by
          rw [abs_div, abs_of_pos hR, lt_div_iff₀ hR]
          simpa [hSdef] using hz
        rw [deriv_cutBump_eq_zero hz']
        simp
    have h1 : ‖∫ z in B0579.cell c, u0 z * (B0579.pd 1 (cutR R) z : ℂ)‖ ≤
        ∫ z in B0579.cell c, K / R * (‖u0 z‖ * S.indicator (fun _ => (1 : ℝ)) z) :=
      norm_integral_le_of_norm_le (hint.const_mul _) (Eventually.of_forall hpt)
    rw [integral_const_mul] at h1
    refine h1.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (div_nonneg hK0 hR.le)
    have hH := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict (B0579.cell c))
      Real.HolderConjugate.two_two (f := fun z => ‖u0 z‖)
      (g := S.indicator (fun _ => (1 : ℝ)))
      (Eventually.of_forall fun z => norm_nonneg _)
      (Eventually.of_forall fun z => indicator_nonneg (fun _ _ => zero_le_one) z)
      (by simpa using hnu0) (by simpa using hind2)
    refine hH.trans_eq ?_
    congr 1
    have hsq : (fun z => S.indicator (fun _ => (1 : ℝ)) z ^ (2 : ℝ)) =
        S.indicator (fun _ => (1 : ℝ)) := by
      funext z
      by_cases hz : z ∈ S
      · simp [indicator_of_mem hz]
      · simp [indicator_of_notMem hz]
    have hone : (S.indicator fun _ => (1 : ℝ)) = S.indicator 1 := rfl
    rw [hsq, hone, integral_indicator_one hS, measureReal_def, hμS,
      ENNReal.toReal_ofReal (by positivity), Real.sqrt_eq_rpow]
  -- limits along `R = n + 1`
  have hR : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hlim1 : Tendsto (fun n : ℕ => ∫ z in B0579.cell c, (a z - b z) * (cutR ((n : ℝ) + 1) z : ℂ))
      atTop (𝓝 (∫ z in B0579.cell c, (a z - b z))) := by
    refine tendsto_integral_of_dominated_convergence (fun z => ‖a z - b z‖) (fun n => ?_)
      hab.norm (fun n => Eventually.of_forall fun z => ?_) (Eventually.of_forall fun z => ?_)
    · have hT := cutR_isCylTest c (hR n)
      exact ((ha.1 _ hT).2.sub (hb.1 _ hT).2).aestronglyMeasurable.congr
        (Eventually.of_forall fun z => by simp only [Pi.sub_apply]; ring)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (show 0 ≤ cutR ((n : ℝ) + 1) z from cutBump.nonneg)]
      exact mul_le_of_le_one_right (norm_nonneg _) (show cutR ((n : ℝ) + 1) z ≤ 1 from cutBump.le_one)
    · refine tendsto_const_nhds.congr' ?_
      obtain ⟨N, hN⟩ := exists_nat_ge |z.2|
      filter_upwards [eventually_ge_atTop N] with n hn
      have hle : |z.2 / ((n : ℝ) + 1)| ≤ 1 := by
        rw [abs_div, abs_of_pos (hR n), div_le_one (hR n)]
        have : (N : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      simp [cutR, cutBump_one_of_le_one hle]
  have hlim2 : Tendsto (fun n : ℕ => ∫ z in B0579.cell c, (a z - b z) * (cutR ((n : ℝ) + 1) z : ℂ))
      atTop (𝓝 0) := by
    have hsq : Tendsto (fun n : ℕ => K * A * Real.sqrt (4 * c) / Real.sqrt ((n : ℝ) + 1)) atTop
        (𝓝 0) := by
      refine Tendsto.div_atTop tendsto_const_nhds ?_
      exact Real.tendsto_sqrt_atTop.comp
        (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    refine squeeze_zero_norm (fun n => ?_) hsq
    rw [hid _ (hR n)]
    refine (hbd _ (hR n)).trans_eq ?_
    have hs : Real.sqrt ((n : ℝ) + 1) ≠ 0 := (Real.sqrt_pos.2 (hR n)).ne'
    have hss : Real.sqrt ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1) = (n : ℝ) + 1 :=
      Real.mul_self_sqrt (hR n).le
    rw [show c * (4 * ((n : ℝ) + 1)) = (4 * c) * ((n : ℝ) + 1) by ring,
      Real.sqrt_mul (by positivity)]
    calc K / ((n : ℝ) + 1) * (A * (Real.sqrt (4 * c) * Real.sqrt ((n : ℝ) + 1)))
        = K * A * Real.sqrt (4 * c) * Real.sqrt ((n : ℝ) + 1) / ((n : ℝ) + 1) := by ring
      _ = K * A * Real.sqrt (4 * c) * Real.sqrt ((n : ℝ) + 1) /
            (Real.sqrt ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1)) := by rw [hss]
      _ = K * A * Real.sqrt (4 * c) / Real.sqrt ((n : ℝ) + 1) := by field_simp
  exact tendsto_nhds_unique hlim1 hlim2

theorem zeroCirculationOfWeak_proof : ZeroCirculationOfWeak :=
  fun _c hc _u0 _u1 _a _b hu0 ha hb hab => zeroCirculation_of_weak hc hu0 ha hb hab

end UnforcedLeray.Short.IIb.FlatBvSliceGoodAeNeeded

end
