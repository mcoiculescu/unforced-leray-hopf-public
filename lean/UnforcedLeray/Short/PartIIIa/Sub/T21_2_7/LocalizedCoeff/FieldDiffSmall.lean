import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.LocalizedCoeff.FieldBound
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_1_7_5

/-!
# `PartIII-a:T21/2/7/1/7/5/3`: the field difference is small (`LocFieldDiffSmall`)

Source: `the November 2 reference manuscript`
lines 3052-3058.

For `w ∈ X_{-m,c}`, `r, r₀ ∈ [0, T]` and `F_j(r) = w ∂_jE(r) - w ∂_jE(r₀)`, the pointwise bound
`|∂_jE(r)| ≤ |C| jb^{-m/2} jb^{-1}` on the cell (`LadTrainBdd`, copied from `locFieldBound`) gives
`|F_j(r)(x)| ≤ |w(x)| · 2|C| jb^{-m/2} jb^{-1}`, and the dominating function is in `L¹ ∩ L²(cell)`
by `FieldBoundAux.core`. Pointwise convergence `r → r₀` comes from `LocPdEcCont`, and dominated
convergence in `eLpNorm` (`tendsto_eLpNorm_zero_of_dom`) gives the claim for `p = 1` and `p = 2`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace FieldDiffSmallAux

open UnforcedLeray.B0579

/-- Dominated convergence for `eLpNorm` along a countably generated filter. -/
theorem tendsto_eLpNorm_zero_of_dom {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    {l : Filter ι} [l.IsCountablyGenerated] {D : ι → α → ℂ} {W : α → ℂ} {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hpt : p ≠ ⊤) (hW : eLpNorm W p μ < ⊤)
    (hD : ∀ᶠ r in l, AEStronglyMeasurable (D r) μ)
    (hdom : ∀ᶠ r in l, ∀ᵐ x ∂μ, ‖D r x‖ₑ ≤ ‖W x‖ₑ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun r => ‖D r x‖ₑ) l (𝓝 0)) :
    Tendsto (fun r => eLpNorm (D r) p μ) l (𝓝 0) := by
  have hqpos : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  have hI : Tendsto (fun r => ∫⁻ x, ‖D r x‖ₑ ^ p.toReal ∂μ) l (𝓝 0) := by
    have h := tendsto_lintegral_filter_of_dominated_convergence' (μ := μ) (l := l)
      (F := fun r x => ‖D r x‖ₑ ^ p.toReal) (f := fun _ => (0 : ℝ≥0∞))
      (fun x => ‖W x‖ₑ ^ p.toReal) ?_ ?_ ?_ ?_
    · simpa only [lintegral_zero] using h
    · filter_upwards [hD] with r hr
      exact (AEStronglyMeasurable.enorm hr).pow_const _
    · filter_upwards [hdom] with r hr
      filter_upwards [hr] with x hx
      exact ENNReal.rpow_le_rpow hx hqpos.le
    · exact ((eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hpt).1 hW).ne
    · filter_upwards [hlim] with x hx
      have h2 : Tendsto (fun r => ‖D r x‖ₑ ^ p.toReal) l (𝓝 ((0 : ℝ≥0∞) ^ p.toReal)) :=
        (ENNReal.continuous_rpow_const.tendsto 0).comp hx
      rw [ENNReal.zero_rpow_of_pos hqpos] at h2
      exact h2
  have hJ : Tendsto (fun r => (∫⁻ x, ‖D r x‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal)) l (𝓝 0) := by
    have h : Tendsto (fun r => (∫⁻ x, ‖D r x‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal)) l
        (𝓝 ((0 : ℝ≥0∞) ^ (1 / p.toReal))) :=
      (ENNReal.continuous_rpow_const.tendsto 0).comp hI
    rw [ENNReal.zero_rpow_of_pos (one_div_pos.2 hqpos)] at h
    exact h
  exact hJ.congr (fun r => (eLpNorm_eq_lintegral_rpow_enorm_toReal (f := D r) hp0 hpt).symm)

/-- The dominating coefficient `2|C| jb^{-m/2} jb^{-1}`. -/
def domP (m C : ℝ) (x : ℝ × ℝ) : ℝ := (2 * |C|) * (jb x ^ (-m / 2) * jb x ^ (-1 : ℝ))

theorem domP_cont (m C : ℝ) : Continuous (domP m C) :=
  continuous_const.mul ((continuous_jb_rpow _).mul (continuous_jb_rpow _))

theorem domP_nonneg (m C : ℝ) (x : ℝ × ℝ) : 0 ≤ domP m C x :=
  mul_nonneg (by positivity)
    (mul_nonneg (Real.rpow_nonneg (jb_pos x).le _) (Real.rpow_nonneg (jb_pos x).le _))

theorem abs_domP (m C : ℝ) (x : ℝ × ℝ) : |domP m C x| = domP m C x :=
  abs_of_nonneg (domP_nonneg m C x)

/-- Pointwise bound of `∂_jE(r)` on the cell (the step of `locFieldBound`). -/
theorem pd_bound {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {m T C : ℝ}
    (hb : LadTrainBdd tr m T C) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) T) (j : Fin 2) {x : ℝ × ℝ}
    (hx : x ∈ cell c) :
    |pd j (UnforcedLeray.B0238.Ec tr r) x| ≤ |C| * (jb x ^ (-m / 2) * jb x ^ (-1 : ℝ)) := by
  have h1 := (hb r hr x hx).2 j
  have hJ : 0 < jb x := jb_pos x
  have hA : jb x ^ ((m + 2) / 2) = jb x ^ (m / 2) * jb x := by
    rw [show (m + 2) / 2 = m / 2 + 1 by ring, Real.rpow_add hJ, Real.rpow_one]
  have hneg : jb x ^ (-m / 2) = (jb x ^ (m / 2))⁻¹ := by
    rw [show -m / 2 = -(m / 2) by ring, Real.rpow_neg hJ.le]
  rw [hneg, Real.rpow_neg_one]
  apply FieldBoundAux.pt_bound (Real.rpow_pos_of_pos hJ _) hJ
  have e : |pd j (UnforcedLeray.B0238.Ec tr r) x| * (jb x ^ (m / 2) * jb x) =
      jb x ^ ((m + 2) / 2) * |pd j (UnforcedLeray.B0238.Ec tr r) x| := by
    rw [hA]; ring
  rw [e]
  exact h1.trans (le_abs_self C)

/-- Continuity of `∂_jE(r)` in space, for `r ≥ 0` (the step of `locFieldBound`). -/
theorem pd_Ec_cont {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {r : ℝ} (hr : 0 ≤ r)
    (j : Fin 2) : Continuous (pd j (UnforcedLeray.B0238.Ec tr r)) := by
  have hv : ContDiff ℝ ∞ (tr.v r) := UnforcedLeray.B0238.contDiff_Vc tr hr
  have hv1 : ContDiff ℝ 1 (tr.v r) := hv.of_le (by exact_mod_cast le_top)
  have hEq : UnforcedLeray.B0238.Ec tr r = fun z =>
      fderiv ℝ (fun w => tr.v r w 1) z (1, 0) - fderiv ℝ (fun w => tr.v r w 0) z (0, 1) :=
    funext fun z => UnforcedLeray.B0238.curl_eq_fderiv hv1 z
  have hEc1 : ContDiff ℝ 1 (UnforcedLeray.B0238.Ec tr r) := by
    rw [hEq]
    exact (((UnforcedLeray.B0238.contDiff_comp_apply hv 1).fderiv_right
        (m := 1) (by norm_num)).clm_apply contDiff_const).sub
      (((UnforcedLeray.B0238.contDiff_comp_apply hv 0).fderiv_right
        (m := 1) (by norm_num)).clm_apply contDiff_const)
  exact UnforcedLeray.B0238.continuous_fderiv_apply hEc1 (dir j)

end FieldDiffSmallAux

open FieldDiffSmallAux FieldBoundAux in
open UnforcedLeray.B0579 in
/-- **(S3) The field difference is small** (SP 3052-3058): dominated convergence in `eLpNorm`
for `F_j(r) = w ∂_jE(r) - w ∂_jE(r₀)`, with dominating function `2|C| |w| jb^{-m/2} jb^{-1}`. -/
theorem locFieldDiffSmall (m : ℝ) (hm : 8 < m) (hP : LocPdEcCont) : LocFieldDiffSmall m := by
  intro ν hν hν1 tr T C hT hb w r₀ hr₀ j
  -- the dominating function lies in `L¹ ∩ L²(cell)`
  obtain ⟨hI1, hL2, -⟩ := core (c := ν ^ (-2 : ℝ)) (m := m) (P := domP m C) (domP_cont m C)
    (K := 2 * |C|) (by positivity)
    (fun x _ => by rw [abs_domP]; unfold domP; exact le_rfl) w
  have hW1 : eLpNorm (fun x => w x * ((domP m C x : ℝ) : ℂ)) 1
      (volume.restrict (cell (ν ^ (-2 : ℝ)))) < ⊤ :=
    (memLp_one_iff_integrable.2 hI1).eLpNorm_lt_top
  have hW2 : eLpNorm (fun x => w x * ((domP m C x : ℝ) : ℂ)) 2
      (volume.restrict (cell (ν ^ (-2 : ℝ)))) < ⊤ :=
    hL2.eLpNorm_lt_top
  -- pointwise domination of the difference
  have hdomPt : ∀ r ∈ Icc (0 : ℝ) T, ∀ x ∈ cell (ν ^ (-2 : ℝ)),
      ‖w x * ((pd j (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ) -
          w x * ((pd j (UnforcedLeray.B0238.Ec tr r₀) x : ℝ) : ℂ)‖ₑ ≤
        ‖w x * ((domP m C x : ℝ) : ℂ)‖ₑ := by
    intro r hr x hx
    have h1 := pd_bound tr hb hr j hx
    have h0 := pd_bound tr hb hr₀ j hx
    have hdom_eq : domP m C x = 2 * (|C| * (jb x ^ (-m / 2) * jb x ^ (-1 : ℝ))) := by
      unfold domP; ring
    have hab : |pd j (UnforcedLeray.B0238.Ec tr r) x - pd j (UnforcedLeray.B0238.Ec tr r₀) x|
        ≤ domP m C x := by
      rw [hdom_eq]
      have a1 := abs_le.1 h1
      have a0 := abs_le.1 h0
      exact abs_le.2 ⟨by linarith [a1.1, a0.2], by linarith [a1.2, a0.1]⟩
    have hn : w x * ((pd j (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ) -
          w x * ((pd j (UnforcedLeray.B0238.Ec tr r₀) x : ℝ) : ℂ) =
        w x * (((pd j (UnforcedLeray.B0238.Ec tr r) x -
          pd j (UnforcedLeray.B0238.Ec tr r₀) x : ℝ)) : ℂ) := by
      push_cast; ring
    rw [hn]
    have key : ‖w x * ((pd j (UnforcedLeray.B0238.Ec tr r) x -
          pd j (UnforcedLeray.B0238.Ec tr r₀) x : ℝ) : ℂ)‖ ≤
        ‖w x * ((domP m C x : ℝ) : ℂ)‖ := by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_domP]
      exact mul_le_mul_of_nonneg_left hab (norm_nonneg _)
    exact le_trans (le_of_eq (ofReal_norm _).symm)
      (le_trans (ENNReal.ofReal_le_ofReal key) (le_of_eq (ofReal_norm _)))

  -- measurability of the differences
  have hwm : AEStronglyMeasurable w (volume.restrict (cell (ν ^ (-2 : ℝ)))) :=
    (Lp.aestronglyMeasurable w).mono_ac (ac_cellMeasure (ν ^ (-2 : ℝ)) (-m))
  have hD : ∀ᶠ r in 𝓝[Icc (0 : ℝ) T] r₀, AEStronglyMeasurable (fun x =>
      w x * ((pd j (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ) -
        w x * ((pd j (UnforcedLeray.B0238.Ec tr r₀) x : ℝ) : ℂ))
      (volume.restrict (cell (ν ^ (-2 : ℝ)))) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (hwm.mul (Complex.continuous_ofReal.comp
        (pd_Ec_cont tr hr.1 j)).aestronglyMeasurable).sub
      (hwm.mul (Complex.continuous_ofReal.comp
        (pd_Ec_cont tr hr₀.1 j)).aestronglyMeasurable)
  have hdom : ∀ᶠ r in 𝓝[Icc (0 : ℝ) T] r₀, ∀ᵐ x ∂(volume.restrict (cell (ν ^ (-2 : ℝ)))),
      ‖w x * ((pd j (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ) -
          w x * ((pd j (UnforcedLeray.B0238.Ec tr r₀) x : ℝ) : ℂ)‖ₑ ≤
        ‖w x * ((domP m C x : ℝ) : ℂ)‖ₑ := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    filter_upwards [ae_restrict_mem (measurableSet_cell (ν ^ (-2 : ℝ)))] with x hx
    exact hdomPt r hr x hx
  -- pointwise convergence from `LocPdEcCont`
  have hlim : ∀ᵐ x ∂(volume.restrict (cell (ν ^ (-2 : ℝ)))),
      Tendsto (fun r => ‖w x * ((pd j (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ) -
          w x * ((pd j (UnforcedLeray.B0238.Ec tr r₀) x : ℝ) : ℂ)‖ₑ)
        (𝓝[Icc (0 : ℝ) T] r₀) (𝓝 0) := by
    filter_upwards [ae_restrict_mem (measurableSet_cell (ν ^ (-2 : ℝ)))] with x hx
    have hc : ContinuousWithinAt (fun r => pd j (UnforcedLeray.B0238.Ec tr r) x) (Ici 0) r₀ :=
      hP ν (ν ^ (-2 : ℝ)) tr j x r₀ (Set.mem_Ici.2 hr₀.1)
    have h2 : Tendsto (fun r => pd j (UnforcedLeray.B0238.Ec tr r) x) (𝓝[Icc (0 : ℝ) T] r₀)
        (𝓝 (pd j (UnforcedLeray.B0238.Ec tr r₀) x)) :=
      hc.mono Icc_subset_Ici_self
    have h2c : Tendsto (fun r => ((pd j (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ))
        (𝓝[Icc (0 : ℝ) T] r₀) (𝓝 ((pd j (UnforcedLeray.B0238.Ec tr r₀) x : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp h2
    have h3 : Tendsto (fun r => w x * ((pd j (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ) -
          w x * ((pd j (UnforcedLeray.B0238.Ec tr r₀) x : ℝ) : ℂ))
        (𝓝[Icc (0 : ℝ) T] r₀)
        (𝓝 (w x * ((pd j (UnforcedLeray.B0238.Ec tr r₀) x : ℝ) : ℂ) -
          w x * ((pd j (UnforcedLeray.B0238.Ec tr r₀) x : ℝ) : ℂ))) :=
      (h2c.const_mul (w x)).sub tendsto_const_nhds
    rw [show w x * ((pd j (UnforcedLeray.B0238.Ec tr r₀) x : ℝ) : ℂ) -
        w x * ((pd j (UnforcedLeray.B0238.Ec tr r₀) x : ℝ) : ℂ) = 0 from sub_self _] at h3
    have h4 : Tendsto (fun r => ‖w x * ((pd j (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ) -
          w x * ((pd j (UnforcedLeray.B0238.Ec tr r₀) x : ℝ) : ℂ)‖ₑ)
        (𝓝[Icc (0 : ℝ) T] r₀) (𝓝 ‖(0 : ℂ)‖ₑ) :=
      (continuous_enorm.tendsto (0 : ℂ)).comp h3
    rw [enorm_zero] at h4
    exact h4
  -- conclusion: the two `eLpNorm` terms tend to `0`
  have e1 := tendsto_eLpNorm_zero_of_dom (p := 1) (D := fun r x =>
      w x * ((pd j (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ) -
        w x * ((pd j (UnforcedLeray.B0238.Ec tr r₀) x : ℝ) : ℂ))
    (W := fun x => w x * ((domP m C x : ℝ) : ℂ)) one_ne_zero ENNReal.one_ne_top hW1 hD hdom hlim
  have e2 := tendsto_eLpNorm_zero_of_dom (p := 2) (D := fun r x =>
      w x * ((pd j (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ) -
        w x * ((pd j (UnforcedLeray.B0238.Ec tr r₀) x : ℝ) : ℂ))
    (W := fun x => w x * ((domP m C x : ℝ) : ℂ)) two_ne_zero ENNReal.ofNat_ne_top hW2 hD hdom hlim
  have e := e1.add e2
  rw [add_zero] at e
  exact e

end UnforcedLeray.Short.IIIa
