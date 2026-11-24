import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_6_4_2_3_2
import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_6_4_2_3_2.L1
import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_6_4_2_3_2.L2

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Short.PartI

/-- The shift derivative of the integrand `v ↦ ⟪ψ(z - v), g z⟫` at `v`, as a functional of `z`. -/
def l4D (ψ g : Plane → Vec) (v z : Plane) : Plane →L[ℝ] ℝ :=
  (innerSL ℝ (g z)).comp ((fderiv ℝ ψ (z - v)).comp (-(ContinuousLinearMap.id ℝ Plane)))

theorem l4_fderiv_zero {R : ℝ} {ψ : Plane → Vec} (hR : ∀ z : Plane, R < |z.2| → ψ z = 0)
    (w : Plane) (hw : R < |w.2|) : fderiv ℝ ψ w = 0 := by
  have hev : ψ =ᶠ[𝓝 w] fun _ => 0 := by
    have h1 : ∀ᶠ z in 𝓝 w, R < |z.2| :=
      ((continuous_snd.abs).tendsto w).eventually (lt_mem_nhds hw)
    filter_upwards [h1] with z hz
    exact hR z hz
  rw [hev.fderiv_eq]
  simp

theorem l4_fderiv_decomp {ψ : Plane → Vec} (hsm : ContDiff ℝ ∞ ψ) (w d : Plane) :
    fderiv ℝ ψ w d = d.1 • Cyl.partialQ ψ w + d.2 • Cyl.partialEta ψ w := by
  have hd : Differentiable ℝ ψ := hsm.differentiable (by simp)
  rw [Cyl.partialQ_eq_fderiv hd w, Cyl.partialEta_eq_fderiv hd w]
  have hdec : d = d.1 • ((1 : ℝ), (0 : ℝ)) + d.2 • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  conv_lhs => rw [hdec]
  rw [map_add, map_smul, map_smul]

theorem l4_hasFDerivAt {ψ g : Plane → Vec} (hsm : ContDiff ℝ ∞ ψ) (z v : Plane) :
    HasFDerivAt (fun v => inner ℝ (ψ (z - v)) (g z)) (l4D ψ g v z) v := by
  have hd : Differentiable ℝ ψ := hsm.differentiable (by simp)
  have hL : HasFDerivAt (fun v : Plane => z - v) (-(ContinuousLinearMap.id ℝ Plane)) v :=
    (hasFDerivAt_id v).const_sub z
  have h2 : HasFDerivAt (fun v : Plane => ψ (z - v))
      ((fderiv ℝ ψ (z - v)).comp (-(ContinuousLinearMap.id ℝ Plane))) v :=
    (hd (z - v)).hasFDerivAt.comp v hL
  have h3 := (innerSL ℝ (g z)).hasFDerivAt.comp v h2
  have hfun : (fun v : Plane => inner ℝ (ψ (z - v)) (g z)) =
      (innerSL ℝ (g z)) ∘ (fun v : Plane => ψ (z - v)) := by
    funext w
    simp only [Function.comp, innerSL_apply_apply]
    exact real_inner_comm _ _
  rw [hfun]
  exact h3

theorem l4_norm_D_le {ψ g : Plane → Vec} (z v : Plane) :
    ‖l4D ψ g v z‖ ≤ ‖g z‖ * ‖fderiv ℝ ψ (z - v)‖ := by
  have h1 := ContinuousLinearMap.opNorm_comp_le (innerSL ℝ (g z))
    ((fderiv ℝ ψ (z - v)).comp (-(ContinuousLinearMap.id ℝ Plane)))
  have h2 := ContinuousLinearMap.opNorm_comp_le (fderiv ℝ ψ (z - v))
    (-(ContinuousLinearMap.id ℝ Plane))
  have h3 : ‖-(ContinuousLinearMap.id ℝ Plane)‖ ≤ 1 := by
    rw [norm_neg]; exact ContinuousLinearMap.norm_id_le
  rw [innerSL_apply_norm] at h1
  unfold l4D
  calc ‖(innerSL ℝ (g z)).comp ((fderiv ℝ ψ (z - v)).comp (-(ContinuousLinearMap.id ℝ Plane)))‖
      ≤ ‖g z‖ * ‖(fderiv ℝ ψ (z - v)).comp (-(ContinuousLinearMap.id ℝ Plane))‖ := h1
    _ ≤ ‖g z‖ * (‖fderiv ℝ ψ (z - v)‖ * ‖-(ContinuousLinearMap.id ℝ Plane)‖) :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ ≤ ‖g z‖ * (‖fderiv ℝ ψ (z - v)‖ * 1) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (norm_nonneg _)) (norm_nonneg _)
    _ = ‖g z‖ * ‖fderiv ℝ ψ (z - v)‖ := by ring

theorem l4_D_base {ψ g : Plane → Vec} (hsm : ContDiff ℝ ∞ ψ) (z x : Plane) :
    l4D ψ g x z = dParam (inner ℝ (Cyl.partialQ ψ (z - x)) (g z))
      (inner ℝ (Cyl.partialEta ψ (z - x)) (g z)) := by
  refine ContinuousLinearMap.ext fun d => ?_
  have hfd : fderiv ℝ ψ (z - x) (-d) =
      (-d).1 • Cyl.partialQ ψ (z - x) + (-d).2 • Cyl.partialEta ψ (z - x) :=
    l4_fderiv_decomp hsm (z - x) (-d)
  unfold l4D
  rw [dParam_apply]
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.id_apply]
  rw [hfd, inner_add_right, real_inner_smul_right, real_inner_smul_right, Prod.fst_neg,
    Prod.snd_neg, real_inner_comm (Cyl.partialQ ψ (z - x)) (g z),
    real_inner_comm (Cyl.partialEta ψ (z - x)) (g z)]
  ring

theorem l4_dParam_eq (a b : ℝ) :
    dParam a b = a • (-(ContinuousLinearMap.fst ℝ ℝ ℝ)) + b • (-(ContinuousLinearMap.snd ℝ ℝ ℝ)) := by
  refine ContinuousLinearMap.ext fun d => ?_
  rw [dParam_apply]
  simp <;> ring

theorem l4_cont_dParam : Continuous fun p : ℝ × ℝ => dParam p.1 p.2 := by
  simp only [l4_dParam_eq]
  exact (continuous_fst.smul continuous_const).add (continuous_snd.smul continuous_const)

theorem l4_fderiv_bound {ψ : Plane → Vec} (hsm : ContDiff ℝ ∞ ψ) (r : ℝ) :
    ∃ M1 : ℝ, ∀ w : Plane, ‖w‖ ≤ r → ‖fderiv ℝ ψ w‖ ≤ M1 := by
  obtain ⟨M1, hM1⟩ := (isCompact_closedBall (0 : Plane) r).exists_bound_of_continuousOn
    (hsm.continuous_fderiv (by simp)).continuousOn
  exact ⟨M1, fun w hw => hM1 w (mem_closedBall_zero_iff.2 hw)⟩

theorem l4_norm_le_of_abs {w : Plane} {r : ℝ} (h1 : |w.1| ≤ r) (h2 : |w.2| ≤ r) : ‖w‖ ≤ r := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  exact max_le h1 h2

theorem l4_ball_coords {v x : Plane} (h : v ∈ Metric.ball x 1) :
    |v.1 - x.1| < 1 ∧ |v.2 - x.2| < 1 := by
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq] at h
  exact h

theorem l4_strip_finite (c R : ℝ) (x : Plane) :
    (volume.restrict (Cyl.cell c)) {z : Plane | |z.2 - x.2| ≤ R + 1} < ⊤ := by
  rw [Measure.restrict_apply' (Cyl.measurableSet_cell c)]
  have hK : IsCompact (Icc (-c / 2) (c / 2) ×ˢ Icc (x.2 - (R + 1)) (x.2 + (R + 1))) :=
    isCompact_Icc.prod isCompact_Icc
  have hsub : {z : Plane | |z.2 - x.2| ≤ R + 1} ∩ Cyl.cell c ⊆
      Icc (-c / 2) (c / 2) ×ˢ Icc (x.2 - (R + 1)) (x.2 + (R + 1)) := by
    rintro z ⟨hz1, hz2⟩
    have hz1' : |z.2 - x.2| ≤ R + 1 := hz1
    obtain ⟨h1, h2⟩ := Cyl.mem_cell.1 hz2
    have h3 := abs_le.1 hz1'
    exact ⟨⟨h1, h2.le⟩, ⟨by linarith [h3.1], by linarith [h3.2]⟩⟩
  exact lt_of_le_of_lt (measure_mono hsub) hK.measure_lt_top

theorem l4_bound_integrable (c R : ℝ) (x : Plane) (G : Cyl.L2v c) (M : ℝ) :
    Integrable (fun z : Plane => M * (‖((G : Cyl.L2v c) : Plane → Vec) z‖ *
      ({z : Plane | |z.2 - x.2| ≤ R + 1}.indicator (fun _ => (1 : ℝ)) z))) (Cyl.cellμ c) := by
  have hSm : MeasurableSet {z : Plane | |z.2 - x.2| ≤ R + 1} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  have hind : MemLp ({z : Plane | |z.2 - x.2| ≤ R + 1}.indicator (fun _ => (1 : ℝ))) 2
      (Cyl.cellμ c) :=
    memLp_indicator_const 2 hSm 1 (Or.inr (l4_strip_finite c R x).ne)
  have hG : MemLp (fun z : Plane => ‖((G : Cyl.L2v c) : Plane → Vec) z‖) 2 (Cyl.cellμ c) :=
    (Lp.memLp G).norm
  have hprod : Integrable (fun z : Plane => ‖((G : Cyl.L2v c) : Plane → Vec) z‖ *
      ({z : Plane | |z.2 - x.2| ≤ R + 1}.indicator (fun _ => (1 : ℝ)) z)) (Cyl.cellμ c) :=
    MemLp.integrable_mul hG hind
  exact hprod.const_mul M

theorem leafParamIntHasFDerivCH_proof : UnforcedLeray.Short.PartI.LeafParamIntHasFDerivCH := by
  unfold LeafParamIntHasFDerivCH
  intro c hc ψ G hψ x
  have hψu : ContDiff ℝ ∞ ψ ∧ Cyl.IsPeriodic c ψ ∧ ∃ R : ℝ, ∀ z : Plane, R < |z.2| → ψ z = 0 := hψ
  obtain ⟨hsm, -, R, hR⟩ := hψu
  have hQ : IsCellTest c (Cyl.partialQ ψ) := (leafCellTestPartialCH_proof c ψ hψ).1
  have hE : IsCellTest c (Cyl.partialEta ψ) := (leafCellTestPartialCH_proof c ψ hψ).2
  have hαint := leafParamIntIntegrableCH_proof c hc (Cyl.partialQ ψ) G hQ x
  have hβint := leafParamIntIntegrableCH_proof c hc (Cyl.partialEta ψ) G hE x
  have hFint := leafParamIntIntegrableCH_proof c hc ψ G hψ x
  set g : Plane → Vec := ((G : Cyl.L2v c) : Plane → Vec) with hg
  set r : ℝ := c / 2 + |x.1| + |R| + 2 with hr
  obtain ⟨M1, hM1⟩ := l4_fderiv_bound hsm r
  set S : Set Plane := {z : Plane | |z.2 - x.2| ≤ R + 1} with hS
  set bnd : Plane → ℝ := fun z => M1 * (‖g z‖ * S.indicator (fun _ => (1 : ℝ)) z) with hbnd
  have hbnd_int : Integrable bnd (Cyl.cellμ c) := l4_bound_integrable c R x G M1
  have hbound : ∀ z ∈ Cyl.cell c, ∀ v ∈ Metric.ball x 1, ‖l4D ψ g v z‖ ≤ bnd z := by
    intro z hz v hv
    obtain ⟨hv1, hv2⟩ := l4_ball_coords hv
    obtain ⟨hz1, hz2⟩ := Cyl.mem_cell.1 hz
    have hx0 := abs_nonneg x.1
    have hR0 := le_abs_self R
    have hR1 := abs_nonneg R
    have hxa := le_abs_self x.1
    have hxb := neg_le_abs x.1
    by_cases hzS : |z.2 - x.2| ≤ R + 1
    · have hmem : z - v ∈ Metric.closedBall (0 : Plane) r := by
        rw [mem_closedBall_zero_iff]
        apply l4_norm_le_of_abs
        · rw [Prod.fst_sub]
          have hv1' := abs_lt.1 hv1
          exact abs_le.2 ⟨by linarith [hv1'.1, hv1'.2], by linarith [hv1'.1, hv1'.2]⟩
        · rw [Prod.snd_sub]
          have hv2' := abs_lt.1 hv2
          have hzS' := abs_le.1 hzS
          exact abs_le.2 ⟨by linarith [hv2'.1, hv2'.2, hzS'.1, hzS'.2],
            by linarith [hv2'.1, hv2'.2, hzS'.1, hzS'.2]⟩
      have hF := hM1 (z - v) (mem_closedBall_zero_iff.1 hmem)
      have hz' : z ∈ S := hzS
      have hind : S.indicator (fun _ => (1 : ℝ)) z = 1 := by
        rw [Set.indicator_apply]; exact if_pos hz'
      show ‖l4D ψ g v z‖ ≤ M1 * (‖g z‖ * S.indicator (fun _ => (1 : ℝ)) z)
      rw [hind]
      calc ‖l4D ψ g v z‖ ≤ ‖g z‖ * ‖fderiv ℝ ψ (z - v)‖ := l4_norm_D_le z v
        _ ≤ ‖g z‖ * M1 := mul_le_mul_of_nonneg_left hF (norm_nonneg _)
        _ = M1 * (‖g z‖ * 1) := by ring
    · have hfar : R < |(z - v).2| := by
        rw [Prod.snd_sub]
        have h1 : R + 1 < |z.2 - x.2| := not_le.1 hzS
        have h2 := abs_sub_abs_le_abs_sub (z.2 - x.2) (v.2 - x.2)
        have h3 : (z.2 - x.2) - (v.2 - x.2) = z.2 - v.2 := by ring
        rw [h3] at h2
        linarith
      have hzero := l4_fderiv_zero hR (z - v) hfar
      have hind0 : S.indicator (fun _ => (1 : ℝ)) z = 0 := by
        rw [Set.indicator_apply]; exact if_neg hzS
      have hn := l4_norm_D_le (ψ := ψ) (g := g) z v
      rw [hzero, norm_zero, mul_zero] at hn
      show ‖l4D ψ g v z‖ ≤ M1 * (‖g z‖ * S.indicator (fun _ => (1 : ℝ)) z)
      rw [hind0, mul_zero, mul_zero]
      exact hn
  have h_bound : ∀ᵐ z ∂(Cyl.cellμ c), ∀ v ∈ Metric.ball x 1, ‖l4D ψ g v z‖ ≤ bnd z := by
    filter_upwards [ae_restrict_mem (Cyl.measurableSet_cell c)] with z hz
    exact fun v hv => hbound z hz v hv
  have h_diff : ∀ᵐ z ∂(Cyl.cellμ c), ∀ v ∈ Metric.ball x 1,
      HasFDerivAt (fun v => inner ℝ (ψ (z - v)) (g z)) (l4D ψ g v z) v :=
    ae_of_all _ fun z v _ => l4_hasFDerivAt (g := g) hsm z v
  have hF_meas : ∀ᶠ v in 𝓝 x,
      AEStronglyMeasurable (fun z => inner ℝ (ψ (z - v)) (g z)) (Cyl.cellμ c) :=
    Filter.Eventually.of_forall fun v =>
      AEStronglyMeasurable.inner
        (Continuous.aestronglyMeasurable (hsm.continuous.comp (continuous_id.sub continuous_const)))
        (Lp.aestronglyMeasurable G)
  have hF'_meas : AEStronglyMeasurable (l4D ψ g x) (Cyl.cellμ c) := by
    have e : l4D ψ g x = fun z => dParam (inner ℝ (Cyl.partialQ ψ (z - x)) (g z))
        (inner ℝ (Cyl.partialEta ψ (z - x)) (g z)) :=
      funext fun z => l4_D_base (g := g) hsm z x
    rw [e]
    exact l4_cont_dParam.comp_aestronglyMeasurable
      (hαint.aestronglyMeasurable.prodMk hβint.aestronglyMeasurable)
  have hDint : Integrable (l4D ψ g x) (Cyl.cellμ c) :=
    Integrable.mono' hbnd_int hF'_meas
      (h_bound.mono fun z hz => hz x (Metric.mem_ball_self one_pos))
  have hH : HasFDerivAt (fun v => ∫ z, inner ℝ (ψ (z - v)) (g z) ∂(Cyl.cellμ c))
      (∫ z, l4D ψ g x z ∂(Cyl.cellμ c)) x :=
    hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := Cyl.cellμ c)
      (F := fun v z => inner ℝ (ψ (z - v)) (g z)) (F' := fun v z => l4D ψ g v z)
      (bound := bnd) (x₀ := x) (s := Metric.ball x 1) (Metric.ball_mem_nhds x one_pos)
      hF_meas hFint hF'_meas h_bound hbnd_int h_diff
  have hfin : (∫ z, l4D ψ g x z ∂(Cyl.cellμ c)) =
      dParam (paramIntCH c (Cyl.partialQ ψ) G x) (paramIntCH c (Cyl.partialEta ψ) G x) := by
    refine ContinuousLinearMap.ext fun d => ?_
    rw [ContinuousLinearMap.integral_apply hDint d, dParam_apply]
    have e1 : ∀ z, l4D ψ g x z d = (-d.1) * inner ℝ (Cyl.partialQ ψ (z - x)) (g z)
        - d.2 * inner ℝ (Cyl.partialEta ψ (z - x)) (g z) := fun z => by
      rw [l4_D_base (g := g) hsm z x, dParam_apply]
      ring
    have h1 : Integrable (fun z : Plane => (-d.1) * inner ℝ (Cyl.partialQ ψ (z - x)) (g z))
        (Cyl.cellμ c) := hαint.const_mul (-d.1)
    have h2 : Integrable (fun z : Plane => d.2 * inner ℝ (Cyl.partialEta ψ (z - x)) (g z))
        (Cyl.cellμ c) := hβint.const_mul d.2
    have hsplit : ∫ z, ((-d.1) * inner ℝ (Cyl.partialQ ψ (z - x)) (g z)
        - d.2 * inner ℝ (Cyl.partialEta ψ (z - x)) (g z)) ∂(Cyl.cellμ c) =
        (-d.1) * ∫ z, inner ℝ (Cyl.partialQ ψ (z - x)) (g z) ∂(Cyl.cellμ c)
        - d.2 * ∫ z, inner ℝ (Cyl.partialEta ψ (z - x)) (g z) ∂(Cyl.cellμ c) := by
      refine (integral_sub h1 h2).trans ?_
      simp only [integral_const_mul]
    simp_rw [e1]
    rw [hsplit]
    show (-d.1) * ∫ z, inner ℝ (Cyl.partialQ ψ (z - x)) (g z) ∂(Cyl.cellμ c)
        - d.2 * ∫ z, inner ℝ (Cyl.partialEta ψ (z - x)) (g z) ∂(Cyl.cellμ c)
        = -(d.1 * ∫ z, inner ℝ (Cyl.partialQ ψ (z - x)) (g z) ∂(Cyl.cellμ c))
        - d.2 * ∫ z, inner ℝ (Cyl.partialEta ψ (z - x)) (g z) ∂(Cyl.cellμ c)
    ring
  rw [hfin] at hH
  exact hH
