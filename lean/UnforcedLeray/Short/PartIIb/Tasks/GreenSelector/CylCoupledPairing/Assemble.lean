import UnforcedLeray.Short.PartIIb.Tasks.GreenSelector.CylCoupledPairing.Core

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Short.IIb.CCP

open UnforcedLeray

/-- Generic assembly of a continuous linear functional from an a.e.-linear family of integrands. -/
theorem clm_of_bound {c m : ℝ} (F : B0579.X c m → B0579.Plane → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hmeas : ∀ w, AEStronglyMeasurable (F w) (volume.restrict (B0579.cell c)))
    (hb : ∀ w, ∫⁻ x in B0579.cell c, ‖F w x‖ₑ ≤ ENNReal.ofReal M * ‖w‖ₑ)
    (hadd : ∀ w1 w2, F (w1 + w2) =ᵐ[volume.restrict (B0579.cell c)]
      fun x => F w1 x + F w2 x)
    (hsm : ∀ (a : ℝ) w, F (a • w) =ᵐ[volume.restrict (B0579.cell c)] fun x => a * F w x) :
    ∃ T : B0579.X c m →L[ℝ] ℝ, ‖T‖ ≤ M ∧ ∀ w, IntegrableOn (F w) (B0579.cell c) volume ∧
      T w = ∫ x in B0579.cell c, F w x := by
  have hint : ∀ w, IntegrableOn (F w) (B0579.cell c) volume := fun w =>
    ⟨hmeas w, lt_of_le_of_lt (hb w) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top enorm_lt_top)⟩
  let f : B0579.X c m →ₗ[ℝ] ℝ :=
    { toFun := fun w => ∫ x in B0579.cell c, F w x
      map_add' := fun w1 w2 => by
        rw [integral_congr_ae (hadd w1 w2), integral_add (hint w1) (hint w2)]
      map_smul' := fun a w => by
        rw [integral_congr_ae (hsm a w), integral_const_mul]
        rfl }
  have hbd : ∀ w, ‖f w‖ ≤ M * ‖w‖ := by
    intro w
    have h1 : ‖f w‖ ≤ ∫ x in B0579.cell c, ‖F w x‖ := norm_integral_le_integral_norm _
    have h2 : ∫ x in B0579.cell c, ‖F w x‖ = (∫⁻ x in B0579.cell c, ‖F w x‖ₑ).toReal :=
      integral_norm_eq_lintegral_enorm (hmeas w)
    have h3 : (∫⁻ x in B0579.cell c, ‖F w x‖ₑ).toReal ≤ (ENNReal.ofReal M * ‖w‖ₑ).toReal :=
      ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top enorm_ne_top) (hb w)
    have h4 : (ENNReal.ofReal M * ‖w‖ₑ).toReal = M * ‖w‖ := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM]
      rfl
    linarith
  refine ⟨f.mkContinuous M hbd, LinearMap.mkContinuous_norm_le f hM hbd, fun w => ⟨hint w, rfl⟩⟩

theorem coe_add_ae {c m : ℝ} (w1 w2 : B0579.X c m) :
    ⇑(w1 + w2) =ᵐ[volume.restrict (B0579.cell c)] fun x => w1 x + w2 x :=
  (B0579.ac_cellMeasure c m).ae_le (Lp.coeFn_add w1 w2)

theorem coe_smul_ae {c m : ℝ} (a : ℝ) (w : B0579.X c m) :
    ⇑(a • w) =ᵐ[volume.restrict (B0579.cell c)] fun x => a * w x :=
  (B0579.ac_cellMeasure c m).ae_le (by
    filter_upwards [Lp.coeFn_smul a w] with x hx
    rw [hx]; rfl)

theorem K_add_ae {c : ℝ} (hc1 : 1 ≤ c) {m : ℝ} (hm : 1 / 2 < m) (w1 w2 : B0579.X c m) :
    ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
      Cyl.K c ⇑(w1 + w2) x = Cyl.K c ⇑w1 x + Cyl.K c ⇑w2 x := by
  obtain ⟨C1, hC1, hC1w⟩ := exists_L1_const c m hm
  obtain ⟨g1, hg1m, hg1i, -, hg1e, -, -⟩ := exists_rep hm C1 hC1w w1
  obtain ⟨g2, hg2m, hg2i, -, hg2e, -, -⟩ := exists_rep hm C1 hC1w w2
  have hge : ⇑(w1 + w2) =ᵐ[volume.restrict (B0579.cell c)] fun x => g1 x + g2 x := by
    filter_upwards [coe_add_ae w1 w2, hg1e, hg2e] with x h h1 h2
    rw [h, h1, h2]
  have h1 := cyl_K_ae_split_and_integrable hc1 hg1m hg1i
  have h2 := cyl_K_ae_split_and_integrable hc1 hg2m hg2i
  rw [ae_restrict_iff' (B0579.measurableSet_cell c)]
  filter_upwards [h1, h2] with x hx1 hx2 hxc
  have hxc' : x ∈ Cyl.cell c := by rwa [← b0579_cell_eq_cyl_cell]
  have i1 := (hx1 hxc').2
  have i2 := (hx2 hxc').2
  rw [K_eq_rep (w1 + w2) (fun x => g1 x + g2 x) hge x, K_eq_rep w1 g1 hg1e x,
    K_eq_rep w2 g2 hg2e x]
  unfold Cyl.K
  rw [← integral_add i1 i2]
  congr 1
  funext y
  simp [add_smul]

theorem K_smul {c : ℝ} {m : ℝ} (hm : 1 / 2 < m) (a : ℝ) (w : B0579.X c m) (x : B0579.Plane) :
    Cyl.K c ⇑(a • w) x = a • Cyl.K c ⇑w x := by
  obtain ⟨C1, hC1, hC1w⟩ := exists_L1_const c m hm
  obtain ⟨g, hgm, hgi, -, hge, -, -⟩ := exists_rep hm C1 hC1w w
  have hge' : ⇑(a • w) =ᵐ[volume.restrict (B0579.cell c)] fun x => a * g x := by
    filter_upwards [coe_smul_ae a w, hge] with x h h1
    rw [h, h1]
  rw [K_eq_rep (a • w) (fun x => a * g x) hge' x, K_eq_rep w g hge x]
  unfold Cyl.K
  rw [← integral_smul]
  congr 1
  funext y
  simp [mul_smul]

theorem K_comp_aesm {c : ℝ} {m : ℝ} (hm : 1 / 2 < m) (w : B0579.X c m) (i : Fin 2) :
    AEStronglyMeasurable (fun x => Cyl.K c ⇑w x i) volume := by
  obtain ⟨C1, hC1, hC1w⟩ := exists_L1_const c m hm
  obtain ⟨g, hgm, hgi, -, hge, -, -⟩ := exists_rep hm C1 hC1w w
  have : (fun x => Cyl.K c ⇑w x i) = fun x => Cyl.K c g x i := by
    funext x; rw [K_eq_rep w g hge x]
  rw [this]
  exact (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp_aestronglyMeasurable
    (aestronglyMeasurable_cyl_K c hgm)

theorem pd_meas (φ : B0579.Plane → ℝ) (j : Fin 2) : Measurable (B0579.pd j φ) :=
  measurable_fderiv_apply_const ℝ φ (B0579.dir j)

theorem main_bound {ν c : ℝ} (hc1 : 1 ≤ c) {m : ℝ} (hm : 1 / 2 < m) (tr : B0140.TrainSol ν c)
    (H : ℝ) (hH : 0 ≤ H) {φ : B0579.Plane → ℝ} (hφ : B0579.IsCylTest c φ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ r ∈ Icc 0 H, ∀ w : B0579.X c m,
      AEStronglyMeasurable (cylCoupledIntegrand tr ⇑w r φ) (volume.restrict (B0579.cell c)) ∧
      ∫⁻ x in B0579.cell c, ‖cylCoupledIntegrand tr ⇑w r φ x‖ₑ ≤ ENNReal.ofReal M * ‖w‖ₑ := by
  obtain ⟨R, B, hR, hB, hRB⟩ := test_bounds hφ
  obtain ⟨C, hC, hCb⟩ := train_strip_bounds tr H R hH
  obtain ⟨C1, hC1, hC1w⟩ := exists_L1_const c m hm
  obtain ⟨CK, hCK, hKb⟩ := K_pair_bound hc1 hm R (B * C) hR
  set A : ℝ := |ν| * (2 * B) + (C * B + C * B) with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨A * C1 + CK + CK, by positivity, fun r hr w => ?_⟩
  have hr0 : 0 ≤ r := hr.1
  set a : B0579.Plane → ℝ := fun x => ν * (B0579.pd 0 (B0579.pd 0 φ) x + B0579.pd 1 (B0579.pd 1 φ) x) +
        (tr.v r x 0 * B0579.pd 0 φ x + tr.v r x 1 * B0579.pd 1 φ x) with ha
  set ψ0 : B0579.Plane → ℝ := fun x => φ x * B0579.pd 0 (B0238.Ec tr r) x with hψ0
  set ψ1 : B0579.Plane → ℝ := fun x => φ x * B0579.pd 1 (B0238.Ec tr r) x with hψ1
  have hint : ∀ x, cylCoupledIntegrand tr ⇑w r φ x =
      w x * a x - Cyl.K c ⇑w x 0 * ψ0 x - Cyl.K c ⇑w x 1 * ψ1 x := fun x => integrand_eq tr _ r φ x
  have hv0 := continuous_train_slice tr hr0 0
  have hv1 := continuous_train_slice tr hr0 1
  have ham : Measurable a := by
    have p0 := pd_meas φ 0
    have p1 := pd_meas φ 1
    have h00 := pd_meas (B0579.pd 0 φ) 0
    have h11 := pd_meas (B0579.pd 1 φ) 1
    exact ((h00.add h11).const_mul ν).add ((hv0.measurable.mul p0).add (hv1.measurable.mul p1))
  have hφm : Measurable φ := hφ.continuous.measurable
  have hψ0m : Measurable ψ0 := hφm.mul (measurable_pd_Ec tr r 0)
  have hψ1m : Measurable ψ1 := hφm.mul (measurable_pd_Ec tr r 1)
  have hwm : AEStronglyMeasurable (⇑w) (volume.restrict (B0579.cell c)) :=
    (Lp.aestronglyMeasurable w).mono_ac (B0579.ac_cellMeasure c m)
  have hK0 := (K_comp_aesm hm w 0).restrict (s := B0579.cell c)
  have hK1 := (K_comp_aesm hm w 1).restrict (s := B0579.cell c)
  have t1m : AEStronglyMeasurable (fun x => w x * a x) (volume.restrict (B0579.cell c)) :=
    hwm.mul ham.aestronglyMeasurable
  have t2m : AEStronglyMeasurable (fun x => Cyl.K c ⇑w x 0 * ψ0 x) (volume.restrict (B0579.cell c)) :=
    hK0.mul hψ0m.aestronglyMeasurable
  have t3m : AEStronglyMeasurable (fun x => Cyl.K c ⇑w x 1 * ψ1 x) (volume.restrict (B0579.cell c)) :=
    hK1.mul hψ1m.aestronglyMeasurable
  have hFm : AEStronglyMeasurable (cylCoupledIntegrand tr ⇑w r φ) (volume.restrict (B0579.cell c)) := by
    have : cylCoupledIntegrand tr ⇑w r φ = fun x => w x * a x - Cyl.K c ⇑w x 0 * ψ0 x - Cyl.K c ⇑w x 1 * ψ1 x :=
      funext hint
    rw [this]
    exact (t1m.sub t2m).sub t3m
  refine ⟨hFm, ?_⟩
  -- the bounds
  have hψb : ∀ ψ : B0579.Plane → ℝ, ∀ j : Fin 2, (ψ = fun x => φ x * B0579.pd j (B0238.Ec tr r) x) →
      (∀ x, |x.1| ≤ c / 2 → |ψ x| ≤ B * C) ∧ (∀ x, R < |x.2| → ψ x = 0) := by
    intro ψ j hψ
    subst hψ
    refine ⟨fun x hx => ?_, fun x hx => by simp [(hRB x).2 hx |>.1]⟩
    by_cases h2 : |x.2| ≤ R
    · have h1 := ((hRB x).1 hx).1
      have h3 := hCb r hr x hx h2
      have h4 : |B0579.pd j (B0238.Ec tr r) x| ≤ C := by
        fin_cases j
        · exact h3.2.2.1
        · exact h3.2.2.2
      rw [abs_mul]
      exact mul_le_mul h1 h4 (abs_nonneg _) hB
    · have := ((hRB x).2 (not_le.mp h2)).1
      simp [this]; positivity
  have hab : ∀ x ∈ B0579.cell c, |a x| ≤ A := by
    intro x hx
    have hx1 : |x.1| ≤ c / 2 := abs_le.mpr ⟨hx.1.1, hx.1.2.le⟩
    by_cases h2 : |x.2| ≤ R
    · have h1 := (hRB x).1 hx1
      have h3 := hCb r hr x hx1 h2
      simp only [ha]
      calc |ν * (B0579.pd 0 (B0579.pd 0 φ) x + B0579.pd 1 (B0579.pd 1 φ) x) +
          (tr.v r x 0 * B0579.pd 0 φ x + tr.v r x 1 * B0579.pd 1 φ x)|
          ≤ |ν * (B0579.pd 0 (B0579.pd 0 φ) x + B0579.pd 1 (B0579.pd 1 φ) x)| +
            |tr.v r x 0 * B0579.pd 0 φ x + tr.v r x 1 * B0579.pd 1 φ x| := abs_add_le _ _
        _ ≤ |ν| * (2 * B) + (C * B + C * B) := by
          gcongr
          · rw [abs_mul]; gcongr; exact h1.2.2.2
          · refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_mul]
            gcongr
            · exact h3.1
            · exact h1.2.1
            · exact h3.2.1
            · exact h1.2.2.1
    · have h5 := (hRB x).2 (not_le.mp h2)
      simp only [ha, h5.2.1, h5.2.2.1, h5.2.2.2]
      simp [hA0]
  obtain ⟨hψ0a, hψ0b⟩ := hψb ψ0 0 rfl
  obtain ⟨hψ1a, hψ1b⟩ := hψb ψ1 1 rfl
  have e1 : ∫⁻ x in B0579.cell c, ‖w x * a x‖ₑ ≤ ENNReal.ofReal (A * C1) * ‖w‖ₑ := by
    calc ∫⁻ x in B0579.cell c, ‖w x * a x‖ₑ
        ≤ ∫⁻ x in B0579.cell c, ENNReal.ofReal A * ‖w x‖ₑ := by
          refine setLIntegral_mono' (B0579.measurableSet_cell c) (fun x hx => ?_)
          rw [enorm_mul, mul_comm]
          gcongr
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (by simpa using hab x hx)
      _ = ENNReal.ofReal A * eLpNorm (⇑w) 1 (volume.restrict (B0579.cell c)) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, eLpNorm_one_eq_lintegral_enorm]
      _ ≤ ENNReal.ofReal A * (ENNReal.ofReal C1 * ‖w‖ₑ) := by gcongr; exact hC1w w
      _ = ENNReal.ofReal (A * C1) * ‖w‖ₑ := by
          rw [ENNReal.ofReal_mul hA0, mul_assoc]
  have e2 := hKb ψ0 hψ0a hψ0b w 0
  have e3 := hKb ψ1 hψ1a hψ1b w 1
  have hpt : ∀ x, ‖cylCoupledIntegrand tr ⇑w r φ x‖ₑ ≤
      (‖w x * a x‖ₑ + ‖Cyl.K c ⇑w x 0 * ψ0 x‖ₑ) + ‖Cyl.K c ⇑w x 1 * ψ1 x‖ₑ := by
    intro x
    rw [hint x]
    exact enorm_sub_le.trans (add_le_add enorm_sub_le le_rfl)
  calc ∫⁻ x in B0579.cell c, ‖cylCoupledIntegrand tr ⇑w r φ x‖ₑ
      ≤ ∫⁻ x in B0579.cell c, ((‖w x * a x‖ₑ + ‖Cyl.K c ⇑w x 0 * ψ0 x‖ₑ) +
          ‖Cyl.K c ⇑w x 1 * ψ1 x‖ₑ) := lintegral_mono hpt
    _ = (∫⁻ x in B0579.cell c, ‖w x * a x‖ₑ) + (∫⁻ x in B0579.cell c, ‖Cyl.K c ⇑w x 0 * ψ0 x‖ₑ) +
          (∫⁻ x in B0579.cell c, ‖Cyl.K c ⇑w x 1 * ψ1 x‖ₑ) := by
        rw [lintegral_add_left' (f := fun x => ‖w x * a x‖ₑ + ‖Cyl.K c ⇑w x 0 * ψ0 x‖ₑ)
            (t1m.enorm.add t2m.enorm),
          lintegral_add_left' (f := fun x => ‖w x * a x‖ₑ) t1m.enorm]
    _ ≤ ENNReal.ofReal (A * C1) * ‖w‖ₑ + ENNReal.ofReal CK * ‖w‖ₑ + ENNReal.ofReal CK * ‖w‖ₑ := by
        gcongr
    _ = ENNReal.ofReal (A * C1 + CK + CK) * ‖w‖ₑ := by
        rw [ENNReal.ofReal_add (by positivity) hCK, ENNReal.ofReal_add (by positivity) hCK]
        ring

end UnforcedLeray.Short.IIb.CCP
