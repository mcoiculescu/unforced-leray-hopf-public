import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.Defs

/-!
# `PartIII-b:C/rep/5/1/2/4/1`: `wardYBinMass_of`, the bin kernel bound from the two reductions

Source `the November 2 reference manuscript` 5585-5593.  From `WardYPointDom`
(pointwise domination of `Y` by the gap-kernel and stream majorants, off the axis), `WardYMajBin`
and `WardYStreamMajBin` (chart bin `L²` bounds of the two majorants) we obtain `WardYBinMassAt`; the domination is used `ageμ`-a.e. (positive
chart ages map off the axis, `ϱ_chartY_pos`, and `{s ≤ 0}` is null, `ageμ_ae_fst_pos`).
`wardYBinMass_of` is the sequence-level statement.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- A chart point of positive age has its similarity point off the axis. -/
theorem ϱ_chartY_pos {R : ℝ} (hR : 0 < R) {p : Chart} (hp : 0 < p.1) :
    0 < ϱ (NearInst.chartY R p) := by
  have h0 : (NearInst.chartY R p) 0 = R / Real.sqrt p.1 := rfl
  have h1 : (NearInst.chartY R p) 1 = 0 := rfl
  rw [ϱ, h0, h1]
  apply Real.sqrt_pos.2
  have : 0 < R / Real.sqrt p.1 := div_pos hR (Real.sqrt_pos.2 hp)
  positivity

/-- The chart measure lives on positive ages: the axis `{s ≤ 0}` is `ageμ`-null. -/
theorem ageμ_ae_fst_pos (c a : ℝ) : ∀ᵐ p ∂(ageμ c a), 0 < p.1 := by
  rw [ae_iff]
  have h : {x : Chart | ¬ 0 < x.1} = Iic (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) := by
    ext x; simp
  have : SFinite (Cyl.avgμ c) := by unfold Cyl.avgμ; infer_instance
  have hI : Iic (0 : ℝ) ∩ Ioi 0 = ∅ := by
    ext x; simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_empty_iff_false, iff_false, not_and,
      not_lt]; exact id
  rw [h, ageμ, Measure.prod_prod, withDensity_apply _ measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic, hI]
  simp

theorem coefOf_enorm_le (R : ℝ) (F : ℝ → Space → Space) (p : Chart) :
    ‖coefOf R F p‖ₑ ≤ ENNReal.ofReal (Real.sqrt p.1)⁻¹ *
      ‖F (NearInst.chartTau R p) (NearInst.chartY R p)‖ₑ := by
  unfold coefOf
  rw [enorm_smul, Real.enorm_eq_ofReal_abs]
  have h0 : 0 ≤ (Real.sqrt p.1)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  rw [abs_of_nonneg h0]
  gcongr
  rw [← ofReal_norm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (merid_norm_le _)

theorem wardYBinMassAt_of {Pl : PlanarData} {K : ReturnConsts} {L : ReturnLevel} {μ : ℝ}
    {C1 C2 C3 : ℝ} {k1 k2 k3 : ℕ} (hμ : -(1 / 4) < μ) (hχ : IsYoungCutoff K.χy) (hδ : 0 < K.δ)
    (hν1 : L.ν ≤ 1)
    (h1 : WardYPointDom L.ν μ L.ε⁻¹ (cOf L.ν) K.δ K.χy C1 k1)
    (h2 : WardYMajBin L.ν L.ε (cOf L.ν) K.δ K.hbin (L.Scut K) C2 k2)
    (h3 : WardYStreamMajBin L.ν L.ε (cOf L.ν) K.δ K.hbin (L.Scut K) C3 k3) :
    WardYBinMassAt Pl K L μ (2 * |C1| * (|C2| + |C3|)) (k1 + (k2 + k3)) := by
  intro hδ' j g hg hg0
  have hν := L.ν_pos
  have hε := L.ε_pos
  have hc : 0 < cOf L.ν := by unfold cOf; positivity
  have hRpos : 0 < L.ε⁻¹ := inv_pos.2 hε
  have hpt := h1 hν hRpos hc hμ hχ hδ' hδ g hg hg0
  have hmb := h2 hν hε hc hδ hδ' rfl j g hg hg0
  obtain ⟨hsm, hsb⟩ := h3 hν hε hc hδ hδ' rfl j g hg hg0
  set θ := Real.exp (-(K.δ / 2))
  set A : ℝ≥0∞ := ENNReal.ofReal (C1 * L.ν⁻¹ ^ k1)
  set M : Chart → ℝ≥0∞ := wardYChartMaj L.ε⁻¹ (cOf L.ν) θ g
  set Ms : Chart → ℝ≥0∞ := wardYStreamChartMaj L.ε⁻¹ (cOf L.ν) θ g
  set μb := (ageμ (cOf L.ν) (-3 / 2)).restrict (binSet (L.Scut K) K.hbin j)
  set X : ℝ≥0∞ := ∫⁻ p, M p ^ (2 : ℝ) ∂μb
  set Y : ℝ≥0∞ := ∫⁻ p, Ms p ^ (2 : ℝ) ∂μb
  set N := ageMass (cOf L.ν) (Real.exp (K.δ - K.hbin) * binUpper (L.Scut K) K.hbin j) g
  set E : ℝ := L.ε ^ (3 / 2 : ℝ) * binUpper (L.Scut K) K.hbin j ^ (5 / 4 : ℝ)
  have hA : A ≠ ⊤ := ENNReal.ofReal_ne_top
  have hptw : ∀ p : Chart, 0 < p.1 →
      ‖coefOf L.ε⁻¹ (wardY L.ν μ L.ε⁻¹ (cOf L.ν) K.χy g) p‖ₑ ≤ A * (M p + Ms p) := by
    intro p hp
    refine (coefOf_enorm_le _ _ p).trans ?_
    calc ENNReal.ofReal (Real.sqrt p.1)⁻¹ *
          ‖wardY L.ν μ L.ε⁻¹ (cOf L.ν) K.χy g (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p)‖ₑ
        ≤ ENNReal.ofReal (Real.sqrt p.1)⁻¹ * (A * (wardYKerMaj L.ε⁻¹ (cOf L.ν) θ g
            (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p) +
            wardYStreamMaj L.ε⁻¹ (cOf L.ν) θ g
            (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p))) :=
          mul_le_mul' le_rfl (hpt _ _ (ϱ_chartY_pos hRpos hp))
      _ = A * (M p + Ms p) := by
          simp only [M, Ms, wardYChartMaj, wardYStreamChartMaj]; ring
  -- the squared bin integral
  have hI : ∫⁻ p, ‖coefOf L.ε⁻¹ (wardY L.ν μ L.ε⁻¹ (cOf L.ν) K.χy g) p‖ₑ ^ (2 : ℝ) ∂μb ≤
      (A ^ (2 : ℝ) * 2) * (X + Y) := by
    have hsm2 : AEMeasurable (fun p => Ms p ^ (2 : ℝ)) μb := hsm.pow_const _
    calc ∫⁻ p, ‖coefOf L.ε⁻¹ (wardY L.ν μ L.ε⁻¹ (cOf L.ν) K.χy g) p‖ₑ ^ (2 : ℝ) ∂μb
        ≤ ∫⁻ p, (A ^ (2 : ℝ) * 2) * (M p ^ (2 : ℝ) + Ms p ^ (2 : ℝ)) ∂μb := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_of_ae (ageμ_ae_fst_pos (cOf L.ν) (-3 / 2))] with p hp
          calc ‖coefOf L.ε⁻¹ (wardY L.ν μ L.ε⁻¹ (cOf L.ν) K.χy g) p‖ₑ ^ (2 : ℝ)
              ≤ (A * (M p + Ms p)) ^ (2 : ℝ) := ENNReal.rpow_le_rpow (hptw p hp) (by norm_num)
            _ = A ^ (2 : ℝ) * (M p + Ms p) ^ (2 : ℝ) := ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
            _ ≤ A ^ (2 : ℝ) * (2 ^ ((2 : ℝ) - 1) * (M p ^ (2 : ℝ) + Ms p ^ (2 : ℝ))) :=
                mul_le_mul' le_rfl (ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ (by norm_num))
            _ = (A ^ (2 : ℝ) * 2) * (M p ^ (2 : ℝ) + Ms p ^ (2 : ℝ)) := by
                norm_num; ring
      _ = (A ^ (2 : ℝ) * 2) * (X + Y) := by
          rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top
            (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hA) (by norm_num))]
          rw [lintegral_add_right' _ hsm2]
  have hmain : ageNormBin (cOf L.ν) (L.Scut K) K.hbin j
      (coefOf L.ε⁻¹ (wardY L.ν μ L.ε⁻¹ (cOf L.ν) K.χy g)) ≤
      A * 2 * (X ^ (1 / 2 : ℝ) + Y ^ (1 / 2 : ℝ)) := by
    unfold ageNormBin
    calc _ ≤ ((A ^ (2 : ℝ) * 2) * (X + Y)) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hI (by norm_num)
      _ = A * (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) * (X + Y) ^ (1 / 2 : ℝ) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
            ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
          norm_num
      _ ≤ A * 2 * (X ^ (1 / 2 : ℝ) + Y ^ (1 / 2 : ℝ)) := by
          gcongr
          · calc (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) ≤ (2 : ℝ≥0∞) ^ (1 : ℝ) :=
                  ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
              _ = 2 := ENNReal.rpow_one _
          · exact ENNReal.rpow_add_le_add_rpow _ _ (by norm_num) (by norm_num)
  refine hmain.trans ?_
  -- constants
  have ha1 : 1 ≤ L.ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hE : 0 ≤ E := by
    have : 0 ≤ binUpper (L.Scut K) K.hbin j ^ (5 / 4 : ℝ) := by
      unfold binUpper ReturnLevel.Scut
      positivity
    exact mul_nonneg (Real.rpow_nonneg hε.le _) this
  have hpk : ∀ m : ℕ, m ≤ k2 + k3 → L.ν⁻¹ ^ m ≤ L.ν⁻¹ ^ (k2 + k3) := fun m hm =>
    pow_le_pow_right₀ ha1 hm
  have hB : ∀ (C' : ℝ) (m : ℕ), m ≤ k2 + k3 →
      ENNReal.ofReal (C' * L.ν⁻¹ ^ m * L.ε ^ (3 / 2 : ℝ) *
        binUpper (L.Scut K) K.hbin j ^ (5 / 4 : ℝ)) ≤
      ENNReal.ofReal (|C'| * L.ν⁻¹ ^ (k2 + k3) * E) := by
    intro C' m hm
    refine ENNReal.ofReal_le_ofReal ?_
    have h0 : 0 ≤ L.ν⁻¹ ^ m := by positivity
    have := mul_le_mul (le_abs_self C') (hpk m hm) h0 (abs_nonneg _)
    simp only [E, ← mul_assoc] at *
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this
      (Real.rpow_nonneg hε.le _)) (by unfold binUpper ReturnLevel.Scut; positivity)
  have hX : X ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (|C2| * L.ν⁻¹ ^ (k2 + k3) * E) * N :=
    hmb.trans (mul_le_mul' (hB C2 k2 (Nat.le_add_right _ _)) le_rfl)
  have hY : Y ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (|C3| * L.ν⁻¹ ^ (k2 + k3) * E) * N :=
    hsb.trans (mul_le_mul' (hB C3 k3 (Nat.le_add_left _ _)) le_rfl)
  have hAle : A ≤ ENNReal.ofReal (|C1| * L.ν⁻¹ ^ k1) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  calc A * 2 * (X ^ (1 / 2 : ℝ) + Y ^ (1 / 2 : ℝ))
      ≤ ENNReal.ofReal (|C1| * L.ν⁻¹ ^ k1) * 2 *
          (ENNReal.ofReal (|C2| * L.ν⁻¹ ^ (k2 + k3) * E) * N +
            ENNReal.ofReal (|C3| * L.ν⁻¹ ^ (k2 + k3) * E) * N) := by
        gcongr
    _ = ENNReal.ofReal (2 * |C1| * (|C2| + |C3|) * L.ν⁻¹ ^ (k1 + (k2 + k3)) * L.ε ^ (3 / 2 : ℝ) *
          binUpper (L.Scut K) K.hbin j ^ (5 / 4 : ℝ)) * N := by
        have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by norm_num
        have hp1 : 0 ≤ |C1| * L.ν⁻¹ ^ k1 := by positivity
        have hp2 : 0 ≤ |C2| * L.ν⁻¹ ^ (k2 + k3) * E := by positivity
        have hp3 : 0 ≤ |C3| * L.ν⁻¹ ^ (k2 + k3) * E := by positivity
        rw [← add_mul, ← ENNReal.ofReal_add hp2 hp3, h2, ← ENNReal.ofReal_mul hp1, ← mul_assoc,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        simp only [E]
        rw [pow_add]
        ring

/-- **The bin kernel bound for `Y`** (source 5585-5593), from the pointwise domination, the chart
bin bounds of the two majorants, and the window `μ > -1/4`. -/
theorem wardYBinMass_of (D : SeqData) {dm dp : ℝ}
    (hmu : D.RepairStanding dm dp → ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, -(1 / 4) < D.mu n z)
    (h1 : D.WardYPointDomSeq dm dp) (h2 : D.WardYMajBinSeq dm dp)
    (h3 : D.WardYStreamMajBinSeq dm dp) :
    D.WardYBinMassSeq dm dp := by
  intro hst
  obtain ⟨C1, k1, e1⟩ := h1 hst
  obtain ⟨C2, k2, e2⟩ := h2 hst
  obtain ⟨C3, k3, e3⟩ := h3 hst
  refine ⟨2 * |C1| * (|C2| + |C3|), k1 + (k2 + k3), ?_⟩
  have hχ : IsYoungCutoff D.K.χy :=
    ⟨hst.chiY.smooth, hst.chiY.one, hst.chiY.zero, hst.chiY.range⟩
  have hle := retNu_retEps_eventually_le_one (Pl := D.Pl) (σ₀ := D.σ₀) hst.omega_ne
    hst.gamma_pos D.coeff_ne
  filter_upwards [e1, e2, e3, hmu hst, hle] with n a b b' c hn z hz
  exact wardYBinMassAt_of (c z hz) hχ hst.δ_pos hn.1 (a z hz) b b'

end UnforcedLeray.Short.PartIIIb.Concrete

end
