import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_3_2_2.AntiSymm
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.MollLimit.AeGood

/-!
# Part III-a, `PartIII-a:T18/3/1/3/2/2/org`: joint measurability and local `L²` bounds

Source of record: `the November 2 reference manuscript` lines 3427-3440, 3541-3552.
`lmDivJMeasRep`, `lmUDerL2Loc`, `lmIpWeightedInt`, `lmUkL2Loc`, `lmYtL2Loc` (statements in
`Props.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **`s ↦ Z(s)` has a jointly measurable version.** -/
theorem lmDivJMeasRep : LMDivJMeasRep := by
  intro c _hc J hJ k T hT
  let D : ℕ → Fin 2 → Fin 2 → ℝ × (ℝ × ℝ) → ℂ := fun n j i p =>
    ((1 / ((n : ℝ) + 1))⁻¹ : ℝ) •
      (J k (fun y i' => T (p.1, y) i' j) (p.2 + (1 / ((n : ℝ) + 1)) • B0579.dir j) i -
        J k (fun y i' => T (p.1, y) i' j) p.2 i)
  have hDm : ∀ n j i, Measurable (D n j i) := by
    intro n j i
    have hg := hJ.measurable k (fun p i' => T p i' j) (fun i' => hT i' j) i
    have hsh : Measurable fun p : ℝ × (ℝ × ℝ) =>
        ((p.1, p.2 + (1 / ((n : ℝ) + 1)) • B0579.dir j) : ℝ × (ℝ × ℝ)) :=
      measurable_fst.prodMk (measurable_snd.add_const _)
    exact Measurable.const_smul ((hg.comp hsh).sub hg) (((1 / ((n : ℝ) + 1))⁻¹ : ℝ))
  refine ⟨fun p i => ∑ j : Fin 2, limUnder atTop (fun n => D n j i p), fun i => ?_,
    fun s hs x i => ?_⟩
  · refine Finset.measurable_sum _ fun j _ => ?_
    exact (StronglyMeasurable.limUnder fun n => (hDm n j i).stronglyMeasurable).measurable
  · show ∑ j : Fin 2, limUnder atTop (fun n => D n j i (s, x)) =
      ∑ j : Fin 2, LMPd j (fun y => J k (fun y' i' => T (s, y') i' j) y i) x
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Tendsto.limUnder_eq ?_
    have hsm := (hJ.smooth k _ (hs j) i).differentiable (by simp) x
    rw [lmPd_eq_fderiv hsm]
    have hline := hsm.hasFDerivAt.hasLineDerivAt (B0579.dir j)
    have hsl := HasDerivAt.tendsto_slope_zero hline
    have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[≠] (0 : ℝ)) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall fun n => by
          have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
          exact this.ne'⟩
    have := hsl.comp ht
    refine this.congr fun n => ?_
    simp [D, Function.comp]

/-- `vnorm2 z ^ 2 = ∑ᵢ ‖zᵢ‖²`. -/
theorem lm_vnorm2_sq (z : Fin 2 → ℂ) : vnorm2 z ^ 2 = ∑ i : Fin 2, ‖z i‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)

/-- `tnorm2 T ^ 2 = ∑ᵢⱼ ‖Tᵢⱼ‖²`. -/
theorem lm_tnorm2_sq (T : Fin 2 → Fin 2 → ℂ) : tnorm2 T ^ 2 = ∑ i : Fin 2, ∑ j : Fin 2, ‖T i j‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)

theorem lm_norm_add_sq_le (a b : ℂ) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h1 : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
  have h2 := mul_self_le_mul_self (norm_nonneg _) h1
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

/-- **`u' = -(μ/s) u + Y ∈ L²_loc((0,∞); L²(cell))` when `u, Y` are.** -/
theorem lmUDerL2Loc : LMUDerL2Loc := by
  intro c μ u Y hu hY s₁ s₂ h1 _h2 hUL hYL
  have hmU : Measurable fun p : ℝ × (ℝ × ℝ) =>
      ENNReal.ofReal (vnorm2 (fun i => u p.1 p.2 i) ^ 2) :=
    ENNReal.measurable_ofReal.comp ((aeg_measurable_vnorm2 hu).pow_const 2)
  have hmY : Measurable fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (vnorm2 (fun i => Y p i) ^ 2) :=
    ENNReal.measurable_ofReal.comp ((aeg_measurable_vnorm2 hY).pow_const 2)
  set A : ℝ := 2 * (‖μ‖ / s₁) ^ 2 with hA
  have hA0 : 0 ≤ A := by positivity
  have hS : MeasurableSet (Icc s₁ s₂ ×ˢ B0579.cell c) :=
    measurableSet_Icc.prod (B0579.measurableSet_cell c)
  have hpt : ∀ p ∈ Icc s₁ s₂ ×ˢ B0579.cell c,
      ENNReal.ofReal (vnorm2 (fun i => lmUDer μ u Y p.1 p.2 i) ^ 2) ≤
        ENNReal.ofReal A * ENNReal.ofReal (vnorm2 (fun i => u p.1 p.2 i) ^ 2) +
          ENNReal.ofReal 2 * ENNReal.ofReal (vnorm2 (fun i => Y p i) ^ 2) := by
    rintro ⟨s, x⟩ ⟨hs, -⟩
    have hs1 : s₁ ≤ s := hs.1
    have hs0 : 0 < s := lt_of_lt_of_le h1 hs1
    rw [← ENNReal.ofReal_mul hA0, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [lm_vnorm2_sq, Fin.sum_univ_two, lmUDer]
    have hq : ‖μ / (s : ℂ)‖ ≤ ‖μ‖ / s₁ := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hs0.le]
      exact div_le_div_of_nonneg_left (norm_nonneg _) h1 hs1
    have hq2 : ‖μ / (s : ℂ)‖ ^ 2 ≤ (‖μ‖ / s₁) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hq 2
    have hterm : ∀ i : Fin 2, ‖-(μ / (s : ℂ)) * u s x i + Y (s, x) i‖ ^ 2 ≤
        A * ‖u s x i‖ ^ 2 + 2 * ‖Y (s, x) i‖ ^ 2 := fun i => by
      refine (lm_norm_add_sq_le _ _).trans ?_
      rw [norm_mul, norm_neg, mul_pow, hA]
      nlinarith [sq_nonneg ‖u s x i‖]
    have h0 := hterm 0
    have h1' := hterm 1
    linarith
  have hle : ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
      ENNReal.ofReal (vnorm2 (fun i => lmUDer μ u Y p.1 p.2 i) ^ 2) ≤
      ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
        (ENNReal.ofReal A * ENNReal.ofReal (vnorm2 (fun i => u p.1 p.2 i) ^ 2) +
          ENNReal.ofReal 2 * ENNReal.ofReal (vnorm2 (fun i => Y p i) ^ 2)) :=
    setLIntegral_mono' hS hpt
  refine lt_of_le_of_lt hle ?_
  rw [lintegral_add_left (hmU.const_mul _), lintegral_const_mul _ hmU, lintegral_const_mul _ hmY]
  exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hUL,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hYL⟩

/-- **`s ↦ w(s) ⟨χ, u(s)⟩` is integrable.** -/
theorem lmIpWeightedInt : LMIpWeightedInt := by
  intro c χ u w hχ hum huL hw hcs hts
  obtain ⟨a, b, ha, hab, hsub⟩ : ∃ a b : ℝ, 0 < a ∧ a < b ∧ tsupport w ⊆ Ioo a b := by
    rcases (tsupport w).eq_empty_or_nonempty with he | hne
    · exact ⟨1, 2, one_pos, one_lt_two, by simp [he]⟩
    · obtain ⟨x0, hx0, hmin⟩ := hcs.exists_isMinOn hne continuous_id.continuousOn
      obtain ⟨y0, hy0, hmax⟩ := hcs.exists_isMaxOn hne continuous_id.continuousOn
      have hx0pos : 0 < x0 := hts hx0
      refine ⟨x0 / 2, y0 + 1, by positivity, ?_, fun x hx => ⟨?_, ?_⟩⟩
      · have := hmax hx0; simp at this; linarith
      · have := hmin hx; simp at this; linarith
      · have := hmax hx; simp at this; linarith
  set νc : Measure (ℝ × ℝ) := volume.restrict (B0579.cell c) with hνc
  have hfin : IsFiniteMeasure (volume.restrict (Icc a b)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact isCompact_Icc.measure_lt_top⟩
  have hg1 : Integrable (fun p : ℝ × (ℝ × ℝ) => ∑ i : Fin 2, ‖χ p.2 i‖ ^ 2)
      ((volume.restrict (Icc a b)).prod νc) :=
    (lm_vec_sq_integrable hχ).comp_snd (volume.restrict (Icc a b))
  have hg2 : Integrable (fun p : ℝ × (ℝ × ℝ) => vnorm2 (fun i => u p.1 p.2 i) ^ 2)
      ((volume.restrict (Icc a b)).prod νc) := by
    have hm : Measurable fun p : ℝ × (ℝ × ℝ) => vnorm2 (fun i => u p.1 p.2 i) ^ 2 :=
      (aeg_measurable_vnorm2 hum).pow_const 2
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun p => sq_nonneg _), hνc,
      Measure.prod_restrict]
    exact huL a b ha hab
  have hmeas : AEStronglyMeasurable (fun p : ℝ × (ℝ × ℝ) =>
      ∑ i : Fin 2, starRingEnd ℂ (χ p.2 i) * u p.1 p.2 i)
      ((volume.restrict (Icc a b)).prod νc) := by
    refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
    exact (Complex.continuous_conj.comp_aestronglyMeasurable (hχ i).1.comp_snd).mul
      (hum i).aestronglyMeasurable
  have hF : Integrable (fun p : ℝ × (ℝ × ℝ) => ∑ i : Fin 2, starRingEnd ℂ (χ p.2 i) * u p.1 p.2 i)
      ((volume.restrict (Icc a b)).prod νc) := by
    refine (hg1.add hg2).mono' hmeas (ae_of_all _ fun p => ?_)
    have h1 : ‖∑ i : Fin 2, starRingEnd ℂ (χ p.2 i) * u p.1 p.2 i‖ ≤
        ∑ i : Fin 2, ‖χ p.2 i‖ * ‖u p.1 p.2 i‖ := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [norm_mul, RCLike.norm_conj]
    refine h1.trans ?_
    simp only [Pi.add_apply, lm_vnorm2_sq, Fin.sum_univ_two]
    nlinarith [sq_nonneg (‖χ p.2 0‖ - ‖u p.1 p.2 0‖), sq_nonneg (‖χ p.2 1‖ - ‖u p.1 p.2 1‖),
      sq_nonneg (‖χ p.2 0‖), sq_nonneg (‖χ p.2 1‖), sq_nonneg (‖u p.1 p.2 0‖),
      sq_nonneg (‖u p.1 p.2 1‖)]
  have hI : Integrable (fun s => LMIp c χ (u s)) (volume.restrict (Icc a b)) :=
    hF.integral_prod_left
  have hwc : Continuous fun s => ((w s : ℝ) : ℂ) := Complex.continuous_ofReal.comp hw
  obtain ⟨M, hM⟩ := hcs.exists_bound_of_continuous hw
  have hI2 : IntegrableOn (fun s => ((w s : ℝ) : ℂ) * LMIp c χ (u s)) (Icc a b) := by
    refine Integrable.bdd_mul (c := M) hI hwc.aestronglyMeasurable (ae_of_all _ fun s => ?_)
    simpa using hM s
  show IntegrableOn _ (Ioi (0 : ℝ))
  refine hI2.of_forall_sdiff_eq_zero measurableSet_Ioi ?_
  rintro s ⟨-, hs⟩
  have hws : w s = 0 := image_eq_zero_of_notMem_tsupport fun h =>
    hs ⟨(hsub h).1.le, (hsub h).2.le⟩
  simp [hws]

/-- Tonelli: a slicewise bound transfers a local space-time bound. -/
theorem lm_L2Loc_of_slice {c s₁ s₂ : ℝ} {Φ Ψ : ℝ × (ℝ × ℝ) → ℝ≥0∞} (hΦ : Measurable Φ)
    (hΨ : Measurable Ψ) {K : ℝ≥0∞} (hK : K ≠ ⊤)
    (hae : ∀ᵐ s ∂(volume.restrict (Icc s₁ s₂)),
      ∫⁻ x in B0579.cell c, Φ (s, x) ≤ K * ∫⁻ x in B0579.cell c, Ψ (s, x))
    (hfin : ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, Ψ p < ⊤) :
    ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, Φ p < ⊤ := by
  have hT : ∀ Θ : ℝ × (ℝ × ℝ) → ℝ≥0∞, Measurable Θ → ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, Θ p =
      ∫⁻ s in Icc s₁ s₂, ∫⁻ x in B0579.cell c, Θ (s, x) := fun Θ hΘ => by
    rw [Measure.volume_eq_prod ℝ (ℝ × ℝ), ← Measure.prod_restrict,
      lintegral_prod _ hΘ.aemeasurable]
  rw [hT Φ hΦ]
  rw [hT Ψ hΨ] at hfin
  refine lt_of_le_of_lt (lintegral_mono_ae hae) ?_
  rw [lintegral_const_mul _ (Measurable.lintegral_prod_right' hΨ)]
  exact ENNReal.mul_lt_top hK.lt_top hfin

/-- **`u_k = J_k b ∈ L²_loc((0,∞); L²(cell))`.** -/
theorem lmUkL2Loc : LMUkL2Loc := by
  intro c ν μ F b G hS J hJ k s₁ s₂ h1 h2
  have hum : ∀ i : Fin 2, Measurable fun p : ℝ × (ℝ × ℝ) => LMMollU J b k p.1 p.2 i := fun i =>
    hJ.measurable k b hS.sol.measurable i
  have hΦ : Measurable fun p : ℝ × (ℝ × ℝ) =>
      ENNReal.ofReal (vnorm2 (fun i => LMMollU J b k p.1 p.2 i) ^ 2) :=
    ENNReal.measurable_ofReal.comp ((aeg_measurable_vnorm2 hum).pow_const 2)
  have hΨ : Measurable fun p : ℝ × (ℝ × ℝ) =>
      ENNReal.ofReal (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) :=
    ENNReal.measurable_ofReal.comp
      (((aeg_measurable_vnorm2 hS.sol.measurable).pow_const 2).add
        ((aeg_measurable_tnorm2 hS.sol.gradMeasurable).pow_const 2))
  have hsub : Icc s₁ s₂ ⊆ Ioi (0 : ℝ) := fun s hs => lt_of_lt_of_le h1 hs.1
  have hgood := ae_restrict_of_ae_restrict_of_subset hsub (lmAeGoodSlice c ν μ F b G hS)
  refine lm_L2Loc_of_slice (K := 1) hΦ hΨ ENNReal.one_ne_top ?_ (hS.sol.energyLoc s₁ s₂ h1 h2)
  filter_upwards [hgood] with s hs
  rw [one_mul]
  have hb := hs.1
  have hu : LMCellL2 c (LMMollU J b k s) := hJ.memL2 k _ hb
  have e1 : ∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (fun i => LMMollU J b k s x i) ^ 2) =
      ENNReal.ofReal (∫ x in B0579.cell c, ∑ i : Fin 2, ‖LMMollU J b k s x i‖ ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal (lm_vec_sq_integrable hu)
      (ae_of_all _ fun x => Finset.sum_nonneg fun i _ => sq_nonneg _)]
    exact lintegral_congr fun x => by rw [lm_vnorm2_sq]
  have e2 : ENNReal.ofReal (∫ x in B0579.cell c, ∑ i : Fin 2, ‖b (s, x) i‖ ^ 2) ≤
      ∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (b (s, x)) ^ 2 + tnorm2 (G (s, x)) ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal (lm_vec_sq_integrable hb)
      (ae_of_all _ fun x => Finset.sum_nonneg fun i _ => sq_nonneg _)]
    refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
    rw [lm_vnorm2_sq]
    exact le_add_of_nonneg_right (sq_nonneg _)
  rw [e1]
  exact (ENNReal.ofReal_le_ofReal (hJ.contr k _ hb)).trans e2

/-- The `L²` bound for `Z`. -/
theorem lmDivJ_norm_le {c : ℝ} {J : ℕ → LMSpField → LMSpField} (hX : LMMollH1 c J) (k : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ × ℝ → Fin 2 → Fin 2 → ℂ, (∀ j, LMCellL2 c (fun y i => T y i j)) →
      ∫ x in B0579.cell c, ∑ i : Fin 2, ‖lmDivJ J k T x i‖ ^ 2 ≤
        K * ∫ x in B0579.cell c, ∑ i : Fin 2, ∑ j : Fin 2, ‖T x i j‖ ^ 2 := by
  obtain ⟨C, hC⟩ := hX.gradL2 k
  refine ⟨8 * |C|, by positivity, fun T hT => ?_⟩
  have hZ := lmDivJ_cellL2 hX k hT
  set W : ℝ := ∫ x in B0579.cell c, ∑ i : Fin 2, ∑ j : Fin 2, ‖T x i j‖ ^ 2 with hW
  have hWi : Integrable (fun x => ∑ i : Fin 2, ∑ j : Fin 2, ‖T x i j‖ ^ 2)
      (volume.restrict (B0579.cell c)) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => lm_sq_integrable (hT j i)
  have hW0 : 0 ≤ W := integral_nonneg fun x =>
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hcol : ∀ i j : Fin 2,
      ∫ x in B0579.cell c, ‖LMPd j (fun y => J k (fun y' i' => T y' i' j) y i) x‖ ^ 2 ≤ |C| * W := by
    intro i j
    refine (hC _ (hT j) i j).2.trans ?_
    have hle : ∫ x in B0579.cell c, ∑ l : Fin 2, ‖T x l j‖ ^ 2 ≤ W := by
      refine integral_mono (lm_vec_sq_integrable (hT j)) hWi fun x => ?_
      show ∑ l : Fin 2, ‖T x l j‖ ^ 2 ≤ ∑ i : Fin 2, ∑ j : Fin 2, ‖T x i j‖ ^ 2
      refine Finset.sum_le_sum fun l _ => ?_
      exact Finset.single_le_sum (f := fun j => ‖T x l j‖ ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ j)
    have hnn : 0 ≤ ∫ x in B0579.cell c, ∑ l : Fin 2, ‖T x l j‖ ^ 2 :=
      integral_nonneg fun x => Finset.sum_nonneg fun l _ => sq_nonneg _
    calc C * _ ≤ |C| * ∫ x in B0579.cell c, ∑ l : Fin 2, ‖T x l j‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (le_abs_self C) hnn
      _ ≤ |C| * W := mul_le_mul_of_nonneg_left hle (abs_nonneg C)
  have hpt : ∀ x, ∑ i : Fin 2, ‖lmDivJ J k T x i‖ ^ 2 ≤ ∑ i : Fin 2, ∑ j : Fin 2,
      2 * ‖LMPd j (fun y => J k (fun y' i' => T y' i' j) y i) x‖ ^ 2 := by
    intro x
    refine Finset.sum_le_sum fun i _ => ?_
    simp only [lmDivJ, Fin.sum_univ_two]
    exact lm_norm_add_sq_le _ _
  have hint : ∀ i j : Fin 2, Integrable
      (fun x => 2 * ‖LMPd j (fun y => J k (fun y' i' => T y' i' j) y i) x‖ ^ 2)
      (volume.restrict (B0579.cell c)) := fun i j =>
    (lm_sq_integrable (hC _ (hT j) i j).1).const_mul 2
  have hInt : Integrable (fun x => ∑ i : Fin 2, ∑ j : Fin 2,
      2 * ‖LMPd j (fun y => J k (fun y' i' => T y' i' j) y i) x‖ ^ 2)
      (volume.restrict (B0579.cell c)) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j
  refine (integral_mono (lm_vec_sq_integrable hZ) hInt hpt).trans ?_
  have hsum : ∀ i : Fin 2, ∫ x in B0579.cell c, ∑ j : Fin 2,
      2 * ‖LMPd j (fun y => J k (fun y' i' => T y' i' j) y i) x‖ ^ 2 = ∑ j : Fin 2,
      2 * ∫ x in B0579.cell c, ‖LMPd j (fun y => J k (fun y' i' => T y' i' j) y i) x‖ ^ 2 := fun i => by
    rw [integral_finsetSum _ fun j _ => hint i j]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  have e : ∫ x in B0579.cell c, ∑ i : Fin 2, ∑ j : Fin 2,
      2 * ‖LMPd j (fun y => J k (fun y' i' => T y' i' j) y i) x‖ ^ 2 = ∑ i : Fin 2, ∑ j : Fin 2,
      2 * ∫ x in B0579.cell c, ‖LMPd j (fun y => J k (fun y' i' => T y' i' j) y i) x‖ ^ 2 := by
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
    exact Finset.sum_congr rfl fun i _ => hsum i
  rw [e]
  simp only [Fin.sum_univ_two]
  have h00 := hcol 0 0
  have h01 := hcol 0 1
  have h10 := hcol 1 0
  have h11 := hcol 1 1
  linarith

/-- **`𝒫₀ Z ∈ L²_loc((0,∞); L²(cell))`.** -/
theorem lmYtL2Loc : LMYtL2Loc := by
  intro c ν μ F b G hS J hJ hX k Yt hYm hYae s₁ s₂ h1 h2
  have hc : 0 < c := hS.pos_c
  obtain ⟨K, hK0, hK⟩ := lmDivJ_norm_le hX k
  have hΦ : Measurable fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (vnorm2 (fun i => Yt p i) ^ 2) :=
    ENNReal.measurable_ofReal.comp ((aeg_measurable_vnorm2 hYm).pow_const 2)
  have hA : Measurable fun p : ℝ × (ℝ × ℝ) =>
      ENNReal.ofReal (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) :=
    ENNReal.measurable_ofReal.comp
      (((aeg_measurable_vnorm2 hS.sol.measurable).pow_const 2).add
        ((aeg_measurable_tnorm2 hS.sol.gradMeasurable).pow_const 2))
  have hB : Measurable fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (tnorm2 (F p) ^ 2) :=
    ENNReal.measurable_ofReal.comp ((aeg_measurable_tnorm2 hS.meas).pow_const 2)
  have hΨ : Measurable fun p : ℝ × (ℝ × ℝ) =>
      ENNReal.ofReal (2 * ν ^ 2) * ENNReal.ofReal (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) +
        ENNReal.ofReal 2 * ENNReal.ofReal (tnorm2 (F p) ^ 2) :=
    (hA.const_mul _).add (hB.const_mul _)
  have hfin : ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
      (ENNReal.ofReal (2 * ν ^ 2) * ENNReal.ofReal (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) +
        ENNReal.ofReal 2 * ENNReal.ofReal (tnorm2 (F p) ^ 2)) < ⊤ := by
    rw [lintegral_add_left (hA.const_mul _), lintegral_const_mul _ hA, lintegral_const_mul _ hB]
    exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (hS.sol.energyLoc s₁ s₂ h1 h2), ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (hS.l2loc s₁ s₂ h1 h2)⟩
  have hsub : Icc s₁ s₂ ⊆ Ioi (0 : ℝ) := fun s hs => lt_of_lt_of_le h1 hs.1
  have hgood := ae_restrict_of_ae_restrict_of_subset hsub (lmAeGoodSlice c ν μ F b G hS)
  have hYr := ae_restrict_of_ae_restrict_of_subset hsub hYae
  refine lm_L2Loc_of_slice (K := ENNReal.ofReal K) hΦ hΨ ENNReal.ofReal_ne_top ?_ hfin
  filter_upwards [hgood, hYr] with s hs hYs
  have hT := fun j => lmTens_col_cellL2 (ν := ν) hs j
  have hZ := lmDivJ_cellL2 hX k hT
  have hP := lmP0C_cellL2 c (lmDivJ J k (fun y => lmTens ν F G (s, y)))
  have e1 : ∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (fun i => Yt (s, x) i) ^ 2) =
      ENNReal.ofReal (∫ x in B0579.cell c, ∑ i : Fin 2,
        ‖P0C c (lmDivJ J k (fun y => lmTens ν F G (s, y))) x i‖ ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal (lm_vec_sq_integrable hP)
      (ae_of_all _ fun x => Finset.sum_nonneg fun i _ => sq_nonneg _)]
    refine lintegral_congr_ae ?_
    filter_upwards [hYs] with x hx
    rw [lm_vnorm2_sq]
    simp only [hx]
  have hTint : Integrable (fun x => ∑ i : Fin 2, ∑ j : Fin 2, ‖lmTens ν F G (s, x) i j‖ ^ 2)
      (volume.restrict (B0579.cell c)) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => lm_sq_integrable (hT j i)
  have e2 : ENNReal.ofReal (∫ x in B0579.cell c, ∑ i : Fin 2, ∑ j : Fin 2,
      ‖lmTens ν F G (s, x) i j‖ ^ 2) ≤ ∫⁻ x in B0579.cell c,
      (ENNReal.ofReal (2 * ν ^ 2) * ENNReal.ofReal (vnorm2 (b (s, x)) ^ 2 + tnorm2 (G (s, x)) ^ 2) +
        ENNReal.ofReal 2 * ENNReal.ofReal (tnorm2 (F (s, x)) ^ 2)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hTint (ae_of_all _ fun x =>
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)]
    refine lintegral_mono fun x => ?_
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hterm : ∀ i j : Fin 2, ‖lmTens ν F G (s, x) i j‖ ^ 2 ≤
        2 * ν ^ 2 * ‖G (s, x) i j‖ ^ 2 + 2 * ‖F (s, x) i j‖ ^ 2 := fun i j => by
      refine (lm_norm_add_sq_le _ _).trans ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
      linarith
    have hsum : ∑ i : Fin 2, ∑ j : Fin 2, ‖lmTens ν F G (s, x) i j‖ ^ 2 ≤
        2 * ν ^ 2 * tnorm2 (G (s, x)) ^ 2 + 2 * tnorm2 (F (s, x)) ^ 2 := by
      simp only [lm_tnorm2_sq, Fin.sum_univ_two]
      have h00 := hterm 0 0
      have h01 := hterm 0 1
      have h10 := hterm 1 0
      have h11 := hterm 1 1
      linarith
    have hv : 0 ≤ 2 * ν ^ 2 * vnorm2 (b (s, x)) ^ 2 := by positivity
    nlinarith
  have hW0 : 0 ≤ ∫ x in B0579.cell c, ∑ i : Fin 2, ∑ j : Fin 2,
      ‖lmTens ν F G (s, x) i j‖ ^ 2 := integral_nonneg fun x =>
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [e1]
  calc _ ≤ ENNReal.ofReal (K * ∫ x in B0579.cell c, ∑ i : Fin 2, ∑ j : Fin 2,
        ‖lmTens ν F G (s, x) i j‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal ((lmP0CContr c hc _ hZ).trans (hK _ hT))
    _ = ENNReal.ofReal K * ENNReal.ofReal (∫ x in B0579.cell c, ∑ i : Fin 2, ∑ j : Fin 2,
        ‖lmTens ν F G (s, x) i j‖ ^ 2) := ENNReal.ofReal_mul hK0
    _ ≤ _ := by gcongr

end UnforcedLeray.Short.IIIa
