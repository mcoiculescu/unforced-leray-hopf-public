import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G4.IntLeaf1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1_2_2_1
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.EnergyBalance.TimeDerivLocal.ErrJetLocal.VelJetLocal.Late.UniformZero

/-!
# `PartIII-b:IIIb-D3/2/G4/4/3`: integrable majorant of the lower piece (`flatLowerMaj`)

Source `the November 2 reference manuscript` 4686-4688 (full forward gain
estimate on `(1.2/ν, ν^{-3/2})`), 4637-4693.

We prove `LowerSup D` (`flatLowerSup`) and deduce `flatLowerMaj (D : SeqData) : LowerMaj D`.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G4

open ConcreteYF FlatSettingInst

private lemma abs_entry_le_frob_local (A : Mat3) (i j : Fin 3) : |A i j| ≤ frob A := by
  unfold frob
  apply Real.abs_le_sqrt
  calc A i j ^ 2 ≤ ∑ j', A i j' ^ 2 :=
        Finset.single_le_sum (f := fun j' => A i j' ^ 2) (fun j' _ => sq_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', A i' j' ^ 2 :=
        Finset.single_le_sum (f := fun i' => ∑ j', A i' j' ^ 2)
          (fun i' _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
          (Finset.mem_univ i)

private lemma abs_two_zz_sub_rr_le_three_frob (A : Mat3) :
    |2 * A 2 2 - A 0 0| ≤ 3 * frob A := by
  have h22 := abs_entry_le_frob_local A 2 2
  have h00 := abs_entry_le_frob_local A 0 0
  have htri : |2 * A 2 2 - A 0 0| ≤ |2 * A 2 2| + |A 0 0| := abs_sub _ _
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at htri
  linarith

private lemma integral_avgμ_eq_cellInt {c : ℝ} (hc : 0 ≤ c) (F : ℝ × ℝ → ℝ) :
    ∫ p, F p ∂(UnforcedLeray.Cyl.avgμ c) = cellInt c F := by
  rw [UnforcedLeray.Cyl.integral_avgμ hc F, cellInt, smul_eq_mul]
  congr 1
  have hmeas : (volume : Measure (ℝ × ℝ)).restrict (Ioo (-c / 2) (c / 2) ×ˢ univ) =
      (volume : Measure (ℝ × ℝ)).restrict (UnforcedLeray.Cyl.cell c) := by
    rw [UnforcedLeray.Cyl.cell, Measure.volume_eq_prod, ← Measure.prod_restrict,
      ← Measure.prod_restrict, Measure.restrict_univ, Measure.restrict_congr_set Ioo_ae_eq_Ico]
  rw [hmeas]

private lemma abs_cellInt_symOuter_le {ν c m : ℝ} [Fact (1 < m)] [Fact (0 < c)]
    (hc : 0 < c) (tr : UnforcedLeray.B0140.TrainSol ν c) (s : ℝ) (y : Xmc c m)
    {E : ℝ} (hE0 : 0 ≤ E) (hE : UnforcedLeray.Train.cellL2 c (tr.v s) ≤ ENNReal.ofReal E) :
    |cellInt c (fun x =>
      2 * IIIa.symOuter (NearInst.trainMer tr (s, x)) (kcMer y x) 2 2 -
        IIIa.symOuter (NearInst.trainMer tr (s, x)) (kcMer y x) 0 0)| ≤
      6 * c⁻¹ * E * ‖kcLp y‖ := by
  set F : ℝ × ℝ → ℝ := fun x =>
    2 * IIIa.symOuter (NearInst.trainMer tr (s, x)) (kcMer y x) 2 2 -
      IIIa.symOuter (NearInst.trainMer tr (s, x)) (kcMer y x) 0 0
  have hRHS0 : 0 ≤ 6 * c⁻¹ * E * ‖kcLp y‖ := by positivity
  rw [← integral_avgμ_eq_cellInt hc.le F, ← Real.norm_eq_abs]
  by_cases hInt : Integrable F (UnforcedLeray.Cyl.avgμ c)
  · have h1 : ‖∫ x, F x ∂(UnforcedLeray.Cyl.avgμ c)‖ ≤ ∫ x, ‖F x‖ ∂(UnforcedLeray.Cyl.avgμ c) :=
      norm_integral_le_integral_norm F
    have h2 : ENNReal.ofReal (∫ x, ‖F x‖ ∂(UnforcedLeray.Cyl.avgμ c)) =
        ∫⁻ x, ENNReal.ofReal ‖F x‖ ∂(UnforcedLeray.Cyl.avgμ c) :=
      ofReal_integral_eq_lintegral_ofReal hInt.norm (ae_of_all _ fun _ => norm_nonneg _)
    have hpt : ∀ x, ENNReal.ofReal ‖F x‖ ≤
        ENNReal.ofReal 3 * ENNReal.ofReal (frob
          (IIIa.symOuter (NearInst.trainMer tr (s, x)) (kcMer y x))) := by
      intro x
      rw [Real.norm_eq_abs, ← ENNReal.ofReal_mul (by norm_num)]
      exact ENNReal.ofReal_le_ofReal (abs_two_zz_sub_rr_le_three_frob _)
    have h3 : ∫⁻ x, ENNReal.ofReal ‖F x‖ ∂(UnforcedLeray.Cyl.avgμ c) ≤
        ENNReal.ofReal (6 * c⁻¹ * E * ‖kcLp y‖) := by
      calc ∫⁻ x, ENNReal.ofReal ‖F x‖ ∂(UnforcedLeray.Cyl.avgμ c)
          ≤ ∫⁻ x, ENNReal.ofReal 3 * ENNReal.ofReal (frob
              (IIIa.symOuter (NearInst.trainMer tr (s, x)) (kcMer y x)))
              ∂(UnforcedLeray.Cyl.avgμ c) := lintegral_mono hpt
        _ = ENNReal.ofReal 3 * ∫⁻ x, ENNReal.ofReal (frob
              (IIIa.symOuter (NearInst.trainMer tr (s, x)) (kcMer y x)))
              ∂(UnforcedLeray.Cyl.avgμ c) :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal 3 * (2 * ENNReal.ofReal c⁻¹ *
              UnforcedLeray.Train.cellL2 c (tr.v s) * ENNReal.ofReal ‖kcLp y‖) := by
            gcongr
            exact slice_gen m tr s y
        _ ≤ ENNReal.ofReal 3 * (2 * ENNReal.ofReal c⁻¹ *
              ENNReal.ofReal E * ENNReal.ofReal ‖kcLp y‖) := by
            gcongr
        _ = ENNReal.ofReal (6 * c⁻¹ * E * ‖kcLp y‖) := by
            have e : 6 * c⁻¹ * E * ‖kcLp y‖ = 3 * (2 * c⁻¹ * E * ‖kcLp y‖) := by ring
            rw [e, ENNReal.ofReal_mul (by norm_num),
              ENNReal.ofReal_mul (by positivity),
              ENNReal.ofReal_mul (by positivity),
              ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]
    have h4 : ∫ x, ‖F x‖ ∂(UnforcedLeray.Cyl.avgμ c) ≤ 6 * c⁻¹ * E * ‖kcLp y‖ :=
      (ENNReal.ofReal_le_ofReal_iff hRHS0).1 (h2 ▸ h3)
    exact h1.trans h4
  · rw [integral_undef hInt, norm_zero]
    exact hRHS0

private lemma cellL2_uniform_on_Icc {ν c : ℝ} (hν : 0 < ν) (hc : 1 ≤ c)
    (tr : UnforcedLeray.B0140.TrainSol ν c) (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    {S : ℝ} (hS : 0 < S) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ s ∈ Icc (0 : ℝ) S,
      UnforcedLeray.Train.cellL2 c (tr.v s) ≤ ENNReal.ofReal E := by
  obtain ⟨B0, hB0⟩ := UnforcedLeray.Short.PartI.velZeroUniformL2_proof ν c hν hc tr htr S hS 0
  obtain ⟨B1, hB1⟩ := UnforcedLeray.Short.PartI.velZeroUniformL2_proof ν c hν hc tr htr S hS 1
  set B := max (B0 + B1) 0
  have hB_nn : 0 ≤ B := le_max_right _ _
  refine ⟨B ^ (1 / (2 : ℝ)), Real.rpow_nonneg hB_nn _, fun s hs => ?_⟩
  have hint : Integrable (fun z => ‖tr.v s z‖ ^ 2) (UnforcedLeray.Cyl.cellμ c) :=
    tr.isTrain.finite_energy s hs.1
  have hcont_v : Continuous (tr.v s) :=
    continuousOn_univ.1 (tr.isTrain.smooth_v.continuousOn.comp
      (continuousOn_const.prodMk continuousOn_id) (fun x _ => ⟨mem_Ici.2 hs.1, mem_univ x⟩))
  have hint_k : ∀ k : Fin 2, Integrable (fun z => (tr.v s z k) ^ 2) (UnforcedLeray.Cyl.cellμ c) := by
    intro k
    have hck : Continuous (fun z => (tr.v s z k) ^ 2) :=
      (((EuclideanSpace.proj k : Merid →L[ℝ] ℝ).continuous.comp hcont_v).pow 2)
    refine hint.mono' hck.aestronglyMeasurable (ae_of_all _ fun z => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact UnforcedLeray.Short.PartI.vcu_comp_le_normsq tr s z k
  have hsq : ∀ z, ‖tr.v s z‖ ^ 2 = (tr.v s z 0) ^ 2 + (tr.v s z 1) ^ 2 := by
    intro z
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    simp [Real.norm_eq_abs, sq_abs]
  have hInt_le : ∫ z, ‖tr.v s z‖ ^ 2 ∂(UnforcedLeray.Cyl.cellμ c) ≤ B := by
    have heq : ∫ z, ‖tr.v s z‖ ^ 2 ∂(UnforcedLeray.Cyl.cellμ c) =
        (∫ z, (tr.v s z 0) ^ 2 ∂(UnforcedLeray.Cyl.cellμ c)) +
          (∫ z, (tr.v s z 1) ^ 2 ∂(UnforcedLeray.Cyl.cellμ c)) := by
      simp_rw [hsq]
      exact integral_add (hint_k 0) (hint_k 1)
    have h0 : ∫ z, (tr.v s z 0) ^ 2 ∂(UnforcedLeray.Cyl.cellμ c) ≤ B0 := hB0 s hs.1 hs.2
    have h1 : ∫ z, (tr.v s z 1) ^ 2 ∂(UnforcedLeray.Cyl.cellμ c) ≤ B1 := hB1 s hs.1 hs.2
    exact (heq ▸ add_le_add h0 h1).trans (le_max_left _ _)
  unfold UnforcedLeray.Train.cellL2
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  have hpt : ∀ z, ‖tr.v s z‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖tr.v s z‖ ^ 2) := by
    intro z
    rw [← ofReal_norm (tr.v s z), ENNReal.rpow_two, sq,
      ← ENNReal.ofReal_mul (norm_nonneg _), ← sq]
  simp_rw [hpt]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => sq_nonneg _)]
  calc ENNReal.ofReal (∫ z, ‖tr.v s z‖ ^ 2 ∂(UnforcedLeray.Cyl.cellμ c)) ^ (1 / (2 : ℝ))
      ≤ (ENNReal.ofReal B) ^ (1 / (2 : ℝ)) := by gcongr
    _ = ENNReal.ofReal (B ^ (1 / (2 : ℝ))) :=
        ENNReal.ofReal_rpow_of_nonneg hB_nn (by norm_num)

/-- For actual flat sequences, eventually in `n`, for each `z ∈ [-1,1]` and `B` of class `a`,
the integrand `ITdens (Mcell ∘ ξ_B)` is bounded on `(0, ν^{-3/2})`. -/
def LowerSup (D : SeqData) : Prop :=
  ForActual D fun S => ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ B,
      IsBclass D.K.as (nu D n) B →
    ∃ C : ℝ, ∀ s : ℝ, 0 < s → s < nu D n ^ (-(3 / 2 : ℝ)) →
      |(S n).ITdens (fun s => (S n).Mcell s ((S n).xi (D.mu n z : ℂ) B s)) s| ≤ C

/-- Proof of `LowerSup D` via `velZeroUniformL2_proof`, `xiD_contOn_of_bclass`, and `slice_gen`. -/
theorem flatLowerSup (D : SeqData) : LowerSup D := by
  intro dm dp hst κ _ m _ _ S hS
  have hmu_ev := mu_eventually_mem D hst.omega_ne hst.sigma_pos hst.sigma_lt
  have hν_lt : ∀ᶠ n : ℕ in atTop, nu D n < 1 :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually (gt_mem_nhds zero_lt_one)
  filter_upwards [hS, hmu_ev, hν_lt] with n ⟨FI, hSn⟩ hmu_z hν1
  intro z hz B hB
  have hμ0 : 0 ≤ D.mu n z := by
    have := (hmu_z z hz).1
    linarith [hst.sigma_pos]
  have hν : 0 < nu D n := retNu_pos D.Pl D.σ₀ n
  have hc0 : 0 < cOf (nu D n) := cOf_pos hν
  have : Fact (0 < cOf (nu D n)) := ⟨hc0⟩
  have hc1 : 1 ≤ cOf (nu D n) := by
    unfold cOf
    exact (one_le_inv₀ (pow_pos hν 2)).2 (pow_le_one₀ hν.le hν1.le)
  let uo : ℝ := nu D n ^ (-(3 / 2 : ℝ))
  have huo_pos : 0 < uo := Real.rpow_pos_of_pos hν _
  obtain ⟨E, hE0, hE⟩ := cellL2_uniform_on_Icc hν hc1 (D.train n) (D.train_buc n) huo_pos
  have hξ_cont : ContinuousOn (fun s : ℝ => ‖kcLp (xiD FI (D.mu n z : ℂ) B s)‖)
      (Icc (6 / 5 / nu D n) uo) := by
    have hsub : Icc (6 / 5 / nu D n) uo ⊆ Ioi 0 := fun s hs =>
      lt_of_lt_of_le (div_pos (by norm_num) hν) hs.1
    exact continuous_kcLp.norm.continuousOn.comp
      ((xiD_contOn_of_bclass FI hμ0 hB).mono hsub) (mapsTo_univ _ _)
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hξ_cont
  set K' : ℝ := max K 0
  have hK'0 : 0 ≤ K' := le_max_right _ _
  refine ⟨6 * (cOf (nu D n))⁻¹ * E * K', fun s hs0 hsuo => ?_⟩
  rw [hSn]
  change |D.K.χo (nu D n * s) * s ^ (-(3 / 2 : ℝ)) *
    cellInt (cOf (nu D n)) (fun x =>
      2 * IIIa.symOuter (NearInst.trainMer (D.train n) (s, x))
        (kcMer (xiD FI (D.mu n z : ℂ) B s) x) 2 2 -
      IIIa.symOuter (NearInst.trainMer (D.train n) (s, x))
        (kcMer (xiD FI (D.mu n z : ℂ) B s) x) 0 0)| ≤
    6 * (cOf (nu D n))⁻¹ * E * K'
  by_cases hs_cut : s ≤ 6 / 5 / nu D n
  · have hνs : nu D n * s ≤ 6 / 5 := by
      have := (le_div_iff₀ hν).1 hs_cut
      linarith
    rw [D.K.hχo.zero (nu D n * s) hνs]
    simp only [zero_mul, abs_zero]
    positivity
  · have hs_cut' : 6 / 5 / nu D n < s := not_le.1 hs_cut
    have hs_mem : s ∈ Icc (6 / 5 / nu D n) uo := ⟨hs_cut'.le, hsuo.le⟩
    have hs1 : 1 ≤ s := by
      have h12 : 1 ≤ 6 / 5 / nu D n := by
        rw [le_div_iff₀ hν]
        linarith
      exact h12.trans hs_cut'.le
    have hχ_abs : |D.K.χo (nu D n * s)| ≤ 1 := by
      rcases D.K.hχo.range (nu D n * s) with ⟨h0, h1⟩
      rw [abs_of_nonneg h0]
      exact h1
    have hpow_abs : |s ^ (-(3 / 2 : ℝ))| ≤ 1 := by
      rw [abs_of_nonneg (Real.rpow_nonneg hs0.le _)]
      exact Real.rpow_le_one_of_one_le_of_nonpos hs1 (by norm_num)
    have hcell : |cellInt (cOf (nu D n)) (fun x =>
        2 * IIIa.symOuter (NearInst.trainMer (D.train n) (s, x))
          (kcMer (xiD FI (D.mu n z : ℂ) B s) x) 2 2 -
        IIIa.symOuter (NearInst.trainMer (D.train n) (s, x))
          (kcMer (xiD FI (D.mu n z : ℂ) B s) x) 0 0)| ≤
        6 * (cOf (nu D n))⁻¹ * E * K' := by
      have h1 := abs_cellInt_symOuter_le hc0 (D.train n) s
        (xiD FI (D.mu n z : ℂ) B s) hE0 (hE s ⟨hs0.le, hsuo.le⟩)
      have h2 : ‖kcLp (xiD FI (D.mu n z : ℂ) B s)‖ ≤ K' := by
        have := hK s hs_mem
        rw [Real.norm_of_nonneg (norm_nonneg _)] at this
        exact this.trans (le_max_left _ _)
      exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
    rw [abs_mul, abs_mul]
    have hχp : |D.K.χo (nu D n * s)| * |s ^ (-(3 / 2 : ℝ))| ≤ 1 := by
      nlinarith [abs_nonneg (D.K.χo (nu D n * s)), abs_nonneg (s ^ (-(3 / 2 : ℝ)))]
    nlinarith [abs_nonneg (cellInt (cOf (nu D n)) (fun x =>
      2 * IIIa.symOuter (NearInst.trainMer (D.train n) (s, x))
        (kcMer (xiD FI (D.mu n z : ℂ) B s) x) 2 2 -
      IIIa.symOuter (NearInst.trainMer (D.train n) (s, x))
        (kcMer (xiD FI (D.mu n z : ℂ) B s) x) 0 0))]

/-- Reduction: the sup bound gives the integrable majorant of the lower piece. -/
theorem lowerMaj_of_sup (D : SeqData) (h : LowerSup D) : LowerMaj D := by
  intro dm dp hst κ hκ m _ hm S hS
  filter_upwards [h dm dp hst κ hκ m hm S hS] with n hn
  intro z hz B hB
  obtain ⟨C, hC⟩ := hn z hz B hB
  have hsub : Ioo (0 : ℝ) (nu D n ^ (-(3 / 2 : ℝ))) ⊆ Ioi 0 := fun x hx => hx.1
  refine ⟨Set.indicator (Ioo (0 : ℝ) (nu D n ^ (-(3 / 2 : ℝ)))) (fun _ => |C|), ?_, ?_⟩
  · rw [integrable_indicator_iff measurableSet_Ioo, IntegrableOn,
      Measure.restrict_restrict measurableSet_Ioo, inter_eq_left.2 hsub]
    exact integrableOn_const measure_Ioo_lt_top.ne
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs' : (0 : ℝ) < s := hs
    by_cases hu : s < nu D n ^ (-(3 / 2 : ℝ))
    · have key : (S n).ITdens (fun s => if s < nu D n ^ (-(3 / 2 : ℝ)) then
            (S n).Mcell s ((S n).xi (D.mu n z : ℂ) B s) else fun _ => 0) s
          = (S n).ITdens (fun s => (S n).Mcell s ((S n).xi (D.mu n z : ℂ) B s)) s := by
        unfold FlatSetting.ITdens
        simp [hu]
      unfold lowerPiece
      rw [key, Real.norm_eq_abs, indicator_of_mem (mem_Ioo.2 ⟨hs', hu⟩)]
      exact (hC s hs' hu).trans (le_abs_self C)
    · have key0 : (S n).ITdens (fun s => if s < nu D n ^ (-(3 / 2 : ℝ)) then
            (S n).Mcell s ((S n).xi (D.mu n z : ℂ) B s) else fun _ => 0) s = 0 := by
        unfold FlatSetting.ITdens
        simp [hu, cellInt]
      unfold lowerPiece
      rw [key0, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => abs_nonneg C) s

theorem flatLowerMaj (D : SeqData) : LowerMaj D :=
  lowerMaj_of_sup D (flatLowerSup D)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G4
