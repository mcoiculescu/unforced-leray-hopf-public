import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T19_3
import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.TailContinuation.CoreUniqueness.MollLimitCore
import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.TailContinuation.CoreUniqueness.CutoffCore

/-!
# Part III-a, task `PartIII-a:T19/3/4`: homogeneous vanishing on the core `(0, H)`

Source of record: `the November 2 reference manuscript` (SP), lines 3541-3545
(Step P6: uniqueness on the core `(0, H)` via the localized weighted energy inequality).

Proves `coreCausalHomogeneousZero : UnforcedLeray.Short.IIIa.CoreCausalHomogeneousZero`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## Helper lemmas on truncated fields and core-restricted norms -/

private theorem gainConj_truncVec (γ ν H' : ℝ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) :
    gainConj γ ν (truncVec H' b) = truncVec H' (gainConj γ ν b) := by
  funext p i
  unfold gainConj truncVec
  split_ifs <;> simp

private theorem gainConj_truncTen (γ ν H' : ℝ) (T : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) :
    gainConj γ ν (truncTen H' T) = truncTen H' (gainConj γ ν T) := by
  funext p i j
  unfold gainConj truncTen
  split_ifs <;> simp

private theorem truncTen_neg_flatMult_eq {ν c H' : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    (d : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) :
    truncTen H' (fun p i j => -flatMult tr d p i j) =
      fun p i j => -flatMult tr (truncVec H' d) p i j := by
  funext p i j
  unfold truncTen truncVec flatMult
  split_ifs with hp <;> simp [hp]

private theorem hCalNormOn_le_hCalNorm_truncVec (c H' : ℝ) (f : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) :
    hCalNormOn c H' f ≤ hCalNorm c (truncVec H' f) := by
  have heq : hCalNormOn c H' f = hCalNormOn c H' (truncVec H' f) := by
    unfold hCalNormOn
    refine eLpNorm_congr_ae ?_
    have hm : MeasurableSet (Iio H' ×ˢ (univ : Set (ℝ × ℝ))) :=
      measurableSet_Iio.prod MeasurableSet.univ
    filter_upwards [ae_restrict_mem hm] with p hp
    have hp1 : p.1 < H' := hp.1
    rw [vnorm2_truncVec_eq, if_pos hp1]
  rw [heq]
  exact hCalNormOn_le_hCalNorm c H' (truncVec H' f)

private theorem tCalNormOn_le_tCalNorm_truncTen (c H' : ℝ) (T : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) :
    tCalNormOn c H' T ≤ tCalNorm c (truncTen H' T) := by
  have heq : tCalNormOn c H' T = tCalNormOn c H' (truncTen H' T) := by
    unfold tCalNormOn
    refine eLpNorm_congr_ae ?_
    have hm : MeasurableSet (Iio H' ×ˢ (univ : Set (ℝ × ℝ))) :=
      measurableSet_Iio.prod MeasurableSet.univ
    filter_upwards [ae_restrict_mem hm] with p hp
    have hp1 : p.1 < H' := hp.1
    rw [tnorm2_truncTen_eq, if_pos hp1]
  rw [heq]
  exact tCalNormOn_le_tCalNorm c H' (truncTen H' T)

private theorem eLpNorm_restrict_Iio_eq_zero_of_lt {μ : Measure (ℝ × (ℝ × ℝ))} {H : ℝ} (hH : 0 < H)
    (F : ℝ × (ℝ × ℝ) → ℝ) (hF : ∀ p, 0 ≤ F p)
    (h : ∀ H' ∈ Ioo 0 H, eLpNorm F 2 (μ.restrict (Iio H' ×ˢ univ)) = 0) :
    eLpNorm F 2 (μ.restrict (Iio H ×ˢ univ)) = 0 := by
  have hcov : Iio H ×ˢ (univ : Set (ℝ × ℝ)) ⊆
      ⋃ n : ℕ, Iio (H - H / ((n : ℝ) + 2)) ×ˢ (univ : Set (ℝ × ℝ)) := by
    intro p hp
    have hpH : 0 < (H - p.1) / H := div_pos (sub_pos.2 hp.1) hH
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpH
    refine mem_iUnion.2 ⟨n, ?_, trivial⟩
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h1 : 1 / ((n : ℝ) + 2) < (H - p.1) / H :=
      (one_div_le_one_div_of_le (by positivity) (by linarith)).trans_lt hn
    have h2 : H / ((n : ℝ) + 2) < H - p.1 := by
      have := mul_lt_mul_of_pos_right h1 hH
      rwa [one_div_mul_eq_div, div_mul_cancel₀ _ hH.ne'] at this
    show p.1 < H - H / ((n : ℝ) + 2)
    linarith
  have hsq : eLpNorm F 2 (μ.restrict (Iio H ×ˢ univ)) ^ 2 ≤
      ∑' n : ℕ, eLpNorm F 2 (μ.restrict (Iio (H - H / ((n : ℝ) + 2)) ×ˢ univ)) ^ 2 := by
    simp only [eLpNorm_two_sq_eq_lintegral_nonneg _ F hF]
    exact (lintegral_mono_set hcov).trans (lintegral_iUnion_le _ _)
  have hsum : (∑' n : ℕ, eLpNorm F 2
      (μ.restrict (Iio (H - H / ((n : ℝ) + 2)) ×ˢ univ)) ^ 2) = 0 := by
    refine ENNReal.tsum_eq_zero.2 fun n => ?_
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hmem : H - H / ((n : ℝ) + 2) ∈ Ioo 0 H := by
      refine ⟨?_, ?_⟩
      · have hle : H / ((n : ℝ) + 2) ≤ H / 2 :=
          div_le_div_of_nonneg_left hH.le (by positivity) (by linarith)
        linarith
      · have hpos : 0 < H / ((n : ℝ) + 2) := by positivity
        linarith
    rw [h _ hmem, sq, zero_mul]
  rw [hsum] at hsq
  exact sq_eq_zero_iff.1 (le_antisymm hsq zero_le)

private theorem lintegral_Ioi_eq_zero_of_Icc_of_Ici {H' : ℝ} (hH' : 0 < H') (f : ℝ → ℝ≥0∞)
    (hIcc : ∀ a B : ℝ, 0 < a → a < B → B < H' → ∫⁻ s in Icc a B, f s = 0)
    (hIci : ∀ s ∈ Ici H', f s = 0) :
    ∫⁻ s in Ioi (0 : ℝ), f s = 0 := by
  have hcov : Ioi (0 : ℝ) ⊆
      Ici H' ∪ ⋃ k : ℕ, Icc (H' / ((k : ℝ) + 3)) (H' - H' / ((k : ℝ) + 3)) := by
    intro s hs
    by_cases hsH' : H' ≤ s
    · exact Or.inl hsH'
    · have hsH'' : s < H' := not_le.1 hsH'
      have hs0 : 0 < s / H' := div_pos hs hH'
      have hs1 : 0 < (H' - s) / H' := div_pos (sub_pos.2 hsH'') hH'
      obtain ⟨k₁, hk₁⟩ := exists_nat_one_div_lt hs0
      obtain ⟨k₂, hk₂⟩ := exists_nat_one_div_lt hs1
      refine Or.inr (mem_iUnion.2 ⟨max k₁ k₂, ?_, ?_⟩)
      · have hk : (k₁ : ℝ) + 1 ≤ (max k₁ k₂ : ℕ) + 3 := by
          have : (k₁ : ℝ) ≤ (max k₁ k₂ : ℕ) := by exact_mod_cast le_max_left k₁ k₂
          linarith
        have h1 : 1 / (((max k₁ k₂ : ℕ) : ℝ) + 3) < s / H' :=
          (one_div_le_one_div_of_le (by positivity) hk).trans_lt hk₁
        have h2 := mul_lt_mul_of_pos_right h1 hH'
        rw [one_div_mul_eq_div, div_mul_cancel₀ _ hH'.ne'] at h2
        exact h2.le
      · have hk : (k₂ : ℝ) + 1 ≤ (max k₁ k₂ : ℕ) + 3 := by
          have : (k₂ : ℝ) ≤ (max k₁ k₂ : ℕ) := by exact_mod_cast le_max_right k₁ k₂
          linarith
        have h1 : 1 / (((max k₁ k₂ : ℕ) : ℝ) + 3) < (H' - s) / H' :=
          (one_div_le_one_div_of_le (by positivity) hk).trans_lt hk₂
        have h2 := mul_lt_mul_of_pos_right h1 hH'
        rw [one_div_mul_eq_div, div_mul_cancel₀ _ hH'.ne'] at h2
        linarith
  have h0_Ici : ∫⁻ s in Ici H', f s = 0 := by
    have hcongr : ∫⁻ s in Ici H', f s = ∫⁻ _s in Ici H', (0 : ℝ≥0∞) :=
      setLIntegral_congr_fun measurableSet_Ici fun s hs => hIci s hs
    rw [hcongr, lintegral_zero]
  have h0_iUnion :
      (∑' k : ℕ, ∫⁻ s in Icc (H' / ((k : ℝ) + 3)) (H' - H' / ((k : ℝ) + 3)), f s) = 0 := by
    refine ENNReal.tsum_eq_zero.2 fun k => hIcc _ _ (by positivity) ?_ ?_
    · have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hle : H' / ((k : ℝ) + 3) ≤ H' / 3 :=
        div_le_div_of_nonneg_left hH'.le (by positivity) (by linarith)
      linarith
    · have hpos : 0 < H' / ((k : ℝ) + 3) := by positivity
      linarith
  have hle : ∫⁻ s in Ioi (0 : ℝ), f s ≤
      (∫⁻ s in Ici H', f s) +
        ∑' k : ℕ, ∫⁻ s in Icc (H' / ((k : ℝ) + 3)) (H' - H' / ((k : ℝ) + 3)), f s :=
    (lintegral_mono_set hcov).trans
      ((lintegral_union_le _ _ _).trans (add_le_add le_rfl (lintegral_iUnion_le _ _)))
  rw [h0_Ici, h0_iUnion, add_zero] at hle
  exact le_antisymm hle zero_le

/-! ## Vanishing of the truncated fields on `(0, H')` for `H' < H` -/

private theorem coreTrunc_norms_zero {ν H H' γ : ℝ} {μ : ℂ} (hν0 : 0 < ν) (hH' : H' ∈ Ioo 0 H)
    (hγ : 0 ≤ γ) (hμre : 0 < μ.re) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    {d : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {Gd : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hsol : IsCoreCausalSolution (ν ^ (-2 : ℝ)) ν H μ (trainVel tr) (fun _ _ _ => 0) d Gd) :
    hCalNorm (ν ^ (-2 : ℝ)) (gainConj γ ν (truncVec H' d)) = 0 ∧
      tCalNorm (ν ^ (-2 : ℝ)) (gainConj γ ν (truncTen H' Gd)) = 0 := by
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc : 0 < c := Real.rpow_pos_of_pos hν0 _
  have hH'0 : 0 < H' := hH'.1
  have hH'H : H' < H := hH'.2
  let b' : ℝ × (ℝ × ℝ) → Fin 2 → ℂ := truncVec H' d
  let G' : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ := truncTen H' Gd
  let F' : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ := truncTen H' (fun p i j => -flatMult tr d p i j)
  have hD : CoreTruncData c ν H' μ F' b' G' :=
    coreTruncData_of_coreSol hc hν0 hH'0 hH'H tr htr hsol
  have hF'_eq : F' = fun p i j => -flatMult tr b' p i j := truncTen_neg_flatMult_eq tr d
  have hbm' := measurable_gainConj_vec (γ := γ) (ν := ν) hD.measurable
  have hGm' := measurable_gainConj_ten γ ν hD.gradMeasurable
  have hFm' := measurable_gainConj_ten γ ν hD.meas
  have hBG := gainLocBG c ν γ hγ hν0 b' G' hD.energyLoc
  have hF'loc : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
        ENNReal.ofReal (tnorm2 (gainConj γ ν F' p) ^ 2) < ⊤ := by
    intro s₁ s₂ hs₁ hs₂
    have hs₂0 : 0 ≤ s₂ := (lt_trans hs₁ hs₂).le
    obtain ⟨M, hM0, hM⟩ := core_trainVel_bound_le tr htr hs₂0
    have hmeas_set : MeasurableSet (Icc s₁ s₂ ×ˢ B0579.cell c) :=
      measurableSet_Icc.prod (measurableSet_Ico.prod MeasurableSet.univ)
    have hle : ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
          ENNReal.ofReal (tnorm2 (gainConj γ ν F' p) ^ 2) ≤
        ENNReal.ofReal (8 * M ^ 2) *
          ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
            ENNReal.ofReal (vnorm2 (gainConj γ ν b' p) ^ 2) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_mono' hmeas_set fun p hp => ?_
      rw [← ENNReal.ofReal_mul (by positivity), hF'_eq, core_gainConj_neg_flatMult]
      apply ENNReal.ofReal_le_ofReal
      exact core_tnorm2_neg_flatMult_sq_le tr (gainConj γ ν b') hM0 (hM p.1 hp.1.2 p.2)
    exact lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hBG s₁ s₂ hs₁ hs₂).1)
  -- Slice functions A, N, M_slice, Q
  let gV : ℝ × (ℝ × ℝ) → ℝ := fun p => vnorm2 (gainConj γ ν b' p) ^ 2
  let gN : ℝ × (ℝ × ℝ) → ℝ := fun p => tnorm2 (gainConj γ ν G' p) ^ 2
  let gQ : ℝ × (ℝ × ℝ) → ℝ := fun p => tnorm2 (gainConj γ ν F' p) ^ 2
  have hgVm : Measurable gV := measurable_vnorm2_sq hbm'
  have hgNm : Measurable gN := (measurable_tnorm2 hGm').pow_const 2
  have hgQm : Measurable gQ := (measurable_tnorm2 hFm').pow_const 2
  have hgV0 : ∀ p, 0 ≤ gV p := fun _ => sq_nonneg _
  have hgN0 : ∀ p, 0 ≤ gN p := fun _ => sq_nonneg _
  have hgQ0 : ∀ p, 0 ≤ gQ p := fun _ => sq_nonneg _
  obtain ⟨hVm, hVi, hVslice⟩ := sliceLoc c gV hc hgVm hgV0 fun s₁ s₂ h1 h2 => (hBG s₁ s₂ h1 h2).1
  obtain ⟨hNm, hNi, -⟩ := sliceLoc c gN hc hgNm hgN0 fun s₁ s₂ h1 h2 => (hBG s₁ s₂ h1 h2).2
  obtain ⟨hQm, hQi, hQslice⟩ := sliceLoc c gQ hc hgQm hgQ0 hF'loc
  let A : ℝ → ℝ := sliceSq c gV
  let N : ℝ → ℝ := sliceSq c gN
  let M_slice : ℝ → ℝ :=
    sliceSq c (fun p => tnorm2 (gainConj γ ν F' p) * tnorm2 (gainConj γ ν G' p))
  let Q : ℝ → ℝ := sliceSq c gQ
  have hnn : ∀ s, 0 ≤ A s ∧ 0 ≤ N s ∧ 0 ≤ M_slice s ∧ 0 ≤ Q s :=
    fun s => ⟨sliceSq_nonneg hgV0 s, sliceSq_nonneg hgN0 s,
      sliceSq_nonneg (fun p => mul_nonneg (tnorm2_nonneg _) (tnorm2_nonneg _)) s,
      sliceSq_nonneg hgQ0 s⟩
  have hY := youngSlice c (gainConj γ ν F') (gainConj γ ν G') hc hFm' hGm'
    hF'loc (fun s₁ s₂ h1 h2 => (hBG s₁ s₂ h1 h2).2) ν hν0
  -- Zero-entrance finiteness for A
  obtain ⟨δ0, hδ0, hfinA⟩ : ∃ δ : ℝ, 0 < δ ∧
      ∫⁻ s in Ioo 0 δ, ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s) < ⊤ := by
    obtain ⟨δ, hδ, hfin⟩ := hsol.zeroEntrance
    refine ⟨δ, hδ, ?_⟩
    obtain ⟨-, h2⟩ := ageSlice c (-3 / 2) gV hc hgVm hgV0 fun s₁ s₂ h1 h2 => (hBG s₁ s₂ h1 h2).1
    have hle : ∫⁻ p, ENNReal.ofReal (gV p)
        ∂((ageμ c (-3 / 2)).restrict (Ioo 0 δ ×ˢ univ)) ≤
        ∫⁻ p, ENNReal.ofReal (vnorm2 (d p) ^ 2)
        ∂((ageμ c (-3 / 2)).restrict (Ioo 0 δ ×ˢ univ)) := by
      refine lintegral_mono_ae ?_
      have hm : MeasurableSet (Ioo (0 : ℝ) δ ×ˢ (univ : Set (ℝ × ℝ))) :=
        measurableSet_Ioo.prod MeasurableSet.univ
      filter_upwards [ae_restrict_mem hm] with p hp
      have hp1 : 0 < p.1 := hp.1.1
      apply ENNReal.ofReal_le_ofReal
      have hle1 : vnorm2 (gainConj γ ν b' p) ≤ vnorm2 (b' p) :=
        vnorm2_smul_le (inv_nonneg.2 (Real.exp_pos _).le) (gainG_inv_le_one hγ hν0 hp1) _
      have hle2 : vnorm2 (b' p) ≤ vnorm2 (d p) := by
        show vnorm2 (truncVec H' d p) ≤ vnorm2 (d p)
        rw [vnorm2_truncVec_eq]
        split_ifs
        · exact le_rfl
        · exact Real.sqrt_nonneg _
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (hle1.trans hle2) 2
    have hlt := hle.trans_lt hfin
    rw [h2 δ] at hlt
    have hc' : ENNReal.ofReal c⁻¹ ≠ 0 := by simpa using inv_pos.2 hc
    rcases ENNReal.mul_lt_top_iff.1 hlt with h | h | h
    · exact h.2
    · exact absurd h hc'
    · simp [A, h]
  -- Vanishing of cutG on every compact subinterval [a, B] ⊂ (0, H')
  obtain ⟨Kσ, hKσ0, hKσ⟩ := sigma_deriv_bound
  set C_ramp : ℝ := 2 * Kσ + 1
  have hC_ramp : 0 < C_ramp := by unfold C_ramp; linarith
  have hIcc_cutG_zero : ∀ a B : ℝ, 0 < a → a < B → B < H' →
      ∫⁻ s in Icc a B, ENNReal.ofReal (cutG (1 / 4) ν ν A N s) = 0 := by
    intro a B ha haB hBH'
    set B₂ : ℝ := (B + H') / 2
    have hBB₂ : B < B₂ := by unfold B₂; linarith
    have hB₂H' : B₂ < H' := by unfold B₂; linarith
    have hB0 : 0 < B := lt_trans ha haB
    have hB₂0 : 0 < B₂ := lt_trans hB0 hBB₂
    obtain ⟨M, hM0, hM⟩ := core_trainVel_bound_le tr htr hB₂0.le
    set L : ℝ := ν⁻¹ * (8 * M ^ 2)
    have hL0 : 0 ≤ L := by unfold L; positivity
    have hQA_ae : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), s ≤ B₂ → Q s ≤ 8 * M ^ 2 * A s := by
      filter_upwards [hVslice, hQslice] with s hsV hsQ hsB
      show ∫ x in B0579.cell c, gQ (s, x) ≤ 8 * M ^ 2 * ∫ x in B0579.cell c, gV (s, x)
      rw [← integral_const_mul]
      refine integral_mono hsQ (hsV.const_mul (8 * M ^ 2)) fun x => ?_
      show tnorm2 (gainConj γ ν F' (s, x)) ^ 2 ≤ 8 * M ^ 2 * vnorm2 (gainConj γ ν b' (s, x)) ^ 2
      rw [hF'_eq, core_gainConj_neg_flatMult]
      exact core_tnorm2_neg_flatMult_sq_le tr (gainConj γ ν b') hM0 (hM s hsB x)
    have hdelta : ∀ δ : ℝ, 0 < δ → 2 * δ ≤ a →
        ENNReal.ofReal (Real.exp (-L * B)) *
            (∫⁻ s in Icc a B, ENNReal.ofReal (cutG (1 / 4) ν ν A N s)) ≤
          ENNReal.ofReal (2 * C_ramp) *
            ∫⁻ s in Ioo 0 (3 * δ), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s) := by
      intro δ hδ h2δa
      have hB2 : 2 * δ < B := lt_of_le_of_lt h2δa haB
      have hδB₂ : δ < B₂ := by linarith
      set ψ : ℝ → ℝ := coreExpRamp L δ B B₂
      have hψ_sm : ContDiff ℝ ∞ ψ := coreExpRamp_contDiff L δ B B₂
      have hc1 : ContDiff ℝ 1 ψ := hψ_sm.of_le (by simp)
      have hsupp : tsupport ψ ⊆ Icc δ B₂ := coreExpRamp_tsupport_subset hδ hBB₂
      have hcs : HasCompactSupport ψ :=
        IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hsupp
      have hψ_Ioo : tsupport ψ ⊆ Ioo 0 H' :=
        hsupp.trans fun s hs => ⟨lt_of_lt_of_le hδ hs.1, lt_of_le_of_lt hs.2 hB₂H'⟩
      have hψ0 : ∀ s, 0 ≤ ψ s := coreExpRamp_nonneg L δ B B₂
      have hW_ψ := coreWeightedEnergySmooth hD hγ hψ_sm hcs hψ_Ioo hψ0
      obtain ⟨hint, hle⟩ := cutoff_young (k := 1 / 4) (ν := ν) (α := 1 / 2 + 2 * μ.re)
        (θ := ν) (A := A) (N := N) (M := M_slice) (Q := Q) (ψ := ψ) (a := δ) (b := B₂)
        hν0 (by linarith) (by linarith) hnn
        (hVi δ B₂ hδ hδB₂) (hNi δ B₂ hδ hδB₂) (hQi δ B₂ hδ hδB₂)
        hY hc1 hδ hsupp hψ0 hW_ψ
      have iA12 : Integrable (fun s => ψ s * (s ^ (-1 / 2 : ℝ) * A s))
          (volume.restrict (Ioi (0 : ℝ))) :=
        integrable_cutoff_mul hc1 hδ hsupp (intOn_rpow_mul hδ (hVi δ B₂ hδ hδB₂) _)
      have iQ12 : Integrable (fun s => ψ s * (s ^ (-1 / 2 : ℝ) * Q s))
          (volume.restrict (Ioi (0 : ℝ))) :=
        integrable_cutoff_mul hc1 hδ hsupp (intOn_rpow_mul hδ (hQi δ B₂ hδ hδB₂) _)
      have hDint : Integrable (fun s => deriv ψ s * (s ^ (-1 / 2 : ℝ) * A s))
          (volume.restrict (Ioi (0 : ℝ))) :=
        integrable_contcutoff_mul (hc1.continuous_deriv le_rfl) hδ
          (tsupport_deriv_subset.trans hsupp) (intOn_rpow_mul hδ (hVi δ B₂ hδ hδB₂) _)
      have hQ_le : ν⁻¹ * (∫ s in Ioi (0 : ℝ), ψ s * (s ^ (-1 / 2 : ℝ) * Q s)) ≤
          L * ∫ s in Ioi (0 : ℝ), ψ s * (s ^ (-1 / 2 : ℝ) * A s) := by
        have hint_le : (∫ s in Ioi (0 : ℝ), ψ s * (s ^ (-1 / 2 : ℝ) * Q s)) ≤
            8 * M ^ 2 * ∫ s in Ioi (0 : ℝ), ψ s * (s ^ (-1 / 2 : ℝ) * A s) := by
          rw [← integral_const_mul]
          refine integral_mono_ae iQ12 (iA12.const_mul (8 * M ^ 2)) ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi, hQA_ae] with s hs hsQA
          have hs0 : 0 < s := hs
          by_cases hsB : s ≤ B₂
          · have h1 := hsQA hsB
            have h2 : 0 ≤ ψ s * s ^ (-1 / 2 : ℝ) :=
              mul_nonneg (hψ0 s) (Real.rpow_nonneg hs0.le _)
            nlinarith [mul_le_mul_of_nonneg_left h1 h2]
          · have hnot : s ∉ Icc δ B₂ := fun h => hsB h.2
            have hψz : ψ s = 0 := coreExpRamp_eq_zero_of_not_mem hδ hBB₂ hnot
            simp [hψz]
        calc ν⁻¹ * (∫ s in Ioi (0 : ℝ), ψ s * (s ^ (-1 / 2 : ℝ) * Q s))
            ≤ ν⁻¹ * (8 * M ^ 2 * ∫ s in Ioi (0 : ℝ), ψ s * (s ^ (-1 / 2 : ℝ) * A s)) :=
              mul_le_mul_of_nonneg_left hint_le (by positivity)
          _ = L * ∫ s in Ioi (0 : ℝ), ψ s * (s ^ (-1 / 2 : ℝ) * A s) := by
              unfold L; ring
      have hcomb_int : Integrable (fun s => (deriv ψ s + L * ψ s) * (s ^ (-1 / 2 : ℝ) * A s))
          (volume.restrict (Ioi (0 : ℝ))) := by
        refine (hDint.add (iA12.const_mul L)).congr (Eventually.of_forall fun s => ?_)
        simp only [Pi.add_apply]; ring
      have hcomb_eq : (∫ s in Ioi (0 : ℝ), deriv ψ s * (s ^ (-1 / 2 : ℝ) * A s)) +
            L * (∫ s in Ioi (0 : ℝ), ψ s * (s ^ (-1 / 2 : ℝ) * A s)) =
          ∫ s in Ioi (0 : ℝ), (deriv ψ s + L * ψ s) * (s ^ (-1 / 2 : ℝ) * A s) := by
        rw [← integral_const_mul, ← integral_add hDint (iA12.const_mul L)]
        congr 1; funext s; ring
      have hle' : ∫ s in Ioi (0 : ℝ), ψ s * cutG (1 / 4) ν ν A N s ≤
          ∫ s in Ioi (0 : ℝ), (deriv ψ s + L * ψ s) * (s ^ (-1 / 2 : ℝ) * A s) := by
        linarith [hle, hQ_le, hcomb_eq]
      have hcutG_nn : ∀ s > 0, 0 ≤ cutG (1 / 4) ν ν A N s := by
        intro s hs
        unfold cutG
        have h1 : 0 ≤ s ^ (-3 / 2 : ℝ) * A s :=
          mul_nonneg (Real.rpow_nonneg hs.le _) (hnn s).1
        have h2 : 0 ≤ s ^ (-1 / 2 : ℝ) * N s :=
          mul_nonneg (Real.rpow_nonneg hs.le _) (hnn s).2.1
        nlinarith
      have s2 : ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (ψ s * cutG (1 / 4) ν ν A N s) =
          ENNReal.ofReal (∫ s in Ioi (0 : ℝ), ψ s * cutG (1 / 4) ν ν A N s) := by
        refine (ofReal_integral_eq_lintegral_ofReal hint ?_).symm
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        exact mul_nonneg (hψ0 s) (hcutG_nn s hs)
      have hLHS_le : ENNReal.ofReal (Real.exp (-L * B)) *
            (∫⁻ s in Icc a B, ENNReal.ofReal (cutG (1 / 4) ν ν A N s)) ≤
          ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (ψ s * cutG (1 / 4) ν ν A N s) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine (setLIntegral_mono' measurableSet_Icc fun s hs => ?_).trans
          (lintegral_mono_set (fun s hs => lt_of_lt_of_le ha hs.1))
        have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
        have hsIcc : s ∈ Icc (2 * δ) B := ⟨le_trans h2δa hs.1, hs.2⟩
        have hψ_ge : Real.exp (-L * B) ≤ ψ s := coreExpRamp_ge_on_Icc hL0 hδ hBB₂ hsIcc
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hψ_ge (hcutG_nn s hs0))
      have hRHS_le := coreExpRamp_rhs_bound hδ hC_ramp (fun s => (hnn s).1)
        (coreExpRamp_deriv_add_le hKσ0 hKσ hL0 hδ hB2 hBB₂) hcomb_int
      exact hLHS_le.trans (s2.le.trans ((ENNReal.ofReal_le_ofReal hle').trans hRHS_le))
    -- Take δ_n = a / (3 * (n + 1)) → 0
    set d_seq : ℕ → ℝ := fun n => a / (3 * ((n : ℝ) + 1))
    have hdpos : ∀ n : ℕ, 0 < d_seq n := fun n => by unfold d_seq; positivity
    have hd2a : ∀ n : ℕ, 2 * d_seq n ≤ a := by
      intro n
      unfold d_seq
      have h1 : (2 : ℝ) * a ≤ a * (3 * ((n : ℝ) + 1)) := by
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith
      rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
      exact h1
    have hdlim : Tendsto (fun n : ℕ => 3 * d_seq n) atTop (𝓝 0) := by
      have heq : (fun n : ℕ => 3 * d_seq n) = fun n : ℕ => a * (1 / ((n : ℝ) + 1)) := by
        funext n; unfold d_seq; field_simp
      rw [heq]
      have h0 := (tendsto_const_nhds (x := a)).mul tendsto_one_div_add_atTop_nhds_zero_nat
      rwa [mul_zero] at h0
    have hE : Tendsto (fun n => ∫⁻ s in Ioo 0 (3 * d_seq n), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s))
        atTop (𝓝 0) := by
      have hE0 : Tendsto (fun n => ∫⁻ s in Ioo 0 (3 * d_seq n), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s)
          ∂(volume.restrict (Ioo 0 δ0))) atTop (𝓝 0) := by
        refine tendsto_setLIntegral_zero (μ := volume.restrict (Ioo 0 δ0))
          (f := fun s => ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s)) hfinA.ne ?_
        have hup : Tendsto (fun n => ENNReal.ofReal (3 * d_seq n)) atTop (𝓝 0) := by
          simpa using ENNReal.tendsto_ofReal hdlim
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
          (fun _ => zero_le) (fun n => ?_)
        calc (volume.restrict (Ioo 0 δ0)) (Ioo 0 (3 * d_seq n)) ≤ volume (Ioo 0 (3 * d_seq n)) :=
              Measure.restrict_le_self _
          _ = ENNReal.ofReal (3 * d_seq n) := by simp
      have hev : ∀ᶠ n : ℕ in atTop, 3 * d_seq n < δ0 :=
        (tendsto_order.1 hdlim).2 δ0 (by simpa using hδ0)
      refine hE0.congr' (hev.mono fun n hn => ?_)
      rw [Measure.restrict_restrict measurableSet_Ioo,
        Set.inter_eq_left.2 (Ioo_subset_Ioo le_rfl hn.le)]
    have hRHS_lim : Tendsto (fun n => ENNReal.ofReal (2 * C_ramp) *
        ∫⁻ s in Ioo 0 (3 * d_seq n), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s)) atTop (𝓝 0) := by
      have h0 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (2 * C_ramp)) hE
        (Or.inr ENNReal.ofReal_ne_top)
      rwa [mul_zero] at h0
    have hle_zero : ENNReal.ofReal (Real.exp (-L * B)) *
        (∫⁻ s in Icc a B, ENNReal.ofReal (cutG (1 / 4) ν ν A N s)) ≤ 0 :=
      ge_of_tendsto' hRHS_lim fun n => hdelta (d_seq n) (hdpos n) (hd2a n)
    have hmul_zero : ENNReal.ofReal (Real.exp (-L * B)) *
        (∫⁻ s in Icc a B, ENNReal.ofReal (cutG (1 / 4) ν ν A N s)) = 0 :=
      le_antisymm hle_zero zero_le
    have hpos : ENNReal.ofReal (Real.exp (-L * B)) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      positivity
    exact (mul_eq_zero.1 hmul_zero).resolve_left hpos
  -- Deduce vanishing of A and N on [a, B] ⊂ (0, H')
  have hIcc_A_zero : ∀ a B : ℝ, 0 < a → a < B → B < H' →
      ∫⁻ s in Icc a B, ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s) = 0 := by
    intro a B ha haB hBH'
    have hle : ENNReal.ofReal (1 / 2) *
          (∫⁻ s in Icc a B, ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s)) ≤
        ∫⁻ s in Icc a B, ENNReal.ofReal (cutG (1 / 4) ν ν A N s) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
      have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
      rw [← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      unfold cutG
      have h2 : 0 ≤ s ^ (-1 / 2 : ℝ) * N s :=
        mul_nonneg (Real.rpow_nonneg hs0.le _) (hnn s).2.1
      nlinarith
    rw [hIcc_cutG_zero a B ha haB hBH'] at hle
    have hmul_zero := le_antisymm hle zero_le
    have hpos : ENNReal.ofReal (1 / 2 : ℝ) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      norm_num
    exact (mul_eq_zero.1 hmul_zero).resolve_left hpos
  have hIcc_N_zero : ∀ a B : ℝ, 0 < a → a < B → B < H' →
      ∫⁻ s in Icc a B, ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * N s) = 0 := by
    intro a B ha haB hBH'
    have hle : ENNReal.ofReal ν *
          (∫⁻ s in Icc a B, ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * N s)) ≤
        ∫⁻ s in Icc a B, ENNReal.ofReal (cutG (1 / 4) ν ν A N s) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
      have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
      rw [← ENNReal.ofReal_mul hν0.le]
      apply ENNReal.ofReal_le_ofReal
      unfold cutG
      have h1 : 0 ≤ s ^ (-3 / 2 : ℝ) * A s :=
        mul_nonneg (Real.rpow_nonneg hs0.le _) (hnn s).1
      nlinarith
    rw [hIcc_cutG_zero a B ha haB hBH'] at hle
    have hmul_zero := le_antisymm hle zero_le
    have hpos : ENNReal.ofReal ν ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact hν0
    exact (mul_eq_zero.1 hmul_zero).resolve_left hpos
  -- Vanishing of A and N on Ici H'
  have hIci_A : ∀ s ∈ Ici H', ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s) = 0 := by
    intro s hs
    have hs' : ¬ s < H' := not_lt.2 hs
    have hA0 : A s = 0 := by
      show ∫ x in B0579.cell c, vnorm2 (gainConj γ ν (truncVec H' d) (s, x)) ^ 2 = 0
      have hpt : ∀ x, vnorm2 (gainConj γ ν (truncVec H' d) (s, x)) ^ 2 = 0 := by
        intro x
        rw [gainConj_truncVec, vnorm2_truncVec_eq, if_neg hs', sq, mul_zero]
      simp [hpt]
    simp [hA0]
  have hIci_N : ∀ s ∈ Ici H', ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * N s) = 0 := by
    intro s hs
    have hs' : ¬ s < H' := not_lt.2 hs
    have hN0 : N s = 0 := by
      show ∫ x in B0579.cell c, tnorm2 (gainConj γ ν (truncTen H' Gd) (s, x)) ^ 2 = 0
      have hpt : ∀ x, tnorm2 (gainConj γ ν (truncTen H' Gd) (s, x)) ^ 2 = 0 := by
        intro x
        rw [gainConj_truncTen, tnorm2_truncTen_eq, if_neg hs', sq, mul_zero]
      simp [hpt]
    simp [hN0]
  have hIoi_A : ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s) = 0 :=
    lintegral_Ioi_eq_zero_of_Icc_of_Ici hH'0 _ hIcc_A_zero hIci_A
  have hIoi_N : ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * N s) = 0 :=
    lintegral_Ioi_eq_zero_of_Icc_of_Ici hH'0 _ hIcc_N_zero hIci_N
  -- Conclude hCalNorm = 0 and tCalNorm = 0 for (b', G')
  refine ⟨?_, ?_⟩
  · have eH : hCalNorm c (gainConj γ ν b') ^ 2 = ENNReal.ofReal c⁻¹ *
        ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s) := by
      rw [normSq.1]
      exact (ageSlice c (-3 / 2) gV hc hgVm hgV0 fun s₁ s₂ h1 h2 => (hBG s₁ s₂ h1 h2).1).1
    rw [hIoi_A, mul_zero] at eH
    exact sq_eq_zero_iff.1 eH
  · have eT : tCalNorm c (gainConj γ ν G') ^ 2 = ENNReal.ofReal c⁻¹ *
        ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * N s) := by
      rw [normSq.2]
      exact (ageSlice c (-1 / 2) gN hc hgNm hgN0 fun s₁ s₂ h1 h2 => (hBG s₁ s₂ h1 h2).2).1
    rw [hIoi_N, mul_zero] at eT
    exact sq_eq_zero_iff.1 eT

/-! ## Main theorem: `CoreCausalHomogeneousZero` -/

theorem coreCausalHomogeneousZero : UnforcedLeray.Short.IIIa.CoreCausalHomogeneousZero := by
  intro P hP K hK ν H hν0 hH0 tr htr μ hμ d Gd hsol
  let c : ℝ := ν ^ (-2 : ℝ)
  let γ : ℝ := P.eigenvalue.re
  have hγ : 0 ≤ γ := hP.eigenpair.re_pos.le
  have hμre : 0 < μ.re := (hK.2 μ hμ).1
  refine ⟨?_, ?_⟩
  · refine eLpNorm_restrict_Iio_eq_zero_of_lt hH0 (fun p => vnorm2 (gainConj γ ν d p))
      (fun _ => Real.sqrt_nonneg _) (fun H' hH' => ?_)
    have hle : hCalNormOn c H' (gainConj γ ν d) ≤
        hCalNorm c (gainConj γ ν (truncVec H' d)) := by
      rw [gainConj_truncVec]
      exact hCalNormOn_le_hCalNorm_truncVec c H' (gainConj γ ν d)
    rw [(coreTrunc_norms_zero hν0 hH' hγ hμre tr htr hsol).1] at hle
    exact le_antisymm hle zero_le
  · refine eLpNorm_restrict_Iio_eq_zero_of_lt hH0 (fun p => tnorm2 (gainConj γ ν Gd p))
      (fun _ => Real.sqrt_nonneg _) (fun H' hH' => ?_)
    have hle : tCalNormOn c H' (gainConj γ ν Gd) ≤
        tCalNorm c (gainConj γ ν (truncTen H' Gd)) := by
      rw [gainConj_truncTen]
      exact tCalNormOn_le_tCalNorm_truncTen c H' (gainConj γ ν Gd)
    rw [(coreTrunc_norms_zero hν0 hH' hγ hμre tr htr hsol).2] at hle
    exact le_antisymm hle zero_le

end UnforcedLeray.Short.IIIa
