import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_of
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.CausalLimitAE.CompleteH
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.CausalLimitAE.CompleteT
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.CausalLimitAE.SliceAE
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.CausalLimitAE.EnergyPerturb
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.CausalLimitAE.SliceClauses

/-!
# Closure of the energy class under `H ∩ H_T`-Cauchy limits (`PartIII-b:C/flatset/col/7/1/2`)

Source of record `the November 2 reference manuscript` 3426-3430.  The Part III-a
limit machinery for causal solutions (`causalCompleteH`, `causalCompleteT`, `causalSliceAE`,
`causalEnergyPerturb`, `causalSliceClauses`, all proved) is applied with the gain `γ = 0`
(`gainG 0 ν s = 1`).  The Cauchy sequence is turned into a null sequence `a n` dominating all
differences; the limit `b'` is identified with `v` through the triangle inequality in `H`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa

theorem gc0 {E : Type*} [AddCommGroup E] [Module ℝ E] (f : ℝ × (ℝ × ℝ) → E) :
    gainConj 0 1 f = f := by
  funext p
  simp [gainConj, gainG]

theorem eLpNorm_two_eq {α : Type*} [MeasurableSpace α] (μ : Measure α) (g : α → ℝ)
    (hg : ∀ x, 0 ≤ g x) :
    eLpNorm g 2 μ = (∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂μ) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by simp)]
  simp only [ENNReal.toReal_ofNat]
  congr 1
  refine lintegral_congr fun x => ?_
  rw [Real.enorm_eq_ofReal (hg x), ENNReal.ofReal_rpow_of_nonneg (hg x) (by norm_num)]
  norm_num

theorem hnorm_eq (c : ℝ) (f : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) :
    hCalNorm c f = (∫⁻ p, ENNReal.ofReal (vnorm2 (f p) ^ 2) ∂(ageμ c (-3 / 2))) ^ (1 / 2 : ℝ) :=
  eLpNorm_two_eq _ _ fun _ => Real.sqrt_nonneg _

theorem tnorm_eq (c : ℝ) (f : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) :
    tCalNorm c f = (∫⁻ p, ENNReal.ofReal (tnorm2 (f p) ^ 2) ∂(ageμ c (-1 / 2))) ^ (1 / 2 : ℝ) :=
  eLpNorm_two_eq _ _ fun _ => Real.sqrt_nonneg _

theorem vnorm2_swap (x y : Fin 2 → ℂ) : vnorm2 (fun i => x i - y i) = vnorm2 (fun i => y i - x i) := by
  have h1 := ch_norm_toLp_sub x y
  have h2 := ch_norm_toLp_sub y x
  have : (fun i => x i - y i) = x - y := rfl
  have h3 : (fun i => y i - x i) = y - x := rfl
  rw [this, h3, ← h1, ← h2, norm_sub_rev]

theorem tnorm2_swap (x y : Fin 2 → Fin 2 → ℂ) :
    tnorm2 (fun i j => x i j - y i j) = tnorm2 (fun i j => y i j - x i j) := by
  unfold tnorm2
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [norm_sub_rev]

theorem hnorm_swap (c : ℝ) (x y : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) :
    hCalNorm c (fun p i => x p i - y p i) = hCalNorm c (fun p i => y p i - x p i) := by
  rw [hnorm_eq, hnorm_eq]
  congr 1
  exact lintegral_congr fun p => by rw [vnorm2_swap]

theorem tnorm_swap (c : ℝ) (x y : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) :
    tCalNorm c (fun p i j => x p i j - y p i j) = tCalNorm c (fun p i j => y p i j - x p i j) := by
  rw [tnorm_eq, tnorm_eq]
  congr 1
  exact lintegral_congr fun p => by rw [tnorm2_swap]

theorem vnorm2_tri (x y z : Fin 2 → ℂ) :
    vnorm2 (fun i => x i - z i) ≤ vnorm2 (fun i => x i - y i) + vnorm2 (fun i => y i - z i) := by
  have h1 := ch_norm_toLp_sub x y
  have h2 := ch_norm_toLp_sub y z
  have h3 := ch_norm_toLp_sub x z
  have e1 : (fun i => x i - y i) = x - y := rfl
  have e2 : (fun i => y i - z i) = y - z := rfl
  have e3 : (fun i => x i - z i) = x - z := rfl
  rw [e1, e2, e3, ← h1, ← h2, ← h3]
  exact norm_sub_le_norm_sub_add_norm_sub _ _ _

theorem vnorm2_eq_zero {x : Fin 2 → ℂ} (h : vnorm2 x = 0) : x = 0 := by
  unfold vnorm2 at h
  rw [Real.sqrt_eq_zero (Finset.sum_nonneg fun i _ => sq_nonneg _)] at h
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖x i‖)).1 h i (Finset.mem_univ i)
  simpa using this

/-- A null sequence dominating all pairwise differences of an `H ∩ H_T`-Cauchy sequence. -/
theorem cauchy_a (c : ℝ) (b : ℕ → Chart → Fin 2 → ℂ) (G : ℕ → Chart → Fin 2 → Fin 2 → ℂ)
    (hC : EnergyCauchy c b G) :
    ∃ a : ℕ → ℝ≥0∞, Tendsto a atTop (𝓝 0) ∧ ∀ n m,
      hCalNorm c (fun p i => b n p i - b m p i) ≤ a n + a m ∧
      tCalNorm c (fun p i j => G n p i j - G m p i j) ≤ a n + a m := by
  set Q : ℕ → ℕ → ℝ≥0∞ := fun m n =>
    ∫⁻ p, ENNReal.ofReal (vnorm2 (b m p - b n p) ^ 2) ∂(ageμ c (-3 / 2)) +
      ∫⁻ p, ENNReal.ofReal (tnorm2 (G m p - G n p) ^ 2) ∂(ageμ c (-1 / 2)) with hQ
  refine ⟨fun n => ⨆ m, ⨆ (_ : n ≤ m), (Q n m) ^ (1 / 2 : ℝ), ?_, ?_⟩
  · rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    by_cases hεt : ε = ⊤
    · exact Eventually.of_forall fun n => hεt ▸ le_top
    have hr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεt
    obtain ⟨N, hN⟩ := hC (ε.toReal ^ 2) (by positivity)
    rw [eventually_atTop]
    refine ⟨N, fun n hn => iSup₂_le fun m hm => ?_⟩
    have h1 : Q n m < ENNReal.ofReal (ε.toReal ^ 2) := hN n hn m (hn.trans hm)
    calc Q n m ^ (1 / 2 : ℝ) ≤ (ENNReal.ofReal (ε.toReal ^ 2)) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow h1.le (by norm_num)
      _ = ENNReal.ofReal ε.toReal := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
          congr 1
          rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
          norm_num
      _ = ε := ENNReal.ofReal_toReal hεt
  · have key : ∀ n m, n ≤ m →
        hCalNorm c (fun p i => b n p i - b m p i) ≤ ⨆ m', ⨆ (_ : n ≤ m'), (Q n m') ^ (1 / 2 : ℝ) ∧
        tCalNorm c (fun p i j => G n p i j - G m p i j) ≤
          ⨆ m', ⨆ (_ : n ≤ m'), (Q n m') ^ (1 / 2 : ℝ) := by
      intro n m hnm
      have hle : (⨆ m', ⨆ (_ : n ≤ m'), (Q n m') ^ (1 / 2 : ℝ)) ≥ (Q n m) ^ (1 / 2 : ℝ) :=
        le_iSup₂ (f := fun m' (_ : n ≤ m') => (Q n m') ^ (1 / 2 : ℝ)) m hnm
      constructor
      · refine le_trans ?_ hle
        rw [hnorm_eq]
        exact ENNReal.rpow_le_rpow le_self_add (by norm_num)
      · refine le_trans ?_ hle
        rw [tnorm_eq]
        exact ENNReal.rpow_le_rpow le_add_self (by norm_num)
    intro n m
    rcases le_total n m with h | h
    · exact ⟨(key n m h).1.trans le_self_add, (key n m h).2.trans le_self_add⟩
    · have h1 := hnorm_swap c (b n) (b m)
      have h2 := tnorm_swap c (G n) (G m)
      rw [h1, h2, add_comm]
      exact ⟨(key m n h).1.trans le_self_add, (key m n h).2.trans le_self_add⟩

set_option maxHeartbeats 2000000 in
theorem energyCauchyLimit : EnergyCauchyLimit := by
  intro c hc b G v hE hC hH hvm
  obtain ⟨a, ha, hab⟩ := cauchy_a c b G hC
  have hbm : ∀ n i, Measurable fun p => b n p i := fun n i => (hE n).measurable i
  have hGm : ∀ n i j, Measurable fun p => G n p i j := fun n i j => (hE n).gradMeasurable i j
  obtain ⟨b', hb'm, hb'T⟩ := causalCompleteH c 1 0 hc one_pos b hbm 1 a ENNReal.one_ne_top ha
    ⟨0, fun n m _ _ => by rw [gc0, one_mul]; exact (hab n m).1⟩
  obtain ⟨G', hG'm, hG'T⟩ := causalCompleteT c 1 0 hc one_pos G hGm 1 a ENNReal.one_ne_top ha
    ⟨0, fun n m _ _ => by rw [gc0, one_mul]; exact (hab n m).2⟩
  obtain ⟨φ, hφ, hae⟩ := causalSliceAE c 1 0 hc one_pos b G b' G' hbm hb'm hGm hG'm hb'T hG'T
  obtain ⟨N, hNb, hNG⟩ : ∃ N : ℕ,
      hCalNorm c (gainConj 0 1 (fun p i => b N p i - b' p i)) < ⊤ ∧
      tCalNorm c (gainConj 0 1 (fun p i j => G N p i j - G' p i j)) < ⊤ :=
    ((hb'T.eventually (gt_mem_nhds ENNReal.zero_lt_top)).and
      (hG'T.eventually (gt_mem_nhds ENNReal.zero_lt_top))).exists
  obtain ⟨hEn, hZe⟩ := causalEnergyPerturb c 1 0 hc one_pos (b N) b' (G N) G' hb'm hG'm (hbm N)
    (hGm N) (hE N).energyLoc (hE N).zeroEntrance hNb hNG
  have hcl := causalSliceClauses c hc (fun n => b (φ n)) (fun n => G (φ n)) b' G'
    (fun n => hbm _) hb'm (fun n => hGm _) hG'm (fun n => (hE (φ n)).energyLoc)
    (fun n => (hE (φ n)).divFree) (fun n => (hE (φ n)).weakGrad) hae
  have hcl' := (ae_restrict_iff' measurableSet_Ioi).1 hcl
  refine ⟨b', G', ?_, ⟨hb'm, hG'm, hEn, hZe, ?_, ?_⟩⟩
  · -- `b' = v` a.e.
    have hT1 : ∀ n, hCalNorm c (fun p i => b' p i - b n p i) =
        hCalNorm c (gainConj 0 1 (fun p i => b n p i - b' p i)) := by
      intro n
      rw [gc0]
      exact hnorm_swap c b' (b n)
    have hT1' : Tendsto (fun n => hCalNorm c (fun p i => b' p i - b n p i)) atTop (𝓝 0) := by
      simpa only [hT1] using hb'T
    have hT2 : Tendsto (fun n => hCalNorm c (fun p i => b n p i - v p i)) atTop (𝓝 0) := by
      have := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0 |>.comp hH
      have h0 : (0 : ℝ≥0∞) ^ (1 / 2 : ℝ) = 0 := ENNReal.zero_rpow_of_pos (by norm_num)
      rw [h0] at this
      simp only [hnorm_eq]
      exact this
    have hvmeas : AEMeasurable (fun p => (fun i => b' p i - v p i)) (ageμ c (-3 / 2)) :=
      aemeasurable_pi_iff.2 fun i => (hb'm i).aemeasurable.sub (hvm i)
    have hv2 : AEMeasurable (fun p => vnorm2 (fun i => b' p i - v p i)) (ageμ c (-3 / 2)) := by
      have hcont : Continuous fun x : Fin 2 → ℂ => vnorm2 x := by
        unfold vnorm2
        fun_prop
      exact hcont.measurable.comp_aemeasurable hvmeas
    have hmeasn : ∀ n, AEMeasurable (fun p => vnorm2 (fun i => b n p i - v p i))
        (ageμ c (-3 / 2)) := by
      intro n
      have hcont : Continuous fun x : Fin 2 → ℂ => vnorm2 x := by
        unfold vnorm2
        fun_prop
      exact hcont.measurable.comp_aemeasurable
        (aemeasurable_pi_iff.2 fun i => (hbm n i).aemeasurable.sub (hvm i))
    have hmeasn' : ∀ n, AEMeasurable (fun p => vnorm2 (fun i => b' p i - b n p i))
        (ageμ c (-3 / 2)) := by
      intro n
      have hcont : Continuous fun x : Fin 2 → ℂ => vnorm2 x := by
        unfold vnorm2
        fun_prop
      exact hcont.measurable.comp_aemeasurable
        (aemeasurable_pi_iff.2 fun i => (hb'm i).aemeasurable.sub (hbm n i).aemeasurable)
    have hle : ∀ n, hCalNorm c (fun p i => b' p i - v p i) ≤
        hCalNorm c (fun p i => b' p i - b n p i) + hCalNorm c (fun p i => b n p i - v p i) := by
      intro n
      unfold hCalNorm
      have hpt : ∀ p, ‖vnorm2 (fun i => b' p i - v p i)‖ ≤
          ‖vnorm2 (fun i => b' p i - b n p i) + vnorm2 (fun i => b n p i - v p i)‖ := by
        intro p
        have h0 := vnorm2_tri (b' p) (b n p) (v p)
        have n1 : 0 ≤ vnorm2 (fun i => b' p i - v p i) := Real.sqrt_nonneg _
        have n2 : 0 ≤ vnorm2 (fun i => b' p i - b n p i) := Real.sqrt_nonneg _
        have n3 : 0 ≤ vnorm2 (fun i => b n p i - v p i) := Real.sqrt_nonneg _
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg n1, abs_of_nonneg (add_nonneg n2 n3)]
        exact h0
      refine (eLpNorm_mono (f := fun p => vnorm2 (fun i => b' p i - v p i))
        (g := fun p => vnorm2 (fun i => b' p i - b n p i) + vnorm2 (fun i => b n p i - v p i))
        hpt).trans ?_
      exact eLpNorm_add_le (hmeasn' n).aestronglyMeasurable (hmeasn n).aestronglyMeasurable
        (by norm_num)
    have hz : hCalNorm c (fun p i => b' p i - v p i) ≤ 0 := by
      have hs := hT1'.add hT2
      rw [add_zero] at hs
      exact ge_of_tendsto hs (Eventually.of_forall hle)
    have hz' : hCalNorm c (fun p i => b' p i - v p i) = 0 := le_antisymm hz bot_le
    unfold hCalNorm at hz'
    have := (eLpNorm_eq_zero_iff hv2.aestronglyMeasurable (by norm_num)).1 hz'
    filter_upwards [this] with p hp
    have hp' : vnorm2 (fun i => b' p i - v p i) = 0 := hp
    have := vnorm2_eq_zero hp'
    funext i
    have := congrFun this i
    simpa [sub_eq_zero] using this
  · filter_upwards [hcl'] with s hs hs0
    exact (hs (mem_Ioi.2 hs0)).1
  · filter_upwards [hcl'] with s hs hs0
    exact (hs (mem_Ioi.2 hs0)).2

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
