import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T19_3
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.MollLimit.AeGood
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.MollLimit.LocInt
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.CoreImpliesWeighted.EnergyLocInt

/-!
# Helper 1 for `PartIII-a:T19/3/4`: core truncation data on `(0, H')`

Source of record: `the November 2 reference manuscript` (SP), lines 3541-3545.
Truncating a core solution `(d, Gd)` of `IsCoreCausalSolution c ν H μ (trainVel tr) 0 d Gd` at
`H' ∈ (0, H)` yields globally locally `L²` fields `(F', b', G')` on `(0, ∞) × cell c` that satisfy
the free weak equation against all flat tests vanishing on `[H₀, ∞)` for any `H₀ < H'`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Truncation of a vector field on `ℝ × ℝ²` to ages `p.1 < H'`. -/
def truncVec (H' : ℝ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (p : ℝ × (ℝ × ℝ)) (i : Fin 2) : ℂ :=
  if p.1 < H' then b p i else 0

/-- Truncation of a tensor field on `ℝ × ℝ²` to ages `p.1 < H'`. -/
def truncTen (H' : ℝ) (T : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (p : ℝ × (ℝ × ℝ)) (i j : Fin 2) : ℂ :=
  if p.1 < H' then T p i j else 0

/-- Standing data for a core solution truncated at `H' > 0`: global local `L²` bounds, slice
divergence-freeness and weak gradient on all `s > 0`, and the free weak equation for flat tests
vanishing on `[H₀, ∞)` for any `H₀ < H'`. -/
structure CoreTruncData (c ν H' : ℝ) (μ : ℂ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) : Prop where
  pos_c : 0 < c
  pos_ν : 0 < ν
  pos_H' : 0 < H'
  l2loc : L2locTensor c F
  meas : ∀ i j, Measurable fun p => F p i j
  measurable : ∀ i, Measurable fun p => b p i
  gradMeasurable : ∀ i j, Measurable fun p => G p i j
  energyLoc : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
    ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) < ⊤
  divFree : ∀ s, 0 < s → ∀ ψ, B0579.IsCylTest c ψ →
    ∫ x in B0579.cell c, (b (s, x) 0 * (B0579.pd 0 ψ x : ℂ) + b (s, x) 1 * (B0579.pd 1 ψ x : ℂ)) = 0
  weakGrad : ∀ s, 0 < s → ∀ i j,
    HasWeakCellDerivC c j (fun x => b (s, x) i) (fun x => G (s, x) i j)
  integrable_core : ∀ H₀ < H', ∀ Φ, IsFlatTest c Φ → (∀ s x i, H₀ ≤ s → Φ s x i = 0) →
    IntegrableOn (flatIntegrand ν μ (fun _ _ _ => 0) F b Φ) (Ioi (0 : ℝ) ×ˢ B0579.cell c)
  weak_core : ∀ H₀ < H', ∀ Φ, IsFlatTest c Φ → (∀ s x i, H₀ ≤ s → Φ s x i = 0) →
    ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, flatIntegrand ν μ (fun _ _ _ => 0) F b Φ p = 0

/-- On `s ≤ S` (`0 ≤ S`), a BUC train velocity `trainVel tr` has components uniformly bounded by
some `M ≥ 0`. -/
theorem core_trainVel_bound_le {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr) {S : ℝ} (hS : 0 ≤ S) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s ≤ S, ∀ x : ℝ × ℝ, ∀ i : Fin 2,
      ‖(trainVel tr s x i : ℂ)‖ ≤ M := by
  obtain ⟨M₀, hM₀⟩ := htr.sup_bound hS
  refine ⟨max M₀ 0, le_max_right _ _, fun s hs x i => ?_⟩
  rw [Complex.norm_real]
  unfold trainVel
  split_ifs with hs0
  · have h1 : ‖tr.v s x i‖ ≤ ‖tr.v s x‖ := PiLp.norm_apply_le (tr.v s x) i
    exact (h1.trans (hM₀ s ⟨hs0, hs⟩ x)).trans (le_max_left _ _)
  · simp

/-- Pointwise quadratic Frobenius bound for `-flatMult tr u`. -/
theorem core_tnorm2_neg_flatMult_sq_le {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    (u : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) {p : ℝ × (ℝ × ℝ)} {M : ℝ} (_hM0 : 0 ≤ M)
    (hM : ∀ i : Fin 2, ‖(trainVel tr p.1 p.2 i : ℂ)‖ ≤ M) :
    tnorm2 (fun i j => -flatMult tr u p i j) ^ 2 ≤ 8 * M ^ 2 * vnorm2 (u p) ^ 2 := by
  have ht : tnorm2 (fun i j => -flatMult tr u p i j) ^ 2 =
      ∑ i : Fin 2, ∑ j : Fin 2, ‖-flatMult tr u p i j‖ ^ 2 := by
    unfold tnorm2
    exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
  have hv : vnorm2 (u p) ^ 2 = ∑ i : Fin 2, ‖u p i‖ ^ 2 := by
    unfold vnorm2
    exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  rw [ht, hv]
  have hij : ∀ i j : Fin 2, ‖-flatMult tr u p i j‖ ^ 2 ≤
      2 * M ^ 2 * ‖u p j‖ ^ 2 + 2 * M ^ 2 * ‖u p i‖ ^ 2 := by
    intro i j
    have h1 : ‖-flatMult tr u p i j‖ ≤ M * ‖u p j‖ + ‖u p i‖ * M := by
      rw [norm_neg]
      unfold flatMult
      calc ‖(trainVel tr p.1 p.2 i : ℂ) * u p j + u p i * (trainVel tr p.1 p.2 j : ℂ)‖
          ≤ ‖(trainVel tr p.1 p.2 i : ℂ) * u p j‖ + ‖u p i * (trainVel tr p.1 p.2 j : ℂ)‖ :=
            norm_add_le _ _
        _ = ‖(trainVel tr p.1 p.2 i : ℂ)‖ * ‖u p j‖ + ‖u p i‖ * ‖(trainVel tr p.1 p.2 j : ℂ)‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ M * ‖u p j‖ + ‖u p i‖ * M :=
            add_le_add (mul_le_mul_of_nonneg_right (hM i) (norm_nonneg _))
              (mul_le_mul_of_nonneg_left (hM j) (norm_nonneg _))
    have h2 : ‖-flatMult tr u p i j‖ ^ 2 ≤ (M * ‖u p j‖ + ‖u p i‖ * M) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (M * ‖u p j‖ - ‖u p i‖ * M)]
  calc ∑ i : Fin 2, ∑ j : Fin 2, ‖-flatMult tr u p i j‖ ^ 2
      ≤ ∑ i : Fin 2, ∑ j : Fin 2, (2 * M ^ 2 * ‖u p j‖ ^ 2 + 2 * M ^ 2 * ‖u p i‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hij i j
    _ = 8 * M ^ 2 * ∑ i : Fin 2, ‖u p i‖ ^ 2 := by
        simp only [Fin.sum_univ_two]
        ring

theorem core_gainConj_neg_flatMult {ν c : ℝ} (γ : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (u : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) :
    gainConj γ ν (fun p i j => -flatMult tr u p i j) =
      fun p i j => -flatMult tr (gainConj γ ν u) p i j := by
  rw [← gainConj_flatMult γ tr u]
  funext p i j
  simp [gainConj, smul_neg]

theorem vnorm2_truncVec_eq (H' : ℝ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (p : ℝ × (ℝ × ℝ)) :
    vnorm2 (truncVec H' b p) = if p.1 < H' then vnorm2 (b p) else 0 := by
  by_cases hp : p.1 < H'
  · have h : truncVec H' b p = b p := funext fun i => if_pos hp
    rw [h, if_pos hp]
  · have h : truncVec H' b p = 0 := funext fun i => if_neg hp
    rw [h, if_neg hp]
    simp [vnorm2]

theorem tnorm2_truncTen_eq (H' : ℝ) (T : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (p : ℝ × (ℝ × ℝ)) :
    tnorm2 (truncTen H' T p) = if p.1 < H' then tnorm2 (T p) else 0 := by
  by_cases hp : p.1 < H'
  · have h : truncTen H' T p = T p := funext fun i => funext fun j => if_pos hp
    rw [h, if_pos hp]
  · have h : truncTen H' T p = 0 := funext fun i => funext fun j => if_neg hp
    rw [h, if_neg hp]
    simp [tnorm2]

/-- Constructing `CoreTruncData` from a homogeneous core causal solution around `trainVel tr`. -/
theorem coreTruncData_of_coreSol {c ν H H' : ℝ} {μ : ℂ} (hc : 0 < c) (hν : 0 < ν)
    (hH'0 : 0 < H') (hH'H : H' < H) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    {d : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {Gd : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hsol : IsCoreCausalSolution c ν H μ (trainVel tr) (fun _ _ _ => 0) d Gd) :
    CoreTruncData c ν H' μ (truncTen H' (fun p i j => -flatMult tr d p i j))
      (truncVec H' d) (truncTen H' Gd) := by
  let F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ := fun p i j => -flatMult tr d p i j
  have hFm : ∀ i j, Measurable fun p => F p i j :=
    fun i j => (measurable_flatMult tr hsol.measurable i j).neg
  have hmeas_lt : MeasurableSet {p : ℝ × (ℝ × ℝ) | p.1 < H'} := measurable_fst measurableSet_Iio
  have hbm' : ∀ i, Measurable fun p => truncVec H' d p i :=
    fun i => Measurable.ite hmeas_lt (hsol.measurable i) measurable_const
  have hGm' : ∀ i j, Measurable fun p => truncTen H' Gd p i j :=
    fun i j => Measurable.ite hmeas_lt (hsol.gradMeasurable i j) measurable_const
  have hFm' : ∀ i j, Measurable fun p => truncTen H' F p i j :=
    fun i j => Measurable.ite hmeas_lt (hFm i j) measurable_const
  have hEloc : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
        ENNReal.ofReal (vnorm2 (truncVec H' d p) ^ 2 + tnorm2 (truncTen H' Gd p) ^ 2) < ⊤ := by
    intro s₁ s₂ hs₁ hs₂
    by_cases hs₁H' : s₁ < H'
    · have hmeas_box : MeasurableSet (Icc s₁ H' ×ˢ B0579.cell c) :=
        measurableSet_Icc.prod (measurableSet_Ico.prod MeasurableSet.univ)
      have hmeas_box2 : MeasurableSet (Icc s₁ s₂ ×ˢ B0579.cell c) :=
        measurableSet_Icc.prod (measurableSet_Ico.prod MeasurableSet.univ)
      have hle : ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
            ENNReal.ofReal (vnorm2 (truncVec H' d p) ^ 2 + tnorm2 (truncTen H' Gd p) ^ 2) ≤
          ∫⁻ p in Icc s₁ H' ×ˢ B0579.cell c,
            ENNReal.ofReal (vnorm2 (d p) ^ 2 + tnorm2 (Gd p) ^ 2) := by
        rw [← lintegral_indicator hmeas_box2, ← lintegral_indicator hmeas_box]
        refine lintegral_mono fun p => ?_
        by_cases hp : p ∈ Icc s₁ s₂ ×ˢ B0579.cell c
        · rw [indicator_of_mem hp]
          by_cases hpH' : p.1 < H'
          · have hp' : p ∈ Icc s₁ H' ×ˢ B0579.cell c := ⟨⟨hp.1.1, hpH'.le⟩, hp.2⟩
            rw [indicator_of_mem hp', vnorm2_truncVec_eq, tnorm2_truncTen_eq,
              if_pos hpH', if_pos hpH']
          · rw [vnorm2_truncVec_eq, tnorm2_truncTen_eq, if_neg hpH', if_neg hpH']
            simp
        · rw [indicator_of_notMem hp]
          exact zero_le
      exact lt_of_le_of_lt hle (hsol.energyLoc s₁ H' hs₁ hs₁H' hH'H)
    · have hmeas_box2 : MeasurableSet (Icc s₁ s₂ ×ˢ B0579.cell c) :=
        measurableSet_Icc.prod (measurableSet_Ico.prod MeasurableSet.univ)
      have h0 : ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
          ENNReal.ofReal (vnorm2 (truncVec H' d p) ^ 2 + tnorm2 (truncTen H' Gd p) ^ 2) = 0 := by
        refine (setLIntegral_eq_zero_iff hmeas_box2
          (ENNReal.measurable_ofReal.comp
            (((aeg_measurable_vnorm2 hbm').pow_const 2).add
              ((aeg_measurable_tnorm2 hGm').pow_const 2)))).2 (ae_of_all _ fun p hp => ?_)
        have hpH' : ¬ p.1 < H' := not_lt.2 ((not_lt.1 hs₁H').trans hp.1.1)
        dsimp only [Function.comp_apply, Pi.add_apply]
        rw [vnorm2_truncVec_eq, tnorm2_truncTen_eq, if_neg hpH', if_neg hpH']
        simp
      rw [h0]
      exact ENNReal.zero_lt_top
  have hFloc : L2locTensor c (truncTen H' F) := by
    intro s₁ s₂ hs₁ hs₂
    obtain ⟨M, hM0, hM⟩ := core_trainVel_bound_le tr htr hH'0.le
    have hmeas_set : MeasurableSet (Icc s₁ s₂ ×ˢ B0579.cell c) :=
      measurableSet_Icc.prod (measurableSet_Ico.prod MeasurableSet.univ)
    have hle : ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
          ENNReal.ofReal (tnorm2 (truncTen H' F p) ^ 2) ≤
        ENNReal.ofReal (8 * M ^ 2) *
          ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
            ENNReal.ofReal (vnorm2 (truncVec H' d p) ^ 2 + tnorm2 (truncTen H' Gd p) ^ 2) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_mono' hmeas_set fun p _hp => ?_
      rw [← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      rw [tnorm2_truncTen_eq, vnorm2_truncVec_eq]
      split_ifs with hpH'
      · have hp1 := core_tnorm2_neg_flatMult_sq_le tr d hM0 (hM p.1 hpH'.le p.2)
        have hp2 : 0 ≤ tnorm2 (truncTen H' Gd p) ^ 2 := sq_nonneg _
        have hM8 : 0 ≤ 8 * M ^ 2 := by positivity
        nlinarith
      · have hp2 : 0 ≤ tnorm2 (truncTen H' Gd p) ^ 2 := sq_nonneg _
        have hM8 : 0 ≤ 8 * M ^ 2 := by positivity
        nlinarith
    exact lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hEloc s₁ s₂ hs₁ hs₂))
  have hflat_eq : ∀ H₀ < H', ∀ Φ, IsFlatTest c Φ → (∀ s x i, H₀ ≤ s → Φ s x i = 0) →
      flatIntegrand ν μ (fun _ _ _ => 0) (truncTen H' F) (truncVec H' d) Φ =
        flatIntegrand ν μ (trainVel tr) (fun _ _ _ => 0) d Φ := by
    intro H₀ hH₀ Φ _hΦ hsupp
    funext p
    by_cases hpH' : p.1 < H'
    · have hd : truncVec H' d p = d p := funext fun i => if_pos hpH'
      have hF : truncTen H' F p = F p := funext fun i => funext fun j => if_pos hpH'
      unfold flatIntegrand
      rw [hd, hF]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      unfold F flatMult
      push_cast
      ring
    · have hpH₀ : H₀ < p.1 := lt_of_lt_of_le hH₀ (not_lt.1 hpH')
      have hd : truncVec H' d p = 0 := funext fun i => if_neg hpH'
      have hF : truncTen H' F p = 0 := funext fun i => funext fun j => if_neg hpH'
      have hΦ0 : ∀ i, Φ p.1 p.2 i = 0 := fun i => hsupp p.1 p.2 i hpH₀.le
      have hdt0 : ∀ i, flatDt Φ p.1 p.2 i = 0 := by
        intro i
        unfold flatDt
        have hev : (fun s' => Φ s' p.2 i) =ᶠ[𝓝 p.1] fun _ => (0 : ℝ) := by
          filter_upwards [Ioi_mem_nhds hpH₀] with s' hs'
          exact hsupp s' p.2 i (le_of_lt hs')
        rw [hev.deriv_eq, deriv_const]
      have hslice0 : ∀ i, (fun y => Φ p.1 y i) = fun _ => (0 : ℝ) :=
        fun i => funext fun y => hsupp p.1 y i hpH₀.le
      have hpd0 : ∀ j, B0579.pd j (fun _ : ℝ × ℝ => (0 : ℝ)) = fun _ => (0 : ℝ) :=
        fun j => funext fun x => by simp [B0579.pd]
      have hgrad0 : ∀ i j, flatGrad Φ p.1 p.2 i j = 0 := by
        intro i j
        unfold flatGrad
        rw [hslice0 i, hpd0 j]
      have hlap0 : ∀ i, flatLap Φ p.1 p.2 i = 0 := by
        intro i
        unfold flatLap lapP
        rw [hslice0 i]
        simp [hpd0]
      unfold flatIntegrand
      simp [hd, hF, hΦ0, hdt0, hgrad0, hlap0]
  refine ⟨hc, hν, hH'0, hFloc, hFm', hbm', hGm', hEloc, ?_, ?_, ?_, ?_⟩
  · intro s hs ψ hψ
    by_cases hsH' : s < H'
    · have hd : ∀ x i, truncVec H' d (s, x) i = d (s, x) i := fun x i => if_pos hsH'
      simp only [hd]
      exact hsol.divFree s ⟨hs, hsH'.trans hH'H⟩ ψ hψ
    · have hd : ∀ x i, truncVec H' d (s, x) i = 0 := fun x i => if_neg hsH'
      simp [hd]
  · intro s hs i j
    by_cases hsH' : s < H'
    · have hd : (fun x => truncVec H' d (s, x) i) = fun x => d (s, x) i :=
        funext fun x => if_pos hsH'
      have hG : (fun x => truncTen H' Gd (s, x) i j) = fun x => Gd (s, x) i j :=
        funext fun x => if_pos hsH'
      rw [hd, hG]
      exact hsol.weakGrad s ⟨hs, hsH'.trans hH'H⟩ i j
    · have hd : (fun x => truncVec H' d (s, x) i) = fun _ => 0 :=
        funext fun x => if_neg hsH'
      have hG : (fun x => truncTen H' Gd (s, x) i j) = fun _ => 0 :=
        funext fun x => if_neg hsH'
      rw [hd, hG]
      refine ⟨fun ψ _ => ⟨by simp, by simp⟩, fun ψ _ => by simp⟩
  · intro H₀ hH₀ Φ hΦ hsupp
    rw [hflat_eq H₀ hH₀ Φ hΦ hsupp]
    exact hsol.integrable Φ hΦ fun s x i hsH => hsupp s x i ((hH₀.trans hH'H).le.trans hsH)
  · intro H₀ hH₀ Φ hΦ hsupp
    rw [hflat_eq H₀ hH₀ Φ hΦ hsupp]
    exact hsol.weak Φ hΦ fun s x i hsH => hsupp s x i ((hH₀.trans hH'H).le.trans hsH)

/-- Almost every slice `s > 0` is a good slice for `CoreTruncData`. -/
theorem aeGoodSlice_trunc {c ν H' : ℝ} {μ : ℂ} {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hD : CoreTruncData c ν H' μ F b G) :
    ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), LMGoodSlice c F G b s := by
  have hΦb : Measurable fun p : ℝ × (ℝ × ℝ) =>
      ENNReal.ofReal (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) :=
    ENNReal.measurable_ofReal.comp
      (((aeg_measurable_vnorm2 hD.measurable).pow_const 2).add
        ((aeg_measurable_tnorm2 hD.gradMeasurable).pow_const 2))
  have hΦF : Measurable fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (tnorm2 (F p) ^ 2) :=
    ENNReal.measurable_ofReal.comp ((aeg_measurable_tnorm2 hD.meas).pow_const 2)
  rw [aeg_Ioi_eq, ae_restrict_iUnion_iff]
  intro n
  have hn0 : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
  have hnab : 1 / ((n : ℝ) + 2) < (n : ℝ) + 2 := by
    have hn1 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hA := aeg_slice_finite hΦb (hD.energyLoc _ _ hn0 hnab)
  have hB := aeg_slice_finite hΦF (hD.l2loc _ _ hn0 hnab)
  filter_upwards [hA, hB] with s hsA hsB
  unfold LMGoodSlice LMCellL2
  refine ⟨fun i => ?_, fun j i => ?_, fun j i => ?_⟩
  · refine aeg_memLp_of_sq ((hD.measurable i).comp measurable_prodMk_left)
      (X := fun x => vnorm2 (b (s, x)) ^ 2 + tnorm2 (G (s, x)) ^ 2) (fun x => ?_) hsA
    exact le_trans (aeg_norm_sq_le_vnorm2 _ i) (le_add_of_nonneg_right (sq_nonneg _))
  · refine aeg_memLp_of_sq ((hD.gradMeasurable i j).comp measurable_prodMk_left)
      (X := fun x => vnorm2 (b (s, x)) ^ 2 + tnorm2 (G (s, x)) ^ 2) (fun x => ?_) hsA
    exact le_trans (aeg_norm_sq_le_tnorm2 _ i j) (le_add_of_nonneg_left (sq_nonneg _))
  · refine aeg_memLp_of_sq ((hD.meas i j).comp measurable_prodMk_left)
      (X := fun x => tnorm2 (F (s, x)) ^ 2) (fun x => ?_) hsB
    exact aeg_norm_sq_le_tnorm2 _ i j

/-- Local integrability in `s` of `energyE`, `energyN G`, `energyN F` for `CoreTruncData`. -/
theorem energyLocInt_trunc {c ν H' : ℝ} {μ : ℂ} {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hD : CoreTruncData c ν H' μ F b G) {s₁ s₂ : ℝ} (h0 : 0 < s₁) (h12 : s₁ < s₂) :
    IntegrableOn (fun s => energyE c b s) (Icc s₁ s₂) ∧
      IntegrableOn (fun s => energyN c G s) (Icc s₁ s₂) ∧
      IntegrableOn (fun s => energyN c F s) (Icc s₁ s₂) := by
  have hEN : Integrable (fun p : ℝ × (ℝ × ℝ) => vnorm2 (b p) ^ 2)
      ((volume.restrict (Icc s₁ s₂)).prod (volume.restrict (B0579.cell c))) ∧
      Integrable (fun p : ℝ × (ℝ × ℝ) => tnorm2 (G p) ^ 2)
      ((volume.restrict (Icc s₁ s₂)).prod (volume.restrict (B0579.cell c))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod ℝ (ℝ × ℝ)]
    have hloc := hD.energyLoc s₁ s₂ h0 h12
    have hb : Measurable fun p : ℝ × (ℝ × ℝ) => vnorm2 (b p) ^ 2 :=
      (loc_measurable_vnorm2 hD.measurable).pow_const 2
    have hG : Measurable fun p : ℝ × (ℝ × ℝ) => tnorm2 (G p) ^ 2 :=
      (loc_measurable_tnorm2 hD.gradMeasurable).pow_const 2
    constructor
    · refine loc_integrable_of_dominated hb (fun _ => sq_nonneg _) (fun _ => ?_) hloc
      exact le_add_of_nonneg_right (sq_nonneg _)
    · refine loc_integrable_of_dominated hG (fun _ => sq_nonneg _) (fun _ => ?_) hloc
      exact le_add_of_nonneg_left (sq_nonneg _)
  have hF : Integrable (fun p : ℝ × (ℝ × ℝ) => tnorm2 (F p) ^ 2)
      ((volume.restrict (Icc s₁ s₂)).prod (volume.restrict (B0579.cell c))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod ℝ (ℝ × ℝ)]
    have hF2 : Measurable fun p : ℝ × (ℝ × ℝ) => tnorm2 (F p) ^ 2 :=
      (loc_measurable_tnorm2 hD.meas).pow_const 2
    exact loc_integrable_of_dominated hF2 (fun _ => sq_nonneg _) (fun _ => le_rfl)
      (hD.l2loc s₁ s₂ h0 h12)
  exact ⟨hEN.1.integral_prod_left, hEN.2.integral_prod_left, hF.integral_prod_left⟩

/-- Local integrability in `s` of `energyE`, `energyN`, `energyR`, and `∫ |F||G|` for `CoreTruncData`. -/
theorem energyLocIntegrable_trunc {c ν H' : ℝ} {μ : ℂ} {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hD : CoreTruncData c ν H' μ F b G) {s₁ s₂ : ℝ} (h₁ : 0 < s₁) (h₂ : s₁ < s₂) :
    IntegrableOn (energyE c b) (Icc s₁ s₂) ∧ IntegrableOn (energyN c G) (Icc s₁ s₂) ∧
      IntegrableOn (energyR c F G) (Icc s₁ s₂) ∧
      IntegrableOn (fun s => ∫ x in B0579.cell c, tnorm2 (F (s, x)) * tnorm2 (G (s, x)))
        (Icc s₁ s₂) := by
  obtain ⟨hE, hN, -⟩ := energyLocInt_trunc hD h₁ h₂
  have hF2m : Measurable fun p => tnorm2 (F p) ^ 2 :=
    (EnergyLocInt.measurable_tnorm2_pt hD.meas).pow_const 2
  have hA : ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
      ENNReal.ofReal (tnorm2 (F p) ^ 2 + (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2)) < ⊤ :=
    EnergyLocInt.lintegral_ofReal_add_lt_top hF2m (hD.l2loc s₁ s₂ h₁ h₂) (hD.energyLoc s₁ s₂ h₁ h₂)
  have hRm : Measurable fun p => ∑ i : Fin 2, ∑ j : Fin 2,
      ((F p i j).re * (G p i j).re + (F p i j).im * (G p i j).im) := by
    apply Finset.measurable_sum; intro i _; apply Finset.measurable_sum; intro j _
    exact ((Complex.measurable_re.comp (hD.meas i j)).mul
      (Complex.measurable_re.comp (hD.gradMeasurable i j))).add
      ((Complex.measurable_im.comp (hD.meas i j)).mul
        (Complex.measurable_im.comp (hD.gradMeasurable i j)))
  have hRb : ∀ p, |∑ i : Fin 2, ∑ j : Fin 2,
      ((F p i j).re * (G p i j).re + (F p i j).im * (G p i j).im)|
      ≤ tnorm2 (F p) ^ 2 + (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) := fun p => by
    have h1 := abs_sum_re_le_tnorm2_mul (F p) (G p)
    have h2 := EnergyLocInt.abs_mul_le_sq_add' (tnorm2 (F p)) (tnorm2 (G p))
    have h3 : 0 ≤ vnorm2 (b p) ^ 2 := sq_nonneg _
    linarith [le_abs_self (tnorm2 (F p) * tnorm2 (G p))]
  have hJm : Measurable fun p => tnorm2 (F p) * tnorm2 (G p) :=
    (EnergyLocInt.measurable_tnorm2_pt hD.meas).mul
      (EnergyLocInt.measurable_tnorm2_pt hD.gradMeasurable)
  have hJb : ∀ p, |tnorm2 (F p) * tnorm2 (G p)|
      ≤ tnorm2 (F p) ^ 2 + (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) := fun p => by
    have h2 := EnergyLocInt.abs_mul_le_sq_add' (tnorm2 (F p)) (tnorm2 (G p))
    have h3 : 0 ≤ vnorm2 (b p) ^ 2 := sq_nonneg _
    linarith
  exact ⟨hE, hN, EnergyLocInt.integrableOn_cell_integral _ _ hRm hRb hA,
    EnergyLocInt.integrableOn_cell_integral _ _ hJm hJb hA⟩

end UnforcedLeray.Short.IIIa
