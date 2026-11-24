import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T19
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.Inequalities

/-!
# Part III-a, task `PartIII-a:T19/4`: homogeneous vanishing around the BUC train

Source of record: `the November 2 reference manuscript` (SP), lines 3541-3545
(Step P6: uniqueness and causality via homogeneous vanishing in the causal zero-entrance energy
class around `trainVel tr`).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## Pointwise and slice bounds for the train advection tensor -/

/-- On `s ≤ S` (`0 ≤ S`), a BUC train velocity `trainVel tr` has components uniformly bounded by
some `M ≥ 0`. -/
private theorem trainVel_bound_le {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
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

/-- Pointwise quadratic Frobenius bound for `-flatMult tr u`: if `‖trainVel tr s x i‖ ≤ M` for
`i = 0, 1` (`M ≥ 0`), then `tnorm2 (-flatMult tr u (s, x))² ≤ 8 M² vnorm2 (u (s, x))²`. -/
private theorem tnorm2_neg_flatMult_sq_le {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
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

private theorem gainConj_neg_flatMult {ν c : ℝ} (γ : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (u : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) :
    gainConj γ ν (fun p i j => -flatMult tr u p i j) =
      fun p i j => -flatMult tr (gainConj γ ν u) p i j := by
  rw [← gainConj_flatMult γ tr u]
  funext p i j
  simp [gainConj, smul_neg]

/-! ## Exponentially weighted ramp cutoff -/

/-- The ramp cutoff `rampPsi δ B` weighted by the integrating factor `exp(-L s)`. -/
private def expRamp (L δ B s : ℝ) : ℝ :=
  Real.exp (-L * s) * rampPsi δ B s

private theorem rampPsi_contDiff (δ B : ℝ) : ContDiff ℝ 1 (rampPsi δ B) := by
  unfold rampPsi
  exact (smooth_sigma_contDiff.comp ((contDiff_id.sub contDiff_const).div_const δ)).mul
    (smooth_sigma_contDiff.comp (((contDiff_const (c := 2 * B)).sub contDiff_id).div_const B))

private theorem rampPsi_deriv_le {K δ B : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x, |deriv Real.smoothTransition x| ≤ K) (hδ : 0 < δ) (hB2 : 2 * δ < B) (s : ℝ) :
    deriv (rampPsi δ B) s ≤
      (2 * K + 1) / δ * (Icc δ (2 * δ)).indicator (fun _ => (1 : ℝ)) s := by
  have hB : 0 < B := by linarith
  by_cases hs : s ∈ Icc δ (2 * δ)
  · simp only [indicator_of_mem hs, mul_one]
    rw [rampPsi_hasDerivAt δ B s hδ hB]
    have ha := abs_le.1 (hK ((s - δ) / δ))
    have hb := abs_le.1 (hK ((2 * B - s) / B))
    have hf0' : Real.smoothTransition ((s - δ) / δ) ≤ 1 := Real.smoothTransition.le_one _
    have hg1 : 0 ≤ Real.smoothTransition ((2 * B - s) / B) := Real.smoothTransition.nonneg _
    have hg1' : Real.smoothTransition ((2 * B - s) / B) ≤ 1 := Real.smoothTransition.le_one _
    have hf0n : 0 ≤ Real.smoothTransition ((s - δ) / δ) := Real.smoothTransition.nonneg _
    have hp : 0 ≤ 1 / δ := by positivity
    have hq : 0 ≤ 1 / B := by positivity
    have hqp : 1 / B ≤ 1 / δ := one_div_le_one_div_of_le hδ (by linarith [hs.1, hs.2])
    have ht : (0 - 1) / B = -(1 / B) := by ring
    rw [ht]
    have hgoal : (2 * K + 1) / δ = (2 * K + 1) * (1 / δ) := by ring
    rw [hgoal]
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 ha.2) hp) hg1,
      mul_nonneg (mul_nonneg hK0 hp) (sub_nonneg.2 hg1'),
      mul_nonneg (mul_nonneg hf0n hq)
        (by linarith [hb.1] : (0 : ℝ) ≤ K + deriv Real.smoothTransition ((2 * B - s) / B)),
      mul_nonneg (mul_nonneg hK0 hq) (sub_nonneg.2 hf0'),
      mul_nonneg hK0 (sub_nonneg.2 hqp), hp]
  · rw [indicator_of_notMem hs, mul_zero]
    have hsc : s < δ ∨ 2 * δ < s := by
      by_contra hc
      exact hs ⟨not_lt.1 (fun h => hc (Or.inl h)), not_lt.1 (fun h => hc (Or.inr h))⟩
    rcases hsc with h | h
    · have hev : rampPsi δ B =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
        filter_upwards [Iio_mem_nhds h] with y hy
        exact rampPsi_eq_zero_of_lt hδ hy
      rw [hev.deriv_eq]
      simp
    · have hev : rampPsi δ B =ᶠ[𝓝 s] fun y => Real.smoothTransition ((2 * B - y) / B) := by
        filter_upwards [Ioi_mem_nhds h] with y hy
        have hy' : 2 * δ < y := hy
        have h1 : 1 ≤ (y - δ) / δ := by
          rw [le_div_iff₀ hδ]
          linarith
        unfold rampPsi
        rw [Real.smoothTransition.one_of_one_le h1, one_mul]
      rw [hev.deriv_eq]
      have hin2 : HasDerivAt (fun y : ℝ => (2 * B - y) / B) ((0 - 1) / B) s :=
        ((hasDerivAt_const s (2 * B)).sub (hasDerivAt_id' s)).div_const B
      have hd : HasDerivAt (fun y => Real.smoothTransition ((2 * B - y) / B))
          (deriv Real.smoothTransition ((2 * B - s) / B) * ((0 - 1) / B)) s :=
        sigma_comp_hasDerivAt hin2
      rw [hd.deriv]
      have h1 := sigma_deriv_nonneg ((2 * B - s) / B)
      have h2 : (0 - 1) / B ≤ 0 := by
        rw [div_le_iff₀ hB]
        linarith
      nlinarith

private theorem expRamp_contDiff (L δ B : ℝ) : ContDiff ℝ 1 (expRamp L δ B) := by
  unfold expRamp
  exact (((contDiff_const (c := -L)).mul contDiff_id).exp).mul (rampPsi_contDiff δ B)

private theorem expRamp_eq_zero_of_not_mem {L δ B s : ℝ} (hδ : 0 < δ) (hB : 0 < B)
    (hs : s ∉ Icc δ (2 * B)) : expRamp L δ B s = 0 := by
  unfold expRamp
  rw [rampPsi_eq_zero_of_not_mem hδ hB hs, mul_zero]

private theorem expRamp_tsupport_subset {L δ B : ℝ} (hδ : 0 < δ) (hB : 0 < B) :
    tsupport (expRamp L δ B) ⊆ Icc δ (2 * B) := by
  have hsupp : Function.support (expRamp L δ B) ⊆ Icc δ (2 * B) := by
    intro s hs
    by_contra hs'
    exact hs (expRamp_eq_zero_of_not_mem hδ hB hs')
  exact closure_minimal hsupp isClosed_Icc

private theorem expRamp_nonneg (L δ B s : ℝ) : 0 ≤ expRamp L δ B s :=
  mul_nonneg (Real.exp_nonneg _) (rampPsi_nonneg δ B s)

private theorem expRamp_ge_on_Icc {L δ B s : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ) (hB : 0 < B)
    (hs : s ∈ Icc (2 * δ) B) :
    Real.exp (-L * B) ≤ expRamp L δ B s := by
  unfold expRamp
  rw [rampPsi_one hδ hB hs, mul_one]
  exact Real.exp_le_exp.2 (by nlinarith [hs.2])

private theorem expRamp_deriv_add (L δ B s : ℝ) :
    deriv (expRamp L δ B) s + L * expRamp L δ B s =
      Real.exp (-L * s) * deriv (rampPsi δ B) s := by
  have h1 : HasDerivAt (fun y : ℝ => Real.exp (-L * y)) (Real.exp (-L * s) * (-L * 1)) s :=
    HasDerivAt.exp ((hasDerivAt_id' s).const_mul (-L))
  have h2 : HasDerivAt (rampPsi δ B) (deriv (rampPsi δ B) s) s :=
    ((rampPsi_contDiff δ B).differentiable (by norm_num) s).hasDerivAt
  have hd : deriv (expRamp L δ B) s =
      Real.exp (-L * s) * (-L * 1) * rampPsi δ B s +
        Real.exp (-L * s) * deriv (rampPsi δ B) s := by
    unfold expRamp
    exact (h1.mul h2).deriv
  rw [hd]
  unfold expRamp
  ring

private theorem expRamp_deriv_add_le {K L δ B : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x, |deriv Real.smoothTransition x| ≤ K) (hL : 0 ≤ L) (hδ : 0 < δ)
    (hB2 : 2 * δ < B) (s : ℝ) :
    deriv (expRamp L δ B) s + L * expRamp L δ B s ≤
      (2 * K + 1) / δ * (Icc δ (2 * δ)).indicator (fun _ => (1 : ℝ)) s := by
  rw [expRamp_deriv_add]
  have hd := rampPsi_deriv_le hK0 hK hδ hB2 s
  have hexp0 : 0 ≤ Real.exp (-L * s) := Real.exp_nonneg _
  calc Real.exp (-L * s) * deriv (rampPsi δ B) s
      ≤ Real.exp (-L * s) *
          ((2 * K + 1) / δ * (Icc δ (2 * δ)).indicator (fun _ => (1 : ℝ)) s) :=
        mul_le_mul_of_nonneg_left hd hexp0
    _ ≤ (2 * K + 1) / δ * (Icc δ (2 * δ)).indicator (fun _ => (1 : ℝ)) s := by
        by_cases hs : s ∈ Icc δ (2 * δ)
        · rw [indicator_of_mem hs, mul_one]
          have hs0 : 0 ≤ s := le_trans hδ.le hs.1
          have hexp1 : Real.exp (-L * s) ≤ 1 :=
            Real.exp_le_one_iff.2 (by nlinarith)
          have hC0 : 0 ≤ (2 * K + 1) / δ := by positivity
          exact mul_le_of_le_one_left hC0 hexp1
        · rw [indicator_of_notMem hs, mul_zero, mul_zero]

/-- Bound on the combined derivative + absorption integral for `expRamp`. -/
private theorem expRamp_rhs_bound {C L δ : ℝ} {A ψ : ℝ → ℝ} (hδ : 0 < δ) (hC : 0 < C)
    (hA : ∀ s, 0 ≤ A s)
    (hb : ∀ s, deriv ψ s + L * ψ s ≤ C / δ * (Icc δ (2 * δ)).indicator (fun _ => (1 : ℝ)) s)
    (hint : Integrable (fun s => (deriv ψ s + L * ψ s) * (s ^ (-1 / 2 : ℝ) * A s))
      (volume.restrict (Ioi (0 : ℝ)))) :
    ENNReal.ofReal (∫ s in Ioi (0 : ℝ), (deriv ψ s + L * ψ s) * (s ^ (-1 / 2 : ℝ) * A s)) ≤
      ENNReal.ofReal (2 * C) * ∫⁻ s in Ioo 0 (3 * δ), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s) := by
  refine (ofReal_integral_le_lintegral' hint).trans ?_
  have hmeas : MeasurableSet (Ioo (0 : ℝ) (3 * δ)) := measurableSet_Ioo
  calc ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal ((deriv ψ s + L * ψ s) * (s ^ (-1 / 2 : ℝ) * A s))
      ≤ ∫⁻ s in Ioi (0 : ℝ), (Ioo (0 : ℝ) (3 * δ)).indicator
          (fun s => ENNReal.ofReal (2 * C) * ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s)) s := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        have hs0 : 0 < s := hs
        by_cases hmem : s ∈ Icc δ (2 * δ)
        · have hIoo : s ∈ Ioo (0 : ℝ) (3 * δ) := ⟨hs0, by linarith [hmem.2]⟩
          rw [Set.indicator_of_mem hIoo, ← ENNReal.ofReal_mul (by linarith)]
          apply ENNReal.ofReal_le_ofReal
          have hd := hb s
          rw [Set.indicator_of_mem hmem] at hd
          have hr : s ^ (-1 / 2 : ℝ) = s ^ (-3 / 2 : ℝ) * s := by
            rw [← Real.rpow_add_one hs0.ne']; norm_num
          have hr0 : 0 ≤ s ^ (-3 / 2 : ℝ) := Real.rpow_nonneg hs0.le _
          have hx : 0 ≤ s ^ (-3 / 2 : ℝ) * A s := mul_nonneg hr0 (hA s)
          have h1 : s ^ (-1 / 2 : ℝ) * A s ≤ 2 * δ * (s ^ (-3 / 2 : ℝ) * A s) := by
            rw [hr]
            nlinarith [mul_le_mul_of_nonneg_right hmem.2 hx]
          have hp : 0 ≤ s ^ (-1 / 2 : ℝ) * A s := mul_nonneg (Real.rpow_nonneg hs0.le _) (hA s)
          calc (deriv ψ s + L * ψ s) * (s ^ (-1 / 2 : ℝ) * A s)
              ≤ C / δ * 1 * (s ^ (-1 / 2 : ℝ) * A s) := mul_le_mul_of_nonneg_right hd hp
            _ ≤ C / δ * 1 * (2 * δ * (s ^ (-3 / 2 : ℝ) * A s)) :=
                mul_le_mul_of_nonneg_left h1 (by positivity)
            _ = 2 * C * (s ^ (-3 / 2 : ℝ) * A s) := by field_simp
        · have hd := hb s
          rw [Set.indicator_of_notMem hmem, mul_zero] at hd
          have hp : 0 ≤ s ^ (-1 / 2 : ℝ) * A s := mul_nonneg (Real.rpow_nonneg hs0.le _) (hA s)
          have : (deriv ψ s + L * ψ s) * (s ^ (-1 / 2 : ℝ) * A s) ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg hd hp
          rw [ENNReal.ofReal_of_nonpos this]
          exact zero_le
    _ = ENNReal.ofReal (2 * C) * ∫⁻ s in Ioo 0 (3 * δ), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s) := by
        have hinter : Ioo (0 : ℝ) (3 * δ) ∩ Ioi 0 = Ioo 0 (3 * δ) :=
          Set.inter_eq_left.2 (fun x hx => hx.1)
        rw [lintegral_indicator hmeas, Measure.restrict_restrict hmeas, hinter,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-! ## Main theorem: `TrainCausalHomogeneousZero` -/

theorem trainCausalHomogeneousZero : UnforcedLeray.Short.IIIa.TrainCausalHomogeneousZero := by
  intro P hP K hK ν hν0 tr htr μ hμ d Gd hsol
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc : 0 < c := Real.rpow_pos_of_pos hν0 _
  let γ : ℝ := P.eigenvalue.re
  have hγ : 0 ≤ γ := hP.eigenpair.re_pos.le
  have hμre : 0 < μ.re := (hK.2 μ hμ).1
  -- Step 1: reduce to the free equation with F = -flatMult tr d
  let F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ := fun p i j => -flatMult tr d p i j
  have hsol_free : IsCausalEnergySolution c ν μ (fun _ _ _ => 0) F d Gd := by
    have h0 : (fun (p : ℝ × (ℝ × ℝ)) (i j : Fin 2) => (0 : ℂ) + (0 : ℂ)) =
        fun _ _ _ => (0 : ℂ) := by
      funext p i j; exact add_zero 0
    have hsol' : IsCausalEnergySolution c ν μ (trainVel tr)
        (fun p i j => (0 : ℂ) + (0 : ℂ)) d Gd := by
      rw [h0]; exact hsol
    have hred := causal_free_reduction tr μ hsol'
    have hF_eq : (fun (p : ℝ × (ℝ × ℝ)) (i j : Fin 2) => (0 - flatMult tr d p i j) + 0) = F := by
      funext p i j; simp [F]
    rw [hF_eq] at hred
    exact hred
  have hdm : ∀ i, Measurable fun p => d p i := hsol.measurable
  have hGdm : ∀ i j, Measurable fun p => Gd p i j := hsol.gradMeasurable
  have hFm : ∀ i j, Measurable fun p => F p i j :=
    fun i j => (measurable_flatMult tr hdm i j).neg
  have hdm' := measurable_gainConj_vec (γ := γ) (ν := ν) hdm
  have hGdm' := measurable_gainConj_ten γ ν hGdm
  have hFm' := measurable_gainConj_ten γ ν hFm
  -- Step 2: local L² bounds for d, Gd, F and their gain conjugations
  have hBG := gainLocBG c ν γ hγ hν0 d Gd hsol.energyLoc
  have hFloc : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      (∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (tnorm2 (F p) ^ 2) < ⊤) ∧
      (∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
        ENNReal.ofReal (tnorm2 (gainConj γ ν F p) ^ 2) < ⊤) := by
    intro s₁ s₂ hs₁ hs₂
    have hs₂0 : 0 ≤ s₂ := (lt_trans hs₁ hs₂).le
    obtain ⟨M, hM0, hM⟩ := trainVel_bound_le tr htr hs₂0
    have hmeas_set : MeasurableSet (Icc s₁ s₂ ×ˢ B0579.cell c) :=
      measurableSet_Icc.prod (measurableSet_Ico.prod MeasurableSet.univ)
    constructor
    · have hle : ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (tnorm2 (F p) ^ 2) ≤
          ENNReal.ofReal (8 * M ^ 2) *
            ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
              ENNReal.ofReal (vnorm2 (d p) ^ 2 + tnorm2 (Gd p) ^ 2) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine setLIntegral_mono' hmeas_set fun p hp => ?_
        rw [← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have hp1 := tnorm2_neg_flatMult_sq_le tr d hM0 (hM p.1 hp.1.2 p.2)
        have hp2 : 0 ≤ tnorm2 (Gd p) ^ 2 := sq_nonneg _
        have hM8 : 0 ≤ 8 * M ^ 2 := by positivity
        nlinarith
      exact lt_of_le_of_lt hle
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hsol.energyLoc s₁ s₂ hs₁ hs₂))
    · have hle : ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
            ENNReal.ofReal (tnorm2 (gainConj γ ν F p) ^ 2) ≤
          ENNReal.ofReal (8 * M ^ 2) *
            ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
              ENNReal.ofReal (vnorm2 (gainConj γ ν d p) ^ 2) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine setLIntegral_mono' hmeas_set fun p hp => ?_
        rw [← ENNReal.ofReal_mul (by positivity), gainConj_neg_flatMult]
        apply ENNReal.ofReal_le_ofReal
        exact tnorm2_neg_flatMult_sq_le tr (gainConj γ ν d) hM0 (hM p.1 hp.1.2 p.2)
      exact lt_of_le_of_lt hle
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hBG s₁ s₂ hs₁ hs₂).1)
  -- Step 3: slice functions A, N, M_slice, Q
  let gV : ℝ × (ℝ × ℝ) → ℝ := fun p => vnorm2 (gainConj γ ν d p) ^ 2
  let gN : ℝ × (ℝ × ℝ) → ℝ := fun p => tnorm2 (gainConj γ ν Gd p) ^ 2
  let gQ : ℝ × (ℝ × ℝ) → ℝ := fun p => tnorm2 (gainConj γ ν F p) ^ 2
  have hgVm : Measurable gV := measurable_vnorm2_sq hdm'
  have hgNm : Measurable gN := (measurable_tnorm2 hGdm').pow_const 2
  have hgQm : Measurable gQ := (measurable_tnorm2 hFm').pow_const 2
  have hgV0 : ∀ p, 0 ≤ gV p := fun _ => sq_nonneg _
  have hgN0 : ∀ p, 0 ≤ gN p := fun _ => sq_nonneg _
  have hgQ0 : ∀ p, 0 ≤ gQ p := fun _ => sq_nonneg _
  obtain ⟨hVm, hVi, hVslice⟩ := sliceLoc c gV hc hgVm hgV0 fun s₁ s₂ h1 h2 => (hBG s₁ s₂ h1 h2).1
  obtain ⟨hNm, hNi, -⟩ := sliceLoc c gN hc hgNm hgN0 fun s₁ s₂ h1 h2 => (hBG s₁ s₂ h1 h2).2
  obtain ⟨hQm, hQi, hQslice⟩ := sliceLoc c gQ hc hgQm hgQ0 fun s₁ s₂ h1 h2 => (hFloc s₁ s₂ h1 h2).2
  let A : ℝ → ℝ := sliceSq c gV
  let N : ℝ → ℝ := sliceSq c gN
  let M_slice : ℝ → ℝ :=
    sliceSq c (fun p => tnorm2 (gainConj γ ν F p) * tnorm2 (gainConj γ ν Gd p))
  let Q : ℝ → ℝ := sliceSq c gQ
  have hnn : ∀ s, 0 ≤ A s ∧ 0 ≤ N s ∧ 0 ≤ M_slice s ∧ 0 ≤ Q s :=
    fun s => ⟨sliceSq_nonneg hgV0 s, sliceSq_nonneg hgN0 s,
      sliceSq_nonneg (fun p => mul_nonneg (tnorm2_nonneg _) (tnorm2_nonneg _)) s,
      sliceSq_nonneg hgQ0 s⟩
  -- Weighted energy identity and Young slice bound at θ = 2ν
  have hWEI := weightedEnergyIdentity c ν γ μ hc hν0 hγ F d Gd
    (fun s₁ s₂ h1 h2 => (hFloc s₁ s₂ h1 h2).1) hFm hsol_free
  have hY := youngSlice c (gainConj γ ν F) (gainConj γ ν Gd) hc hFm' hGdm'
    (fun s₁ s₂ h1 h2 => (hFloc s₁ s₂ h1 h2).2)
    (fun s₁ s₂ h1 h2 => (hBG s₁ s₂ h1 h2).2) (2 * ν) (by linarith)
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
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _)
        (vnorm2_smul_le (inv_nonneg.2 (Real.exp_pos _).le) (gainG_inv_le_one hγ hν0 hp1) _) 2
    have hlt := hle.trans_lt hfin
    rw [h2 δ] at hlt
    have hc' : ENNReal.ofReal c⁻¹ ≠ 0 := by simpa using inv_pos.2 hc
    rcases ENNReal.mul_lt_top_iff.1 hlt with h | h | h
    · exact h.2
    · exact absurd h hc'
    · simp [A, h]
  -- Step 4: for every 0 < a < B, the integral of s^{-3/2} A(s) on [a, B] vanishes
  obtain ⟨Kσ, hKσ0, hKσ⟩ := sigma_deriv_bound
  set C_ramp : ℝ := 2 * Kσ + 1
  have hC_ramp : 0 < C_ramp := by unfold C_ramp; linarith
  have hIcc_zero : ∀ a B : ℝ, 0 < a → a < B →
      ∫⁻ s in Icc a B, ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s) = 0 := by
    intro a B ha haB
    have hB0 : 0 < B := lt_trans ha haB
    obtain ⟨M, hM0, hM⟩ := trainVel_bound_le tr htr (by linarith : (0 : ℝ) ≤ 2 * B)
    set L : ℝ := (2 * ν)⁻¹ * (8 * M ^ 2)
    have hL0 : 0 ≤ L := by unfold L; positivity
    -- Bound Q(s) ≤ 8 M² A(s) for a.e. s > 0 with s ≤ 2B
    have hQA_ae : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), s ≤ 2 * B → Q s ≤ 8 * M ^ 2 * A s := by
      filter_upwards [hVslice, hQslice] with s hsV hsQ hsB
      show ∫ x in B0579.cell c, gQ (s, x) ≤ 8 * M ^ 2 * ∫ x in B0579.cell c, gV (s, x)
      rw [← integral_const_mul]
      refine integral_mono hsQ (hsV.const_mul (8 * M ^ 2)) fun x => ?_
      show tnorm2 (gainConj γ ν F (s, x)) ^ 2 ≤ 8 * M ^ 2 * vnorm2 (gainConj γ ν d (s, x)) ^ 2
      rw [gainConj_neg_flatMult]
      exact tnorm2_neg_flatMult_sq_le tr (gainConj γ ν d) hM0 (hM s hsB x)
    -- Per-δ bound for any 0 < δ with 2δ ≤ a
    have hdelta : ∀ δ : ℝ, 0 < δ → 2 * δ ≤ a →
        ENNReal.ofReal (1 / 2 * Real.exp (-L * B)) *
            (∫⁻ s in Icc a B, ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s)) ≤
          ENNReal.ofReal (2 * C_ramp) *
            ∫⁻ s in Ioo 0 (3 * δ), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s) := by
      intro δ hδ h2δa
      have hB2 : 2 * δ < B := lt_of_le_of_lt h2δa haB
      set ψ : ℝ → ℝ := expRamp L δ B
      have hc1 : ContDiff ℝ 1 ψ := expRamp_contDiff L δ B
      have hsupp : tsupport ψ ⊆ Icc δ (2 * B) := expRamp_tsupport_subset hδ hB0
      have hcs : HasCompactSupport ψ :=
        IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hsupp
      have hts : tsupport ψ ⊆ Ioi 0 := hsupp.trans fun s hs => lt_of_lt_of_le hδ hs.1
      have hψ0 : ∀ s, 0 ≤ ψ s := expRamp_nonneg L δ B
      have hδ2B : δ < 2 * B := by linarith
      obtain ⟨hint, hle⟩ := cutoff_young (k := 1 / 4) (ν := ν) (α := 1 / 2 + 2 * μ.re)
        (θ := 2 * ν) (A := A) (N := N) (M := M_slice) (Q := Q) (ψ := ψ) (a := δ) (b := 2 * B)
        (by linarith) le_rfl (by linarith) hnn
        (hVi δ (2 * B) hδ hδ2B) (hNi δ (2 * B) hδ hδ2B) (hQi δ (2 * B) hδ hδ2B)
        hY hc1 hδ hsupp hψ0 (hWEI ψ hc1 hcs hts hψ0)
      have iA12 : Integrable (fun s => ψ s * (s ^ (-1 / 2 : ℝ) * A s))
          (volume.restrict (Ioi (0 : ℝ))) :=
        integrable_cutoff_mul hc1 hδ hsupp (intOn_rpow_mul hδ (hVi δ (2 * B) hδ hδ2B) _)
      have iQ12 : Integrable (fun s => ψ s * (s ^ (-1 / 2 : ℝ) * Q s))
          (volume.restrict (Ioi (0 : ℝ))) :=
        integrable_cutoff_mul hc1 hδ hsupp (intOn_rpow_mul hδ (hQi δ (2 * B) hδ hδ2B) _)
      have hDint : Integrable (fun s => deriv ψ s * (s ^ (-1 / 2 : ℝ) * A s))
          (volume.restrict (Ioi (0 : ℝ))) :=
        integrable_contcutoff_mul (hc1.continuous_deriv le_rfl) hδ
          (tsupport_deriv_subset.trans hsupp) (intOn_rpow_mul hδ (hVi δ (2 * B) hδ hδ2B) _)
      -- Absorb the Q term into L * A
      have hQ_le : (2 * ν)⁻¹ * (∫ s in Ioi (0 : ℝ), ψ s * (s ^ (-1 / 2 : ℝ) * Q s)) ≤
          L * ∫ s in Ioi (0 : ℝ), ψ s * (s ^ (-1 / 2 : ℝ) * A s) := by
        have hint_le : (∫ s in Ioi (0 : ℝ), ψ s * (s ^ (-1 / 2 : ℝ) * Q s)) ≤
            8 * M ^ 2 * ∫ s in Ioi (0 : ℝ), ψ s * (s ^ (-1 / 2 : ℝ) * A s) := by
          rw [← integral_const_mul]
          refine integral_mono_ae iQ12 (iA12.const_mul (8 * M ^ 2)) ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi, hQA_ae] with s hs hsQA
          have hs0 : 0 < s := hs
          by_cases hsB : s ≤ 2 * B
          · have h1 := hsQA hsB
            have h2 : 0 ≤ ψ s * s ^ (-1 / 2 : ℝ) :=
              mul_nonneg (hψ0 s) (Real.rpow_nonneg hs0.le _)
            nlinarith [mul_le_mul_of_nonneg_left h1 h2]
          · have hnot : s ∉ Icc δ (2 * B) := fun h => hsB h.2
            have hψz : ψ s = 0 := expRamp_eq_zero_of_not_mem hδ hB0 hnot
            simp [hψz]
        calc (2 * ν)⁻¹ * (∫ s in Ioi (0 : ℝ), ψ s * (s ^ (-1 / 2 : ℝ) * Q s))
            ≤ (2 * ν)⁻¹ * (8 * M ^ 2 * ∫ s in Ioi (0 : ℝ), ψ s * (s ^ (-1 / 2 : ℝ) * A s)) :=
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
      have hle' : ∫ s in Ioi (0 : ℝ), ψ s * cutG (1 / 4) ν (2 * ν) A N s ≤
          ∫ s in Ioi (0 : ℝ), (deriv ψ s + L * ψ s) * (s ^ (-1 / 2 : ℝ) * A s) := by
        linarith [hle, hQ_le, hcomb_eq]
      -- Lower bound LHS by the integral over [a, B]
      have s2 : ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (ψ s * cutG (1 / 4) ν (2 * ν) A N s) =
          ENNReal.ofReal (∫ s in Ioi (0 : ℝ), ψ s * cutG (1 / 4) ν (2 * ν) A N s) := by
        refine (ofReal_integral_eq_lintegral_ofReal hint ?_).symm
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        have hs0 : (0 : ℝ) ≤ s := le_of_lt hs
        have h1 := mul_nonneg (Real.rpow_nonneg hs0 (-3 / 2 : ℝ)) (hnn s).1
        have : 0 ≤ cutG (1 / 4) ν (2 * ν) A N s := by
          unfold cutG
          have hsub : 2 * ν - 2 * ν = 0 := sub_self _
          rw [hsub, zero_mul, add_zero]
          linarith
        exact mul_nonneg (hψ0 s) this
      have hLHS_le : ENNReal.ofReal (1 / 2 * Real.exp (-L * B)) *
            (∫⁻ s in Icc a B, ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s)) ≤
          ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (ψ s * cutG (1 / 4) ν (2 * ν) A N s) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine (setLIntegral_mono' measurableSet_Icc fun s hs => ?_).trans
          (lintegral_mono_set (fun s hs => lt_of_lt_of_le ha hs.1))
        have hs0 : 0 ≤ s := le_trans ha.le hs.1
        have hsIcc : s ∈ Icc (2 * δ) B := ⟨le_trans h2δa hs.1, hs.2⟩
        have hψ_ge : Real.exp (-L * B) ≤ ψ s := expRamp_ge_on_Icc hL0 hδ hB0 hsIcc
        have hcut : cutG (1 / 4) ν (2 * ν) A N s = 1 / 2 * (s ^ (-3 / 2 : ℝ) * A s) := by
          unfold cutG; ring
        rw [hcut, ← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have hx : 0 ≤ s ^ (-3 / 2 : ℝ) * A s :=
          mul_nonneg (Real.rpow_nonneg hs0 _) (hnn s).1
        nlinarith [mul_le_mul_of_nonneg_right hψ_ge hx]
      have hRHS_le := expRamp_rhs_bound hδ hC_ramp (fun s => (hnn s).1)
        (expRamp_deriv_add_le hKσ0 hKσ hL0 hδ hB2) hcomb_int
      exact hLHS_le.trans (s2.le.trans ((ENNReal.ofReal_le_ofReal hle').trans hRHS_le))
    -- Take δ_n = a / (3 * (n + 1)) → 0
    set d : ℕ → ℝ := fun n => a / (3 * ((n : ℝ) + 1))
    have hdpos : ∀ n : ℕ, 0 < d n := fun n => by unfold d; positivity
    have hd2a : ∀ n : ℕ, 2 * d n ≤ a := by
      intro n
      unfold d
      have h1 : (2 : ℝ) * a ≤ a * (3 * ((n : ℝ) + 1)) := by
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith
      rw [ ← mul_div_assoc, div_le_iff₀ (by positivity)]
      exact h1
    have hdlim : Tendsto (fun n : ℕ => 3 * d n) atTop (𝓝 0) := by
      have heq : (fun n : ℕ => 3 * d n) = fun n : ℕ => a * (1 / ((n : ℝ) + 1)) := by
        funext n; unfold d; field_simp
      rw [heq]
      have h0 := (tendsto_const_nhds (x := a)).mul tendsto_one_div_add_atTop_nhds_zero_nat
      rwa [mul_zero] at h0
    have hE : Tendsto (fun n => ∫⁻ s in Ioo 0 (3 * d n), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s))
        atTop (𝓝 0) := by
      have hE0 : Tendsto (fun n => ∫⁻ s in Ioo 0 (3 * d n), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s)
          ∂(volume.restrict (Ioo 0 δ0))) atTop (𝓝 0) := by
        refine tendsto_setLIntegral_zero (μ := volume.restrict (Ioo 0 δ0))
          (f := fun s => ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s)) hfinA.ne ?_
        have hup : Tendsto (fun n => ENNReal.ofReal (3 * d n)) atTop (𝓝 0) := by
          simpa using ENNReal.tendsto_ofReal hdlim
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
          (fun _ => zero_le) (fun n => ?_)
        calc (volume.restrict (Ioo 0 δ0)) (Ioo 0 (3 * d n)) ≤ volume (Ioo 0 (3 * d n)) :=
              Measure.restrict_le_self _
          _ = ENNReal.ofReal (3 * d n) := by simp
      have hev : ∀ᶠ n : ℕ in atTop, 3 * d n < δ0 :=
        (tendsto_order.1 hdlim).2 δ0 (by simpa using hδ0)
      refine hE0.congr' (hev.mono fun n hn => ?_)
      rw [Measure.restrict_restrict measurableSet_Ioo,
        Set.inter_eq_left.2 (Ioo_subset_Ioo le_rfl hn.le)]
    have hRHS_lim : Tendsto (fun n => ENNReal.ofReal (2 * C_ramp) *
        ∫⁻ s in Ioo 0 (3 * d n), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s)) atTop (𝓝 0) := by
      have h0 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (2 * C_ramp)) hE
        (Or.inr ENNReal.ofReal_ne_top)
      rwa [mul_zero] at h0
    have hle_zero : ENNReal.ofReal (1 / 2 * Real.exp (-L * B)) *
        (∫⁻ s in Icc a B, ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s)) ≤ 0 :=
      ge_of_tendsto' hRHS_lim fun n => hdelta (d n) (hdpos n) (hd2a n)
    have hmul_zero : ENNReal.ofReal (1 / 2 * Real.exp (-L * B)) *
        (∫⁻ s in Icc a B, ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s)) = 0 :=
      le_antisymm hle_zero zero_le
    have hpos : ENNReal.ofReal (1 / 2 * Real.exp (-L * B)) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      positivity
    exact (mul_eq_zero.1 hmul_zero).resolve_left hpos
  -- Step 5: cover (0, ∞) by ⋃ k : ℕ, Icc (1 / (k + 1)) (k + 2)
  have hIoi_zero : ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s) = 0 := by
    have hcov : Ioi (0 : ℝ) ⊆ ⋃ k : ℕ, Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 2) := by
      intro s hs
      have hs0 : 0 < s := hs
      obtain ⟨k₁, hk₁⟩ := exists_nat_one_div_lt hs0
      obtain ⟨k₂, hk₂⟩ := exists_nat_ge s
      refine mem_iUnion.2 ⟨max k₁ k₂, ?_, ?_⟩
      · have hle : (k₁ : ℝ) + 1 ≤ (max k₁ k₂ : ℕ) + 1 := by
          exact_mod_cast Nat.add_le_add_right (le_max_left k₁ k₂) 1
        exact (one_div_le_one_div_of_le (by positivity) hle).trans hk₁.le
      · have hle : (k₂ : ℝ) ≤ (max k₁ k₂ : ℕ) := by exact_mod_cast le_max_right k₁ k₂
        linarith
    have hle : ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s) ≤
        ∑' k : ℕ, ∫⁻ s in Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 2),
          ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s) :=
      (lintegral_mono_set hcov).trans (lintegral_iUnion_le _ _)
    have hsum : (∑' k : ℕ, ∫⁻ s in Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 2),
        ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s)) = 0 := by
      refine ENNReal.tsum_eq_zero.2 fun k => hIcc_zero _ _ (by positivity) ?_
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have h1 : 1 / ((k : ℝ) + 1) ≤ 1 := div_le_one_of_le₀ (by linarith) (by positivity)
      linarith
    rw [hsum] at hle
    exact le_antisymm hle zero_le
  -- Step 6: conclude hCalNorm c (gainConj γ ν d) = 0
  have eH : hCalNorm c (gainConj γ ν d) ^ 2 = ENNReal.ofReal c⁻¹ *
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s) := by
    rw [normSq.1]
    exact (ageSlice c (-3 / 2) gV hc hgVm hgV0 fun s₁ s₂ h1 h2 => (hBG s₁ s₂ h1 h2).1).1
  rw [hIoi_zero, mul_zero] at eH
  exact sq_eq_zero_iff.1 eH

end UnforcedLeray.Short.IIIa
