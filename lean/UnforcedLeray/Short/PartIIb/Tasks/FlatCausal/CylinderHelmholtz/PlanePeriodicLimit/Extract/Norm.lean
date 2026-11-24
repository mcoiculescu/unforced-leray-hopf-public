import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlanePeriodicLimit.Extract.Shift

/-!
# Part II-b, leaf `PartII-b:T12/1/4/2/3` (`PPLNorm`): window norm bound for the weak limit

Source of record: `the November 2 reference manuscript` lines 1933-1935.
Duality by truncated extremals `ψ_n = 1_{S_n} |G|^{r-2} \bar G` (`S_n = {1/(n+1) ≤ |G| ≤ n}`, finite
measure support, bounded, hence in `L²`): `|∫ G ψ_n| = lim |∫ H_N ψ_n| ≤ B ‖ψ_n‖_{r'}`, which gives
`(∫_{S_n} |G|^r)^{1/r} ≤ B`, and monotone convergence in `n`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem eLpNorm_le_of_weak_limit {μ : Measure (ℝ × ℝ)} {r : ℝ} (hr : 1 < r) {B : ℝ≥0∞}
    (H : ℕ → ℝ × ℝ → CMerid) (G : ℝ × ℝ → CMerid) (hG : MemLp G 2 μ)
    (hHm : ∀ N, AEStronglyMeasurable (H N) μ)
    (hH : ∀ N, eLpNorm (H N) (ENNReal.ofReal r) μ ≤ B)
    (hlim : ∀ ψ : ℝ × ℝ → CMerid, MemLp ψ 2 μ →
      Tendsto (fun N => ∫ z, ∑ i : Fin 2, H N z i * ψ z i ∂μ) atTop
        (𝓝 (∫ z, ∑ i : Fin 2, G z i * ψ z i ∂μ))) :
    eLpNorm G (ENNReal.ofReal r) μ ≤ B := by
  have hr0 : 0 < r := by linarith
  have hr1 : r - 1 ≠ 0 := by linarith
  set r' : ℝ := r.conjExponent with hr'
  have hpq : r.HolderConjugate r' := Real.HolderConjugate.conjExponent hr
  have hr'0 : 0 < r' := hpq.symm.pos
  have hrr' : (r - 1) * r' = r := by
    have : r' = r / (r - 1) := rfl
    rw [this]; field_simp
  haveI : ENNReal.HolderTriple (ENNReal.ofReal r) (ENNReal.ofReal r') 1 :=
    ⟨by
      rw [← ENNReal.ofReal_inv_of_pos hr0, ← ENNReal.ofReal_inv_of_pos hr'0,
        ← ENNReal.ofReal_add (inv_nonneg.2 hr0.le) (inv_nonneg.2 hr'0.le),
        hpq.inv_add_inv_eq_one, ENNReal.ofReal_one, inv_one]⟩
  -- a strongly measurable representative
  set G' : ℝ × ℝ → CMerid := hG.1.mk G with hG'def
  have hGG' : G =ᵐ[μ] G' := hG.1.ae_eq_mk
  have hG'm : StronglyMeasurable G' := hG.1.stronglyMeasurable_mk
  have hG'2 : MemLp G' 2 μ := hG.ae_eq hGG'
  rw [eLpNorm_congr_ae hGG']
  -- truncation sets
  set S : ℕ → Set (ℝ × ℝ) := fun n =>
    {z | ((n : ℝ≥0∞) + 1)⁻¹ ≤ ‖G' z‖ₑ ∧ ‖G' z‖ₑ ≤ n} with hSdef
  have hSm : ∀ n, MeasurableSet (S n) := fun n =>
    (measurableSet_le measurable_const hG'm.measurable.enorm).inter
      (measurableSet_le hG'm.measurable.enorm measurable_const)
  have hSmono : ∀ n, S n ⊆ S (n + 1) := by
    intro n z hz
    refine ⟨le_trans (ENNReal.inv_le_inv.2 ?_) hz.1, hz.2.trans (by exact_mod_cast n.le_succ)⟩
    push_cast
    gcongr
    exact le_self_add
  have hSfin : ∀ n, μ (S n) ≠ ⊤ := by
    intro n
    have h := hG'2.meas_ge_lt_top'_enorm (by norm_num) (by norm_num)
      (ε := ((n : ℝ≥0∞) + 1)⁻¹) (by simp) (by simp)
    exact ne_top_of_le_ne_top h.ne (measure_mono fun z hz => hz.1)
  have hSpos : ∀ n z, z ∈ S n → ‖G' z‖ ≠ 0 := by
    intro n z hz h0
    have h1 := hz.1
    rw [← ofReal_norm, h0] at h1
    simp at h1
  -- extremals
  set ψ : ℕ → ℝ × ℝ → CMerid := fun n z =>
    (S n).indicator (fun z => (‖G' z‖ ^ (r - 2)) • conjVec (G' z)) z with hψdef
  have hnormψ : ∀ n z, ‖ψ n z‖ = (S n).indicator (fun z => ‖G' z‖ ^ (r - 1)) z := by
    intro n z
    by_cases hz : z ∈ S n
    · have hne := hSpos n z hz
      simp only [hψdef, Set.indicator_of_mem hz]
      rw [norm_smul, norm_conjVec, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      have : r - 1 = (r - 2) + 1 := by ring
      rw [this, Real.rpow_add_one hne]
    · simp [hψdef, Set.indicator_of_notMem hz]
  have hψm : ∀ n, AEStronglyMeasurable (ψ n) μ := by
    intro n
    refine Measurable.aestronglyMeasurable ?_
    refine Measurable.indicator ?_ (hSm n)
    exact (hG'm.measurable.norm.pow_const _).smul
      (continuous_conjVec.measurable.comp hG'm.measurable)
  have hψmem : ∀ n, MemLp (ψ n) 2 μ := by
    intro n
    have hg : MemLp ((S n).indicator (fun _ => ((n : ℝ) ^ (r - 1)))) 2 μ :=
      memLp_indicator_const 2 (hSm n) _ (Or.inr (hSfin n))
    refine hg.of_le (hψm n) (ae_of_all _ fun z => ?_)
    rw [hnormψ]
    by_cases hz : z ∈ S n
    · simp only [Set.indicator_of_mem hz]
      have hle : ‖G' z‖ ≤ n := by
        have := hz.2
        rw [← ofReal_norm] at this
        have h2 := (ENNReal.ofReal_le_iff_le_toReal (by simp)).1 this
        simpa using h2
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
      exact Real.rpow_le_rpow (norm_nonneg _) hle (by linarith)
    · simp [Set.indicator_of_notMem hz]
  -- pairing of G' with ψ n
  have hGψ : ∀ n z, ∑ i : Fin 2, G' z i * ψ n z i =
      (((S n).indicator (fun z => ‖G' z‖ ^ r) z : ℝ) : ℂ) := by
    intro n z
    by_cases hz : z ∈ S n
    · have hne := hSpos n z hz
      simp only [hψdef, Set.indicator_of_mem hz]
      have h1 : ∑ i : Fin 2, G' z i * ((‖G' z‖ ^ (r - 2)) • conjVec (G' z)) i =
          ((‖G' z‖ ^ (r - 2) : ℝ) : ℂ) * ∑ i : Fin 2, G' z i * (conjVec (G' z)) i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [PiLp.smul_apply, Complex.real_smul]
        ring
      rw [h1, sum_mul_conj]
      have h2 : ‖G' z‖ ^ r = ‖G' z‖ ^ (r - 2) * ‖G' z‖ ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_add (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne))]
        norm_num
      rw [h2]; push_cast; rfl
    · simp [hψdef, Set.indicator_of_notMem hz]
  set J : ℕ → ℝ≥0∞ := fun n => ∫⁻ z, (S n).indicator (fun z => ‖G' z‖ₑ ^ r) z ∂μ with hJdef
  -- claim 1: modulus of the pairing
  have hclaim1 : ∀ n, ‖∫ z, ∑ i : Fin 2, G' z i * ψ n z i ∂μ‖ₑ = J n := by
    intro n
    have hint : Integrable (fun z => (S n).indicator (fun z => ‖G' z‖ ^ r) z) μ := by
      have := (integrable_pair hG'2 (hψmem n)).re
      refine this.congr (ae_of_all _ fun z => ?_)
      simp only [hGψ, RCLike.re_to_complex, Complex.ofReal_re]
    have h1 : ∫ z, ∑ i : Fin 2, G' z i * ψ n z i ∂μ =
        ((∫ z, (S n).indicator (fun z => ‖G' z‖ ^ r) z ∂μ : ℝ) : ℂ) := by
      simp_rw [hGψ]
      exact integral_complex_ofReal
    rw [h1, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
    have hnn : 0 ≤ᵐ[μ] fun z => (S n).indicator (fun z => ‖G' z‖ ^ r) z :=
      ae_of_all _ fun z => Set.indicator_nonneg (fun z _ => Real.rpow_nonneg (norm_nonneg _) _) z
    rw [abs_of_nonneg (integral_nonneg_of_ae hnn),
      ofReal_integral_eq_lintegral_ofReal hint hnn]
    refine lintegral_congr fun z => ?_
    by_cases hz : z ∈ S n
    · simp only [Set.indicator_of_mem hz]
      rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr0.le, ofReal_norm]
    · simp [Set.indicator_of_notMem hz]
  have hJfin : ∀ n, J n ≠ ⊤ := fun n => by
    rw [← hclaim1 n]; exact enorm_ne_top
  -- claim 2: the dual norm of ψ n
  have hclaim2 : ∀ n, eLpNorm (ψ n) (ENNReal.ofReal r') μ = J n ^ (1 / r') := by
    intro n
    rw [eLpNorm_eq_lintegral_rpow_enorm (by simp [hr'0]) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hr'0.le]
    congr 1
    refine lintegral_congr fun z => ?_
    rw [← ofReal_norm, hnormψ]
    by_cases hz : z ∈ S n
    · simp only [Set.indicator_of_mem hz]
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _) hr'0.le,
        ← Real.rpow_mul (norm_nonneg _), hrr',
        ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr0.le, ofReal_norm]
    · simp [Set.indicator_of_notMem hz, ENNReal.zero_rpow_of_pos hr'0]
  -- claim 3: the inequality J ≤ B J^{1/r'}
  have hclaim3 : ∀ n, J n ≤ B * J n ^ (1 / r') := by
    intro n
    have ha : ∫ z, ∑ i : Fin 2, G z i * ψ n z i ∂μ =
        ∫ z, ∑ i : Fin 2, G' z i * ψ n z i ∂μ :=
      integral_congr_ae (hGG'.mono fun z hz => by simp [hz])
    have hl := hlim (ψ n) (hψmem n)
    rw [ha] at hl
    have hT : Tendsto (fun N => ‖∫ z, ∑ i : Fin 2, H N z i * ψ n z i ∂μ‖ₑ) atTop
        (𝓝 ‖∫ z, ∑ i : Fin 2, G' z i * ψ n z i ∂μ‖ₑ) :=
      (continuous_enorm.tendsto _).comp hl
    have hb : ∀ N, ‖∫ z, ∑ i : Fin 2, H N z i * ψ n z i ∂μ‖ₑ ≤ B * J n ^ (1 / r') := by
      intro N
      calc ‖∫ z, ∑ i : Fin 2, H N z i * ψ n z i ∂μ‖ₑ
          ≤ eLpNorm (H N) (ENNReal.ofReal r) μ * eLpNorm (ψ n) (ENNReal.ofReal r') μ :=
            enorm_integral_pair_le (hHm N) (hψmem n).1
        _ ≤ B * J n ^ (1 / r') := by
            rw [hclaim2]; gcongr; exact hH N
    have := le_of_tendsto' hT hb
    rwa [hclaim1] at this
  -- claim 4: J^{1/r} ≤ B
  have hclaim4 : ∀ n, J n ^ (1 / r) ≤ B := by
    intro n
    by_cases h0 : J n = 0
    · rw [h0, ENNReal.zero_rpow_of_pos (by positivity)]; exact zero_le
    · have hpos : J n ^ (1 / r') ≠ 0 := by
        simp [ENNReal.rpow_eq_zero_iff, h0, hJfin n, hr'0]
      have hne : J n ^ (1 / r') ≠ ⊤ := by
        simp [ENNReal.rpow_eq_top_iff, hJfin n, hr'0.le]
      have hsplit : J n = J n ^ (1 / r) * J n ^ (1 / r') := by
        rw [← ENNReal.rpow_add _ _ h0 (hJfin n)]
        have : 1 / r + 1 / r' = 1 := by simpa [one_div] using hpq.inv_add_inv_eq_one
        rw [this, ENNReal.rpow_one]
      have h3 : J n ^ (1 / r) * J n ^ (1 / r') ≤ B * J n ^ (1 / r') := by
        rw [← hsplit]; exact hclaim3 n
      exact (ENNReal.mul_le_mul_iff_left hpos hne).1 h3
  have hclaim5 : ∀ n, J n ≤ B ^ r := by
    intro n
    have := ENNReal.rpow_le_rpow (hclaim4 n) hr0.le
    rwa [← ENNReal.rpow_mul, one_div_mul_cancel hr0.ne', ENNReal.rpow_one] at this
  -- monotone convergence
  have hsup : ∫⁻ z, ‖G' z‖ₑ ^ r ∂μ ≤ B ^ r := by
    have hmono : Monotone (fun n z => (S n).indicator (fun z => ‖G' z‖ₑ ^ r) z) := by
      refine monotone_nat_of_le_succ fun n z => ?_
      exact Set.indicator_le_indicator_of_subset (hSmono n) (fun _ => zero_le) z
    have hmeas : ∀ n, Measurable (fun z => (S n).indicator (fun z => ‖G' z‖ₑ ^ r) z) := fun n =>
      (hG'm.measurable.enorm.pow_const _).indicator (hSm n)
    have hpt : ∀ z, ‖G' z‖ₑ ^ r = ⨆ n, (S n).indicator (fun z => ‖G' z‖ₑ ^ r) z := by
      intro z
      refine le_antisymm ?_ (iSup_le fun n => ?_)
      · by_cases h0 : ‖G' z‖ₑ = 0
        · rw [h0, ENNReal.zero_rpow_of_pos hr0]; exact zero_le
        · obtain ⟨n1, hn1⟩ := ENNReal.exists_inv_nat_lt h0
          obtain ⟨n2, hn2⟩ := ENNReal.exists_nat_gt (enorm_ne_top (x := G' z))
          have hz : z ∈ S (n1 + n2) := by
            have hn2' : (n2 : ℝ≥0∞) ≤ ((n1 + n2 : ℕ) : ℝ≥0∞) := by
              exact_mod_cast Nat.le_add_left n2 n1
            refine ⟨le_trans (ENNReal.inv_le_inv.2 ?_) hn1.le, hn2.le.trans hn2'⟩
            push_cast
            calc (n1 : ℝ≥0∞) ≤ n1 + n2 := le_self_add
              _ ≤ n1 + n2 + 1 := le_self_add
          have := le_iSup (fun n => (S n).indicator (fun z => ‖G' z‖ₑ ^ r) z) (n1 + n2)
          simpa [Set.indicator_of_mem hz] using this
      · by_cases hz : z ∈ S n
        · simp [Set.indicator_of_mem hz]
        · simp [Set.indicator_of_notMem hz]
    calc ∫⁻ z, ‖G' z‖ₑ ^ r ∂μ
        = ∫⁻ z, ⨆ n, (S n).indicator (fun z => ‖G' z‖ₑ ^ r) z ∂μ :=
          lintegral_congr hpt
      _ = ⨆ n, ∫⁻ z, (S n).indicator (fun z => ‖G' z‖ₑ ^ r) z ∂μ :=
          lintegral_iSup hmeas hmono
      _ ≤ B ^ r := iSup_le hclaim5
  rw [eLpNorm_eq_lintegral_rpow_enorm (by simp [hr0]) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hr0.le]
  calc (∫⁻ z, ‖G' z‖ₑ ^ r ∂μ) ^ (1 / r) ≤ (B ^ r) ^ (1 / r) :=
        ENNReal.rpow_le_rpow hsup (by positivity)
    _ = B := by rw [← ENNReal.rpow_mul, mul_one_div_cancel hr0.ne', ENNReal.rpow_one]

theorem pplNorm : UnforcedLeray.Short.IIb.PPLNorm := by
  unfold PPLNorm
  intro r C c F H hctx φ G hφ hG M
  obtain ⟨hr, hC, hc, hF, hF2, hP⟩ := hctx
  exact eLpNorm_le_of_weak_limit hr (fun N => H (φ N)) G (hG.1 M)
    (fun N => (hP.memLp (φ N) M).1.aestronglyMeasurable)
    (fun N => hP.boundR (φ N) M) (fun ψ hψ => hG.2 M ψ hψ)

end UnforcedLeray.Short.IIb
