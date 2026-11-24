import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.CoreDuhamel.Propagation.Vorticity1.TimeWeak
import UnforcedLeray.Lib.BochnerTime.Slices

/-!
# `PartIII-a:T19/2/3/2/1` helpers: zero entrance and Lebesgue points

* `rep_zero`: the continuous representative of `H(r) = r^μ ⟨w(r), Ψ⟩` vanishes at `r = 0`
  (zero entrance `b ∈ 𝓗` near zero, SP 3428-3429).
* `ae_lebesgue`, `lebesgue_ident`: for almost every age `s`, simultaneously for every cylinder
  test, `H(s)` equals the representative at `s`. The null set is that of the Lebesgue points of the
  `L²(cell)`-valued slice path `r ↦ w(r)`, which does not depend on the test.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.V1

open UnforcedLeray.Short.IIIa UnforcedLeray.BochnerTime

instance fact_two_ne_top' : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

variable {ν c : ℝ}

/-! ## Zero entrance -/

section ZeroEntrance

variable {μ : ℂ} {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} {b₀ b_sol : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
  {G₀ G_sol : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}

/-- `H(r)/r = r^{μ-1} ⟨w(r), Ψ⟩` is integrable near zero. -/
theorem Hf_div_int (hc : 0 < c) (hfree : IsCausalEnergySolution c ν μ (fun _ _ _ => 0) F b₀ G₀)
    {tr : UnforcedLeray.B0140.TrainSol ν c}
    (hsol : IsCausalEnergySolution c ν μ (trainVel tr) F b_sol G_sol) (hμpos : 0 < μ.re)
    (T : ℝ) {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (μ - 1) * ∫ x in B0579.cell c, hInt (wF b₀ b_sol) φ (t, x))
      (Ioo 0 T) := by
  have hre : -5 / 4 < (μ - 1).re := by simp; linarith
  have hJ := joint_hInt hc hfree hsol hre T hφ
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hJ
  refine hJ.integral_prod_left.congr (Eventually.of_forall fun r => ?_)
  simp only
  rw [integral_const_mul]

/-- **Zero entrance**: the representative of `H` vanishes at `0`. -/
theorem rep_zero (hc : 0 < c) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (hbuc : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    (hfree : IsCausalEnergySolution c ν μ (fun _ _ _ => 0) F b₀ G₀)
    (hsol : IsCausalEnergySolution c ν μ (trainVel tr) F b_sol G_sol) (hμ0 : μ ≠ 0)
    (hμpos : 0 < μ.re) {T : ℝ} (hT : 0 < T) {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ) :
    (hasWeakDeriv hc tr hbuc hfree hsol hμ0 (by linarith) hT hφ).rep 0 = 0 := by
  set h := hasWeakDeriv hc tr hbuc hfree hsol hμ0 (by linarith) hT hφ with hh
  by_contra hL
  set L := h.rep 0
  have hLpos : 0 < ‖L‖ := norm_pos_iff.2 hL
  have hcont := h.continuousOn_rep 0 ⟨le_rfl, hT.le⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.1 hcont (‖L‖ / 2) (by positivity)
  set d := min (δ / 2) T with hd_def
  have hd : 0 < d := lt_min (by positivity) hT
  have hdT : d ≤ T := min_le_right _ _
  have hdδ : d < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hae : ∀ᵐ t ∂(volume.restrict (Ioo 0 d)),
      ‖L‖ / 2 ≤ ‖Hf c μ (wF b₀ b_sol) φ t‖ := by
    have h1 := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_right hdT) h.ae_eq_rep
    filter_upwards [h1, ae_restrict_mem measurableSet_Ioo] with t ht htm
    rw [ht]
    have hdist : dist t 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos htm.1]; exact htm.2.trans hdδ
    have := hball ⟨htm.1.le, htm.2.le.trans hdT⟩ hdist
    rw [dist_eq_norm] at this
    have h2 : ‖L‖ ≤ ‖h.rep t‖ + ‖h.rep t - L‖ := by
      calc ‖L‖ = ‖h.rep t - (h.rep t - L)‖ := by congr 1; abel
        _ ≤ ‖h.rep t‖ + ‖h.rep t - L‖ := norm_sub_le _ _
    linarith
  have hint := Hf_div_int hc hfree hsol hμpos d hφ
  have hinv : IntegrableOn (fun t : ℝ => t ^ (-1 : ℝ)) (Ioo 0 d) := by
    refine Integrable.mono' (hint.norm.const_mul (2 / ‖L‖))
      (measurable_id.pow_const _).aestronglyMeasurable ?_
    filter_upwards [hae, ae_restrict_mem measurableSet_Ioo] with t ht htm
    have ht0 : 0 < t := htm.1
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ht0 _), norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have hHf : ‖Hf c μ (wF b₀ b_sol) φ t‖ =
        t ^ μ.re * ‖∫ x in B0579.cell c, hInt (wF b₀ b_sol) φ (t, x)‖ := by
      rw [Hf, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    rw [hHf] at ht
    have hsub : (μ - 1).re = μ.re - 1 := by simp
    rw [hsub, Real.rpow_sub_one ht0.ne', Real.rpow_neg_one]
    set I := ‖∫ x in B0579.cell c, hInt (wF b₀ b_sol) φ (t, x)‖
    have key : (‖L‖ / 2) / t ≤ t ^ μ.re / t * I := by
      rw [div_mul_eq_mul_div]; exact div_le_div_of_nonneg_right ht ht0.le
    calc t⁻¹ = 2 / ‖L‖ * ((‖L‖ / 2) / t) := by field_simp
      _ ≤ 2 / ‖L‖ * (t ^ μ.re / t * I) := mul_le_mul_of_nonneg_left key (by positivity)
  exact absurd ((intervalIntegral.integrableOn_Ioo_rpow_iff hd).1 hinv) (lt_irrefl _)

end ZeroEntrance

/-! ## The `L²(cell)` slice path and its Lebesgue points -/

/-- The slice path `r ↦ f(r, ·) ∈ L²(cell)`. -/
def pathZ (c : ℝ) (f : ℝ × (ℝ × ℝ) → ℂ) : ℝ → Lp ℂ 2 (volume.restrict (B0579.cell c)) :=
  toPathLq 2 (volume.restrict (B0579.cell c)) f

theorem memLp_of_lint {X : Type*} [MeasurableSpace X] {m : Measure X} {φ : X → ℂ}
    (hφ : AEStronglyMeasurable φ m) {g : X → ℝ} (hg : ∀ x, ‖φ x‖ ^ 2 ≤ g x)
    (hfin : ∫⁻ x, ENNReal.ofReal (g x) ∂m < ⊤) : MemLp φ 2 m := by
  refine ⟨hφ, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hfin
  have h2 : ENNReal.toReal 2 = 2 := by norm_num
  rw [h2, ENNReal.rpow_two, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (hg x)

theorem pathZ_intervalIntegrable {f : ℝ × (ℝ × ℝ) → ℂ} (hf : Measurable f)
    (hEL : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (‖f p‖ ^ 2) < ⊤)
    {a T : ℝ} (ha : 0 < a) (haT : a < T) : IntervalIntegrable (pathZ c f) volume a T := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le haT.le]
  have hmem : MemLp f 2 ((volume.restrict (Icc a T)).prod (volume.restrict (B0579.cell c))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact memLp_of_lint hf.aestronglyMeasurable (g := fun p => ‖f p‖ ^ 2) (fun p => le_rfl)
      (hEL a T ha haT)
  obtain ⟨hsm, hnorm⟩ := stronglyMeasurable_toPath_Lq (ν := volume.restrict (Icc a T))
    (μ := volume.restrict (B0579.cell c)) (q := 2) hmem
  have hZ : MemLp (pathZ c f) 2 (volume.restrict (Icc a T)) := by
    refine ⟨hsm, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
    rw [pathZ, hnorm]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hmem.eLpNorm_ne_top
  exact hZ.integrable (by norm_num)

/-- For almost every `s ∈ (0, T)`, `s` is a Lebesgue point of the slice path, from every base
point `a ∈ (0, s)`. -/
theorem ae_lebesgue {f : ℝ × (ℝ × ℝ) → ℂ} (hf : Measurable f)
    (hEL : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (‖f p‖ ^ 2) < ⊤)
    {T : ℝ} (hT : 0 < T) :
    ∀ᵐ s ∂volume, s ∈ Ioo 0 T → ∀ a ∈ Ioo 0 s,
      HasDerivAt (fun x => ∫ t in a..x, pathZ c f t) (pathZ c f s) s := by
  have key : ∀ n : ℕ, ∀ᵐ s ∂volume, s ∈ uIcc (T / ((n : ℝ) + 2)) T →
      ∀ c' ∈ uIcc (T / ((n : ℝ) + 2)) T,
        HasDerivAt (fun x => ∫ t in c'..x, pathZ c f t) (pathZ c f s) s := by
    intro n
    have ha : 0 < T / ((n : ℝ) + 2) := by positivity
    have haT : T / ((n : ℝ) + 2) < T := by
      rw [div_lt_iff₀ (by positivity)]; nlinarith [n.cast_nonneg (α := ℝ)]
    exact (pathZ_intervalIntegrable hf hEL ha haT).ae_hasDerivAt_integral
  filter_upwards [ae_all_iff.2 key] with s hs hsT a ha
  obtain ⟨n, hn⟩ := exists_nat_gt (T / a)
  have hpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hna : T / ((n : ℝ) + 2) < a := by
    rw [div_lt_iff₀ hpos]
    rw [div_lt_iff₀ ha.1] at hn
    nlinarith
  have haT : T / ((n : ℝ) + 2) < T := by
    rw [div_lt_iff₀ hpos]; nlinarith [n.cast_nonneg (α := ℝ)]
  refine hs n ?_ a ?_
  · rw [uIcc_of_le haT.le]; exact ⟨(hna.trans ha.2).le, hsT.2.le⟩
  · rw [uIcc_of_le haT.le]; exact ⟨hna.le, (ha.2.trans hsT.2).le⟩

/-- The pairing of the slice path with a real `L²` test. -/
theorem pair_eq {m : ℝ × ℝ → ℝ}
    (hm2 : MemLp (fun x => (m x : ℂ)) 2 (volume.restrict (B0579.cell c)))
    {f : ℝ × (ℝ × ℝ) → ℂ} {t : ℝ}
    (ht : MemLp (fun x => f (t, x)) 2 (volume.restrict (B0579.cell c))) :
    innerSL ℂ (hm2.toLp _) (pathZ c f t) = ∫ x in B0579.cell c, f (t, x) * (m x : ℂ) := by
  rw [innerSL_apply_apply, pathZ, toPathLq_of_memLp ht, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hm2.coeFn_toLp, ht.coeFn_toLp] with x h1 h2
  rw [h1, h2, RCLike.inner_apply, Complex.conj_ofReal]

theorem memLp_test {m : ℝ × ℝ → ℝ} (hm : B0579.IsCylTest c m) :
    MemLp (fun x => (m x : ℂ)) 2 (volume.restrict (B0579.cell c)) := by
  obtain ⟨R, hR⟩ := hm.band
  have hm2 : MemLp m 2 (volume.restrict (B0579.cell c)) := by
    refine B0579.memLp_cell_of_continuous hm.continuous (B0579.isCompact_box c R)
      fun x hx hxK => hR x ?_
    by_contra h
    exact hxK (B0579.mem_box_of_mem_cell hx (not_lt.1 h))
  exact hm2.ofReal

end UnforcedLeray.Short.IIIa.V1

end
