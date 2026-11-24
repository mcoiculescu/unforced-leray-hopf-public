import UnforcedLeray.Short.PartIIIa.Sub.T18_2_3

/-!
# Part III-a, task `PartIII-a:T18/2/3/1`: the truncations converge (`niceTruncation`)

Proves `NiceTruncation` (`Sub/T18_2_3.lean`; SP 3427-3440, source of record
`the November 2 reference manuscript`, lines 3427-3440).

Route. Write `H q = tnorm2 (gainConj γ ν F q)` (`niceTrH`) and `μ = ageμ c (-1/2)`.
* Pointwise, `tnorm2 (gainConj γ ν (1_{box} F) p) = 1_{box} H p` and
  `tnorm2 (gainConj γ ν (F - 1_{box} F) p) = 1_{box^c} H p`.
* (a) `eLpNorm_mono_ae` with the bound `1_{box} H ≤ H`.
* (b) `eLpNorm` is the power `1/2` of the lower integral of `1_{box^c} ‖H‖ₑ^2`. Dominated
  convergence (majorant `‖H‖ₑ^2`, finite since `tCalNorm < ⊤`) makes this tend to `0`, because
  for `μ`-a.e. `p` (those with `0 < p.1`, `|p.2.1| < c/2`) one has `p ∈ box_k` for all large `k`.
  The exceptional sets `{s ≤ 0}` and `{|q| ≥ c/2}` are `μ`-null: the first by the
  `s`-factor, the second because the cell measure charges only `{q = -c/2}`, a Lebesgue null set.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ### Pointwise norm algebra -/

theorem niceTr_tnorm2_smul {r : ℝ} (hr : 0 ≤ r) (T : Fin 2 → Fin 2 → ℂ) :
    tnorm2 (r • T) = r * tnorm2 T := by
  unfold tnorm2
  have h : ∑ i : Fin 2, ∑ j : Fin 2, ‖(r • T) i j‖ ^ 2
      = r ^ 2 * ∑ i : Fin 2, ∑ j : Fin 2, ‖T i j‖ ^ 2 := by
    simp [Pi.smul_apply, Real.norm_of_nonneg hr, mul_pow]
    ring
  rw [h, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr]

theorem niceTr_gainG_pos (γ ν s : ℝ) : 0 < gainG γ ν s := Real.exp_pos _

theorem niceTr_gainG_inv_nonneg (γ ν s : ℝ) : 0 ≤ (gainG γ ν s)⁻¹ :=
  (inv_pos.2 (niceTr_gainG_pos γ ν s)).le

theorem niceTr_tnorm2_gain (γ ν : ℝ) (T : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (p : ℝ × (ℝ × ℝ)) :
    tnorm2 (gainConj γ ν T p) = (gainG γ ν p.1)⁻¹ * tnorm2 (T p) := by
  rw [show gainConj γ ν T p = (gainG γ ν p.1)⁻¹ • T p from rfl,
    niceTr_tnorm2_smul (niceTr_gainG_inv_nonneg γ ν p.1)]

theorem niceTr_tnorm2_indicator (S : Set (ℝ × (ℝ × ℝ)))
    (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (p : ℝ × (ℝ × ℝ)) :
    tnorm2 (S.indicator F p) = S.indicator (fun q => tnorm2 (F q)) p := by
  by_cases hp : p ∈ S
  · simp [Set.indicator_of_mem hp]
  · simp [Set.indicator_of_notMem hp, tnorm2]

/-- The Frobenius norm of the gain-conjugated field `g⁻¹F`, as a real function. -/
def niceTrH (γ ν : ℝ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (q : ℝ × (ℝ × ℝ)) : ℝ :=
  tnorm2 (gainConj γ ν F q)

theorem niceTr_tnorm2_gain_indicator (γ ν : ℝ) (S : Set (ℝ × (ℝ × ℝ)))
    (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (p : ℝ × (ℝ × ℝ)) :
    tnorm2 (gainConj γ ν (S.indicator F) p) = S.indicator (niceTrH γ ν F) p := by
  rw [niceTr_tnorm2_gain, niceTr_tnorm2_indicator]
  by_cases hp : p ∈ S
  · simp [Set.indicator_of_mem hp, niceTrH, niceTr_tnorm2_gain]
  · simp [Set.indicator_of_notMem hp]

theorem niceTr_trunc_eq (c : ℝ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (k : ℕ) :
    niceTrunc c F k = (niceTruncBox c k).indicator F := by
  funext p i j
  by_cases hp : p ∈ niceTruncBox c k
  · simp [niceTrunc, hp]
  · simp [niceTrunc, hp]

theorem niceTr_gain_trunc (c ν γ : ℝ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (k : ℕ)
    (p : ℝ × (ℝ × ℝ)) :
    tnorm2 (gainConj γ ν (niceTrunc c F k) p)
      = (niceTruncBox c k).indicator (niceTrH γ ν F) p := by
  rw [niceTr_trunc_eq]
  exact niceTr_tnorm2_gain_indicator γ ν _ F p

theorem niceTr_diff_eq (c : ℝ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (k : ℕ) :
    (fun p i j => F p i j - niceTrunc c F k p i j)
      = ((niceTruncBox c k)ᶜ).indicator F := by
  funext p i j
  by_cases hp : p ∈ niceTruncBox c k
  · simp [niceTrunc, hp]
  · simp [niceTrunc, hp]

theorem niceTr_gain_diff (c ν γ : ℝ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (k : ℕ)
    (p : ℝ × (ℝ × ℝ)) :
    tnorm2 (gainConj γ ν (fun p i j => F p i j - niceTrunc c F k p i j) p)
      = ((niceTruncBox c k)ᶜ).indicator (niceTrH γ ν F) p := by
  rw [niceTr_diff_eq]
  exact niceTr_tnorm2_gain_indicator γ ν _ F p

theorem niceTr_indicator_le_self {α : Type*} (S : Set α) (g : α → ℝ≥0∞) (p : α) :
    S.indicator g p ≤ g p := by
  by_cases hp : p ∈ S
  · simp [Set.indicator_of_mem hp]
  · simp [Set.indicator_of_notMem hp]

/-! ### Measurability -/

theorem niceTr_measurable_H (γ ν : ℝ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (hF : ∀ i j, Measurable fun p => F p i j) : Measurable (niceTrH γ ν F) := by
  have hg : Measurable fun s : ℝ => (gainG γ ν s)⁻¹ := by
    unfold gainG
    fun_prop
  have hT : Measurable fun p => tnorm2 (F p) := by
    unfold tnorm2
    apply Measurable.sqrt
    apply Finset.measurable_sum
    intro i _
    apply Finset.measurable_sum
    intro j _
    exact ((hF i j).norm).pow_const 2
  have e : niceTrH γ ν F = fun p => (gainG γ ν p.1)⁻¹ * tnorm2 (F p) := by
    funext p
    exact niceTr_tnorm2_gain γ ν F p
  rw [e]
  exact (hg.comp measurable_fst).mul hT

/-! ### Null sets for `ageμ` -/

theorem niceTr_ageμ_fst_Iic (c a : ℝ) : ageμ c a (Prod.fst ⁻¹' Iic (0 : ℝ)) = 0 := by
  rw [← Set.prod_univ]
  unfold ageμ
  have : SFinite (UnforcedLeray.Cyl.avgμ c) := by
    unfold UnforcedLeray.Cyl.avgμ
    infer_instance
  rw [Measure.prod_prod]
  have hempty : Iic (0 : ℝ) ∩ Ioi (0 : ℝ) = ∅ :=
    Set.eq_empty_of_forall_notMem fun x hx => by
      have hx1 : x ≤ 0 := hx.1
      have hx2 : 0 < x := hx.2
      linarith
  have h1 : ((volume : Measure ℝ).restrict (Ioi (0 : ℝ))) (Iic 0) = 0 := by
    rw [Measure.restrict_apply measurableSet_Iic, hempty, measure_empty]
  have h2 : (((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).withDensity
      fun s => ENNReal.ofReal (s ^ a)) (Iic 0) = 0 :=
    withDensity_absolutelyContinuous _ _ h1
  rw [h2, zero_mul]

theorem niceTr_avg_Q_null (c : ℝ) :
    UnforcedLeray.Cyl.avgμ c {x : ℝ × ℝ | c / 2 ≤ |x.1|} = 0 := by
  have hsub : {x : ℝ × ℝ | c / 2 ≤ |x.1|} ∩ UnforcedLeray.Cyl.cell c
      ⊆ Prod.fst ⁻¹' ({-c / 2} : Set ℝ) := by
    rintro x ⟨hx, hcell⟩
    have hx' : c / 2 ≤ |x.1| := hx
    have hc' : -c / 2 ≤ x.1 ∧ x.1 < c / 2 := hcell.1
    show x.1 ∈ ({-c / 2} : Set ℝ)
    rw [Set.mem_singleton_iff]
    rcases abs_cases x.1 with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith [hc'.1, hc'.2]
  have hnull : (volume : Measure (ℝ × ℝ)) (Prod.fst ⁻¹' ({-c / 2} : Set ℝ)) = 0 := by
    rw [← Set.prod_univ, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton,
      zero_mul]
  have hmeas : MeasurableSet (UnforcedLeray.Cyl.cell c) :=
    measurableSet_Ico.prod MeasurableSet.univ
  unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
  rw [Measure.smul_apply, Measure.restrict_apply' hmeas, measure_mono_null hsub hnull,
    smul_zero]

theorem niceTr_ageμ_Q (c a : ℝ) : ageμ c a {p : ℝ × (ℝ × ℝ) | c / 2 ≤ |p.2.1|} = 0 := by
  have e : {p : ℝ × (ℝ × ℝ) | c / 2 ≤ |p.2.1|}
      = (univ : Set ℝ) ×ˢ {x : ℝ × ℝ | c / 2 ≤ |x.1|} := by
    ext p
    simp
  have : SFinite (UnforcedLeray.Cyl.avgμ c) := by
    unfold UnforcedLeray.Cyl.avgμ
    infer_instance
  rw [e]
  unfold ageμ
  rw [Measure.prod_prod, niceTr_avg_Q_null c, mul_zero]

/-- The `μ`-almost-everywhere region where the truncation sequence eventually captures the
point: `0 < s` and `|q| < c/2`. -/
theorem niceTr_ae_good (c a : ℝ) : ∀ᵐ p ∂(ageμ c a), 0 < p.1 ∧ |p.2.1| < c / 2 := by
  rw [ae_iff]
  refine measure_mono_null ?_
    (measure_union_null (niceTr_ageμ_fst_Iic c a) (niceTr_ageμ_Q c a))
  intro p hp
  have hp' : ¬ (0 < p.1 ∧ |p.2.1| < c / 2) := hp
  by_cases h1 : 0 < p.1
  · refine Set.mem_union_right _ ?_
    show c / 2 ≤ |p.2.1|
    by_contra h2
    exact hp' ⟨h1, not_le.1 h2⟩
  · refine Set.mem_union_left _ ?_
    show p.1 ≤ 0
    exact not_lt.1 h1

/-! ### Eventual capture of a point by the truncation boxes -/

theorem niceTr_eventually_mem (c : ℝ) (hc : 0 < c) (p : ℝ × (ℝ × ℝ)) (hs : 0 < p.1)
    (hq : |p.2.1| < c / 2) :
    ∀ᶠ k : ℕ in atTop, p ∈ niceTruncBox c k := by
  have hd : 0 < c / 2 - |p.2.1| := by linarith
  have h0 : 0 ≤ c / (c / 2 - |p.2.1|) := div_nonneg hc.le hd.le
  obtain ⟨N, hN⟩ := exists_nat_gt (c / (c / 2 - |p.2.1|) + 1 / p.1 + p.1 + |p.2.2|)
  have h1 : 0 < 1 / p.1 := one_div_pos.2 hs
  have h2 : 0 ≤ |p.2.2| := abs_nonneg _
  rw [Filter.eventually_atTop]
  refine ⟨N, fun k hk => ?_⟩
  have hkN : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk1 : c / (c / 2 - |p.2.1|) < (k : ℝ) := by linarith
  have hk2 : 1 / p.1 < (k : ℝ) := by linarith
  have hk3 : p.1 < (k : ℝ) := by linarith
  have hk4 : |p.2.2| < (k : ℝ) := by linarith
  have h3 : 1 < (k : ℝ) * p.1 := (div_lt_iff₀ hs).1 hk2
  have h4 : c < (k : ℝ) * (c / 2 - |p.2.1|) := (div_lt_iff₀ hd).1 hk1
  have hpos1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hpos2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  simp only [niceTruncBox, Set.mem_ofPred_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ hpos1]
    nlinarith
  · linarith
  · rw [le_div_iff₀ hpos2]
    nlinarith [abs_nonneg p.2.1]
  · linarith

theorem niceTr_eventually_mem_compl (c : ℝ) (hc : 0 < c) (p : ℝ × (ℝ × ℝ)) (hs : 0 < p.1)
    (hq : |p.2.1| < c / 2) :
    ∀ᶠ k : ℕ in atTop, p ∉ (niceTruncBox c k)ᶜ := by
  filter_upwards [niceTr_eventually_mem c hc p hs hq] with k hk
  exact Set.notMem_compl_iff.2 hk

/-! ### Convergence of the complementary truncation norm -/

theorem niceTr_tendsto_eLpNorm (c ν γ : ℝ) (hc : 0 < c)
    (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (hFm : ∀ i j, Measurable fun p => F p i j)
    (hF : tCalNorm c (gainConj γ ν F) < ⊤) :
    Tendsto (fun k : ℕ =>
      eLpNorm (fun p => ((niceTruncBox c k)ᶜ).indicator (niceTrH γ ν F) p) 2
        (ageμ c (-1 / 2))) atTop (𝓝 0) := by
  have hHm : Measurable (niceTrH γ ν F) := niceTr_measurable_H γ ν F hFm
  have hgm : Measurable fun p => ‖niceTrH γ ν F p‖ₑ ^ (2 : ℝ) :=
    (hHm.enorm).pow_const (2 : ℝ)
  have hF' : eLpNorm (niceTrH γ ν F) 2 (ageμ c (-1 / 2)) < ⊤ := hF
  have hfin : ∫⁻ p, ‖niceTrH γ ν F p‖ₑ ^ (2 : ℝ) ∂(ageμ c (-1 / 2)) < ⊤ := by
    have h := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero (by norm_num)).1 hF'
    simpa using h
  have hlim_ae : ∀ᵐ p ∂(ageμ c (-1 / 2)),
      Tendsto (fun k : ℕ => ((niceTruncBox c k)ᶜ).indicator
        (fun q => ‖niceTrH γ ν F q‖ₑ ^ (2 : ℝ)) p) atTop (𝓝 0) := by
    filter_upwards [niceTr_ae_good c (-1 / 2)] with p hp
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [niceTr_eventually_mem_compl c hc p hp.1 hp.2] with k hk
    exact (Set.indicator_of_notMem hk _).symm
  have hlim : Tendsto (fun k : ℕ => ∫⁻ p, ((niceTruncBox c k)ᶜ).indicator
      (fun q => ‖niceTrH γ ν F q‖ₑ ^ (2 : ℝ)) p ∂(ageμ c (-1 / 2))) atTop (𝓝 0) := by
    have hdc := tendsto_lintegral_of_dominated_convergence (μ := ageμ c (-1 / 2))
      (F := fun k p => ((niceTruncBox c k)ᶜ).indicator
        (fun q => ‖niceTrH γ ν F q‖ₑ ^ (2 : ℝ)) p)
      (f := fun _ => (0 : ℝ≥0∞))
      (fun q => ‖niceTrH γ ν F q‖ₑ ^ (2 : ℝ))
      (fun k => hgm.indicator (measurableSet_niceTruncBox c k).compl)
      (fun k => ae_of_all _ fun p => niceTr_indicator_le_self _ _ p)
      hfin.ne hlim_ae
    rw [lintegral_zero] at hdc
    exact hdc
  have hrw : ∀ k : ℕ, eLpNorm (fun p => ((niceTruncBox c k)ᶜ).indicator (niceTrH γ ν F) p) 2
      (ageμ c (-1 / 2)) = (∫⁻ p, ((niceTruncBox c k)ᶜ).indicator
        (fun q => ‖niceTrH γ ν F q‖ₑ ^ (2 : ℝ)) p ∂(ageμ c (-1 / 2))) ^ (1 / 2 : ℝ) := by
    intro k
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero (by norm_num)]
    simp only [ENNReal.toReal_ofNat]
    congr 1
    refine lintegral_congr fun p => ?_
    by_cases hp : p ∈ (niceTruncBox c k)ᶜ
    · simp [Set.indicator_of_mem hp]
    · simp [Set.indicator_of_notMem hp]
  have hpow : Tendsto (fun k : ℕ => (∫⁻ p, ((niceTruncBox c k)ᶜ).indicator
      (fun q => ‖niceTrH γ ν F q‖ₑ ^ (2 : ℝ)) p ∂(ageμ c (-1 / 2))) ^ (1 / 2 : ℝ))
      atTop (𝓝 ((0 : ℝ≥0∞) ^ (1 / 2 : ℝ))) :=
    ((ENNReal.continuous_rpow_const (y := 1 / 2)).tendsto (0 : ℝ≥0∞)).comp hlim
  rw [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hpow
  exact Tendsto.congr (fun k => (hrw k).symm) hpow

/-! ### The two parts of `NiceTruncation` -/

theorem niceTr_part_a (c ν γ : ℝ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (k : ℕ)
    (hF : tCalNorm c (gainConj γ ν F) < ⊤) :
    tCalNorm c (gainConj γ ν (niceTrunc c F k)) < ⊤ := by
  have hF' : eLpNorm (fun p => tnorm2 (gainConj γ ν F p)) 2 (ageμ c (-1 / 2)) < ⊤ := hF
  unfold tCalNorm
  refine lt_of_le_of_lt (eLpNorm_mono_ae (ae_of_all _ fun p => ?_)) hF'
  show ‖tnorm2 (gainConj γ ν (niceTrunc c F k) p)‖ ≤ ‖tnorm2 (gainConj γ ν F p)‖
  rw [niceTr_gain_trunc]
  by_cases hp : p ∈ niceTruncBox c k
  · simp [Set.indicator_of_mem hp, niceTrH]
  · simp [Set.indicator_of_notMem hp]

theorem niceTr_part_b (c ν γ : ℝ) (hc : 0 < c) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (hFm : ∀ i j, Measurable fun p => F p i j)
    (hF : tCalNorm c (gainConj γ ν F) < ⊤) :
    Tendsto (fun k : ℕ =>
      tCalNorm c (gainConj γ ν (fun p i j => F p i j - niceTrunc c F k p i j)))
      atTop (𝓝 0) := by
  have hfun : ∀ k : ℕ,
      tCalNorm c (gainConj γ ν (fun p i j => F p i j - niceTrunc c F k p i j))
        = eLpNorm (fun p => ((niceTruncBox c k)ᶜ).indicator (niceTrH γ ν F) p) 2
            (ageμ c (-1 / 2)) := by
    intro k
    unfold tCalNorm
    congr 1
    funext p
    exact niceTr_gain_diff c ν γ F k p
  exact Tendsto.congr (fun k => (hfun k).symm)
    (niceTr_tendsto_eLpNorm c ν γ hc F hFm hF)

/-- **Truncation** (`PartIII-a:T18/2/3/1`; SP 3427-3440). For `F` measurable with
`‖g⁻¹F‖_𝒯 < ∞` the truncations `1_{box_k} F` have finite `𝒯` norm and converge to `F`:
`‖g⁻¹(F - 1_{box_k} F)‖_𝒯 → 0`. -/
theorem niceTruncation : NiceTruncation := by
  unfold NiceTruncation
  intro c ν γ hc _hν F hFm hF
  exact ⟨fun k => niceTr_part_a c ν γ F k hF, niceTr_part_b c ν γ hc F hFm hF⟩

end UnforcedLeray.Short.IIIa
