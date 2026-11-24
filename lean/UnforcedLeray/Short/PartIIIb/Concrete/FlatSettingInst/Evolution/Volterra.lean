import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Evolution.Leaves

/-!
# Two abstract laws of the Volterra evolution (source 2819-2836)

Source of record: `the November 2 reference manuscript` (73 pages).

* `volterraReflect`: the evolution commutes with a symmetry of its data (uniqueness of the strip
  Volterra equations, `VolterraData.eq_evolution_of_volterra`);
* `volterraDiagCont`: `‖E(τ,s)x - x‖ → 0` as `τ - s → 0⁺`, uniformly in `s` (the short-time
  comparison `VolterraData.norm_stripEvolution_sub_apply_le` and strong continuity of `S₀` at `0`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Evol

open UnforcedLeray.Infra.VolterraEvolution (VolterraData)

/-- **`VolterraReflect`** (source 2819-2836): `R_X ∘ E ∘ R_X` solves the same strip Volterra
equations, hence equals `E`. -/
theorem volterraReflect : VolterraReflect := by
  intro X Y _ _ _ _ _ D hD RX RY hRR hS₀ hS hB s τ hsτ x
  have key := D.eq_evolution_of_volterra hD (fun τ s => RX.comp ((D.evolution τ s).comp RX))
    (fun s x => ?_) (fun s τ hτ x => ?_) (fun s r τ hsr hrτ => ?_) s τ hsτ
  · have h := congrArg (fun L => L (RX x)) key
    simp only [ContinuousLinearMap.comp_apply, hRR] at h
    exact h.symm
  · exact RX.continuous.comp_continuousOn
      ((D.continuousOn_evolution hD s (RX x)).mono Icc_subset_Ici_self)
  · simp only [ContinuousLinearMap.comp_apply]
    rw [D.evolution_volterra hD hτ (RX x), map_add, hS₀, hRR,
      ← RX.intervalIntegral_comp_comm (D.intervalIntegrable_integrand hτ.1 hτ.2
        ((D.continuousOn_evolution hD s (RX x)).mono (fun r hr => hr.1)))]
    congr 1
    refine intervalIntegral.integral_congr fun r _ => ?_
    rw [← hS, ← hB]
  · ext y
    simp only [ContinuousLinearMap.comp_apply, hRR]
    rw [D.evolution_apply_comp hD hsr hrτ]

/-- **`VolterraDiagCont`** (source 2819-2836): uniform continuity of the evolution at the
diagonal. -/
theorem volterraDiagCont : VolterraDiagCont := by
  intro X Y _ _ _ _ _ D hD h0 x ε hε
  set K := 2 * D.C₀ * D.β * D.stripBound * ‖x‖ with hK
  have hK0 : 0 ≤ K := by
    have := D.C₀_nonneg
    have := D.β_nonneg
    have := D.stripBound_nonneg
    positivity
  have hc := (D.continuousOn_S₀ x) 0 ⟨le_rfl, zero_le_one⟩
  rw [Metric.continuousWithinAt_iff] at hc
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := hc (ε / 2) (by linarith)
  set a : ℝ := ε / 2 / (K + 1) with ha
  have ha0 : 0 < a := by positivity
  refine ⟨min 1 (min (δ₁ / 2) (a ^ 2)), lt_min one_pos (lt_min (half_pos hδ₁) (by positivity)),
    fun s τ hsτ hτ => ?_⟩
  have hτ1 : τ - s ≤ 1 := by linarith [min_le_left 1 (min (δ₁ / 2) (a ^ 2))]
  have hτδ : τ - s ≤ δ₁ / 2 := by
    linarith [(min_le_right 1 (min (δ₁ / 2) (a ^ 2))).trans (min_le_left _ _)]
  have hτa : τ - s ≤ a ^ 2 := by
    linarith [(min_le_right 1 (min (δ₁ / 2) (a ^ 2))).trans (min_le_right _ _)]
  have hmem : τ ∈ Icc s (s + 1) := ⟨hsτ, by linarith⟩
  rw [D.evolution_eq_stripEvolution hD hmem]
  have h1 := D.norm_stripEvolution_sub_apply_le hmem x
  have h2 : ‖D.S₀ (τ - s) x - x‖ < ε / 2 := by
    have hd : dist (τ - s) 0 < δ₁ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by linarith)]
      linarith
    have := hδ₁' (x := τ - s) ⟨by linarith, hτ1⟩ hd
    rwa [dist_eq_norm, h0, ContinuousLinearMap.id_apply] at this
  have h3 : (τ - s) ^ (1 / 2 : ℝ) ≤ a := by
    rw [← Real.sqrt_eq_rpow]
    calc Real.sqrt (τ - s) ≤ Real.sqrt (a ^ 2) := Real.sqrt_le_sqrt hτa
      _ = a := Real.sqrt_sq ha0.le
  have h4 : K * (τ - s) ^ (1 / 2 : ℝ) ≤ ε / 2 := by
    calc K * (τ - s) ^ (1 / 2 : ℝ) ≤ K * a := mul_le_mul_of_nonneg_left h3 hK0
      _ ≤ (K + 1) * a := by nlinarith
      _ = ε / 2 := by rw [ha]; field_simp
  have h1' : ‖D.stripEvolution τ s x - D.S₀ (τ - s) x‖ ≤ K * (τ - s) ^ (1 / 2 : ℝ) := by
    rw [hK]
    calc ‖D.stripEvolution τ s x - D.S₀ (τ - s) x‖
        ≤ 2 * D.C₀ * D.β * D.stripBound * (τ - s) ^ (1 / 2 : ℝ) * ‖x‖ := h1
      _ = 2 * D.C₀ * D.β * D.stripBound * ‖x‖ * (τ - s) ^ (1 / 2 : ℝ) := by ring
  calc ‖D.stripEvolution τ s x - x‖
      ≤ ‖D.stripEvolution τ s x - D.S₀ (τ - s) x‖ + ‖D.S₀ (τ - s) x - x‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ε := by linarith

/-- **`VolterraJointCont` from `VolterraDiagCont`** (source 2819-2836: the Volterra evolution is
jointly strongly continuous): the cocycle law moves the initial time to `s₀`, the bound
`VolterraData.norm_evolution_le` controls the outer factor, and near the diagonal both values are
compared with `x`. -/
theorem volterraJointCont_of (h : VolterraDiagCont) : VolterraJointCont := by
  intro X Y _ _ _ _ _ D hD h0 x
  rw [Metric.continuousOn_iff]
  rintro ⟨τ₀, s₀⟩ hp ε hε
  simp only [Set.mem_ofPred_eq] at hp
  have hMb : 1 ≤ D.evolutionBound := D.one_le_evolutionBound
  set M := D.evolutionBound * Real.exp (Real.log D.evolutionBound * (τ₀ - s₀ + 2)) with hM
  have hM1 : 1 ≤ M := one_le_mul_of_one_le_of_one_le hMb
    (Real.one_le_exp (mul_nonneg (Real.log_nonneg hMb) (by linarith)))
  have hM0 : 0 ≤ M := by linarith
  have hbound : ∀ s τ : ℝ, s ≤ τ → τ - s ≤ τ₀ - s₀ + 2 → ‖D.evolution τ s‖ ≤ M := by
    intro s τ hsτ hd
    refine (D.norm_evolution_le hsτ).trans ?_
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hd (Real.log_nonneg hMb))) (by linarith)
  set η := ε / (2 * (M + 1)) with hη
  have hη0 : 0 < η := by positivity
  have hMη : M * η < ε / 2 := by
    have e : M * η = ε / 2 * (M / (M + 1)) := by
      rw [hη]
      field_simp
    rw [e]
    have : M / (M + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
    nlinarith
  have h2η : 2 * η < ε := by
    have e : 2 * η = ε * (1 / (M + 1)) := by
      rw [hη]
      field_simp
    rw [e]
    have : 1 / (M + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
    nlinarith
  obtain ⟨δ₂, hδ₂, hdiag⟩ := h X Y D hD h0 x η hη0
  have hc := D.continuousOn_evolution hD s₀ x τ₀ hp
  rw [Metric.continuousWithinAt_iff] at hc
  obtain ⟨δ₁, hδ₁, hcont⟩ := hc (ε / 2) (by linarith)
  refine ⟨min (min δ₁ 1) (δ₂ / 2), lt_min (lt_min hδ₁ one_pos) (half_pos hδ₂), ?_⟩
  rintro ⟨τ, s⟩ hq hdist
  simp only [Set.mem_ofPred_eq] at hq
  rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq] at hdist
  obtain ⟨hdτ, hds⟩ := hdist
  have hδa : min (min δ₁ 1) (δ₂ / 2) ≤ δ₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hδb : min (min δ₁ 1) (δ₂ / 2) ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hδc : min (min δ₁ 1) (δ₂ / 2) ≤ δ₂ / 2 := min_le_right _ _
  have hτ1 := abs_lt.1 hdτ
  have hs1 := abs_lt.1 hds
  rw [dist_eq_norm]
  simp only
  by_cases hτs₀ : s₀ ≤ τ
  · have hcτ : ‖D.evolution τ s₀ x - D.evolution τ₀ s₀ x‖ < ε / 2 := by
      have := hcont (x := τ) hτs₀ (by rw [Real.dist_eq]; exact lt_of_lt_of_le hdτ hδa)
      rwa [dist_eq_norm] at this
    rcases le_total s s₀ with hss₀ | hss₀
    · -- `s ≤ s₀ ≤ τ`
      have e : D.evolution τ s x = D.evolution τ s₀ (D.evolution s₀ s x) :=
        (D.evolution_apply_comp hD hss₀ hτs₀ x).symm
      have hd : ‖D.evolution s₀ s x - x‖ ≤ η := hdiag s s₀ hss₀ (by linarith)
      have hb : ‖D.evolution τ s₀‖ ≤ M := hbound s₀ τ hτs₀ (by linarith)
      have h1 : ‖D.evolution τ s₀ (D.evolution s₀ s x - x)‖ ≤ M * η :=
        ((D.evolution τ s₀).le_opNorm _).trans (mul_le_mul hb hd (norm_nonneg _) hM0)
      calc ‖D.evolution τ s x - D.evolution τ₀ s₀ x‖
          = ‖D.evolution τ s₀ (D.evolution s₀ s x - x) +
              (D.evolution τ s₀ x - D.evolution τ₀ s₀ x)‖ := by
            rw [e, map_sub]
            congr 1
            abel
        _ ≤ ‖D.evolution τ s₀ (D.evolution s₀ s x - x)‖ +
              ‖D.evolution τ s₀ x - D.evolution τ₀ s₀ x‖ := norm_add_le _ _
        _ < ε := by linarith
    · -- `s₀ ≤ s ≤ τ`
      have e : D.evolution τ s₀ x = D.evolution τ s (D.evolution s s₀ x) :=
        (D.evolution_apply_comp hD hss₀ hq x).symm
      have hd : ‖D.evolution s s₀ x - x‖ ≤ η := hdiag s₀ s hss₀ (by linarith)
      have hb : ‖D.evolution τ s‖ ≤ M := hbound s τ hq (by linarith)
      have h1 : ‖D.evolution τ s (x - D.evolution s s₀ x)‖ ≤ M * η := by
        refine ((D.evolution τ s).le_opNorm _).trans (mul_le_mul hb ?_ (norm_nonneg _) hM0)
        rw [norm_sub_rev]
        exact hd
      calc ‖D.evolution τ s x - D.evolution τ₀ s₀ x‖
          = ‖D.evolution τ s (x - D.evolution s s₀ x) +
              (D.evolution τ s₀ x - D.evolution τ₀ s₀ x)‖ := by
            rw [e, map_sub]
            congr 1
            abel
        _ ≤ ‖D.evolution τ s (x - D.evolution s s₀ x)‖ +
              ‖D.evolution τ s₀ x - D.evolution τ₀ s₀ x‖ := norm_add_le _ _
        _ < ε := by linarith
  · -- `s ≤ τ < s₀ ≤ τ₀`: both values are close to `x`
    have hτs₀ : τ < s₀ := not_le.1 hτs₀
    have hd1 : ‖D.evolution τ s x - x‖ ≤ η := hdiag s τ hq (by linarith)
    have hd2 : ‖D.evolution τ₀ s₀ x - x‖ ≤ η := hdiag s₀ τ₀ hp (by linarith)
    calc ‖D.evolution τ s x - D.evolution τ₀ s₀ x‖
        = ‖(D.evolution τ s x - x) - (D.evolution τ₀ s₀ x - x)‖ := by
          congr 1
          abel
      _ ≤ ‖D.evolution τ s x - x‖ + ‖D.evolution τ₀ s₀ x - x‖ := norm_sub_le _ _
      _ < ε := by linarith

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Evol
