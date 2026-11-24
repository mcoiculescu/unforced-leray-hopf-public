import UnforcedLeray.Short.PartI.Sub.T02_5

/-!
# Part I, task `PartI:T02/5`: `TendstoZeroOfLipschitzIntegrable` (pure real analysis)

Source of record: `the November 2 reference manuscript`, lines 261-288 (decay of
the stream). The statement is `TendstoZeroOfLipschitzIntegrable` from `Short/PartI/Sub/T02_5.lean`.

Proof idea. Let `K ≥ 0` be the Lipschitz constant. If `f ≥ ε` at a point `x`, then `f ≥ ε/2` on
`[x, x + d]` with `d = ε / (2 (K + 1))`. Tail integrals over `Ioi M` tend to `0`, so for large `M`
the integral of `f` over `Ioi M` is below `ε d / 2`, while `[x, x + d] ⊆ Ioi M` carries integral
at least `ε d / 2` when `x ≥ M + 1`. The `atBot` half follows from the `atTop` half applied to
`x ↦ f (-x)`.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace UnforcedLeray.Short.PartI

/-- A nonnegative, `K`-Lipschitz, integrable function on `ℝ` tends to `0` at `+∞`. -/
theorem tendsto_atTop_zero_of_nonneg_lip_integrable (f : ℝ → ℝ) (K : ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hK : ∀ x y, |f x - f y| ≤ K * |x - y|) (hi : Integrable f) :
    Tendsto f atTop (𝓝 0) := by
  have hK0 : 0 ≤ K := by
    have h := hK 0 1
    have h1 : |(0 : ℝ) - 1| = 1 := by norm_num
    rw [h1, mul_one] at h
    linarith [abs_nonneg (f 0 - f 1)]
  -- the tail integrals over `Ioi M` tend to `0`
  have hT : Tendsto (fun M : ℝ => ∫ x in Ioi M, f x) atTop (𝓝 0) := by
    have hempty : (⋂ M : ℝ, Ioi M) = ∅ := by
      ext x
      constructor
      · intro hx
        have hx' := Set.mem_iInter.mp hx x
        simp at hx'
      · intro hx
        simp at hx
    have h : Tendsto (fun M : ℝ => ∫ x in Ioi M, f x) atTop
        (𝓝 (∫ x in (⋂ M : ℝ, Ioi M), f x)) :=
      tendsto_setIntegral_of_antitone (fun M => measurableSet_Ioi)
        (fun a b hab => Ioi_subset_Ioi hab) ⟨0, hi.integrableOn⟩
    rw [hempty, setIntegral_empty] at h
    exact h
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨d, hd_def⟩ : ∃ d : ℝ, d = ε / (2 * (K + 1)) := ⟨_, rfl⟩
  have hK1 : 0 < 2 * (K + 1) := by linarith
  have hK1' : 2 * (K + 1) ≠ 0 := ne_of_gt hK1
  have hd : 0 < d := by rw [hd_def]; exact div_pos hε hK1
  have hdK : d * (2 * (K + 1)) = ε := by rw [hd_def]; field_simp
  have hKd : K * d ≤ ε / 2 := by nlinarith [hdK, hd]
  have hpos : 0 < ε * d / 2 := div_pos (mul_pos hε hd) two_pos
  obtain ⟨M0, hM0⟩ := eventually_atTop.mp (Metric.tendsto_nhds.mp hT (ε * d / 2) hpos)
  rw [eventually_atTop]
  refine ⟨M0 + 1, fun x hx => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hf0 x)]
  by_contra hcon
  replace hcon : ε ≤ f x := not_lt.mp hcon
  -- `f ≥ ε/2` on `[x, x + d]`
  have hlow : ∀ y ∈ Icc x (x + d), ε / 2 ≤ f y := by
    intro y hy
    have hy1 : 0 ≤ y - x := sub_nonneg.mpr hy.1
    have hy2 : y - x ≤ d := by linarith [hy.2]
    have h1 : |f y - f x| ≤ K * |y - x| := hK y x
    have h2 : K * |y - x| ≤ K * d :=
      mul_le_mul_of_nonneg_left (by rw [abs_of_nonneg hy1]; exact hy2) hK0
    have h3 : |f y - f x| ≤ ε / 2 := le_trans h1 (le_trans h2 hKd)
    have h4 := (abs_le.mp h3).1
    linarith
  have hsub : Icc x (x + d) ⊆ Ioi M0 := fun y hy => by
    show M0 < y
    linarith [hy.1]
  have hvol : volume.real (Icc x (x + d)) = d := by
    rw [Real.volume_real_Icc_of_le (show x ≤ x + d by linarith)]
    ring
  have hμs : volume (Icc x (x + d)) ≠ ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hlowint : ε / 2 * d ≤ ∫ y in Icc x (x + d), f y := by
    have h := setIntegral_ge_of_const_le_real measurableSet_Icc hμs hlow hi.integrableOn
    rw [hvol] at h
    exact h
  have hup : ∫ y in Icc x (x + d), f y ≤ ∫ y in Ioi M0, f y :=
    setIntegral_mono_set hi.integrableOn (Eventually.of_forall fun y => hf0 y)
      (LE.le.eventuallyLE (show Icc x (x + d) ≤ Ioi M0 from hsub))
  have hnn : 0 ≤ ∫ y in Ioi M0, f y :=
    setIntegral_nonneg measurableSet_Ioi (fun y _ => hf0 y)
  have hMlt : dist (∫ y in Ioi M0, f y) 0 < ε * d / 2 := hM0 M0 le_rfl
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn] at hMlt
  linarith

/-- **Lemma `TendstoZeroOfLipschitzIntegrable`** (pure real analysis): a nonnegative Lipschitz
integrable function on `ℝ` tends to `0` at `±∞`. -/
theorem tendstoZeroOfLipschitzIntegrable : TendstoZeroOfLipschitzIntegrable := by
  intro f K hf0 hK hi
  refine ⟨tendsto_atTop_zero_of_nonneg_lip_integrable f K hf0 hK hi, ?_⟩
  have hg : ∀ x y : ℝ, |f (-x) - f (-y)| ≤ K * |x - y| := by
    intro x y
    have h := hK (-x) (-y)
    rwa [show -x - -y = -(x - y) by ring, abs_neg] at h
  have h2 := tendsto_atTop_zero_of_nonneg_lip_integrable (fun x => f (-x)) K
    (fun x => hf0 (-x)) hg hi.comp_neg
  have h3 := h2.comp tendsto_neg_atBot_atTop
  simpa [Function.comp_def] using h3

end UnforcedLeray.Short.PartI
