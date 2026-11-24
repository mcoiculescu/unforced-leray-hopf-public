import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.SmoothOf
import UnforcedLeray.Units.B0224.PlaneHeat

/-!
# Leaf 1: the Duhamel shift (task `PartIII-b:C/flatset/col/7/1/1/2/1/org2/smooth/1`)

Source `the November 2 reference manuscript` 1650-1656, 1684-1689.
For `0 < s < S`, the substitution `σ = s - τ` turns `duhamel ν μ G (s,x) i` into an integral over
`τ ∈ [0,s]`; the cut-off `rhoCut s0 μ s τ` equals `((s-τ)/s)^μ` where `s - τ ≥ s0` and the slice
`heatH ν G i τ (s,x)` vanishes where `s - τ < s0` (the chart field vanishes for `σ < s0`), so the
integrand agrees with the shifted Duhamel integrand on `[0,s]` and vanishes on `[s,S]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- The integrand of `duhamel` in the substituted variable `σ` (source 1650-1656). -/
def dhShiftIntegrand (ν μ s : ℝ) (G : Chart → Fin 2 → ℝ) (x : ℝ × ℝ) (i : Fin 2) (σ : ℝ) : ℂ :=
  (((σ / s : ℝ) : ℂ) ^ (μ : ℂ)) •
    UnforcedLeray.B0224.planeHeat (ν * (s - σ)) (fun z => ((G (σ, z) i : ℝ) : ℂ)) x

theorem dhShift_duhamel_eq (ν μ s : ℝ) (G : Chart → Fin 2 → ℝ) (x : ℝ × ℝ) (i : Fin 2) :
    duhamel ν μ G (s, x) i = ∫ σ in (0 : ℝ)..s, dhShiftIntegrand ν μ s G x i σ := rfl

theorem dhShift_planeHeat_zero (θ : ℝ) (x : ℝ × ℝ) :
    UnforcedLeray.B0224.planeHeat θ (fun _ : ℝ × ℝ => (0 : ℂ)) x = 0 := by
  by_cases hθ : 0 < θ
  · rw [UnforcedLeray.B0224.planeHeat_of_pos hθ]
    simp
  · simp [UnforcedLeray.B0224.planeHeat_of_nonpos (not_lt.1 hθ)]

/-- The chart field vanishes on the slices `σ < s₀`. -/
theorem dhShift_zero_of_lt {G : Chart → Fin 2 → ℝ} {s0 s1 : ℝ} (i : Fin 2)
    (hsupp : ∀ p : Chart, G p ≠ 0 → p.1 ∈ Icc s0 s1) (σ : ℝ) (hσ : σ < s0) (z : ℝ × ℝ) :
    ((G (σ, z) i : ℝ) : ℂ) = 0 := by
  have hG0 : G (σ, z) i = 0 := by
    by_contra hne
    have hne' : G (σ, z) ≠ 0 := fun h => hne (by simp [h])
    have hmem := hsupp (σ, z) hne'
    have h2 : s0 ≤ σ := hmem.1
    linarith
  rw [hG0]
  simp

/-- On `s - τ ≥ s₀` the cut-off is `1` and the slice is the shifted Duhamel integrand. -/
theorem dhShift_pt_pos {ν μ s τ s0 : ℝ} (G : Chart → Fin 2 → ℝ) (x : ℝ × ℝ) (i : Fin 2)
    (hs0 : 0 < s0) (hτ : s0 ≤ s - τ) :
    rhoCut s0 μ s τ * heatH ν G i τ (s, x) = dhShiftIntegrand ν μ s G x i (s - τ) := by
  have h1 : Real.smoothTransition (((s - τ) - s0 / 2) / (s0 / 2)) = 1 := by
    apply Real.smoothTransition.one_of_one_le
    rw [le_div_iff₀ (by linarith)]
    linarith
  unfold rhoCut heatH dhShiftIntegrand
  rw [h1, sub_sub_cancel]
  simp [smul_eq_mul]

/-- On `s - τ < s₀` the slice vanishes, so the cut-off integrand vanishes. -/
theorem dhShift_neg_lhs {ν μ s τ s0 : ℝ} (G : Chart → Fin 2 → ℝ) (x : ℝ × ℝ) (i : Fin 2)
    (hzero : ∀ σ : ℝ, σ < s0 → ∀ z : ℝ × ℝ, ((G (σ, z) i : ℝ) : ℂ) = 0) (hτ : s - τ < s0) :
    rhoCut s0 μ s τ * heatH ν G i τ (s, x) = 0 := by
  have hfun : (fun z : ℝ × ℝ => ((G (s - τ, z) i : ℝ) : ℂ)) = fun _ => 0 :=
    funext fun z => hzero (s - τ) hτ z
  have hH : heatH ν G i τ (s, x) = 0 := by
    show UnforcedLeray.B0224.planeHeat (ν * τ) (fun z => ((G (s - τ, z) i : ℝ) : ℂ)) x = 0
    rw [hfun]
    exact dhShift_planeHeat_zero _ _
  rw [hH, mul_zero]

theorem dhShift_neg_rhs {ν μ s τ s0 : ℝ} (G : Chart → Fin 2 → ℝ) (x : ℝ × ℝ) (i : Fin 2)
    (hzero : ∀ σ : ℝ, σ < s0 → ∀ z : ℝ × ℝ, ((G (σ, z) i : ℝ) : ℂ) = 0) (hτ : s - τ < s0) :
    dhShiftIntegrand ν μ s G x i (s - τ) = 0 := by
  have hfun : (fun z : ℝ × ℝ => ((G (s - τ, z) i : ℝ) : ℂ)) = fun _ => 0 :=
    funext fun z => hzero (s - τ) hτ z
  show (((s - τ) / s : ℝ) : ℂ) ^ (μ : ℂ) •
    UnforcedLeray.B0224.planeHeat (ν * (s - (s - τ))) (fun z => ((G (s - τ, z) i : ℝ) : ℂ)) x = 0
  rw [hfun, dhShift_planeHeat_zero, smul_zero]

/-- **Leaf 1.** The Duhamel shift (source 1650-1656). -/
theorem duhamelShift : DuhamelShift := by
  intro c ν μ G hG
  obtain ⟨s0, s1, hs0, hsupp⟩ := hG.2.2.1
  refine ⟨s0, hs0, ?_⟩
  intro S s hs hsS x i
  have hzero : ∀ σ : ℝ, σ < s0 → ∀ z : ℝ × ℝ, ((G (σ, z) i : ℝ) : ℂ) = 0 :=
    fun σ hσ z => dhShift_zero_of_lt i hsupp σ hσ z
  have hpt : EqOn (fun τ : ℝ => rhoCut s0 μ s τ * heatH ν G i τ (s, x))
      (fun τ : ℝ => dhShiftIntegrand ν μ s G x i (s - τ)) (uIcc 0 s) := by
    intro τ _
    by_cases h : s0 ≤ s - τ
    · exact dhShift_pt_pos G x i hs0 h
    · dsimp only
      rw [dhShift_neg_lhs G x i hzero (not_le.1 h), dhShift_neg_rhs G x i hzero (not_le.1 h)]
  have hzeroS : EqOn (fun τ : ℝ => rhoCut s0 μ s τ * heatH ν G i τ (s, x))
      (fun _ : ℝ => (0 : ℂ)) (uIcc s S) := by
    intro τ hτ
    rw [uIcc_of_le hsS.le] at hτ
    dsimp only
    exact dhShift_neg_lhs (μ := μ) G x i hzero (by linarith [hτ.1])
  have key : ∫ τ in (0 : ℝ)..s, dhShiftIntegrand ν μ s G x i (s - τ) =
      ∫ σ in (0 : ℝ)..s, dhShiftIntegrand ν μ s G x i σ := by
    have := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := s)
      (fun σ => dhShiftIntegrand ν μ s G x i σ) s
    simpa using this
  by_cases hI : IntervalIntegrable (fun τ : ℝ => rhoCut s0 μ s τ * heatH ν G i τ (s, x))
      volume 0 S
  · have h1 : IntervalIntegrable (fun τ : ℝ => rhoCut s0 μ s τ * heatH ν G i τ (s, x))
        volume 0 s :=
      hI.mono_set (by
        rw [uIcc_of_le hs.le, uIcc_of_le (hs.trans hsS).le]
        exact Icc_subset_Icc le_rfl hsS.le)
    have h2 : IntervalIntegrable (fun τ : ℝ => rhoCut s0 μ s τ * heatH ν G i τ (s, x))
        volume s S :=
      hI.mono_set (by
        rw [uIcc_of_le hsS.le, uIcc_of_le (hs.trans hsS).le]
        exact Icc_subset_Icc hs.le le_rfl)
    rw [dhShift_duhamel_eq, ← intervalIntegral.integral_add_adjacent_intervals h1 h2,
      intervalIntegral.integral_congr hzeroS, intervalIntegral.integral_zero, add_zero,
      intervalIntegral.integral_congr hpt, key]
  · rw [intervalIntegral.integral_undef hI, dhShift_duhamel_eq]
    apply intervalIntegral.integral_undef
    intro hF
    apply hI
    have hΦ : IntervalIntegrable (fun τ : ℝ => dhShiftIntegrand ν μ s G x i (s - τ))
        volume 0 s := by
      have := (hF.comp_sub_left s).symm
      simpa only [sub_zero, sub_self] using this
    have h1 : IntervalIntegrable (fun τ : ℝ => rhoCut s0 μ s τ * heatH ν G i τ (s, x))
        volume 0 s :=
      (intervalIntegrable_congr (hpt.mono (Set.uIoc_subset_uIcc))).2 hΦ
    have h2' : IntervalIntegrable (fun _ : ℝ => (0 : ℂ)) volume s S :=
      intervalIntegrable_const
    have h2 : IntervalIntegrable (fun τ : ℝ => rhoCut s0 μ s τ * heatH ν G i τ (s, x))
        volume s S :=
      (intervalIntegrable_congr (hzeroS.mono (Set.uIoc_subset_uIcc))).2 h2'
    exact h1.trans h2

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
