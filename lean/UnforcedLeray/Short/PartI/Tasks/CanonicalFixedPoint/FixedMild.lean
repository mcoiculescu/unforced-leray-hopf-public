import UnforcedLeray.Short.PartI.Sub.PartI_C06

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartI

/-- Splitting an integral over `Ioi θ` at a point `s₀ ≥ θ`. -/
theorem canonicalFixedMild_split {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : ℝ → E) {θ s₀ : ℝ} (hθs : θ ≤ s₀) (hf : IntegrableOn f (Ioi θ)) :
    ∫ s in Ioi θ, f s = (∫ s in θ..s₀, f s) + ∫ s in Ioi s₀, f s := by
  rw [intervalIntegral.integral_of_le hθs, ← Ioc_union_Ioi_eq_Ioi hθs]
  rw [setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hf.mono_set Ioc_subset_Ioi_self) (hf.mono_set (Ioi_subset_Ioi hθs))]

theorem canonicalFixedMild : CanonicalFixedMild := by
  intro b S y φ A hcoc hint1 hint2 hfix θ s₀ hθ hθs₀
  have hb₀ : b ≤ s₀ := hθ.trans hθs₀
  have hS : ∀ s, s₀ ≤ s → S θ s y = S θ s₀ (S s₀ s y) := by
    intro s hs
    rw [hcoc θ s₀ s hθ hθs₀ hs]
    rfl
  have hA1 : ∫ s in Ioi θ, (A s / s) • S θ s y =
      (∫ s in θ..s₀, (A s / s) • S θ s y) + ∫ s in Ioi s₀, (A s / s) • S θ s y :=
    canonicalFixedMild_split _ hθs₀ (hint1 θ hθ)
  have hA2 : ∫ s in Ioi s₀, (A s / s) • S θ s y =
      S θ s₀ (∫ s in Ioi s₀, (A s / s) • S s₀ s y) := by
    have key : S θ s₀ (∫ s in Ioi s₀, (A s / s) • S s₀ s y) =
        ∫ s in Ioi s₀, S θ s₀ ((A s / s) • S s₀ s y) :=
      (ContinuousLinearMap.integral_comp_comm (S θ s₀) (hint1 s₀ hb₀)).symm
    rw [key]
    refine setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
    show (A s / s) • S θ s y = S θ s₀ ((A s / s) • S s₀ s y)
    rw [hS s (le_of_lt (Set.mem_Ioi.mp hs)), map_smul]
  have hB1 : ∫ s in Ioi θ, φ (canonicalRA S y A s) / s =
      (∫ s in θ..s₀, φ (canonicalRA S y A s) / s) + ∫ s in Ioi s₀, φ (canonicalRA S y A s) / s :=
    canonicalFixedMild_split _ hθs₀ (hint2 θ hθ)
  have e1 : 1 + ∫ s in Ioi θ, φ (canonicalRA S y A s) / s = A θ := hfix θ hθ
  have e2 : 1 + ∫ s in Ioi s₀, φ (canonicalRA S y A s) / s = A s₀ := hfix s₀ hb₀
  refine ⟨?_, ?_⟩
  · show ∫ s in Ioi θ, (A s / s) • S θ s y =
      S θ s₀ (∫ s in Ioi s₀, (A s / s) • S s₀ s y) + ∫ s in θ..s₀, (A s / s) • S θ s y
    rw [hA1, hA2]
    exact add_comm _ _
  · linear_combination -e1 + e2 + hB1

end UnforcedLeray.Short.PartI
