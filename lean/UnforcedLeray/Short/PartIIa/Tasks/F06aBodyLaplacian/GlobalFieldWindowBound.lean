import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F06_1
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F04_1
import UnforcedLeray.Short.PartIIa.Tasks.F04aGlobalField.WindowLapAEMeas
import UnforcedLeray.Short.PartIIa.Tasks.F04aGlobalField.WindowLapLocInt
import UnforcedLeray.Short.PartIIa.Tasks.F04aGlobalField.WindowRhsFinite
import UnforcedLeray.Short.PartIIa.Tasks.F04aGlobalField.WindowLapUnique
import UnforcedLeray.Short.PartIIa.Tasks.F04aGlobalField.WindowLapGlue
import UnforcedLeray.Short.PartIIa.Tasks.F04aGlobalField.WindowLapPoU
import UnforcedLeray.Short.PartIIa.Tasks.F04aGlobalField.WindowLapPeriodic

/-!
# Part II-a, task `PartII-a:F06/1/1`: the global field with the window bound at every centre

The global window Laplacian `Λ` is glued from the integer-centre Laplacians `Λk` exactly as in
`globalLaplacianField_of` (`Sub/PartIIa_F04_1.lean`). For a real centre `τ₀`, the local
Laplacian `Λ₀` from `LocalWindowEstimate` is a window Laplacian on `(τ₀-1, τ₀+1)`, and by
`windowLapUnique` it agrees with `Λ` there; the window bound then transfers to `Λ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.Short.PartIIa.Rep

theorem globalFieldWindowBound : GlobalFieldWindowBound := by
  intro hloc r _ hr1 hrt
  obtain ⟨C, hC0, hC⟩ := hloc r hr1 hrt
  refine ⟨C, hC0, ?_⟩
  intro P hP hP1 ν hν μ f w hf W hW
  have hCP := hC P hP1 ν hν μ f w hf W hW
  choose Λk hΛk hbd using fun k : ℤ => hCP (k : ℝ)
  have hfin2 : ∀ k : ℤ, ∫⁻ τ in Ioo ((k : ℝ) - 1) ((k : ℝ) + 1), ∫⁻ y, ‖Λk k (τ, y)‖ₑ ^ r.toReal
      < ⊤ := by
    intro k
    refine lt_of_le_of_lt (hbd k) (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg
      ENNReal.toReal_nonneg ENNReal.ofReal_ne_top) (windowRhsFinite r hrt P μ f w (k : ℝ)))
  have hmeas : ∀ k : ℤ, AEStronglyMeasurable (Λk k) (volume.restrict (winSet (k : ℝ))) :=
    fun k => windowLapAEMeas ν (k : ℝ) W (Λk k) (hΛk k)
  have hli : ∀ k : ℤ, LocallyIntegrableOn (Λk k) (winSet (k : ℝ)) :=
    fun k => windowLapLocInt r hrt _ _ (Λk k) (hmeas k) (hfin2 k)
  have hover : ∀ k l : ℤ, Λk k =ᵐ[volume.restrict (winSet (k : ℝ) ∩ winSet (l : ℝ))] Λk l := by
    intro k l
    have hset : winSet (k : ℝ) ∩ winSet (l : ℝ) =
        Ioo (max ((k : ℝ) - 1) ((l : ℝ) - 1)) (min ((k : ℝ) + 1) ((l : ℝ) + 1)) ×ˢ
          (univ : Set Space) := by
      unfold winSet
      rw [Set.prod_inter_prod, Set.inter_univ, Set.Ioo_inter_Ioo]
    rw [hset]
    exact windowLapUnique ν k l _ _ W (Λk k) (Λk l) (le_max_left _ _) (min_le_left _ _)
      (le_max_right _ _) (min_le_right _ _) (hΛk k) (hΛk l)
      ((hli k).mono_set (by rw [← hset]; exact Set.inter_subset_left))
      ((hli l).mono_set (by rw [← hset]; exact Set.inter_subset_right))
  obtain ⟨Λ, hΛm, hΛeq⟩ := windowLapGlue Λk hmeas hover
  have hwin : ∀ τ₀ : ℝ, IsWindowLaplacian ν τ₀ W Λ := windowLapPoU ν W Λ Λk hΛk hΛeq
  have hli' : ∀ k : ℤ, LocallyIntegrableOn Λ (winSet (k : ℝ)) :=
    fun k => (hli k).congr (hΛeq k).symm
  have hWper : ∀ᵐ τ : ℝ, (fun y => W (τ + P, y)) =ᵐ[volume] fun y => W (τ, y) := by
    filter_upwards [hW.slice, hW.slice_shift P] with t h1 h2
    have e : ((P + t : ℝ) : AddCircle P) = (t : AddCircle P) := by
      rw [add_comm]; exact AddCircle.coe_add_period P t
    rw [e] at h2
    rw [add_comm t P]
    exact h2.trans h1.symm
  have hperΛ : ∀ᵐ τ : ℝ, (fun y => Λ (τ + P, y)) =ᵐ[volume] fun y => Λ (τ, y) :=
    windowLapPeriodic_of windowLapUnique P ν hP.out W Λ hW.meas hΛm hWper hwin hli'
  -- equal integrals over a window when the fields agree a.e. on that window
  have hcongrW : ∀ (a b : ℝ) (Λ₁ Λ₂ : ℝ × Space → CVec3),
      Λ₁ =ᵐ[volume.restrict (Ioo a b ×ˢ (univ : Set Space))] Λ₂ →
      ∫⁻ τ in Ioo a b, ∫⁻ y, ‖Λ₁ (τ, y)‖ₑ ^ r.toReal =
        ∫⁻ τ in Ioo a b, ∫⁻ y, ‖Λ₂ (τ, y)‖ₑ ^ r.toReal := by
    intro a b Λ₁ Λ₂ h
    have h' : Λ₁ =ᵐ[((volume : Measure ℝ).restrict (Ioo a b)).prod (volume : Measure Space)] Λ₂ := by
      rw [Measure.restrict_prod_eq_prod_univ]; exact h
    apply lintegral_congr_ae
    filter_upwards [Measure.ae_ae_of_ae_prod h'] with τ hτ
    apply lintegral_congr_ae
    filter_upwards [hτ] with y hy
    rw [hy]
  have hfinW : ∀ k : ℤ, ∫⁻ τ in Ioo ((k : ℝ) - 1) ((k : ℝ) + 1), ∫⁻ y, ‖Λ (τ, y)‖ₑ ^ r.toReal < ⊤ := by
    intro k
    rw [hcongrW ((k : ℝ) - 1) ((k : ℝ) + 1) Λ (Λk k) (hΛeq k)]
    exact hfin2 k
  -- local integrability of `Λ` on every real window, from two integer windows
  have hLIΛ : ∀ τ₀ : ℝ, LocallyIntegrableOn Λ (Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space)) := by
    intro τ₀
    apply windowLapLocInt r hrt (τ₀ - 1) (τ₀ + 1) Λ hΛm.aestronglyMeasurable
    have hk1 := Int.floor_le τ₀
    have hk2 := Int.lt_floor_add_one τ₀
    have hsub : Ioo (τ₀ - 1) (τ₀ + 1) ⊆
        Ioo (((⌊τ₀⌋ : ℤ) : ℝ) - 1) (((⌊τ₀⌋ : ℤ) : ℝ) + 1) ∪
          Ioo ((((⌊τ₀⌋ + 1 : ℤ)) : ℝ) - 1) ((((⌊τ₀⌋ + 1 : ℤ)) : ℝ) + 1) := by
      intro t ht
      simp only [Set.mem_union, Set.mem_Ioo, Int.cast_add, Int.cast_one] at ht ⊢
      by_cases hkt : t < ((⌊τ₀⌋ : ℤ) : ℝ) + 1
      · left
        constructor <;> linarith [ht.1, ht.2]
      · right
        push_neg at hkt
        constructor <;> linarith [ht.1, ht.2]
    refine lt_of_le_of_lt (lintegral_mono_set hsub) ?_
    refine lt_of_le_of_lt (lintegral_union_le _ _ _) ?_
    exact ENNReal.add_lt_top.2 ⟨hfinW _, hfinW _⟩
  refine ⟨Λ, hΛm, hwin, hperΛ, ?_⟩
  intro τ₀
  obtain ⟨Λ₀, hΛ₀, hbd₀⟩ := hCP τ₀
  have hli₀ : LocallyIntegrableOn Λ₀ (Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space)) := by
    refine windowLapLocInt r hrt (τ₀ - 1) (τ₀ + 1) Λ₀ (windowLapAEMeas ν τ₀ W Λ₀ hΛ₀) ?_
    exact lt_of_le_of_lt hbd₀ (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg
      ENNReal.toReal_nonneg ENNReal.ofReal_ne_top) (windowRhsFinite r hrt P μ f w τ₀))
  have hae : Λ =ᵐ[volume.restrict (Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space))] Λ₀ :=
    windowLapUnique ν τ₀ τ₀ (τ₀ - 1) (τ₀ + 1) W Λ Λ₀ le_rfl le_rfl le_rfl le_rfl (hwin τ₀) hΛ₀
      (hLIΛ τ₀) hli₀
  rw [hcongrW (τ₀ - 1) (τ₀ + 1) Λ Λ₀ hae]
  exact hbd₀

end UnforcedLeray.Short.PartIIa

#print axioms UnforcedLeray.Short.PartIIa.globalFieldWindowBound
