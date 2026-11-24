import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Differentiation under the integral sign, generic form (helper of `FmrDeriv`)

Source of record: `the November 2 reference manuscript`, lines 2937-2946.
Abstract form of the argument of `PartII-b` `regularEnergyDeriv`: a family `F σ` on a measurable set
`S` with an integrable bound `G` for `F` and for the pointwise derivative `F'`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

open MeasureTheory Set Filter Topology

theorem fd_generic {α : Type*} [MeasurableSpace α] {μ : Measure α} (t T : ℝ) (S : Set α)
    (hS : MeasurableSet S) (F F' : ℝ → α → ℝ) (G : α → ℝ) (hG : IntegrableOn G S μ)
    (hFm : ∀ σ ∈ Icc t T, AEStronglyMeasurable (F σ) (μ.restrict S))
    (hFb : ∀ σ ∈ Icc t T, ∀ x ∈ S, |F σ x| ≤ G x)
    (hF'b : ∀ σ ∈ Icc t T, ∀ x ∈ S, |F' σ x| ≤ G x)
    (hder : ∀ x ∈ S, ∀ σ ∈ Icc t T,
      HasDerivWithinAt (fun r => F r x) (F' σ x) (Icc t T) σ) :
    (∀ σ ∈ Icc t T, IntegrableOn (F σ) S μ) ∧
      ContinuousOn (fun σ => ∫ x in S, F σ x ∂μ) (Icc t T) ∧
      ∀ τ ∈ Ico t T, IntegrableOn (F' τ) S μ ∧
        HasDerivWithinAt (fun σ => ∫ x in S, F σ x ∂μ) (∫ x in S, F' τ x ∂μ) (Ici τ) τ := by
  have hFint : ∀ σ ∈ Icc t T, IntegrableOn (F σ) S μ := by
    intro σ hσ
    refine Integrable.mono' hG (hFm σ hσ) ?_
    refine (ae_restrict_iff' hS).2 (ae_of_all _ (fun x hx => ?_))
    rw [Real.norm_eq_abs]; exact hFb σ hσ x hx
  have hcont : ContinuousOn (fun σ => ∫ x in S, F σ x ∂μ) (Icc t T) := by
    refine continuousOn_of_dominated (bound := G) hFm ?_ hG ?_
    · intro σ hσ
      refine (ae_restrict_iff' hS).2 (ae_of_all _ (fun x hx => ?_))
      rw [Real.norm_eq_abs]; exact hFb σ hσ x hx
    · refine (ae_restrict_iff' hS).2 (ae_of_all _ (fun x hx => ?_))
      intro σ hσ
      exact (hder x hx σ hσ).continuousWithinAt
  refine ⟨hFint, hcont, fun τ hτ => ?_⟩
  obtain ⟨hsτ, hτT⟩ := hτ
  have hτI : τ ∈ Icc t T := ⟨hsτ, hτT.le⟩
  have hnhds : Icc t T ∈ 𝓝[Ici τ] τ :=
    Filter.mem_of_superset (Ico_mem_nhdsGE hτT) (fun y hy => ⟨le_trans hsτ hy.1, hy.2.le⟩)
  have hev : ∀ᶠ σ in 𝓝[Ici τ \ {τ}] τ, σ ∈ Ioo τ T := by
    have hsub : Ici τ \ {τ} ⊆ Ioi τ := fun y hy =>
      lt_of_le_of_ne hy.1 (fun h => hy.2 (Set.mem_singleton_iff.mpr h.symm))
    exact Filter.eventually_of_mem (nhdsWithin_mono τ hsub (Ioo_mem_nhdsGT hτT))
      (fun σ hσ => hσ)
  have hL : ∀ x ∈ S,
      Tendsto (fun σ => (σ - τ)⁻¹ * (F σ x - F τ x)) (𝓝[Ici τ \ {τ}] τ) (𝓝 (F' τ x)) := by
    intro x hx
    have h1 : HasDerivWithinAt (fun r => F r x) (F' τ x) (Ici τ) τ :=
      (hder x hx τ hτI).mono_of_mem_nhdsWithin hnhds
    have h := hasDerivWithinAt_iff_tendsto_slope.mp h1
    exact Tendsto.congr (fun σ => by simp only [slope, smul_eq_mul, vsub_eq_sub]) h
  have hmeas : ∀ᶠ σ in 𝓝[Ici τ \ {τ}] τ,
      AEStronglyMeasurable (fun x => (σ - τ)⁻¹ * (F σ x - F τ x)) (μ.restrict S) := by
    filter_upwards [hev] with σ hσ
    have hσI : σ ∈ Icc t T := ⟨le_trans hsτ hσ.1.le, hσ.2.le⟩
    exact ((hFm σ hσI).sub (hFm τ hτI)).const_mul _
  have hbd : ∀ᶠ σ in 𝓝[Ici τ \ {τ}] τ,
      ∀ᵐ x ∂(μ.restrict S), ‖(σ - τ)⁻¹ * (F σ x - F τ x)‖ ≤ G x := by
    filter_upwards [hev] with σ hσ
    refine (ae_restrict_iff' hS).2 (ae_of_all _ (fun x hx => ?_))
    have hpos : 0 < σ - τ := sub_pos.mpr hσ.1
    have hder' : ∀ r ∈ Icc τ σ, HasDerivWithinAt (fun r' => F r' x) (F' r x) (Icc τ σ) r := by
      intro r hr
      have hrI : r ∈ Icc t T := ⟨le_trans hsτ hr.1, le_trans hr.2 hσ.2.le⟩
      exact (hder x hx r hrI).mono (Icc_subset_Icc hsτ hσ.2.le)
    have hbd' : ∀ r ∈ Icc τ σ, ‖F' r x‖ ≤ G x := by
      intro r hr
      have hrI : r ∈ Icc t T := ⟨le_trans hsτ hr.1, le_trans hr.2 hσ.2.le⟩
      rw [Real.norm_eq_abs]; exact hF'b r hrI x hx
    have hmvt : ‖F σ x - F τ x‖ ≤ G x * ‖σ - τ‖ :=
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder' hbd' (convex_Icc τ σ)
        (left_mem_Icc.2 hσ.1.le) (right_mem_Icc.2 hσ.1.le)
    rw [Real.norm_of_nonneg hpos.le] at hmvt
    rw [norm_mul, norm_inv, Real.norm_of_nonneg hpos.le]
    calc (σ - τ)⁻¹ * ‖F σ x - F τ x‖ ≤ (σ - τ)⁻¹ * (G x * (σ - τ)) :=
          mul_le_mul_of_nonneg_left hmvt (inv_nonneg.2 hpos.le)
      _ = G x := by field_simp
  have hlim : ∀ᵐ x ∂(μ.restrict S),
      Tendsto (fun σ => (σ - τ)⁻¹ * (F σ x - F τ x)) (𝓝[Ici τ \ {τ}] τ) (𝓝 (F' τ x)) :=
    (ae_restrict_iff' hS).2 (ae_of_all _ hL)
  have hT := tendsto_integral_filter_of_dominated_convergence G hmeas hbd hG hlim
  have hmeas' : AEStronglyMeasurable (F' τ) (μ.restrict S) := by
    let σn : ℕ → ℝ := fun n => τ + (T - τ) / ((n + 2 : ℕ) : ℝ)
    have hpos : 0 < T - τ := sub_pos.mpr hτT
    have hσn0 : Tendsto (fun n : ℕ => (T - τ) / ((n + 2 : ℕ) : ℝ)) atTop (𝓝 0) :=
      (tendsto_const_div_atTop_nhds_zero_nat (T - τ)).comp (tendsto_add_atTop_nat 2)
    have hσn1 : ∀ n : ℕ, 0 < (T - τ) / ((n + 2 : ℕ) : ℝ) := fun n => by positivity
    have hσn2 : ∀ n : ℕ, (T - τ) / ((n + 2 : ℕ) : ℝ) ≤ T - τ := fun n => by
      rw [div_le_iff₀ (by positivity)]
      have : (1 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        push_cast; linarith
      nlinarith
    have hseq : Tendsto σn atTop (𝓝[Ici τ \ {τ}] τ) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Filter.Eventually.of_forall (fun n => ?_)⟩
      · have := hσn0.const_add τ
        simpa [σn] using this
      · refine ⟨Set.mem_Ici.2 ?_, ?_⟩
        · have := hσn1 n; simp only [σn]; linarith
        · have := hσn1 n
          intro h
          have h' : τ + (T - τ) / ((n + 2 : ℕ) : ℝ) = τ := h
          linarith
    refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
      (f := fun n x => (σn n - τ)⁻¹ * (F (σn n) x - F τ x)) (fun n => ?_) ?_
    · have hI : σn n ∈ Icc t T := by
        have := hσn1 n; have := hσn2 n
        exact ⟨by simp only [σn]; linarith, by simp only [σn]; linarith⟩
      exact ((hFm _ hI).sub (hFm τ hτI)).const_mul _
    · filter_upwards [hlim] with x hx
      exact hx.comp hseq
  have hF'int : IntegrableOn (F' τ) S μ := by
    refine Integrable.mono' hG hmeas' ?_
    refine (ae_restrict_iff' hS).2 (ae_of_all _ (fun x hx => ?_))
    rw [Real.norm_eq_abs]; exact hF'b τ hτI x hx
  refine ⟨hF'int, ?_⟩
  have hEq : (slope (fun σ => ∫ x in S, F σ x ∂μ) τ) =ᶠ[𝓝[Ici τ \ {τ}] τ]
      (fun σ => ∫ x in S, (σ - τ)⁻¹ * (F σ x - F τ x) ∂μ) := by
    filter_upwards [hev] with σ hσ
    have hσI : σ ∈ Icc t T := ⟨le_trans hsτ hσ.1.le, hσ.2.le⟩
    simp only [slope, smul_eq_mul, vsub_eq_sub]
    rw [integral_const_mul, integral_sub (hFint σ hσI) (hFint τ hτI)]
  rw [hasDerivWithinAt_iff_tendsto_slope]
  exact Tendsto.congr' hEq.symm hT

end UnforcedLeray.Short.IIIa
