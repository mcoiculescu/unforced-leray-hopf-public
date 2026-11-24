import UnforcedLeray.Statement
import Mathlib.Tactic.Linarith

/-!
# Consequences and semantic checks for the target statement

These theorems verify that the concrete target has genuine L² nonuniqueness
and the expected consequences of the unforced energy equality. They do not
construct a solution or prove `MainClaim`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray

theorem l2Norm_nonneg (f : SpatialField) : 0 ≤ l2Norm f :=
  ENNReal.toReal_nonneg

theorem l2Norm_congr_ae {f g : SpatialField} (hfg : f =ᵐ[volume] g) :
    l2Norm f = l2Norm g :=
  congrArg ENNReal.toReal (eLpNorm_congr_ae hfg)

/-- Finite L² norms have no `toReal ∞ = 0` loophole. -/
theorem l2Norm_eq_zero_iff {f : SpatialField} (hf : MemLp f 2 volume) :
    l2Norm f = 0 ↔ f =ᵐ[volume] (0 : SpatialField) := by
  rw [l2Norm, ENNReal.toReal_eq_zero_iff]
  simp only [hf.2.ne, or_false]
  exact eLpNorm_eq_zero_iff hf.1 (by norm_num)

theorem toL2_sub {f g : SpatialField} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    toL2 (f - g) = toL2 f - toL2 g := by
  rw [toL2_of_memLp (hf.sub hg), toL2_of_memLp hf, toL2_of_memLp hg]
  exact hf.toLp_sub hg

/-- The stated separation norm is the distance in the actual L² quotient. -/
theorem dist_toL2 {f g : SpatialField} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    dist (toL2 f) (toL2 g) = l2Norm (f - g) := by
  rw [dist_eq_norm, ← toL2_sub hf hg, norm_toL2 (hf.sub hg)]

theorem toL2_eq_iff {f g : SpatialField} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    toL2 f = toL2 g ↔ f =ᵐ[volume] g := by
  rw [toL2_of_memLp hf, toL2_of_memLp hg]
  exact hf.toLp_eq_toLp_iff hg

theorem l2Norm_sub_eq_zero_of_ae_eq {f g : SpatialField} (hfg : f =ᵐ[volume] g) :
    l2Norm (f - g) = 0 := by
  have hz : f - g =ᵐ[volume] (0 : SpatialField) := by
    filter_upwards [hfg] with x hx
    simp only [Pi.sub_apply, Pi.zero_apply, hx, sub_self]
  exact (l2Norm_congr_ae hz).trans l2Norm_zero

/-- Positive separation rules out equality almost everywhere, not merely equality
of chosen pointwise representatives. No measurability hypothesis is hidden here. -/
theorem not_ae_eq_of_l2Norm_sub_pos {f g : SpatialField} (h : 0 < l2Norm (f - g)) :
    ¬ f =ᵐ[volume] g := by
  intro hfg
  exact (ne_of_gt h) (l2Norm_sub_eq_zero_of_ae_eq hfg)

theorem not_ae_eq_of_quantitative_separation {f g : SpatialField} {c σ t : ℝ}
    (hc : 0 < c) (ht : 0 < t)
    (hsep : c * Real.rpow t (σ + 1 / 4) ≤ l2Norm (f - g)) :
    ¬ f =ᵐ[volume] g :=
  not_ae_eq_of_l2Norm_sub_pos ((mul_pos hc (Real.rpow_pos_of_pos ht _)).trans_le hsep)

/-- A proved `MainClaim` would yield two distinct L² solution classes at every
positive time, both satisfying the concrete equation with exactly the same datum. -/
theorem mainClaim_implies_genuine_nonuniqueness (h : MainClaim) :
    ∃ T : ℝ, 0 < T ∧ ∃ u₀ : SpatialField, IsInitialDatum u₀ ∧
      ∃ u₁ u₂ : Velocity,
        (∃ p₁ G₁ H₁, IsTheoremASolution T u₀ u₁ p₁ G₁ H₁) ∧
        (∃ p₂ G₂ H₂, IsTheoremASolution T u₀ u₂ p₂ G₂ H₂) ∧
        ∀ t ∈ Ioc (0 : ℝ) T, ¬ u₂ t =ᵐ[volume] u₁ t := by
  obtain ⟨T, u₀, u₁, u₂, p₁, p₂, G₁, G₂, H₁, H₂, c, σ,
    hT, hdatum, h₁, h₂, hc, _, _, hsep, _, _, _⟩ := h
  refine ⟨T, hT, u₀, hdatum, u₁, u₂, ⟨p₁, G₁, H₁, h₁⟩,
    ⟨p₂, G₂, H₂, h₂⟩, ?_⟩
  intro t ht
  exact not_ae_eq_of_quantitative_separation hc ht.1 (hsep t ht)

namespace IsTheoremASolution

variable {T : ℝ} {u₀ : SpatialField} {u : Velocity} {p : Pressure}
  {G : FirstDerivatives} {H : SecondDerivatives}

/-- Every pair of admissible times has decreasing kinetic energy. -/
theorem l2Norm_sq_le (h : IsTheoremASolution T u₀ u p G H)
    {t₀ t₁ : ℝ} (ht₀ : 0 ≤ t₀) (horder : t₀ ≤ t₁) (ht₁ : t₁ ≤ T) :
    l2Norm (u t₁) ^ 2 ≤ l2Norm (u t₀) ^ 2 := by
  have he := h.energy_equality t₀ t₁ ht₀ horder ht₁
  have hd : 0 ≤ ∫ t in Ioo t₀ t₁, dissipation G t :=
    integral_nonneg (fun t => dissipation_nonneg G t)
  linarith

theorem l2Norm_le (h : IsTheoremASolution T u₀ u p G H)
    {t₀ t₁ : ℝ} (ht₀ : 0 ≤ t₀) (horder : t₀ ≤ t₁) (ht₁ : t₁ ≤ T) :
    l2Norm (u t₁) ≤ l2Norm (u t₀) := by
  have he := h.l2Norm_sq_le ht₀ horder ht₁
  have hn₀ := l2Norm_nonneg (u t₀)
  have hn₁ := l2Norm_nonneg (u t₁)
  nlinarith

theorem antitoneOn_l2Norm (h : IsTheoremASolution T u₀ u p G H) :
    AntitoneOn (fun t => l2Norm (u t)) (Icc (0 : ℝ) T) := by
  intro s hs t ht hst
  exact h.l2Norm_le hs.1 hst ht.2

/-- This uses the actual zero datum, without assuming `IsInitialDatum`, whose
nonzero clause is specific to the target nonuniqueness theorem. -/
theorem ae_zero_of_zero_datum (h : IsTheoremASolution T u₀ u p G H)
    (hzero : u₀ =ᵐ[volume] (0 : SpatialField)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    u t =ᵐ[volume] (0 : SpatialField) := by
  have hnorm₀ : l2Norm (u 0) = 0 :=
    (l2Norm_congr_ae (h.initial_value.trans hzero)).trans l2Norm_zero
  have hle := h.l2Norm_le (t₀ := 0) le_rfl ht.1 ht.2
  rw [hnorm₀] at hle
  exact (l2Norm_eq_zero_iff (h.memL2 t ht)).mp
    (le_antisymm hle (l2Norm_nonneg (u t)))

theorem continuousOn_l2Norm (h : IsTheoremASolution T u₀ u p G H) :
    ContinuousOn (fun t => l2Norm (u t)) (Icc (0 : ℝ) T) := by
  have hn : ContinuousOn (fun t => ‖toL2 (u t)‖) (Icc (0 : ℝ) T) :=
    h.continuousL2.norm
  exact hn.congr (fun t ht => (norm_toL2 (h.memL2 t ht)).symm)

end IsTheoremASolution

end UnforcedLeray
