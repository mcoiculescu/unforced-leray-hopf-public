import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.Kernel
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.LogSubst

/-!
# `PartIII-b:C/rep/5/1/2/4/1/3/3/11`: atom representation of `psiMaj`

Source `the November 2 reference manuscript` 3611-3621 (`σ = τ + 2 log λ`).
The substitution `λ = e^{(σ-τ)/2}` (`logSubst`) writes `psiMaj(τ, y)` as an integral over
`σ < τ` of `(λ/2)` times the inner integral over `{ϱ z < θ ϱ y}`. The same integrand, restricted to
`Iio τ ×ˢ {ϱ z < θ ϱ y}`, is exactly `phKer · srcW`; the set integral over the product is the
iterated set integral (`setLIntegral_prod`), and the full integral dominates it.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.WYCore

/-- **Atom representation** (source 3611-3621 with `σ = τ + 2 log λ`):
`psiMaj(τ, y) ≤ ∫ phKer(τ, y; σ, z) srcW(σ, z) d(σ, z)`. -/
theorem psiMajRep : PsiMajRep := by
  intro R c θ G hG τ y
  set S : Set Space := {z : Space | ϱ z < θ * ϱ y} with hS
  have hSm : MeasurableSet S := measurableSet_lt measurable_ϱ measurable_const
  -- joint integrand of the inner integral, in (l, z)
  set Φ : ℝ × Space → ℝ≥0∞ := fun p =>
    ENNReal.ofReal ((‖y - p.1 • p.2‖ ^ 4)⁻¹) * srcW R c G (τ + 2 * Real.log p.1) p.2 with hΦ
  have hΦm : Measurable Φ := by
    have h1 : Measurable (fun p : ℝ × Space => (‖y - p.1 • p.2‖ ^ 4)⁻¹) := by fun_prop
    have h2 : Measurable (fun p : ℝ × Space => srcW R c G (τ + 2 * Real.log p.1) p.2) :=
      (measurable_srcW R c hG).comp
        ((measurable_const.add (measurable_const.mul (Real.measurable_log.comp measurable_fst))).prodMk
          measurable_snd)
    exact h1.ennreal_ofReal.mul h2
  have hΨm : Measurable ((Prod.snd ⁻¹' S).indicator Φ) :=
    hΦm.indicator (hSm.preimage measurable_snd)
  -- the restricted inner integral as a full integral of the indicator
  have hpsi : ∀ l : ℝ, ∫⁻ z in S, Φ (l, z) = ∫⁻ z, (Prod.snd ⁻¹' S).indicator Φ (l, z) := by
    intro l
    rw [← lintegral_indicator hSm]
    congr 1
  have hFm : Measurable (fun l : ℝ => ∫⁻ z in S, Φ (l, z)) := by
    have hfun : (fun l : ℝ => ∫⁻ z in S, Φ (l, z)) =
        fun l : ℝ => ∫⁻ z, (Prod.snd ⁻¹' S).indicator Φ (l, z) := funext hpsi
    rw [hfun]
    exact hΨm.lintegral_prod_right'
  -- the substitution λ = e^{(σ-τ)/2}
  have hL : ∫⁻ l in Ioo (0 : ℝ) 1, ∫⁻ z in S, Φ (l, z) =
      ∫⁻ σ in Iio τ, ENNReal.ofReal (Real.exp ((σ - τ) / 2) / 2) *
        ∫⁻ z in S, Φ (Real.exp ((σ - τ) / 2), z) :=
    logSubst τ (fun l : ℝ => ∫⁻ z in S, Φ (l, z)) hFm
  -- the integrand on the output-side product, in the atom variables
  set K : ℝ × Space → ℝ≥0∞ := fun a =>
    ENNReal.ofReal (Real.exp ((a.1 - τ) / 2) / 2) *
      (ENNReal.ofReal ((‖y - Real.exp ((a.1 - τ) / 2) • a.2‖ ^ 4)⁻¹) * srcW R c G a.1 a.2)
    with hK
  have hKm : Measurable K := by
    have h1 : Measurable (fun a : ℝ × Space => Real.exp ((a.1 - τ) / 2) / 2) := by fun_prop
    have h2 : Measurable (fun a : ℝ × Space => (‖y - Real.exp ((a.1 - τ) / 2) • a.2‖ ^ 4)⁻¹) := by
      fun_prop
    exact h1.ennreal_ofReal.mul (h2.ennreal_ofReal.mul (measurable_srcW R c hG))
  -- inner integrals agree with the constant-factored form
  have hinner : ∀ σ : ℝ, ∫⁻ z in S, K (σ, z) =
      ENNReal.ofReal (Real.exp ((σ - τ) / 2) / 2) * ∫⁻ z in S, Φ (Real.exp ((σ - τ) / 2), z) := by
    intro σ
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun z => ?_
    have hlog : τ + 2 * Real.log (Real.exp ((σ - τ) / 2)) = σ := by
      rw [Real.log_exp]; ring
    simp only [hK, hΦ]
    rw [hlog]
  -- the product set and the iterated integral
  have hA : MeasurableSet (Iio τ ×ˢ S) := measurableSet_Iio.prod hSm
  have hAK : ∫⁻ a in Iio τ ×ˢ S, K a = ∫⁻ σ in Iio τ, ∫⁻ z in S, K (σ, z) := by
    rw [Measure.volume_eq_prod]
    exact setLIntegral_prod K hKm.aemeasurable
  -- on the product set, the kernel `phKer · srcW` equals `K`
  have hPhKer : ∀ a ∈ Iio τ ×ˢ S, phKer θ τ y a.1 a.2 * srcW R c G a.1 a.2 = K a := by
    rintro ⟨σ, z⟩ ⟨hσ, hz⟩
    have hσ' : σ < τ := hσ
    have hz' : ϱ z < θ * ϱ y := hz
    simp only [hK, phKer]
    rw [if_pos ⟨hσ', hz'⟩, mul_assoc]
  have hRHS : ∫⁻ a in Iio τ ×ˢ S, phKer θ τ y a.1 a.2 * srcW R c G a.1 a.2 =
      ∫⁻ a in Iio τ ×ˢ S, K a :=
    setLIntegral_congr_fun hA hPhKer
  have hle : ∫⁻ a in Iio τ ×ˢ S, phKer θ τ y a.1 a.2 * srcW R c G a.1 a.2 ≤
      ∫⁻ a : ℝ × Space, phKer θ τ y a.1 a.2 * srcW R c G a.1 a.2 :=
    setLIntegral_le_lintegral _ _
  calc ∫⁻ l in Ioo (0 : ℝ) 1, ∫⁻ z in S, Φ (l, z)
      = ∫⁻ σ in Iio τ, ∫⁻ z in S, K (σ, z) :=
        hL.trans (lintegral_congr fun σ => (hinner σ).symm)
    _ = ∫⁻ a in Iio τ ×ˢ S, K a := hAK.symm
    _ = ∫⁻ a in Iio τ ×ˢ S, phKer θ τ y a.1 a.2 * srcW R c G a.1 a.2 := hRHS.symm
    _ ≤ ∫⁻ a : ℝ × Space, phKer θ τ y a.1 a.2 * srcW R c G a.1 a.2 := hle

end UnforcedLeray.Short.PartIIIb.Concrete.WYCore

end
