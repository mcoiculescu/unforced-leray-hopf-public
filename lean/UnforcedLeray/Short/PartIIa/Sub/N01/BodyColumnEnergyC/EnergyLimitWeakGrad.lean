import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_4
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.CausalLimitAE.SliceAE
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.CausalLimitAE.SliceClauses

/-!
# `PartII-a:N01/9/1/4/5`: `EnergyLimitWeakGrad`

Source `the November 2 reference manuscript`
lines 3426-3430. The weak cell derivative identity passes to the `L²` limit at almost every age.

Route. The gain is trivial (`γ = 0`, `ν = 1`, so `gainG = 1`). The `L²(ageμ)` convergence
of `b_k` and `G_k` gives the `𝓗`- and `𝒯`-norm convergence of `causalSliceAE`, which yields a
subsequence `φ` along which, for almost every age `s > 0`, the `L²(cell)` slices converge
(Tonelli plus the summable-subsequence trick, already proved). At such an age the slice energies
are finite (`sc_good_ages`) and the slice identities hold for all `k` (countable intersection of
the `a.e.` clauses of `IsEnergyFieldAE`), so `sc_at_age` gives the weak derivative of the limit.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff
open UnforcedLeray.Axi (ageμ)
open UnforcedLeray.Short.IIIa (vnorm2 tnorm2 HasWeakCellDerivC hCalNorm tCalNorm gainConj gainG)
open UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst (IsEnergyFieldAE)

namespace UnforcedLeray.Short.PartIIa.N01

/-- Pure measure theory: an `ENNReal` `L²`-square tending to `0` gives an `eLpNorm` tending to `0`. -/
theorem eLpNorm_two_tendsto_zero_of_lint {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℕ → α → ℝ} (hF : ∀ n x, 0 ≤ F n x)
    (h : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (F n x ^ 2) ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (F n) 2 μ) atTop (𝓝 0) := by
  have hp : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  have key : ∀ n, eLpNorm (F n) 2 μ = (∫⁻ x, ENNReal.ofReal (F n x ^ 2) ∂μ) ^ (2⁻¹ : ℝ) := by
    intro n
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), hp]
    congr 1
    · apply lintegral_congr
      intro x
      rw [ENNReal.rpow_two, Real.enorm_eq_ofReal (hF n x), ENNReal.ofReal_pow (hF n x)]
    · norm_num
  have hlim : Tendsto (fun n => (∫⁻ x, ENNReal.ofReal (F n x ^ 2) ∂μ) ^ (2⁻¹ : ℝ)) atTop
      (𝓝 ((0 : ℝ≥0∞) ^ (2⁻¹ : ℝ))) :=
    ((ENNReal.continuous_rpow_const).tendsto 0).comp h
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at hlim
  exact Tendsto.congr (fun n => (key n).symm) hlim

theorem energyLimitWeakGrad : UnforcedLeray.Short.PartIIa.N01.EnergyLimitWeakGrad := by
  unfold EnergyLimitWeakGrad
  intro c hc bk Gk b G hE hL hbm hGm
  unfold EnergyL2Limit at hL
  obtain ⟨hLb, hLG⟩ := hL
  -- the gain with `γ = 0`, `ν = 1` is the identity
  have hgain1 : ∀ s : ℝ, gainG 0 1 s = 1 := fun s => by simp [gainG]
  have hidV : ∀ f : ℝ × (ℝ × ℝ) → Fin 2 → ℂ, gainConj 0 1 f = f := fun f => by
    funext p
    simp [gainConj, hgain1]
  have hidT : ∀ f : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ, gainConj 0 1 f = f := fun f => by
    funext p
    simp [gainConj, hgain1]
  have hcal : Tendsto (fun k => hCalNorm c (gainConj 0 1 (fun p i => bk k p i - b p i)))
      atTop (𝓝 0) := by
    have h1 := eLpNorm_two_tendsto_zero_of_lint (μ := ageμ c (-3 / 2))
      (F := fun k p => vnorm2 (fun i => bk k p i - b p i)) (fun k p => Real.sqrt_nonneg _) hLb
    refine Tendsto.congr (fun k => ?_) h1
    rw [hidV]
    rfl
  have hcalT : Tendsto (fun k => tCalNorm c (gainConj 0 1 (fun p i j => Gk k p i j - G p i j)))
      atTop (𝓝 0) := by
    have h1 := eLpNorm_two_tendsto_zero_of_lint (μ := ageμ c (-1 / 2))
      (F := fun k p => tnorm2 (fun i j => Gk k p i j - G p i j)) (fun k p => Real.sqrt_nonneg _) hLG
    refine Tendsto.congr (fun k => ?_) h1
    rw [hidT]
    rfl
  -- a subsequence with a.e. convergent `L²(cell)` slices
  obtain ⟨φ, hφ, hae⟩ := UnforcedLeray.Short.IIIa.causalSliceAE c 1 0 hc one_pos bk Gk b G
    (fun k i => (hE k).measurable i) hbm
    (fun k i j => (hE k).gradMeasurable i j) hGm hcal hcalT
  -- measurability of the subsequence energy
  have hφm : ∀ n, Measurable fun p : ℝ × (ℝ × ℝ) =>
      ENNReal.ofReal (vnorm2 (bk (φ n) p) ^ 2 + tnorm2 (Gk (φ n) p) ^ 2) := fun n =>
    ENNReal.measurable_ofReal.comp
      (((UnforcedLeray.Short.IIIa.causalLin_measurable_vnorm2 (hE (φ n)).measurable).pow_const 2).add
        ((UnforcedLeray.Short.IIIa.causalLin_measurable_tnorm2 (hE (φ n)).gradMeasurable).pow_const 2))
  have hgood := UnforcedLeray.Short.IIIa.sc_good_ages c
    (φ := fun n p => ENNReal.ofReal (vnorm2 (bk (φ n) p) ^ 2 + tnorm2 (Gk (φ n) p) ^ 2)) hφm
    (fun n s₁ s₂ h₁ h₂ => (hE (φ n)).energyLoc s₁ s₂ h₁ h₂)
  -- the slice identities hold for every `k` at almost every age
  have hdivAll : ∀ᵐ s ∂(volume : Measure ℝ), ∀ k, 0 < s → ∀ ψ : ℝ × ℝ → ℝ,
      UnforcedLeray.B0579.IsCylTest c ψ →
      ∫ x in UnforcedLeray.B0579.cell c,
        (bk k (s, x) 0 * (UnforcedLeray.B0579.pd 0 ψ x : ℂ) +
          bk k (s, x) 1 * (UnforcedLeray.B0579.pd 1 ψ x : ℂ)) = 0 :=
    ae_all_iff.2 fun k => (hE k).divFreeAE
  have hweakAll : ∀ᵐ s ∂(volume : Measure ℝ), ∀ k, 0 < s → ∀ i j,
      HasWeakCellDerivC c j (fun x => bk k (s, x) i) (fun x => Gk k (s, x) i j) :=
    ae_all_iff.2 fun k => (hE k).weakGradAE
  have hfin : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), ∀ i j,
      HasWeakCellDerivC c j (fun x => b (s, x) i) (fun x => G (s, x) i j) := by
    filter_upwards [hae, hgood, ae_restrict_of_ae hdivAll, ae_restrict_of_ae hweakAll,
      ae_restrict_mem measurableSet_Ioi] with s hs hgs hdk hwk hsI
    have hs0 : (0 : ℝ) < s := hsI
    exact (UnforcedLeray.Short.IIIa.sc_at_age (c := c)
      (A := fun n x => bk (φ n) (s, x)) (B := fun x => b (s, x))
      (GA := fun n x => Gk (φ n) (s, x)) (GB := fun x => G (s, x))
      (fun n i => ((hE (φ n)).measurable i).comp measurable_prodMk_left)
      (fun i => (hbm i).comp measurable_prodMk_left)
      (fun n i j => ((hE (φ n)).gradMeasurable i j).comp measurable_prodMk_left)
      (fun i j => (hGm i j).comp measurable_prodMk_left)
      (fun n => hgs n) (fun n ψ hψ => hdk (φ n) hs0 ψ hψ)
      (fun n i j => hwk (φ n) hs0 i j) hs.1 hs.2).2
  exact (ae_restrict_iff' measurableSet_Ioi).1 hfin

end UnforcedLeray.Short.PartIIa.N01
