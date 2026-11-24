import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_4
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.CausalLimitAE.SliceAE
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.CausalLimitAE.SliceClauses

/-!
# `PartII-a:N01/9/1/4/4`: `EnergyLimitDivFree`

Source `the November 2 reference manuscript`
lines 3426-3430. The tested divergence identity passes to the `L²` limit at almost every age (the tensor is replaced by `0`, so no measurability of `G` is needed).

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
theorem eLpNorm_two_tendsto_zero_of_lint_div {α : Type*} [MeasurableSpace α] {μ : Measure α}
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


/-- Divergence part of the slice limit (the pairing argument of `sc_at_age`, tensor omitted). -/
theorem div_at_age {c : ℝ} {A : ℕ → (ℝ × ℝ) → Fin 2 → ℂ} {B : (ℝ × ℝ) → Fin 2 → ℂ}
    (hAm : ∀ n i, Measurable fun x => A n x i) (hBm : ∀ i, Measurable fun x => B x i)
    (hAL2 : ∀ n, ∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (A n x) ^ 2) < ⊤)
    (hdiv : ∀ n, ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ →
      ∫ x in B0579.cell c, (A n x 0 * (B0579.pd 0 ψ x : ℂ) + A n x 1 * (B0579.pd 1 ψ x : ℂ)) = 0)
    (hconvB : Tendsto (fun n => ∫⁻ x in B0579.cell c,
      ENNReal.ofReal (vnorm2 (fun i => A n x i - B x i) ^ 2)) atTop (𝓝 0)) :
    ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ →
      ∫ x in B0579.cell c, (B x 0 * (B0579.pd 0 ψ x : ℂ) + B x 1 * (B0579.pd 1 ψ x : ℂ)) = 0 := by
  have hA2 : ∀ n i, ∫⁻ x in B0579.cell c, ENNReal.ofReal (‖A n x i‖ ^ 2) < ⊤ := by
    intro n i
    refine lt_of_le_of_lt (lintegral_mono (fun x => ?_)) (hAL2 n)
    exact ENNReal.ofReal_le_ofReal (UnforcedLeray.Short.IIIa.sc_norm_comp_sq_le (A n x) i)
  have hconvB' : ∀ i, Tendsto
      (fun n => ∫⁻ x in B0579.cell c, ENNReal.ofReal (‖A n x i - B x i‖ ^ 2)) atTop (𝓝 0) :=
    fun i => UnforcedLeray.Short.IIIa.sc_vnorm_comp_tendsto (volume.restrict (B0579.cell c))
      (F := fun n x k => A n x k - B x k) hconvB i
  have hBL2 : ∀ i, ∫⁻ x in B0579.cell c, ENNReal.ofReal (‖B x i‖ ^ 2) < ⊤ := fun i =>
    UnforcedLeray.Short.IIIa.sc_limit_L2 (A := fun n x => A n x i) (B := fun x => B x i)
      (fun n => hAm n i) (fun n => hA2 n i) (hconvB' i)
  intro ψ hψ
  have hψ0 : B0579.IsCylTest c (B0579.pd 0 ψ) := hψ.pd 0
  have hψ1 : B0579.IsCylTest c (B0579.pd 1 ψ) := hψ.pd 1
  have T0 := UnforcedLeray.Short.IIIa.sc_tendsto_integral_mul (μ := volume.restrict (B0579.cell c))
    (fn := fun n x => A n x 0) (f0 := fun x => B x 0)
    (w := fun x => (B0579.pd 0 ψ x : ℂ))
    (fun n => hAm n 0) (hBm 0) (UnforcedLeray.Short.IIIa.sc_cyl_meas hψ0) (fun n => hA2 n 0)
    (hBL2 0) (UnforcedLeray.Short.IIIa.sc_test_L2 hψ0) (hconvB' 0)
  have T1 := UnforcedLeray.Short.IIIa.sc_tendsto_integral_mul (μ := volume.restrict (B0579.cell c))
    (fn := fun n x => A n x 1) (f0 := fun x => B x 1)
    (w := fun x => (B0579.pd 1 ψ x : ℂ))
    (fun n => hAm n 1) (hBm 1) (UnforcedLeray.Short.IIIa.sc_cyl_meas hψ1) (fun n => hA2 n 1)
    (hBL2 1) (UnforcedLeray.Short.IIIa.sc_test_L2 hψ1) (hconvB' 1)
  have hI : ∀ n, (∫ x in B0579.cell c, A n x 0 * (B0579.pd 0 ψ x : ℂ)) +
      ∫ x in B0579.cell c, A n x 1 * (B0579.pd 1 ψ x : ℂ) = 0 := by
    intro n
    rw [← integral_add
      (UnforcedLeray.Short.IIIa.sc_integrable (hAm n 0) (UnforcedLeray.Short.IIIa.sc_cyl_meas hψ0)
        (hA2 n 0) (UnforcedLeray.Short.IIIa.sc_test_L2 hψ0))
      (UnforcedLeray.Short.IIIa.sc_integrable (hAm n 1) (UnforcedLeray.Short.IIIa.sc_cyl_meas hψ1)
        (hA2 n 1) (UnforcedLeray.Short.IIIa.sc_test_L2 hψ1))]
    exact hdiv n ψ hψ
  have hzero : Tendsto (fun n => (∫ x in B0579.cell c, A n x 0 * (B0579.pd 0 ψ x : ℂ)) +
      ∫ x in B0579.cell c, A n x 1 * (B0579.pd 1 ψ x : ℂ)) atTop (𝓝 0) := by
    simp only [hI]
    exact tendsto_const_nhds
  have hlim := tendsto_nhds_unique (T0.add T1) hzero
  rw [integral_add
    (UnforcedLeray.Short.IIIa.sc_integrable (hBm 0) (UnforcedLeray.Short.IIIa.sc_cyl_meas hψ0)
      (hBL2 0) (UnforcedLeray.Short.IIIa.sc_test_L2 hψ0))
    (UnforcedLeray.Short.IIIa.sc_integrable (hBm 1) (UnforcedLeray.Short.IIIa.sc_cyl_meas hψ1)
      (hBL2 1) (UnforcedLeray.Short.IIIa.sc_test_L2 hψ1))]
  exact hlim

theorem energyLimitDivFree : UnforcedLeray.Short.PartIIa.N01.EnergyLimitDivFree := by
  unfold EnergyLimitDivFree
  intro c hc bk Gk b G hE hL hbm
  unfold EnergyL2Limit at hL
  obtain ⟨hLb, -⟩ := hL
  have hgain1 : ∀ s : ℝ, gainG 0 1 s = 1 := fun s => by simp [gainG]
  have hidV : ∀ f : ℝ × (ℝ × ℝ) → Fin 2 → ℂ, gainConj 0 1 f = f := fun f => by
    funext p
    simp [gainConj, hgain1]
  have hcal : Tendsto (fun k => hCalNorm c (gainConj 0 1 (fun p i => bk k p i - b p i)))
      atTop (𝓝 0) := by
    have h1 := eLpNorm_two_tendsto_zero_of_lint_div (μ := ageμ c (-3 / 2))
      (F := fun k p => vnorm2 (fun i => bk k p i - b p i)) (fun k p => Real.sqrt_nonneg _) hLb
    refine Tendsto.congr (fun k => ?_) h1
    rw [hidV]
    rfl
  have hcalT : Tendsto (fun k : ℕ => tCalNorm c (gainConj 0 1
      (fun p i j => (fun (_ : ℕ) (_ : ℝ × (ℝ × ℝ)) (_ _ : Fin 2) => (0 : ℂ)) k p i j -
        (fun (_ : ℝ × (ℝ × ℝ)) (_ _ : Fin 2) => (0 : ℂ)) p i j))) atTop (𝓝 0) := by
    exact tendsto_const_nhds.congr (fun k => by simp [tCalNorm, gainConj, tnorm2])
  obtain ⟨φ, hφ, hae⟩ := UnforcedLeray.Short.IIIa.causalSliceAE c 1 0 hc one_pos bk
    (fun _ _ _ _ => 0) b (fun _ _ _ => 0)
    (fun k i => (hE k).measurable i) hbm (fun _ _ _ => measurable_const)
    (fun _ _ => measurable_const) hcal hcalT
  have hφm : ∀ n, Measurable fun p : ℝ × (ℝ × ℝ) =>
      ENNReal.ofReal (vnorm2 (bk (φ n) p) ^ 2) := fun n =>
    ENNReal.measurable_ofReal.comp
      ((UnforcedLeray.Short.IIIa.causalLin_measurable_vnorm2 (hE (φ n)).measurable).pow_const 2)
  have hgood := UnforcedLeray.Short.IIIa.sc_good_ages c
    (φ := fun n p => ENNReal.ofReal (vnorm2 (bk (φ n) p) ^ 2)) hφm
    (fun n s₁ s₂ h₁ h₂ => lt_of_le_of_lt
      (lintegral_mono fun p => ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (sq_nonneg _)))
      ((hE (φ n)).energyLoc s₁ s₂ h₁ h₂))
  have hdivAll : ∀ᵐ s ∂(volume : Measure ℝ), ∀ k, 0 < s → ∀ ψ : ℝ × ℝ → ℝ,
      UnforcedLeray.B0579.IsCylTest c ψ →
      ∫ x in UnforcedLeray.B0579.cell c,
        (bk k (s, x) 0 * (UnforcedLeray.B0579.pd 0 ψ x : ℂ) +
          bk k (s, x) 1 * (UnforcedLeray.B0579.pd 1 ψ x : ℂ)) = 0 :=
    ae_all_iff.2 fun k => (hE k).divFreeAE
  have hfin : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), ∀ ψ : ℝ × ℝ → ℝ,
      UnforcedLeray.B0579.IsCylTest c ψ →
      ∫ x in UnforcedLeray.B0579.cell c,
        (b (s, x) 0 * (UnforcedLeray.B0579.pd 0 ψ x : ℂ) +
          b (s, x) 1 * (UnforcedLeray.B0579.pd 1 ψ x : ℂ)) = 0 := by
    filter_upwards [hae, hgood, ae_restrict_of_ae hdivAll,
      ae_restrict_mem measurableSet_Ioi] with s hs hgs hdk hsI
    have hs0 : (0 : ℝ) < s := hsI
    exact div_at_age (c := c) (A := fun n x => bk (φ n) (s, x)) (B := fun x => b (s, x))
      (fun n i => ((hE (φ n)).measurable i).comp measurable_prodMk_left)
      (fun i => (hbm i).comp measurable_prodMk_left)
      (fun n => by simpa [UnforcedLeray.Short.IIIa.vnorm2] using hgs n)
      (fun n ψ hψ => hdk (φ n) hs0 ψ hψ) hs.1
  exact (ae_restrict_iff' measurableSet_Ioi).1 hfin

end UnforcedLeray.Short.PartIIa.N01
