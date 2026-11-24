import UnforcedLeray.Short.PartIIa.StatementsRing
import UnforcedLeray.Short.PartIIa.Tasks.R02.HeatProfile
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanCoeff
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Sub.RingLiftOffAxis_Sub.RingLiftPtJet
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Sub.RingLiftOffAxis_Sub.RingProfileMeridJet
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Sub.RingLiftOffAxis_Sub.HeatFieldJet

/-!


Source of record: `the November 2 reference manuscript`, lines 1310–1325.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0190
open UnforcedLeray.Short.IIb
open UnforcedLeray.Short.PartIIIb.Concrete
open UnforcedLeray.Short.PartI (meanCoeff heatKernel1)

/-! ### 1. `R`-uniform meridional and Cartesian lift jets -/

/-- `R`-uniform version of `IIb.ringProfileJet` for `1 ≤ R` (since `|R⁻¹| ≤ 1`). -/
theorem ringProfileJet_unif (i : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ) (Φ : ℝ × (ℝ × ℝ) → ℝ),
      1 ≤ R → ContDiffOn ℝ ∞ Φ (Ioi 0 ×ˢ univ) →
      ∀ y : ℝ × (ℝ × ℝ), 0 < y.1 →
        ‖iteratedFDeriv ℝ i (fun z => Axi.ringStreamProfile R Φ z 0) y‖ ≤
          C * ∑ l ∈ Finset.range (i + 2), ‖iteratedFDeriv ℝ l Φ y‖ ∧
        ‖iteratedFDeriv ℝ i (fun z => Axi.ringStreamProfile R Φ z 1) y‖ ≤
          C * (1 + |y.1| + |y.2.2|) * ∑ l ∈ Finset.range (i + 2), ‖iteratedFDeriv ℝ l Φ y‖ := by
  refine ⟨2 + 3 * (((i : ℝ) + 1) * 2 ^ i), by positivity, fun R Φ hR1 hΦ y hy => ?_⟩
  have hR0 : 0 < R := zero_lt_one.trans_le hR1
  have hRinv : |R⁻¹| ≤ 1 := by
    rw [abs_of_pos (inv_pos.2 hR0)]
    exact inv_le_one_of_one_le₀ hR1
  have e0 : ∀ z, Axi.ringStreamProfile R Φ z 0 = -(fderiv ℝ Φ z (0, (0, 1))) := by
    intro z; rw [ringStreamProfile_apply_zero]; rfl
  have e1 : ∀ z, Axi.ringStreamProfile R Φ z 1 =
      ((fderiv ℝ Φ z (0, (1, 0)) + R⁻¹ * Φ z) - (2 * R⁻¹) * (z.1 * fderiv ℝ Φ z (1, (0, 0))))
        - R⁻¹ * (z.2.2 * fderiv ℝ Φ z (0, (0, 1))) := by
    intro z
    rw [ringStreamProfile_apply_one]
    simp only [Axi.dQ, Axi.dS, Axi.dEta]
    ring
  have hF1 : ContDiffOn ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => z.1) (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    contDiff_fst.contDiffOn
  have hF2 : ContDiffOn ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => z.2.2)
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    (contDiff_snd.comp contDiff_snd).contDiffOn
  have hcΦ : ContDiffOn ℝ ∞ (fun z => R⁻¹ * Φ z) (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    (contDiffOn_const (c := R⁻¹)).mul hΦ
  have hA : ContDiffOn ℝ ∞ (fun z => fderiv ℝ Φ z (0, (1, 0)) + R⁻¹ * Φ z)
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    (IIb.contDiffOn_fderiv_apply hΦ _).add hcΦ
  have hB : ContDiffOn ℝ ∞ (fun z => (2 * R⁻¹) * (z.1 * fderiv ℝ Φ z (1, (0, 0))))
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    (contDiffOn_const (c := 2 * R⁻¹)).mul (hF1.mul (IIb.contDiffOn_fderiv_apply hΦ _))
  have hC : ContDiffOn ℝ ∞ (fun z => R⁻¹ * (z.2.2 * fderiv ℝ Φ z (0, (0, 1))))
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    (contDiffOn_const (c := R⁻¹)).mul (hF2.mul (IIb.contDiffOn_fderiv_apply hΦ _))
  have hyU : y ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := IIb.mem_Uo.2 hy
  have hM0 : 0 ≤ ∑ l ∈ Finset.range (i + 2), ‖iteratedFDeriv ℝ l Φ y‖ :=
    Finset.sum_nonneg (fun l _ => norm_nonneg _)
  have hMj : ∀ j, j ≤ i + 1 → ‖iteratedFDeriv ℝ j Φ y‖ ≤
      ∑ l ∈ Finset.range (i + 2), ‖iteratedFDeriv ℝ l Φ y‖ := fun j hj =>
    Finset.single_le_sum (f := fun l => ‖iteratedFDeriv ℝ l Φ y‖)
      (fun l _ => norm_nonneg _) (Finset.mem_range.2 (by omega))
  set M := ∑ l ∈ Finset.range (i + 2), ‖iteratedFDeriv ℝ l Φ y‖
  have hD : ∀ v : ℝ × (ℝ × ℝ), ‖v‖ ≤ 1 → ∀ k ≤ i,
      ‖iteratedFDeriv ℝ k (fun z => fderiv ℝ Φ z v) y‖ ≤ M := by
    intro v hv k hk
    refine (IIb.norm_iteratedFDeriv_fderiv_apply_le hΦ hyU v k).trans ?_
    calc ‖v‖ * ‖iteratedFDeriv ℝ (k + 1) Φ y‖ ≤ 1 * M :=
          mul_le_mul hv (hMj (k + 1) (by omega)) (norm_nonneg _) zero_le_one
      _ = M := one_mul M
  have nE : ‖((0 : ℝ), ((0 : ℝ), (1 : ℝ)))‖ ≤ 1 := by simp [Prod.norm_def]
  have nS : ‖((1 : ℝ), ((0 : ℝ), (0 : ℝ)))‖ ≤ 1 := by simp [Prod.norm_def]
  have nQ : ‖((0 : ℝ), ((1 : ℝ), (0 : ℝ)))‖ ≤ 1 := by simp [Prod.norm_def]
  have hc1 : ∀ k, ‖iteratedFDeriv ℝ k (fun z : ℝ × (ℝ × ℝ) => z.1) y‖ ≤ 1 + |y.1| := fun k => by
    simpa [IIb.t1Proj, Real.norm_eq_abs] using
      IIb.norm_iteratedFDeriv_clm_le IIb.t1Proj IIb.norm_t1Proj_le k y
  have hc2 : ∀ k, ‖iteratedFDeriv ℝ k (fun z : ℝ × (ℝ × ℝ) => z.2.2) y‖ ≤ 1 + |y.2.2| := fun k => by
    simpa [IIb.t2Proj, Real.norm_eq_abs] using
      IIb.norm_iteratedFDeriv_clm_le IIb.t2Proj IIb.norm_t2Proj_le k y
  have hG1 := IIb.norm_iteratedFDeriv_mul_le_of hF1 (IIb.contDiffOn_fderiv_apply hΦ (1, (0, 0))) hyU i
    hc1 (fun k hk => hD _ nS k hk) (by positivity) hM0
  have hG2 := IIb.norm_iteratedFDeriv_mul_le_of hF2 (IIb.contDiffOn_fderiv_apply hΦ (0, (0, 1))) hyU i
    hc2 (fun k hk => hD _ nE k hk) (by positivity) hM0
  have hΦi : ‖iteratedFDeriv ℝ i Φ y‖ ≤ M := hMj i (by omega)
  have hK : 0 ≤ ((i : ℝ) + 1) * 2 ^ i := by positivity
  have hE0 : ContDiffAt ℝ i (fun z => fderiv ℝ Φ z (0, (0, 1))) y :=
    IIb.contDiffAt_of_mem (IIb.contDiffOn_fderiv_apply hΦ _) hyU
  have bound0 : ‖iteratedFDeriv ℝ i (fun z => Axi.ringStreamProfile R Φ z 0) y‖ ≤ M := by
    have hfun : (fun z => Axi.ringStreamProfile R Φ z 0) =
        fun z => -(fderiv ℝ Φ z (0, (0, 1))) := funext e0
    rw [hfun]
    exact (IIb.norm_iter_neg_le' i hE0).trans (hD _ nE i le_rfl)
  have hfun1 : (fun z => Axi.ringStreamProfile R Φ z 1) =
      fun z => ((fderiv ℝ Φ z (0, (1, 0)) + R⁻¹ * Φ z) -
        (2 * R⁻¹) * (z.1 * fderiv ℝ Φ z (1, (0, 0)))) - R⁻¹ * (z.2.2 * fderiv ℝ Φ z (0, (0, 1))) :=
    funext e1
  have TA : ‖iteratedFDeriv ℝ i (fun z => (fderiv ℝ Φ z (0, (1, 0)) + R⁻¹ * Φ z) -
      (2 * R⁻¹) * (z.1 * fderiv ℝ Φ z (1, (0, 0)))) y‖ ≤
      (M + |R⁻¹| * M) + |2 * R⁻¹| * ((((i : ℝ) + 1) * 2 ^ i) * (1 + |y.1|) * M) := by
    refine (IIb.norm_iter_sub_le' i (IIb.contDiffAt_of_mem hA hyU) (IIb.contDiffAt_of_mem hB hyU)).trans ?_
    apply add_le_add
    · refine (IIb.norm_iter_add_le' i (IIb.contDiffAt_of_mem (IIb.contDiffOn_fderiv_apply hΦ _) hyU)
        (IIb.contDiffAt_of_mem hcΦ hyU)).trans ?_
      apply add_le_add (hD _ nQ i le_rfl)
      exact (IIb.norm_iter_const_mul_le' R⁻¹ i (IIb.contDiffAt_of_mem hΦ hyU)).trans
        (mul_le_mul_of_nonneg_left hΦi (abs_nonneg _))
    · exact (IIb.norm_iter_const_mul_le' (2 * R⁻¹) i
        (IIb.contDiffAt_of_mem (hF1.mul (IIb.contDiffOn_fderiv_apply hΦ (1, (0, 0)))) hyU)).trans
        (mul_le_mul_of_nonneg_left hG1 (abs_nonneg _))
  have TC : ‖iteratedFDeriv ℝ i (fun z => R⁻¹ * (z.2.2 * fderiv ℝ Φ z (0, (0, 1)))) y‖ ≤
      |R⁻¹| * ((((i : ℝ) + 1) * 2 ^ i) * (1 + |y.2.2|) * M) :=
    (IIb.norm_iter_const_mul_le' R⁻¹ i
      (IIb.contDiffAt_of_mem (hF2.mul (IIb.contDiffOn_fderiv_apply hΦ (0, (0, 1)))) hyU)).trans
      (mul_le_mul_of_nonneg_left hG2 (abs_nonneg _))
  have bound1 : ‖iteratedFDeriv ℝ i (fun z => Axi.ringStreamProfile R Φ z 1) y‖
      ≤ (2 + 3 * (((i : ℝ) + 1) * 2 ^ i)) * (1 + |y.1| + |y.2.2|) * M := by
    rw [hfun1]
    refine (IIb.norm_iter_sub_le' i (IIb.contDiffAt_of_mem (hA.sub hB) hyU)
      (IIb.contDiffAt_of_mem hC hyU)).trans ?_
    have h2 : |2 * R⁻¹| = 2 * |R⁻¹| := by rw [abs_mul, abs_two]
    rw [h2] at TA
    have hle_R : 1 + |R⁻¹| + 3 * |R⁻¹| * (((i : ℝ) + 1) * 2 ^ i) ≤
        2 + 3 * (((i : ℝ) + 1) * 2 ^ i) := by nlinarith
    have hid : (1 + |R⁻¹| + 3 * |R⁻¹| * (((i : ℝ) + 1) * 2 ^ i)) * (1 + |y.1| + |y.2.2|) * M -
        ((M + |R⁻¹| * M) + 2 * |R⁻¹| * ((((i : ℝ) + 1) * 2 ^ i) * (1 + |y.1|) * M) +
          |R⁻¹| * ((((i : ℝ) + 1) * 2 ^ i) * (1 + |y.2.2|) * M)) =
        (|y.1| + |y.2.2|) * M + |R⁻¹| * (|y.1| + |y.2.2|) * M +
          |R⁻¹| * (((i : ℝ) + 1) * 2 ^ i) * M * (|y.1| + 2 * |y.2.2|) := by ring
    have hnn : 0 ≤ (|y.1| + |y.2.2|) * M + |R⁻¹| * (|y.1| + |y.2.2|) * M +
          |R⁻¹| * (((i : ℝ) + 1) * 2 ^ i) * M * (|y.1| + 2 * |y.2.2|) := by positivity
    have key : (M + |R⁻¹| * M) + 2 * |R⁻¹| * ((((i : ℝ) + 1) * 2 ^ i) * (1 + |y.1|) * M) +
        |R⁻¹| * ((((i : ℝ) + 1) * 2 ^ i) * (1 + |y.2.2|) * M) ≤
        (1 + |R⁻¹| + 3 * |R⁻¹| * (((i : ℝ) + 1) * 2 ^ i)) * (1 + |y.1| + |y.2.2|) * M := by
      linarith [hid, hnn]
    refine (add_le_add TA TC).trans (key.trans ?_)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hle_R (by positivity)) hM0
  have hC1 : (1 : ℝ) ≤ 2 + 3 * (((i : ℝ) + 1) * 2 ^ i) := by linarith
  exact ⟨bound0.trans (le_mul_of_one_le_left hM0 hC1), bound1⟩

/-- `R`-uniform meridional vector jet bound for `Axi.ringStreamProfile R Φ` (`1 ≤ R`). -/
theorem ringProfileMeridJet_unif (i : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ) (Φ : ℝ × (ℝ × ℝ) → ℝ),
      1 ≤ R → ContDiffOn ℝ ∞ Φ (Ioi 0 ×ˢ univ) →
      ContDiffOn ℝ ∞ (Axi.ringStreamProfile R Φ) (Ioi 0 ×ˢ univ) ∧
      ∀ y : ℝ × (ℝ × ℝ), 0 < y.1 →
        ‖iteratedFDeriv ℝ i (Axi.ringStreamProfile R Φ) y‖ ≤
          C * (1 + |y.1| + |y.2.2|) * ∑ l ∈ Finset.range (i + 2), ‖iteratedFDeriv ℝ l Φ y‖ := by
  obtain ⟨C₀, hC₀, h0⟩ := ringProfileJet_unif i
  refine ⟨2 * C₀, by positivity, fun R Φ hR1 hΦ => ?_⟩
  obtain ⟨hsm0, hsm1, -⟩ := IIb.ringProfileJet R Φ hΦ
  have hfun : Axi.ringStreamProfile R Φ =
      fun z => Axi.ringStreamProfile R Φ z 0 • Axi.m0 + Axi.ringStreamProfile R Φ z 1 • Axi.m1 :=
    funext fun _ => merid_eq_comb _
  refine ⟨by rw [hfun]; exact contDiffOn_comb hsm0 hsm1, fun y hy => ?_⟩
  obtain ⟨hA, hB⟩ := h0 R Φ hR1 hΦ y hy
  have hcomb := norm_iteratedFDeriv_comb_le hy hsm0 hsm1 i
  have hS : 0 ≤ ∑ l ∈ Finset.range (i + 2), ‖iteratedFDeriv ℝ l Φ y‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hW : 1 ≤ 1 + |y.1| + |y.2.2| := by
    have := abs_nonneg y.1
    have := abs_nonneg y.2.2
    linarith
  have hCW : C₀ ≤ C₀ * (1 + |y.1| + |y.2.2|) := le_mul_of_one_le_right hC₀ hW
  have h1' : C₀ * ∑ l ∈ Finset.range (i + 2), ‖iteratedFDeriv ℝ l Φ y‖ ≤
      C₀ * (1 + |y.1| + |y.2.2|) * ∑ l ∈ Finset.range (i + 2), ‖iteratedFDeriv ℝ l Φ y‖ :=
    mul_le_mul_of_nonneg_right hCW hS
  rw [hfun]
  calc ‖iteratedFDeriv ℝ i (fun z =>
          Axi.ringStreamProfile R Φ z 0 • Axi.m0 + Axi.ringStreamProfile R Φ z 1 • Axi.m1) y‖
      ≤ ‖iteratedFDeriv ℝ i (fun z => Axi.ringStreamProfile R Φ z 0) y‖ +
          ‖iteratedFDeriv ℝ i (fun z => Axi.ringStreamProfile R Φ z 1) y‖ := hcomb
    _ ≤ C₀ * (1 + |y.1| + |y.2.2|) * ∑ l ∈ Finset.range (i + 2), ‖iteratedFDeriv ℝ l Φ y‖ +
          C₀ * (1 + |y.1| + |y.2.2|) * ∑ l ∈ Finset.range (i + 2), ‖iteratedFDeriv ℝ l Φ y‖ :=
        add_le_add (hA.trans h1') hB
    _ = 2 * C₀ * (1 + |y.1| + |y.2.2|) *
          ∑ l ∈ Finset.range (i + 2), ‖iteratedFDeriv ℝ l Φ y‖ := by ring

/-- `R`-uniform Cartesian jet bound for `Axi.Nv R (Axi.ringStreamProfile R Φ) τ` off the axis. -/
theorem nv_jet_le_unif (k : ℕ) :
    ∃ (C : ℝ) (K : ℕ), 0 ≤ C ∧
      ∀ (R : ℝ) (Φ : ℝ × (ℝ × ℝ) → ℝ), 1 ≤ R → ContDiffOn ℝ ∞ Φ (Ioi 0 ×ˢ univ) →
        ∀ (τ : ℝ) (y : Space), y ∉ Axi.axis →
          ‖iteratedFDeriv ℝ k (Axi.Nv R (Axi.ringStreamProfile R Φ) τ) y‖ ≤
            C * (1 + Axi.age R y) ^ (K + 1) * ((1 + |Axi.trans R y|) ^ (k + 1) *
              ∑ i ∈ Finset.range (k + 2), ‖iteratedFDeriv ℝ i Φ (Axi.chart R τ y)‖) := by
  obtain ⟨CJ, K, hCJ, HJ⟩ := ringLiftPtJet k
  choose CP hCP0 hCP using fun l => ringProfileMeridJet_unif l
  have hCP_sum : 0 ≤ ∑ l ∈ Finset.range (k + 1), CP l :=
    Finset.sum_nonneg fun l _ => hCP0 l
  refine ⟨CJ * ∑ l ∈ Finset.range (k + 1), CP l, K, mul_nonneg hCJ.le hCP_sum,
    fun R Φ hR hΦ τ y hy => ?_⟩
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hs : 0 < Axi.age R y := age_pos_of hR0 hy
  have hBs : ContDiffOn ℝ ∞ (Axi.ringStreamProfile R Φ) (Ioi 0 ×ˢ univ) := (hCP 0 R Φ hR hΦ).1
  have h1 := (HJ R τ _ hR hBs).2 y hy
  have hfac : 1 + |(Axi.chart R τ y).1| + |(Axi.chart R τ y).2.2| ≤
      (1 + Axi.age R y) * (1 + |Axi.trans R y|) := by
    show 1 + |Axi.age R y| + |Axi.trans R y| ≤ (1 + Axi.age R y) * (1 + |Axi.trans R y|)
    rw [abs_of_pos hs]
    nlinarith [abs_nonneg (Axi.trans R y)]
  have h1s : 0 ≤ 1 + Axi.age R y := by linarith
  have hl : ∀ l ∈ Finset.range (k + 1),
      ‖iteratedFDeriv ℝ l (Axi.ringStreamProfile R Φ) (Axi.chart R τ y)‖ ≤
        CP l * ((1 + Axi.age R y) * (1 + |Axi.trans R y|)) *
          ∑ i ∈ Finset.range (k + 2), ‖iteratedFDeriv ℝ i Φ (Axi.chart R τ y)‖ := by
    intro l hl
    have hl' : l + 2 ≤ k + 2 := by have := Finset.mem_range.1 hl; omega
    have h2 := (hCP l R Φ hR hΦ).2 (Axi.chart R τ y) hs
    have hsub : ∑ i ∈ Finset.range (l + 2), ‖iteratedFDeriv ℝ i Φ (Axi.chart R τ y)‖ ≤
        ∑ i ∈ Finset.range (k + 2), ‖iteratedFDeriv ℝ i Φ (Axi.chart R τ y)‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hl')
        (fun _ _ _ => norm_nonneg _)
    have hsum0 : 0 ≤ ∑ i ∈ Finset.range (l + 2), ‖iteratedFDeriv ℝ i Φ (Axi.chart R τ y)‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    refine h2.trans (mul_le_mul ?_ hsub hsum0 (mul_nonneg (hCP0 l) (mul_nonneg h1s (by positivity))))
    exact mul_le_mul_of_nonneg_left hfac (hCP0 l)
  have hsumB : ∑ l ∈ Finset.range (k + 1),
      ‖iteratedFDeriv ℝ l (Axi.ringStreamProfile R Φ) (Axi.chart R τ y)‖ ≤
        (∑ l ∈ Finset.range (k + 1), CP l) * ((1 + Axi.age R y) * (1 + |Axi.trans R y|)) *
          ∑ i ∈ Finset.range (k + 2), ‖iteratedFDeriv ℝ i Φ (Axi.chart R τ y)‖ := by
    rw [Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_le_sum hl
  have hpos1 : 0 ≤ CJ * (1 + Axi.age R y) ^ K * (1 + |Axi.trans R y|) ^ k :=
    mul_nonneg (mul_nonneg hCJ.le (pow_nonneg h1s _)) (pow_nonneg (by positivity) _)
  calc ‖iteratedFDeriv ℝ k (Axi.Nv R (Axi.ringStreamProfile R Φ) τ) y‖
      ≤ CJ * (1 + Axi.age R y) ^ K * (1 + |Axi.trans R y|) ^ k *
          ∑ l ∈ Finset.range (k + 1),
            ‖iteratedFDeriv ℝ l (Axi.ringStreamProfile R Φ) (Axi.chart R τ y)‖ := h1
    _ ≤ CJ * (1 + Axi.age R y) ^ K * (1 + |Axi.trans R y|) ^ k *
          ((∑ l ∈ Finset.range (k + 1), CP l) * ((1 + Axi.age R y) * (1 + |Axi.trans R y|)) *
            ∑ i ∈ Finset.range (k + 2), ‖iteratedFDeriv ℝ i Φ (Axi.chart R τ y)‖) :=
        mul_le_mul_of_nonneg_left hsumB hpos1
    _ = CJ * (∑ l ∈ Finset.range (k + 1), CP l) * (1 + Axi.age R y) ^ (K + 1) *
          ((1 + |Axi.trans R y|) ^ (k + 1) *
            ∑ i ∈ Finset.range (k + 2), ‖iteratedFDeriv ℝ i Φ (Axi.chart R τ y)‖) := by
        ring

/-! ### 2. `R`-uniform and `(ν, c)`-polynomial heat-field and heat-sum jet bounds -/

/-- For `0 < ν ≤ 1` and `0 < c`, `|B0191.profileDeriv ν n z| ≤ C * (1 + c + ν⁻¹) ^ (n + 1)`
uniformly in `z : ℝ`. -/
theorem profileDeriv_le_poly (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν c : ℝ), 0 < ν → ν ≤ 1 → 0 < c → ∀ z : ℝ,
      ‖iteratedFDeriv ℝ 0 (UnforcedLeray.B0191.profileDeriv ν n) z‖ ≤
        C * (1 + c + ν⁻¹) ^ (n + 1) := by
  obtain ⟨C, hC0, hC⟩ := lhBound1D 0 n
  refine ⟨C, hC0, fun ν c hν hν1 hc z => ?_⟩
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
  have h1 := hC ν hν hν1 1 le_rfl z
  simp only [pow_zero, one_mul, mul_one] at h1
  have heq : UnforcedLeray.B0191.profileDeriv ν n z = iteratedDeriv n (heatKernel1 (ν * 1)) z :=
    lhHeatKernelEq ν n z 1
  rw [heq, mul_one]
  have hν_inv : 1 ≤ ν⁻¹ := one_le_inv₀ hν |>.2 hν1
  have hrpow : ν ^ (-(((n : ℝ) + 1) / 2)) ≤ (1 + c + ν⁻¹) ^ (n + 1) := by
    have h_eq : ν ^ (-(((n : ℝ) + 1) / 2)) = (ν⁻¹) ^ (((n : ℝ) + 1) / 2) := by
      rw [Real.inv_rpow hν.le, Real.rpow_neg hν.le]
    rw [h_eq]
    have h_exp : ((n : ℝ) + 1) / 2 ≤ ((n + 1 : ℕ) : ℝ) := by
      push_cast; linarith
    calc (ν⁻¹) ^ (((n : ℝ) + 1) / 2)
        ≤ (ν⁻¹) ^ ((n + 1 : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hν_inv h_exp
      _ = (ν⁻¹) ^ (n + 1) := Real.rpow_natCast _ _
      _ ≤ (1 + c + ν⁻¹) ^ (n + 1) :=
          pow_le_pow_left₀ (by positivity) (by linarith) (n + 1)
  exact h1.trans (mul_le_mul_of_nonneg_left hrpow hC0)

/-- The `k`-th derivative of `z ↦ B0191.profileDeriv ν m z` is bounded by
`C * (1 + c + ν⁻¹) ^ (m + k + 1)` for `0 < ν ≤ 1`, `0 < c`. -/
theorem iter_profileDeriv_le_poly (m k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν c : ℝ), 0 < ν → ν ≤ 1 → 0 < c → ∀ z : ℝ,
      ‖iteratedFDeriv ℝ k (UnforcedLeray.B0191.profileDeriv ν m) z‖ ≤
        C * (1 + c + ν⁻¹) ^ (m + k + 1) := by
  obtain ⟨C, hC0, hC⟩ := profileDeriv_le_poly (m + k)
  refine ⟨C, hC0, fun ν c hν hν1 hc z => ?_⟩
  have h0 := hC ν c hν hν1 hc z
  rw [norm_iteratedFDeriv_zero] at h0
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hfjProfileDerivEq ν k m]
  exact h0

/-- If `f : Space → ℝ` satisfies `HeatJetBdd 1 f` and `ContDiff ℝ ∞ f`, then
`y ↦ f (R⁻¹ • y)` has `k`-th derivative bounded by the same constant on `Axi.ϱ y ^ 2 ≤ R ^ 2`
for all `1 ≤ R`. -/
theorem scale_heatJetBdd_one {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (Hf : HeatJetBdd 1 f) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R → ∀ y : Space, Axi.ϱ y ^ 2 ≤ R ^ 2 →
      ‖iteratedFDeriv ℝ k (fun z : Space => f (R⁻¹ • z)) y‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := Hf k
  refine ⟨C, hC0, fun R hR y hy => ?_⟩
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  set L : Space →L[ℝ] Space := R⁻¹ • ContinuousLinearMap.id ℝ Space
  have hL_norm : ‖L‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR0)]
    calc R⁻¹ * ‖ContinuousLinearMap.id ℝ Space‖
        ≤ 1 * 1 := mul_le_mul (inv_le_one_of_one_le₀ hR)
          (ContinuousLinearMap.norm_id_le) (norm_nonneg _) zero_le_one
      _ = 1 := mul_one 1
  have hfun : (fun z : Space => f (R⁻¹ • z)) = f ∘ L := rfl
  have hy1 : Axi.ϱ (L y) ^ 2 ≤ 1 := by
    change Axi.ϱ (R⁻¹ • y) ^ 2 ≤ 1
    rw [Axi.ϱ_smul, abs_of_pos (inv_pos.2 hR0), mul_pow, inv_pow]
    exact inv_mul_le_iff₀ (pow_pos hR0 2) |>.2 (by linarith)
  rw [hfun, L.iteratedFDeriv_comp_right hf y (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hpow : ‖L‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg _) hL_norm
  calc ‖iteratedFDeriv ℝ k f (L y)‖ * ‖L‖ ^ k
      ≤ C * 1 := mul_le_mul (hC (L y) hy1) hpow (by positivity) hC0
    _ = C := mul_one C

/-- `R`-uniform and `(ν, c)`-polynomial Cartesian jet bound for `heatField ν R j` on
`Axi.ϱ y ^ 2 ≤ R ^ 2` for `1 ≤ R`, `0 < ν ≤ 1`, `0 < c`. -/
theorem heatField_jet_le_unif (j k : ℕ) :
    ∃ (C : ℝ) (d : ℕ), 0 ≤ C ∧
      ∀ (ν c R : ℝ), 0 < ν → ν ≤ 1 → 0 < c → 1 ≤ R →
        ∀ y : Space, Axi.ϱ y ^ 2 ≤ R ^ 2 →
          ‖iteratedFDeriv ℝ k (heatField ν R j) y‖ ≤ polyConst C d ν c := by
  have c0 : ContDiff ℝ ∞ (fun y : Space => y 0) := by fun_prop
  have c1 : ContDiff ℝ ∞ (fun y : Space => y 1) := by fun_prop
  have cw : ContDiff ℝ ∞ (fun y : Space => y 0 ^ 2 + y 1 ^ 2) := by fun_prop
  have cwj : ContDiff ℝ ∞ (fun y : Space => (y 0 ^ 2 + y 1 ^ 2) ^ j) := cw.pow j
  have h0 : HeatJetBdd 1 (fun y : Space => y 0) :=
    hfjCoord (W := 1) 0 (fun y => le_add_of_nonneg_right (sq_nonneg _))
  have h1 : HeatJetBdd 1 (fun y : Space => y 1) :=
    hfjCoord (W := 1) 1 (fun y => le_add_of_nonneg_left (sq_nonneg _))
  have hw : HeatJetBdd 1 (fun y : Space => y 0 ^ 2 + y 1 ^ 2) :=
    hfjAdd (c0.pow 2) (c1.pow 2) (hfjPow c0 h0 2) (hfjPow c1 h1 2)
  have hP : HeatJetBdd 1 (fun y : Space => (y 0 ^ 2 + y 1 ^ 2) ^ j) := hfjPow cw hw j
  set pA0 : Space → ℝ := fun z => -((z 0 ^ 2 + z 1 ^ 2) ^ j * z 0)
  set pA1 : Space → ℝ := fun z => -((z 0 ^ 2 + z 1 ^ 2) ^ j * z 1)
  set pB : Space → ℝ := fun z => (2 * (j : ℝ) + 2) * (z 0 ^ 2 + z 1 ^ 2) ^ j
  have cpA0 : ContDiff ℝ ∞ pA0 := (cwj.mul c0).neg
  have cpA1 : ContDiff ℝ ∞ pA1 := (cwj.mul c1).neg
  have cpB : ContDiff ℝ ∞ pB := contDiff_const.mul cwj
  have hpA0 : HeatJetBdd 1 pA0 := by
    have heq : pA0 = fun z => (-1 : ℝ) * ((z 0 ^ 2 + z 1 ^ 2) ^ j * z 0) := by
      funext z; dsimp [pA0]; ring
    rw [heq]
    exact hfjMul contDiff_const (cwj.mul c0) (hfjConst (-1)) (hfjMul cwj c0 hP h0)
  have hpA1 : HeatJetBdd 1 pA1 := by
    have heq : pA1 = fun z => (-1 : ℝ) * ((z 0 ^ 2 + z 1 ^ 2) ^ j * z 1) := by
      funext z; dsimp [pA1]; ring
    rw [heq]
    exact hfjMul contDiff_const (cwj.mul c1) (hfjConst (-1)) (hfjMul cwj c1 hP h1)
  have hpB : HeatJetBdd 1 pB :=
    hfjMul contDiff_const cwj (hfjConst (2 * (j : ℝ) + 2)) hP
  choose CA0 hCA0_0 hCA0 using fun i => scale_heatJetBdd_one cpA0 hpA0 i
  choose CA1 hCA1_0 hCA1 using fun i => scale_heatJetBdd_one cpA1 hpA1 i
  choose CB hCB_0 hCB using fun i => scale_heatJetBdd_one cpB hpB i
  choose CG1 hCG1_0 hCG1 using fun i => iter_profileDeriv_le_poly (2 * j + 1) i
  choose CG0 hCG0_0 hCG0 using fun i => iter_profileDeriv_le_poly (2 * j) i
  set P2 : Space →L[ℝ] ℝ := EuclideanSpace.proj 2
  have hP2_norm : ‖P2‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
    rw [one_mul]
    exact PiLp.norm_apply_le y 2
  set d : ℕ := 2 * j + 1 + k + 1
  set K0 : ℝ := ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * CA0 i * CG1 (k - i)
  set K1 : ℝ := ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * CA1 i * CG1 (k - i)
  set K2 : ℝ := ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * CB i * CG0 (k - i)
  have hK0_nn : 0 ≤ K0 := Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCA0_0 i)) (hCG1_0 _)
  have hK1_nn : 0 ≤ K1 := Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCA1_0 i)) (hCG1_0 _)
  have hK2_nn : 0 ≤ K2 := Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCB_0 i)) (hCG0_0 _)
  set L0 : ℝ →L[ℝ] Space := (ContinuousLinearMap.id ℝ ℝ).smulRight (coordinateVector 0)
  set L1 : ℝ →L[ℝ] Space := (ContinuousLinearMap.id ℝ ℝ).smulRight (coordinateVector 1)
  set L2 : ℝ →L[ℝ] Space := (ContinuousLinearMap.id ℝ ℝ).smulRight Axi.e3
  refine ⟨‖L0‖ * K0 + (‖L1‖ * K1 + ‖L2‖ * K2), d, by positivity,
    fun ν c R hν hν1 hc hR y hy => ?_⟩
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hRinv : |R⁻¹| ≤ 1 := by
    rw [abs_of_pos (inv_pos.2 hR0)]
    exact inv_le_one_of_one_le₀ hR
  have hX1 : 1 ≤ 1 + c + ν⁻¹ := by
    have : 0 < ν⁻¹ := inv_pos.2 hν
    linarith
  -- Bounds on the Gaussian factor composed with `P2`
  have hG_comp : ∀ (m i : ℕ) (CG : ℕ → ℝ),
      (∀ i', ∀ z : ℝ, ‖iteratedFDeriv ℝ i' (UnforcedLeray.B0191.profileDeriv ν m) z‖ ≤
        CG i' * (1 + c + ν⁻¹) ^ (m + i' + 1)) →
      (∀ i', 0 ≤ CG i') →
      i ≤ k → m ≤ 2 * j + 1 →
      ‖iteratedFDeriv ℝ i (fun z : Space => UnforcedLeray.B0191.profileDeriv ν m (z 2)) y‖ ≤
        CG i * (1 + c + ν⁻¹) ^ d := by
    intro m i CG hCG_bd hCG_nn hik hm
    have hg_sm : ContDiff ℝ ∞ (UnforcedLeray.B0191.profileDeriv ν m) :=
      IIb.contDiff_profileDeriv ν m
    have hfun_g : (fun z : Space => UnforcedLeray.B0191.profileDeriv ν m (z 2)) =
        UnforcedLeray.B0191.profileDeriv ν m ∘ P2 := rfl
    rw [hfun_g, P2.iteratedFDeriv_comp_right hg_sm y (by exact_mod_cast le_top)]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hpow1 : ‖P2‖ ^ i ≤ 1 := pow_le_one₀ (norm_nonneg _) hP2_norm
    have hpow2 : (1 + c + ν⁻¹) ^ (m + i + 1) ≤ (1 + c + ν⁻¹) ^ d :=
      pow_le_pow_right₀ hX1 (by dsimp [d]; omega)
    calc ‖iteratedFDeriv ℝ i (UnforcedLeray.B0191.profileDeriv ν m) (P2 y)‖ * ‖P2‖ ^ i
        ≤ (CG i * (1 + c + ν⁻¹) ^ (m + i + 1)) * 1 :=
          mul_le_mul (hCG_bd i (P2 y)) hpow1 (by positivity)
            (mul_nonneg (hCG_nn i) (by positivity))
      _ ≤ CG i * (1 + c + ν⁻¹) ^ d := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_left hpow2 (hCG_nn i)
  -- Identities relating `hfjA * y i` and `hfjB` to `pA0`, `pA1`, `pB`
  have heqA0 : (fun z : Space => hfjA ν R j z * z 0) =
      fun z : Space => pA0 (R⁻¹ • z) * UnforcedLeray.B0191.profileDeriv ν (2 * j + 1) (z 2) := by
    funext z
    dsimp [hfjA, pA0]
    simp only [mul_pow, ← mul_add, ← inv_pow]
    ring
  have heqA1 : (fun z : Space => hfjA ν R j z * z 1) =
      fun z : Space => pA1 (R⁻¹ • z) * UnforcedLeray.B0191.profileDeriv ν (2 * j + 1) (z 2) := by
    funext z
    dsimp [hfjA, pA1]
    simp only [mul_pow, ← mul_add, ← inv_pow]
    ring
  have heqB : hfjB ν R j =
      fun z : Space => R⁻¹ * (pB (R⁻¹ • z) * UnforcedLeray.B0191.profileDeriv ν (2 * j) (z 2)) := by
    funext z
    dsimp [hfjB, pB]
    simp only [mul_pow, ← mul_add, ← inv_pow]
    ring
  have c_scale : ContDiff ℝ ∞ (fun z : Space => R⁻¹ • z) := contDiff_const_smul R⁻¹
  have c_pA0_R : ContDiff ℝ ∞ (fun z : Space => pA0 (R⁻¹ • z)) := cpA0.comp c_scale
  have c_pA1_R : ContDiff ℝ ∞ (fun z : Space => pA1 (R⁻¹ • z)) := cpA1.comp c_scale
  have c_pB_R : ContDiff ℝ ∞ (fun z : Space => pB (R⁻¹ • z)) := cpB.comp c_scale
  have c_g1 : ContDiff ℝ ∞ (fun z : Space => UnforcedLeray.B0191.profileDeriv ν (2 * j + 1) (z 2)) :=
    (IIb.contDiff_profileDeriv ν (2 * j + 1)).comp (by fun_prop)
  have c_g0 : ContDiff ℝ ∞ (fun z : Space => UnforcedLeray.B0191.profileDeriv ν (2 * j) (z 2)) :=
    (IIb.contDiff_profileDeriv ν (2 * j)).comp (by fun_prop)
  have hbd_A0 : ‖iteratedFDeriv ℝ k (fun z : Space => hfjA ν R j z * z 0) y‖ ≤
      K0 * (1 + c + ν⁻¹) ^ d := by
    rw [heqA0]
    refine (norm_iteratedFDeriv_mul_le c_pA0_R c_g1 y (by exact_mod_cast le_top)).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    have hik : k - i ≤ k := Nat.sub_le k i
    have h1 := hCA0 i R hR y hy
    have h2 := hG_comp (2 * j + 1) (k - i) CG1 (fun i' => hCG1 i' ν c hν hν1 hc) hCG1_0 hik le_rfl
    calc (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun z => pA0 (R⁻¹ • z)) y‖ *
            ‖iteratedFDeriv ℝ (k - i) (fun z => UnforcedLeray.B0191.profileDeriv ν (2 * j + 1) (z 2)) y‖
        ≤ (k.choose i : ℝ) * CA0 i * (CG1 (k - i) * (1 + c + ν⁻¹) ^ d) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2
            (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hCA0_0 i))
      _ = (k.choose i : ℝ) * CA0 i * CG1 (k - i) * (1 + c + ν⁻¹) ^ d := by ring
  have hbd_A1 : ‖iteratedFDeriv ℝ k (fun z : Space => hfjA ν R j z * z 1) y‖ ≤
      K1 * (1 + c + ν⁻¹) ^ d := by
    rw [heqA1]
    refine (norm_iteratedFDeriv_mul_le c_pA1_R c_g1 y (by exact_mod_cast le_top)).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    have hik : k - i ≤ k := Nat.sub_le k i
    have h1 := hCA1 i R hR y hy
    have h2 := hG_comp (2 * j + 1) (k - i) CG1 (fun i' => hCG1 i' ν c hν hν1 hc) hCG1_0 hik le_rfl
    calc (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun z => pA1 (R⁻¹ • z)) y‖ *
            ‖iteratedFDeriv ℝ (k - i) (fun z => UnforcedLeray.B0191.profileDeriv ν (2 * j + 1) (z 2)) y‖
        ≤ (k.choose i : ℝ) * CA1 i * (CG1 (k - i) * (1 + c + ν⁻¹) ^ d) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2
            (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hCA1_0 i))
      _ = (k.choose i : ℝ) * CA1 i * CG1 (k - i) * (1 + c + ν⁻¹) ^ d := by ring
  have hbd_B : ‖iteratedFDeriv ℝ k (hfjB ν R j) y‖ ≤ K2 * (1 + c + ν⁻¹) ^ d := by
    rw [heqB]
    have hsm_prod : ContDiffAt ℝ k
        (fun z : Space => pB (R⁻¹ • z) * UnforcedLeray.B0191.profileDeriv ν (2 * j) (z 2)) y :=
      ((c_pB_R.mul c_g0).contDiffAt).of_le (by exact_mod_cast le_top)
    have hconst : (fun z : Space => R⁻¹ * (pB (R⁻¹ • z) * UnforcedLeray.B0191.profileDeriv ν (2 * j) (z 2))) =
        R⁻¹ • fun z : Space => pB (R⁻¹ • z) * UnforcedLeray.B0191.profileDeriv ν (2 * j) (z 2) := rfl
    rw [hconst, iteratedFDeriv_const_smul_apply hsm_prod, norm_smul, Real.norm_eq_abs]
    have hprod : ‖iteratedFDeriv ℝ k
        (fun z : Space => pB (R⁻¹ • z) * UnforcedLeray.B0191.profileDeriv ν (2 * j) (z 2)) y‖ ≤
        K2 * (1 + c + ν⁻¹) ^ d := by
      refine (norm_iteratedFDeriv_mul_le c_pB_R c_g0 y (by exact_mod_cast le_top)).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i hi => ?_
      have hik : k - i ≤ k := Nat.sub_le k i
      have h1 := hCB i R hR y hy
      have h2 := hG_comp (2 * j) (k - i) CG0 (fun i' => hCG0 i' ν c hν hν1 hc) hCG0_0 hik (by omega)
      calc (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun z => pB (R⁻¹ • z)) y‖ *
              ‖iteratedFDeriv ℝ (k - i) (fun z => UnforcedLeray.B0191.profileDeriv ν (2 * j) (z 2)) y‖
          ≤ (k.choose i : ℝ) * CB i * (CG0 (k - i) * (1 + c + ν⁻¹) ^ d) :=
            mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2
              (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hCB_0 i))
        _ = (k.choose i : ℝ) * CB i * CG0 (k - i) * (1 + c + ν⁻¹) ^ d := by ring
    calc |R⁻¹| * ‖iteratedFDeriv ℝ k
            (fun z : Space => pB (R⁻¹ • z) * UnforcedLeray.B0191.profileDeriv ν (2 * j) (z 2)) y‖
        ≤ 1 * (K2 * (1 + c + ν⁻¹) ^ d) := mul_le_mul hRinv hprod (norm_nonneg _) zero_le_one
      _ = K2 * (1 + c + ν⁻¹) ^ d := one_mul _
  -- Combine the three vector terms via `hfjField`
  have cA0 : ContDiff ℝ ∞ (fun z : Space => hfjA ν R j z * z 0) := by
    rw [heqA0]; exact c_pA0_R.mul c_g1
  have cA1 : ContDiff ℝ ∞ (fun z : Space => hfjA ν R j z * z 1) := by
    rw [heqA1]; exact c_pA1_R.mul c_g1
  have cB : ContDiff ℝ ∞ (hfjB ν R j) := by
    rw [heqB]; exact contDiff_const.mul (c_pB_R.mul c_g0)
  have hT0 : ‖iteratedFDeriv ℝ k (fun z : Space => (hfjA ν R j z * z 0) • coordinateVector 0) y‖ ≤
      ‖L0‖ * (K0 * (1 + c + ν⁻¹) ^ d) := by
    have hfun : (fun z : Space => (hfjA ν R j z * z 0) • coordinateVector 0) =
        L0 ∘ (fun z : Space => hfjA ν R j z * z 0) := rfl
    rw [hfun]
    exact (L0.norm_iteratedFDeriv_comp_left cA0.contDiffAt (by exact_mod_cast le_top)).trans
      (mul_le_mul_of_nonneg_left hbd_A0 (norm_nonneg _))
  have hT1 : ‖iteratedFDeriv ℝ k (fun z : Space => (hfjA ν R j z * z 1) • coordinateVector 1) y‖ ≤
      ‖L1‖ * (K1 * (1 + c + ν⁻¹) ^ d) := by
    have hfun : (fun z : Space => (hfjA ν R j z * z 1) • coordinateVector 1) =
        L1 ∘ (fun z : Space => hfjA ν R j z * z 1) := rfl
    rw [hfun]
    exact (L1.norm_iteratedFDeriv_comp_left cA1.contDiffAt (by exact_mod_cast le_top)).trans
      (mul_le_mul_of_nonneg_left hbd_A1 (norm_nonneg _))
  have hT2 : ‖iteratedFDeriv ℝ k (fun z : Space => hfjB ν R j z • Axi.e3) y‖ ≤
      ‖L2‖ * (K2 * (1 + c + ν⁻¹) ^ d) := by
    have hfun : (fun z : Space => hfjB ν R j z • Axi.e3) = L2 ∘ hfjB ν R j := rfl
    rw [hfun]
    exact (L2.norm_iteratedFDeriv_comp_left cB.contDiffAt (by exact_mod_cast le_top)).trans
      (mul_le_mul_of_nonneg_left hbd_B (norm_nonneg _))
  have cT0 : ContDiffAt ℝ k (fun z : Space => (hfjA ν R j z * z 0) • coordinateVector 0) y :=
    ((cA0.smul contDiff_const).contDiffAt).of_le (by exact_mod_cast le_top)
  have cT1 : ContDiffAt ℝ k (fun z : Space => (hfjA ν R j z * z 1) • coordinateVector 1) y :=
    ((cA1.smul contDiff_const).contDiffAt).of_le (by exact_mod_cast le_top)
  have cT2 : ContDiffAt ℝ k (fun z : Space => hfjB ν R j z • Axi.e3) y :=
    ((cB.smul contDiff_const).contDiffAt).of_le (by exact_mod_cast le_top)
  have hfun : heatField ν R j = fun z : Space =>
      (hfjA ν R j z * z 0) • coordinateVector 0 +
      ((hfjA ν R j z * z 1) • coordinateVector 1 + hfjB ν R j z • Axi.e3) :=
    funext (hfjField ν R j)
  have e1 : iteratedFDeriv ℝ k (heatField ν R j) y =
      iteratedFDeriv ℝ k (fun z : Space => (hfjA ν R j z * z 0) • coordinateVector 0) y +
      iteratedFDeriv ℝ k (fun z : Space =>
        (hfjA ν R j z * z 1) • coordinateVector 1 + hfjB ν R j z • Axi.e3) y := by
    rw [hfun]
    exact iteratedFDeriv_add_apply cT0 (cT1.add cT2)
  have e2 : iteratedFDeriv ℝ k (fun z : Space =>
        (hfjA ν R j z * z 1) • coordinateVector 1 + hfjB ν R j z • Axi.e3) y =
      iteratedFDeriv ℝ k (fun z : Space => (hfjA ν R j z * z 1) • coordinateVector 1) y +
      iteratedFDeriv ℝ k (fun z : Space => hfjB ν R j z • Axi.e3) y :=
    iteratedFDeriv_add_apply cT1 cT2
  rw [e1, e2]
  calc ‖iteratedFDeriv ℝ k (fun z : Space => (hfjA ν R j z * z 0) • coordinateVector 0) y +
          (iteratedFDeriv ℝ k (fun z : Space => (hfjA ν R j z * z 1) • coordinateVector 1) y +
            iteratedFDeriv ℝ k (fun z : Space => hfjB ν R j z • Axi.e3) y)‖
      ≤ ‖iteratedFDeriv ℝ k (fun z : Space => (hfjA ν R j z * z 0) • coordinateVector 0) y‖ +
          (‖iteratedFDeriv ℝ k (fun z : Space => (hfjA ν R j z * z 1) • coordinateVector 1) y‖ +
            ‖iteratedFDeriv ℝ k (fun z : Space => hfjB ν R j z • Axi.e3) y‖) :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ ≤ ‖L0‖ * (K0 * (1 + c + ν⁻¹) ^ d) +
          (‖L1‖ * (K1 * (1 + c + ν⁻¹) ^ d) + ‖L2‖ * (K2 * (1 + c + ν⁻¹) ^ d)) :=
        add_le_add hT0 (add_le_add hT1 hT2)
    _ = polyConst (‖L0‖ * K0 + (‖L1‖ * K1 + ‖L2‖ * K2)) d ν c := by
        unfold polyConst; ring

/-- `R`-uniform and `(ν, c)`-polynomial Cartesian jet bound for `heatSum ν R (meanCoeff tr) N` on
`Axi.ϱ y ^ 2 ≤ R ^ 2` for `1 ≤ R`. -/
theorem heatSum_jet_le_unif (hCoeff : LateMeanCoeff) {ρ : ℝ} (hρ : 1 / 2 < ρ) (N k : ℕ) :
    ∃ (ν₀ C : ℝ) (d : ℕ), 0 < ν₀ ∧ 0 ≤ C ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-ρ)), UnforcedLeray.Short.PartI.IsBUCTrain tr →
          ∀ R : ℝ, 1 ≤ R → ∀ y : Space, Axi.ϱ y ^ 2 ≤ R ^ 2 →
            ‖iteratedFDeriv ℝ k (heatSum ν R (meanCoeff tr) N) y‖ ≤
              polyConst C d ν (ν ^ (-ρ)) := by
  choose Ca da νa hνa hCa using fun j => hCoeff ρ j hρ
  choose Ch dh hCh0 hCh using fun j => heatField_jet_le_unif j k
  set S : Finset ℕ := Finset.range (N + 1)
  have hS_ne : S.Nonempty := ⟨0, Finset.mem_range.2 (Nat.succ_pos N)⟩
  set ν₀ : ℝ := min (S.inf' hS_ne νa) 1
  have hν₀ : 0 < ν₀ := lt_min ((Finset.lt_inf'_iff hS_ne).2 fun j _ => hνa j) one_pos
  set D : ℕ := ∑ j ∈ S, (da j + dh j)
  set C : ℝ := ∑ j ∈ S, max (Ca j) 0 * Ch j
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun j _ => mul_nonneg (le_max_right _ _) (hCh0 j)
  refine ⟨ν₀, C, D, hν₀, hC0, fun ν hν hν_le tr htr R hR y hy => ?_⟩
  have hν1 : ν ≤ 1 := hν_le.trans (min_le_right _ _)
  have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν (-ρ)
  have hX1 : 1 ≤ 1 + ν ^ (-ρ) + ν⁻¹ := by
    have : 0 < ν⁻¹ := inv_pos.2 hν
    linarith
  have hsm : ∀ j ∈ S, ContDiff ℝ k (fun z => meanCoeff tr j • heatField ν R j z) :=
    fun j _ => ((contDiff_heatField ν R j).const_smul (meanCoeff tr j)).of_le
      (m := (k : WithTop ℕ∞)) (by exact_mod_cast le_top)
  have e : iteratedFDeriv ℝ k (heatSum ν R (meanCoeff tr) N) y =
      ∑ j ∈ S, iteratedFDeriv ℝ k (fun z => meanCoeff tr j • heatField ν R j z) y := by
    have h := iteratedFDeriv_sum (𝕜 := ℝ) (i := k) hsm
    have h' := congrFun h y
    rw [Finset.sum_apply] at h'
    exact h'
  rw [e]
  refine (norm_sum_le _ _).trans ?_
  unfold polyConst
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj => ?_
  rw [iteratedFDeriv_const_smul_apply'
      (((contDiff_heatField ν R j).contDiffAt (x := y)).of_le (m := (k : WithTop ℕ∞))
        (by exact_mod_cast le_top)),
    norm_smul, Real.norm_eq_abs]
  have hν_j : ν ≤ νa j := (hν_le.trans (min_le_left _ _)).trans (Finset.inf'_le νa hj)
  have ha_j : |meanCoeff tr j| ≤ max (Ca j) 0 * (1 + ν ^ (-ρ) + ν⁻¹) ^ da j :=
    (hCa j ν hν hν_j tr htr).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hh_j : ‖iteratedFDeriv ℝ k (heatField ν R j) y‖ ≤
      Ch j * (1 + ν ^ (-ρ) + ν⁻¹) ^ dh j := hCh j ν (ν ^ (-ρ)) R hν hν1 hc hR y hy
  have hd_le : da j + dh j ≤ D :=
    Finset.single_le_sum (f := fun i => da i + dh i) (fun _ _ => Nat.zero_le _) hj
  have hpow : (1 + ν ^ (-ρ) + ν⁻¹) ^ (da j + dh j) ≤ (1 + ν ^ (-ρ) + ν⁻¹) ^ D :=
    pow_le_pow_right₀ hX1 hd_le
  calc |meanCoeff tr j| * ‖iteratedFDeriv ℝ k (heatField ν R j) y‖
      ≤ (max (Ca j) 0 * (1 + ν ^ (-ρ) + ν⁻¹) ^ da j) *
          (Ch j * (1 + ν ^ (-ρ) + ν⁻¹) ^ dh j) :=
        mul_le_mul ha_j hh_j (norm_nonneg _) (by positivity)
    _ = (max (Ca j) 0 * Ch j) * (1 + ν ^ (-ρ) + ν⁻¹) ^ (da j + dh j) := by
        rw [pow_add]; ring
    _ ≤ (max (Ca j) 0 * Ch j) * (1 + ν ^ (-ρ) + ν⁻¹) ^ D :=
        mul_le_mul_of_nonneg_left hpow (mul_nonneg (le_max_right _ _) (hCh0 j))

end UnforcedLeray.Short.PartIIa
