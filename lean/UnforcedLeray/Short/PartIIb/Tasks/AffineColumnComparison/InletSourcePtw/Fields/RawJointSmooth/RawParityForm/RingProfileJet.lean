import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_4_1_1_2_org
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Calculus.TangentCone.Basic

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

/-- The first coordinate `y ↦ y.1` as a continuous linear map. -/
def t1Proj : ℝ × (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)

/-- The third coordinate `y ↦ y.2.2` as a continuous linear map. -/
def t2Proj : ℝ × (ℝ × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

theorem norm_t1Proj_le : ‖t1Proj‖ ≤ 1 := ContinuousLinearMap.norm_fst_le ℝ ℝ (ℝ × ℝ)

theorem norm_t2Proj_le : ‖t2Proj‖ ≤ 1 := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have h1 : ‖ContinuousLinearMap.snd ℝ ℝ ℝ‖ ≤ 1 := ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ
  have h2 : ‖ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)‖ ≤ 1 := ContinuousLinearMap.norm_snd_le ℝ ℝ (ℝ × ℝ)
  exact mul_le_one₀ h1 (norm_nonneg _) h2

theorem isOpen_Uo : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
  isOpen_Ioi.prod isOpen_univ

theorem mem_Uo {y : ℝ × (ℝ × ℝ)} : y ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) ↔ 0 < y.1 := by
  simp [Set.mem_prod]

theorem contDiffAt_of_mem {f : ℝ × (ℝ × ℝ) → ℝ} {y : ℝ × (ℝ × ℝ)} {i : ℕ}
    (h : ContDiffOn ℝ ∞ f (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))))
    (hy : y ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)))) : ContDiffAt ℝ i f y :=
  ((h.contDiffAt (isOpen_Uo.mem_nhds hy))).of_le (by exact_mod_cast le_top)

theorem contDiffOn_fderiv_apply {Φ : ℝ × (ℝ × ℝ) → ℝ}
    (hΦ : ContDiffOn ℝ ∞ Φ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))))
    (v : ℝ × (ℝ × ℝ)) :
    ContDiffOn ℝ ∞ (fun y => fderiv ℝ Φ y v) (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := by
  have h : ContDiffOn ℝ ∞ (fun y => fderiv ℝ Φ y)
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    hΦ.fderiv_of_isOpen isOpen_Uo (by simp)
  exact h.clm_apply contDiffOn_const

theorem norm_iteratedFDeriv_fderiv_apply_le {Φ : ℝ × (ℝ × ℝ) → ℝ}
    (hΦ : ContDiffOn ℝ ∞ Φ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))))
    {y : ℝ × (ℝ × ℝ)} (hy : y ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)))) (v : ℝ × (ℝ × ℝ))
    (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun z => fderiv ℝ Φ z v) y‖ ≤
      ‖v‖ * ‖iteratedFDeriv ℝ (k + 1) Φ y‖ := by
  have hc : ContDiffAt ℝ ∞ (fderiv ℝ Φ) y := by
    have h : ContDiffOn ℝ ∞ (fun z => fderiv ℝ Φ z)
        (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
      hΦ.fderiv_of_isOpen isOpen_Uo (by simp)
    exact h.contDiffAt (isOpen_Uo.mem_nhds hy)
  have h := norm_iteratedFDeriv_clm_apply_const (f := fderiv ℝ Φ) (c := v) (x := y)
    (n := k) (N := ∞) hc (by exact_mod_cast le_top)
  rw [norm_iteratedFDeriv_fderiv] at h
  exact h

theorem norm_iteratedFDeriv_clm_le (L : ℝ × (ℝ × ℝ) →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (k : ℕ)
    (y : ℝ × (ℝ × ℝ)) :
    ‖iteratedFDeriv ℝ k (fun z => L z) y‖ ≤ 1 + ‖L y‖ := by
  rcases k with _ | _ | m
  · rw [norm_iteratedFDeriv_zero]
    linarith [norm_nonneg (L y)]
  · rw [norm_iteratedFDeriv_one]
    have h2 : fderiv ℝ (fun z => L z) y = L := L.fderiv
    rw [h2]
    linarith [norm_nonneg (L y)]
  · have h1 : ‖iteratedFDeriv ℝ (m + 1 + 1) (fun z => L z) y‖ =
        ‖iteratedFDeriv ℝ (m + 1) (fderiv ℝ (fun z => L z)) y‖ :=
      (norm_iteratedFDeriv_fderiv).symm
    have h2 : fderiv ℝ (fun z => L z) = fun _ => L := funext fun z => L.fderiv
    rw [h1, h2, iteratedFDeriv_succ_const]
    simp only [Pi.zero_apply, norm_zero]
    linarith [norm_nonneg (L y)]

theorem norm_iteratedFDeriv_mul_le_of {f F : ℝ × (ℝ × ℝ) → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))))
    (hF : ContDiffOn ℝ ∞ F (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))))
    {y : ℝ × (ℝ × ℝ)} (hy : y ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)))) (i : ℕ) {a B : ℝ}
    (ha : ∀ k, ‖iteratedFDeriv ℝ k f y‖ ≤ a) (hB : ∀ k ≤ i, ‖iteratedFDeriv ℝ k F y‖ ≤ B)
    (ha0 : 0 ≤ a) (hB0 : 0 ≤ B) :
    ‖iteratedFDeriv ℝ i (fun z => f z * F z) y‖ ≤ (((i : ℝ) + 1) * 2 ^ i) * a * B := by
  have hn : (i : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hu : UniqueDiffOn ℝ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Uo.uniqueDiffOn
  have hw : ∀ (k : ℕ) (g : ℝ × (ℝ × ℝ) → ℝ),
      iteratedFDerivWithin ℝ k g (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) y =
        iteratedFDeriv ℝ k g y :=
    fun k g => iteratedFDerivWithin_of_isOpen k isOpen_Uo hy
  have hL := norm_iteratedFDerivWithin_mul_le hf hF hu hy hn
  simp only [hw] at hL
  refine hL.trans ?_
  have hsum : ∑ k ∈ Finset.range (i + 1),
      (i.choose k : ℝ) * ‖iteratedFDeriv ℝ k f y‖ * ‖iteratedFDeriv ℝ (i - k) F y‖ ≤
      ∑ k ∈ Finset.range (i + 1), (2 : ℝ) ^ i * a * B := by
    apply Finset.sum_le_sum
    intro k hk
    have hk' : k ≤ i := by
      rw [Finset.mem_range] at hk
      omega
    have hch : (i.choose k : ℝ) ≤ 2 ^ i := by exact_mod_cast Nat.choose_le_two_pow i k
    have hA : (i.choose k : ℝ) * ‖iteratedFDeriv ℝ k f y‖ ≤ 2 ^ i * a :=
      mul_le_mul hch (ha k) (norm_nonneg _) (by positivity)
    exact mul_le_mul hA (hB (i - k) (by omega)) (norm_nonneg _) (by positivity)
  refine hsum.trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

theorem norm_iter_add_le' {f g : ℝ × (ℝ × ℝ) → ℝ} {y : ℝ × (ℝ × ℝ)} (i : ℕ)
    (hf : ContDiffAt ℝ i f y) (hg : ContDiffAt ℝ i g y) :
    ‖iteratedFDeriv ℝ i (fun z => f z + g z) y‖ ≤
      ‖iteratedFDeriv ℝ i f y‖ + ‖iteratedFDeriv ℝ i g y‖ := by
  have h : iteratedFDeriv ℝ i (fun z => f z + g z) y =
      iteratedFDeriv ℝ i f y + iteratedFDeriv ℝ i g y :=
    iteratedFDeriv_add_apply hf hg
  rw [h]
  exact norm_add_le _ _

theorem norm_iter_sub_le' {f g : ℝ × (ℝ × ℝ) → ℝ} {y : ℝ × (ℝ × ℝ)} (i : ℕ)
    (hf : ContDiffAt ℝ i f y) (hg : ContDiffAt ℝ i g y) :
    ‖iteratedFDeriv ℝ i (fun z => f z - g z) y‖ ≤
      ‖iteratedFDeriv ℝ i f y‖ + ‖iteratedFDeriv ℝ i g y‖ := by
  have h : iteratedFDeriv ℝ i (fun z => f z - g z) y =
      iteratedFDeriv ℝ i f y - iteratedFDeriv ℝ i g y :=
    iteratedFDeriv_sub_apply hf hg
  rw [h]
  exact (norm_sub_le _ _)

theorem norm_iter_const_mul_le' (c : ℝ) {f : ℝ × (ℝ × ℝ) → ℝ} {y : ℝ × (ℝ × ℝ)} (i : ℕ)
    (hf : ContDiffAt ℝ i f y) :
    ‖iteratedFDeriv ℝ i (fun z => c * f z) y‖ ≤ |c| * ‖iteratedFDeriv ℝ i f y‖ := by
  have hfun : (fun z => c * f z) = c • f := by
    funext z
    simp [smul_eq_mul]
  have h : iteratedFDeriv ℝ i (fun z => c * f z) y = c • iteratedFDeriv ℝ i f y := by
    rw [hfun]
    exact iteratedFDeriv_const_smul_apply hf
  rw [h, norm_smul, Real.norm_eq_abs]

theorem norm_iter_neg_le' {f : ℝ × (ℝ × ℝ) → ℝ} {y : ℝ × (ℝ × ℝ)} (i : ℕ)
    (hf : ContDiffAt ℝ i f y) :
    ‖iteratedFDeriv ℝ i (fun z => -f z) y‖ ≤ ‖iteratedFDeriv ℝ i f y‖ := by
  have h : iteratedFDeriv ℝ i (fun z => -f z) y = -iteratedFDeriv ℝ i f y :=
    iteratedFDeriv_neg_apply
  rw [h, norm_neg]

/-- **Jets of the ring stream profile** (SP 1897-2663, parity chart): the components of
`ringStreamProfile R Φ` are smooth on `s > 0` and obey the Leibniz bounds. -/
theorem ringProfileJet : UnforcedLeray.Short.IIb.RingProfileJet := by
  intro R Φ hΦ
  have e0 : ∀ z, UnforcedLeray.Axi.ringStreamProfile R Φ z 0 =
      -(fderiv ℝ Φ z (0, (0, 1))) := by
    intro z
    rw [UnforcedLeray.Short.IIb.ringStreamProfile_apply_zero]
    rfl
  have e1 : ∀ z, UnforcedLeray.Axi.ringStreamProfile R Φ z 1 =
      ((fderiv ℝ Φ z (0, (1, 0)) + R⁻¹ * Φ z) - (2 * R⁻¹) * (z.1 * fderiv ℝ Φ z (1, (0, 0))))
        - R⁻¹ * (z.2.2 * fderiv ℝ Φ z (0, (0, 1))) := by
    intro z
    rw [UnforcedLeray.Short.IIb.ringStreamProfile_apply_one]
    simp only [UnforcedLeray.Axi.dQ, UnforcedLeray.Axi.dS, UnforcedLeray.Axi.dEta]
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
    (contDiffOn_fderiv_apply hΦ _).add hcΦ
  have hB : ContDiffOn ℝ ∞ (fun z => (2 * R⁻¹) * (z.1 * fderiv ℝ Φ z (1, (0, 0))))
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    (contDiffOn_const (c := 2 * R⁻¹)).mul (hF1.mul (contDiffOn_fderiv_apply hΦ _))
  have hC : ContDiffOn ℝ ∞ (fun z => R⁻¹ * (z.2.2 * fderiv ℝ Φ z (0, (0, 1))))
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    (contDiffOn_const (c := R⁻¹)).mul (hF2.mul (contDiffOn_fderiv_apply hΦ _))
  have s0 : ContDiffOn ℝ ∞ (fun z => -(fderiv ℝ Φ z (0, (0, 1))))
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    (contDiffOn_fderiv_apply hΦ _).neg
  have s1 : ContDiffOn ℝ ∞ (fun z => ((fderiv ℝ Φ z (0, (1, 0)) + R⁻¹ * Φ z) -
      (2 * R⁻¹) * (z.1 * fderiv ℝ Φ z (1, (0, 0)))) - R⁻¹ * (z.2.2 * fderiv ℝ Φ z (0, (0, 1))))
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    (hA.sub hB).sub hC
  refine ⟨s0.congr (fun z _ => e0 z), s1.congr (fun z _ => e1 z), ?_⟩
  intro i
  refine ⟨1 + |R⁻¹| + 3 * |R⁻¹| * (((i : ℝ) + 1) * 2 ^ i), ?_⟩
  intro y hy
  have hyU : y ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := mem_Uo.2 hy
  have hM0 : 0 ≤ ∑ l ∈ Finset.range (i + 2), ‖iteratedFDeriv ℝ l Φ y‖ :=
    Finset.sum_nonneg (fun l _ => norm_nonneg _)
  have hMj : ∀ j, j ≤ i + 1 → ‖iteratedFDeriv ℝ j Φ y‖ ≤
      ∑ l ∈ Finset.range (i + 2), ‖iteratedFDeriv ℝ l Φ y‖ := by
    intro j hj
    exact Finset.single_le_sum (f := fun l => ‖iteratedFDeriv ℝ l Φ y‖)
      (fun l _ => norm_nonneg _) (Finset.mem_range.2 (by omega))
  set M := ∑ l ∈ Finset.range (i + 2), ‖iteratedFDeriv ℝ l Φ y‖ with hMdef
  have hD : ∀ v : ℝ × (ℝ × ℝ), ‖v‖ ≤ 1 → ∀ k ≤ i,
      ‖iteratedFDeriv ℝ k (fun z => fderiv ℝ Φ z v) y‖ ≤ M := by
    intro v hv k hk
    refine (norm_iteratedFDeriv_fderiv_apply_le hΦ hyU v k).trans ?_
    calc ‖v‖ * ‖iteratedFDeriv ℝ (k + 1) Φ y‖ ≤ 1 * M :=
          mul_le_mul hv (hMj (k + 1) (by omega)) (norm_nonneg _) zero_le_one
      _ = M := one_mul M
  have nE : ‖((0 : ℝ), ((0 : ℝ), (1 : ℝ)))‖ ≤ 1 := by simp [Prod.norm_def, max_le_iff]
  have nS : ‖((1 : ℝ), ((0 : ℝ), (0 : ℝ)))‖ ≤ 1 := by simp [Prod.norm_def, max_le_iff]
  have nQ : ‖((0 : ℝ), ((1 : ℝ), (0 : ℝ)))‖ ≤ 1 := by simp [Prod.norm_def, max_le_iff]
  have hc1 : ∀ k, ‖iteratedFDeriv ℝ k (fun z : ℝ × (ℝ × ℝ) => z.1) y‖ ≤ 1 + |y.1| := by
    intro k
    have h := norm_iteratedFDeriv_clm_le t1Proj norm_t1Proj_le k y
    simpa [t1Proj, Real.norm_eq_abs] using h
  have hc2 : ∀ k, ‖iteratedFDeriv ℝ k (fun z : ℝ × (ℝ × ℝ) => z.2.2) y‖ ≤ 1 + |y.2.2| := by
    intro k
    have h := norm_iteratedFDeriv_clm_le t2Proj norm_t2Proj_le k y
    simpa [t2Proj, Real.norm_eq_abs] using h
  have hG1 := norm_iteratedFDeriv_mul_le_of hF1 (contDiffOn_fderiv_apply hΦ (1, (0, 0))) hyU i
    hc1 (fun k hk => hD _ nS k hk) (by positivity) hM0
  have hG2 := norm_iteratedFDeriv_mul_le_of hF2 (contDiffOn_fderiv_apply hΦ (0, (0, 1))) hyU i
    hc2 (fun k hk => hD _ nE k hk) (by positivity) hM0
  have hΦi : ‖iteratedFDeriv ℝ i Φ y‖ ≤ M := hMj i (by omega)
  have hK : 0 ≤ ((i : ℝ) + 1) * 2 ^ i := by positivity
  have hκ : 0 ≤ |R⁻¹| := abs_nonneg _
  -- component 0
  have hE0 : ContDiffAt ℝ i (fun z => fderiv ℝ Φ z (0, (0, 1))) y :=
    contDiffAt_of_mem (contDiffOn_fderiv_apply hΦ _) hyU
  have bound0 : ‖iteratedFDeriv ℝ i (fun z => UnforcedLeray.Axi.ringStreamProfile R Φ z 0) y‖
      ≤ M := by
    have hfun : (fun z => UnforcedLeray.Axi.ringStreamProfile R Φ z 0) =
        fun z => -(fderiv ℝ Φ z (0, (0, 1))) := funext e0
    rw [hfun]
    refine (norm_iter_neg_le' i hE0).trans ?_
    exact hD _ nE i le_rfl
  -- component 1
  have hfun1 : (fun z => UnforcedLeray.Axi.ringStreamProfile R Φ z 1) =
      fun z => ((fderiv ℝ Φ z (0, (1, 0)) + R⁻¹ * Φ z) -
        (2 * R⁻¹) * (z.1 * fderiv ℝ Φ z (1, (0, 0)))) - R⁻¹ * (z.2.2 * fderiv ℝ Φ z (0, (0, 1))) :=
    funext e1
  have TA : ‖iteratedFDeriv ℝ i (fun z => (fderiv ℝ Φ z (0, (1, 0)) + R⁻¹ * Φ z) -
      (2 * R⁻¹) * (z.1 * fderiv ℝ Φ z (1, (0, 0)))) y‖ ≤
      (M + |R⁻¹| * M) + |2 * R⁻¹| * ((((i : ℝ) + 1) * 2 ^ i) * (1 + |y.1|) * M) := by
    refine (norm_iter_sub_le' i (contDiffAt_of_mem hA hyU) (contDiffAt_of_mem hB hyU)).trans ?_
    apply add_le_add
    · refine (norm_iter_add_le' i (contDiffAt_of_mem (contDiffOn_fderiv_apply hΦ _) hyU)
        (contDiffAt_of_mem hcΦ hyU)).trans ?_
      apply add_le_add (hD _ nQ i le_rfl)
      refine (norm_iter_const_mul_le' R⁻¹ i (contDiffAt_of_mem hΦ hyU)).trans ?_
      exact mul_le_mul_of_nonneg_left hΦi (abs_nonneg _)
    · refine (norm_iter_const_mul_le' (2 * R⁻¹) i
        (contDiffAt_of_mem (hF1.mul (contDiffOn_fderiv_apply hΦ (1, (0, 0)))) hyU)).trans ?_
      exact mul_le_mul_of_nonneg_left hG1 (abs_nonneg _)
  have TC : ‖iteratedFDeriv ℝ i (fun z => R⁻¹ * (z.2.2 * fderiv ℝ Φ z (0, (0, 1)))) y‖ ≤
      |R⁻¹| * ((((i : ℝ) + 1) * 2 ^ i) * (1 + |y.2.2|) * M) := by
    refine (norm_iter_const_mul_le' R⁻¹ i
      (contDiffAt_of_mem (hF2.mul (contDiffOn_fderiv_apply hΦ (0, (0, 1)))) hyU)).trans ?_
    exact mul_le_mul_of_nonneg_left hG2 (abs_nonneg _)
  have bound1 : ‖iteratedFDeriv ℝ i (fun z => UnforcedLeray.Axi.ringStreamProfile R Φ z 1) y‖
      ≤ (1 + |R⁻¹| + 3 * |R⁻¹| * (((i : ℝ) + 1) * 2 ^ i)) * (1 + |y.1| + |y.2.2|) * M := by
    rw [hfun1]
    refine (norm_iter_sub_le' i (contDiffAt_of_mem (hA.sub hB) hyU) (contDiffAt_of_mem hC hyU)).trans ?_
    have h2 : |2 * R⁻¹| = 2 * |R⁻¹| := by rw [abs_mul, abs_two]
    rw [h2] at TA
    have hid : (1 + |R⁻¹| + 3 * |R⁻¹| * (((i : ℝ) + 1) * 2 ^ i)) * (1 + |y.1| + |y.2.2|) * M -
        ((M + |R⁻¹| * M) + 2 * |R⁻¹| * ((((i : ℝ) + 1) * 2 ^ i) * (1 + |y.1|) * M) +
          |R⁻¹| * ((((i : ℝ) + 1) * 2 ^ i) * (1 + |y.2.2|) * M)) =
        (|y.1| + |y.2.2|) * M + |R⁻¹| * (|y.1| + |y.2.2|) * M +
          |R⁻¹| * (((i : ℝ) + 1) * 2 ^ i) * M * (|y.1| + 2 * |y.2.2|) := by ring
    have hnn : 0 ≤ (|y.1| + |y.2.2|) * M + |R⁻¹| * (|y.1| + |y.2.2|) * M +
          |R⁻¹| * (((i : ℝ) + 1) * 2 ^ i) * M * (|y.1| + 2 * |y.2.2|) :=
      add_nonneg (add_nonneg (mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) hM0)
        (mul_nonneg (mul_nonneg hκ (add_nonneg (abs_nonneg _) (abs_nonneg _))) hM0))
        (mul_nonneg (mul_nonneg (mul_nonneg hκ hK) hM0) (by positivity))
    have key : (M + |R⁻¹| * M) + 2 * |R⁻¹| * ((((i : ℝ) + 1) * 2 ^ i) * (1 + |y.1|) * M) +
        |R⁻¹| * ((((i : ℝ) + 1) * 2 ^ i) * (1 + |y.2.2|) * M) ≤
        (1 + |R⁻¹| + 3 * |R⁻¹| * (((i : ℝ) + 1) * 2 ^ i)) * (1 + |y.1| + |y.2.2|) * M := by
      linarith [hid, hnn]
    exact (add_le_add TA TC).trans key
  have hC1 : (1 : ℝ) ≤ 1 + |R⁻¹| + 3 * |R⁻¹| * (((i : ℝ) + 1) * 2 ^ i) := by
    have hCK : 0 ≤ 3 * |R⁻¹| * (((i : ℝ) + 1) * 2 ^ i) := by positivity
    linarith
  exact ⟨bound0.trans (le_mul_of_one_le_left hM0 hC1), bound1⟩

end UnforcedLeray.Short.IIb
