import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_1_1
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Part III-a, task `PartIII-a:T21/c5/1/1/2` decomposition (`Sub/PartIII-a_T21_c5_1_1_2.lean`, SP 2520-2525, 2891-2913)

Source of record: `the November 2 reference manuscript` (SP), lines 2520-2525 and
2891-2913 (`eq:short-causal-moving-eq`).

## Proved results in this file

1. **Cell-length lower bound on the extended horizon `Ico t (s + 1)` (`cellLen_ge_on_Ico_add_one`)**:
   Proves that for any threshold `D ≥ 0`, if `1 ≤ b ≤ clockTheta ν s`, `0 ≤ t ≤ s`, `0 < ν ≤ 1`,
   and `ν ≤ 1 / (2 * (D + 1) ^ 2)`, then `D ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r)` holds for every
   `r ∈ Ico t (s + 1)` (extending `cellLen_ge` from `Icc t s` to `Ico t (s + 1)` using
   `clockA ν r ≤ clockA ν s + 1 ≤ 2 * ν⁻¹`).
2. **Smoothness of `clockA`, `√(clockA)`, `cellLen`, and the `2 × 2` Gram inverse
   (`contDiff_clockA`, `contDiffOn_sqrt_clockA`, `contDiffOn_cellLen_clockA`,
   `contDiffOn_perGram_inv_of`, `contDiffOn_perGram_inv_clockA_of`)**:
   Uses `perGramNear_of`, `gram_inv_bound`, and Cramer's rule (`Matrix.adjugate_fin_two`) to prove
   that if the Gram entries `d ↦ perGram κ d a b` are `C^∞` on `Ici 1`, then `(perGram κ d)⁻¹ i j`
   is `C^∞` on `Ici (max D₁ 1)`, and its pullback along `p ↦ cellLen (ν ^ (-2 : ℝ)) (clockA ν p.1)`
   is `C^∞` on `Ico t (s + 1) ×ˢ univ`.
3. **Conditional assembly (`physFrameLamSmooth_of`)**:
   Combines `ComplCouplingHeat.physFrameLam_eq_sum_perGram_inv` and
   `ComplCouplingHeat.physFrameLam0_eq_perSum_physAdj` with `contDiffOn_perGram_inv_clockA_of` to
   deduce `PhysFrameLamSmooth κ` (composed by `PartIII-a:T21/c5/1/1/2`) from `PerGramSmooth κ`
   (`PartIII-a:T21/c5/1/1/2/1`) and `PhysFrameLam0Smooth κ` (`PartIII-a:T21/c5/1/1/2/2`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace CutFTCSmooth

open ComplCouplingHeat

/-! ## 1. Cell-length lower bound on `Ico t (s + 1)` -/

/-- Extending `cellLen_ge` from `Icc t s` to `Ico t (s + 1)`: if `1 ≤ b ≤ clockTheta ν s`,
`0 ≤ t ≤ s`, `0 < ν ≤ 1`, and `ν ≤ 1 / (2 * (D + 1) ^ 2)`, then for every `r ∈ Ico t (s + 1)` we
have `D ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r)`. -/
theorem cellLen_ge_on_Ico_add_one {D ν t s b : ℝ} (hD : 0 ≤ D) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hνD : ν ≤ 1 / (2 * (D + 1) ^ 2)) (hb : 1 ≤ b) (ht : 0 ≤ t) (hts : t ≤ s)
    (hθs : b ≤ clockTheta ν s) {r : ℝ} (hr : r ∈ Ico t (s + 1)) :
    D ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) := by
  have hr0 : 0 ≤ r := ht.trans hr.1
  have hs0 : 0 ≤ s := ht.trans hts
  have ha_r1 : 1 ≤ clockA ν r := one_le_clockA hν.le hr0
  have ha_r_pos : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one ha_r1
  have ha_s1 : 1 ≤ clockA ν s := one_le_clockA hν.le hs0
  have ha_s_pos : 0 < clockA ν s := lt_of_lt_of_le zero_lt_one ha_s1
  have hθ1 : 1 ≤ (ν * clockA ν s)⁻¹ := by
    have := le_trans hb hθs
    simpa [clockTheta] using this
  have hνa_s : ν * clockA ν s ≤ 1 := by
    have hp : 0 < ν * clockA ν s := mul_pos hν ha_s_pos
    rwa [one_le_inv₀ hp] at hθ1
  have hA_s : clockA ν s ≤ ν⁻¹ := by
    rw [le_inv_comm₀ ha_s_pos hν, inv_eq_one_div, le_div_iff₀ ha_s_pos]
    linarith
  have hν_inv1 : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hA_r_le : clockA ν r ≤ 2 * ν⁻¹ := by
    have hrs1 : r ≤ s + 1 := hr.2.le
    have h1 : clockA ν r ≤ clockA ν s + ν := by
      unfold clockA
      nlinarith
    linarith
  have hrpow : ν ^ (-2 : ℝ) = (ν ^ 2)⁻¹ := by
    rw [Real.rpow_neg hν.le]
    norm_cast
  unfold cellLen
  rw [hrpow]
  have hsq : 0 < Real.sqrt (clockA ν r) := Real.sqrt_pos.2 ha_r_pos
  rw [le_div_iff₀ hsq]
  have h1 : 0 < (ν ^ 2)⁻¹ := by positivity
  refine le_of_sq_le_sq ?_ h1.le
  rw [mul_pow, Real.sq_sqrt ha_r_pos.le]
  have hD_nu : 2 * D ^ 2 * ν ^ 3 ≤ 1 := by
    have h3 : ν ^ 3 ≤ ν * (1 / (2 * (D + 1) ^ 2)) ^ 2 := by
      have : ν ^ 2 ≤ (1 / (2 * (D + 1) ^ 2)) ^ 2 := pow_le_pow_left₀ hν.le hνD 2
      nlinarith [hν]
    have h4 : 2 * D ^ 2 * (1 / (2 * (D + 1) ^ 2)) ^ 2 ≤ 1 := by
      rw [div_pow, one_pow, ← mul_div_assoc, mul_one, div_le_one (by positivity)]
      nlinarith [sq_nonneg D, sq_nonneg (D + 1), mul_nonneg hD hD]
    calc 2 * D ^ 2 * ν ^ 3
        ≤ 2 * D ^ 2 * (ν * (1 / (2 * (D + 1) ^ 2)) ^ 2) := by gcongr
      _ = ν * (2 * D ^ 2 * (1 / (2 * (D + 1) ^ 2)) ^ 2) := by ring
      _ ≤ ν * 1 := by gcongr
      _ ≤ 1 := by linarith
  have hrhs : ((ν ^ 2)⁻¹) ^ 2 = (ν ^ 4)⁻¹ := by rw [← inv_pow]; ring
  calc D ^ 2 * clockA ν r
      ≤ D ^ 2 * (2 * ν⁻¹) := by gcongr
    _ = (2 * D ^ 2 * ν ^ 3) * (ν ^ 4)⁻¹ := by field_simp
    _ ≤ 1 * (ν ^ 4)⁻¹ := by gcongr
    _ = ((ν ^ 2)⁻¹) ^ 2 := by rw [hrhs, one_mul]

/-! ## 2. Smoothness of `clockA`, `cellLen`, and `(perGram κ ·)⁻¹` -/

/-- `clockA ν` is `C^∞` on `ℝ`. -/
theorem contDiff_clockA (ν : ℝ) : ContDiff ℝ ∞ (clockA ν) := by
  unfold clockA
  exact contDiff_const.add (contDiff_const.mul contDiff_id)

/-- `r ↦ Real.sqrt (clockA ν r)` is `C^∞` on `Ici 0` for `ν ≥ 0`. -/
theorem contDiffOn_sqrt_clockA {ν : ℝ} (hν : 0 ≤ ν) :
    ContDiffOn ℝ ∞ (fun r => Real.sqrt (clockA ν r)) (Ici 0) :=
  (contDiff_clockA ν).contDiffOn.sqrt fun _r hr =>
    (lt_of_lt_of_le zero_lt_one (one_le_clockA hν hr)).ne'

/-- `r ↦ cellLen c (clockA ν r)` is `C^∞` on `Ici 0` for `ν ≥ 0`. -/
theorem contDiffOn_cellLen_clockA (c : ℝ) {ν : ℝ} (hν : 0 ≤ ν) :
    ContDiffOn ℝ ∞ (fun r => cellLen c (clockA ν r)) (Ici 0) := by
  unfold cellLen
  refine contDiffOn_const.div (contDiffOn_sqrt_clockA hν) fun _r hr => ?_
  exact (Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one (one_le_clockA hν hr))).ne'

/-- If every entry of `perGram κ d` is `C^∞` on `Ici 1` and `perGram κ d` is within `1 / 4` of the
identity for `d ≥ D₁`, then every entry of `(perGram κ d)⁻¹` is `C^∞` on `Ici (max D₁ 1)`. -/
theorem contDiffOn_perGram_inv_of (κ : PlanarFrameKernels) {D₁ : ℝ}
    (hD₁ : ∀ d : ℝ, D₁ ≤ d → ∀ i j : Fin 2,
      ‖perGram κ d i j - (if i = j then 1 else 0)‖ ≤ 1 / 4)
    (hG : ∀ a b : Fin 2, ContDiffOn ℝ ∞ (fun d : ℝ => perGram κ d a b) (Ici 1))
    (i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun d : ℝ => (perGram κ d)⁻¹ i j) (Ici (max D₁ 1)) := by
  have hsub : Ici (max D₁ 1) ⊆ Ici 1 := Ici_subset_Ici.2 (le_max_right _ _)
  have hG' : ∀ a b : Fin 2, ContDiffOn ℝ ∞ (fun d : ℝ => perGram κ d a b) (Ici (max D₁ 1)) :=
    fun a b => (hG a b).mono hsub
  have hdet : ContDiffOn ℝ ∞ (fun d : ℝ => (perGram κ d).det) (Ici (max D₁ 1)) := by
    have heq : (fun d : ℝ => (perGram κ d).det) =
        fun d => perGram κ d 0 0 * perGram κ d 1 1 - perGram κ d 0 1 * perGram κ d 1 0 := by
      funext d
      exact Matrix.det_fin_two (perGram κ d)
    rw [heq]
    exact ((hG' 0 0).mul (hG' 1 1)).sub ((hG' 0 1).mul (hG' 1 0))
  have hdet_ne : ∀ d ∈ Ici (max D₁ 1), (perGram κ d).det ≠ 0 := by
    intro d hd
    have hdD : D₁ ≤ d := le_trans (le_max_left _ _) hd
    exact isUnit_iff_ne_zero.1 (gram_inv_bound _ (hD₁ d hdD)).1
  have hdet_inv : ContDiffOn ℝ ∞ (fun d : ℝ => ((perGram κ d).det)⁻¹) (Ici (max D₁ 1)) :=
    hdet.inv hdet_ne
  fin_cases i <;> fin_cases j
  · change ContDiffOn ℝ ∞ (fun d : ℝ => (perGram κ d)⁻¹ 0 0) (Ici (max D₁ 1))
    have hentry : (fun d : ℝ => (perGram κ d)⁻¹ 0 0) =
        fun d => ((perGram κ d).det)⁻¹ * perGram κ d 1 1 := by
      funext d; rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]; rfl
    rw [hentry]
    exact hdet_inv.mul (hG' 1 1)
  · change ContDiffOn ℝ ∞ (fun d : ℝ => (perGram κ d)⁻¹ 0 1) (Ici (max D₁ 1))
    have hentry : (fun d : ℝ => (perGram κ d)⁻¹ 0 1) =
        fun d => ((perGram κ d).det)⁻¹ * (-perGram κ d 0 1) := by
      funext d; rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]; rfl
    rw [hentry]
    exact hdet_inv.mul (hG' 0 1).neg
  · change ContDiffOn ℝ ∞ (fun d : ℝ => (perGram κ d)⁻¹ 1 0) (Ici (max D₁ 1))
    have hentry : (fun d : ℝ => (perGram κ d)⁻¹ 1 0) =
        fun d => ((perGram κ d).det)⁻¹ * (-perGram κ d 1 0) := by
      funext d; rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]; rfl
    rw [hentry]
    exact hdet_inv.mul (hG' 1 0).neg
  · change ContDiffOn ℝ ∞ (fun d : ℝ => (perGram κ d)⁻¹ 1 1) (Ici (max D₁ 1))
    have hentry : (fun d : ℝ => (perGram κ d)⁻¹ 1 1) =
        fun d => ((perGram κ d).det)⁻¹ * perGram κ d 0 0 := by
      funext d; rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]; rfl
    rw [hentry]
    exact hdet_inv.mul (hG' 0 0)

/-- Joint `C^∞` smoothness of `p ↦ (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν p.1)))⁻¹ i j` on
`Ico t (s + 1) ×ˢ univ`. -/
theorem contDiffOn_perGram_inv_clockA_of (κ : PlanarFrameKernels) {D₁ ν t s b : ℝ}
    (hD₁ : ∀ d : ℝ, D₁ ≤ d → ∀ i j : Fin 2,
      ‖perGram κ d i j - (if i = j then 1 else 0)‖ ≤ 1 / 4)
    (hG : ∀ a b : Fin 2, ContDiffOn ℝ ∞ (fun d : ℝ => perGram κ d a b) (Ici 1))
    (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hνD : ν ≤ 1 / (2 * (max D₁ 1 + 1) ^ 2))
    (hb : 1 ≤ b) (ht : 0 ≤ t) (hts : t ≤ s) (hθs : b ≤ clockTheta ν s)
    (i j : Fin 2) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × (ℝ × ℝ) =>
        (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν p.1)))⁻¹ i j)
      (Ico t (s + 1) ×ˢ univ) := by
  have hD_nonneg : 0 ≤ max D₁ 1 := le_trans zero_le_one (le_max_right _ _)
  have hcell : ContDiffOn ℝ ∞
      (fun p : ℝ × (ℝ × ℝ) => cellLen (ν ^ (-2 : ℝ)) (clockA ν p.1))
      (Ico t (s + 1) ×ˢ univ) :=
    (contDiffOn_cellLen_clockA (ν ^ (-2 : ℝ)) hν.le).comp contDiff_fst.contDiffOn
      (fun p hp => ht.trans hp.1.1)
  refine (contDiffOn_perGram_inv_of κ hD₁ hG i j).comp hcell (fun p hp => ?_)
  exact cellLen_ge_on_Ico_add_one hD_nonneg hν hν1 hνD hb ht hts hθs hp.1

/-! ## 3. Analytical leaves and conditional assembly of `PhysFrameLamSmooth` -/

/-- **Leaf 2a (`PartIII-a:T21/c5/1/1/2/1`, `PerGramSmooth`, SP 593-610, 2891-2905)**:
For a Part I seed kernel `κ` (`IsSeedKernels κ`), each Gram matrix entry `d ↦ perGram κ d i j` is
`C^∞` on `Ici 1`.
Composed by task `PartIII-a:T21/c5/1/1/2` via `physFrameLamSmooth_of`. -/
def PerGramSmooth (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ i j : Fin 2, ContDiffOn ℝ ∞ (fun d : ℝ => perGram κ d i j) (Ici 1)

/-- **Leaf 2b (`PartIII-a:T21/c5/1/1/2/2`, `PhysFrameLam0Smooth`, SP 593-610, 2891-2905)**:
For a Part I seed kernel `κ` (`IsSeedKernels κ`), for any `ν > 0` and `t ≥ 0`, the unnormalised
physical-variable periodized dual row
`(r, x) ↦ perSum (ν ^ (-2 : ℝ)) (physAdj (clockA ν r) (κ.lamP j)) x` is jointly `C^∞` on
`Ici t ×ˢ univ`.
Composed by task `PartIII-a:T21/c5/1/1/2` via `physFrameLamSmooth_of`. -/
def PhysFrameLam0Smooth (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ {ν t : ℝ}, 0 < ν → 0 ≤ t → ∀ j : Fin 2,
    ContDiffOn ℝ ∞
      (fun p : ℝ × (ℝ × ℝ) =>
        perSum (ν ^ (-2 : ℝ)) (physAdj (clockA ν p.1) (κ.lamP j)) p.2)
      (Ici t ×ˢ univ)

/-- Conditional proof of `PhysFrameLamSmooth κ` (`PartIII-a:T21/c5/1/1/2`) from
`PerGramSmooth κ` and `PhysFrameLam0Smooth κ`. -/
theorem physFrameLamSmooth_of (κ : PlanarFrameKernels)
    (hGram : PerGramSmooth κ) (hLam0 : PhysFrameLam0Smooth κ) :
    PhysFrameLamSmooth κ := by
  intro hκ
  obtain ⟨D₁, hD₁⟩ :=
    perGramNear_of κ (perGramUnfold κ) (perGramTail κ) (1 / 4) (by norm_num)
  have hG := hGram hκ
  set D : ℝ := max D₁ 1
  set ν_sm : ℝ := min (1 / (2 * (D + 1) ^ 2)) 1
  have hD_pos : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hν_sm_pos : 0 < ν_sm := lt_min (by positivity) zero_lt_one
  refine ⟨1, le_rfl, fun b hb => ⟨ν_sm, hν_sm_pos, fun ν hν t s ht hts hθs i => ?_⟩⟩
  have hν0 : 0 < ν := hν.1
  have hνD : ν ≤ 1 / (2 * (D + 1) ^ 2) := le_trans hν.2 (min_le_left _ _)
  have hν1 : ν ≤ 1 := le_trans hν.2 (min_le_right _ _)
  have hsub : Ico t (s + 1) ×ˢ (univ : Set (ℝ × ℝ)) ⊆ Ici t ×ˢ univ :=
    prod_mono Ico_subset_Ici_self Subset.rfl
  have hterm : ∀ j : Fin 2,
      ContDiffOn ℝ ∞
        (fun p : ℝ × (ℝ × ℝ) =>
          (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν p.1)))⁻¹ i j *
            perSum (ν ^ (-2 : ℝ)) (physAdj (clockA ν p.1) (κ.lamP j)) p.2)
        (Ico t (s + 1) ×ˢ univ) := fun j =>
    (contDiffOn_perGram_inv_clockA_of κ hD₁ hG hν0 hν1 hνD hb ht hts hθs i j).mul
      ((hLam0 hκ hν0 ht j).mono hsub)
  have hsum : ContDiffOn ℝ ∞
      (fun p : ℝ × (ℝ × ℝ) =>
        ∑ j : Fin 2,
          (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν p.1)))⁻¹ i j *
            perSum (ν ^ (-2 : ℝ)) (physAdj (clockA ν p.1) (κ.lamP j)) p.2)
      (Ico t (s + 1) ×ˢ univ) := by
    have heq : (fun p : ℝ × (ℝ × ℝ) =>
        ∑ j : Fin 2,
          (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν p.1)))⁻¹ i j *
            perSum (ν ^ (-2 : ℝ)) (physAdj (clockA ν p.1) (κ.lamP j)) p.2) =
        fun p =>
          (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν p.1)))⁻¹ i 0 *
            perSum (ν ^ (-2 : ℝ)) (physAdj (clockA ν p.1) (κ.lamP 0)) p.2 +
          (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν p.1)))⁻¹ i 1 *
            perSum (ν ^ (-2 : ℝ)) (physAdj (clockA ν p.1) (κ.lamP 1)) p.2 := by
      funext p
      exact Fin.sum_univ_two _
    rw [heq]
    exact (hterm 0).add (hterm 1)
  refine hsum.congr fun p hp => ?_
  have hr0 : 0 ≤ p.1 := ht.trans hp.1.1
  rw [physFrameLam_eq_sum_perGram_inv κ ν p.1 i p.2]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [physFrameLam0_eq_perSum_physAdj κ hν0 hr0 j p.2]

end CutFTCSmooth

/-- Top-level alias for `CutFTCSmooth.PerGramSmooth`. -/
abbrev PerGramSmooth (κ : PlanarFrameKernels) : Prop :=
  CutFTCSmooth.PerGramSmooth κ

/-- Top-level alias for `CutFTCSmooth.PhysFrameLam0Smooth`. -/
abbrev PhysFrameLam0Smooth (κ : PlanarFrameKernels) : Prop :=
  CutFTCSmooth.PhysFrameLam0Smooth κ

/-- Top-level conditional proof of `PhysFrameLamSmooth κ` (`PartIII-a:T21/c5/1/1/2`) from
`PerGramSmooth κ` and `PhysFrameLam0Smooth κ`. -/
theorem physFrameLamSmooth_of (κ : PlanarFrameKernels)
    (hGram : PerGramSmooth κ) (hLam0 : PhysFrameLam0Smooth κ) :
    PhysFrameLamSmooth κ :=
  CutFTCSmooth.physFrameLamSmooth_of κ hGram hLam0

end UnforcedLeray.Short.IIIa
