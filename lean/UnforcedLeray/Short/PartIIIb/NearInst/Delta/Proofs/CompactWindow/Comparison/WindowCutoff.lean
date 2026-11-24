import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Sub.PartIIIb_C_near_delta_8_2
import UnforcedLeray.Short.PartIIIb.NearInst.Body.Proofs.WindowCutoff

/-!
# `windowCutoffExists` (source 3956-3967, item `PartIII-b:C/near/delta/8/2/1`)

Product cutoffs `cutK α β γ δ e p = φ(α s + β) φ(γ s + δ) φ(e - η) φ(e + η)` built from
`Real.smoothTransition`, independent of `q` (so `c`-periodic). The factors are the ones of
`Body.WindowCutoff` (`good_factor`, `good_mul`, `cNorm8_le`, `iterDeriv_bdd8`), with the edges
chosen for the Delta window:

* `χ` (rising edge `l/2 → l`, falling edge `r → r+1`, `η`-width `|L|+1`): support in
  `[l/2, r+1] × {|η| ≤ |L|+1}`, equal to one on `[l, r] × {|η| ≤ |L|}`;
* `χ₁` (edges `l/8 → l/4`, `r+2 → r+3`, `η`-width `|L|+3`): equal to one on the open set
  `(l/4, r+2) × {|η| < |L|+2}`, which contains `tsupport χ`.

Both have `C⁸` norm `≤ 9 D (8(1+l⁻¹))⁸` with the universal `D` of `good_mul`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.Blueprint.Planar
open UnforcedLeray.Short.PartIIIb.NearInst.Body.WindowCutoff
open UnforcedLeray.Short.PartIIa
open Real

/-- The product cutoff `φ(α s + β) φ(γ s + δ) φ(e - η) φ(e + η)`. -/
def cutK (α β γ δ e : ℝ) (p : UnforcedLeray.B0220.Profile) : ℝ :=
  smoothTransition (α * ℓs p + β) * smoothTransition (γ * ℓs p + δ) *
    smoothTransition ((-1) * ℓη p + e) * smoothTransition (1 * ℓη p + e)

lemma cutK_good (C0 : ℝ) (hC0 : ∀ k, k ≤ 8 → ∀ x, ‖iteratedDeriv k smoothTransition x‖ ≤ C0)
    (α β γ δ e N : ℝ) (hα : |α| ≤ N) (hγ : |γ| ≤ N) (h1 : 1 ≤ N) :
    Good N (2 ^ 8 * (2 ^ 8 * (2 ^ 8 * C0 * C0) * C0) * C0) (cutK α β γ δ e) := by
  have hN : 0 ≤ N := le_trans zero_le_one h1
  have f1 := good_factor C0 hC0 ℓs ℓs_norm α β N hα
  have f2 := good_factor C0 hC0 ℓs ℓs_norm γ δ N hγ
  have f3 := good_factor C0 hC0 ℓη ℓη_norm (-1) e N (by simpa using h1)
  have f4 := good_factor C0 hC0 ℓη ℓη_norm 1 e N (by simpa using h1)
  exact good_mul hN (good_mul hN (good_mul hN f1 f2) f3) f4

lemma cutK_periodic (c α β γ δ e : ℝ) :
    UnforcedLeray.B0220.QPeriodic c (cutK α β γ δ e) := by
  intro p; rfl

lemma cutK_range (α β γ δ e : ℝ) (p : UnforcedLeray.B0220.Profile) :
    0 ≤ cutK α β γ δ e p ∧ cutK α β γ δ e p ≤ 1 := by
  unfold cutK
  have n1 := smoothTransition.nonneg (α * ℓs p + β)
  have n2 := smoothTransition.nonneg (γ * ℓs p + δ)
  have n3 := smoothTransition.nonneg ((-1) * ℓη p + e)
  have n4 := smoothTransition.nonneg (1 * ℓη p + e)
  have l1 := smoothTransition.le_one (α * ℓs p + β)
  have l2 := smoothTransition.le_one (γ * ℓs p + δ)
  have l3 := smoothTransition.le_one ((-1) * ℓη p + e)
  have l4 := smoothTransition.le_one (1 * ℓη p + e)
  exact ⟨mul_nonneg (mul_nonneg (mul_nonneg n1 n2) n3) n4,
    mul_le_one₀ (mul_le_one₀ (mul_le_one₀ l1 n2 l2) n3 l3) n4 l4⟩

/-- Support of `χ = cutK (2/l) (-1) (-1) (r+1) (|L|+1)`. -/
lemma cutK_support_chi {l r L : ℝ} (hl : 0 < l) (p : UnforcedLeray.B0220.Profile)
    (hp : cutK (2 * l⁻¹) (-1) (-1) (r + 1) (|L| + 1) p ≠ 0) :
    l / 2 ≤ p.1 ∧ p.1 ≤ r + 1 ∧ |p.2.2| ≤ |L| + 1 := by
  unfold cutK at hp
  simp only [ne_eq, mul_eq_zero, not_or, smoothTransition.zero_iff_nonpos, not_le] at hp
  obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := hp
  rw [ℓs_apply] at a b
  rw [ℓη_apply] at c d
  have hsa : 2 * l⁻¹ * p.1 + -1 = l⁻¹ * (2 * p.1 - l) := by
    rw [mul_sub, inv_mul_cancel₀ hl.ne']; ring
  rw [hsa] at a
  have a' := (mul_pos_iff_of_pos_left (inv_pos.2 hl)).1 a
  exact ⟨by linarith, by linarith, abs_le.2 ⟨by linarith, by linarith⟩⟩

/-- Support of `χ₁ = cutK (8/l) (-1) (-1) (r+3) (|L|+3)`. -/
lemma cutK_support_big {l r L : ℝ} (hl : 0 < l) (p : UnforcedLeray.B0220.Profile)
    (hp : cutK (8 * l⁻¹) (-1) (-1) (r + 3) (|L| + 3) p ≠ 0) :
    l / 8 ≤ p.1 ∧ p.1 ≤ r + 3 ∧ |p.2.2| ≤ |L| + 3 := by
  unfold cutK at hp
  simp only [ne_eq, mul_eq_zero, not_or, smoothTransition.zero_iff_nonpos, not_le] at hp
  obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := hp
  rw [ℓs_apply] at a b
  rw [ℓη_apply] at c d
  have hsa : 8 * l⁻¹ * p.1 + -1 = l⁻¹ * (8 * p.1 - l) := by
    rw [mul_sub, inv_mul_cancel₀ hl.ne']; ring
  rw [hsa] at a
  have a' := (mul_pos_iff_of_pos_left (inv_pos.2 hl)).1 a
  exact ⟨by linarith, by linarith, abs_le.2 ⟨by linarith, by linarith⟩⟩

/-- `χ = 1` on the bin `l ≤ s ≤ r`, `|η| ≤ |L|`. -/
lemma cutK_one_chi {l r L : ℝ} (hl : 0 < l) (p : UnforcedLeray.B0220.Profile)
    (h1 : l ≤ p.1) (h2 : p.1 ≤ r) (h3 : |p.2.2| ≤ |L|) :
    cutK (2 * l⁻¹) (-1) (-1) (r + 1) (|L| + 1) p = 1 := by
  unfold cutK
  rw [ℓs_apply, ℓη_apply]
  have hli : 0 < l⁻¹ := inv_pos.2 hl
  have hli' : l⁻¹ * l = 1 := inv_mul_cancel₀ hl.ne'
  have h0 : 0 ≤ l⁻¹ * (p.1 - l) := mul_nonneg hli.le (by linarith)
  have hA : 1 ≤ 2 * l⁻¹ * p.1 + -1 := by nlinarith
  have hB : 1 ≤ -1 * p.1 + (r + 1) := by linarith
  have hC : 1 ≤ -1 * p.2.2 + (|L| + 1) := by linarith [(abs_le.1 h3).2]
  have hD : 1 ≤ 1 * p.2.2 + (|L| + 1) := by linarith [(abs_le.1 h3).1]
  rw [smoothTransition.one_of_one_le hA, smoothTransition.one_of_one_le hB,
    smoothTransition.one_of_one_le hC, smoothTransition.one_of_one_le hD]
  norm_num

/-- `χ₁ = 1` on the open set `(l/4, r+2) × {|η| < |L|+2}`. -/
lemma cutK_one_big {l r L : ℝ} (hl : 0 < l) (p : UnforcedLeray.B0220.Profile)
    (h1 : l / 4 < p.1) (h2 : p.1 < r + 2) (h3 : |p.2.2| < |L| + 2) :
    cutK (8 * l⁻¹) (-1) (-1) (r + 3) (|L| + 3) p = 1 := by
  unfold cutK
  rw [ℓs_apply, ℓη_apply]
  have hli : 0 < l⁻¹ := inv_pos.2 hl
  have hli' : l⁻¹ * l = 1 := inv_mul_cancel₀ hl.ne'
  have h0 : 0 ≤ l⁻¹ * (4 * p.1 - l) := mul_nonneg hli.le (by linarith)
  have hA : 1 ≤ 8 * l⁻¹ * p.1 + -1 := by nlinarith
  have hB : 1 ≤ -1 * p.1 + (r + 3) := by linarith
  have hC : 1 ≤ -1 * p.2.2 + (|L| + 3) := by linarith [(abs_lt.1 h3).2]
  have hD : 1 ≤ 1 * p.2.2 + (|L| + 3) := by linarith [(abs_lt.1 h3).1]
  rw [smoothTransition.one_of_one_le hA, smoothTransition.one_of_one_le hB,
    smoothTransition.one_of_one_le hC, smoothTransition.one_of_one_le hD]
  norm_num

open UnforcedLeray.Short.PartIIa in
/-- **The window cutoff** (item `PartIII-b:C/near/delta/8/2/1`; source 3956-3967). -/
theorem windowCutoffExists : WindowCutoffExists := by
  obtain ⟨C0, hC01, hC0⟩ := iterDeriv_bdd8
  have hC00 : 0 ≤ C0 := by linarith
  have hZ : 0 ≤ 2 ^ 8 * C0 * C0 := mul_nonneg (mul_nonneg (by norm_num) hC00) hC00
  have hY : 0 ≤ 2 ^ 8 * (2 ^ 8 * C0 * C0) * C0 :=
    mul_nonneg (mul_nonneg (by norm_num) hZ) hC00
  have hD0 : 0 ≤ 2 ^ 8 * (2 ^ 8 * (2 ^ 8 * C0 * C0) * C0) * C0 :=
    mul_nonneg (mul_nonneg (by norm_num) hY) hC00
  refine ⟨18 * (2 ^ 8 * (2 ^ 8 * (2 ^ 8 * C0 * C0) * C0) * C0) * 8 ^ 8,
    mul_nonneg (mul_nonneg (by norm_num) hD0) (by norm_num), ?_⟩
  intro c l r L hc hl hlr
  have hli : 0 < l⁻¹ := inv_pos.2 hl
  have hli' : l⁻¹ * l = 1 := inv_mul_cancel₀ hl.ne'
  set N : ℝ := 8 * (1 + l⁻¹) with hNdef
  have hN1 : 1 ≤ N := by rw [hNdef]; linarith
  have gχ := cutK_good C0 hC0 (2 * l⁻¹) (-1) (-1) (r + 1) (|L| + 1) N
    (by rw [abs_of_nonneg (by linarith)]; linarith) (by norm_num; linarith) hN1
  have gχ1 := cutK_good C0 hC0 (8 * l⁻¹) (-1) (-1) (r + 3) (|L| + 3) N
    (by rw [abs_of_nonneg (by linarith)]; linarith) (by norm_num; linarith) hN1
  have e1 := cNorm8_le hN1 gχ
  have e2 := cNorm8_le hN1 gχ1
  have hNpow : N ^ 8 = 8 ^ 8 * (1 + l⁻¹) ^ 8 := by rw [hNdef, mul_pow]
  rw [hNpow] at e1 e2
  -- the closed box containing the support of `χ`
  have hsub : Function.support (cutK (2 * l⁻¹) (-1) (-1) (r + 1) (|L| + 1)) ⊆
      {p : UnforcedLeray.B0220.Profile | l / 2 ≤ p.1 ∧ p.1 ≤ r + 1 ∧ |p.2.2| ≤ |L| + 1} :=
    fun p hp => cutK_support_chi hl p hp
  have hK' : IsClosed {p : UnforcedLeray.B0220.Profile |
      l / 2 ≤ p.1 ∧ p.1 ≤ r + 1 ∧ |p.2.2| ≤ |L| + 1} :=
    (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_fst continuous_const).inter
        (isClosed_le (continuous_abs.comp (continuous_snd.comp continuous_snd)) continuous_const))
  have hUo : IsOpen {p : UnforcedLeray.B0220.Profile |
      l / 4 < p.1 ∧ p.1 < r + 2 ∧ |p.2.2| < |L| + 2} :=
    (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_fst continuous_const).inter
        (isOpen_lt (continuous_abs.comp (continuous_snd.comp continuous_snd)) continuous_const))
  have htsub : tsupport (cutK (2 * l⁻¹) (-1) (-1) (r + 1) (|L| + 1)) ⊆
      {p : UnforcedLeray.B0220.Profile | l / 4 < p.1 ∧ p.1 < r + 2 ∧ |p.2.2| < |L| + 2} :=
    subset_trans (closure_minimal hsub hK')
      (fun p hp => ⟨by linarith [hp.1], by linarith [hp.2.1], by linarith [hp.2.2]⟩)
  refine ⟨cutK (2 * l⁻¹) (-1) (-1) (r + 1) (|L| + 1), cutK (8 * l⁻¹) (-1) (-1) (r + 3) (|L| + 3),
    ⟨gχ.1, cutK_periodic c _ _ _ _ _, fun p hp => cutK_support_chi hl p hp⟩,
    ⟨gχ1.1, cutK_periodic c _ _ _ _ _,
      ⟨l / 8, r + 3, |L| + 3, by linarith, fun p hp =>
        ⟨⟨(cutK_support_big hl p hp).1, (cutK_support_big hl p hp).2.1⟩,
          (cutK_support_big hl p hp).2.2⟩⟩,
      ⟨{p : UnforcedLeray.B0220.Profile | l / 4 < p.1 ∧ p.1 < r + 2 ∧ |p.2.2| < |L| + 2},
        hUo, htsub, fun p hp => cutK_one_big hl p hp.1 hp.2.1 hp.2.2⟩⟩,
    fun p => cutK_range _ _ _ _ _ p,
    fun p h1 h2 h3 => cutK_one_chi hl p h1 h2.le (le_trans h3 (le_abs_self L)),
    ?_⟩
  linarith [e1, e2]

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
