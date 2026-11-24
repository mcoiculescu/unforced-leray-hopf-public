import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1_4_1_2.B.Avg

/-!
# Closure properties of "smooth on `s > 0` with bounded jets up to order `N`"

`JB N f`: `f : ℝ × Plane → E` is `C^∞` on `s > 0` and its joint jets of orders `≤ N` are bounded
there.  Closed under differences, constant multiples, continuous linear maps, products (Leibniz),
and `fderiv` (lowering `N`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete.PO

open UnforcedLeray.Cyl (Plane)

/-- Smooth on `s > 0` with joint jets of orders `≤ N` bounded there. -/
def JB {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (N : ℕ) (f : ℝ × Plane → E) : Prop :=
  ContDiffOn ℝ ∞ f DD ∧ ∃ K : ℝ, ∀ k : ℕ, k ≤ N → ∀ y : ℝ × Plane, 0 < y.1 →
    ‖iteratedFDeriv ℝ k f y‖ ≤ K

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiffAt_of_DD {f : ℝ × Plane → E} (hf : ContDiffOn ℝ ∞ f DD) {y : ℝ × Plane}
    (hy : 0 < y.1) : ContDiffAt ℝ ∞ f y :=
  hf.contDiffAt (isOpen_DD.mem_nhds ⟨hy, mem_univ _⟩)

theorem JB.mono {N M : ℕ} {f : ℝ × Plane → E} (h : JB N f) (hM : M ≤ N) : JB M f := by
  obtain ⟨hs, K, hK⟩ := h
  exact ⟨hs, K, fun k hk y hy => hK k (hk.trans hM) y hy⟩

theorem JB.sub {N : ℕ} {f g : ℝ × Plane → E} (hf : JB N f) (hg : JB N g) :
    JB N (fun y => f y - g y) := by
  obtain ⟨hfs, K1, hK1⟩ := hf
  obtain ⟨hgs, K2, hK2⟩ := hg
  refine ⟨hfs.sub hgs, K1 + K2, fun k hk y hy => ?_⟩
  have e : iteratedFDeriv ℝ k (f - g) y =
      iteratedFDeriv ℝ k f y - iteratedFDeriv ℝ k g y :=
    iteratedFDeriv_sub_apply ((contDiffAt_of_DD hfs hy).of_le (by exact_mod_cast le_top))
      ((contDiffAt_of_DD hgs hy).of_le (by exact_mod_cast le_top))
  show ‖iteratedFDeriv ℝ k (f - g) y‖ ≤ _
  rw [e]
  exact (norm_sub_le _ _).trans (add_le_add (hK1 k hk y hy) (hK2 k hk y hy))

theorem JB.const_smul {N : ℕ} {f : ℝ × Plane → E} (hf : JB N f) (a : ℝ) :
    JB N (fun y => a • f y) := by
  obtain ⟨hfs, K1, hK1⟩ := hf
  refine ⟨hfs.const_smul a, ‖a‖ * K1, fun k hk y hy => ?_⟩
  rw [iteratedFDeriv_const_smul_apply'
    ((contDiffAt_of_DD hfs hy).of_le (by exact_mod_cast le_top)), norm_smul]
  exact mul_le_mul_of_nonneg_left (hK1 k hk y hy) (norm_nonneg _)

theorem JB.clm {N : ℕ} {f : ℝ × Plane → E} (hf : JB N f) (L : E →L[ℝ] F) :
    JB N (fun y => L (f y)) := by
  obtain ⟨hfs, K1, hK1⟩ := hf
  refine ⟨L.contDiff.comp_contDiffOn hfs, ‖L‖ * K1, fun k hk y hy => ?_⟩
  have h := L.norm_iteratedFDeriv_comp_left (f := f) (x := y) (N := ∞) (n := k)
    (contDiffAt_of_DD hfs hy) (by exact_mod_cast le_top)
  exact h.trans (mul_le_mul_of_nonneg_left (hK1 k hk y hy) (norm_nonneg _))

theorem JB.fderiv {N : ℕ} {f : ℝ × Plane → ℝ} (hf : JB (N + 1) f) :
    JB N (fun y => fderiv ℝ f y) := by
  obtain ⟨hfs, K1, hK1⟩ := hf
  refine ⟨hfs.fderiv_of_isOpen isOpen_DD (by simp), K1, fun k hk y hy => ?_⟩
  rw [norm_iteratedFDeriv_fderiv]
  exact hK1 (k + 1) (by omega) y hy

theorem JB.mul {N : ℕ} {f g : ℝ × Plane → ℝ} (hf : JB N f) (hg : JB N g) :
    JB N (fun y => f y * g y) := by
  obtain ⟨hfs, K1, hK1⟩ := hf
  obtain ⟨hgs, K2, hK2⟩ := hg
  refine ⟨hfs.mul hgs, 2 ^ N * (max K1 0 * max K2 0), fun k hk y hy => ?_⟩
  have hyD : y ∈ DD := ⟨hy, mem_univ _⟩
  have h := norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ) (N := ∞) hfs hgs isOpen_DD.uniqueDiffOn
    hyD (n := k) (by exact_mod_cast le_top)
  rw [iteratedFDerivWithin_of_isOpen k isOpen_DD hyD] at h
  have hsum : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        ‖iteratedFDerivWithin ℝ i f DD y‖ * ‖iteratedFDerivWithin ℝ (k - i) g DD y‖ ≤
      ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (max K1 0 * max K2 0) := by
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hi' : i ≤ k := by simpa [Nat.lt_succ_iff] using hi
    rw [iteratedFDerivWithin_of_isOpen i isOpen_DD hyD,
      iteratedFDerivWithin_of_isOpen (k - i) isOpen_DD hyD]
    have a1 := (hK1 i (hi'.trans hk) y hy).trans (le_max_left K1 0)
    have a2 := (hK2 (k - i) ((Nat.sub_le _ _).trans hk) y hy).trans (le_max_left K2 0)
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    exact mul_le_mul a1 a2 (norm_nonneg _) (le_max_right _ _)
  have hchoose : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) = 2 ^ k := by
    exact_mod_cast Nat.sum_range_choose k
  rw [← Finset.sum_mul, hchoose] at hsum
  refine (h.trans hsum).trans ?_
  have hp : 0 ≤ max K1 0 * max K2 0 := mul_nonneg (le_max_right _ _) (le_max_right _ _)
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk) hp

end UnforcedLeray.Short.PartIIIb.Concrete.PO
