import UnforcedLeray.Short.PartIIa.Sub.R08_2

/-!
# Part II-a, task `PartII-a:R08/2/3`: Leibniz for the flatness class (`FlatSmul`)

Source of record: `the November 2 reference manuscript`, lines 1330-1334 ("Each
derivative costs `C/r`; all powers of `|x|/r` are absorbed by the Gaussian decay in `η = Rz/r`").

Target `FlatSmul` (`Sub/R08_2.lean`): if a scalar `f` is `FlatOn W κ₁` and a vector field `g` is
`FlatOn W κ₂`, then `f • g` is `FlatOn W (κ₁ + κ₂)`, where `W = flatRegion δ M`.

Proof: on the open set `axisᶜ`, the bilinear scalar multiplication has norm at most one, so the
Leibniz bound `‖D^n (f • g)‖ ≤ Σ_i choose n i ‖D^i f‖ ‖D^(n-i) g‖` holds (Mathlib's bilinear
estimate, transported from `iteratedFDerivWithin` to `iteratedFDeriv` on an open set). Each factor
is bounded by its own flatness constants; the powers of `ϱ` are compared using `ϱ ≤ 1`, and the two
Gaussian factors multiply to the Gaussian with exponent `κ₁ + κ₂`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

/-- Powers of `r ∈ (0, 1]`: `1/r^a * (1/r^b) ≤ 1/r^N` whenever `a + b ≤ N`. -/
theorem fsm_pow_mul_le {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (a b N : ℕ) (h : a + b ≤ N) :
    1 / r ^ a * (1 / r ^ b) ≤ 1 / r ^ N := by
  have e : 1 / r ^ a * (1 / r ^ b) = 1 / r ^ (a + b) := by
    rw [pow_add, one_div_mul_one_div]
  rw [e]
  exact one_div_le_one_div_of_le (pow_pos hr N) (pow_le_pow_of_le_one hr.le hr1 h)

/-- Replacing the constant by its absolute value only enlarges the bound. -/
theorem fsm_abs_le (C r e : ℝ) (k : ℕ) (hr : 0 ≤ r) (he : 0 ≤ e) :
    C / r ^ k * e ≤ |C| / r ^ k * e := by
  refine mul_le_mul_of_nonneg_right ?_ he
  exact div_le_div_of_nonneg_right (le_abs_self C) (pow_nonneg hr k)

/-- Pointwise Leibniz bound for `z ↦ f z • g z` on the open set `axisᶜ`, with the norms of the
iterated derivatives of `f` and `g` (bilinear estimate for `lsmul`, which has norm at most one). -/
theorem fsm_leibniz {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Space → ℝ} {g : Space → E} {y : Space}
    (hfS : ContDiffOn ℝ ∞ f Axi.axisᶜ) (hgS : ContDiffOn ℝ ∞ g Axi.axisᶜ) (hy : y ∈ Axi.axisᶜ)
    (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun z => f z • g z) y‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f y‖ *
        ‖iteratedFDeriv ℝ (n - i) g y‖ := by
  have hB : ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_lsmul_le
  have h1 : ‖iteratedFDerivWithin ℝ n (fun z => f z • g z) Axi.axisᶜ y‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i f Axi.axisᶜ y‖ *
        ‖iteratedFDerivWithin ℝ (n - i) g Axi.axisᶜ y‖ :=
    ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear_of_le_one
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E) hfS hgS
      Axi.isOpen_compl_axis.uniqueDiffOn hy (by exact_mod_cast le_top) hB
  have eF : ∀ m : ℕ, iteratedFDerivWithin ℝ m f Axi.axisᶜ y = iteratedFDeriv ℝ m f y :=
    fun m => iteratedFDerivWithin_of_isOpen m Axi.isOpen_compl_axis hy
  have eG : ∀ m : ℕ, iteratedFDerivWithin ℝ m g Axi.axisᶜ y = iteratedFDeriv ℝ m g y :=
    fun m => iteratedFDerivWithin_of_isOpen m Axi.isOpen_compl_axis hy
  have eP : iteratedFDerivWithin ℝ n (fun z => f z • g z) Axi.axisᶜ y =
      iteratedFDeriv ℝ n (fun z => f z • g z) y :=
    iteratedFDerivWithin_of_isOpen n Axi.isOpen_compl_axis hy
  rw [eP] at h1
  simp only [eF, eG] at h1
  exact h1

/-- **Leibniz for the flatness class** (task `PartII-a:R08/2/3`): scalar times vector, with the
exponents added. -/
theorem flatSmul : FlatSmul := by
  unfold FlatSmul
  intro δ M κ₁ κ₂ E _ _ f g hf hg
  unfold FlatOn at hf hg ⊢
  obtain ⟨hfS, hfb⟩ := hf
  obtain ⟨hgS, hgb⟩ := hg
  refine ⟨hfS.smul hgS, fun n => ?_⟩
  choose Cf Nf hCf using hfb
  choose Cg Ng hCg using hgb
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * |Cf i| * |Cg (n - i)|,
    (∑ i ∈ Finset.range (n + 1), Nf i) + (∑ i ∈ Finset.range (n + 1), Ng i), ?_⟩
  intro y hy
  have hy' : y ∉ Axi.axis ∧ Axi.ϱ y < 1 ∧ δ ≤ |y 2| ∧ |y 2| ≤ M := hy
  have hyS : y ∈ Axi.axisᶜ := hy'.1
  have hr : 0 < Axi.ϱ y := Axi.ϱ_pos hy'.1
  have hr1 : Axi.ϱ y ≤ 1 := hy'.2.1.le
  have hL := fsm_leibniz hfS hgS hyS n
  have hterm : ∀ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f y‖ * ‖iteratedFDeriv ℝ (n - i) g y‖ ≤
        (n.choose i : ℝ) * |Cf i| * |Cg (n - i)| *
          (Real.exp (-κ₁ / Axi.ϱ y ^ 2) * Real.exp (-κ₂ / Axi.ϱ y ^ 2)) *
          (1 / Axi.ϱ y ^ ((∑ k ∈ Finset.range (n + 1), Nf k) +
            (∑ k ∈ Finset.range (n + 1), Ng k))) := by
    intro i hi
    have hj : n - i ∈ Finset.range (n + 1) := Finset.mem_range.2 (by omega)
    have hNf : Nf i ≤ ∑ k ∈ Finset.range (n + 1), Nf k :=
      Finset.single_le_sum (fun k _ => Nat.zero_le _) hi
    have hNg : Ng (n - i) ≤ ∑ k ∈ Finset.range (n + 1), Ng k :=
      Finset.single_le_sum (fun k _ => Nat.zero_le _) hj
    have hA : ‖iteratedFDeriv ℝ i f y‖ ≤
        |Cf i| / Axi.ϱ y ^ Nf i * Real.exp (-κ₁ / Axi.ϱ y ^ 2) :=
      (hCf i y hy).trans (fsm_abs_le _ _ _ _ hr.le (Real.exp_pos _).le)
    have hB : ‖iteratedFDeriv ℝ (n - i) g y‖ ≤
        |Cg (n - i)| / Axi.ϱ y ^ Ng (n - i) * Real.exp (-κ₂ / Axi.ϱ y ^ 2) :=
      (hCg (n - i) y hy).trans (fsm_abs_le _ _ _ _ hr.le (Real.exp_pos _).le)
    have hpow := fsm_pow_mul_le hr hr1 (Nf i) (Ng (n - i))
      ((∑ k ∈ Finset.range (n + 1), Nf k) + (∑ k ∈ Finset.range (n + 1), Ng k)) (by omega)
    have hnn : (0 : ℝ) ≤ (n.choose i : ℝ) * |Cf i| * |Cg (n - i)| *
        (Real.exp (-κ₁ / Axi.ϱ y ^ 2) * Real.exp (-κ₂ / Axi.ϱ y ^ 2)) := by
      positivity
    calc (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f y‖ * ‖iteratedFDeriv ℝ (n - i) g y‖
        ≤ (n.choose i : ℝ) * (|Cf i| / Axi.ϱ y ^ Nf i * Real.exp (-κ₁ / Axi.ϱ y ^ 2)) *
            (|Cg (n - i)| / Axi.ϱ y ^ Ng (n - i) * Real.exp (-κ₂ / Axi.ϱ y ^ 2)) := by
          gcongr
      _ = (n.choose i : ℝ) * |Cf i| * |Cg (n - i)| *
            (Real.exp (-κ₁ / Axi.ϱ y ^ 2) * Real.exp (-κ₂ / Axi.ϱ y ^ 2)) *
            (1 / Axi.ϱ y ^ Nf i * (1 / Axi.ϱ y ^ Ng (n - i))) := by
          ring
      _ ≤ (n.choose i : ℝ) * |Cf i| * |Cg (n - i)| *
            (Real.exp (-κ₁ / Axi.ϱ y ^ 2) * Real.exp (-κ₂ / Axi.ϱ y ^ 2)) *
            (1 / Axi.ϱ y ^ ((∑ k ∈ Finset.range (n + 1), Nf k) +
              (∑ k ∈ Finset.range (n + 1), Ng k))) :=
          mul_le_mul_of_nonneg_left hpow hnn
  have he : Real.exp (-κ₁ / Axi.ϱ y ^ 2) * Real.exp (-κ₂ / Axi.ϱ y ^ 2) =
      Real.exp (-(κ₁ + κ₂) / Axi.ϱ y ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc ‖iteratedFDeriv ℝ n (fun z => f z • g z) y‖
      ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * |Cf i| * |Cg (n - i)| *
          (Real.exp (-κ₁ / Axi.ϱ y ^ 2) * Real.exp (-κ₂ / Axi.ϱ y ^ 2)) *
          (1 / Axi.ϱ y ^ ((∑ k ∈ Finset.range (n + 1), Nf k) +
            (∑ k ∈ Finset.range (n + 1), Ng k))) :=
        hL.trans (Finset.sum_le_sum hterm)
    _ = (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * |Cf i| * |Cg (n - i)|) *
          (Real.exp (-κ₁ / Axi.ϱ y ^ 2) * Real.exp (-κ₂ / Axi.ϱ y ^ 2)) *
          (1 / Axi.ϱ y ^ ((∑ k ∈ Finset.range (n + 1), Nf k) +
            (∑ k ∈ Finset.range (n + 1), Ng k))) := by
          rw [Finset.sum_mul, Finset.sum_mul]
    _ = (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * |Cf i| * |Cg (n - i)|) /
          Axi.ϱ y ^ ((∑ k ∈ Finset.range (n + 1), Nf k) +
            (∑ k ∈ Finset.range (n + 1), Ng k)) *
          Real.exp (-(κ₁ + κ₂) / Axi.ϱ y ^ 2) := by
          rw [← he]
          ring

end UnforcedLeray.Short.PartIIa
