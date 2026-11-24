import UnforcedLeray.Short.PartIIa.Sub.R08_2

/-!
# Part II-a, task `PartII-a:R08/2/4`: sums and congruence for the flatness class (`FlatAddCongr`)

Source of record: `the November 2 reference manuscript`, lines 1330-1334 ("Each
derivative costs `C/r`; all powers of `|x|/r` are absorbed by the Gaussian decay in `η = Rz/r`";
"including smoothness at nonzero axis points").

Target `FlatAddCongr` (`Sub/R08_2.lean`), with `W = flatRegion δ M`:
(i) `FlatOn W κ f → FlatOn W κ g → FlatOn W κ (f + g)`;
(ii) `(∀ y ∉ Axi.axis, f y = g y) → FlatOn W κ f → FlatOn W κ g`.

Proof. (i) On the open set `axisᶜ` both `f` and `g` are `C^∞`, so `ContDiffOn.add` gives the
smoothness of the sum, and `iteratedFDeriv_add_apply` splits the iterated derivative of the sum
into the two iterated derivatives. Each term is bounded by `C_i / ϱ^{N_i} * e` with the common
factor `e = exp(-κ/ϱ²) ≥ 0`. On `W` we have `0 < ϱ < 1`, so `ϱ^{-N_i} ≤ ϱ^{-N}` for
`N = max N₁ N₂`, and `|C_i|` dominates `C_i`; the constant is `|C₁| + |C₂|`.
(ii) `f` and `g` agree on the open set `axisᶜ`, so `f =ᶠ[𝓝 y] g` at every `y ∈ W`
(`Filter.EventuallyEq.iteratedFDeriv`), hence their iterated derivatives agree at `y`, and the
same constants serve.

Helper prefix: `fac*`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

/-- Helper: a bound `C / t^{N₁} * e ≤ |C| / t^N * e` for `0 < t < 1`, `N₁ ≤ N`, `e ≥ 0`. -/
theorem fac_term_le {C t e : ℝ} {N₁ N : ℕ} (ht0 : 0 < t) (ht1 : t < 1) (h : N₁ ≤ N)
    (he : 0 ≤ e) : C / t ^ N₁ * e ≤ |C| / t ^ N * e := by
  have hinv : (t ^ N₁)⁻¹ ≤ (t ^ N)⁻¹ :=
    inv_anti₀ (pow_pos ht0 N) (pow_le_pow_of_le_one ht0.le ht1.le h)
  have h1 : C / t ^ N₁ ≤ |C| / t ^ N := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    calc C * (t ^ N₁)⁻¹ ≤ |C| * (t ^ N₁)⁻¹ :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (inv_nonneg.mpr (pow_nonneg ht0.le N₁))
      _ ≤ |C| * (t ^ N)⁻¹ := mul_le_mul_of_nonneg_left hinv (abs_nonneg C)
  exact mul_le_mul_of_nonneg_right h1 he

/-- **Sums and congruence** (task `PartII-a:R08/2/4`): `FlatOn` is closed under sums, and depends
only on the values off the axis. -/
theorem flatAddCongr : FlatAddCongr := by
  unfold FlatAddCongr
  intro δ M κ E _ _ f g
  refine ⟨fun hf hg => ?_, fun hfg hf => ?_⟩
  · obtain ⟨hfC, hfB⟩ := hf
    obtain ⟨hgC, hgB⟩ := hg
    unfold FlatOn
    refine ⟨hfC.add hgC, fun n => ?_⟩
    obtain ⟨C₁, N₁, h₁⟩ := hfB n
    obtain ⟨C₂, N₂, h₂⟩ := hgB n
    refine ⟨|C₁| + |C₂|, max N₁ N₂, fun y hy => ?_⟩
    have hy' : y ∉ Axi.axis ∧ Axi.ϱ y < 1 ∧ δ ≤ |y 2| ∧ |y 2| ≤ M := hy
    obtain ⟨hyax, hylt, -, -⟩ := hy'
    have hpos : 0 < Axi.ϱ y := Axi.ϱ_pos hyax
    have hexp : 0 ≤ Real.exp (-κ / Axi.ϱ y ^ 2) := (Real.exp_pos _).le
    have hyc : y ∈ Axi.axisᶜ := hyax
    have hfa : ContDiffAt ℝ n f y :=
      contDiffAt_infty.mp (hfC.contDiffAt (Axi.isOpen_compl_axis.mem_nhds hyc)) n
    have hga : ContDiffAt ℝ n g y :=
      contDiffAt_infty.mp (hgC.contDiffAt (Axi.isOpen_compl_axis.mem_nhds hyc)) n
    have hsum : iteratedFDeriv ℝ n (fun z => f z + g z) y
        = iteratedFDeriv ℝ n f y + iteratedFDeriv ℝ n g y :=
      iteratedFDeriv_add_apply hfa hga
    calc ‖iteratedFDeriv ℝ n (fun z => f z + g z) y‖
        ≤ ‖iteratedFDeriv ℝ n f y‖ + ‖iteratedFDeriv ℝ n g y‖ := by
          rw [hsum]
          exact norm_add_le _ _
      _ ≤ C₁ / Axi.ϱ y ^ N₁ * Real.exp (-κ / Axi.ϱ y ^ 2)
            + C₂ / Axi.ϱ y ^ N₂ * Real.exp (-κ / Axi.ϱ y ^ 2) :=
          add_le_add (h₁ y hy) (h₂ y hy)
      _ ≤ |C₁| / Axi.ϱ y ^ max N₁ N₂ * Real.exp (-κ / Axi.ϱ y ^ 2)
            + |C₂| / Axi.ϱ y ^ max N₁ N₂ * Real.exp (-κ / Axi.ϱ y ^ 2) :=
          add_le_add (fac_term_le hpos hylt (le_max_left N₁ N₂) hexp)
            (fac_term_le hpos hylt (le_max_right N₁ N₂) hexp)
      _ = (|C₁| + |C₂|) / Axi.ϱ y ^ max N₁ N₂ * Real.exp (-κ / Axi.ϱ y ^ 2) := by ring
  · obtain ⟨hfC, hfB⟩ := hf
    unfold FlatOn
    have hgC : ContDiffOn ℝ ∞ g Axi.axisᶜ := hfC.congr (fun z hz => (hfg z hz).symm)
    refine ⟨hgC, fun n => ?_⟩
    obtain ⟨C, N, hCN⟩ := hfB n
    refine ⟨C, N, fun y hy => ?_⟩
    have hy' : y ∉ Axi.axis ∧ Axi.ϱ y < 1 ∧ δ ≤ |y 2| ∧ |y 2| ≤ M := hy
    obtain ⟨hyax, -, -, -⟩ := hy'
    have hyc : y ∈ Axi.axisᶜ := hyax
    have hev : f =ᶠ[𝓝 y] g := by
      filter_upwards [Axi.isOpen_compl_axis.mem_nhds hyc] with z hz using hfg z hz
    have heq : iteratedFDeriv ℝ n g y = iteratedFDeriv ℝ n f y :=
      ((hev.iteratedFDeriv ℝ n).eq_of_nhds).symm
    rw [heq]
    exact hCN y hy

end UnforcedLeray.Short.PartIIa

end
