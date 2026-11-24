import UnforcedLeray.Short.PartIIa.Sub.R02_6

/-!
# Part II-a, task `PartII-a:R02/MeanStress/MixedLeibniz`: the mixed Leibniz rule

Source of record: `the November 2 reference manuscript`, lines 397-404 (`sct:mean`,
`g = \overline{v_1 v_2}`) and 439-446 (`sct:fluctuation`).

Target: `mixedLeibniz_of (hA : AgeDerivSmooth) : MixedLeibniz` (`Sub/R02_6.lean`).

Route. Fix `s > 0`, `a`, `k`, `η`.
1. Inner Leibniz in the age variable, at each `e`: `r ↦ A r e` and `r ↦ B r e` are `C^∞` at `s`
   (restriction of the jointly smooth function to a slice through the open set), so
   `iteratedDeriv_fun_mul` gives `∂_s^k (A B)(·, e) = ∑_l C(k,l) (∂_s^l A)(·,e) (∂_s^{k-l} B)(·,e)`.
2. The slices `e ↦ ∂_s^l A(s, e)` are `C^∞` on `ℝ` (by `hA.1`, composed with `e ↦ (s, e)`).
3. Outer derivative in `e`: `iteratedDeriv_fun_sum` and `iteratedDeriv_const_mul_field`, then
   `iteratedDeriv_fun_mul` for each product; finally `Finset.sum_comm` and `ring`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

/-- A `C^∞` function on the open set is `C^n` at each point, for each natural `n`. -/
theorem mlz_contDiffAt_nat {f : ℝ → ℝ} {x : ℝ} (h : ContDiffAt ℝ ∞ f x) (n : ℕ) :
    ContDiffAt ℝ n f x :=
  ContDiffAt.of_le h (by exact_mod_cast le_top)

/-- The age slice `r ↦ A r e` of a jointly smooth function is `C^∞` at each age `s > 0`. -/
theorem mlz_age_slice_contDiffAt (A : ℝ → ℝ → ℝ)
    (hA : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => A x.1 x.2) (Ioi 0 ×ˢ univ))
    (s : ℝ) (hs : 0 < s) (e : ℝ) :
    ContDiffAt ℝ ∞ (fun r => A r e) s := by
  have h1 : ContDiffAt ℝ ∞ (fun x : ℝ × ℝ => A x.1 x.2) (s, e) :=
    hA.contDiffAt ((isOpen_Ioi.prod isOpen_univ :
      IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))).mem_nhds
        (Set.mk_mem_prod (show s ∈ Ioi (0 : ℝ) from hs) (Set.mem_univ e)))
  have h2 : ContDiffAt ℝ ∞ (fun r : ℝ => (r, e)) s :=
    contDiffAt_id.prodMk contDiffAt_const
  exact h1.comp s h2

/-- The age-derivative slice `e ↦ ∂_s^l A(s, e)` is `C^∞` on `ℝ`, for `s > 0`. -/
theorem mlz_slice_contDiff (A : ℝ → ℝ → ℝ)
    (hAge : ∀ j : ℕ, ContDiffOn ℝ ∞
      (fun x : ℝ × ℝ => iteratedDeriv j (fun r => A r x.2) x.1) (Ioi 0 ×ˢ univ))
    (s : ℝ) (hs : 0 < s) (l : ℕ) :
    ContDiff ℝ ∞ (fun e => iteratedDeriv l (fun r => A r e) s) := by
  rw [contDiff_iff_contDiffAt]
  intro e
  have h1 : ContDiffAt ℝ ∞ (fun x : ℝ × ℝ => iteratedDeriv l (fun r => A r x.2) x.1) (s, e) :=
    (hAge l).contDiffAt ((isOpen_Ioi.prod isOpen_univ :
      IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))).mem_nhds
        (Set.mk_mem_prod (show s ∈ Ioi (0 : ℝ) from hs) (Set.mem_univ e)))
  have h2 : ContDiffAt ℝ ∞ (fun y : ℝ => (s, y)) e :=
    contDiffAt_const.prodMk contDiffAt_id
  exact h1.comp e h2

/-- **Mixed Leibniz rule** (source lines 397-404 and 439-446): from `AgeDerivSmooth`, the
statement `MixedLeibniz` holds. -/
theorem mixedLeibniz_of (hA : UnforcedLeray.Short.PartIIa.AgeDerivSmooth) :
    UnforcedLeray.Short.PartIIa.MixedLeibniz := by
  unfold UnforcedLeray.Short.PartIIa.MixedLeibniz
  intro A B hA' hB' a k s η hs
  have hAge := hA.1 A hA'
  have hBge := hA.1 B hB'
  have hPc : ∀ l : ℕ, ContDiff ℝ ∞ (fun e => iteratedDeriv l (fun r => A r e) s) :=
    fun l => mlz_slice_contDiff A hAge s hs l
  have hQc : ∀ j : ℕ, ContDiff ℝ ∞ (fun e => iteratedDeriv j (fun r => B r e) s) :=
    fun j => mlz_slice_contDiff B hBge s hs j
  -- Step 1: Leibniz in the age variable, for each age slice `e`
  have hinner : ∀ e : ℝ, iteratedDeriv k (fun r => A r e * B r e) s =
      ∑ l ∈ Finset.range (k + 1), (k.choose l : ℝ) *
        (iteratedDeriv l (fun r => A r e) s * iteratedDeriv (k - l) (fun r => B r e) s) := by
    intro e
    rw [iteratedDeriv_fun_mul
      (mlz_contDiffAt_nat (mlz_age_slice_contDiffAt A hA' s hs e) k)
      (mlz_contDiffAt_nat (mlz_age_slice_contDiffAt B hB' s hs e) k)]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  -- Step 2: each summand is `C^∞` in `e`
  have hF : ∀ l : ℕ, ContDiff ℝ ∞ (fun e => (k.choose l : ℝ) *
      (iteratedDeriv l (fun r => A r e) s * iteratedDeriv (k - l) (fun r => B r e) s)) :=
    fun l => contDiff_const.mul ((hPc l).mul (hQc (k - l)))
  -- Step 3: outer derivative in `e` commutes with the finite sum
  have hsumlin : iteratedDeriv a (fun e => ∑ l ∈ Finset.range (k + 1), (k.choose l : ℝ) *
      (iteratedDeriv l (fun r => A r e) s * iteratedDeriv (k - l) (fun r => B r e) s)) η =
      ∑ l ∈ Finset.range (k + 1), iteratedDeriv a (fun e => (k.choose l : ℝ) *
        (iteratedDeriv l (fun r => A r e) s * iteratedDeriv (k - l) (fun r => B r e) s)) η :=
    iteratedDeriv_fun_sum (fun l _ => mlz_contDiffAt_nat (hF l).contDiffAt a)
  -- Step 4: each term is Leibniz in `e`
  have hterm : ∀ l ∈ Finset.range (k + 1),
      iteratedDeriv a (fun e => (k.choose l : ℝ) *
        (iteratedDeriv l (fun r => A r e) s * iteratedDeriv (k - l) (fun r => B r e) s)) η =
      ∑ i ∈ Finset.range (a + 1), (k.choose l : ℝ) * ((a.choose i : ℝ) *
        (iteratedDeriv i (fun e => iteratedDeriv l (fun r => A r e) s) η *
          iteratedDeriv (a - i) (fun e => iteratedDeriv (k - l) (fun r => B r e) s) η)) := by
    intro l _
    rw [iteratedDeriv_const_mul_field,
      iteratedDeriv_fun_mul (mlz_contDiffAt_nat (hPc l).contDiffAt a)
        (mlz_contDiffAt_nat (hQc (k - l)).contDiffAt a),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  -- Assemble: reorder the double sum and match the statement
  simp only [hinner]
  rw [hsumlin, Finset.sum_congr rfl hterm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end UnforcedLeray.Short.PartIIa
