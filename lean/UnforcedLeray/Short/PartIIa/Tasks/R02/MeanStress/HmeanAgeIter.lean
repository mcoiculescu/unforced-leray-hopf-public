import UnforcedLeray.Short.PartIIa.Sub.R02_6
import UnforcedLeray.Short.PartI.Sub.T01

/-!
# Part II-a, task `PartII-a:R02/MeanStress/HmeanAgeIter`: iterated age derivatives commute with the
cell average

Source of record: `the November 2 reference manuscript`, lines 397-404 (`sct:mean`).
The statement `HmeanAgeIter` is defined in `Short/PartII-a/Sub/R02_6.lean`; the hypotheses are
`HmeanDerivS` (`Short/PartI/Sub/T01.lean`) and `AgeDerivSmooth` (`Short/PartII-a/Sub/R02_2.lean`).

Route. Fix `c > 0`. Induction on `k`, generalising over `f` (with its smoothness hypothesis) and over
`s`, `η`.
* `k = 0`: `iteratedDeriv_zero` makes both sides equal to `hmean c (f s) η`.
* `k + 1`: `iteratedDeriv_succ` turns the left side into `deriv` of `iteratedDeriv k` of the cell
  average. By the induction hypothesis the functions `r ↦ iteratedDeriv k (hmean c (f r) η)` and
  `r ↦ hmean c (g r) η` agree on the open set `Ioi 0`, which is a neighbourhood of `s`, where
  `g r z := iteratedDeriv k (fun r' => f r' z) r`. So their derivatives at `s` agree
  (`Filter.EventuallyEq.deriv_eq`). `g` is jointly `C^∞` on `Ioi 0 ×ˢ univ` by `AgeDerivSmooth`, so
  `HmeanDerivS` gives `deriv (fun r => hmean c (g r) η) s = hmean c (fun z => deriv (g · z) s) η`,
  and `deriv (g · z) s = iteratedDeriv (k + 1) (fun r => f r z) s` by `iteratedDeriv_succ`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.Short.PartI (hmean)

/-- **Iterated age derivatives commute with the cell average** (source lines 397-404): from
`HmeanDerivS` and `AgeDerivSmooth`, `HmeanAgeIter` holds. -/
theorem hmeanAgeIter_of (hD : UnforcedLeray.Short.PartI.HmeanDerivS)
    (hA : UnforcedLeray.Short.PartIIa.AgeDerivSmooth) :
    UnforcedLeray.Short.PartIIa.HmeanAgeIter := by
  unfold UnforcedLeray.Short.PartIIa.HmeanAgeIter
  intro c hc
  have key : ∀ k : ℕ, ∀ f : ℝ → ℝ × ℝ → ℝ,
      ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => f x.1 x.2) (Ioi 0 ×ˢ univ) →
      ∀ (s : ℝ), 0 < s → ∀ η : ℝ,
        iteratedDeriv k (fun r => hmean c (f r) η) s =
          hmean c (fun z => iteratedDeriv k (fun r => f r z) s) η := by
    intro k
    induction k with
    | zero =>
      intro f _hf s _hs η
      simp [iteratedDeriv_zero]
    | succ k ih =>
      intro f hf s hs η
      -- the induction hypothesis holds on the open neighbourhood `Ioi 0` of `s`
      have hev : (fun r => iteratedDeriv k (fun r' => hmean c (f r') η) r) =ᶠ[𝓝 s]
          (fun r => hmean c (fun z => iteratedDeriv k (fun r' => f r' z) r) η) := by
        filter_upwards [Ioi_mem_nhds hs] with r hr
        exact ih f hf r hr η
      -- the `k`-th age derivative of `f` is jointly smooth
      have hg : ContDiffOn ℝ ∞
          (fun x : ℝ × (ℝ × ℝ) => iteratedDeriv k (fun r => f r x.2) x.1) (Ioi 0 ×ˢ univ) :=
        hA.2 f hf k
      have h1 : iteratedDeriv (k + 1) (fun r => hmean c (f r) η) s =
          deriv (fun r => hmean c (fun z => iteratedDeriv k (fun r' => f r' z) r) η) s := by
        rw [iteratedDeriv_succ]
        exact hev.deriv_eq
      rw [h1]
      refine (hD c hc (fun r z => iteratedDeriv k (fun r' => f r' z) r) hg s hs η).trans ?_
      congr 1
      funext z
      rw [iteratedDeriv_succ]
  intro f hf k s hs η
  exact key k f hf s hs η

end UnforcedLeray.Short.PartIIa
