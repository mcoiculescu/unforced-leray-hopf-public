import UnforcedLeray.Short.PartIIa.Sub.R02_6

/-!
# Part II-a, task `PartII-a:R02/MeanStress/HmeanMixedDeriv`: mixed derivatives commute with the
cell average

Source of record: `the November 2 reference manuscript`, lines 397-404 (`sct:mean`).
The statement `HmeanMixedDeriv` is defined in `Short/PartII-a/Sub/R02_6.lean`; the hypotheses are
`AgeDerivSmooth` (`Short/PartII-a/Sub/R02_2.lean`), `HmeanAgeIter` and `HmeanEtaDeriv`
(`Short/PartII-a/Sub/R02_6.lean`).

Route. Fix `c > 0`, `f` jointly smooth, `s > 0`, `η`.
* `HmeanAgeIter` rewrites the inner age derivative of the cell average as the cell average of
  `z ↦ ∂_s^k f(s, z)`; funext in the variable `e` turns the outer `∂_η^a` into a derivative of a
  single cell average.
* `AgeDerivSmooth` shows `h z := ∂_s^k f(s, z)` is `C^∞` on the plane: compose the jointly smooth
  map `(s', z) ↦ ∂_{s'}^k f(s', z)` with `z ↦ (s, z)`, which maps `univ` into `Ioi 0 ×ˢ univ`.
* `HmeanEtaDeriv` applied to `h` gives the `η`-derivative of the cell average of `h`, which is the
  right-hand side since `h (z.1, e) = ∂_s^k f(s, (z.1, e))` definitionally.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.Short.PartI (hmean)

/-- **Mixed derivatives commute with the cell average** (source lines 397-404): from
`AgeDerivSmooth`, `HmeanAgeIter` and `HmeanEtaDeriv`, `HmeanMixedDeriv` holds. -/
theorem hmeanMixedDeriv_of (hA : UnforcedLeray.Short.PartIIa.AgeDerivSmooth)
    (hAge : UnforcedLeray.Short.PartIIa.HmeanAgeIter)
    (hEta : UnforcedLeray.Short.PartIIa.HmeanEtaDeriv) :
    UnforcedLeray.Short.PartIIa.HmeanMixedDeriv := by
  unfold UnforcedLeray.Short.PartIIa.HmeanMixedDeriv
  intro c hc f hf a k s η hs
  -- the age-`k` derivative of the cell average is the cell average of the age-`k` derivative
  have hfun : (fun e => iteratedDeriv k (fun r => hmean c (f r) e) s) =
      (fun e => hmean c (fun z => iteratedDeriv k (fun r => f r z) s) e) := by
    funext e
    exact hAge c hc f hf k s hs e
  -- the plane function `z ↦ ∂_s^k f(s, z)` is `C^∞`
  have hh : ContDiff ℝ ∞ (fun z : ℝ × ℝ => iteratedDeriv k (fun r => f r z) s) := by
    have hg : ContDiffOn ℝ ∞
        (fun x : ℝ × (ℝ × ℝ) => iteratedDeriv k (fun r => f r x.2) x.1) (Ioi 0 ×ˢ univ) :=
      hA.2 f hf k
    have hmap : ∀ z : ℝ × ℝ, ((s, z) : ℝ × (ℝ × ℝ)) ∈ Ioi 0 ×ˢ (univ : Set (ℝ × ℝ)) := by
      intro z
      exact Set.mk_mem_prod (Set.mem_Ioi.mpr hs) (Set.mem_univ z)
    have hcomp : ContDiff ℝ ∞ (fun z : ℝ × ℝ => ((s, z) : ℝ × (ℝ × ℝ))) := by
      fun_prop
    exact hg.comp_contDiff hcomp hmap
  rw [hfun]
  exact hEta c hc (fun z => iteratedDeriv k (fun r => f r z) s) hh a η

end UnforcedLeray.Short.PartIIa
