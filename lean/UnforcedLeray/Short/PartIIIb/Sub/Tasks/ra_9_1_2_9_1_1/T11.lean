import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AyDiffAt

/-!


Source `the November 2 reference manuscript` lines 4953-4958, 5063-5071.

`A^y = χ_f A` with `χ_f(s) = χ̂_f(νs)` (`C^∞`) and `A ∈ 𝒜` (`C^6` on `(0,∞)`), so each matrix
entry of `A^y` is a product of a `C^∞` function and a `C^6` function on the open set `(0,∞)`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem ayEntrySmooth (as : ℝ) (χf : ℝ → ℝ) : IsSourceCutoffC χf → ∀ ν : ℝ, 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A → ∀ i j : Fin 3, ContDiffOn ℝ 4 (fun s => Ay ν χf A s i j) (Set.Ioi 0) := by
  intro hχ ν _hν A hA i j
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : ℝ => χf (ν * s)) :=
    hχ.smooth.comp (contDiff_const.mul contDiff_id)
  have hcO : ContDiffOn ℝ 4 (fun s : ℝ => χf (ν * s)) (Ioi 0) :=
    (hc.contDiffOn).of_le (by norm_num)
  have hproj : ContDiff ℝ 4 (fun f : Mat3 => f i j) := by
    fun_prop
  have hAi : ContDiffOn ℝ 4 (fun s => A s i j) (Ioi 0) :=
    (hproj.comp_contDiffOn (hA.smooth.of_le (by norm_num))).of_le (by norm_num)
  have hfun : (fun s => Ay ν χf A s i j) = fun s => χf (ν * s) * A s i j := by
    funext s
    simp [Ay]
  rw [hfun]
  exact hcO.mul hAi

end UnforcedLeray.Short.PartIIIb.Concrete
