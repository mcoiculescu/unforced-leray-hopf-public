import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_9_5_1

/-!
# Proof of `SCPsiF_smooth` (source 4178-4186, 4917-4937)

For `t > 1`, `y ↦ t Z_z(t y₀, t y₁, y₂)` is `C^7` on `psiU ν`: the linear map
`y ↦ (t y₀, t y₁, y₂)` sends `psiU ν` into `{eucSq > 11ν/12}` (since `eucSq` increases),
where `Z` is `C^7`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Metric UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem scPsiF_smooth : SCPsiF_smooth := by
  unfold SCPsiF_smooth
  intro ν B Z hν hB hZ t ht
  have hZc : ContDiffOn ℝ 7 Z {w : Vec3 | ν * (11 / 12) < eucSq w} := hZ.1
  have hLc : ContDiff ℝ 7 (fun y : Vec3 => (![t * y 0, t * y 1, y 2] : Vec3)) := by
    rw [contDiff_pi]
    intro i
    fin_cases i <;> simp <;> fun_prop
  have hmap : MapsTo (fun y : Vec3 => (![t * y 0, t * y 1, y 2] : Vec3)) (psiU ν)
      {w : Vec3 | ν * (11 / 12) < eucSq w} := by
    intro y hy
    have h1 : ν * (11 / 12) < eucSq y := hy.1
    show ν * (11 / 12) < eucSq ![t * y 0, t * y 1, y 2]
    have ht2 : 1 ≤ t ^ 2 := by nlinarith
    have hE : eucSq (![t * y 0, t * y 1, y 2] : Vec3)
        = t ^ 2 * (y 0) ^ 2 + t ^ 2 * (y 1) ^ 2 + (y 2) ^ 2 := by
      simp [eucSq, Fin.sum_univ_three]
      ring
    have hE' : eucSq y = (y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2 := by
      simp [eucSq, Fin.sum_univ_three]
    rw [hE']at h1
    rw [hE]
    nlinarith [mul_nonneg (sub_nonneg.2 ht2) (sq_nonneg (y 0)),
      mul_nonneg (sub_nonneg.2 ht2) (sq_nonneg (y 1)), sq_nonneg (y 0), sq_nonneg (y 1)]
  have hc : ContDiffOn ℝ 7 (Z ∘ fun y : Vec3 => (![t * y 0, t * y 1, y 2] : Vec3)) (psiU ν) :=
    hZc.comp hLc.contDiffOn hmap
  have h2 : ContDiffOn ℝ 7 (fun y : Vec3 => Z ![t * y 0, t * y 1, y 2] 2) (psiU ν) :=
    (contDiff_apply ℝ ℝ (2 : Fin 3)).comp_contDiffOn hc
  unfold psiF
  exact contDiffOn_const.mul h2

end UnforcedLeray.Short.PartIIIb.Concrete
