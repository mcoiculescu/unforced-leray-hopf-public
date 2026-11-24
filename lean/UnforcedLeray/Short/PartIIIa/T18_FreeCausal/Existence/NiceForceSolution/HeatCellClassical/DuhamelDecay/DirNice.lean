import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T18_2_4_1_4

/-!
# Part III-a, task `PartIII-a:T18/2/4/1/4/4`: the x-directional derivative of a nice source is nice

Target: `duhDecDirNice : DuhDecDirNice` (`Sub/PartIIIa_T18_2_4_1_4.lean`, leaf 4 of the Duhamel
decay; SP 3427-3440 of `the November 2 reference manuscript`).

For `NiceScalar c h` and a direction `e`, the function `q ↦ duhDecDirDeriv e h q` equals
`q ↦ fderiv ℝ h q (0, e)` (slice derivative = ambient derivative in the `(0, e)` direction).
Smoothness follows from `fderiv` of a smooth map; periodicity from translation invariance of the
slice derivative; vanishing for `s < a` or `s > B` because the slice is identically zero; and
vanishing for `|η| > R` because the slice vanishes on the open set `{|y.2| > R}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Slice derivative in direction `e` equals the ambient derivative in direction `(0, e)`. -/
theorem dn_slice {h : ℝ × (ℝ × ℝ) → ℂ} (hh : Differentiable ℝ h) (s : ℝ) (x e : ℝ × ℝ) :
    fderiv ℝ (fun y => h (s, y)) x e = fderiv ℝ h (s, x) (0, e) := by
  have hd : HasFDerivAt (fun y : ℝ × ℝ => h (s, y))
      ((fderiv ℝ h (s, x)).comp
        ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ)))) x :=
    (hh (s, x)).hasFDerivAt.comp x ((hasFDerivAt_const s x).prodMk (hasFDerivAt_id x))
  rw [hd.fderiv]
  simp

theorem dn_dd {h : ℝ × (ℝ × ℝ) → ℂ} (hh : Differentiable ℝ h) (e : ℝ × ℝ) (q : ℝ × (ℝ × ℝ)) :
    duhDecDirDeriv e h q = fderiv ℝ h q (0, e) := by
  obtain ⟨s, x⟩ := q
  exact dn_slice hh s x e

theorem duhDecDirNice : UnforcedLeray.Short.IIIa.DuhDecDirNice := by
  intro c e h hn
  unfold NiceScalar at hn ⊢
  obtain ⟨hC, hper, a, B, R, ha, hvan⟩ := hn
  have hdiff : Differentiable ℝ h := hC.differentiable (by simp)
  have hfun : duhDecDirDeriv e h = fun p => fderiv ℝ h p (0, e) :=
    funext fun q => dn_dd hdiff e q
  have hsm : ContDiff ℝ ∞ (duhDecDirDeriv e h) := by
    rw [hfun]
    have h1 : ContDiff ℝ ∞ (fderiv ℝ h) := (contDiff_infty_iff_fderiv.1 hC).2
    exact h1.clm_apply contDiff_const
  have hper' : ∀ s x, duhDecDirDeriv e h (s, (x.1 + c, x.2)) = duhDecDirDeriv e h (s, x) := by
    intro s x
    have hG : ∀ y : ℝ × ℝ, h (s, y + (c, 0)) = h (s, y) := fun y => by
      rw [show y + ((c : ℝ), (0 : ℝ)) = (y.1 + c, y.2) by ext <;> simp]
      exact hper s y
    have e1 : (fun y : ℝ × ℝ => h (s, y + (c, 0))) = fun y => h (s, y) := funext hG
    have key : fderiv ℝ (fun y : ℝ × ℝ => h (s, y + (c, 0))) x
        = fderiv ℝ (fun y : ℝ × ℝ => h (s, y)) (x + (c, 0)) :=
      fderiv_comp_add_right (f := fun y : ℝ × ℝ => h (s, y)) (c, 0)
    rw [e1] at key
    have hx : x + (c, 0) = (x.1 + c, x.2) := by ext <;> simp
    show fderiv ℝ (fun y => h (s, y)) (x.1 + c, x.2) e = fderiv ℝ (fun y => h (s, y)) x e
    rw [← hx, ← key]
  refine ⟨hsm, hper', a, B, R, ha, ?_⟩
  intro s x hsx
  show fderiv ℝ (fun y => h (s, y)) x e = 0
  rcases hsx with hs | hs | hR
  · have hz : (fun y : ℝ × ℝ => h (s, y)) = fun _ => 0 :=
      funext fun y => hvan s y (Or.inl hs)
    rw [hz]
    simp
  · have hz : (fun y : ℝ × ℝ => h (s, y)) = fun _ => 0 :=
      funext fun y => hvan s y (Or.inr (Or.inl hs))
    rw [hz]
    simp
  · have hopen : IsOpen {y : ℝ × ℝ | R < |y.2|} :=
      isOpen_lt continuous_const (continuous_abs.comp continuous_snd)
    have hev : ∀ᶠ y in nhds x, h (s, y) = 0 := by
      filter_upwards [hopen.mem_nhds hR] with y hy
      exact hvan s y (Or.inr (Or.inr hy))
    have hev' : (fun y : ℝ × ℝ => h (s, y)) =ᶠ[nhds x] (fun _ => (0 : ℂ)) := hev
    rw [hev'.fderiv_eq]
    simp

end UnforcedLeray.Short.IIIa
