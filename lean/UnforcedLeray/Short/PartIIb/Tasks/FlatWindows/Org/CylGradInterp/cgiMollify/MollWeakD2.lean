import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylGradInterp.cgiMollify.MollDeriv

/-!
# `PartII-b:T13/1/5/5/6` leaf: the weak identity for `D2` through the convolution

Source: `the November 2 reference manuscript` lines 1932-1935.
`MollDeriv` (leaf `/5`) is used twice; the test `y ↦ κ(x - y)` is a space-time test, and the
chain rule for `y ↦ x - y` gives two sign flips that cancel.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

/-- The `j`-th partial derivative of a smooth kernel is smooth. -/
theorem mwd2_cpd_contDiff (j : Fin 3) (κ : Coord → ℝ) (hκ : ContDiff ℝ ∞ κ) :
    ContDiff ℝ ∞ (cpd j κ) := by
  unfold cpd
  exact (hκ.fderiv_right (by simp)).clm_apply contDiff_const

/-- The `j`-th partial derivative of a compactly supported kernel is compactly supported. -/
theorem mwd2_cpd_hasCompact (j : Fin 3) (κ : Coord → ℝ) (hκc : HasCompactSupport κ) :
    HasCompactSupport (cpd j κ) := by
  unfold cpd
  exact HasCompactSupport.fderiv_apply (𝕜 := ℝ) hκc (cdir j)

/-- The derivative of a smooth compactly supported kernel is again one. -/
theorem mwd2_isKer_cpd (j : Fin 3) (κ : Coord → ℝ) (hκ : IsKer κ) : IsKer (cpd j κ) := by
  obtain ⟨hκs, hκc⟩ := hκ
  unfold IsKer
  exact ⟨mwd2_cpd_contDiff j κ hκs, mwd2_cpd_hasCompact j κ hκc⟩

/-- Chain rule for the reflection `y ↦ κ(x - y)`: one sign flip. -/
theorem mwd2_cpd_reflect (j : Fin 3) (κ : Coord → ℝ) (hκ : Differentiable ℝ κ) (x y : Coord) :
    cpd j (fun z => κ (x - z)) y = -(cpd j κ (x - y)) := by
  unfold cpd
  have h1 : HasFDerivAt (fun z : Coord => x - z) (-ContinuousLinearMap.id ℝ Coord) y :=
    (hasFDerivAt_id y).const_sub x
  have h2 : HasFDerivAt (fun z => κ (x - z))
      ((fderiv ℝ κ (x - y)).comp (-ContinuousLinearMap.id ℝ Coord)) y :=
    (hκ (x - y)).hasFDerivAt.comp y h1
  rw [h2.fderiv]
  simp

/-- Pointwise derivative of a negated function. -/
theorem mwd2_cpd_neg (j : Fin 3) (g : Coord → ℝ) (y : Coord) :
    cpd j (fun z => -g z) y = -(cpd j g y) := by
  unfold cpd
  rw [fderiv_fun_neg]
  simp

/-- The test function `y ↦ κ(x - y)` is a space-time test. -/
theorem mwd2_test (κ : Coord → ℝ) (hκ : IsKer κ) (x : Coord) :
    IsSTTestCoord (fun z => κ (x - z)) := by
  obtain ⟨hκs, hκc⟩ := hκ
  refine ⟨?_, ?_⟩
  · exact hκs.comp (contDiff_const.sub contDiff_id)
  · have := hκc.comp_homeomorph (Homeomorph.subLeft x)
    convert this using 1
    funext z
    simp

/-- Double derivative of the reflected test: two sign flips cancel. -/
theorem mwd2_double_reflect (k l : Fin 3) (κ : Coord → ℝ) (hκ : ContDiff ℝ ∞ κ) (x z : Coord) :
    cpd k (fun y => cpd l (fun w => κ (x - w)) y) z = cpd k (cpd l κ) (x - z) := by
  have hl : Differentiable ℝ (cpd l κ) := (mwd2_cpd_contDiff l κ hκ).differentiable (by simp)
  have hG : Differentiable ℝ (fun w => -(cpd l κ w)) := fun w => (hl w).neg
  have houter : (fun y => cpd l (fun w => κ (x - w)) y) =
      (fun y => (fun w => -(cpd l κ w)) (x - y)) := by
    funext y
    exact mwd2_cpd_reflect l κ (hκ.differentiable (by simp)) x y
  rw [houter, mwd2_cpd_reflect k (fun w => -(cpd l κ w)) hG x z,
    mwd2_cpd_neg k (cpd l κ) (x - z), neg_neg]

/-- **Weak identity through the convolution** (SP 1932-1935). -/
theorem mollWeakD2_proof : UnforcedLeray.Short.IIb.MollWeakD2 := by
  intro κ u D2 hκ hu _hD2 hw k l
  have hDκ : MollDeriv := mollDeriv_proof
  rw [hDκ κ u hκ hu l.succ, hDκ (cpd l.succ κ) u (mwd2_isKer_cpd l.succ κ hκ) hu k.succ]
  funext x
  have hκs : ContDiff ℝ ∞ κ := by
    obtain ⟨h, _⟩ := hκ
    exact h
  have key := hw k l (fun z => κ (x - z)) (mwd2_test κ hκ x)
  have e1 : ∀ z, cpd k.succ (fun y => cpd l.succ (fun w => κ (x - w)) y) z
      = cpd k.succ (cpd l.succ κ) (x - z) := fun z => mwd2_double_reflect k.succ l.succ κ hκs x z
  unfold convK
  have hc : (∫ y, u y * ((cpd k.succ (cpd l.succ κ) (x - y) : ℝ) : ℂ)) =
      ∫ z, u z * ((cpd k.succ (fun y => cpd l.succ (fun w => κ (x - w)) y) z : ℝ) : ℂ) := by
    congr 1
    funext z
    rw [e1 z]
  rw [hc]
  exact key

end UnforcedLeray.Short.IIb
