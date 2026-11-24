import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_of
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# `SFCGradMeas`: measurability of the classical cell gradient

Source `the November 2 reference manuscript` 1684-1689.  On the open set `s > 0`
the slice derivative is the joint Fréchet derivative applied to `(0, dir j)`, and Mathlib's
`measurable_fderiv` applies to an arbitrary function; for `s ≤ 0` the field vanishes (the
clause added to `SmoothRep`), so the gradient is `0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem sfcGradMeas : SFCGradMeas := by
  intro c b hb i j
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hmeasU : MeasurableSet (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := hU.measurableSet
  have hF : Measurable fun p : Chart => fderiv ℝ (fun q : Chart => b q i) p (0, B0579.dir j) :=
    (measurable_fderiv_apply_const ℝ (fun q : Chart => b q i) _)
  have hz : ∀ p : Chart, p.1 ≤ 0 → cellGrad b p i j = 0 := by
    intro p hp
    have : (fun x : ℝ × ℝ => b (p.1, x) i) = fun _ => 0 := by
      funext x; simp [hb.2.2.2.2 (p.1, x) hp]
    unfold cellGrad
    rw [this]; simp
  have heq : ∀ p ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)),
      cellGrad b p i j = fderiv ℝ (fun q : Chart => b q i) p (0, B0579.dir j) := by
    intro p hp
    have hd : DifferentiableAt ℝ (fun q : Chart => b q i) p :=
      ((hb.2.1 i).differentiableOn (by simp)).differentiableAt (hU.mem_nhds hp)
    unfold cellGrad
    have hc : HasFDerivAt (fun x : ℝ × ℝ => b (p.1, x) i)
        ((fderiv ℝ (fun q : Chart => b q i) p).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) p.2 := by
      have h1 : HasFDerivAt (fun q : Chart => b q i) (fderiv ℝ (fun q : Chart => b q i) p) (p.1, p.2) :=
        hd.hasFDerivAt
      have h2 : HasFDerivAt (fun x : ℝ × ℝ => ((p.1, x) : Chart)) (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) p.2 :=
        hasFDerivAt_prodMk_right p.1 p.2
      exact h1.comp p.2 h2
    rw [hc.fderiv]; rfl
  have : (fun p : Chart => cellGrad b p i j) =
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))).piecewise
        (fun p : Chart => fderiv ℝ (fun q : Chart => b q i) p (0, B0579.dir j)) (fun _ => 0) := by
    funext p
    by_cases hp : p ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))
    · rw [piecewise_eq_of_mem _ _ _ hp]; exact heq p hp
    · rw [piecewise_eq_of_notMem _ _ _ hp]
      apply hz
      simpa using hp
  rw [this]
  exact Measurable.piecewise hmeasU hF measurable_const

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
