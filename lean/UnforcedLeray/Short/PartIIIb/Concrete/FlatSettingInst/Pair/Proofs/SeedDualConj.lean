import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.Proofs.AngularSectorConj
import UnforcedLeray.Short.PartI.StatementsSeed
import UnforcedLeray.Short.PartIIIa.Clock.Frame
import UnforcedLeray.Lib.PlanarSectors.NUE.PolarDefs
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.Algebra.Support

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair

/-- **The planar dual kernels are conjugate** (source 601-610, 2896-2899). -/
theorem seedDualConj :
    UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.SeedDualConj := by
  intro κ hκ
  obtain ⟨lam, h, hh, ℓ, _, he0, he1, hlam⟩ := hκ
  -- the identity of the two functionals on smooth compactly supported planar tests
  have hkey : ∀ F : ℂ → ℂ, ContDiff ℝ ∞ F → HasCompactSupport F →
      ∫ y, κ.lamP 1 y * F (UnforcedLeray.Short.IIIa.planeToC y) =
        ∫ y, conj (κ.lamP 0 y) * F (UnforcedLeray.Short.IIIa.planeToC y) := by
    intro F hF hFc
    have hG : ContDiff ℝ ∞ (fun z : ℂ => conj (F z)) :=
      Complex.conjCLE.contDiff.comp hF
    have hGc : HasCompactSupport (fun z : ℂ => conj (F z)) :=
      hFc.comp_left (by simp)
    have hA := (hlam _ hG hGc).1
    have hfun : (fun r => conj (UnforcedLeray.Planar.NUE.Polar.angularSector F (-2) r)) =
        UnforcedLeray.Planar.NUE.Polar.angularSector (fun z => conj (F z)) 2 :=
      funext fun r =>
        UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.angularSectorConj F r
    rw [(hlam F hF hFc).2, hfun, ← hA, ← integral_conj]
    congr 1
    funext y
    simp [map_mul]
  have hDc : Continuous (fun y : ℝ × ℝ => κ.lamP 1 y - conj (κ.lamP 0 y)) :=
    (κ.lamP_cont 1).sub (Complex.continuous_conj.comp (κ.lamP_cont 0))
  -- the integrated identity against real smooth compactly supported test functions
  have hint : ∀ g : ℝ × ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      ∫ x, g x • (κ.lamP 1 x - conj (κ.lamP 0 x)) = 0 := by
    intro g hg hgc
    let F : ℂ → ℂ := fun z => ((g (Complex.equivRealProdCLM z) : ℝ) : ℂ)
    have hFp : ∀ y : ℝ × ℝ, F (UnforcedLeray.Short.IIIa.planeToC y) = ((g y : ℝ) : ℂ) := by
      intro y
      simp [F, UnforcedLeray.Short.IIIa.planeToC]
    have hFc : ContDiff ℝ ∞ F :=
      Complex.ofRealCLM.contDiff.comp (hg.comp Complex.equivRealProdCLM.contDiff)
    have hgc' : HasCompactSupport (fun z : ℂ => g (Complex.equivRealProdCLM z)) :=
      hgc.comp_homeomorph Complex.equivRealProdCLM.toHomeomorph
    have hcoe : ∀ (X : Type) [TopologicalSpace X] (φ : X → ℝ), HasCompactSupport φ →
        HasCompactSupport (fun z => ((φ z : ℝ) : ℂ)) := fun X _ φ hφ =>
      hφ.comp_left (g := Complex.ofReal) Complex.ofReal_zero
    have hFs : HasCompactSupport F := hcoe ℂ (fun z => g (Complex.equivRealProdCLM z)) hgc'
    have hgcC : HasCompactSupport (fun y : ℝ × ℝ => ((g y : ℝ) : ℂ)) :=
      hcoe (ℝ × ℝ) g hgc
    have hcs1 : HasCompactSupport (fun y : ℝ × ℝ => κ.lamP 1 y * ((g y : ℝ) : ℂ)) :=
      HasCompactSupport.mul_left (f := fun y => κ.lamP 1 y) hgcC
    have hcs0 : HasCompactSupport (fun y : ℝ × ℝ => conj (κ.lamP 0 y) * ((g y : ℝ) : ℂ)) :=
      HasCompactSupport.mul_left (f := fun y => conj (κ.lamP 0 y)) hgcC
    have hcont1 : Continuous (fun y : ℝ × ℝ => κ.lamP 1 y * ((g y : ℝ) : ℂ)) :=
      (κ.lamP_cont 1).mul (Complex.continuous_ofReal.comp hg.continuous)
    have hcont0 : Continuous (fun y : ℝ × ℝ => conj (κ.lamP 0 y) * ((g y : ℝ) : ℂ)) :=
      (Complex.continuous_conj.comp (κ.lamP_cont 0)).mul (Complex.continuous_ofReal.comp hg.continuous)
    have hint1 : Integrable (fun y : ℝ × ℝ => κ.lamP 1 y * ((g y : ℝ) : ℂ)) volume :=
      hcont1.integrable_of_hasCompactSupport hcs1
    have hint0 : Integrable (fun y : ℝ × ℝ => conj (κ.lamP 0 y) * ((g y : ℝ) : ℂ)) volume :=
      hcont0.integrable_of_hasCompactSupport hcs0
    have hsmul : (fun x : ℝ × ℝ => g x • (κ.lamP 1 x - conj (κ.lamP 0 x))) =
        fun x => κ.lamP 1 x * ((g x : ℝ) : ℂ) - conj (κ.lamP 0 x) * ((g x : ℝ) : ℂ) := by
      funext x
      simp only [Complex.real_smul]
      ring
    have hk := hkey F hFc hFs
    simp only [hFp] at hk
    rw [hsmul, integral_sub hint1 hint0]
    exact sub_eq_zero.mpr hk
  have hae : ∀ᵐ x ∂(volume : Measure (ℝ × ℝ)), κ.lamP 1 x - conj (κ.lamP 0 x) = 0 :=
    ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (f := fun x => κ.lamP 1 x - conj (κ.lamP 0 x))
      hDc.locallyIntegrable (fun g hg hgc => hint g hg hgc)
  have hfin : (fun y : ℝ × ℝ => κ.lamP 1 y - conj (κ.lamP 0 y)) = fun _ => 0 :=
    (Continuous.ae_eq_iff_eq volume hDc continuous_const).mp hae
  intro y
  exact sub_eq_zero.mp (congrFun hfin y)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair
