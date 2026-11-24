import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_2_1.Defs
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_2_1.T3
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_1_1.T11

/-!


Source `the November 2 reference manuscript` lines 5063-5071, 5076-5079, 4979.

Each lattice summand is `Σ_{a,b} A^y_{mi a, mi b}(s) · psiGauss a b` on `UChart` (`psiSummandExpand`,
task 3). The entries of `A^y` are `C⁴` on `(0,∞)` (`ayEntrySmooth`, Hp task 11), composing with the
first projection gives `C⁴` on `UChart`; the Gaussian factors `psiGauss` are `C⁴` on `UChart` for
`ν > 0` (`psiGaussSmooth_pos` below, copy of `hpGaussSmooth_pos`). Finite sums and products preserve
`ContDiffOn`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- `psiGauss` is `C⁴` on `UChart` for `ν > 0` (the age `a = 1 + νs` is nonzero on `s > 0`). -/
theorem psiGaussSmooth_pos (ν : ℝ) (hν : 0 < ν) (j : ℤ) (a b : Fin 2) :
    ContDiffOn ℝ 4 (psiSummandGauss ν j a b) UChart := by
  have hA : ∀ p ∈ UChart, 1 + ν * p.1 ≠ 0 := by
    intro p hp
    have : 0 < p.1 := hp.1
    positivity
  unfold psiSummandGauss
  fin_cases a <;> fin_cases b <;>
  · simp [comp2, xj, sq2, ageA, cOf]
    fun_prop (disch := (intro x hx; have h := hA x hx; simp [h]))

theorem psiSummandSmooth (as : ℝ) (χf : ℝ → ℝ) : PsiSummandSmooth as χf := by
  intro hχ ν hν A hA j
  have hG : ContDiffOn ℝ 4
      (fun p : Chart => ∑ a : Fin 2, ∑ b : Fin 2,
          Ay ν χf A p.1 (mi a) (mi b) * psiSummandGauss ν j a b p) UChart := by
    refine ContDiffOn.sum (fun a _ => ?_)
    refine ContDiffOn.sum (fun b _ => ?_)
    have hent : ContDiffOn ℝ 4 (fun s => Ay ν χf A s (mi a) (mi b)) (Ioi 0) :=
      ayEntrySmooth as χf hχ ν hν A hA (mi a) (mi b)
    have hentP : ContDiffOn ℝ 4 (fun p : Chart => Ay ν χf A p.1 (mi a) (mi b)) UChart :=
      hent.comp contDiff_fst.contDiffOn (fun p hp => hp.1)
    exact hentP.mul (psiGaussSmooth_pos ν hν j a b)
  exact hG.congr (fun p hp => psiSummandExpand ν hν χf A j p hp)

end UnforcedLeray.Short.PartIIIb.Concrete
