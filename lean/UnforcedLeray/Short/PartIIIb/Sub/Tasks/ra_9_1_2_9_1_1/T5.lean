import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_1_1.Defs
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_1_1.T6
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_1_1.T10
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_1_1.T11

/-!


Source `the November 2 reference manuscript` lines 5063-5071, 5076-5079, 4963-4985.

Each lattice summand is `Σ_{a,b} A^y_{mi a, mi b}(s) · hpGaussM a b` (`HpSummandExpand`, task 6).
The entries of `A^y` are `C⁴` on `(0,∞)` (task 11) and composing with the first projection gives
`C⁴` on `UChart`; the Gaussian factors `hpGaussM` are `C⁴` on `UChart` (task 10). Finite sums and
smul preserve `ContDiffOn`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem hpSummandSmooth (as : ℝ) (χf : ℝ → ℝ) : HpSummandSmooth as χf := by
  intro hχ ν hν A hA j
  have hexp : hpSummandM ν χf A j
      = fun p => ∑ a : Fin 2, ∑ b : Fin 2,
          (Ay ν χf A p.1 (mi a) (mi b)) • hpGaussM ν j a b p :=
    hpSummandExpand ν χf A j
  rw [hexp]
  refine ContDiffOn.sum (fun a _ => ?_)
  refine ContDiffOn.sum (fun b _ => ?_)
  have hent : ContDiffOn ℝ 4 (fun s => Ay ν χf A s (mi a) (mi b)) (Ioi 0) :=
    ayEntrySmooth as χf hχ ν hν A hA (mi a) (mi b)
  have hentP : ContDiffOn ℝ 4 (fun p : Chart => Ay ν χf A p.1 (mi a) (mi b)) UChart :=
    hent.comp contDiff_fst.contDiffOn (fun p hp => hp.1)
  exact hentP.smul (hpGaussSmooth_pos ν hν j a b)

end UnforcedLeray.Short.PartIIIb.Concrete
