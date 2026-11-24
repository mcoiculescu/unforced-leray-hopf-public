import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer

/-!
# Leaves for the free inverses of the concrete return (source 1341-1362, 1556-1583, 2683-2689)

Source of record: `the November 2 reference manuscript` (73 pages).

Four elementary facts about the phase-periodic field space `Y_2` (source 1341-1347: `Y_r` is
`L^r((ℝ/Pℤ) × ℝ³)` with normalized phase measure, `D_r` its maximal distributional graph) used by
`Inverses/Level.lean` to upgrade the weak free solution `R_μ f` of the near layer to the graph
solution of `bg:common-body-graph` (source 1351-1362):

* `SrcLiftYr` : lifts `𝒩_v f` of body forces `f ∈ SrcG c` lie in `Y_2` (source 2683-2689);
* `YrSub` : `Y_2` is closed under differences;
* `WeakDmuSubY` : the difference of two `Y_2` weak solutions with the same right side is a
  homogeneous weak solution ("subtracting two solutions", source 1580-1583);
* `FreeResponseAECongr` : a free response is an a.e. class (the clauses of
  `IIb.IsFreeResponse` see `w` only through integrals over the phase cell).

Each is a task (`PartIII-b:C/inv/1`-`4`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- **Lifts of body forces lie in `Y_2`** (source 2683-2689, 1341-1344): for `f ∈ SrcG c`, the
physical field `𝒩_v f = √s (f_r e_r + f_z e_z)` (`velPhys`, the `q`-periodic extension `perExt`)
is `P`-periodic in the phase, measurable, and has finite phase-normalized `L²` norm,
`P = 2εc`, `R = ε⁻¹` (`R⁻¹‖𝒩_v f‖_{Y_2} = √π‖f‖_H`, `Axi.eLpNorm_liftFun`; the analogue of
`FWULiftYr` for the ungained body measure `srcMeasure c = π s^{-3/2} dς`). -/
def SrcLiftYr : Prop :=
  ∀ (c ε : ℝ), 0 < c → 0 < ε → ∀ f : SrcG c,
    UnforcedLeray.Short.IIb.IsInYr (2 * ε * c) 2 (velPhys ε⁻¹ c f)

/-- **`Y_2` is a vector space** (source 1341-1344): the difference of two fields of `Y_2` is in
`Y_2` (a.e. periodicity of both, measurability, Minkowski for the phase-normalized `L²` norm). -/
def YrSub : Prop :=
  ∀ (P : ℝ) (w w' : ℝ × Space → CVec3), 0 < P → UnforcedLeray.Short.IIb.IsInYr P 2 w →
    UnforcedLeray.Short.IIb.IsInYr P 2 w' → UnforcedLeray.Short.IIb.IsInYr P 2 (w - w')

/-- **Subtracting two weak solutions** (source 1580-1583: "Distributional uniqueness follows by
subtracting two solutions"): if `w, w' ∈ Y_2` are weakly solenoidal distributional solutions of
`D_μ w = ℙ(rhs)` with the same right side (`IsWeakDmu`), then `w - w'` is a weakly solenoidal
solution with right side `0`.  The pairings `pairF P Φ ·` of a phase test with fields of `Y_2` are
additive (integrability on the phase cell as in `WeakDmuAdd.lean`, `wda_integrable_dotL`). -/
def WeakDmuSubY : Prop :=
  ∀ (ν μ P : ℝ) (w w' : ℝ × Space → CVec3) (rhs : (ℝ × Space → CVec3) → ℂ), 0 < P →
    UnforcedLeray.Short.IIb.IsInYr P 2 w → UnforcedLeray.Short.IIb.IsInYr P 2 w' →
    IsWeakDmu ν μ P w rhs → IsWeakDmu ν μ P w' rhs → IsWeakDmu ν μ P (w - w') (fun _ => 0)

/-- **Free responses are a.e. classes** (source 1341-1347: `Y_r` and the maximal graph `D_r` consist
of a.e. classes): if `w` is a free response (`IIb.IsFreeResponse`) and `w' = w` a.e. on `ℝ × ℝ³`,
then `w'` is a free response of the same force.  The phase translation `(τ, y) ↦ (τ + P, y)`
preserves Lebesgue measure (a.e. periodicity), and every clause sees `w` only through the
iterated integrals `pairF`, `phaseLpNorm` over the phase cell, which are unchanged by an a.e.
modification (`Measure.ae_ae_of_ae_prod`). -/
def FreeResponseAECongr : Prop :=
  ∀ (ν : ℝ) (μ : ℂ) (r P : ℝ) (f w w' : ℝ × Space → CVec3),
    UnforcedLeray.Short.IIb.IsFreeResponse ν μ r P f w → w' =ᵐ[volume] w →
      UnforcedLeray.Short.IIb.IsFreeResponse ν μ r P f w'

end UnforcedLeray.Short.PartIIIb.Concrete
