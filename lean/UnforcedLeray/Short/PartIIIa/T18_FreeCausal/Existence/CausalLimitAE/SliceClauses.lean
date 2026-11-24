import UnforcedLeray.Short.PartIIIa.Sub.T18_2_1
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.CausalLimitAE.SliceClauses.Ages

/-!
# Part III-a, task `PartIII-a:T18/2/1`: `CausalSliceClauses`

Proves `UnforcedLeray.Short.IIIa.CausalSliceClauses` (statement in `Sub/T18_2_1.lean`).
Source of record: `the November 2 reference manuscript`, lines 3427-3440
("divFree/weakGrad for the a.e. s where the slices converge in L2(cell)").

Proof: the energy clauses give, for almost every `s > 0`, finite `cell`-energy of every `bn n`
and `Gn n` (`sc_good_ages`, Tonelli). At such an `s` with the slices converging
(`sc_at_age`), `divFree` and `weakGrad` pass to the limit by the `L²` pairing
(`sc_tendsto_integral_mul`). Helpers live in `SliceClauses/`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem causalSliceClauses : UnforcedLeray.Short.IIIa.CausalSliceClauses := by
  intro c hc bn Gn b G hbnM hbM hGnM hGM hE hD hW hconv
  have hφm : ∀ n, Measurable fun p : ℝ × (ℝ × ℝ) =>
      ENNReal.ofReal (vnorm2 (bn n p) ^ 2 + tnorm2 (Gn n p) ^ 2) := fun n =>
    ENNReal.measurable_ofReal.comp
      (((causalLin_measurable_vnorm2 (hbnM n)).pow_const 2).add
        ((causalLin_measurable_tnorm2 (hGnM n)).pow_const 2))
  filter_upwards [sc_good_ages c hφm hE, hconv, ae_restrict_mem measurableSet_Ioi]
    with s hgood hcs hs
  have hs0 : 0 < s := hs
  exact sc_at_age (c := c) (A := fun n x => bn n (s, x)) (B := fun x => b (s, x))
    (GA := fun n x => Gn n (s, x)) (GB := fun x => G (s, x))
    (fun n i => (hbnM n i).comp (measurable_prodMk_left (x := s)))
    (fun i => (hbM i).comp (measurable_prodMk_left (x := s)))
    (fun n i j => (hGnM n i j).comp (measurable_prodMk_left (x := s)))
    (fun i j => (hGM i j).comp (measurable_prodMk_left (x := s)))
    hgood (fun n ψ hψ => hD n s hs0 ψ hψ) (fun n i j => hW n s hs0 i j) hcs.1 hcs.2

end UnforcedLeray.Short.IIIa
