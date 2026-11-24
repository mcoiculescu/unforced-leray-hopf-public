import UnforcedLeray.Short.PartI.Sub.PartI_T04_10_1_2_1
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2.VelocityJetL2.EnergyIneq.AdvCommutator
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2.VelocityJetL2.EnergyIneq.ConsAppend

/-!
# Part I, `PartI:T04/10/1/2/1/12`: `CommWord2Expand`

Source of record: `the November 2 reference manuscript`, lines 285-288
(`[∂², v·∇]ω = ∂²v·∇ω + 2∂v·∇∂ω`).  The second word derivative of `scalarAdv b h` is expanded by
the Leibniz rule over the four splittings of `[a, a']` (`wacSplits`, `wac_gen`); the splitting with
all letters on `h` is `b_k ∂_{[a,a',k]} h = b_k ∂_{k::[a,a']} h` (`DerivWordConsAppend`), which
cancels against `scalarAdv b (∂_{[a,a']} h)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-- The four splittings of a two-letter word. -/
theorem cwe_splits_two (a a' : Bool) :
    wacSplits [a, a'] = [([a, a'], []), ([a], [a']), ([a'], [a]), ([], [a, a'])] := by
  simp [wacSplits]

/-- **Target** `commWord2Expand_proof`: the second-order Leibniz expansion of `scalarAdv`
(`CommWord2Expand`, `Sub/PartI_T04_10_1_2_1.lean`). -/
theorem commWord2Expand_proof : CommWord2Expand := by
  intro b h hb hh a a' z
  have hb0 : ContDiff ℝ ∞ (fun x => b x 0) := wac_comp_cd hb 0
  have hb1 : ContDiff ℝ ∞ (fun x => b x 1) := wac_comp_cd hb 1
  have hCA : DerivWordConsAppend := derivWordConsAppend_proof
  have hsp := cwe_splits_two a a'
  have hX : ContDiff ℝ ∞ (fun x => b x 0 * B0151.derivWord [true] h x) :=
    hb0.mul (B0151.contDiff_derivWord hh [true])
  have hY : ContDiff ℝ ∞ (fun x => b x 1 * B0151.derivWord [false] h x) :=
    hb1.mul (B0151.contDiff_derivWord hh [false])
  have hD : B0151.derivWord [a, a'] (scalarAdv b h) z =
      B0151.derivWord [a, a'] (fun x => b x 0 * B0151.derivWord [true] h x) z +
      B0151.derivWord [a, a'] (fun x => b x 1 * B0151.derivWord [false] h x) z := by
    have hS : scalarAdv b h = fun x => b x 0 * B0151.derivWord [true] h x +
        b x 1 * B0151.derivWord [false] h x := by
      funext x
      rfl
    rw [hS]
    exact congrFun (ForcingIBP.derivWord_add_smooth [a, a'] _ _ hX hY) z
  have G0 : B0151.derivWord [a, a'] (fun x => b x 0 * B0151.derivWord [true] h x) z =
      ((wacSplits [a, a']).map (fun p =>
        B0151.derivWord p.1 (fun x => b x 0) z * B0151.derivWord (p.2 ++ [true]) h z)).sum :=
    wac_gen [a, a'] (fun x => b x 0) h hb0 hh true z
  have G1 : B0151.derivWord [a, a'] (fun x => b x 1 * B0151.derivWord [false] h x) z =
      ((wacSplits [a, a']).map (fun p =>
        B0151.derivWord p.1 (fun x => b x 1) z * B0151.derivWord (p.2 ++ [false]) h z)).sum :=
    wac_gen [a, a'] (fun x => b x 1) h hb1 hh false z
  rw [hsp] at G0 G1
  have e0 : B0151.derivWord (true :: [a, a']) h z = B0151.derivWord ([a, a'] ++ [true]) h z :=
    congrFun (hCA h hh true [a, a']) z
  have e1 : B0151.derivWord (false :: [a, a']) h z = B0151.derivWord ([a, a'] ++ [false]) h z :=
    congrFun (hCA h hh false [a, a']) z
  have hT : scalarAdv b (B0151.derivWord [a, a'] h) z =
      b z 0 * B0151.derivWord (true :: [a, a']) h z +
        b z 1 * B0151.derivWord (false :: [a, a']) h z := rfl
  have hnil : ∀ (f : Plane → ℝ) (w : Plane), B0151.derivWord [] f w = f w := fun _ _ => rfl
  rw [hD, G0, G1, hT, e0, e1]
  simp only [wordComp, hnil, List.nil_append, List.cons_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  ring

end UnforcedLeray.Short.PartI
