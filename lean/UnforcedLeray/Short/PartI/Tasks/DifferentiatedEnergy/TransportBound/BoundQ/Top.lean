import UnforcedLeray.Short.PartI.Sub.PartI_T08_7_3_1
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.TransportBound.BoundA

/-!
# Part I, task `PartI:T08/7/3/1/1`: `JTQTop` (top term vanishes)

Source: `the November 2 reference manuscript` lines 352-358.
For each `k`, the sum over `m` is `∫ G (f·∇G)` with `G = ∂_w f_k`; this is zero by
`ba_top_zero` (integration by parts on the periodic cell, `div f = 0`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

theorem jtQTop_proof : UnforcedLeray.Short.PartI.JTQTop := by
  intro c V f Gb M H w
  obtain ⟨hc, hV, hVp, hVd, hf, hfd, hfb, hG, hMb⟩ := H
  have hc0 : 0 < c := by linarith
  have hfs : ContDiff ℝ ∞ f := hf.1
  refine Finset.sum_eq_zero fun k _ => ?_
  have hFk : ContDiff ℝ ∞ (fun x => f x k) := contDiff_comp_coord hfs k
  have hGc : ContDiff ℝ ∞ (wordComp w f k) := contDiff_wordComp hfs w k
  have hGp : Cyl.IsPeriodic c (wordComp w f k) :=
    ForcingIBP.per_derivWord w _ (hf.2.1.fun_comp (fun x => x k))
  have hQ : wordComp (w ++ [true]) f k = Cyl.partialQ (wordComp w f k) :=
    ba_wordComp_append_true w hFk
  have hE : wordComp (w ++ [false]) f k = Cyl.partialEta (wordComp w f k) :=
    ba_wordComp_append_false w hFk
  have hG0 : MemLp (wordComp w f k) 2 (Cyl.cellμ c) := hf.2.2 w k
  have hGq : MemLp (Cyl.partialQ (wordComp w f k)) 2 (Cyl.cellμ c) := by
    rw [← hQ]; exact hf.2.2 _ k
  have hGe : MemLp (Cyl.partialEta (wordComp w f k)) 2 (Cyl.cellμ c) := by
    rw [← hE]; exact hf.2.2 _ k
  have hbt := ba_top_zero hc0 hfs hf.2.1 hfd hfb hGc
    (ForcingIBP.per_derivWord w _ (hf.2.1.fun_comp (fun x => x k))) hG0 hGq hGe
  obtain ⟨M0, hM0⟩ := hfb [] 0
  obtain ⟨M1, hM1⟩ := hfb [] 1
  have cB0 : AEStronglyMeasurable (fun z => wordComp [] f 0 z) (Cyl.cellμ c) :=
    (contDiff_wordComp hfs [] 0).continuous.aestronglyMeasurable
  have cB1 : AEStronglyMeasurable (fun z => wordComp [] f 1 z) (Cyl.cellμ c) :=
    (contDiff_wordComp hfs [] 1).continuous.aestronglyMeasurable
  have hA : Integrable (fun z => wordComp w f k z *
      (wordComp [] f 0 z * Cyl.partialQ (wordComp w f k) z)) (Cyl.cellμ c) :=
    (ba_int3 (μ := Cyl.cellμ c) (x := wordComp w f k)
      (y := Cyl.partialQ (wordComp w f k)) (B := fun z => wordComp [] f 0 z)
      hG0 hGq cB0 M0 hM0).congr (Filter.Eventually.of_forall fun z => by
        dsimp only; ring)
  have hB : Integrable (fun z => wordComp w f k z *
      (wordComp [] f 1 z * Cyl.partialEta (wordComp w f k) z)) (Cyl.cellμ c) :=
    (ba_int3 (μ := Cyl.cellμ c) (x := wordComp w f k)
      (y := Cyl.partialEta (wordComp w f k)) (B := fun z => wordComp [] f 1 z)
      hG0 hGe cB1 M1 hM1).congr (Filter.Eventually.of_forall fun z => by
        dsimp only; ring)
  rw [Fin.sum_univ_two]
  have d0 : dirOf 0 = true := rfl
  have d1 : dirOf 1 = false := rfl
  rw [d0, d1, hQ, hE]
  refine Eq.trans (Eq.trans (integral_add hA hB).symm ?_) hbt
  have e0 : ∀ z, wordComp [] f 0 z = f z 0 := fun z => rfl
  have e1 : ∀ z, wordComp [] f 1 z = f z 1 := fun z => rfl
  exact integral_congr_ae (Filter.Eventually.of_forall fun z => by
    dsimp only; rw [e0, e1]; ring)

end UnforcedLeray.Short.PartI
