import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.Duhamel
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_2

/-!
# `SFCRep` from five Duhamel facts (`PartIII-b:C/flatset/col/7/1/1/2/1`)

Source `the November 2 reference manuscript` 1650-1656, 1684-1689.
The representative is `b = 1_{s>0} · duhamel ν μ G` where `G` is the `H_g`-density of the flat Leray
projection of the force (`LerayDriving`), `velC (R0 g) = duhamel ν μ G` a.e. (`DuhamelBridge`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem sfcRep_of (hLeray : LerayDriving) (hBridge : DuhamelBridge) (hSmooth : DuhamelSmooth)
    (hPer : DuhamelPeriodic) (hBound : DuhamelSliceBound) : SFCRep := by
  classical
  intro c ν μ hc R0 g hctx
  have hν : 0 < ν := hctx.1
  obtain ⟨G, hG, hPep⟩ := hLeray c hc g hctx.2.2.2
  set S : Set Chart := Ioi (0 : ℝ) ×ˢ univ with hSdef
  have hSopen : IsOpen S := isOpen_Ioi.prod isOpen_univ
  have hmem : ∀ p : Chart, 0 < p.1 → p ∈ S := fun p hp => ⟨hp, mem_univ _⟩
  have hsm := hSmooth c ν μ G hG hν
  have hpw : ∀ i, (fun p => (S.piecewise (duhamel ν μ G) 0 p) i) =
      S.piecewise (fun p => duhamel ν μ G p i) (fun _ => 0) := by
    intro i; funext p
    by_cases h : p ∈ S <;> simp [Set.piecewise, h]
  refine ⟨S.piecewise (duhamel ν μ G) 0, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i
    rw [hpw i]
    exact ContinuousOn.measurable_piecewise (hsm i).continuousOn continuousOn_const
      hSopen.measurableSet
  · intro i
    exact (hsm i).congr (fun p hp => by
      have := congrFun (hpw i) p
      rw [this, Set.piecewise_eq_of_mem _ _ _ hp])
  · intro s q η hs
    rw [Set.piecewise_eq_of_mem _ _ _ (hmem _ hs), Set.piecewise_eq_of_mem _ _ _ (hmem (s, (q, η)) hs)]
    exact hPer c ν μ G hG s q η hs
  · intro s hs
    obtain ⟨C, hC⟩ := hBound c ν μ G hG hν s hs
    refine ⟨C, fun x => ?_⟩
    have hcg : ∀ i j, cellGrad (S.piecewise (duhamel ν μ G) 0) (s, x) i j =
        cellGrad (duhamel ν μ G) (s, x) i j := by
      intro i j
      unfold cellGrad
      have : (fun y : ℝ × ℝ => S.piecewise (duhamel ν μ G) 0 (s, y) i) =
          fun y => duhamel ν μ G (s, y) i := by
        funext y; rw [Set.piecewise_eq_of_mem _ _ _ (hmem (s, y) hs)]
      simp only [this]
    rw [Set.piecewise_eq_of_mem _ _ _ (hmem (s, x) hs)]
    refine ⟨(hC x).1, fun i j => ?_⟩
    rw [hcg]
    exact (hC x).2 i j
  · intro p hp
    exact Set.piecewise_eq_of_notMem _ _ _ (fun h => absurd h.1 (not_lt.2 hp))
  · have hb := hBridge c ν μ hc R0 g G hctx hG hPep
    filter_upwards [hb, UnforcedLeray.Short.IIb.ageμ_ae_pos c (-3 / 2)] with p hp hpos
    rw [Set.piecewise_eq_of_mem _ _ _ (hmem p hpos)]
    exact hp.symm

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
