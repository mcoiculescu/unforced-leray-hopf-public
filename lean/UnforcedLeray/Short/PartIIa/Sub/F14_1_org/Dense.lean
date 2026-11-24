import UnforcedLeray.Short.PartIIa.Sub.F14_1_org.Defs
import UnforcedLeray.Short.PartIIa.Sub.F12
import UnforcedLeray.Short.PartIIa.Tasks.F12bPhaseInnerEqPairing

/-!
# Part II-a, `PartII-a:F14/1/1/org`: phase tests are dense in `Y_2`

Source of record: `the November 2 reference manuscript`, lines 1456-1457
("approximate the right side by smooth periodic Schwartz functions"; the phase tests are smooth
periodic Schwartz functions of bounded support).

Proof: the test elements form a subspace `M` of `Y_2`. If `Z ⊥ M`, then for every phase test `Φ`,
`⟪Φ, Z⟫ = ⟨testElem (conj Φ), Z⟩ = 0` (`phaseInnerEqPairing`, `conj (conj Φ) = Φ`), so `Z = 0`
(`B0411.eq_zero_of_forall_phasePair`); hence `M` is dense (`le_topologicalClosure_of_orthogonal`,
`Sub/F12.lean`), and a sequence realises any `g ∈ Y_2`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

theorem conjF_conjF (Φ : ℝ × Space → CVec3) : conjF (conjF Φ) = Φ := by
  funext p
  ext k
  simp [conjF]

/-- **Phase tests are dense in `Y_2`.** -/
theorem phaseTestsDenseY2 : PhaseTestsDenseY2 := by
  intro P _ g
  let M : Submodule ℂ (Yq P 2) :=
    { carrier := {x | ∃ G : ℝ × Space → CVec3, IsPhaseTest P G ∧ testElem P 2 G = x}
      add_mem' := by
        rintro _ _ ⟨G, hG, rfl⟩ ⟨H, hH, rfl⟩
        exact ⟨G + H, hG.add hH, testElem_add (hG.isSliceTest 2) (hH.isSliceTest 2)⟩
      zero_mem' := ⟨0, IsPhaseTest.zero, testElem_zero⟩
      smul_mem' := by
        rintro c _ ⟨G, hG, rfl⟩
        exact ⟨c • G, hG.const_smul c, testElem_const_smul (hG.isSliceTest 2) c⟩ }
  have htop : IsClosed ((⊤ : Submodule ℂ (Yq P 2)) : Set (Yq P 2)) := by
    rw [Submodule.top_coe]
    exact isClosed_univ
  have hsub : (⊤ : Submodule ℂ (Yq P 2)) ≤ M.topologicalClosure := by
    refine le_topologicalClosure_of_orthogonal ⊤ M htop le_top fun Z _ hZ => ?_
    refine eq_zero_of_forall_phasePair fun Φ hΦ => ?_
    have hc1 : IsPhaseTest P (conjF Φ) := (phaseInnerEqPairing P Φ hΦ).1
    have hc2 := (phaseInnerEqPairing P (conjF Φ) hc1).2 Z
    rw [conjF_conjF] at hc2
    rw [← hc2]
    exact hZ _ ⟨conjF Φ, hc1, rfl⟩
  have hg : g ∈ closure (M : Set (Yq P 2)) := by
    rw [← Submodule.topologicalClosure_coe]
    exact hsub Submodule.mem_top
  obtain ⟨x, hxM, hx⟩ := mem_closure_iff_seq_limit.1 hg
  choose G hG hGx using hxM
  refine ⟨G, hG, ?_⟩
  have e : (fun n => testElem P 2 (G n)) = x := funext hGx
  rw [e]
  exact hx

end UnforcedLeray.Short.PartIIa
