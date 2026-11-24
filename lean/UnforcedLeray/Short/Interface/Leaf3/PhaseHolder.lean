import UnforcedLeray.Short.Interface.Sub.I05

/-!
# Interface leaf 3, sub-lemma 2: `L³ × H¹ → L²` at one phase

Source of record: `the November 2 reference manuscript`, lines 6071-6075.
Hölder `(3, 6, 2)` and the Sobolev bound `‖f‖₆ ≤ S Σᵢ ‖∂ᵢf‖₂`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal NNReal ContDiff Topology

namespace UnforcedLeray.Short.Interface

open UnforcedLeray.Blueprint UnforcedLeray.SobolevGraph UnforcedLeray.Cons.C08

theorem phase_holder_sobolev : PhaseHolderSobolev := by
  intro j a f g ha hf hg hd
  have h6 : MemLp f 6 volume := SobolevEmbedding.weak_memLp_six hf hg hd
  have h6b := SobolevEmbedding.weak_eLpNorm_six_le_sum hf hg hd
  have hH : ENNReal.HolderTriple 3 6 2 := by
    apply ENNReal.HolderTriple.of_toReal
    norm_num [Real.holderTriple_iff]
  calc eLpNorm (fun x => symCol j (a x) (f x)) 2 volume
      ≤ (‖symCol j‖₊ : ℝ≥0∞) * eLpNorm a 3 volume * eLpNorm f 6 volume :=
        eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm ha.1 h6.1 (fun u v => symCol j u v) ‖symCol j‖₊
          (Eventually.of_forall fun x => by
            have := (symCol j).le_opNorm₂ (a x) (f x)
            rw [← NNReal.coe_le_coe]
            simpa using this)
    _ ≤ _ := by gcongr

end UnforcedLeray.Short.Interface
