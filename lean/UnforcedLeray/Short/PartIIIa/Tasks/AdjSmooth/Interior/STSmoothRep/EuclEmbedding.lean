import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.STSmooth.Defs
import UnforcedLeray.Lib.SobolevC.ContDiffRep

/-!
# `PartIII-a:T21/2/7/2/1/1/8/3`: `H^∞(ℝ³) ⊂ C^k` (`euclGlobalEmbedding`)

Fields `g α := G (letters α)` where `G l` is a chosen weak derivative of `f` along the word `l`;
`Sob.W.ofFields` builds an element of `W^{k+2,2}(ℝ³)`, and `Sob.W.exists_contDiff_rep` gives its
`C^k` representative.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology ContDiff

namespace UnforcedLeray.Short.IIIa

open UnforcedLeray.Sob

theorem word_letters {k : ℕ} (α : Idx 3 k) :
    (wholeSpace 3).word α = (List.ofFn α.2).map e := by
  rw [List.map_ofFn]
  rfl

theorem memLp_wμ_one' {f : Eucl 3 → ℂ} (hf : MemLp f 2 volume) :
    MemLp f 2 (wμ (wholeSpace 3).μ 1) := by
  rw [wμ_one]
  exact hf

theorem hasWeakDeriv_nil_self' {f : Eucl 3 → ℂ} (hf : MemLp f 2 volume) :
    HasWeakDeriv (wholeSpace 3) [] f f := by
  have hf' := memLp_wμ_one' hf
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · simpa only [iterDirDeriv_nil] using
      integrable_smul_of_memLp (CompactlyBounded.of_adm hφ) hf'
  · exact integrable_smul_of_memLp (CompactlyBounded.of_adm hφ) hf'
  · simp

theorem euclGlobalEmbedding : EuclGlobalEmbedding := by
  intro f hf k
  obtain ⟨hf1, hf2⟩ := hf
  choose G hGmem hGw using hf2
  have hG0 : G [] =ᵐ[volume] f :=
    HasWeakDeriv.ae_unique (hGw []) (hasWeakDeriv_nil_self' hf1)
      (locallyIntegrable_of_memLp (memLp_wμ_one' (hGmem [])))
      (locallyIntegrable_of_memLp (memLp_wμ_one' hf1))
  have hmem : ∀ α : Idx 3 (k + 2), MemLp (G (List.ofFn α.2)) 2 (wμ (wholeSpace 3).μ 1) :=
    fun α => memLp_wμ_one' (hGmem _)
  have hw : ∀ α : Idx 3 (k + 2), HasWeakDeriv (wholeSpace 3) ((wholeSpace 3).word α)
      (G (List.ofFn (Idx.zero : Idx 3 (k + 2)).2)) (G (List.ofFn α.2)) := by
    intro α
    rw [word_letters]
    have hz : List.ofFn (Idx.zero : Idx 3 (k + 2)).2 = [] := rfl
    rw [hz]
    exact (hGw (List.ofFn α.2)).congr_ae hG0.symm EventuallyEq.rfl
  obtain ⟨C, _, hall⟩ := Sob.W.exists_contDiff_rep (F := ℂ) (k := k) (n := 3) (by norm_num)
  obtain ⟨G', hG'c, hG'ae, -⟩ :=
    hall (Sob.W.ofFields (𝕜 := ℂ) (fun α => G (List.ofFn α.2)) hmem hw)
  refine ⟨G', hG'c, ?_⟩
  refine hG'ae.symm.trans ?_
  have hz := (ae_eq_wμ_iff (wholeSpace 3).μ 1).mp (hmem Idx.zero).coeFn_toLp
  exact hz.trans hG0

end UnforcedLeray.Short.IIIa
