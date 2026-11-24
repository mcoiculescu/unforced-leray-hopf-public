import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.STSobolev.Defs
import UnforcedLeray.Short.PartIIIa.Sub.T18_2_4_2
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.STSobolev.CellWeakUnique

/-!
# `PartIII-a:T21/2/7/2/1/1/7/9`: coherent derivative fields of the time jets

Source: `the November 2 reference manuscript` lines 3060-3061.
Two cell jets of the same function agree almost everywhere on the cell for all common-length words
(induction on the word, using `CellWeakUnique`).  Hence the fields `D j r w := D^{(j,|w|)} r w`
of the chosen jets give the coherent fields `CohJets`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Two cell jets of the same function agree almost everywhere on the cell for every word of
length at most both orders. -/
theorem cellJet_ae_eq_of_le {c m : ℝ} {k k' : ℕ} {f : ℝ × ℝ → ℂ}
    {D1 D2 : List (Fin 2) → ℝ × ℝ → ℂ} (hc : 0 < c)
    (h1 : IsCellJet c m k f D1) (h2 : IsCellJet c m k' f D2) :
    ∀ w : List (Fin 2), w.length ≤ k → w.length ≤ k' →
      D1 w =ᵐ[volume.restrict (B0579.cell c)] D2 w := by
  intro w
  induction w with
  | nil =>
    intro _ _
    rw [h1.base, h2.base]
  | cons i w ih =>
    intro hl1 hl2
    simp only [List.length_cons] at hl1 hl2
    have ihw := ih (by omega) (by omega)
    have d1 : HasWeakCellDerivC c i (D1 w) (D1 (i :: w)) := h1.deriv i w (by omega)
    have d2 : HasWeakCellDerivC c i (D2 w) (D2 (i :: w)) := h2.deriv i w (by omega)
    have d1' : HasWeakCellDerivC c i (D2 w) (D1 (i :: w)) :=
      HasWeakCellDerivC.congr_ae ihw.symm EventuallyEq.rfl d1
    exact cellWeakUnique c i (D2 w) (D1 (i :: w)) (D2 (i :: w)) hc d1' d2

theorem cohJetsExists : UnforcedLeray.Short.IIIa.CohJetsExists := by
  intro c m t s Φ hc hJ
  have hA : ∀ j k : ℕ, ∃ D : ℝ → List (Fin 2) → ℝ × ℝ → ℂ,
      (∀ r ∈ Ioo t s, IsCellJet c m k (Φ j r) (D r)) ∧
        ∀ w : List (Fin 2), w.length ≤ k → ∀ r ∈ Ioo t s,
          Tendsto (fun r' => xNorm c (-m) (D r' w - D r w)) (𝓝[Ioo t s] r) (𝓝 0) :=
    fun j k => hJ.1 j k
  choose D hDj hDc using hA
  refine ⟨fun j r w => D j w.length r w, ?_, ?_⟩
  · intro j k r hr
    refine { base := ?_, periodic := ?_, memX := ?_, deriv := ?_ }
    · exact (hDj j 0 r hr).base
    · intro w _ x
      exact (hDj j w.length r hr).periodic w le_rfl x
    · intro w _
      exact (hDj j w.length r hr).memX w le_rfl
    · intro i w _
      have h1 := (hDj j (w.length + 1) r hr).deriv i w (Nat.lt_succ_self _)
      have hk : D j (w.length + 1) r w =ᵐ[volume.restrict (B0579.cell c)] D j w.length r w :=
        cellJet_ae_eq_of_le hc (hDj j (w.length + 1) r hr) (hDj j w.length r hr) w
          (Nat.le_succ _) le_rfl
      exact HasWeakCellDerivC.congr_ae hk.symm EventuallyEq.rfl h1
  · intro j w r hr
    exact hDc j w.length w le_rfl r hr

end UnforcedLeray.Short.IIIa
