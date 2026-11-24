import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.TimeJets.Defs
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.Leaf.WeakCellAeUnique

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Transport of a weak cell derivative along an a.e. equality of its first argument. -/
theorem hwcd_transport {c : ℝ} {j : Fin 2} {φ φ' g : ℝ × ℝ → ℂ}
    (h : HasWeakCellDerivC c j φ g) (he : φ =ᵐ[volume.restrict (B0579.cell c)] φ') :
    HasWeakCellDerivC c j φ' g := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun ψ hψ => ?_, fun ψ hψ => ?_⟩
  · obtain ⟨hi1, hi2⟩ := h1 ψ hψ
    have hae : (fun x => φ x * (B0579.pd j ψ x : ℂ)) =ᵐ[volume.restrict (B0579.cell c)]
        (fun x => φ' x * (B0579.pd j ψ x : ℂ)) := by
      filter_upwards [he] with x hx
      simp only [hx]
    exact ⟨hi1.congr_fun_ae hae, hi2⟩
  · have hae : (fun x => φ x * (B0579.pd j ψ x : ℂ)) =ᵐ[volume.restrict (B0579.cell c)]
        (fun x => φ' x * (B0579.pd j ψ x : ℂ)) := by
      filter_upwards [he] with x hx
      simp only [hx]
    rw [← h2 ψ hψ]
    exact (integral_congr_ae hae).symm

/-- **(1) One family of fields for all orders** (SP 3060-3061): the fields of all orders agree a.e.
on the cell along the words, by induction on the word with `weakCellAeUnique`. -/
theorem adjHkAllOf : AdjHkAllOf := by
  intro c m I f hc hk
  simp only [AdjHkOn] at hk
  choose D hD using hk
  -- Key lemma: the fields of order `k` agree a.e. with those of order `|w|`.
  have key : ∀ r ∈ I, ∀ w : List (Fin 2), ∀ k : ℕ, w.length ≤ k →
      D k r w =ᵐ[volume.restrict (B0579.cell c)] D w.length r w := by
    intro r hr w
    induction w with
    | nil =>
      intro k _
      have e : D k r [] = D 0 r [] :=
        ((hD k).1 r hr).base.trans ((hD 0).1 r hr).base.symm
      simp only [List.length_nil]
      rw [e]
    | cons j w ih =>
      intro k hk'
      have hk2 : w.length + 1 ≤ k := by simpa using hk'
      have IHk : D k r w =ᵐ[volume.restrict (B0579.cell c)] D w.length r w :=
        ih k (by omega)
      have IHn1 : D (w.length + 1) r w =ᵐ[volume.restrict (B0579.cell c)] D w.length r w :=
        ih (w.length + 1) (by omega)
      have hA : HasWeakCellDerivC c j (D k r w) (D k r (j :: w)) :=
        ((hD k).1 r hr).deriv j w (by omega)
      have hB : HasWeakCellDerivC c j (D (w.length + 1) r w) (D (w.length + 1) r (j :: w)) :=
        ((hD (w.length + 1)).1 r hr).deriv j w (by omega)
      have hA' := hwcd_transport hA IHk
      have hB' := hwcd_transport hB IHn1
      exact weakCellAeUnique c j (D w.length r w) _ _ hA' hB'
  refine ⟨fun r w => D w.length r w, ⟨fun r hr k => ⟨?_, ?_, ?_, ?_⟩, fun w r hr => ?_⟩⟩
  · exact ((hD 0).1 r hr).base
  · intro w hw x
    exact ((hD w.length).1 r hr).periodic w le_rfl x
  · intro w hw
    exact ((hD w.length).1 r hr).memX w le_rfl
  · intro j w _
    have hB : HasWeakCellDerivC c j (D (w.length + 1) r w) (D (w.length + 1) r (j :: w)) :=
      ((hD (w.length + 1)).1 r hr).deriv j w (by omega)
    have hB' := hwcd_transport hB (key r hr w (w.length + 1) (by omega))
    simpa using hB'
  · exact (hD w.length).2 w le_rfl r hr

end UnforcedLeray.Short.IIIa
