import UnforcedLeray.Short.PartIIb.Sub.T11_6
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.CellStream.PeriodicUnfold

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

theorem mollPeriodic : MollPeriodic := by
  intro c g δ ρ₁ ρ₂ hc hper p
  have hcut : ∀ᵐ x : Coord, cutC δ g (qShift c x) = cutC δ g x := by
    filter_upwards [hper] with x hx
    by_cases h : δ < x.1
    · have h' : δ < (qShift c x).1 := h
      simp only [cutC, Set.indicator_of_mem (show x ∈ {x : Coord | δ < x.1} from h),
        Set.indicator_of_mem (show qShift c x ∈ {x : Coord | δ < x.1} from h'), hx]
    · have h' : ¬ δ < (qShift c x).1 := h
      simp only [cutC, Set.indicator_of_notMem (show x ∉ {x : Coord | δ < x.1} from h),
        Set.indicator_of_notMem (show qShift c x ∉ {x : Coord | δ < x.1} from h')]
  unfold mollC mollG
  have hsub : ∀ y : Coord, ((qShift c p).1 - (qShift c y).1 = p.1 - y.1) ∧
      ((qShift c p).2 - (qShift c y).2 = p.2 - y.2) := by
    intro y
    refine ⟨rfl, ?_⟩
    ext <;> simp [qShift]
  have e := (puc_measurePreserving_qShift c).integral_comp (puc_qShift_measurableEmbedding c)
    (fun x : Coord => ((ρ₁ ((qShift c p).1 - x.1) * ρ₂ ((qShift c p).2 - x.2) : ℝ) : ℂ) * cutC δ g x)
  rw [← e]
  refine integral_congr_ae ?_
  filter_upwards [hcut] with y hy
  simp only [(hsub y).1, (hsub y).2, hy]

end UnforcedLeray.Short.IIb
