import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.STSobolev.Defs

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

lemma mpv_shift_eq {c : ℝ} {g : ℝ × ℝ → ℂ} (hg : ∀ x : ℝ × ℝ, g (x.1 + c, x.2) = g x)
    (k : ℤ) (x : ℝ × ℝ) : g (x - ((k : ℝ) * c, (0 : ℝ))) = g x := by
  have hk : ∀ j : ℤ, ∀ y : ℝ × ℝ, g (y.1 + (j : ℝ) * c, y.2) = g y := by
    intro j
    refine Int.induction_on j ?_ ?_ ?_
    · intro y
      simp
    · intro i ih y
      have h1 := ih (y.1 + c, y.2)
      dsimp only at h1
      rw [show y.1 + c + ((i : ℤ) : ℝ) * c = y.1 + (((i : ℤ) + 1 : ℤ) : ℝ) * c by
        push_cast; ring] at h1
      rw [h1]
      exact hg y
    · intro i ih y
      have h1 := hg (y.1 + (((-(i : ℤ)) - 1 : ℤ) : ℝ) * c, y.2)
      dsimp only at h1
      rw [show y.1 + (((-(i : ℤ)) - 1 : ℤ) : ℝ) * c + c
          = y.1 + ((-(i : ℤ) : ℤ) : ℝ) * c by push_cast; ring] at h1
      rw [← h1]
      exact ih y
  have e : x - ((k : ℝ) * c, (0 : ℝ)) = (x.1 + ((-k : ℤ) : ℝ) * c, x.2) := by
    ext <;> simp <;> ring
  rw [e]
  exact hk (-k) x

/-- Translation invariance of volume on the plane, in preimage form. -/
lemma mpv_preimage_sub (A : Set (ℝ × ℝ)) (v : ℝ × ℝ) :
    volume ((fun x : ℝ × ℝ => x - v) ⁻¹' A) = volume A := by
  simpa [sub_eq_add_neg] using measure_preimage_add_right (volume : Measure (ℝ × ℝ)) (-v) A

theorem measPlaneVersion : UnforcedLeray.Short.IIIa.MeasPlaneVersion := by
  intro c m t s f F hc hF hper hae
  -- the periodic shift index and the translated function
  let T : ℝ × (ℝ × ℝ) → ℝ × (ℝ × ℝ) := fun p =>
    (p.1, (p.2.1 - ((⌊(p.2.1 + c / 2) / c⌋ : ℤ) : ℝ) * c, p.2.2))
  have hfl : Measurable (fun y : ℝ => ((⌊(y + c / 2) / c⌋ : ℤ) : ℝ)) := by
    have hfloor : Measurable (fun y : ℝ => ⌊(y + c / 2) / c⌋) :=
      Int.measurable_floor.comp ((measurable_id.add_const _).div_const _)
    exact (Measurable.of_discrete (f := fun n : ℤ => (n : ℝ))).comp hfloor
  have hT : Measurable T := by
    refine Measurable.prodMk measurable_fst ?_
    refine Measurable.prodMk ?_ ?_
    · exact (measurable_fst.comp measurable_snd |>.sub
        ((hfl.comp (measurable_fst.comp measurable_snd)).mul_const c))
    · exact measurable_snd.comp measurable_snd
  refine ⟨fun p => F (T p), hF.comp hT, ?_⟩
  intro r hr
  -- the cell-null set
  have hN0 : volume ({x : ℝ × ℝ | ¬ F (r, x) = f r x} ∩ B0579.cell c) = 0 := by
    have h1 : B0579.cellMeasure c (-m) {x : ℝ × ℝ | ¬ F (r, x) = f r x} = 0 :=
      ae_iff.mp (hae r hr)
    have h2 : (volume.restrict (B0579.cell c)) {x : ℝ × ℝ | ¬ F (r, x) = f r x} = 0 :=
      (B0579.ac_cellMeasure c (-m)) h1
    rwa [Measure.restrict_apply' (B0579.measurableSet_cell c)] at h2
  -- every bad point is a translate of a bad point in the cell
  have hsub : {x : ℝ × ℝ | ¬ F (T (r, x)) = f r x} ⊆
      ⋃ k : ℤ, (fun x : ℝ × ℝ => x - ((k : ℝ) * c, (0 : ℝ))) ⁻¹'
        ({x : ℝ × ℝ | ¬ F (r, x) = f r x} ∩ B0579.cell c) := by
    intro x hx
    simp only [mem_setOf_eq] at hx
    set k : ℤ := ⌊(x.1 + c / 2) / c⌋ with hk
    have h1 : (k : ℝ) * c ≤ x.1 + c / 2 := (le_div_iff₀ hc).1 (Int.floor_le _)
    have h2 : x.1 + c / 2 < ((k : ℝ) + 1) * c := (div_lt_iff₀ hc).1 (Int.lt_floor_add_one _)
    have hy1 : x.1 - (k : ℝ) * c ∈ Ico (-(c / 2)) (c / 2) := by
      constructor <;> nlinarith
    have hpt : x - ((k : ℝ) * c, (0 : ℝ)) = (x.1 - (k : ℝ) * c, x.2) := by
      ext <;> simp
    have hfx : f r (x - ((k : ℝ) * c, (0 : ℝ))) = f r x := mpv_shift_eq (hper r hr) k x
    simp only [mem_iUnion, mem_preimage, mem_inter_iff, mem_setOf_eq]
    refine ⟨k, ?_, ?_⟩
    · rw [hfx]
      have hTx : T (r, x) = (r, x - ((k : ℝ) * c, (0 : ℝ))) := by
        rw [hpt]
      rw [hTx] at hx
      exact hx
    · exact ⟨hy1, trivial⟩
  refine ae_iff.mpr ?_
  refine measure_mono_null hsub ?_
  refine measure_iUnion_null fun k => ?_
  rw [mpv_preimage_sub]
  exact hN0
