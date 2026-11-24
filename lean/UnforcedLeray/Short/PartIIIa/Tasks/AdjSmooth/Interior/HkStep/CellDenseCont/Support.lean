import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Shared
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.AdjWeakDefs

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.IIIa

/-- The periodic extension of a continuous field vanishing on `|x₁| ≥ c/2` is continuous. -/
theorem continuous_perRep {c : ℝ} (hc : 0 < c) {h1 : ℝ × ℝ → ℂ} (hcont : Continuous h1)
    (h0 : ∀ x : ℝ × ℝ, (x.1 ≤ -(c / 2) ∨ c / 2 ≤ x.1) → h1 x = 0) :
    Continuous (perRep c h1) := by
  let A : ℤ → Set (ℝ × ℝ) := fun k => Icc ((k : ℝ) * c - c / 2) ((k : ℝ) * c + c / 2) ×ˢ univ
  have hAclosed : ∀ k, IsClosed (A k) := fun k => isClosed_Icc.prod isClosed_univ
  have hcover : ⋃ k, A k = univ := by
    refine eq_univ_of_forall fun x => mem_iUnion.2 ⟨⌊(x.1 + c / 2) / c⌋, ?_⟩
    have h1' := Int.floor_le ((x.1 + c / 2) / c)
    have h2' := Int.lt_floor_add_one ((x.1 + c / 2) / c)
    rw [le_div_iff₀ hc] at h1'
    rw [div_lt_iff₀ hc] at h2'
    exact ⟨⟨by linarith, by linarith⟩, trivial⟩
  have hloc : LocallyFinite A := by
    intro x
    refine ⟨{y | |y.1 - x.1| < c}, ?_, ?_⟩
    · exact IsOpen.mem_nhds (isOpen_lt (continuous_fst.sub continuous_const).abs continuous_const)
        (by simpa using hc)
    · refine (Set.finite_Icc (⌈x.1 / c - 3 / 2⌉) (⌊x.1 / c + 3 / 2⌋)).subset ?_
      intro k hk
      obtain ⟨y, hyA, hyU⟩ := hk
      have hy1 : (k : ℝ) * c - c / 2 ≤ y.1 ∧ y.1 ≤ (k : ℝ) * c + c / 2 := hyA.1
      have hy2 := abs_lt.1 (show |y.1 - x.1| < c from hyU)
      constructor
      · rw [Int.ceil_le, show x.1 / c - 3 / 2 = (x.1 - 3 * c / 2) / c by field_simp,
          div_le_iff₀ hc]
        linarith [hy2.1, hy2.2]
      · rw [Int.le_floor, show x.1 / c + 3 / 2 = (x.1 + 3 * c / 2) / c by field_simp,
          le_div_iff₀ hc]
        linarith [hy2.1, hy2.2]
  refine hloc.continuous hcover hAclosed fun k => ?_
  have hEq : EqOn (perRep c h1) (fun x => h1 (x.1 - (k : ℝ) * c, x.2)) (A k) := by
    intro x hx
    have hx1 := hx.1
    simp only [perRep, dif_pos hc]
    by_cases hlt : x.1 < (k : ℝ) * c + c / 2
    · have : toIcoMod hc (-(c / 2)) x.1 = x.1 - (k : ℝ) * c := by
        rw [toIcoMod_eq_iff]
        refine ⟨⟨by linarith [hx1.1], by linarith⟩, k, ?_⟩
        simp
      rw [this]
    · have hx' : x.1 = (k : ℝ) * c + c / 2 := le_antisymm hx1.2 (not_lt.1 hlt)
      have : toIcoMod hc (-(c / 2)) x.1 = -(c / 2) := by
        rw [toIcoMod_eq_iff]
        refine ⟨⟨le_refl _, by linarith⟩, k + 1, ?_⟩
        simp only [zsmul_eq_mul]
        push_cast
        linarith
      rw [this, h0 (-(c / 2), x.2) (Or.inl le_rfl), h0 (x.1 - (k : ℝ) * c, x.2)
        (Or.inr (by simp only; linarith))]
  exact (hcont.comp ((continuous_fst.sub continuous_const).prodMk continuous_snd)).continuousOn.congr hEq

end UnforcedLeray.Short.IIIa
