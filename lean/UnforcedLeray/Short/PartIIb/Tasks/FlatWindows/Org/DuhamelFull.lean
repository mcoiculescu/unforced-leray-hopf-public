import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.FlatGraphOrg
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Tasks_FlatCausal_DuhamelEquation

/-!
# Part II-b, leaf `PartII-b:T13/1/2` (`DuhamelFullEq`)

Source of record: `the November 2 reference manuscript`, lines 1922-1927.

The renamed copy `dfe_duhamelEquation` (folder `DuhamelFull/`) of the causal Duhamel equation holds for every
`IsPlanarTestDfe` field `Ψ` (smooth components only, no divergence condition). Taking `Ψ = φ e_i` gives
the componentwise statement `DuhamelFullEq`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff

theorem dfe_cpd_zero (j : Fin 3) : cpd j (fun _ : Coord => (0 : ℝ)) = fun _ => 0 := by
  funext x
  simp [cpd]

theorem dfe_flatTransposeS_zero (ν : ℝ) (μ : ℂ) :
    flatTransposeS ν μ (fun _ : Coord => (0 : ℝ)) = fun _ => 0 := by
  funext x
  simp [flatTransposeS, dfe_cpd_zero]

/-- The test `φ e_i`. -/
def dfePsi (i : Fin 2) (φ : Coord → ℝ) : Coord → Fin 2 → ℝ := fun y j => if j = i then φ y else 0

theorem dfePsi_test (i : Fin 2) {φ : Coord → ℝ} (hφ : IsCoordTest φ) :
    IsPlanarTestDfe (dfePsi i φ) := by
  refine ⟨fun j => ?_⟩
  by_cases h : j = i
  · simpa [dfePsi, h] using hφ
  · have : (fun x => dfePsi i φ x j) = fun _ => (0 : ℝ) := by
      funext x; simp [dfePsi, h]
    rw [this]
    exact ⟨contDiff_const, HasCompactSupport.zero, by simp⟩

theorem dfe_sum_eq (ν : ℝ) (μ : ℂ) (b : CProf) (i : Fin 2) (φ : Coord → ℝ) (x : Coord) :
    ∑ j : Fin 2, b x j * flatTranspose ν μ (dfePsi i φ) x j = b x i * flatTransposeS ν μ φ x := by
  rw [Finset.sum_eq_single i]
  · simp [flatTranspose, flatTransposeS, dfePsi]
  · intro j _ hj
    have : flatTranspose ν μ (dfePsi i φ) x j = 0 := by
      have h0 : (fun y => dfePsi i φ y j) = fun _ => (0 : ℝ) := by
        funext y; simp [dfePsi, hj]
      have : flatTranspose ν μ (dfePsi i φ) x j =
          flatTransposeS ν μ (fun y => dfePsi i φ y j) x := rfl
      rw [this, h0, dfe_flatTransposeS_zero]
    simp [this]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem dfe_cdot_eq (G : CProf) (i : Fin 2) (φ : Coord → ℝ) (x : Coord) :
    cdot G (dfePsi i φ) x = G x i * (φ x : ℂ) := by
  unfold cdot
  rw [Finset.sum_eq_single i]
  · simp [dfePsi]
  · intro j _ hj; simp [dfePsi, hj]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- **Leaf `PartII-b:T13/1/2`** (SP 1922-1927). -/
theorem duhamelFullEq : UnforcedLeray.Short.IIb.DuhamelFullEq := by
  intro r hr1 hr3 μ hμ ν c hν hc G hG hb i φ hφ
  obtain ⟨h1, h2, h3⟩ := dfe_duhamelEquation r hr1 hr3 μ hμ ν c hν hc G hG hb
    (dfePsi i φ) (dfePsi_test i hφ)
  have e1 : (fun x => ∑ j : Fin 2, flatDuhamel ν μ G x j * flatTranspose ν μ (dfePsi i φ) x j) =
      fun x => flatDuhamel ν μ G x i * flatTransposeS ν μ φ x :=
    funext fun x => dfe_sum_eq ν μ (flatDuhamel ν μ G) i φ x
  have e2 : cdot G (dfePsi i φ) = fun x => G x i * (φ x : ℂ) :=
    funext fun x => dfe_cdot_eq G i φ x
  rw [e1] at h1 h3
  rw [e2] at h2 h3
  exact ⟨h1, h2, h3⟩

end UnforcedLeray.Short.IIb

end
