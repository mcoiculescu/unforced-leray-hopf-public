import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_8
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
# Leaf `PartII-b:T13/1/8/2`: consistency of local weak derivatives on overlaps (SP 1928-1933)

`WglConsistency`: two local weak derivatives of `b` on windows `(a, 2a)` and `(a', 2a')` agree a.e.
on the intersection. Proof: the difference is locally integrable on the open intersection and has
zero pairing with every smooth compactly supported test there, so it vanishes a.e. (fundamental
lemma of the calculus of variations).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter Metric
open scoped ENNReal ContDiff

theorem wglc_open (a : ℝ) : IsOpen (winOpen a) := isOpen_Ioo.prod isOpen_univ

theorem wglc_pos (a : ℝ) (ha : 0 < a) : winOpen a ⊆ Ioi (0 : ℝ) ×ˢ univ :=
  fun _ hx => ⟨lt_trans ha hx.1.1, trivial⟩

/-- Componentwise fundamental lemma on the overlap of two windows. -/
theorem wglc_component (v : Coord → Fin 3 → ℝ) (b : CProf) (g : ℝ → CProf)
    (hloc : ∀ a : ℝ, 0 < a → HasWeakVecOn (winOpen a) v dZero b (g a))
    (a a' : ℝ) (ha : 0 < a) (ha' : 0 < a') (i : Fin 2) :
    ∀ᵐ x ∂(volume : Measure Coord), x ∈ winOpen a ∩ winOpen a' → g a x i = g a' x i := by
  have hUo : IsOpen (winOpen a ∩ winOpen a') := (wglc_open a).inter (wglc_open a')
  have hzero : ∀ᵐ x ∂(volume : Measure Coord),
      x ∈ winOpen a ∩ winOpen a' → (g a x i - g a' x i) = 0 := by
    refine hUo.ae_eq_zero_of_integral_contDiff_smul_eq_zero ?_ ?_
    · -- local integrability on the overlap
      intro x hx
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUo x hx
      let β : ContDiffBump x :=
        { rIn := ε / 4
          rOut := ε / 2
          rIn_pos := by linarith
          rIn_lt_rOut := by linarith }
      have hβsub : tsupport β ⊆ winOpen a ∩ winOpen a' := by
        rw [β.tsupport_eq]
        exact (Metric.closedBall_subset_ball (by linarith : ε / 2 < ε)).trans hball
      have hβa : tsupport β ⊆ winOpen a := fun y hy => (hβsub hy).1
      have hβa' : tsupport β ⊆ winOpen a' := fun y hy => (hβsub hy).2
      have hβtest : IsCoordTest β :=
        ⟨β.contDiff, β.hasCompactSupport, fun y hy => wglc_pos a ha (hβa hy)⟩
      obtain ⟨-, J1, -⟩ := (hloc a ha i) β hβtest hβa
      obtain ⟨-, J2, -⟩ := (hloc a' ha' i) β hβtest hβa'
      have hB1 : IntegrableOn (fun y => g a y i) (ball x (ε / 4)) := by
        apply (J1.integrableOn).congr_fun _ measurableSet_ball
        intro y hy
        have h1 : β y = 1 := β.one_of_mem_closedBall (ball_subset_closedBall hy)
        simp [h1]
      have hB2 : IntegrableOn (fun y => g a' y i) (ball x (ε / 4)) := by
        apply (J2.integrableOn).congr_fun _ measurableSet_ball
        intro y hy
        have h1 : β y = 1 := β.one_of_mem_closedBall (ball_subset_closedBall hy)
        simp [h1]
      have hBF : IntegrableOn (fun y => g a y i - g a' y i) (ball x (ε / 4)) :=
        hB1.sub hB2
      have hat : IntegrableAtFilter (fun y => g a y i - g a' y i) (nhds x) volume :=
        ⟨ball x (ε / 4), ball_mem_nhds x (by linarith), hBF⟩
      exact hat.filter_mono nhdsWithin_le_nhds
    · -- vanishing of the pairing with every test supported in the overlap
      intro φ hφ hφc hφU
      have hφa : tsupport φ ⊆ winOpen a := fun y hy => (hφU hy).1
      have hφa' : tsupport φ ⊆ winOpen a' := fun y hy => (hφU hy).2
      have hφtest : IsCoordTest φ :=
        ⟨hφ, hφc, fun y hy => wglc_pos a ha (hφa hy)⟩
      obtain ⟨-, J1, E1⟩ := (hloc a ha i) φ hφtest hφa
      obtain ⟨-, J2, E2⟩ := (hloc a' ha' i) φ hφtest hφa'
      have J1' : Integrable (fun y => g a y i * (φ y : ℂ)) volume := J1
      have J2' : Integrable (fun y => g a' y i * (φ y : ℂ)) volume := J2
      have E1' : ∫ y, g a y i * (φ y : ℂ) = ∫ y, b y i * (coordTranspose v dZero φ y : ℂ) := E1
      have E2' : ∫ y, g a' y i * (φ y : ℂ) = ∫ y, b y i * (coordTranspose v dZero φ y : ℂ) := E2
      have hfun : (fun y => φ y • (g a y i - g a' y i)) =
          fun y => g a y i * (φ y : ℂ) - g a' y i * (φ y : ℂ) := by
        funext y
        rw [Complex.real_smul]
        ring
      show ∫ y, φ y • (g a y i - g a' y i) = 0
      rw [hfun, integral_sub J1' J2', E1', E2', sub_self]
  filter_upwards [hzero] with x hx hxU
  exact sub_eq_zero.mp (hx hxU)

theorem wglConsistency : WglConsistency := by
  intro v hv b g hloc a a' ha ha'
  filter_upwards [ae_all_iff.mpr (fun i => wglc_component v b g hloc a a' ha ha' i)] with x hx hxa hxa'
  ext i
  exact hx i ⟨hxa, hxa'⟩

end UnforcedLeray.Short.IIb
