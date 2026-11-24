import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_2_1_2
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductHilbert
import UnforcedLeray.Lib.PhaseTrace.Periodize
import Mathlib.Analysis.Calculus.BumpFunction.Normed

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace

/-- The reflected kernel vanishes where the first coordinate is more than `rOut` away. -/
theorem reflK_eq_zero_of_abs_lt (ρ : ContDiffBump (0 : ℝ × Space)) (x : ℝ × Space) (t : ℝ)
    (y : Space) (h : ρ.rOut < |x.1 - t|) : reflK ρ x (t, y) = 0 := by
  have hval : ρ.normed volume (x - (t, y)) = 0 := by
    by_contra hne
    have hmem : x - (t, y) ∈ Function.support (ρ.normed volume) := hne
    rw [ContDiffBump.support_normed_eq, Metric.mem_ball, dist_zero_right] at hmem
    have h1 : |x.1 - t| ≤ ‖x - (t, y)‖ := by
      have := norm_fst_le (x - (t, y))
      simpa [Real.norm_eq_abs] using this
    linarith
  simp [reflK, hval]

theorem reflK_contDiff (ρ : ContDiffBump (0 : ℝ × Space)) (x : ℝ × Space) :
    ContDiff ℝ ∞ (reflK ρ x) := by
  have h2 : ContDiff ℝ ∞ (fun w : ℝ × Space => x - w) := contDiff_const.sub contDiff_id
  have h1 : ContDiff ℝ ∞ (ρ.normed volume ∘ fun w : ℝ × Space => x - w) :=
    (ρ.contDiff_normed).comp h2
  exact Complex.ofRealCLM.contDiff.comp h1

theorem reflK_hasCompactSupport (ρ : ContDiffBump (0 : ℝ × Space)) (x : ℝ × Space) :
    HasCompactSupport (reflK ρ x) := by
  have h1 : HasCompactSupport (ρ.normed volume ∘ fun w : ℝ × Space => x - w) :=
    (ρ.hasCompactSupport_normed).comp_homeomorph (Homeomorph.subLeft x)
  have h2 : HasCompactSupport (Complex.ofReal ∘ (ρ.normed volume ∘ fun w : ℝ × Space => x - w)) :=
    h1.comp_left Complex.ofReal_zero
  exact h2

/-- The periodised reflected kernel is the phase periodisation of the reflected kernel. -/
theorem perK_eq_perT (ρ : ContDiffBump (0 : ℝ × Space)) (x : ℝ × Space) {P : ℝ} (hP : 0 < P) :
    perK ρ x P = UnforcedLeray.PhaseTrace.perT P (reflK ρ x) := by
  funext w
  obtain ⟨τ, y⟩ := w
  obtain ⟨N, hN⟩ : ∃ N : ℤ, (|x.1 - τ| + ρ.rOut) / P ≤ N :=
    ⟨⌈(|x.1 - τ| + ρ.rOut) / P⌉, Int.le_ceil _⟩
  have hcP : (|x.1 - τ| + ρ.rOut) / P * P = |x.1 - τ| + ρ.rOut := div_mul_cancel₀ _ hP.ne'
  have hA : ∀ k : ℤ, k ∉ Finset.Icc (-N) N → reflK ρ x (τ + (k : ℝ) * P, y) = 0 := by
    intro k hk
    apply reflK_eq_zero_of_abs_lt
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hk
    rw [lt_abs]
    rcases hk with hk | hk
    · have hk' : (k : ℝ) < -(N : ℝ) := by exact_mod_cast hk
      have h1 : (k : ℝ) * P < (-((|x.1 - τ| + ρ.rOut) / P)) * P :=
        mul_lt_mul_of_pos_right (by linarith) hP
      have h2 : (-((|x.1 - τ| + ρ.rOut) / P)) * P = -(|x.1 - τ| + ρ.rOut) := by
        rw [neg_mul, hcP]
      left
      linarith [neg_abs_le (x.1 - τ)]
    · have hk' : (N : ℝ) < (k : ℝ) := by exact_mod_cast hk
      have h1 : (|x.1 - τ| + ρ.rOut) / P * P < (k : ℝ) * P :=
        mul_lt_mul_of_pos_right (by linarith) hP
      right
      linarith [le_abs_self (x.1 - τ)]
  have hpair : ∀ k : ℤ, ((τ, y) + ((k : ℝ) * P, (0 : Space))) = (τ + (k : ℝ) * P, y) := by
    intro k
    ext <;> simp
  show ∑' k : ℤ, reflK ρ x ((τ, y) + ((k : ℝ) * P, (0 : Space))) =
    ∑ᶠ k : ℤ, reflK ρ x (τ + (k : ℝ) * P, y)
  simp only [hpair]
  rw [tsum_eq_sum (L := SummationFilter.unconditional ℤ)
    (f := fun k : ℤ => reflK ρ x (τ + (k : ℝ) * P, y)) (s := Finset.Icc (-N) N)
    (fun k hk => hA k hk)]
  have hsub : Function.support (fun k : ℤ => reflK ρ x (τ + (k : ℝ) * P, y)) ⊆
      ↑(Finset.Icc (-N) N) := by
    intro k hk
    rw [Finset.mem_coe]
    by_contra hks
    exact (Function.mem_support.mp hk) (hA k hks)
  rw [finsum_eq_sum_of_support_subset _ hsub]

/-- **S1** (lines 1351-1362): `φ_x` is a phase test. Proof: `φ_x` is the phase periodisation of
the compactly supported smooth reflected kernel `reflK ρ x`. -/
theorem perKPhaseTest : PerKPhaseTest := by
  intro ρ x P hP
  have h := UnforcedLeray.Cons.C03.Concrete.isPhaseTest_perT_of_compactSupport hP
    (reflK_contDiff ρ x) (reflK_hasCompactSupport ρ x)
  rw [perK_eq_perT ρ x hP]
  exact h

end UnforcedLeray.Short.PartIIIb.Concrete
