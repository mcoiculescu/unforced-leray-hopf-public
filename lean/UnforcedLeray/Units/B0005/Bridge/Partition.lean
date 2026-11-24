import UnforcedLeray.Units.B0005.Bridge.Unfold
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# B0005 bridge, part 3: every phase test is the periodization of a windowed test

Blueprint unit B0005 (tex 136–147). "In distributions" means: against smooth `𝒯`-periodic
tests in the phase model (`PhaseSpace.IsPhaseTest`), and against smooth compactly supported
spacetime tests in the interface (`Blueprint.IsSimilarityTest`). To pass from the second to the
first, every phase test `Φ` is written as `perT 𝒯 (χ Φ)` with a smooth partition of unity
`χ(τ) = θ(τ) / ∑ₖ θ(τ + k𝒯)` (`perT_cutoffTest`), where `θ` is a bump equal to `1` on
`[-𝒯/2, 3𝒯/2] ⊇ [0, 𝒯]`. The test `χ Φ` is smooth, of bounded support, and vanishes outside
the phase window `[-3𝒯/2, 5𝒯/2]` (`isPhaseTest_cutoffTest`, `timeSupp_cutoffTest`).

Also: post-composition with a real-linear map commutes with the transposed operators
(`driftT_clm`, `lapT_clm`), used to split complex tests into real and imaginary parts.

Status: infrastructure for the B0005 bridge. Theorem A is not proved in Lean.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.B0005

open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace

/-! ### Real-linear maps commute with the transposed operators -/

section Clm

variable {F F' : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F']
  [NormedSpace ℝ F']

theorem fderiv_clm_comp (L : F →L[ℝ] F') {Φ : ℝ × Space → F} (hΦ : Differentiable ℝ Φ)
    (p : ℝ × Space) : fderiv ℝ (fun q => L (Φ q)) p = L.comp (fderiv ℝ Φ p) :=
  (L.hasFDerivAt.comp p (hΦ p).hasFDerivAt).fderiv

theorem dy_clm (L : F →L[ℝ] F') {Φ : ℝ × Space → F} (hΦ : Differentiable ℝ Φ) (j : Fin 3) :
    dy j (fun q => L (Φ q)) = fun q => L (dy j Φ q) := by
  funext p
  simp only [dy, fderiv_clm_comp L hΦ, ContinuousLinearMap.comp_apply]

theorem dτ_clm (L : F →L[ℝ] F') {Φ : ℝ × Space → F} (hΦ : Differentiable ℝ Φ) :
    dτ (fun q => L (Φ q)) = fun q => L (dτ Φ q) := by
  funext p
  simp only [dτ, fderiv_clm_comp L hΦ, ContinuousLinearMap.comp_apply]

theorem driftT_clm (L : F →L[ℝ] F') {Φ : ℝ × Space → F} (hΦ : Differentiable ℝ Φ) :
    driftT (fun q => L (Φ q)) = fun q => L (driftT Φ q) := by
  funext p
  simp only [driftT, radialT, dτ_clm L hΦ, dy_clm L hΦ, map_add, map_neg, map_smul, map_sum]

theorem lapT_clm (L : F →L[ℝ] F') {Φ : ℝ × Space → F} (hΦ : ContDiff ℝ ∞ Φ) :
    lapT (fun q => L (Φ q)) = fun q => L (lapT Φ q) := by
  funext p
  simp only [lapT, dy_clm L (hΦ.differentiable (by simp)),
    dy_clm L ((contDiff_dy' hΦ _).differentiable (by simp)), map_sum]

end Clm

/-! ### The partition of unity in the phase -/

section Partition

variable (𝒯 : ℝ) [hT : Fact (0 < 𝒯)]

/-- The bump `θ`: `1` on `[-𝒯/2, 3𝒯/2]`, supported in `(-3𝒯/2, 5𝒯/2)`. -/
def bumpT : ContDiffBump (𝒯 / 2 : ℝ) := ⟨𝒯, 2 * 𝒯, hT.out, by linarith [hT.out]⟩

/-- `Θ(τ, y) = θ(τ)`. -/
def bumpFn (p : ℝ × Space) : ℝ := bumpT 𝒯 p.1

/-- The phase window `[A₀, B₀] = [-3𝒯/2, 5𝒯/2]` of the cutoff. -/
def winA : ℝ := 𝒯 / 2 - 2 * 𝒯
/-- The right end of the phase window. -/
def winB : ℝ := 𝒯 / 2 + 2 * 𝒯

theorem winA_le_winB : winA 𝒯 ≤ winB 𝒯 := by
  unfold winA winB; linarith [hT.out]

theorem contDiff_bumpFn : ContDiff ℝ ∞ (bumpFn 𝒯) :=
  (bumpT 𝒯).contDiff.comp contDiff_fst

theorem timeSupp_bumpFn : TimeSupp (winA 𝒯) (winB 𝒯) (bumpFn 𝒯) := by
  intro τ y hτ
  refine (bumpT 𝒯).zero_of_le_dist ?_
  simp only [winA, winB, mem_Icc, not_and_or, not_le] at hτ
  show 2 * 𝒯 ≤ dist τ (𝒯 / 2)
  rw [Real.dist_eq]
  rcases hτ with h | h
  · rw [abs_of_neg (by linarith [hT.out])]; linarith
  · rw [abs_of_pos (by linarith [hT.out])]; linarith

/-- `S = ∑ₖ Θ(· + k𝒯)`. -/
def bumpSum : ℝ × Space → ℝ := perT 𝒯 (bumpFn 𝒯)

theorem contDiff_bumpSum : ContDiff ℝ ∞ (bumpSum 𝒯) :=
  contDiff_perT hT.out (timeSupp_bumpFn 𝒯) (contDiff_bumpFn 𝒯)

theorem bumpSum_eq (p : ℝ × Space) :
    bumpSum 𝒯 p = ∑ k ∈ perIdx 𝒯 (winA 𝒯) (winB 𝒯) (p.1 - 1) (p.1 + 1),
      bumpFn 𝒯 (p.1 + k * 𝒯, p.2) :=
  perT_eq_sum (timeSupp_bumpFn 𝒯) _ p
    (fun k hk => mem_perIdx hT.out ⟨by linarith, by linarith⟩ hk)

theorem one_le_bumpSum (p : ℝ × Space) : 1 ≤ bumpSum 𝒯 p := by
  rw [bumpSum_eq]
  set k₀ : ℤ := -toIocDiv hT.out 0 p.1
  have hmem := sub_toIocDiv_zsmul_mem_Ioc hT.out 0 p.1
  rw [zero_add] at hmem
  have hk₀ : p.1 + (k₀ : ℝ) * 𝒯 = p.1 - toIocDiv hT.out 0 p.1 • 𝒯 := by
    simp only [k₀, Int.cast_neg, zsmul_eq_mul]; ring
  have hone : bumpFn 𝒯 (p.1 + k₀ * 𝒯, p.2) = 1 := by
    refine (bumpT 𝒯).one_of_mem_closedBall ?_
    rw [hk₀, Metric.mem_closedBall, Real.dist_eq]
    show |p.1 - toIocDiv hT.out 0 p.1 • 𝒯 - 𝒯 / 2| ≤ 𝒯
    rw [abs_le]
    constructor <;> linarith [hmem.1, hmem.2]
  have hin : k₀ ∈ perIdx 𝒯 (winA 𝒯) (winB 𝒯) (p.1 - 1) (p.1 + 1) := by
    refine mem_perIdx hT.out (σ := p.1) ⟨by linarith, by linarith⟩ ?_
    rw [hk₀]
    simp only [winA, winB, mem_Icc]
    constructor <;> linarith [hmem.1, hmem.2, hT.out]
  calc (1 : ℝ) = bumpFn 𝒯 (p.1 + k₀ * 𝒯, p.2) := hone.symm
    _ ≤ _ := Finset.single_le_sum (f := fun k : ℤ => bumpFn 𝒯 (p.1 + k * 𝒯, p.2))
        (fun k _ => (bumpT 𝒯).nonneg) hin

theorem bumpSum_pos (p : ℝ × Space) : 0 < bumpSum 𝒯 p :=
  lt_of_lt_of_le one_pos (one_le_bumpSum 𝒯 p)

theorem bumpSum_shift (t : ℝ) (y : Space) (k : ℤ) :
    bumpSum 𝒯 (t + k * 𝒯, y) = bumpSum 𝒯 (t, y) := by
  have hper : Function.Periodic (fun s => bumpSum 𝒯 (s, y)) 𝒯 :=
    fun s => perT_periodic 𝒯 (bumpFn 𝒯) s y
  exact (hper.int_mul k) t

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The windowed test `χ Φ`, `χ = Θ / S`. -/
def cutoffTest (Φ : ℝ × Space → F) : ℝ × Space → F :=
  fun p => (bumpFn 𝒯 p / bumpSum 𝒯 p) • Φ p

variable {𝒯}

theorem contDiff_cutoff : ContDiff ℝ ∞ (fun p => bumpFn 𝒯 p / bumpSum 𝒯 p) :=
  (contDiff_bumpFn 𝒯).div (contDiff_bumpSum 𝒯) fun p => (bumpSum_pos 𝒯 p).ne'

theorem timeSupp_cutoffTest (Φ : ℝ × Space → F) :
    TimeSupp (winA 𝒯) (winB 𝒯) (cutoffTest 𝒯 Φ) := by
  intro τ y hτ
  simp [cutoffTest, timeSupp_bumpFn 𝒯 τ y hτ]

theorem isPhaseTest_cutoffTest {Φ : ℝ × Space → F} (hΦ : IsPhaseTest 𝒯 Φ) :
    IsPhaseTest 0 (cutoffTest 𝒯 Φ) where
  smooth := contDiff_cutoff.smul hΦ.smooth
  periodic := fun τ y => by simp
  bounded_support := by
    obtain ⟨R, hR⟩ := hΦ.bounded_support
    exact ⟨R, fun τ y hy => by simp [cutoffTest, hR τ y hy]⟩

/-- **Every phase test is a periodization**: `perT 𝒯 (χ Φ) = Φ`. -/
theorem perT_cutoffTest {Φ : ℝ × Space → F} (hΦ : IsPhaseTest 𝒯 Φ) :
    perT 𝒯 (cutoffTest 𝒯 Φ) = Φ := by
  funext p
  obtain ⟨t, y⟩ := p
  rw [perT_eq_sum (timeSupp_cutoffTest Φ) (perIdx 𝒯 (winA 𝒯) (winB 𝒯) (t - 1) (t + 1)) (t, y)
    (fun k hk => mem_perIdx hT.out ⟨by linarith, by linarith⟩ hk)]
  have hΦper : Function.Periodic (fun s => Φ (s, y)) 𝒯 := fun s => hΦ.periodic s y
  have hterm : ∀ k : ℤ, cutoffTest 𝒯 Φ (t + k * 𝒯, y) =
      (bumpFn 𝒯 (t + k * 𝒯, y) / bumpSum 𝒯 (t, y)) • Φ (t, y) := by
    intro k
    simp only [cutoffTest, bumpSum_shift 𝒯 t y k]
    rw [show Φ (t + k * 𝒯, y) = Φ (t, y) from (hΦper.int_mul k) t]
  simp only [hterm]
  rw [← Finset.sum_smul, ← Finset.sum_div]
  have hS := bumpSum_eq 𝒯 (t, y)
  simp only at hS
  rw [← hS, div_self (bumpSum_pos 𝒯 (t, y)).ne', one_smul]

end Partition

end UnforcedLeray.B0005
