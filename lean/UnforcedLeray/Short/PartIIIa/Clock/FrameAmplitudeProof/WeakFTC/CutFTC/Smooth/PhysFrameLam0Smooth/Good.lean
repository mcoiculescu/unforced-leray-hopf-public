import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.WeakFTC.CutFTC.Smooth.PhysFrameLam0Smooth.LamJet

/-!
# Planar kernels with symbol-type decay (helper for `PartIII-a:T21/c5/1/1/2/1-2`)

Source `the November 2 reference manuscript`
lines 2891-2897: the planar dual kernels and their fixed derivatives decay like `|y|^{-2-j}`.

`Good L` says that `L : ℝ² → ℂ` is `C^∞` with `‖D^k L(z)‖ (1+‖z‖)^{k+2} ≤ C_k` for every `k`.
The seed dual kernels are `Good` (`good_lamP`, from `lamP_jet_decay`), and the class is closed
under directional derivatives `z ↦ DL(z) v`, the Euler operator `z ↦ DL(z) z`, sums and complex
multiples.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa.LamJetInf

open UnforcedLeray.Short.IIIa.SeedJet2Aux

/-- Planar kernels with symbol-type decay `‖D^k L(z)‖ ≲ (1+‖z‖)^{-k-2}`. -/
def Good (L : ℝ × ℝ → ℂ) : Prop :=
  ContDiff ℝ ∞ L ∧ ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z,
    ‖iteratedFDeriv ℝ k L z‖ * (1 + ‖z‖) ^ (k + 2) ≤ C

/-- The seed dual kernels are `Good`. -/
theorem good_lamP {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) (j : Fin 2) :
    Good (κ.lamP j) := by
  obtain ⟨hc, hb⟩ := lamP_jet_decay hκ
  refine ⟨hc j, fun k => ?_⟩
  obtain ⟨C, hC0, hC⟩ := hb k
  exact ⟨C, hC0, fun z => hC j z⟩

/-- `D^{m+2} id = 0`. -/
theorem iteratedFDeriv_id_add_two (m : ℕ) (z : ℝ × ℝ) :
    iteratedFDeriv ℝ (m + 1 + 1) (id : ℝ × ℝ → ℝ × ℝ) z = 0 := by
  rw [iteratedFDeriv_succ_eq_comp_right]
  have : (fun y : ℝ × ℝ => fderiv ℝ (id : ℝ × ℝ → ℝ × ℝ) y) =
      fun _ => ContinuousLinearMap.id ℝ (ℝ × ℝ) := by
    funext y; exact fderiv_id
  simp only [Function.comp_apply, this, iteratedFDeriv_succ_const, Pi.zero_apply, map_zero]

namespace Good

variable {L L₁ L₂ : ℝ × ℝ → ℂ}

theorem norm_le (hL : Good L) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖L z‖ * (1 + ‖z‖) ^ 2 ≤ C := by
  obtain ⟨C, hC0, hC⟩ := hL.2 0
  exact ⟨C, hC0, fun z => by simpa [norm_iteratedFDeriv_zero] using hC z⟩

theorem fderiv_norm_le (hL : Good L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖fderiv ℝ L z‖ * (1 + ‖z‖) ^ 3 ≤ C := by
  obtain ⟨C, hC0, hC⟩ := hL.2 1
  exact ⟨C, hC0, fun z => by simpa [norm_iteratedFDeriv_one] using hC z⟩

theorem contDiff_fderiv (hL : Good L) : ContDiff ℝ ∞ (fderiv ℝ L) :=
  (contDiff_infty_iff_fderiv.1 hL.1).2

theorem differentiable (hL : Good L) : Differentiable ℝ L :=
  (contDiff_infty_iff_fderiv.1 hL.1).1

/-- Directional derivatives of `Good` kernels are `Good`. -/
theorem fderiv_apply (hL : Good L) (v : ℝ × ℝ) : Good (fun z => fderiv ℝ L z v) := by
  refine ⟨hL.contDiff_fderiv.clm_apply contDiff_const, fun k => ?_⟩
  obtain ⟨C, hC0, hC⟩ := hL.2 (k + 1)
  refine ⟨‖v‖ * C, by positivity, fun z => ?_⟩
  have h1 := norm_iteratedFDeriv_clm_apply_const (c := v) (x := z)
    hL.contDiff_fderiv.contDiffAt (le_top_nat k)
  rw [norm_iteratedFDeriv_fderiv] at h1
  have hp : (1 + ‖z‖) ^ (k + 2) ≤ (1 + ‖z‖) ^ (k + 1 + 2) :=
    pow_le_pow_right₀ (by linarith [norm_nonneg z]) (by omega)
  calc ‖iteratedFDeriv ℝ k (fun y => fderiv ℝ L y v) z‖ * (1 + ‖z‖) ^ (k + 2)
      ≤ (‖v‖ * ‖iteratedFDeriv ℝ (k + 1) L z‖) * (1 + ‖z‖) ^ (k + 1 + 2) := by gcongr
    _ = ‖v‖ * (‖iteratedFDeriv ℝ (k + 1) L z‖ * (1 + ‖z‖) ^ (k + 1 + 2)) := by ring
    _ ≤ ‖v‖ * C := by gcongr; exact hC z

/-- The Euler operator `z ↦ DL(z) z` preserves `Good`. -/
theorem euler (hL : Good L) : Good (fun z => fderiv ℝ L z z) := by
  have hfd := hL.contDiff_fderiv
  refine ⟨hfd.clm_apply contDiff_id, fun k => ?_⟩
  choose C hC0 hC using hL.2
  refine ⟨∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * C (i + 1),
    Finset.sum_nonneg fun i _ => by have := hC0 (i + 1); positivity, fun z => ?_⟩
  have h1 := norm_iteratedFDeriv_clm_apply (f := fderiv ℝ L) (g := id) hfd contDiff_id z
    (le_top_nat k)
  have hz1 : 1 ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
  have hterm : ∀ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fderiv ℝ L) z‖ *
        ‖iteratedFDeriv ℝ (k - i) (id : ℝ × ℝ → ℝ × ℝ) z‖ * (1 + ‖z‖) ^ (k + 2) ≤
      (k.choose i : ℝ) * C (i + 1) := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [norm_iteratedFDeriv_fderiv, mul_assoc, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hCi := hC (i + 1) z
    rcases (show k - i = 0 ∨ k - i = 1 ∨ 2 ≤ k - i by omega) with h0 | h1' | h2
    · have hik' : i = k := by omega
      subst hik'
      rw [h0, norm_iteratedFDeriv_zero, id]
      calc ‖iteratedFDeriv ℝ (i + 1) L z‖ * (‖z‖ * (1 + ‖z‖) ^ (i + 2))
          ≤ ‖iteratedFDeriv ℝ (i + 1) L z‖ * ((1 + ‖z‖) * (1 + ‖z‖) ^ (i + 2)) := by
            gcongr; linarith
        _ = ‖iteratedFDeriv ℝ (i + 1) L z‖ * (1 + ‖z‖) ^ (i + 1 + 2) := by ring
        _ ≤ C (i + 1) := hCi
    · have hk : k = i + 1 := by omega
      rw [h1', norm_iteratedFDeriv_one, fderiv_id, hk]
      calc ‖iteratedFDeriv ℝ (i + 1) L z‖ * (‖ContinuousLinearMap.id ℝ (ℝ × ℝ)‖ *
            (1 + ‖z‖) ^ (i + 1 + 2))
          ≤ ‖iteratedFDeriv ℝ (i + 1) L z‖ * (1 * (1 + ‖z‖) ^ (i + 1 + 2)) := by
            gcongr; exact ContinuousLinearMap.norm_id_le
        _ = ‖iteratedFDeriv ℝ (i + 1) L z‖ * (1 + ‖z‖) ^ (i + 1 + 2) := by ring
        _ ≤ C (i + 1) := hCi
    · obtain ⟨m, hm⟩ : ∃ m, k - i = m + 1 + 1 := ⟨k - i - 2, by omega⟩
      rw [hm, iteratedFDeriv_id_add_two m z, norm_zero, zero_mul, mul_zero]
      exact hC0 _
  calc ‖iteratedFDeriv ℝ k (fun z => fderiv ℝ L z z) z‖ * (1 + ‖z‖) ^ (k + 2)
      ≤ (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fderiv ℝ L) z‖ *
          ‖iteratedFDeriv ℝ (k - i) (id : ℝ × ℝ → ℝ × ℝ) z‖) * (1 + ‖z‖) ^ (k + 2) := by
        gcongr; exact h1
    _ = ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fderiv ℝ L) z‖ *
          ‖iteratedFDeriv ℝ (k - i) (id : ℝ × ℝ → ℝ × ℝ) z‖ * (1 + ‖z‖) ^ (k + 2) := by
        rw [Finset.sum_mul]
    _ ≤ _ := Finset.sum_le_sum hterm

/-- Sums of `Good` kernels are `Good`. -/
theorem add (h1 : Good L₁) (h2 : Good L₂) : Good (fun z => L₁ z + L₂ z) := by
  refine ⟨h1.1.add h2.1, fun k => ?_⟩
  obtain ⟨C₁, hC₁0, hC₁⟩ := h1.2 k
  obtain ⟨C₂, hC₂0, hC₂⟩ := h2.2 k
  refine ⟨C₁ + C₂, by positivity, fun z => ?_⟩
  show ‖iteratedFDeriv ℝ k (L₁ + L₂) z‖ * (1 + ‖z‖) ^ (k + 2) ≤ C₁ + C₂
  rw [iteratedFDeriv_add_apply (h1.1.contDiffAt.of_le (le_top_nat k))
    (h2.1.contDiffAt.of_le (le_top_nat k))]
  calc ‖iteratedFDeriv ℝ k L₁ z + iteratedFDeriv ℝ k L₂ z‖ * (1 + ‖z‖) ^ (k + 2)
      ≤ (‖iteratedFDeriv ℝ k L₁ z‖ + ‖iteratedFDeriv ℝ k L₂ z‖) * (1 + ‖z‖) ^ (k + 2) := by
        gcongr; exact norm_add_le _ _
    _ = ‖iteratedFDeriv ℝ k L₁ z‖ * (1 + ‖z‖) ^ (k + 2) +
          ‖iteratedFDeriv ℝ k L₂ z‖ * (1 + ‖z‖) ^ (k + 2) := by ring
    _ ≤ C₁ + C₂ := add_le_add (hC₁ z) (hC₂ z)

/-- Complex multiples of `Good` kernels are `Good`. -/
theorem const_mul (h : Good L) (a : ℂ) : Good (fun z => a * L z) := by
  refine ⟨contDiff_const.mul h.1, fun k => ?_⟩
  obtain ⟨C, hC0, hC⟩ := h.2 k
  refine ⟨‖a‖ * C, by positivity, fun z => ?_⟩
  have e : (fun z => a * L z) = a • L := by funext z; simp [smul_eq_mul]
  rw [e, iteratedFDeriv_const_smul_apply (h.1.contDiffAt.of_le (le_top_nat k)), norm_smul,
    mul_assoc]
  gcongr
  exact hC z

end Good

end UnforcedLeray.Short.IIIa.LamJetInf
