import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T09_4

/-!
# Part II-b, task `PartII-b:T09/4/4` (`FundWindow`): fundamental lemma on the window strip

Source of record: `the November 2 reference manuscript`, SP 1639-1668, 1912-1916.
Target `fundWindow_proof : UnforcedLeray.Short.IIb.FundWindow`.

Proof. Let `U = {s > 0, |q| < c/2}` (open). For a smooth compactly supported real test `φ` with
`tsupport φ ⊆ U`, the function `χ = φ · s^{5/2}` is a window test (`IsWinTest`): smooth because
`φ` vanishes near `s ≤ 0` and `s^{5/2}` is smooth on `s > 0`; compactly supported; and with
support in `U`. On `U` the weight cancels, `χ · s^{-5/2} = φ`, so `∫ φ g = wInt χ g = 0`.
Mathlib's `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` then gives `g = 0` a.e. on `U`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

namespace FundWindowHelp

/-- The window strip `U = {s > 0, |q| < c/2}` is open. -/
theorem isOpen_strip (c : ℝ) :
    IsOpen (Ioi (0 : ℝ) ×ˢ (Ioo (-c / 2) (c / 2) ×ˢ (univ : Set ℝ))) :=
  isOpen_Ioi.prod (isOpen_Ioo.prod isOpen_univ)

/-- The test `χ = φ · s^{5/2}` built from a real test `φ` supported in `U`. -/
theorem winTest_of_strip {c : ℝ} {φ : Coord → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ Ioi (0 : ℝ) ×ˢ (Ioo (-c / 2) (c / 2) ×ˢ (univ : Set ℝ))) :
    IsWinTest c (fun x => φ x * (x.1 ^ (5 / 2 : ℝ))) := by
  have hsub : tsupport (fun x : Coord => φ x * (x.1 ^ (5 / 2 : ℝ))) ⊆ tsupport φ :=
    tsupport_mul_subset_left
  have hUs : Ioi (0 : ℝ) ×ˢ (Ioo (-c / 2) (c / 2) ×ˢ (univ : Set ℝ)) ⊆
      Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) :=
    prod_mono subset_rfl (subset_univ _)
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x0
    by_cases hx0 : 0 < x0.1
    · exact hφ.contDiffAt.mul (contDiffAt_fst.rpow_const_of_ne hx0.ne')
    · have hnot : x0 ∉ tsupport φ := fun h => by
        have := hφU h
        exact absurd this.1 hx0
      have hev : ∀ᶠ x in 𝓝 x0, φ x = 0 :=
        Filter.eventually_of_mem ((isClosed_tsupport φ).isOpen_compl.mem_nhds hnot)
          (fun x hx => image_eq_zero_of_notMem_tsupport hx)
      have h0 : ContDiffAt ℝ ∞ (fun _ : Coord => (0 : ℝ)) x0 := contDiffAt_const
      exact h0.congr_of_eventuallyEq (by
        filter_upwards [hev] with x hx
        simp [hx])
  · exact hφc.mul_right (f' := fun x : Coord => x.1 ^ (5 / 2 : ℝ))
  · exact hsub.trans (hφU.trans hUs)
  · intro x hx
    have hx' := hφU (hsub hx)
    exact ⟨hx'.2.1.1, hx'.2.1.2⟩

end FundWindowHelp

open FundWindowHelp in
/-- **Leaf `T09/4/4`** (fundamental lemma of the calculus of variations on the window strip). -/
theorem fundWindow_proof : UnforcedLeray.Short.IIb.FundWindow := by
  intro c g hc hloc hint
  have hUo := isOpen_strip c
  have hUm : MeasurableSet (Ioi (0 : ℝ) ×ˢ (Ioo (-c / 2) (c / 2) ×ˢ (univ : Set ℝ))) :=
    hUo.measurableSet
  have hUs : Ioi (0 : ℝ) ×ˢ (Ioo (-c / 2) (c / 2) ×ˢ (univ : Set ℝ)) ⊆
      Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) :=
    prod_mono subset_rfl (subset_univ _)
  have hloc' := hloc.mono_set hUs
  have key : ∀ᵐ x ∂(volume : Measure Coord),
      x ∈ (Ioi (0 : ℝ) ×ˢ (Ioo (-c / 2) (c / 2) ×ˢ (univ : Set ℝ))) → g x = 0 := by
    refine hUo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc' ?_
    intro φ hφ hφc hφU
    have hW := hint _ (winTest_of_strip hφ hφc hφU)
    rw [← hW]
    unfold wInt
    congr 1
    funext x
    by_cases hx : φ x = 0
    · simp [hx]
    · have hxU : x ∈ tsupport φ := subset_tsupport φ (Function.mem_support.2 hx)
      have hs : 0 < x.1 := (hφU hxU).1
      have hw : x.1 ^ (5 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hs _).ne'
      have hreal : φ x * x.1 ^ (5 / 2 : ℝ) * x.1 ^ (-(5 / 2 : ℝ)) = φ x := by
        rw [Real.rpow_neg hs.le, mul_inv_cancel_right₀ hw]
      show φ x • g x = (((φ x * x.1 ^ (5 / 2 : ℝ) : ℝ) : ℂ) *
        ((x.1 ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)) * g x
      rw [← Complex.ofReal_mul, hreal, Complex.real_smul]
  have hmeas := (ae_restrict_iff' hUm).2 key
  exact hmeas
