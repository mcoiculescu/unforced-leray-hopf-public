import UnforcedLeray.Lib.Kernels.NewtonDerivatives
import UnforcedLeray.Lib.AxisymmetricB.Lift
import UnforcedLeray.Lib.AxisymmetricB.Hessian

/-!
# Jets of the inverse radius `ϱ⁻¹` (all scales), task `PartII-b:G4/5/2/1/3`

Source of record: `the November 2 reference manuscript` lines 2347-2369.
`ϱ⁻¹ = 4π · N ∘ horL` with `N` the Newton potential; the Newton derivative bound
`‖Dʲ N(x)‖ ≤ C_j |x|^{-(1+j)}` transports along the linear map `horL`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb.SqrtFrameJetsAux

open UnforcedLeray

theorem horL_preimage : (⇑Axi.horL ⁻¹' ({0}ᶜ : Set Space)) = Axi.axisᶜ := by
  ext y
  simp only [mem_preimage, mem_compl_iff, mem_singleton_iff, Axi.horL_apply]
  constructor
  · intro h hy
    apply h
    ext i
    fin_cases i <;> simp [Axi.hor, hy.1, hy.2]
  · intro h h0
    apply h
    refine ⟨?_, ?_⟩
    · simpa [Axi.hor] using congrArg (fun v : Space => v 0) h0
    · simpa [Axi.hor] using congrArg (fun v : Space => v 1) h0

theorem inv_varrho_eq (w : Space) :
    (Axi.ϱ w)⁻¹ = (4 * Real.pi) * PressureAnalysis.newtonPotential (Axi.horL w) := by
  have h : ‖Axi.horL w‖ = Axi.ϱ w := by rw [Axi.horL_apply, Axi.norm_hor_self]
  unfold PressureAnalysis.newtonPotential
  rw [h]
  by_cases h0 : Axi.ϱ w = 0
  · simp [h0]
  · have : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp

/-- Jets of `ϱ⁻¹` of order `j` at every off-axis point. -/
theorem varrho_inv_jet (j : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ z : Space, z ∉ Axi.axis →
    ‖iteratedFDeriv ℝ j (fun w : Space => (Axi.ϱ w)⁻¹) z‖ ≤ C * ((Axi.ϱ z)⁻¹) ^ (j + 1) := by
  obtain ⟨C0, hC0⟩ := Kernels.norm_iteratedFDeriv_newton_le j
  refine ⟨(4 * Real.pi * |C0| + 1) * (‖Axi.horL‖ + 1) ^ j, by positivity, fun z hz => ?_⟩
  have hopen : IsOpen ({0}ᶜ : Set Space) := isOpen_compl_singleton
  have hND : ContDiffOn ℝ ∞ PressureAnalysis.newtonPotential ({0}ᶜ : Set Space) :=
    fun x hx => (Kernels.contDiffAt_newton hx).contDiffWithinAt
  have hND' : ContDiffOn ℝ ∞ ((4 * Real.pi) • PressureAnalysis.newtonPotential)
      ({0}ᶜ : Set Space) := hND.const_smul (4 * Real.pi)
  have hzpre : z ∈ (⇑Axi.horL ⁻¹' ({0}ᶜ : Set Space)) := by rw [horL_preimage]; exact hz
  have hx0 : Axi.horL z ∈ ({0}ᶜ : Set Space) := hzpre
  have hpreopen : IsOpen (⇑Axi.horL ⁻¹' ({0}ᶜ : Set Space)) :=
    hopen.preimage Axi.horL.continuous
  have hfun : (fun w : Space => (Axi.ϱ w)⁻¹) =
      ((4 * Real.pi) • PressureAnalysis.newtonPotential) ∘ Axi.horL := by
    funext w; simp [inv_varrho_eq w]
  have hcomp := ContinuousLinearMap.iteratedFDerivWithin_comp_right (𝕜 := ℝ) Axi.horL hND'
    hopen.uniqueDiffOn hpreopen.uniqueDiffOn hx0 (i := j) (by exact_mod_cast le_top)
  rw [← hfun, iteratedFDerivWithin_of_isOpen j hpreopen hzpre,
    iteratedFDerivWithin_const_smul_apply ((hND.contDiffWithinAt hx0).of_le (by exact_mod_cast le_top)) hopen.uniqueDiffOn hx0,
    iteratedFDerivWithin_of_isOpen j hopen hx0] at hcomp
  rw [hcomp]
  have hn : ‖Axi.horL z‖ = Axi.ϱ z := by rw [Axi.horL_apply, Axi.norm_hor_self]
  have hϱ : 0 < Axi.ϱ z := Axi.ϱ_pos hz
  have h1 := hC0 (Axi.horL z) hx0
  rw [hn, Real.rpow_neg hϱ.le] at h1
  have h2 : Axi.ϱ z ^ ((1 + j : ℝ)) = Axi.ϱ z ^ (j + 1) := by
    rw [show (1 + j : ℝ) = ((j + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  rw [h2] at h1
  have h3 : ‖(4 * Real.pi) • iteratedFDeriv ℝ j PressureAnalysis.newtonPotential (Axi.horL z)‖
      ≤ 4 * Real.pi * |C0| * (Axi.ϱ z)⁻¹ ^ (j + 1) := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity), inv_pow]
    have h4 : 0 ≤ ((Axi.ϱ z) ^ (j + 1))⁻¹ := by positivity
    have h5 := mul_le_mul_of_nonneg_right (le_abs_self C0) h4
    have h6 := h1.trans h5
    have h7 : 0 ≤ 4 * Real.pi := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h6 h7]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hp : ∏ _i : Fin j, ‖Axi.horL‖ ≤ (‖Axi.horL‖ + 1) ^ j := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_pow_left₀ (norm_nonneg _) (by linarith) _
  have hpos : 0 ≤ ∏ _i : Fin j, ‖Axi.horL‖ := by positivity
  calc _ ≤ (4 * Real.pi * |C0| * (Axi.ϱ z)⁻¹ ^ (j + 1)) * (‖Axi.horL‖ + 1) ^ j :=
        mul_le_mul h3 hp hpos (by positivity)
    _ ≤ _ := by
        have : 0 ≤ (Axi.ϱ z)⁻¹ ^ (j + 1) := by positivity
        have : 0 ≤ (‖Axi.horL‖ + 1) ^ j := by positivity
        nlinarith [mul_nonneg ‹0 ≤ (Axi.ϱ z)⁻¹ ^ (j + 1)› ‹0 ≤ (‖Axi.horL‖ + 1) ^ j›]

end UnforcedLeray.Short.IIb.SqrtFrameJetsAux
