import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_2.Shell.Smooth

/-!
# `ShellInvBound`, and the frame, age and phase jets on the shell

Source `the November 2 reference manuscript`
lines 2545-2549, 1206-1222.  The slice `{ρ₀ ≤ ϱ ≤ R₀, y₃ = 0}` is compact and avoids the axis;
an axially invariant function smooth off the axis has continuous jets there, hence bounded, and
`D^i f(y) = D^i f(y − y₃ e₃)`.  The frame factor, the age and `log s` are axially invariant.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.Shell

open UnforcedLeray.Axi

theorem isCompact_shellSlice (ρ0 R0 : ℝ) :
    IsCompact {y : UnforcedLeray.Space | ρ0 ≤ ϱ y ∧ ϱ y ≤ R0 ∧ y 2 = 0} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · have h2 : Continuous fun y : UnforcedLeray.Space => y 2 := by fun_prop
    exact (isClosed_le continuous_const continuous_ϱ).inter
      ((isClosed_le continuous_ϱ continuous_const).inter (isClosed_eq h2 continuous_const))
  · rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨|R0|, fun y hy => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hy
    rw [Metric.mem_closedBall, dist_zero_right]
    have hsq : ‖y‖ ^ 2 = ϱ y ^ 2 := by rw [norm_sq_eq_ϱ_sq_add, h3]; ring
    have hn : ‖y‖ = ϱ y := by
      rw [← Real.sqrt_sq (norm_nonneg y), hsq, Real.sqrt_sq (ϱ_nonneg y)]
    rw [hn]
    exact h2.trans (le_abs_self R0)

/-- Jets of a function smooth off the axis are bounded on the compact slice
`{ρ₀ ≤ ϱ ≤ R₀, y₃ = 0}` (source 2545-2549). -/
theorem shellSliceBound {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : UnforcedLeray.Space → F) (hf : ContDiffOn ℝ ∞ f axisᶜ) (n : ℕ) {ρ0 : ℝ} (R0 : ℝ)
    (hρ0 : 0 < ρ0) : ∃ C : ℝ, ∀ y : UnforcedLeray.Space, ρ0 ≤ ϱ y → ϱ y ≤ R0 → y 2 = 0 →
      ∀ i : ℕ, i ≤ n → ‖iteratedFDeriv ℝ i f y‖ ≤ C := by
  set K : Set UnforcedLeray.Space := {y | ρ0 ≤ ϱ y ∧ ϱ y ≤ R0 ∧ y 2 = 0} with hK
  have hKax : K ⊆ axisᶜ := fun y hy => notMem_axis_of_le hρ0 hy.1
  have hs : IsOpen (axisᶜ : Set UnforcedLeray.Space) := isOpen_compl_axis
  have hcont : ∀ i : ℕ, ContinuousOn (fun y => iteratedFDeriv ℝ i f y) axisᶜ := by
    intro i
    have h := hf.continuousOn_iteratedFDerivWithin (m := i) (by exact_mod_cast le_top)
      hs.uniqueDiffOn
    exact h.congr fun y hy => (iteratedFDerivWithin_of_isOpen i hs hy).symm
  have hg : ContinuousOn
      (fun y => ∑ i ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ i f y‖) K :=
    continuousOn_finset_sum _ fun i _ => ((hcont i).mono hKax).norm
  obtain ⟨C, hC⟩ := (isCompact_shellSlice ρ0 R0).exists_bound_of_continuousOn hg
  refine ⟨C, fun y hy1 hy2 hy3 i hi => ?_⟩
  have hle : ‖iteratedFDeriv ℝ i f y‖ ≤
      ∑ j ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ j f y‖ :=
    Finset.single_le_sum (f := fun j => ‖iteratedFDeriv ℝ j f y‖)
      (fun j _ => norm_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
  refine hle.trans ?_
  have := hC y ⟨hy1, hy2, hy3⟩
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun j _ => norm_nonneg _)] at this
  exact this

/-- The point `y − y₃ e₃` of the slice. -/
theorem shellSlice_mem {ρ0 R0 : ℝ} {y : UnforcedLeray.Space} (hy1 : ρ0 ≤ ϱ y) (hy2 : ϱ y ≤ R0) :
    ρ0 ≤ ϱ (y + (-(y 2)) • e3) ∧ ϱ (y + (-(y 2)) • e3) ≤ R0 ∧ (y + (-(y 2)) • e3) 2 = 0 := by
  rw [ϱ_add_e3]
  exact ⟨hy1, hy2, by simp [e3_apply]⟩

theorem shellSlice_add (y : UnforcedLeray.Space) : y + (-(y 2)) • e3 + y 2 • e3 = y := by
  rw [add_assoc, ← add_smul]; simp

/-- **`ShellInvBound`** (source 2545-2549). -/
theorem shellInvBound : ShellInvBound := by
  intro F _ _ f hf hinv n ρ0 R0 hρ0
  obtain ⟨C, hC⟩ := shellSliceBound f hf n R0 hρ0
  refine ⟨C, fun y hy1 hy2 i hi => ?_⟩
  obtain ⟨h1, h2, h3⟩ := shellSlice_mem hy1 hy2
  have hshift : (fun z => f (z + y 2 • e3)) = f := funext fun z => hinv z (y 2)
  have heq : iteratedFDeriv ℝ i f y = iteratedFDeriv ℝ i f (y + (-(y 2)) • e3) := by
    have h := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := f) i (y 2 • e3)
      (y + (-(y 2)) • e3)
    rw [hshift, shellSlice_add] at h
    exact h.symm
  rw [heq]
  exact hC _ h1 h2 h3 i hi

/-- **`ShellTransJets`** (source 1209, 2545-2549): `η(z + c e₃) = η(z) + c R ϱ(z)⁻¹`, so
`D^i η(y) = D^i η(y') + y₃ R D^i(ϱ⁻¹)(y')` at the slice point `y' = y − y₃ e₃`. -/
theorem shellTransJets : ShellTransJets := by
  intro R ρ0 R0 n hR hρ0
  have hh : ContDiffOn ℝ ∞ (fun y => R * (ϱ y)⁻¹) axisᶜ := contDiffOn_const.mul contDiffOn_inv_ϱ
  obtain ⟨C1, hC1⟩ := shellSliceBound (Axi.trans R) (contDiffOn_trans R) n R0 hρ0
  obtain ⟨C2, hC2⟩ := shellSliceBound (fun y => R * (ϱ y)⁻¹) hh n R0 hρ0
  refine ⟨max C1 C2, fun y hy1 hy2 i hi => ?_⟩
  obtain ⟨h1, h2, h3⟩ := shellSlice_mem hy1 hy2
  set y' := y + (-(y 2)) • e3 with hy'
  have hax' : y' ∉ axis := notMem_axis_of_le hρ0 h1
  have hnhds : axisᶜ ∈ nhds y' := isOpen_compl_axis.mem_nhds hax'
  have hle : ((i : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hT : ContDiffAt ℝ i (Axi.trans R) y' := ((contDiffOn_trans R).contDiffAt hnhds).of_le hle
  have hH : ContDiffAt ℝ i (fun y => R * (ϱ y)⁻¹) y' := (hh.contDiffAt hnhds).of_le hle
  have hshift : (fun z => Axi.trans R (z + y 2 • e3)) =
      Axi.trans R + fun z => y 2 • (R * (ϱ z)⁻¹) := by
    funext z
    simp only [Axi.trans, ϱ_add_e3, Pi.add_apply, PiLp.add_apply, PiLp.smul_apply, e3_apply,
      smul_eq_mul, if_true, mul_one]
    ring
  have heq : iteratedFDeriv ℝ i (Axi.trans R) y =
      iteratedFDeriv ℝ i (Axi.trans R) y' + y 2 • iteratedFDeriv ℝ i (fun y => R * (ϱ y)⁻¹) y' := by
    have h := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := Axi.trans R) i (y 2 • e3) y'
    rw [hshift, shellSlice_add, iteratedFDeriv_add_apply hT (hH.const_smul (y 2)),
      iteratedFDeriv_const_smul_apply' hH] at h
    exact h.symm
  rw [heq]
  have hb1 := hC1 y' h1 h2 h3 i hi
  have hb2 := hC2 y' h1 h2 h3 i hi
  have hC1' : C1 ≤ max C1 C2 := le_max_left _ _
  have hC2' : C2 ≤ max C1 C2 := le_max_right _ _
  have hC20 : 0 ≤ C2 := (norm_nonneg _).trans hb2
  calc ‖iteratedFDeriv ℝ i (Axi.trans R) y' + y 2 • iteratedFDeriv ℝ i (fun y => R * (ϱ y)⁻¹) y'‖
      ≤ ‖iteratedFDeriv ℝ i (Axi.trans R) y'‖ +
          |y 2| * ‖iteratedFDeriv ℝ i (fun y => R * (ϱ y)⁻¹) y'‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, Real.norm_eq_abs]
    _ ≤ C1 + |y 2| * C2 := add_le_add hb1 (mul_le_mul_of_nonneg_left hb2 (abs_nonneg _))
    _ ≤ max C1 C2 + |y 2| * max C1 C2 :=
        add_le_add hC1' (mul_le_mul_of_nonneg_left hC2' (abs_nonneg _))
    _ = max C1 C2 * (1 + |y 2|) := by ring

/-- **`ShellFrameJets`** from `ShellInvBound` (source 1214-1216, 2545-2549). -/
theorem shellFrameJets : ShellFrameJets := by
  intro R ρ0 R0 n hR hρ0
  exact shellInvBound _ (frameFac R) (contDiffOn_frameFac hR.ne') (frameFac_add_e3 R) n ρ0 R0
    hρ0

/-- **`ShellAgeJets`** from `ShellInvBound` (source 1209, 2545-2549). -/
theorem shellAgeJets : ShellAgeJets := by
  intro R ρ0 R0 n _ hρ0
  exact shellInvBound _ (age R) (contDiffOn_age R) (age_add_e3 R) n ρ0 R0 hρ0

/-- **`ShellPhaseJets`** from `ShellInvBound` (source 1209, 2545-2549): `ξ = Rτ/2 − (R/2) log s`,
the constant drops out of the derivatives of order `≥ 1`. -/
theorem shellPhaseJets : ShellPhaseJets := by
  intro R ρ0 R0 n hR hρ0
  obtain ⟨C, hC⟩ := shellInvBound ℝ (fun y => Real.log (age R y)) (contDiffOn_log_age hR.ne')
    (fun x t => by simp only [age_add_e3]) n ρ0 R0 hρ0
  refine ⟨|R / 2| * C, fun τ y hy1 hy2 i hi1 hin => ?_⟩
  have hax := notMem_axis_of_le hρ0 hy1
  have hnhds : axisᶜ ∈ nhds y := isOpen_compl_axis.mem_nhds hax
  have hle : ((i : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hL : ContDiffAt ℝ i (fun y => Real.log (age R y)) y :=
    ((contDiffOn_log_age hR.ne').contDiffAt hnhds).of_le hle
  have hph : phase R τ = (fun _ : UnforcedLeray.Space => R * τ / 2) -
      fun y => (R / 2) • Real.log (age R y) := by
    funext y
    simp [phase, smul_eq_mul]
  have hsm : iteratedFDeriv ℝ i (fun y => (R / 2) • Real.log (age R y)) y =
      (R / 2) • iteratedFDeriv ℝ i (fun y => Real.log (age R y)) y :=
    iteratedFDeriv_const_smul_apply' hL
  rw [hph, iteratedFDeriv_sub_apply contDiffAt_const (hL.const_smul (R / 2)),
    iteratedFDeriv_const_of_ne (by omega), hsm]
  simp only [Pi.zero_apply, zero_sub, norm_neg, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hC y hy1 hy2 i hin) (abs_nonneg _)

end UnforcedLeray.Short.PartIIIb.Concrete.Shell
