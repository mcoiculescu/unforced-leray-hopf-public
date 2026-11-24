import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.RingLift.SqrtFrameJets.InvRho

/-!
# Jets of the frame `frameL` off the axis, task `PartII-b:G4/5/2/1/3`

Source of record: `the November 2 reference manuscript` lines 2347-2369.
`frameL y = ϱ(y)⁻¹ • Φ y + Ψ` with `Φ y = proj₀.smulRight (hor y)` linear in `y` and `Ψ` constant;
Leibniz plus the jets of `ϱ⁻¹` (`varrho_inv_jet`) give `‖Dʲ frameL(y)‖ ≤ C_j ϱ(y)^{-j}`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb.SqrtFrameJetsAux

open UnforcedLeray

/-- The linear part `y ↦ proj₀.smulRight (hor y)`. -/
def Phi : Space →L[ℝ] (Axi.Merid →L[ℝ] Space) :=
  ((ContinuousLinearMap.smulRightL ℝ Axi.Merid Space)
    (EuclideanSpace.proj (0 : Fin 2) : Axi.Merid →L[ℝ] ℝ)).comp Axi.horL

theorem Phi_apply (y : Space) (v : Axi.Merid) : Phi y v = v 0 • Axi.hor y := by
  simp [Phi, Axi.horL_apply]

/-- The constant part. -/
def Psi : Axi.Merid →L[ℝ] Space :=
  (EuclideanSpace.proj (1 : Fin 2) : Axi.Merid →L[ℝ] ℝ).smulRight Axi.e3

theorem frameL_eq (y : Space) : Axi.frameL y = (Axi.ϱ y)⁻¹ • Phi y + Psi := by
  ext v : 1
  simp [Axi.frameL_apply, Phi_apply, Psi, Axi.eR, smul_smul, mul_comm]

theorem norm_Phi_le (y : Space) : ‖Phi y‖ ≤ Axi.ϱ y := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Axi.ϱ_nonneg y) fun v => ?_
  rw [Phi_apply, norm_smul, Axi.norm_hor_self, mul_comm]
  have : ‖v 0‖ ≤ ‖v‖ := PiLp.norm_apply_le v 0
  exact mul_le_mul_of_nonneg_left this (Axi.ϱ_nonneg y)

/-- Iterated derivatives of a continuous linear map of order `≥ 2` vanish, of order 1 are bounded
by the operator norm. -/
theorem clm_jet_ge_two {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) (m : ℕ) (x : E) :
    iteratedFDeriv ℝ (m + 2) L x = 0 := by
  have h := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := (L : E → F)) (x := x) (n := m + 1)
  have hf : fderiv ℝ (L : E → F) = fun _ => L := funext fun z => L.fderiv
  rw [hf, iteratedFDeriv_succ_const] at h
  simpa using h.symm

theorem clm_jet_one {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) (x : E) :
    ‖iteratedFDeriv ℝ 1 L x‖ ≤ ‖L‖ := by
  have h := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := (L : E → F)) (x := x) (n := 0)
  have hf : fderiv ℝ (L : E → F) = fun _ => L := funext fun z => L.fderiv
  rw [hf] at h
  simp only [norm_iteratedFDeriv_zero] at h
  exact h.symm.le

/-- Jets of the frame of order `j ≥ 1`. -/
theorem frameL_jet_pos (j : ℕ) (hj : 1 ≤ j) : ∃ C : ℝ, 0 < C ∧ ∀ z : Space, z ∉ Axi.axis →
    ‖iteratedFDeriv ℝ j Axi.frameL z‖ ≤ C * ((Axi.ϱ z)⁻¹) ^ j := by
  choose C hC0 hC using varrho_inv_jet
  set Cs : ℝ := ∑ i ∈ Finset.range (j + 1), C i with hCs
  have hCs0 : 0 < Cs := Finset.sum_pos (fun i _ => hC0 i) ⟨0, by simp⟩
  have hCle : ∀ i ∈ Finset.range (j + 1), C i ≤ Cs :=
    fun i hi => Finset.single_le_sum (f := C) (fun k _ => (hC0 k).le) hi
  refine ⟨(j + 1) * 2 ^ j * Cs * (1 + ‖Phi‖) + 1, by positivity, fun z hz => ?_⟩
  have hopen := Axi.isOpen_compl_axis
  have hzc : z ∈ Axi.axisᶜ := hz
  have hϱ : 0 < Axi.ϱ z := Axi.ϱ_pos hz
  set t := (Axi.ϱ z)⁻¹ with ht
  have ht0 : 0 < t := inv_pos.2 hϱ
  have htϱ : t * Axi.ϱ z = 1 := inv_mul_cancel₀ hϱ.ne'
  have hfC : ContDiffOn ℝ ∞ (fun w : Space => (Axi.ϱ w)⁻¹) Axi.axisᶜ :=
    Axi.contDiffOn_ϱ.inv fun _ hy => Axi.ϱ_ne_zero hy
  have hPC : ContDiffOn ℝ ∞ (fun w : Space => Phi w) Axi.axisᶜ := Phi.contDiff.contDiffOn
  have hsm : ContDiffOn ℝ ∞ (fun w : Space => (Axi.ϱ w)⁻¹ • Phi w) Axi.axisᶜ := hfC.smul hPC
  have hframe : Axi.frameL = (fun w : Space => (Axi.ϱ w)⁻¹ • Phi w) + fun _ => Psi :=
    funext frameL_eq
  have hj0 : j ≠ 0 := by omega
  have hD : iteratedFDeriv ℝ j Axi.frameL z =
      iteratedFDerivWithin ℝ j (fun w : Space => (Axi.ϱ w)⁻¹ • Phi w) Axi.axisᶜ z := by
    rw [hframe, ← iteratedFDerivWithin_of_isOpen j hopen hzc,
      iteratedFDerivWithin_add_apply
        ((hsm.contDiffWithinAt hzc).of_le (by exact_mod_cast le_top)) contDiffWithinAt_const
        hopen.uniqueDiffOn hzc, iteratedFDerivWithin_const_of_ne hj0 Psi, Pi.zero_apply, add_zero]
  have hleib := norm_iteratedFDerivWithin_smul_le hfC hPC hopen.uniqueDiffOn hzc
    (n := j) (by exact_mod_cast le_top)
  have hphi : ∀ m : ℕ, ‖iteratedFDerivWithin ℝ m (fun w : Space => Phi w) Axi.axisᶜ z‖ ≤
      (if m = 0 then Axi.ϱ z else if m = 1 then ‖Phi‖ else 0) := by
    intro m
    rw [iteratedFDerivWithin_of_isOpen m hopen hzc]
    match m with
    | 0 => simp only [norm_iteratedFDeriv_zero, if_true]; exact norm_Phi_le z
    | 1 => simpa using clm_jet_one Phi z
    | m + 2 =>
      have := clm_jet_ge_two Phi m z
      simp only [show m + 2 ≠ 0 by omega, show m + 2 ≠ 1 by omega, ite_false]
      rw [show (fun w : Space => Phi w) = ⇑Phi from rfl, this]; simp
  have hfj : ∀ i : ℕ, i ≤ j → ‖iteratedFDerivWithin ℝ i (fun w : Space => (Axi.ϱ w)⁻¹) Axi.axisᶜ z‖
      ≤ Cs * t ^ (i + 1) := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen i hopen hzc]
    exact (hC i z hz).trans (mul_le_mul_of_nonneg_right
      (hCle i (Finset.mem_range.2 (by omega))) (by positivity))
  have hterm : ∀ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i (fun w : Space => (Axi.ϱ w)⁻¹) Axi.axisᶜ z‖ *
        ‖iteratedFDerivWithin ℝ (j - i) (fun w : Space => Phi w) Axi.axisᶜ z‖ ≤
        2 ^ j * Cs * (1 + ‖Phi‖) * t ^ j := by
    intro i hi
    have hij : i ≤ j := by have := Finset.mem_range.1 hi; omega
    have hch : (j.choose i : ℝ) ≤ 2 ^ j := by exact_mod_cast Nat.choose_le_two_pow j i
    have h1 := hfj i hij
    have h2 := hphi (j - i)
    have hP : 0 ≤ ‖Phi‖ := ContinuousLinearMap.opNorm_nonneg Phi
    have hpow : 0 ≤ t ^ j := by positivity
    have hnn1 : 0 ≤ ‖iteratedFDerivWithin ℝ i (fun w : Space => (Axi.ϱ w)⁻¹) Axi.axisᶜ z‖ :=
      norm_nonneg _
    have hnn2 : 0 ≤ ‖iteratedFDerivWithin ℝ (j - i) (fun w : Space => Phi w) Axi.axisᶜ z‖ :=
      norm_nonneg _
    have hbd : ‖iteratedFDerivWithin ℝ i (fun w : Space => (Axi.ϱ w)⁻¹) Axi.axisᶜ z‖ *
        ‖iteratedFDerivWithin ℝ (j - i) (fun w : Space => Phi w) Axi.axisᶜ z‖ ≤
        Cs * (1 + ‖Phi‖) * t ^ j := by
      by_cases h0 : j - i = 0
      · have hi' : i = j := by omega
        subst hi'
        rw [if_pos h0] at h2
        calc _ ≤ (Cs * t ^ (i + 1)) * Axi.ϱ z := mul_le_mul h1 h2 hnn2 (by positivity)
          _ = Cs * t ^ i * (t * Axi.ϱ z) := by ring
          _ = Cs * t ^ i := by rw [htϱ, mul_one]
          _ ≤ _ := by nlinarith [mul_nonneg hCs0.le (pow_nonneg ht0.le i)]
      · by_cases h1' : j - i = 1
        · have hi' : i + 1 = j := by omega
          rw [if_neg h0, if_pos h1'] at h2
          calc _ ≤ (Cs * t ^ (i + 1)) * ‖Phi‖ := mul_le_mul h1 h2 hnn2 (by positivity)
            _ = Cs * t ^ j * ‖Phi‖ := by rw [hi']
            _ ≤ _ := by nlinarith [mul_nonneg hCs0.le hpow]
        · rw [if_neg h0, if_neg h1'] at h2
          have : ‖iteratedFDerivWithin ℝ (j - i) (fun w : Space => Phi w) Axi.axisᶜ z‖ = 0 :=
            le_antisymm h2 hnn2
          rw [this, mul_zero]; positivity
    calc _ = (j.choose i : ℝ) * (‖iteratedFDerivWithin ℝ i (fun w : Space => (Axi.ϱ w)⁻¹)
          Axi.axisᶜ z‖ * ‖iteratedFDerivWithin ℝ (j - i) (fun w : Space => Phi w) Axi.axisᶜ z‖) := by
          ring
      _ ≤ 2 ^ j * (Cs * (1 + ‖Phi‖) * t ^ j) :=
          mul_le_mul hch hbd (by positivity) (by positivity)
      _ = _ := by ring
  have hsum := (Finset.sum_le_card_nsmul _ _ _ hterm)
  rw [Finset.card_range, nsmul_eq_mul] at hsum
  rw [hD]
  calc _ ≤ _ := hleib
    _ ≤ _ := hsum
    _ ≤ _ := by
        have : 0 ≤ ((j : ℝ) + 1) * 2 ^ j * Cs * (1 + ‖Phi‖) * t ^ j := by positivity
        push_cast
        nlinarith [pow_nonneg ht0.le j]

/-- Jets of the frame of every order `j`. -/
theorem frameL_jet (j : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ z : Space, z ∉ Axi.axis →
    ‖iteratedFDeriv ℝ j Axi.frameL z‖ ≤ C * ((Axi.ϱ z)⁻¹) ^ j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · refine ⟨2, by norm_num, fun z hz => ?_⟩
    rw [norm_iteratedFDeriv_zero, pow_zero, mul_one]
    refine (ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun v => ?_)
    rw [Axi.norm_frameL hz]; linarith [norm_nonneg v]
  · exact frameL_jet_pos j hj

end UnforcedLeray.Short.IIb.SqrtFrameJetsAux
