import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_11_3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.PsipADiff.Phi
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.PsipADiff.XPart
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.PsipADiff.SPart

/-!
# `PartIII-b:C/inst/11/3/4`: `HAcKopEq`

Source `the November 2 reference manuscript`
lines 4973-4980 (the lattice sums), 4741-4745.

`psipAC ν t M x` is a lattice sum `∑ₙ Φ_{t,M}(xₙ)` and linear in the matrix `M` through its four
meridional entries.  For a constant matrix, `t ↦ psipAC ν t M x` has the explicit derivative
`∑ₙ sV ν xₙ M 0 t` (`sV_hasDerivAt`, `hasDerivAt_tsum_of_isPreconnected`); then the product rule
at the single point `s` gives `HAcKopEq` (only differentiability of `C` at `s` is used).
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The elementary matrix with a single entry `1` at `(a, b)`. -/
def Eab (a b : Fin 3) : Mat3 := fun i j => if i = a ∧ j = b then 1 else 0

theorem psipAC_eq_sum (ν s : ℝ) (M : Mat3) (x : ℝ × ℝ) :
    psipAC ν s M x = ∑' j : ℤ, psiPhi ν s M (xj ν j x) := by
  unfold psipAC
  refine tsum_congr fun j => ?_
  unfold psiPhi
  rw [gp_fderiv_psij]
  unfold psij
  ring

theorem psiPhi_lin (ν t : ℝ) (M : Mat3) (y : ℝ × ℝ) :
    psiPhi ν t M y = M 0 0 * psiPhi ν t (Eab 0 0) y + M 0 2 * psiPhi ν t (Eab 0 2) y
      + M 2 0 * psiPhi ν t (Eab 2 0) y + M 2 2 * psiPhi ν t (Eab 2 2) y := by
  simp [psiPhi, merTrace, merApply, Eab]
  ring

theorem psiPhi_summable (ν t : ℝ) (M : Mat3) (x : ℝ × ℝ) (hν : 0 < ν) (ht : 0 < t) :
    Summable (fun n : ℤ => psiPhi ν t M (xj ν n x)) := by
  have ha1 : 1 ≤ ageA ν t := by unfold ageA; nlinarith [mul_pos hν ht]
  have hα : 0 < 1 / (4 * ageA ν t) := div_pos one_pos (by linarith)
  have hc : 0 < cOf ν := by unfold cOf; exact inv_pos.mpr (pow_pos hν 2)
  have hK := Kmat_nonneg M
  have hu : Summable (fun n : ℤ => 2 * Kmat M * (1 + |x.2|) ^ 4 *
      ((1 + |x.1 - (n : ℝ) * cOf ν|) ^ 4 *
        Real.exp (-(1 / (4 * ageA ν t)) * (x.1 - (n : ℝ) * cOf ν) ^ 2))) :=
    (sp_poly4_summable x.1 (1 / (4 * ageA ν t)) (cOf ν) hα hc).mul_left
      (2 * Kmat M * (1 + |x.2|) ^ 4)
  refine Summable.of_norm_bounded hu (fun n => ?_)
  rw [Real.norm_eq_abs]
  have h1 := psiPhi_abs_le ν t ha1 M (xj ν n x)
  have hR1 : (1:ℝ) ≤ 1 + ‖xj ν n x‖ := by linarith [norm_nonneg (xj ν n x)]
  have hR3 : (1 + ‖xj ν n x‖) ^ 3 ≤ (1 + ‖xj ν n x‖) ^ 4 :=
    pow_le_pow_right₀ hR1 (by norm_num)
  have hE : 0 ≤ Real.exp (-(sq2 (xj ν n x)) / (4 * ageA ν t)) := (Real.exp_pos _).le
  have hM := sp_major ν t (ageA ν t) (2 * Kmat M) (2 * Kmat M) x n ha1 le_rfl (by linarith)
    le_rfl (by linarith)
  calc |psiPhi ν t M (xj ν n x)|
      ≤ 2 * Kmat M * ((1 + ‖xj ν n x‖) ^ 3 *
          Real.exp (-(sq2 (xj ν n x)) / (4 * ageA ν t))) := h1
    _ ≤ 2 * Kmat M * ((1 + ‖xj ν n x‖) ^ 4 *
          Real.exp (-(sq2 (xj ν n x)) / (4 * ageA ν t))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hR3 hE) (by linarith)
    _ = 2 * Kmat M * (1 + ‖xj ν n x‖) ^ 4 *
          Real.exp (-(sq2 (xj ν n x)) / (4 * ageA ν t)) := by ring
    _ ≤ _ := hM

/-- `psipAC` is linear in the matrix (four meridional entries). -/
theorem psipAC_lin (ν t : ℝ) (hν : 0 < ν) (ht : 0 < t) (M : Mat3) (x : ℝ × ℝ) :
    psipAC ν t M x = M 0 0 * psipAC ν t (Eab 0 0) x + M 0 2 * psipAC ν t (Eab 0 2) x
      + M 2 0 * psipAC ν t (Eab 2 0) x + M 2 2 * psipAC ν t (Eab 2 2) x := by
  simp only [psipAC_eq_sum]
  have h1 := (psiPhi_summable ν t (Eab 0 0) x hν ht).mul_left (M 0 0)
  have h2 := (psiPhi_summable ν t (Eab 0 2) x hν ht).mul_left (M 0 2)
  have h3 := (psiPhi_summable ν t (Eab 2 0) x hν ht).mul_left (M 2 0)
  have h4 := (psiPhi_summable ν t (Eab 2 2) x hν ht).mul_left (M 2 2)
  rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left,
    ← h1.tsum_add h2, ← (h1.add h2).tsum_add h3, ← ((h1.add h2).add h3).tsum_add h4]
  exact tsum_congr fun n => psiPhi_lin ν t M _

/-- For a constant matrix, `t ↦ psipAC ν t M x` is differentiable with the explicit derivative. -/
theorem psipAC_hasDerivAt (ν s : ℝ) (hν : 0 < ν) (hs : 0 < s) (M : Mat3) (x : ℝ × ℝ) :
    HasDerivAt (fun t => psipAC ν t M x) (∑' n : ℤ, sV ν (xj ν n x) M 0 s) s := by
  set K1 : ℝ := ‖M‖ with hK1def
  have hK1nn : 0 ≤ K1 := norm_nonneg _
  have hMb : ∀ i j, |M i j| ≤ K1 := fun i j => sp_entry_le _ i j
  have hDb : ∀ i j, |(0 : Mat3) i j| ≤ 0 := fun i j => by simp
  have hPm : ∀ t ∈ Ioo (s / 2) (2 * s), ageA ν t ≤ 1 + ν * (2 * s) := by
    intro t ht
    unfold ageA
    nlinarith [mul_le_mul_of_nonneg_left ht.2.le hν.le]
  have hα : 0 < 1 / (4 * (1 + ν * (2 * s))) := by
    have := mul_pos hν hs
    exact div_pos one_pos (by linarith)
  have hc : 0 < cOf ν := by unfold cOf; exact inv_pos.mpr (pow_pos hν 2)
  have hC1nn : 0 ≤ 10 * ν * K1 + 8 * K1 := by
    have h1 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 10) hν.le) hK1nn
    linarith
  have hu : Summable (fun n : ℤ => (10 * ν * K1 + 8 * K1) * (1 + |x.2|) ^ 4 *
      ((1 + |x.1 - (n : ℝ) * cOf ν|) ^ 4 *
        Real.exp (-(1 / (4 * (1 + ν * (2 * s)))) * (x.1 - (n : ℝ) * cOf ν) ^ 2))) :=
    (sp_poly4_summable x.1 (1 / (4 * (1 + ν * (2 * s)))) (cOf ν) hα hc).mul_left
      ((10 * ν * K1 + 8 * K1) * (1 + |x.2|) ^ 4)
  have hbound : ∀ (n : ℤ) (τ : ℝ), τ ∈ Ioo (s / 2) (2 * s) →
      ‖sV ν (xj ν n x) M 0 τ‖ ≤
        (10 * ν * K1 + 8 * K1) * (1 + |x.2|) ^ 4 *
          ((1 + |x.1 - (n : ℝ) * cOf ν|) ^ 4 *
            Real.exp (-(1 / (4 * (1 + ν * (2 * s)))) * (x.1 - (n : ℝ) * cOf ν) ^ 2)) := by
    intro n τ hτ
    have hτ0 : 0 < τ := by linarith [hτ.1]
    have h1 := sV_bound ν hν (xj ν n x) K1 0 M 0 τ hτ0 hMb hDb
    rw [Real.norm_eq_abs]
    refine (le_of_eq_of_le (by ring_nf) h1).trans ?_
    have ha1τ : 1 ≤ ageA ν τ := by unfold ageA; nlinarith [mul_pos hν hτ0]
    exact sp_major ν τ (1 + ν * (2 * s)) (10 * ν * K1 + 8 * K1) (10 * ν * K1 + 8 * 0)
      x n ha1τ (hPm τ hτ) (by nlinarith [mul_nonneg hν.le hK1nn])
      (by linarith) hC1nn
  have hdiff : ∀ (n : ℤ) (τ : ℝ), τ ∈ Ioo (s / 2) (2 * s) →
      HasDerivAt (fun τ' => psiPhi ν τ' M (xj ν n x)) (sV ν (xj ν n x) M 0 τ) τ := by
    intro n τ hτ
    have hτ0 : 0 < τ := by linarith [hτ.1]
    exact sV_hasDerivAt ν hν (xj ν n x) (fun _ => M) 0 τ hτ0 (hasDerivAt_const τ M)
  have hg0 := psiPhi_summable ν s M x hν hs
  have key := hasDerivAt_tsum_of_isPreconnected
    (g := fun n τ => psiPhi ν τ M (xj ν n x))
    (g' := fun n τ => sV ν (xj ν n x) M 0 τ)
    (u := fun n : ℤ => (10 * ν * K1 + 8 * K1) * (1 + |x.2|) ^ 4 *
      ((1 + |x.1 - (n : ℝ) * cOf ν|) ^ 4 *
        Real.exp (-(1 / (4 * (1 + ν * (2 * s)))) * (x.1 - (n : ℝ) * cOf ν) ^ 2)))
    (t := Ioo (s / 2) (2 * s)) (y₀ := s) (y := s)
    hu isOpen_Ioo isPreconnected_Ioo
    (fun n τ hτ => hdiff n τ hτ) (fun n τ hτ => hbound n τ hτ)
    ⟨by linarith, by linarith⟩ hg0 ⟨by linarith, by linarith⟩
  refine key.congr_of_eventuallyEq ?_
  filter_upwards with t
  exact psipAC_eq_sum ν t M x

/-- `HAcKopEq` (source 4978, 4973-4975, 4741-4745). -/
theorem hAcKopEq : HAcKopEq := by
  unfold HAcKopEq
  intro ν s hν hs C hC x
  have hCd : HasDerivAt C (deriv C s) s := hC.hasDerivAt
  set G : Fin 3 → Fin 3 → ℝ → ℝ := fun a b t => psipAC ν t (Eab a b) x with hGdef
  have hG : ∀ a b, HasDerivAt (G a b) (∑' n : ℤ, sV ν (xj ν n x) (Eab a b) 0 s) s :=
    fun a b => psipAC_hasDerivAt ν s hν hs (Eab a b) x
  have hCe : ∀ a b, HasDerivAt (fun t => C t a b) (deriv C s a b) s :=
    fun a b => sp_entry_hasDerivAt hCd a b
  have hev : ∀ᶠ t in nhds s, 0 < t := Ioi_mem_nhds hs
  -- derivative of `t ↦ psipAC ν t (C t) x`
  have hΨ : HasDerivAt (fun t => psipAC ν t (C t) x)
      ((deriv C s 0 0 * G 0 0 s + C s 0 0 * (∑' n : ℤ, sV ν (xj ν n x) (Eab 0 0) 0 s))
        + (deriv C s 0 2 * G 0 2 s + C s 0 2 * (∑' n : ℤ, sV ν (xj ν n x) (Eab 0 2) 0 s))
        + (deriv C s 2 0 * G 2 0 s + C s 2 0 * (∑' n : ℤ, sV ν (xj ν n x) (Eab 2 0) 0 s))
        + (deriv C s 2 2 * G 2 2 s + C s 2 2 * (∑' n : ℤ, sV ν (xj ν n x) (Eab 2 2) 0 s))) s := by
    have h := (((hCe 0 0).mul (hG 0 0)).add ((hCe 0 2).mul (hG 0 2))).add
      (((hCe 2 0).mul (hG 2 0)).add ((hCe 2 2).mul (hG 2 2)))
    refine (h.congr_of_eventuallyEq ?_).congr_deriv (by ring)
    filter_upwards [hev] with t ht
    rw [psipAC_lin ν t hν ht (C t) x]
    simp only [hGdef, Pi.add_apply, Pi.mul_apply]
    ring
  -- derivative of `t ↦ psipAC ν t (C s) x`
  have hF : HasDerivAt (fun t => psipAC ν t (C s) x)
      (C s 0 0 * (∑' n : ℤ, sV ν (xj ν n x) (Eab 0 0) 0 s)
        + C s 0 2 * (∑' n : ℤ, sV ν (xj ν n x) (Eab 0 2) 0 s)
        + C s 2 0 * (∑' n : ℤ, sV ν (xj ν n x) (Eab 2 0) 0 s)
        + C s 2 2 * (∑' n : ℤ, sV ν (xj ν n x) (Eab 2 2) 0 s)) s := by
    have h := (((hG 0 0).const_mul (C s 0 0)).add ((hG 0 2).const_mul (C s 0 2))).add
      (((hG 2 0).const_mul (C s 2 0)).add ((hG 2 2).const_mul (C s 2 2)))
    refine (h.congr_of_eventuallyEq ?_).congr_deriv (by ring)
    filter_upwards [hev] with t ht
    rw [psipAC_lin ν t hν ht (C s) x]
    simp only [hGdef, Pi.add_apply, Pi.mul_apply]
    ring
  have hlin := psipAC_lin ν s hν hs (deriv C s) x
  have hsm : psipAC ν s (sDeriv C s) x = s * psipAC ν s (deriv C s) x := by
    rw [psipAC_lin ν s hν hs (sDeriv C s) x, hlin]
    simp only [sDeriv, Pi.smul_apply, smul_eq_mul]
    ring
  unfold Kop KopC
  rw [hΨ.deriv, hF.deriv, hsm]
  simp only [hGdef] at hlin ⊢
  rw [hlin]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
