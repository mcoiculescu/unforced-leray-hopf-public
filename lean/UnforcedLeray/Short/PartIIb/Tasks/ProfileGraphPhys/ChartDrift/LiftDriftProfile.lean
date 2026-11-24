import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ChartDrift.Lift
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ChartDrift.PerSmooth
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ChartDrift.PerVanish
import UnforcedLeray.Short.PartIIb.Tasks.HilbertEnergy.SPeriodic

/-!
# `PartII-b:T10/6/3/1/3a`: the drift of the lift is the lift of `Sᵗφ + φ/2`

Target `liftDriftProfile_proof : UnforcedLeray.Short.IIb.ChartLift.LiftDriftProfile`.

Pointwise: `driftTest φ = -φ/2 - s ∂_s φ` (`coordTranspose_vS_eq`). The `q`-periodization is a
locally finite sum of shifts `φ(· + a_k)`, so `∂_s` commutes with it (`ldp_fderiv`). The identity
then reduces to the real identity `κ A (-(P/2) - s Q) = (3/2) κ A P - (s κ((3/2) B P + A Q) + κ A P/2)`
with `A = s^{3/2}`, `B = s^{3/2 - 1}`, `s B = A` for `s > 0`; for `s ≤ 0` everything vanishes.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb.ChartLift

open UnforcedLeray.Short.IIb

/-- The `q`-shift by `k c`, as a translation of `Coord`. -/
def ldpShift (c : ℝ) (k : ℤ) : Coord := (0, ((k : ℝ) * c, 0))

lemma ldp_shift_fst (c : ℝ) (k : ℤ) (x : Coord) : (x + ldpShift c k).1 = x.1 := by
  simp [ldpShift]

lemma ldp_shift_snd (c : ℝ) (k : ℤ) (x : Coord) :
    (x + ldpShift c k).2.1 = x.2.1 + (k : ℝ) * c := by
  simp [ldpShift]

lemma ldp_tk_eq (c : ℝ) (k : ℤ) (x : Coord) :
    (x.1, (x.2.1 + (k : ℝ) * c, x.2.2)) = x + ldpShift c k := by
  ext <;> simp [ldpShift]

lemma ldp_tsum_eq_sum (ψ : Coord → ℝ) (c : ℝ) (x : Coord) (N : ℕ)
    (h : ∀ k : ℤ, k ∉ Finset.Icc (-(N:ℤ)) (N:ℤ) → ψ (x + ldpShift c k) = 0) :
    perCoord c ψ x = ∑ k ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), ψ (x + ldpShift c k) := by
  have hz : ∀ k : ℤ, k ∉ Finset.Icc (-(N:ℤ)) (N:ℤ) →
      ψ (x.1, (x.2.1 + (k:ℝ) * c, x.2.2)) = 0 :=
    fun k hk => by rw [ldp_tk_eq]; exact h k hk
  unfold perCoord
  rw [tsum_eq_sum hz]
  exact Finset.sum_congr rfl fun k _ => by rw [ldp_tk_eq]

lemma ldp_bound (φ : Coord → ℝ) (hφ : IsCoordTest φ) :
    ∃ Q : ℝ, ∀ y : Coord, φ y ≠ 0 → |y.2.1| ≤ Q := by
  have hK : IsCompact (tsupport φ) := hφ.compact
  obtain ⟨Q, hQ⟩ := (hK.image (continuous_fst.comp continuous_snd)).isBounded.exists_norm_le
  refine ⟨Q, fun y hy => ?_⟩
  have h := hQ (y.2.1) ⟨y, subset_tsupport φ hy, rfl⟩
  rw [Real.norm_eq_abs] at h
  exact h

lemma ldp_vanish (φ : Coord → ℝ) (z : Coord) (hev : φ =ᶠ[𝓝 z] fun _ => (0 : ℝ)) :
    φ z = 0 ∧ cpd 0 φ z = 0 := by
  refine ⟨hev.self_of_nhds, ?_⟩
  unfold cpd
  rw [hev.fderiv_eq]
  simp

lemma ldp_zero_far (φ : Coord → ℝ) {Q : ℝ} (hQ : ∀ y : Coord, φ y ≠ 0 → |y.2.1| ≤ Q)
    (z : Coord) (hz : Q < |z.2.1|) : φ z = 0 ∧ cpd 0 φ z = 0 := by
  have hopen : IsOpen {y : Coord | Q < |y.2.1|} :=
    isOpen_lt continuous_const (continuous_abs.comp (continuous_fst.comp continuous_snd))
  apply ldp_vanish
  filter_upwards [hopen.mem_nhds hz] with y hy
  by_contra h
  exact absurd (hQ y h) (not_le.mpr hy)

lemma ldp_zero_left (φ : Coord → ℝ) (hφ : IsCoordTest φ) (z : Coord) (hz : z.1 ≤ 0) :
    φ z = 0 ∧ cpd 0 φ z = 0 := by
  apply ldp_vanish
  have hnot : z ∉ tsupport φ := fun h => by
    have h1 : (0:ℝ) < z.1 := (hφ.supp h).1
    linarith
  exact notMem_tsupport_iff_eventuallyEq.mp hnot

lemma ldp_far (φ : Coord → ℝ) (hφ : IsCoordTest φ) {c : ℝ} (hc : 0 < c) (x0 : Coord) :
    ∃ N : ℕ, ∀ x : Coord, |x.2.1| < |x0.2.1| + 1 → ∀ k : ℤ, k ∉ Finset.Icc (-(N:ℤ)) (N:ℤ) →
      φ (x + ldpShift c k) = 0 ∧ cpd 0 φ (x + ldpShift c k) = 0 := by
  obtain ⟨Q, hQ⟩ := ldp_bound φ hφ
  obtain ⟨N, hN⟩ := exists_nat_ge ((Q + |x0.2.1| + 1) / c)
  refine ⟨N, fun x hx k hk => ?_⟩
  have hNc : Q + |x0.2.1| + 1 ≤ (N:ℝ) * c := by
    have h := (div_le_iff₀ hc).mp hN
    linarith
  have hxa := abs_lt.mp hx
  have hk2 : k ≤ -(N:ℤ) - 1 ∨ (N:ℤ) + 1 ≤ k := by
    simp only [Finset.mem_Icc] at hk
    omega
  apply ldp_zero_far φ hQ
  rw [ldp_shift_snd]
  rcases hk2 with h | h
  · have hkR : (k:ℝ) ≤ -(N:ℝ) - 1 := by exact_mod_cast h
    have hkc : (k:ℝ) * c ≤ (-(N:ℝ) - 1) * c := mul_le_mul_of_nonneg_right hkR hc.le
    have h3 : (-(N:ℝ) - 1) * c = -((N:ℝ) * c) - c := by ring
    apply lt_abs.mpr
    right
    linarith [hxa.1, hxa.2]
  · have hkR : (N:ℝ) + 1 ≤ (k:ℝ) := by exact_mod_cast h
    have hkc : ((N:ℝ) + 1) * c ≤ (k:ℝ) * c := mul_le_mul_of_nonneg_right hkR hc.le
    have h3 : ((N:ℝ) + 1) * c = (N:ℝ) * c + c := by ring
    apply lt_abs.mpr
    left
    linarith [hxa.1, hxa.2]

lemma ldp_perCoord_zero_left (φ : Coord → ℝ) (hφ : IsCoordTest φ) (c : ℝ) (x : Coord)
    (hx : x.1 ≤ 0) : perCoord c φ x = 0 ∧ perCoord c (cpd 0 φ) x = 0 := by
  refine ⟨?_, ?_⟩
  · unfold perCoord
    have h : ∀ k : ℤ, φ (x.1, (x.2.1 + (k:ℝ) * c, x.2.2)) = 0 :=
      fun k => (ldp_zero_left φ hφ (x.1, (x.2.1 + (k:ℝ) * c, x.2.2)) hx).1
    simp only [h, tsum_zero]
  · unfold perCoord
    have h : ∀ k : ℤ, cpd 0 φ (x.1, (x.2.1 + (k:ℝ) * c, x.2.2)) = 0 :=
      fun k => (ldp_zero_left φ hφ (x.1, (x.2.1 + (k:ℝ) * c, x.2.2)) hx).2
    simp only [h, tsum_zero]

/-- `∂_s` commutes with the `q`-periodization (locally finite sum of shifts). -/
lemma ldp_fderiv (φ : Coord → ℝ) (hφ : IsCoordTest φ) {c : ℝ} (hc : 0 < c) (x0 : Coord) :
    fderiv ℝ (perCoord c φ) x0 (cdir 0) = perCoord c (cpd 0 φ) x0 := by
  obtain ⟨N, hN⟩ := ldp_far φ hφ hc x0
  have hx0 : |x0.2.1| < |x0.2.1| + 1 := by linarith
  have hU : {x : Coord | |x.2.1| < |x0.2.1| + 1} ∈ 𝓝 x0 := by
    apply IsOpen.mem_nhds
    · exact isOpen_lt (continuous_abs.comp (continuous_fst.comp continuous_snd)) continuous_const
    · exact hx0
  have hφd : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
  have hEv : perCoord c φ =ᶠ[𝓝 x0]
      fun x => ∑ k ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), φ (x + ldpShift c k) := by
    filter_upwards [hU] with x hx
    exact ldp_tsum_eq_sum φ c x N (fun k hk => (hN x hx k hk).1)
  have hdiff : ∀ k : ℤ, DifferentiableAt ℝ (fun x : Coord => φ (x + ldpShift c k)) x0 :=
    fun k => (hφd (x0 + ldpShift c k)).comp x0 (differentiableAt_id.add_const _)
  rw [hEv.fderiv_eq, fderiv_fun_sum (fun k _ => hdiff k), ContinuousLinearMap.sum_apply,
    ldp_tsum_eq_sum (cpd 0 φ) c x0 N (fun k hk => (hN x0 hx0 k hk).2)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [fderiv_comp_add_right]
  rfl

lemma driftTest_eq (φ : Coord → ℝ) (hφ : IsCoordTest φ) (y : Coord) :
    driftTest φ y = -(1/2 : ℝ) * φ y - y.1 * cpd 0 φ y := by
  show coordTranspose vS dZero φ y + (1/2 : ℝ) * φ y = _
  rw [coordTranspose_vS_eq hφ.smooth y]
  ring

/-- Pointwise: the periodization of the drift test. -/
lemma ldp_perCoord_drift (φ : Coord → ℝ) (hφ : IsCoordTest φ) {c : ℝ} (hc : 0 < c) (x : Coord) :
    perCoord c (driftTest φ) x = -(1/2 : ℝ) * perCoord c φ x - x.1 * perCoord c (cpd 0 φ) x := by
  obtain ⟨N, hN⟩ := ldp_far φ hφ hc x
  have hx : |x.2.1| < |x.2.1| + 1 := by linarith
  have hz : ∀ k : ℤ, k ∉ Finset.Icc (-(N:ℤ)) (N:ℤ) → driftTest φ (x + ldpShift c k) = 0 := by
    intro k hk
    rw [driftTest_eq φ hφ, (hN x hx k hk).1, (hN x hx k hk).2]
    ring
  rw [ldp_tsum_eq_sum (driftTest φ) c x N hz,
    ldp_tsum_eq_sum φ c x N (fun k hk => (hN x hx k hk).1),
    ldp_tsum_eq_sum (cpd 0 φ) c x N (fun k hk => (hN x hx k hk).2)]
  simp only [driftTest_eq φ hφ, ldp_shift_fst, Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- The `s`-derivative of the lift profile. -/
lemma ldp_liftB_fderiv (φ : Coord → ℝ) (hφ : IsCoordTest φ) {c ε : ℝ} (hc : 0 < c) (i : Fin 2)
    (x : Coord) :
    fderiv ℝ (liftB c ε φ i) x (cdir 0) =
      ((c * ε ^ 2 / Real.pi * ((3:ℝ)/2 * x.1 ^ ((3:ℝ)/2 - 1) * perCoord c φ x +
        x.1 ^ ((3:ℝ)/2) * perCoord c (cpd 0 φ) x) : ℝ) : ℂ) •
        (EuclideanSpace.single i (1:ℂ) : CMerid) := by
  have hfst : HasFDerivAt (fun y : Coord => y.1) (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) x :=
    hasFDerivAt_fst
  have hs := hfst.rpow_const (Or.inr (show (1:ℝ) ≤ (3:ℝ)/2 by norm_num))
  have hP : HasFDerivAt (perCoord c φ) (fderiv ℝ (perCoord c φ) x) x :=
    ((perSmooth_proof c φ hc hφ).differentiable (by simp) x).hasFDerivAt
  have hg := (hs.const_mul (c * ε ^ 2 / Real.pi)).mul hP
  have hcoe := Complex.ofRealCLM.hasFDerivAt.comp x hg
  have hfull := hcoe.smul_const (EuclideanSpace.single i (1:ℂ) : CMerid)
  have hLB := (hfull : HasFDerivAt (liftB c ε φ i) _ x)
  have hd : fderiv ℝ (liftB c ε φ i) x = _ := hLB.fderiv
  rw [hd]
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, Complex.ofRealCLM_apply,
    Function.comp_apply, smul_eq_mul]
  rw [ldp_fderiv φ hφ hc x]
  simp [cdir] <;> ring

/-- **Leaf `T10/6/3/1/3a`**: the profile of `Sᵗφ + φ/2` is `(3/2) B - (s ∂_s B + B/2)`. -/
theorem liftDriftProfile_proof : UnforcedLeray.Short.IIb.ChartLift.LiftDriftProfile := by
  intro c ε φ i hc hφ
  funext x
  rw [ldp_liftB_fderiv φ hφ hc i x]
  unfold liftB
  rw [ldp_perCoord_drift φ hφ hc x]
  by_cases hs : 0 < x.1
  · have hB : x.1 * x.1 ^ ((3:ℝ)/2 - 1) = x.1 ^ ((3:ℝ)/2) := by
      rw [Real.rpow_sub_one hs.ne']
      field_simp
    have hBc : (x.1 : ℂ) * ((x.1 ^ ((3:ℝ)/2 - 1) : ℝ) : ℂ) = ((x.1 ^ ((3:ℝ)/2) : ℝ) : ℂ) := by
      exact_mod_cast hB
    simp only [← Complex.coe_smul, smul_smul, ← add_smul, ← sub_smul]
    congr 1
    push_cast
    linear_combination (3/2 : ℂ) * ((c : ℂ) * (ε : ℂ) ^ 2 / (Real.pi : ℂ)) *
      (perCoord c φ x : ℂ) * hBc
  · have hx : x.1 ≤ 0 := not_lt.mp hs
    obtain ⟨h0, h1⟩ := ldp_perCoord_zero_left φ hφ c x hx
    simp [h0, h1]

end UnforcedLeray.Short.IIb.ChartLift
