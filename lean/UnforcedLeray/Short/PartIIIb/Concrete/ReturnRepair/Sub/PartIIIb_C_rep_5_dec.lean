import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Estimates

/-!
# `PartIII-b:C/rep/5`: `ageVelocity` reduced to two leaves

Source `the November 2 reference manuscript` 5569-5605, 5618-5619.  `AgeVelocityAt`
is the conjunction of the far thin-source velocity bound (5585-5600, margin `e^{(γ/10+ω_b+3m₀/2)/ν}`)
and the repair-source velocity bound (5601-5605, margin `31γ/165`).  The S-degree `k₀`
(`ω_b = k₀ b γ/3`) depends only on `Pl, σ₀, m_Z, dm, dp`, as in `C/rep/4`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace SeqData

/-- Far thin-source velocity (5585-5600): `‖ageVel (thinPart T)‖ ≤ P_ν e^{(γ/10+ω_b+3m₀/2)/ν}‖T‖`. -/
def AgeVelThinAt (D : SeqData) (ωb : ℝ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ∀ T : LStr D.Pl D.K (D.level n),
      ‖ageVel D.Pl D.K (D.level n) (D.mu n z) (thinPart T)‖ ≤
        C * (D.level n).ν⁻¹ ^ k *
          Real.exp ((gRate D.Pl / 10 + ωb + 3 * D.K.m0 / 2) / (D.level n).ν) * ‖T‖

/-- Repair-source velocity (5601-5605): margin `31γ/165` (Young `L^{22/19} → L²`). -/
def AgeVelRepAt (D : SeqData) (ωb : ℝ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ∀ w : LVel D.Pl (D.level n),
      ‖ageVel D.Pl D.K (D.level n) (D.mu n z) (repPart (multOp D.Pl D.K (D.level n) w))‖ ≤
        C * (D.level n).ν⁻¹ ^ k *
          Real.exp (-(31 * gRate D.Pl / 165 - ωb - 3 * D.K.m0 / 2) / (D.level n).ν) * ‖w‖

end SeqData

/-- Leaf 1 (far thin velocity). -/
def AgeVelThin (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∃ k₀ : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ → D.RepairStanding dm dp →
    D.AgeVelThinAt ((k₀ : ℝ) * D.K.b * (gRate D.Pl / 3))

/-- Leaf 2 (repair-source velocity). -/
def AgeVelRep (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∃ k₀ : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ → D.RepairStanding dm dp →
    D.AgeVelRepAt ((k₀ : ℝ) * D.K.b * (gRate D.Pl / 3))

/-- Enlarge the constant, degree and exponent. -/
theorem lift {v C Cb P Pm E E' x : ℝ} (hv : v ≤ C * P * E * x) (hC : |C| ≤ Cb) (hP : 0 ≤ P)
    (hPm : P ≤ Pm) (hE : 0 ≤ E) (hEE : E ≤ E') (hx : 0 ≤ x) : v ≤ Cb * Pm * E' * x := by
  have hCb : 0 ≤ Cb := (abs_nonneg C).trans hC
  have h1 : C * P * E * x ≤ |C| * P * E * x := by
    have : 0 ≤ P * E * x := by positivity
    nlinarith [le_abs_self C]
  refine hv.trans (h1.trans ?_)
  have hE' : 0 ≤ E' := hE.trans hEE
  have hPm0 : 0 ≤ Pm := hP.trans hPm
  have : 0 ≤ Cb * Pm := mul_nonneg hCb hPm0
  gcongr

theorem ageVelocity_of (Pl : PlanarData) (σ₀ mZ dm dp : ℝ)
    (h1 : AgeVelThin Pl σ₀ mZ dm dp) (h2 : AgeVelRep Pl σ₀ mZ dm dp) :
    ∃ k₀ : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ → D.RepairStanding dm dp →
      D.AgeVelocity ((k₀ : ℝ) * D.K.b * (gRate D.Pl / 3)) := by
  obtain ⟨k1, H1⟩ := h1
  obtain ⟨k2, H2⟩ := h2
  refine ⟨max k1 k2, fun D hPl hσ hmZ hst => ?_⟩
  have hb := hst.b_pos
  have hg := hst.gamma_pos
  have hmono : ∀ j : ℕ, j ≤ max k1 k2 →
      (j : ℝ) * D.K.b * (gRate D.Pl / 3) ≤ ((max k1 k2 : ℕ) : ℝ) * D.K.b * (gRate D.Pl / 3) := by
    intro j hj
    have : (j : ℝ) ≤ ((max k1 k2 : ℕ) : ℝ) := by exact_mod_cast hj
    have hbg : 0 ≤ D.K.b * (gRate D.Pl / 3) := by positivity
    nlinarith
  obtain ⟨C1, j1, e1⟩ := H1 D hPl hσ hmZ hst
  obtain ⟨C2, j2, e2⟩ := H2 D hPl hσ hmZ hst
  have hν1 : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n ≤ 1 :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually (ge_mem_nhds one_pos)
  set ω := ((max k1 k2 : ℕ) : ℝ) * D.K.b * (gRate D.Pl / 3) with hω
  have m1 := hmono k1 (le_max_left _ _)
  have m2 := hmono k2 (le_max_right _ _)
  refine ⟨|C1| + |C2|, max j1 j2, ?_⟩
  filter_upwards [e1, e2, hν1] with n a1 a2 hν z hz
  have hνp : 0 < (D.level n).ν := (D.level n).ν_pos
  have hν1' : (D.level n).ν ≤ 1 := hν
  have hi : 1 ≤ (D.level n).ν⁻¹ := (one_le_inv₀ hνp).2 hν1'
  have hP : ∀ j : ℕ, 0 ≤ (D.level n).ν⁻¹ ^ j := fun j => by positivity
  have pj1 : (D.level n).ν⁻¹ ^ j1 ≤ (D.level n).ν⁻¹ ^ (max j1 j2) :=
    pow_le_pow_right₀ hi (le_max_left _ _)
  have pj2 : (D.level n).ν⁻¹ ^ j2 ≤ (D.level n).ν⁻¹ ^ (max j1 j2) :=
    pow_le_pow_right₀ hi (le_max_right _ _)
  have pm := hP (max j1 j2)
  refine ⟨fun T => ?_, fun w => ?_⟩
  · have e : Real.exp ((gRate D.Pl / 10 + (k1 : ℝ) * D.K.b * (gRate D.Pl / 3) +
        3 * D.K.m0 / 2) / (D.level n).ν) ≤
        Real.exp ((gRate D.Pl / 10 + ω + 3 * D.K.m0 / 2) / (D.level n).ν) := by
      refine Real.exp_le_exp.2 (div_le_div_of_nonneg_right ?_ hνp.le)
      linarith
    exact lift (a1 z hz T) (by linarith [abs_nonneg C2]) (hP j1) pj1
      (Real.exp_pos _).le e (norm_nonneg T)
  · have e' : Real.exp (-(31 * gRate D.Pl / 165 - (k2 : ℝ) * D.K.b * (gRate D.Pl / 3) -
        3 * D.K.m0 / 2) / (D.level n).ν) ≤
        Real.exp (-(31 * gRate D.Pl / 165 - ω - 3 * D.K.m0 / 2) / (D.level n).ν) := by
      refine Real.exp_le_exp.2 (div_le_div_of_nonneg_right ?_ hνp.le)
      linarith
    exact lift (a2 z hz w) (by linarith [abs_nonneg C1]) (hP j2) pj2 (Real.exp_pos _).le e' (norm_nonneg w)

end UnforcedLeray.Short.PartIIIb.Concrete
