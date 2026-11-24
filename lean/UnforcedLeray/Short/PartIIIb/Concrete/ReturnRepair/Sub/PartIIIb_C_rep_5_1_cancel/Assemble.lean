import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_cancel.Bridge

/-!
# Gained per-bin velocity of the sum `S_far T + Y[T]`, from late and plateau bins

Source `the November 2 reference manuscript` 5303-5316, 5594-5599, 5688-5689.
`D.PerBinVelocityG ageThinFam` from `FarLateBin`, `FarEarlyBin`, `WardLateBin`, `PlateauCancel`:

* late bins (`ν s_{j+1} ≥ 2/3`): triangle inequality for `binNorm`, `FarLateBin` and `WardLateBin`;
* plateau bins (`ν s_{j+1} < 2/3`, hence `ν s_j < (2/3) e^{δ/4} < 4/5`): on the bin the sum
  coincides a.e. with `S_far` of the early part (`PlateauCancel`), bounded by `FarEarlyBin`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem measurableSet_binSet (S h : ℝ) (j : ℕ) : MeasurableSet (binSet S h j) :=
  (measurableSet_lt measurable_const measurable_fst).inter
    (measurableSet_le measurable_fst measurable_const)

/-- Bin norms of two body velocities that agree a.e. on the bin agree. -/
theorem binNorm_congr (c γ ν S h : ℝ) (j : ℕ) (φ ψ : VelG c γ ν)
    (hae : ∀ᵐ p ∂(bodyMeasure c γ ν), p ∈ binSet S h j → (φ : Chart → Merid) p = ψ p) :
    binNorm c γ ν S h j φ = binNorm c γ ν S h j ψ := by
  unfold binNorm
  have h' : (φ : Chart → Merid) =ᵐ[(bodyMeasure c γ ν).restrict (binSet S h j)] (ψ : Chart → Merid) :=
    (ae_restrict_iff' (measurableSet_binSet S h j)).2 hae
  rw [eLpNorm_congr_ae h']

/-- `e^{δ/4} ≤ 6/5` for `δ < log(12/11)`: so a bin with `ν s_{j+1} < 2/3` has `ν s_j < 4/5`. -/
theorem exp_quarter_le {δ : ℝ} (hδ : δ < Real.log (12 / 11)) : Real.exp (δ / 4) ≤ 6 / 5 := by
  by_contra hlt
  push Not at hlt
  have h4 := pow_lt_pow_left₀ hlt (by norm_num) (by norm_num : (4 : ℕ) ≠ 0)
  have e : Real.exp (δ / 4) ^ 4 = Real.exp δ := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hx : Real.exp δ < 12 / 11 := by
    calc Real.exp δ < Real.exp (Real.log (12 / 11)) := Real.exp_lt_exp.2 hδ
      _ = 12 / 11 := Real.exp_log (by norm_num)
  rw [e] at h4
  norm_num at h4
  linarith

/-- Plateau geometry: if `ν s_{j+1} < 2/3` then every age of the bin `j` is at most `4/(5ν)`. -/
theorem binSet_le_plateau {S h δ ν : ℝ} (hS : 0 ≤ S) (hδ : δ < Real.log (12 / 11))
    (hh : h = δ / 4) (hν : 0 < ν) (j : ℕ) (hj : ν * binUpper S h (j + 1) < 2 / 3) :
    ∀ p ∈ binSet S h j, p.1 ≤ 4 / (5 * ν) := by
  intro p hp
  have hp2 : p.1 ≤ binUpper S h j := hp.2
  have e : binUpper S h j = binUpper S h (j + 1) * Real.exp h := by
    rw [binUpper_succ, mul_assoc, ← Real.exp_add]; simp
  have hexp : Real.exp h ≤ 6 / 5 := by rw [hh]; exact exp_quarter_le hδ
  have hs1 : 0 ≤ binUpper S h (j + 1) := by unfold binUpper; positivity
  rw [le_div_iff₀ (by positivity)]
  have h1 : p.1 ≤ binUpper S h (j + 1) * Real.exp h := e ▸ hp2
  have h2 : ν * (binUpper S h (j + 1) * Real.exp h) ≤ ν * binUpper S h (j + 1) * (6 / 5) := by
    have := mul_le_mul_of_nonneg_left hexp (mul_nonneg hν.le hs1)
    linarith
  nlinarith

theorem lift2 {v C Cb P Pm E Sg x : ℝ} (hv : v ≤ C * P * E * Sg * x) (hC : |C| ≤ Cb)
    (hP : 0 ≤ P) (hPm : P ≤ Pm) (hE : 0 ≤ E) (hSg : 0 ≤ Sg) (hx : 0 ≤ x) :
    v ≤ Cb * Pm * E * Sg * x := by
  have h1 : v ≤ C * P * (E * Sg) * x := by
    calc v ≤ C * P * E * Sg * x := hv
      _ = C * P * (E * Sg) * x := by ring
  have h2 := lift h1 hC hP hPm (mul_nonneg hE hSg) le_rfl hx
  calc v ≤ Cb * Pm * (E * Sg) * x := h2
    _ = Cb * Pm * E * Sg * x := by ring

/-- **Gained per-bin velocity of the sum** (5303-5316, 5594-5599, 5688-5689): late bins by the
triangle inequality and the two late-output bounds, plateau bins by the exact cancellation of the
young-old rectangle and the early-source bound. -/
theorem ageThinPerBinG_of (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (hL : D.FarLateBin) (hE : D.FarEarlyBin) (hW : D.WardLateBin) (hP : D.PlateauCancel) :
    D.PerBinVelocityG ageThinFam := by
  obtain ⟨C1, k1, h1⟩ := hL
  obtain ⟨C2, k2, h2⟩ := hE
  obtain ⟨C3, k3, h3⟩ := hW
  have hle := retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  refine ⟨|C1| + |C2| + |C3|, k1 + k2 + k3, ?_⟩
  filter_upwards [h1, h2, h3, hP, hle] with n a1 a2 a3 ap ⟨hν1, hε1⟩ z hz T j
  have hνp : 0 < (D.level n).ν := (D.level n).ν_pos
  have hεp : 0 < (D.level n).ε := (D.level n).ε_pos
  have hi : 1 ≤ (D.level n).ν⁻¹ := (one_le_inv₀ hνp).2 hν1
  have hS0 : 0 ≤ (D.level n).Scut D.K := by
    have : (D.level n).Scut D.K = (D.level n).ε ^ (-D.K.b) := rfl
    rw [this]; positivity
  have hs0 : 0 ≤ binUpper ((D.level n).Scut D.K) D.K.hbin j := by unfold binUpper; positivity
  have hP1 : (D.level n).ν⁻¹ ^ k1 ≤ (D.level n).ν⁻¹ ^ (k1 + k2 + k3) :=
    pow_le_pow_right₀ hi (by omega)
  have hP2 : (D.level n).ν⁻¹ ^ k2 ≤ (D.level n).ν⁻¹ ^ (k1 + k2 + k3) :=
    pow_le_pow_right₀ hi (by omega)
  have hP3 : (D.level n).ν⁻¹ ^ k3 ≤ (D.level n).ν⁻¹ ^ (k1 + k2 + k3) :=
    pow_le_pow_right₀ hi (by omega)
  have hE0 : 0 ≤ Real.exp ((gRate D.Pl / 10) / (D.level n).ν) := (Real.exp_pos _).le
  have hSg : 0 ≤ binUpper ((D.level n).Scut D.K) D.K.hbin j ^ (1 / 2 : ℝ) +
      binUpper ((D.level n).Scut D.K) D.K.hbin j ^ (3 / 4 : ℝ) := by positivity
  have hpos : 0 ≤ (D.level n).ν⁻¹ ^ (k1 + k2 + k3) := by positivity
  have hT0 : 0 ≤ ‖T‖ := norm_nonneg T
  have z1 : 0 ≤ |C1| * (D.level n).ν⁻¹ ^ (k1 + k2 + k3) *
      Real.exp ((gRate D.Pl / 10) / (D.level n).ν) * (binUpper ((D.level n).Scut D.K) D.K.hbin j
        ^ (1 / 2 : ℝ) + binUpper ((D.level n).Scut D.K) D.K.hbin j ^ (3 / 4 : ℝ)) * ‖T‖ := by
    positivity
  have z2 : 0 ≤ |C2| * (D.level n).ν⁻¹ ^ (k1 + k2 + k3) *
      Real.exp ((gRate D.Pl / 10) / (D.level n).ν) * (binUpper ((D.level n).Scut D.K) D.K.hbin j
        ^ (1 / 2 : ℝ) + binUpper ((D.level n).Scut D.K) D.K.hbin j ^ (3 / 4 : ℝ)) * ‖T‖ := by
    positivity
  have z3 : 0 ≤ |C3| * (D.level n).ν⁻¹ ^ (k1 + k2 + k3) *
      Real.exp ((gRate D.Pl / 10) / (D.level n).ν) * (binUpper ((D.level n).Scut D.K) D.K.hbin j
        ^ (1 / 2 : ℝ) + binUpper ((D.level n).Scut D.K) D.K.hbin j ^ (3 / 4 : ℝ)) * ‖T‖ := by
    positivity
  by_cases hlate : 2 / 3 ≤ (D.level n).ν * binUpper ((D.level n).Scut D.K) D.K.hbin (j + 1)
  · have e : ageThinFam D n z (thinPart T) =
        sopThinFam D n z (thinPart T) + wardThinFam D n z (thinPart T) := rfl
    rw [e]
    refine (binNorm_add_le _ _ _ _ _ _ _ _).trans ?_
    have b1 := lift2 (a1 z hz T j hlate) le_rfl (by positivity) hP1 hE0 hSg hT0
    have b3 := lift2 (a3 z hz T j hlate) le_rfl (by positivity) hP3 hE0 hSg hT0
    nlinarith [b1, b3, z2]
  · push Not at hlate
    have hplat := binSet_le_plateau hS0 hst.δ_lt (rfl : D.K.hbin = D.K.δ / 4) hνp j hlate
    set c := chiOStr (cOf (D.level n).ν) D.K.mZ ((D.level n).ρb D.Pl D.K) (gRate D.Pl)
      (D.level n).ν D.K.hχo (thinPart T) with hc
    have key : sopThinFam D n z (thinPart T) =
        sopThinFam D n z (earlyPart D.Pl D.K (D.level n) T) + sopThinFam D n z c := by
      rw [← map_add]
      congr 1
      unfold earlyPart
      rw [hc]
      abel
    have e : ageThinFam D n z (thinPart T) =
        (sopThinFam D n z (earlyPart D.Pl D.K (D.level n) T) + sopThinFam D n z c) +
          wardThinFam D n z (thinPart T) := by
      show sopThinFam D n z (thinPart T) + wardThinFam D n z (thinPart T) = _
      rw [key]
    have hcong : binNorm (cOf (D.level n).ν) (gRate D.Pl) (D.level n).ν
        ((D.level n).Scut D.K) D.K.hbin j (ageThinFam D n z (thinPart T)) =
        binNorm (cOf (D.level n).ν) (gRate D.Pl) (D.level n).ν ((D.level n).Scut D.K)
          D.K.hbin j (sopThinFam D n z (earlyPart D.Pl D.K (D.level n) T)) := by
      refine binNorm_congr _ _ _ _ _ _ _ _ ?_
      rw [e]
      have q1 := Lp.coeFn_add (sopThinFam D n z (earlyPart D.Pl D.K (D.level n) T) +
        sopThinFam D n z c) (wardThinFam D n z (thinPart T))
      have q2 := Lp.coeFn_add (sopThinFam D n z (earlyPart D.Pl D.K (D.level n) T))
        (sopThinFam D n z c)
      filter_upwards [q1, q2, ap z hz T] with p r1 r2 r3 hpb
      have r4 := r3 (hplat p hpb)
      rw [r1, Pi.add_apply, r2, Pi.add_apply]
      calc _ = ((sopThinFam D n z (earlyPart D.Pl D.K (D.level n) T) : Chart → Merid) p) +
            ((wardThinFam D n z (thinPart T) : Chart → Merid) p +
              (sopThinFam D n z c : Chart → Merid) p) := by abel
        _ = _ := by
          have : ((wardThinFam D n z (thinPart T) : Chart → Merid) p +
              (sopThinFam D n z c : Chart → Merid) p) = 0 := r4
          rw [this, add_zero]
    rw [hcong]
    have b2 := lift2 (a2 z hz T j hlate) le_rfl (by positivity) hP2 hE0 hSg hT0
    nlinarith [b2, z1, z3]

end UnforcedLeray.Short.PartIIIb.Concrete

end
