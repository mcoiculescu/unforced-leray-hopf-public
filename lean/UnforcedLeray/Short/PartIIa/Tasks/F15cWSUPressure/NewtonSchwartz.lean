import UnforcedLeray.Short.PartIIa.Tasks.F15cWSUPressure.CutoffGraph
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_3_2_1_of
import UnforcedLeray.Short.PartIIa.Tasks.F05bSliceContOfDecay
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_3_2_1.DecayOfFarBound
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_3_2_1.NewtonJointFDeriv
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_3_2_1.NewtonHessFar

/-!
# Schwartz-type decay and Poisson identity for joint Newton potentials of phase tests

Helper for `PartII-a:F15/3` (`Tasks/F15cWSUPressure.lean`).
For any real scalar phase test `D : ℝ × Space → ℝ`:
* `lapT (LTS.newtonJoint D) = -D` (`lapT_newtonJoint`),
* `dy k (LTS.newtonJoint D) • v` is in `IsPhaseSchwartz P (conjExp 2)`,
* `dy j (dy k (LTS.newtonJoint D) • v)` is in `IsPhaseSchwartz P (conjExp 2)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa.F15c

open UnforcedLeray.PhaseSpace UnforcedLeray.RieszLp UnforcedLeray.PressureAnalysis
open UnforcedLeray.Short.IIb

/-! ### Poisson identity for `LTS.newtonJoint` -/

theorem lapT_newtonJoint {P : ℝ} {D : ℝ × Space → ℝ} (hD : IsPhaseTest P D) :
    lapT (LTS.newtonJoint D) = -D := by
  funext ⟨τ, y⟩
  show ∑ j : Fin 3, dy j (dy j (LTS.newtonJoint D)) (τ, y) = -D (τ, y)
  simp_rw [LTS.dy_dy_newtonJoint_eq hD _ _ τ y]
  exact congrFun (laplacian_newtonConv (LTS.isSpatialTest_slice hD τ)) y

/-! ### Derivatives of `f • v` for a scalar function `f : ℝ × Space → ℝ` -/

theorem fderiv_smul_const_vec {f : ℝ × Space → ℝ} (hf : Differentiable ℝ f) (v : CVec3)
    (p w : ℝ × Space) :
    fderiv ℝ (fun q => (f q) • v) p w = (fderiv ℝ f p w) • v := by
  have h := ((hf p).hasFDerivAt.smul_const v).fderiv
  rw [h]
  simp

theorem dy_smul_const_vec {f : ℝ × Space → ℝ} (hf : Differentiable ℝ f) (v : CVec3) (j : Fin 3) :
    dy j (fun q => (f q) • v) = fun q => (dy j f q) • v :=
  funext fun p => fderiv_smul_const_vec hf v p (0, coordinateVector j)

theorem dτ_smul_const_vec {f : ℝ × Space → ℝ} (hf : Differentiable ℝ f) (v : CVec3) :
    dτ (fun q => (f q) • v) = fun q => (dτ f q) • v :=
  funext fun p => fderiv_smul_const_vec hf v p (1, 0)

theorem lapT_smul_const_vec {f : ℝ × Space → ℝ} (hf : ContDiff ℝ ∞ f) (v : CVec3) :
    lapT (fun q => (f q) • v) = fun q => (∑ j : Fin 3, dy j (dy j f) q) • v := by
  have hdf : Differentiable ℝ f := hf.differentiable (by simp)
  have h2 : ∀ j : Fin 3, dy j (dy j (fun q => (f q) • v)) = fun q => (dy j (dy j f) q) • v := by
    intro j
    rw [dy_smul_const_vec hdf v j]
    exact dy_smul_const_vec ((LTS.contDiff_dy_real hf j).differentiable (by simp)) v j
  funext p
  simp only [lapT, h2, Finset.sum_smul]

/-! ### `IsPhaseSchwartz` for first and second derivatives of `LTS.newtonJoint` -/

theorem isPhaseSchwartz_dy_newtonJoint {P : ℝ} [Fact (0 < P)] {D : ℝ × Space → ℝ}
    (hD : IsPhaseTest P D) (k : Fin 3) (v : CVec3) :
    IsPhaseSchwartz P (conjExp 2) (fun p => (dy k (LTS.newtonJoint D) p) • v) := by
  have hP : 0 < P := Fact.out
  let f : ℝ × Space → ℝ := dy k (LTS.newtonJoint D)
  let U : ℝ × Space → CVec3 := fun p => f p • v
  have hfs : ContDiff ℝ ∞ f := LTS.contDiff_dy_real (LTS.contDiff_newtonJoint hD) k
  have hfd : Differentiable ℝ f := hfs.differentiable (by simp)
  have hfp : ∀ τ y, f (τ + P, y) = f (τ, y) := periodic_dy (LTS.newtonJoint_periodic hD) k
  have hUs : ContDiff ℝ ∞ U := hfs.smul contDiff_const
  have hUp : ∀ τ y, U (τ + P, y) = U (τ, y) := fun τ y => by simp [U, hfp τ y]
  obtain ⟨ρ, C, hρ, hC, hfar⟩ :=
    LTS.lts_scalar_far LTS.newtonJointFDeriv_proof LTS.newtonHessFar_proof hD
  have hρ0 : 0 < ρ := by linarith
  have hCv : 0 ≤ C * ‖v‖ := mul_nonneg hC (norm_nonneg v)
  have hbU : ∀ τ ∈ Icc (0 : ℝ) P, ∀ y : Space, ρ ≤ ‖y‖ →
      ‖U (τ, y)‖ ≤ (C * ‖v‖) * (‖y‖ ^ 2)⁻¹ := by
    intro τ hτ y hy
    simp only [U, norm_smul, Real.norm_eq_abs]
    calc |f (τ, y)| * ‖v‖ ≤ (C * (‖y‖ ^ 2)⁻¹) * ‖v‖ :=
          mul_le_mul_of_nonneg_right ((hfar τ hτ y hy).1 k) (norm_nonneg v)
      _ = (C * ‖v‖) * (‖y‖ ^ 2)⁻¹ := by ring
  have hbdy : ∀ (j : Fin 3), ∀ τ ∈ Icc (0 : ℝ) P, ∀ y : Space, ρ ≤ ‖y‖ →
      ‖dy j U (τ, y)‖ ≤ (C * ‖v‖) * (‖y‖ ^ 3)⁻¹ := by
    intro j τ hτ y hy
    rw [dy_smul_const_vec hfd v j]
    simp only [norm_smul, Real.norm_eq_abs]
    calc |dy j f (τ, y)| * ‖v‖ ≤ (C * (‖y‖ ^ 3)⁻¹) * ‖v‖ :=
          mul_le_mul_of_nonneg_right ((hfar τ hτ y hy).2.1 j k) (norm_nonneg v)
      _ = (C * ‖v‖) * (‖y‖ ^ 3)⁻¹ := by ring
  have hblap : ∀ τ ∈ Icc (0 : ℝ) P, ∀ y : Space, ρ ≤ ‖y‖ →
      ‖lapT U (τ, y)‖ ≤ (3 * (C * ‖v‖)) * (‖y‖ ^ 3)⁻¹ := by
    intro τ hτ y hy
    rw [lapT_smul_const_vec hfs v]
    simp only [norm_smul, Real.norm_eq_abs]
    have hsum : |∑ j : Fin 3, dy j (dy j f) (τ, y)| ≤ 3 * (C * (‖y‖ ^ 3)⁻¹) := by
      calc |∑ j : Fin 3, dy j (dy j f) (τ, y)|
          ≤ ∑ j : Fin 3, |dy j (dy j f) (τ, y)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ 3 * (C * (‖y‖ ^ 3)⁻¹) := LTS.lts_sum3_le fun j => (hfar τ hτ y hy).2.2.1 j k
    calc |∑ j : Fin 3, dy j (dy j f) (τ, y)| * ‖v‖
        ≤ (3 * (C * (‖y‖ ^ 3)⁻¹)) * ‖v‖ :=
          mul_le_mul_of_nonneg_right hsum (norm_nonneg v)
      _ = (3 * (C * ‖v‖)) * (‖y‖ ^ 3)⁻¹ := by ring
  have hbdτ : ∀ τ ∈ Icc (0 : ℝ) P, ∀ y : Space, ρ ≤ ‖y‖ →
      ‖dτ U (τ, y)‖ ≤ (C * ‖v‖) * (‖y‖ ^ 2)⁻¹ := by
    intro τ hτ y hy
    rw [dτ_smul_const_vec hfd v]
    simp only [norm_smul, Real.norm_eq_abs]
    calc |dτ f (τ, y)| * ‖v‖ ≤ (C * (‖y‖ ^ 2)⁻¹) * ‖v‖ :=
          mul_le_mul_of_nonneg_right ((hfar τ hτ y hy).2.2.2 k) (norm_nonneg v)
      _ = (C * ‖v‖) * (‖y‖ ^ 2)⁻¹ := by ring
  obtain ⟨C0, hC0⟩ := LTS.decayOfFarBound_proof P hP 2 U hUs.continuous hUp ρ (C * ‖v‖) hρ0 hbU
  choose Cd hCd using fun j : Fin 3 => LTS.decayOfFarBound_proof P hP 3 (dy j U)
    (PhaseSpace.contDiff_dy hUs j).continuous (periodic_dy hUp j) ρ (C * ‖v‖) hρ0 (hbdy j)
  obtain ⟨Cl, hCl⟩ := LTS.decayOfFarBound_proof P hP 3 (lapT U) (contDiff_lapT hUs).continuous
    (periodic_lapT hUp) ρ (3 * (C * ‖v‖)) hρ0 hblap
  have hcont_dr : Continuous (driftT U) := by
    have hτc := (contDiff_dτ hUs).continuous
    have hrc := (contDiff_radialT hUs).continuous
    exact (hτc.neg.add (hrc.const_smul (1 / 2 : ℝ))).add (hUs.continuous.const_smul (3 / 2 : ℝ))
  obtain ⟨Ct, hCt⟩ := LTS.decayOfFarBound_proof P hP 2 (driftT U) hcont_dr (periodic_driftT hUp) ρ
    (4 * (C * ‖v‖)) hρ0 fun τ hτ y hy =>
      LTS.lts_driftT_far (by linarith) (hbU τ hτ y hy) (fun j => hbdy j τ hτ y hy) (hbdτ τ hτ y hy)
  have hsl : ∀ (n : ℕ) (G : ℝ × Space → CVec3) (K : ℝ), 2 ≤ n → Continuous G →
      (∀ τ y, ‖G (τ, y)‖ ≤ K * (1 + ‖y‖) ^ (-(n : ℝ))) → SliceCont (conjExp 2) G := by
    intro n G K hn hG hb
    refine sliceContOfDecay (conjExp 2) LTS.conjExp_two_ne_top (n : ℝ) K ?_ G hG hb
    rw [LTS.toReal_conjExp_two]
    have h2n : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  exact ⟨hUs, hUp, hsl 2 _ C0 le_rfl hUs.continuous hC0,
    fun j => hsl 3 _ (Cd j) (by norm_num) (PhaseSpace.contDiff_dy hUs j).continuous (hCd j),
    hsl 3 _ Cl (by norm_num) (contDiff_lapT hUs).continuous hCl,
    hsl 2 _ Ct le_rfl hcont_dr hCt⟩

theorem isPhaseSchwartz_dy_dy_newtonJoint {P : ℝ} [Fact (0 < P)] {D : ℝ × Space → ℝ}
    (hD : IsPhaseTest P D) (k j : Fin 3) (v : CVec3) :
    IsPhaseSchwartz P (conjExp 2) (dy j (fun p => (dy k (LTS.newtonJoint D) p) • v)) := by
  have hfs : ContDiff ℝ ∞ (dy k (LTS.newtonJoint D)) :=
    LTS.contDiff_dy_real (LTS.contDiff_newtonJoint hD) k
  rw [dy_smul_const_vec (hfs.differentiable (by simp)) v j,
    LTS.lts_dy_newtonJoint_comm LTS.newtonJointFDeriv_proof hD k]
  exact isPhaseSchwartz_dy_newtonJoint (hD.dy k) j v

end UnforcedLeray.Short.PartIIa.F15c
