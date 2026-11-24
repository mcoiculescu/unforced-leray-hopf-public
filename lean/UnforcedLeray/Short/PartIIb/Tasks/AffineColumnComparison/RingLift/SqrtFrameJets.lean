import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_5_2_1
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.RingLift.SqrtFrameJets.FrameJets

/-!
# Part II-b, task `PartII-b:G4/5/2/1/3` (`SqrtFrameJets`)

Source of record: `the November 2 reference manuscript` lines 2347-2369.
Off the axis `√(age R z) = R ϱ(z)⁻¹` (`Axi.sqrt_age`), so with `t = ϱ(y)⁻¹` the jets are
`‖Dʲ √age‖ ≤ R C_j t^{j+1}` and `‖Dʲ frameL‖ ≤ C_j t^j` (`varrho_inv_jet`, `frameL_jet`).  For `R ≥ 1`
and `age R y < S`, `t ≤ R t = √age ≤ 1 + S`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray SqrtFrameJetsAux

theorem sqrtFrameJets : UnforcedLeray.Short.IIb.SqrtFrameJets := by
  intro j
  obtain ⟨C1, hC1, h1⟩ := varrho_inv_jet j
  obtain ⟨C2, hC2, h2⟩ := frameL_jet j
  refine ⟨C1 + C2, j + 1, by positivity, fun S R hS hR y hy hage => ?_⟩
  have hϱ : 0 < Axi.ϱ y := Axi.ϱ_pos hy
  set t := (Axi.ϱ y)⁻¹ with ht
  have ht0 : 0 < t := inv_pos.2 hϱ
  have hR0 : 0 < R := by linarith
  set u := R * t with hu
  have hsq : √(Axi.age R y) = u := by
    rw [Axi.sqrt_age hR0 hy, hu, ht]; ring
  have hu0 : 0 < u := by positivity
  have htu : t ≤ u := by nlinarith
  have hu2 : u ^ 2 < S := by
    have : Axi.age R y = u ^ 2 := by
      have h := Real.sq_sqrt (Axi.age_pos hR0.ne' hy).le
      rw [hsq] at h; exact h.symm
    rw [← this]; exact hage
  have hu1 : u ≤ 1 + S := by nlinarith
  have hupow : ∀ n : ℕ, u ^ n ≤ (1 + S) ^ n := fun n => pow_le_pow_left₀ hu0.le hu1 n
  have hS1 : (1 : ℝ) ≤ 1 + S := by linarith
  have hfun : (fun z : Space => √(Axi.age R z)) =ᶠ[𝓝 y] (R • fun z : Space => (Axi.ϱ z)⁻¹) := by
    filter_upwards [Axi.isOpen_compl_axis.mem_nhds (show y ∈ Axi.axisᶜ from hy)] with z hz
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Axi.sqrt_age hR0 hz, div_eq_mul_inv]
  have hcd : ContDiffAt ℝ j (fun z : Space => (Axi.ϱ z)⁻¹) y :=
    ((Axi.contDiffOn_ϱ.inv fun _ hy => Axi.ϱ_ne_zero hy).contDiffAt
      (Axi.isOpen_compl_axis.mem_nhds hy)).of_le (by exact_mod_cast le_top)
  have hD : iteratedFDeriv ℝ j (fun z : Space => √(Axi.age R z)) y =
      R • iteratedFDeriv ℝ j (fun z : Space => (Axi.ϱ z)⁻¹) y := by
    rw [hfun.iteratedFDeriv ℝ j |>.self_of_nhds, iteratedFDeriv_const_smul_apply hcd]
  have hA : ‖iteratedFDeriv ℝ j (fun z : Space => √(Axi.age R z)) y‖ ≤ C1 * (1 + S) ^ (j + 1) := by
    rw [hD, norm_smul, Real.norm_of_nonneg hR0.le]
    calc R * ‖iteratedFDeriv ℝ j (fun z : Space => (Axi.ϱ z)⁻¹) y‖
        ≤ R * (C1 * t ^ (j + 1)) := mul_le_mul_of_nonneg_left (h1 y hy) hR0.le
      _ = C1 * (u * t ^ j) := by rw [hu]; ring
      _ ≤ C1 * (u * u ^ j) := by
          apply mul_le_mul_of_nonneg_left _ hC1.le
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht0.le htu j) hu0.le
      _ = C1 * u ^ (j + 1) := by ring
      _ ≤ C1 * (1 + S) ^ (j + 1) := mul_le_mul_of_nonneg_left (hupow _) hC1.le
  have hB : ‖iteratedFDeriv ℝ j Axi.frameL y‖ ≤ C2 * (1 + S) ^ (j + 1) := by
    calc _ ≤ C2 * t ^ j := h2 y hy
      _ ≤ C2 * u ^ j := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht0.le htu j) hC2.le
      _ ≤ C2 * (1 + S) ^ j := mul_le_mul_of_nonneg_left (hupow _) hC2.le
      _ ≤ C2 * (1 + S) ^ (j + 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hS1 (by omega)) hC2.le
  have hp : 0 ≤ (1 + S) ^ (j + 1) := by positivity
  constructor
  · nlinarith [mul_nonneg hC2.le hp]
  · nlinarith [mul_nonneg hC1.le hp]

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.sqrtFrameJets
