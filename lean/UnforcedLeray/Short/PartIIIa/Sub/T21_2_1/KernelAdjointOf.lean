import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.KernelDefs

/-!
# Part III-a, `PartIII-a:T21/2/1/2`: assembly of `KernelAdjointBound` from the kernel leaves

Source of record: `the November 2 reference manuscript` (SP), lines 3052-3057
("split the Biot-Savart kernel into its integrable near part and bounded far part, and use the
uniform order-zero multiplier bound for its derivative, including the horizontal mean"), with
the kernel facts of SP 2117-2121, 2876-2881 (definitions and leaves in `KernelDefs.lean`).

Proof of `kernelAdjointBound_of`. Take `χ = kerAdj d F = K_d^T F`.
* `‖χ‖_{X_{-m,d}}`: `KerAdjSplit` writes `χ = a + b` with `‖a‖_{L²} ≤ C_S Σ‖F_j‖_{L²}` and
  `|b| ≤ C_S Σ‖F_j‖_{L¹}`; `XNormSplitLe m` (`m > 1`) gives
  `‖χ‖_{X_{-m,d}} ≤ C_S Σ‖F_j‖₂ + C_W C_S Σ‖F_j‖₁`.
* `∂_kχ`: by `KerAdjFubini` at the test `∂_kψ`,
  `∫ χ ∂_kψ = ∫ F · K_d(∂_kψ)`, and Hölder with `KerVelDerivBound` bounds it by
  `(Σ_j ‖F_j‖₂) ‖ψ‖₂`; `WeakDerivOfBoundedPairing` gives `g_k = ∂_kχ` with
  `‖g_k‖_{L²} ≤ 2 Σ_j‖F_j‖₂`, and `‖g_k‖_{X_{-m,d}} ≤ ‖g_k‖_{L²}` (`XNormSplitLe` with `b = 0`).
* `h1Norm = (‖χ‖² + ‖g_0‖² + ‖g_1‖²)^{1/2} ≤ ‖χ‖ + ‖g_0‖ + ‖g_1‖ ≤ (C_S + C_W C_S + 4) Σ_j
  (‖F_j‖₁ + ‖F_j‖₂)`.
* Duality: `KerAdjFubini` at `ψ` gives `∫ χψ = ∫ F · K_dψ`; `K_dψ` satisfies
  `IsKernelBiotSavart` (`KerVelFarField`, `KerVelDivFree`, `KerVelCurl`), so any `uψ` with
  `IsKernelBiotSavart d ψ uψ` equals it a.e. (`KernelBiotSavartUnique`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Hölder for the pairing `∫ F · v` of a complex `L²` field with a real `L²` field. -/
theorem enorm_integral_sum_mul_le {μ : Measure (ℝ × ℝ)} (F : Fin 2 → ℝ × ℝ → ℂ)
    (v : Fin 2 → ℝ × ℝ → ℝ) (hF : ∀ j, MemLp (F j) 2 μ) (hv : ∀ j, MemLp (v j) 2 μ)
    (B : ℝ≥0∞) (hB : ∀ j, eLpNorm (v j) 2 μ ≤ B) :
    ‖∫ x, ∑ j, F j x * ((v j x : ℝ) : ℂ) ∂μ‖ₑ ≤ (∑ j, eLpNorm (F j) 2 μ) * B := by
  have hv' : ∀ j, AEStronglyMeasurable (fun x => ((v j x : ℝ) : ℂ)) μ :=
    fun j => Complex.continuous_ofReal.comp_aestronglyMeasurable (hv j).1
  have hprod : ∀ j, AEStronglyMeasurable (fun x => F j x * ((v j x : ℝ) : ℂ)) μ :=
    fun j => (hF j).1.mul (hv' j)
  have hHold : ∀ j, eLpNorm (fun x => F j x * ((v j x : ℝ) : ℂ)) 1 μ ≤
      eLpNorm (F j) 2 μ * B := by
    intro j
    have h := eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm (f := F j) (g := v j)
      (p := 2) (q := 2) (r := 1) (hF j).1 (hv j).1 (fun z t => z * ((t : ℝ) : ℂ)) 1
      (Eventually.of_forall fun x => by
        simp only [norm_mul, Complex.norm_real, NNReal.coe_one, one_mul, le_refl])
    rw [ENNReal.coe_one, one_mul] at h
    refine h.trans ?_
    gcongr
    exact hB j
  calc ‖∫ x, ∑ j, F j x * ((v j x : ℝ) : ℂ) ∂μ‖ₑ
      ≤ ∫⁻ x, ‖∑ j, F j x * ((v j x : ℝ) : ℂ)‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
    _ = eLpNorm (∑ j, fun x => F j x * ((v j x : ℝ) : ℂ)) 1 μ := by
        rw [eLpNorm_one_eq_lintegral_enorm, Finset.sum_fn]
    _ ≤ ∑ j, eLpNorm (fun x => F j x * ((v j x : ℝ) : ℂ)) 1 μ :=
        eLpNorm_sum_le (fun j _ => hprod j) le_rfl
    _ ≤ ∑ j, eLpNorm (F j) 2 μ * B := Finset.sum_le_sum fun j _ => hHold j
    _ = (∑ j, eLpNorm (F j) 2 μ) * B := (Finset.sum_mul _ _ _).symm

/-- `(A² + (G₀² + G₁²))^{1/2} ≤ A + (G₀ + G₁)` in `ℝ≥0∞`. -/
theorem sqrt_sum_sq_le_sum (A G0 G1 : ℝ≥0∞) :
    (A ^ 2 + (G0 ^ 2 + G1 ^ 2)) ^ (1 / 2 : ℝ) ≤ A + (G0 + G1) := by
  have h1 : A ^ 2 + (G0 ^ 2 + G1 ^ 2) ≤ (A + (G0 + G1)) ^ 2 :=
    calc A ^ 2 + (G0 ^ 2 + G1 ^ 2)
        ≤ A ^ 2 + (G0 ^ 2 + G1 ^ 2) + (2 * A * (G0 + G1) + 2 * G0 * G1) := le_self_add
      _ = (A + (G0 + G1)) ^ 2 := by ring
  calc (A ^ 2 + (G0 ^ 2 + G1 ^ 2)) ^ (1 / 2 : ℝ) ≤ ((A + (G0 + G1)) ^ 2) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow h1 (by norm_num)
    _ = A + (G0 + G1) := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num

/-- **Assembly of `KernelAdjointBound`** (SP 3052-3057) from the kernel leaves of
`KernelDefs.lean`. -/
theorem kernelAdjointBound_of (m : ℝ) (hS : KerAdjSplit) (hW : XNormSplitLe m)
    (hM : KerVelDerivBound) (hR : WeakDerivOfBoundedPairing) (hF : KerAdjFubini)
    (hFar : KerVelFarField) (hD : KerVelDivFree) (hC : KerVelCurl)
    (hU : KernelBiotSavartUnique) : KernelAdjointBound m := by
  intro hm
  obtain ⟨CS, hCS0, hCS⟩ := hS
  obtain ⟨CW, hCW0, hCW⟩ := hW hm
  refine ⟨CS + CW * CS + 4, by positivity, ?_⟩
  intro d hd F hFj
  have hd0 : 0 < d := by linarith
  have hL2fin : (∑ j, eLpNorm (F j) 2 (volume.restrict (B0579.cell d))) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun j _ => (hFj j).2.eLpNorm_ne_top
  -- the weak gradient, from the multiplier bound and the bounded pairing
  have hgrad : ∀ k : Fin 2, ∃ g : ℝ × ℝ → ℂ, HasWeakCellDerivC d k (kerAdj d F) g ∧
      MemLp g 2 (volume.restrict (B0579.cell d)) ∧
      eLpNorm g 2 (volume.restrict (B0579.cell d)) ≤
        2 * ∑ j, eLpNorm (F j) 2 (volume.restrict (B0579.cell d)) := by
    intro k
    refine hR d hd0 (kerAdj d F) k _ hL2fin (fun ψ hψ => ?_)
    obtain ⟨hint, heq⟩ := hF d hd F (fun j => (hFj j).1) (B0579.pd k ψ) (hψ.pd k)
    refine ⟨hint, ?_⟩
    rw [heq]
    exact enorm_integral_sum_mul_le F (fun j x => kerVel d (B0579.pd k ψ) x j)
      (fun j => (hFj j).2) (fun j => (hM d hd ψ hψ k j).1) _
      (fun j => (hM d hd ψ hψ k j).2)
  choose g hg using hgrad
  refine ⟨kerAdj d F, g, fun j => (hg j).1, ?_, ?_⟩
  · -- the `H¹_{-m,d}` bound
    obtain ⟨a, b, hab, ha, haB, hb, hbB⟩ := hCS d hd F hFj
    set μ := volume.restrict (B0579.cell d) with hμ
    set L1 : ℝ≥0∞ := ∑ j, eLpNorm (F j) 1 μ with hL1
    set L2 : ℝ≥0∞ := ∑ j, eLpNorm (F j) 2 μ with hL2
    have hA : xNorm d (-m) (kerAdj d F) ≤
        ENNReal.ofReal CS * L2 + ENNReal.ofReal CW * (ENNReal.ofReal CS * L1) :=
      (hCW d hd0 _ a b _ hab ha.1 hb hbB).trans (add_le_add haB le_rfl)
    have hG : ∀ k, xNorm d (-m) (g k) ≤ 2 * L2 := by
      intro k
      have h := hCW d hd0 (g k) (g k) 0 0 (Eventually.of_forall fun y => by simp)
        (hg k).2.1.1 aestronglyMeasurable_const (fun y => by simp)
      rw [mul_zero, add_zero] at h
      exact h.trans (hg k).2.2
    rw [h1Norm, Fin.sum_univ_two]
    refine (sqrt_sum_sq_le_sum _ _ _).trans ?_
    calc xNorm d (-m) (kerAdj d F) + (xNorm d (-m) (g 0) + xNorm d (-m) (g 1))
        ≤ ENNReal.ofReal CS * L2 + ENNReal.ofReal CW * (ENNReal.ofReal CS * L1) +
            (2 * L2 + 2 * L2) := add_le_add hA (add_le_add (hG 0) (hG 1))
      _ = ENNReal.ofReal CS * L2 + ENNReal.ofReal CW * (ENNReal.ofReal CS * L1) + 4 * L2 := by
          ring
      _ ≤ ENNReal.ofReal CS * L2 + ENNReal.ofReal CW * (ENNReal.ofReal CS * L1) + 4 * L2 +
            (ENNReal.ofReal CS * L1 + ENNReal.ofReal CW * ENNReal.ofReal CS * L2 + 4 * L1) :=
          le_self_add
      _ = (ENNReal.ofReal CS + ENNReal.ofReal CW * ENNReal.ofReal CS + 4) * (L1 + L2) := by
          ring
      _ = ENNReal.ofReal (CS + CW * CS + 4) *
            ∑ j, (eLpNorm (F j) 1 μ + eLpNorm (F j) 2 μ) := by
          rw [Finset.sum_add_distrib, ENNReal.ofReal_add (by positivity) (by norm_num),
            ENNReal.ofReal_add hCS0 (by positivity), ENNReal.ofReal_mul hCW0,
            ENNReal.ofReal_ofNat]
  · -- the duality identity against every kernel Biot-Savart velocity
    intro ψ uψ hψ hu
    obtain ⟨-, heq⟩ := hF d hd F (fun j => (hFj j).1) ψ hψ
    rw [heq]
    have hE : IsKernelBiotSavart d ψ (kerVel d ψ) := by
      unfold IsKernelBiotSavart
      exact ⟨hFar d hd ψ hψ, hD d hd ψ hψ, hC d hd ψ hψ⟩
    have hae := hU d hd0 ψ uψ (kerVel d ψ) hu hE
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]

end UnforcedLeray.Short.IIIa
