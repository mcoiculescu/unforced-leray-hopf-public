import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2WeakEq.FramePairingDefs
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2WeakEq.FramePairing2.Scale
import UnforcedLeray.Short.PartIIIa.Clock.ZeroCirc

/-!
# `PartIII-a:T21/c3/3/1/1/2/2/3/c/2`: moving form of the interaction pairing

Source `the November 2 reference manuscript` (SP) lines 2863-2865 (the moving
operator `L_{ν,c}(z) W = -V·∇W - (K_{d}W)·∇E_mov`), 2937-2958 (moving free adjoint `Φ`).

For a weak linearised flow `w` with velocity `u` and zero-circulation datum, at an age `r ≥ t₁`
with `a = a(r)`, `c = ν⁻²`, `d = c/√a`:
* `w(r)` has zero circulation (`zeroCirculationPreserved`) and `u(r)` is an `L²` Biot-Savart
  velocity of `w(r)`, hence `u(r) = K_c w(r)` a.e. on the cell (`kerVelCx_ae_eq_of_isBiotSavart_pos`:
  uniqueness against the kernel velocity, `FramePairing2/Core.lean`, `FramePairing2/Scale.lean`);
* `K_d(J_a⁻¹ w(r))(y) = a^{3/2}(K_c w(r))(√a y)`, `∇E_mov(y) = a^{5/2}∇E(√a y)`,
  `Φ(y) = a⁻¹φ(√a y)`, and `∫_{C_d} F(√a y) dy = a⁻¹ ∫_{C_c} F` (`cv_cell`).
Hence `-a⁻² ∫_{C_d} interactionTerm(W) Φ = a⁻² · a³ · a⁻¹ ∫_{C_c} (u·∇E) φ = ∫_{C_c} (u·∇E) φ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar

namespace UnforcedLeray.Short.IIIa

namespace ComplFreeRateSub

namespace Leaf2WeakEqFrame

theorem movingInteractionForm_proof (ν m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t₁ : ℝ) : UnforcedLeray.Short.IIIa.ComplFreeRateSub.Leaf2WeakEqFrame.MovingInteractionForm ν m tr t₁ := by
  intro hm hν ht₁ _hBUC f w u hw hf s g φ _hφ r hr
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hr0 : t₁ ≤ r := hr.1
  have ha : 0 < clockA ν r := by
    unfold clockA
    have : 0 ≤ ν * r := mul_nonneg hν.le (ht₁.trans hr0)
    linarith
  have hne : clockA ν r ≠ 0 := ha.ne'
  have hBS : IsBiotSavart (ν ^ (-2 : ℝ)) (w r) (u r) := hw.biotSavart r hr0
  have hZC : HasZeroCirculation (ν ^ (-2 : ℝ)) (w r) :=
    zeroCirculationPreserved ν (ν ^ (-2 : ℝ)) m hc (by linarith) tr t₁ f w u hw hf r hr0
  have hmem : MemLp (w r) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) := hw.memX r hr0
  have hid := KerBSAux.kerVelCx_ae_eq_of_isBiotSavart_pos hc hm hmem hZC hBS
  set G : ℝ × ℝ → ℂ := fun x =>
    (kerVelCx (ν ^ (-2 : ℝ)) (w r) x 0 * ((B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ) +
      kerVelCx (ν ^ (-2 : ℝ)) (w r) x 1 *
        ((B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ)) * φ r x with hG
  have hL : ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
      (u r x 0 * ((B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ) +
        u r x 1 * ((B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ)) * φ r x =
      ∫ x in B0579.cell (ν ^ (-2 : ℝ)), G x := by
    refine integral_congr_ae ?_
    filter_upwards [hid] with x hx
    simp only [hG]
    rw [hx 0, hx 1]
  have hpow : clockA ν r ^ ((3 : ℝ) / 2) * clockA ν r ^ ((5 : ℝ) / 2) * (clockA ν r)⁻¹ =
      clockA ν r ^ 3 := by
    rw [← Real.rpow_add ha, show (3 : ℝ) / 2 + 5 / 2 = ((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
    field_simp
  have hpowC : ((clockA ν r ^ ((3 : ℝ) / 2) : ℝ) : ℂ) * ((clockA ν r ^ ((5 : ℝ) / 2) : ℝ) : ℂ) *
      (((clockA ν r)⁻¹ : ℝ) : ℂ) = ((clockA ν r ^ 3 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, hpow]
  have hpt : ∀ y : ℝ × ℝ, interactionTerm tr r (movingW ν w r) y * movingPhi ν φ r y =
      -(((clockA ν r ^ 3 : ℝ) : ℂ) *
        G (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2)) := by
    intro y
    have hk : ∀ k : Fin 2, kerVelCx (dd ν r) (movingW ν w r) y k =
        ((clockA ν r ^ ((3 : ℝ) / 2) : ℝ) : ℂ) *
          kerVelCx (ν ^ (-2 : ℝ)) (w r)
            (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2) k :=
      fun k => KerBSAux.kerVelCx_jscaleInv ha (w r) y k
    unfold interactionTerm movingPhi movingTrainGradE
    rw [hk 0, hk 1]
    simp only [hG, Complex.ofReal_mul]
    rw [← hpowC]
    ring
  have hcv := cv_cell (c := ν ^ (-2 : ℝ)) ha G
  have hac : ((clockA ν r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hne
  have hcv' : ∫ y in B0579.cell (dd ν r),
      G (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2) =
      ((clockA ν r : ℝ) : ℂ)⁻¹ * ∫ x in B0579.cell (ν ^ (-2 : ℝ)), G x := by
    rw [← hcv, Complex.real_smul, ← mul_assoc, inv_mul_cancel₀ hac, one_mul]
  have hR : ∫ y in B0579.cell (dd ν r),
      interactionTerm tr r (movingW ν w r) y * movingPhi ν φ r y =
      -(((clockA ν r ^ 3 : ℝ) : ℂ) *
        (((clockA ν r : ℝ) : ℂ)⁻¹ * ∫ x in B0579.cell (ν ^ (-2 : ℝ)), G x)) := by
    calc ∫ y in B0579.cell (dd ν r), interactionTerm tr r (movingW ν w r) y * movingPhi ν φ r y
        = ∫ y in B0579.cell (dd ν r), -(((clockA ν r ^ 3 : ℝ) : ℂ) *
            G (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2)) :=
          integral_congr_ae (Eventually.of_forall hpt)
      _ = -(((clockA ν r ^ 3 : ℝ) : ℂ) * ∫ y in B0579.cell (dd ν r),
            G (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2)) := by
          rw [integral_neg, integral_const_mul]
      _ = _ := by rw [hcv']
  have hreal : clockA ν r ^ (-2 : ℝ) * clockA ν r ^ 3 * (clockA ν r)⁻¹ = 1 := by
    rw [Real.rpow_neg ha.le, Real.rpow_two]
    field_simp
  have hfinal : ((clockA ν r ^ (-2 : ℝ) : ℝ) : ℂ) * ((clockA ν r ^ 3 : ℝ) : ℂ) *
      ((clockA ν r : ℝ) : ℂ)⁻¹ = 1 := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Complex.ofReal_mul, hreal,
      Complex.ofReal_one]
  rw [hL, hR]
  linear_combination (-(∫ x in B0579.cell (ν ^ (-2 : ℝ)), G x)) * hfinal

end Leaf2WeakEqFrame

end ComplFreeRateSub

end UnforcedLeray.Short.IIIa
