import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S1
import UnforcedLeray.Short.PartIIa.Tasks.F06GraphBound
import UnforcedLeray.Short.PartIIa.Tasks.F08Projected
import UnforcedLeray.Short.PartIIa.Tasks.R06AxisSmooth
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.RingLiftSmoothExt
import UnforcedLeray.Short.PartIIb.Tasks.PhysicalRowReduction
import UnforcedLeray.Short.PartIIb.Tasks.QuadraticEstimate.InletLp
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.LerayForceProj.Reduction
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.SliceFieldElem
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.RingResidualProved
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEWeak
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEHess
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8.G1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8.G2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8.G3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_4_1_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_4_1.DerivY.IBP

/-!
# `Sub/PartII-b_S1_1.lean`: Decomposition of `DifferentiatedEquationGraphBound` (`PartII-b:S1/1`, SP 2525-2537)

Source of record: `the November 2 reference manuscript`
(SP), lines 2525-2537.

## Proved here (zero `sorry`)

1. **`grad_graphNormD_of_weak_eq` (unconditional)**: for `p.period ≤ 1`, if `g₀ : Fin 3 → Yq p.period q0E`
   satisfies `GEData p z g₀` and `⟨L0T p.ν Φ, g₀ j⟩ = ⟨Φ, F j⟩` on solenoidal tests `Φ`, then
   `commonBodyProjected` (`PartII-a:F08`), `gEGradSol_proof`, `gEBodyUniqueSol_proof`,
   `gELerayPairSol_proof`, `commonBodyGraphBound` (`PartII-a:F06`) at `μ = 0`, and
   `RieszLp.norm_lerayY_le` upgrade `g₀` to `g : Fin 3 → B0411.D p.period p.ν q0E` with
   `(g j : Yq p.period q0E) = g₀ j` and `B0411.graphNormD (g j) ≤ C_body * ‖F j‖`.
2. **`exists_grad_and_hess_bound` and `grad_and_hess_bound_of_geData` (unconditional)**: for
   `p.period ≤ 1` and `p.ν ≤ 1`, `commonBodyGraphBound` and `freeGraphHessian_of` at `μ = 0`
   produce the distributional gradient `g₀` and Hessian `h` of `p.wOf z` in `Yq p.period q0E` with
   `‖g₀ j‖ ≤ C_GH * (p.ν ^ 1)⁻¹ * ‖z‖` and `‖h j k‖ ≤ C_GH * (p.ν ^ 1)⁻¹ * ‖z‖`; by uniqueness
   (`B0411.hasPhaseOp_unique`), any `g₀, h` satisfying `GEData p z g₀` and
   `∀ j k, HasPhaseOp (-dy k) (g₀ j) (h j k)` satisfy the same `Yq` bounds.
3. **`diffEq_inlet_bound_of_affineInletFacts` (unconditional from `h4 : AffineInletFacts`)**:
   using `h4.2.1 : InletSourceBound`, `hasPtwOp_dy_iff`, and `R_rpow_mul_norm_coord_le`, the
   differentiated inlet source in `gEWeak` is represented by `Fi : Fin 2 → Yq p.period q0E` with
   `‖∑ i : Fin 2, (p.coord z i : ℂ) • Fi i‖ ≤ C_in * (p.ν ^ k_in)⁻¹ * ‖z‖`.
4. **`ringLiftSmoothExt_proof` and `diffEqRawBound_proof` (unconditional)**: combining
   `UnforcedLeray.Short.PartIIa.ringAxisSmooth` (`PartII-a:R06`), `ringLiftSmoothExt_of`
   (`PartII-b:R1/6`), `ringResidualBound_proved`, `rawResidualWeakIdentity_of_lift`,
   `sliceFieldElem_proof`, and `sliceIntegrationByParts_thm`, the differentiated raw residual
   source in `gEWeak` is represented by `Fr : Yq p.period q0E` with
   `‖Fr‖ ≤ C_raw * (p.ν ^ k_raw)⁻¹ * p.ε ^ (3 / 11 : ℝ)`.
5. **`exp_eps_le_one_of_two_mul_lt` (unconditional)**: when `0 < m`, `0 < dm`, and
   `2 * m < 3 * dm / 11`, in `BgRegime p d dm dp` one has
   `Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) ≤ 1`, absorbing the quadratic factor
   `(Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ)) ^ 2 ≤ Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ)`.
6. **`differentiatedEquationGraphBound_of_leaves`**: assembly of `DifferentiatedEquationGraphBound`
   from `DiffEqLinBound` (`PartII-b:S1/1/1`), `DiffEqQuadBound` (`PartII-b:S1/1/2`),
   `h4 : AffineInletFacts`, and `hQ1 : QuadBound`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03 UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace
  UnforcedLeray.B0411 UnforcedLeray.B0412 UnforcedLeray.Blueprint
  UnforcedLeray.Short.PartIIIb.Concrete

namespace DiffEqSub

local instance fact_q0_ge_one_de : Fact (1 ≤ ENNReal.ofReal B0281.q0) :=
  inferInstanceAs (Fact (1 ≤ q0E))

/-! ## 1. Unconditional body operator bound and quantitative upgrade to `D_p` -/

/-- At shift `μ = 0`, `bodyOp P ν r 0 u = L0D u` has `Yq` norm at most `B0411.graphNormD u`. -/
theorem norm_bodyOp_zero_le_graphNormD {P ν : ℝ} [Fact (0 < P)] {r : ℝ≥0∞} [Fact (1 ≤ r)]
    (u : B0411.D P ν r) :
    ‖Short.PartIIa.bodyOp P ν r 0 u‖ ≤ B0411.graphNormD u := by
  have hbody : Short.PartIIa.bodyOp P ν r 0 u = L0D u := by
    simp [Short.PartIIa.bodyOp, L0L_apply]
  rw [hbody]
  unfold L0D B0411.graphNormD
  have h1 : ‖T0D u - nuLapD u - (1 / 2 : ℂ) • (u : Yq P r)‖ ≤
      ‖T0D u - nuLapD u‖ + ‖(1 / 2 : ℂ) • (u : Yq P r)‖ := norm_sub_le _ _
  have h2 : ‖T0D u - nuLapD u‖ ≤ ‖T0D u‖ + ‖nuLapD u‖ := norm_sub_le _ _
  have h3 : ‖(1 / 2 : ℂ) • (u : Yq P r)‖ = (1 / 2 : ℝ) * ‖(u : Yq P r)‖ := by
    rw [norm_smul]
    norm_num
  have hu0 : 0 ≤ ‖(u : Yq P r)‖ := norm_nonneg _
  linarith

/-- For any `z : p.Z`, `‖bodyOp p.period p.ν q0E 0 (B0412.XToD (p.graphX z))‖ ≤ ‖z‖`. -/
theorem norm_bodyOp_graphX_le_norm (p : Params) (z : p.Z) :
    ‖Short.PartIIa.bodyOp p.period p.ν q0E 0 (B0412.XToD (p.graphX z))‖ ≤ ‖z‖ :=
  (norm_bodyOp_zero_le_graphNormD _).trans (S1Sub.graphNormD_graphX_le_norm p z)

/-- Unconditional quantitative upgrade from the differentiated weak equation on solenoidal tests to
`B0411.D p.period p.ν q0E` via `commonBodyProjected`, `gEGradSol_proof`, `gEBodyUniqueSol_proof`,
`gELerayPairSol_proof`, `commonBodyGraphBound`, and `RieszLp.norm_lerayY_le`. -/
theorem grad_graphNormD_of_weak_eq :
    ∃ C_body : ℝ, 0 < C_body ∧ ∀ (p : Params), p.period ≤ 1 →
      ∀ (z : p.Z) (g₀ : Fin 3 → Yq p.period q0E), GEData p z g₀ →
      ∀ (F : Fin 3 → Yq p.period q0E),
        (∀ (j : Fin 3) Φ, IsSolTest p.period Φ →
          phasePair p.period q0E (L0T p.ν Φ) (g₀ j) = phasePair p.period q0E Φ (F j)) →
        ∃ g : Fin 3 → B0411.D p.period p.ν q0E,
          (∀ j : Fin 3, (g j : Yq p.period q0E) = g₀ j) ∧
          (∀ j : Fin 3, B0411.graphNormD (g j) ≤ C_body * ‖F j‖) := by
  obtain ⟨C₀, hC₀, HB⟩ := Short.PartIIa.commonBodyGraphBound q0E q0E_gt_one B0412.q0E_lt_three
  set γ₀ : ℝ := Short.PartIIa.gammaR q0E
  have hγ₀ : 0 < γ₀ := gammaR_q0E_pos
  set K_L : ℝ := ‖UnforcedLeray.RieszLp.lerayC q0E q0E_gt_one (ne_top_of_lt B0412.q0E_lt_three)‖
  have hK_L0 : 0 ≤ K_L := norm_nonneg _
  set C_body : ℝ := C₀ * (1 + 1 / γ₀) * K_L + 1
  have hC_body : 0 < C_body := by positivity
  refine ⟨C_body, hC_body, ?_⟩
  intro p hP1 z g₀ hd F hF
  have h_ex : ∀ j : Fin 3, ∃ u : B0411.D p.period p.ν q0E,
      (u : Yq p.period q0E) = g₀ j ∧ B0411.graphNormD u ≤ C_body * ‖F j‖ := by
    intro j
    have hgσ : g₀ j ∈ Ysigma p.period q0E := gEGradSol_proof p z g₀ hd j
    obtain ⟨u, huσ, hu⟩ := Short.PartIIa.commonBodyProjected
      q0E q0E_gt_one B0412.q0E_lt_three p.period hP1 p.ν p.ν_pos 0 (by simpa using hγ₀) (F j)
    have hL : L0D u = UnforcedLeray.RieszLp.lerayY p.period q0E q0E_gt_one
        (ne_top_of_lt B0412.q0E_lt_three) (F j) := by
      simpa [Short.PartIIa.bodyOp, L0L_apply] using hu
    have hv : g₀ j - (u : Yq p.period q0E) = 0 := by
      refine gEBodyUniqueSol_proof p.period p.ν hP1 p.ν_pos _ (Submodule.sub_mem _ hgσ huσ) ?_
      intro Φ hΦ
      rw [map_sub, hF j Φ hΦ, hasPhaseOp_L0D u Φ hΦ.1, hL,
        gELerayPairSol_proof p.period (F j) Φ hΦ, sub_self]
    have hgu : (u : Yq p.period q0E) = g₀ j := (sub_eq_zero.1 hv).symm
    obtain ⟨g_u, -, hgn_u⟩ := HB p.period hP1 p.ν p.ν_pos 0 (by simpa using hγ₀) u
    have hsqrt_nonneg : 0 ≤ Real.sqrt p.ν * ∑ k : Fin 3, ‖g_u k‖ :=
      mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    have hgn1 : B0411.graphNormD u ≤
        C₀ * (1 + 1 / γ₀) * ‖Short.PartIIa.bodyOp p.period p.ν q0E 0 u‖ := by
      simpa [γ₀] using (le_add_of_nonneg_right hsqrt_nonneg).trans hgn_u
    have hleray : ‖Short.PartIIa.bodyOp p.period p.ν q0E 0 u‖ ≤ K_L * ‖F j‖ := by
      rw [hu]
      exact ((UnforcedLeray.RieszLp.lerayY p.period q0E q0E_gt_one
        (ne_top_of_lt B0412.q0E_lt_three)).le_opNorm (F j)).trans
        (mul_le_mul_of_nonneg_right
          (UnforcedLeray.RieszLp.norm_lerayY_le q0E_gt_one (ne_top_of_lt B0412.q0E_lt_three))
          (norm_nonneg _))
    have hgn2 : B0411.graphNormD u ≤ C_body * ‖F j‖ := by
      calc B0411.graphNormD u
          ≤ C₀ * (1 + 1 / γ₀) * (K_L * ‖F j‖) :=
            hgn1.trans (mul_le_mul_of_nonneg_left hleray (by positivity))
        _ = (C₀ * (1 + 1 / γ₀) * K_L) * ‖F j‖ := by ring
        _ ≤ C_body * ‖F j‖ := by
            have : C₀ * (1 + 1 / γ₀) * K_L ≤ C_body := by dsimp [C_body]; linarith
            gcongr
    exact ⟨u, hgu, hgn2⟩
  choose g hg_eq hg_bd using h_ex
  exact ⟨g, hg_eq, hg_bd⟩

/-! ## 2. Unconditional existence and `Yq` bounds for the gradient `g₀` and Hessian `h` of `p.wOf z` -/

/-- The assembled `FreeGraphHessian` theorem from `GradEq/GEHess.lean`. -/
theorem freeGraphHessian_proved : FreeGraphHessian :=
  freeGraphHessian_of (bodyHessianBound_of
    (localWindowHess_of windowBackHess)
    (globalHessFieldWindowBound_of windowHessAEMeas windowHessUnique windowHessPoU
      (windowHessPeriodic_of windowHessUnique))
    (hessFieldToYRep_of windowTestIdentityHess))

/-- For `0 < ν ≤ 1`, `ν ≤ Real.sqrt ν`. -/
theorem self_le_sqrt_of_le_one {ν : ℝ} (hν0 : 0 < ν) (hν1 : ν ≤ 1) : ν ≤ Real.sqrt ν := by
  have h1 : Real.sqrt ν ≤ 1 := Real.sqrt_le_one.mpr hν1
  calc ν = Real.sqrt ν * Real.sqrt ν := (Real.mul_self_sqrt hν0.le).symm
    _ ≤ 1 * Real.sqrt ν := mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg ν)
    _ = Real.sqrt ν := one_mul _

/-- Unconditional existence and polynomial-in-`ν⁻¹` `Yq` norm bounds for the distributional
gradient `g₀` and Hessian `h` of `p.wOf z`. -/
theorem exists_grad_and_hess_bound :
    ∃ C_GH : ℝ, 0 < C_GH ∧ ∀ (p : Params), p.period ≤ 1 → p.ν ≤ 1 → ∀ z : p.Z,
      ∃ (g₀ : Fin 3 → Yq p.period q0E) (h : Fin 3 → Fin 3 → Yq p.period q0E),
        (∀ j : Fin 3, HasPhaseOp (fun Φ => -dy j Φ) (p.wOf z) (g₀ j)) ∧
        (∀ j k : Fin 3, HasPhaseOp (fun Φ => -dy k Φ) (g₀ j) (h j k)) ∧
        (∀ j : Fin 3, ‖g₀ j‖ ≤ C_GH * (p.ν ^ 1)⁻¹ * ‖z‖) ∧
        (∀ j k : Fin 3, ‖h j k‖ ≤ C_GH * (p.ν ^ 1)⁻¹ * ‖z‖) := by
  obtain ⟨C₁, hC₁, HB⟩ := Short.PartIIa.commonBodyGraphBound q0E q0E_gt_one B0412.q0E_lt_three
  obtain ⟨C₂, hC₂, HH⟩ := freeGraphHessian_proved q0E q0E_gt_one B0412.q0E_lt_three
  set γ₀ : ℝ := Short.PartIIa.gammaR q0E
  have hγ₀ : 0 < γ₀ := gammaR_q0E_pos
  set C_GH : ℝ := (C₁ + C₂) * (1 + 1 / γ₀) + 1
  have hC_GH : 0 < C_GH := by positivity
  refine ⟨C_GH, hC_GH, ?_⟩
  intro p hP1 hν1 z
  let u_z : B0411.D p.period p.ν q0E := B0412.XToD (p.graphX z)
  have hu_coe : (u_z : Yq p.period q0E) = p.wOf z := rfl
  obtain ⟨g₀, hg₀, hbd_g⟩ := HB p.period hP1 p.ν p.ν_pos 0 (by simpa using hγ₀) u_z
  obtain ⟨h, hh, hbd_h⟩ := HH p.period hP1 p.ν p.ν_pos 0 (by simpa using hγ₀) u_z g₀ hg₀
  have hbody_le : ‖Short.PartIIa.bodyOp p.period p.ν q0E 0 u_z‖ ≤ ‖z‖ :=
    norm_bodyOp_graphX_le_norm p z
  have hν_pos : 0 < p.ν := p.ν_pos
  have hν_sqrt : p.ν ≤ Real.sqrt p.ν := self_le_sqrt_of_le_one hν_pos hν1
  have hgn_nonneg : 0 ≤ B0411.graphNormD u_z := S1Sub.s1_graphNormD_nonneg u_z
  have hsum_g_nonneg : 0 ≤ ∑ j : Fin 3, ‖g₀ j‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hsum_g : p.ν * ∑ j : Fin 3, ‖g₀ j‖ ≤ C_GH * ‖z‖ := by
    have h1 : p.ν * ∑ j : Fin 3, ‖g₀ j‖ ≤ Real.sqrt p.ν * ∑ j : Fin 3, ‖g₀ j‖ :=
      mul_le_mul_of_nonneg_right hν_sqrt hsum_g_nonneg
    have h2 : Real.sqrt p.ν * ∑ j : Fin 3, ‖g₀ j‖ ≤
        C₁ * (1 + 1 / γ₀) * ‖Short.PartIIa.bodyOp p.period p.ν q0E 0 u_z‖ := by
      simpa [γ₀] using (le_add_of_nonneg_left hgn_nonneg).trans hbd_g
    calc p.ν * ∑ j : Fin 3, ‖g₀ j‖
        ≤ C₁ * (1 + 1 / γ₀) * ‖Short.PartIIa.bodyOp p.period p.ν q0E 0 u_z‖ := h1.trans h2
      _ ≤ C₁ * (1 + 1 / γ₀) * ‖z‖ :=
          mul_le_mul_of_nonneg_left hbody_le (by positivity)
      _ ≤ C_GH * ‖z‖ := by
          have : C₁ * (1 + 1 / γ₀) ≤ C_GH := by
            dsimp [C_GH]
            nlinarith [hC₂, div_pos zero_lt_one hγ₀]
          gcongr
  have hsum_h : p.ν * ∑ j : Fin 3, ∑ k : Fin 3, ‖h j k‖ ≤ C_GH * ‖z‖ := by
    have h2 : p.ν * ∑ j : Fin 3, ∑ k : Fin 3, ‖h j k‖ ≤
        C₂ * (1 + 1 / γ₀) * ‖Short.PartIIa.bodyOp p.period p.ν q0E 0 u_z‖ := by
      simpa [γ₀] using hbd_h
    calc p.ν * ∑ j : Fin 3, ∑ k : Fin 3, ‖h j k‖
        ≤ C₂ * (1 + 1 / γ₀) * ‖Short.PartIIa.bodyOp p.period p.ν q0E 0 u_z‖ := h2
      _ ≤ C₂ * (1 + 1 / γ₀) * ‖z‖ :=
          mul_le_mul_of_nonneg_left hbody_le (by positivity)
      _ ≤ C_GH * ‖z‖ := by
          have : C₂ * (1 + 1 / γ₀) ≤ C_GH := by
            dsimp [C_GH]
            nlinarith [hC₁, div_pos zero_lt_one hγ₀]
          gcongr
  refine ⟨g₀, h, hg₀, hh, ?_, ?_⟩
  · intro j
    have hj : ‖g₀ j‖ ≤ ∑ j' : Fin 3, ‖g₀ j'‖ :=
      Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    have hmul : p.ν * ‖g₀ j‖ ≤ C_GH * ‖z‖ :=
      (mul_le_mul_of_nonneg_left hj hν_pos.le).trans hsum_g
    calc ‖g₀ j‖ = (p.ν ^ 1)⁻¹ * (p.ν * ‖g₀ j‖) := by
          rw [pow_one, inv_mul_cancel_left₀ hν_pos.ne']
      _ ≤ (p.ν ^ 1)⁻¹ * (C_GH * ‖z‖) :=
          mul_le_mul_of_nonneg_left hmul (by positivity)
      _ = C_GH * (p.ν ^ 1)⁻¹ * ‖z‖ := by ring
  · intro j k
    have hjk : ‖h j k‖ ≤ ∑ j' : Fin 3, ∑ k' : Fin 3, ‖h j' k'‖ := by
      refine (Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ k)).trans ?_
      exact Finset.single_le_sum (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
        (Finset.mem_univ j)
    have hmul : p.ν * ‖h j k‖ ≤ C_GH * ‖z‖ :=
      (mul_le_mul_of_nonneg_left hjk hν_pos.le).trans hsum_h
    calc ‖h j k‖ = (p.ν ^ 1)⁻¹ * (p.ν * ‖h j k‖) := by
          rw [pow_one, inv_mul_cancel_left₀ hν_pos.ne']
      _ ≤ (p.ν ^ 1)⁻¹ * (C_GH * ‖z‖) :=
          mul_le_mul_of_nonneg_left hmul (by positivity)
      _ = C_GH * (p.ν ^ 1)⁻¹ * ‖z‖ := by ring

/-- By uniqueness of `HasPhaseOp` (`B0411.hasPhaseOp_unique`), any `g₀, h` satisfying `GEData p z g₀`
and `∀ j k, HasPhaseOp (-dy k) (g₀ j) (h j k)` satisfy the quantitative `Y_{q₀}` bounds of
`exists_grad_and_hess_bound`. -/
theorem grad_and_hess_bound_of_geData :
    ∃ C_GH : ℝ, 0 < C_GH ∧
      ∀ (p : Params), p.period ≤ 1 → p.ν ≤ 1 → ∀ (z : p.Z)
        (g₀ : Fin 3 → Yq p.period q0E) (h : Fin 3 → Fin 3 → Yq p.period q0E),
        GEData p z g₀ → (∀ j k : Fin 3, HasPhaseOp (fun Φ => -dy k Φ) (g₀ j) (h j k)) →
        (∀ j : Fin 3, ‖g₀ j‖ ≤ C_GH * (p.ν ^ 1)⁻¹ * ‖z‖) ∧
        (∀ j k : Fin 3, ‖h j k‖ ≤ C_GH * (p.ν ^ 1)⁻¹ * ‖z‖) := by
  obtain ⟨C_GH, hC_GH, HGH⟩ := exists_grad_and_hess_bound
  refine ⟨C_GH, hC_GH, fun p hP1 hν1 z g₀ h hg h_op => ?_⟩
  obtain ⟨g₀', h', hg₀'_op, hh'_op, hg₀'_bd, hh'_bd⟩ := HGH p hP1 hν1 z
  have hg_eq : ∀ j : Fin 3, g₀ j = g₀' j := fun j =>
    B0411.hasPhaseOp_unique (hg.2 j) (hg₀'_op j)
  have hh_eq : ∀ j k : Fin 3, h j k = h' j k := fun j k => by
    have h_op' : HasPhaseOp (fun Φ => -dy k Φ) (g₀' j) (h j k) := by
      rw [← hg_eq j]
      exact h_op j k
    exact B0411.hasPhaseOp_unique h_op' (hh'_op j k)
  exact ⟨fun j => by rw [hg_eq j]; exact hg₀'_bd j,
    fun j k => by rw [hh_eq j k]; exact hh'_bd j k⟩

/-! ## 3. Differentiated inlet bound from `h4 : AffineInletFacts` -/

/-- From `h4 : AffineInletFacts` (`InletSourceBound`, SP 2383), the differentiated inlet source in
`gEWeak` is represented by `Fi : Fin 2 → Yq p.period q0E` with
`‖∑ i : Fin 2, (p.coord z i : ℂ) • Fi i‖ ≤ C_in * (p.ν ^ k_in)⁻¹ * ‖z‖`. -/
theorem diffEq_inlet_bound_of_affineInletFacts (h4 : AffineInletFacts)
    (Sig : ℝ) (lam : ℂ) (q : Planar.Profile) (hSig : 0 < Sig)
    (hq : Planar.IsGrowingEigenpair lam q) (dm dp : ℝ) (hdm : 0 < dm) :
    ∃ (C_in : ℝ) (k_in : ℕ) (ν_in : ℝ), 0 < C_in ∧ 0 < ν_in ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν_in → p.ageCut = Sig → p.mode = q →
        ∀ (z : p.Z) (j : Fin 3), ∃ Fi : Fin 2 → Yq p.period q0E,
          (∀ (i : Fin 2) Φ, IsSolTest p.period Φ →
            pairF p.period (L0T p.ν (dy j Φ)) (p.Efun i) +
              pairF p.period (convT p.raw (dy j Φ)) (p.Efun i) =
                phasePair p.period q0E Φ (Fi i)) ∧
          ‖∑ i : Fin 2, (p.coord z i : ℂ) • Fi i‖ ≤ C_in * (p.ν ^ k_in)⁻¹ * ‖z‖ := by
  obtain ⟨C₀, k₀, ν₀, hC₀, hν₀, Hsrc⟩ := h4.2.1 Sig lam q hSig hq dm dp hdm
  refine ⟨2 * C₀, k₀, min ν₀ 1, by positivity, lt_min hν₀ zero_lt_one, ?_⟩
  intro p d hreg hν hSg hmode z j
  have hν0 : p.ν ≤ ν₀ := hν.trans (min_le_left _ _)
  have hν_le1 : p.ν ≤ 1 := hν.trans (min_le_right _ _)
  have hex : ∀ i : Fin 2, ∃ F_i : Yq p.period q0E,
      (∀ Φ, IsSolTest p.period Φ →
        pairF p.period (L0T p.ν (dy j Φ)) (p.Efun i) +
          pairF p.period (convT p.raw (dy j Φ)) (p.Efun i) =
            phasePair p.period q0E Φ F_i) ∧
      ‖F_i‖ ≤ C₀ * (p.ν ^ k₀)⁻¹ * p.R ^ (8 / 11 : ℝ) := by
    intro i
    obtain ⟨g_in, G_in, hrel, hptw, hbd⟩ := Hsrc p d hreg hν0 hSg hmode i
    have hop : HasPhaseOp (fun Φ => -dy j Φ) (g_in : Yq p.period q0E) (G_in j) :=
      (hasPtwOp_dy_iff p.period j (g_in : Yq p.period q0E) (G_in j)).mp (hptw j)
    have hE_cont : Continuous (p.Efun i) :=
      continuous_Efun_of_growingEigenpair hreg hν_le1 (hmode ▸ hq) i
    refine ⟨-(G_in j), ?_, ?_⟩
    · intro Φ hΦ
      have hΨ : IsSolTest p.period (dy j Φ) := gEW_isSolTest_dy hΦ j
      have hadd : pairF p.period (L0T p.ν (dy j Φ)) (p.Efun i) +
            pairF p.period (convT p.raw (dy j Φ)) (p.Efun i) =
          pairF p.period (fun x => L0T p.ν (dy j Φ) x + convT p.raw (dy j Φ) x) (p.Efun i) :=
        (pairF_L0T_add_convT_Efun hreg i hE_cont hΨ.1).symm
      rw [hadd, ← hrel (dy j Φ) hΨ]
      have hneg1 : phasePair p.period q0E (-dy j Φ) (g_in : Yq p.period q0E) =
          -phasePair p.period q0E (dy j Φ) (g_in : Yq p.period q0E) :=
        phasePair_neg hΨ.1 (g_in : Yq p.period q0E)
      have hneg2 : phasePair p.period q0E Φ (-(G_in j)) =
          -phasePair p.period q0E Φ (G_in j) := map_neg _ _
      rw [hneg2, ← hop Φ hΦ.1, hneg1, neg_neg]
    · rw [norm_neg]
      have hj_le : ‖G_in j‖ ≤ ‖g_in‖ + ∑ j' : Fin 3, ‖G_in j'‖ := by
        have h1 : ‖G_in j‖ ≤ ∑ j' : Fin 3, ‖G_in j'‖ :=
          Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
        linarith [norm_nonneg g_in]
      have hexp : (2 : ℝ) / bgp = 8 / 11 := by norm_num [bgp]
      rw [← hexp]
      exact hj_le.trans hbd
  choose Fi hFi_pair hFi_bd using hex
  refine ⟨Fi, hFi_pair, ?_⟩
  have hRz : p.R ^ (8 / 11 : ℝ) * ‖p.coord z‖ ≤ ‖z‖ := R_rpow_mul_norm_coord_le p z
  have hterm : ∀ i : Fin 2, ‖(p.coord z i : ℂ) • Fi i‖ ≤ C₀ * (p.ν ^ k₀)⁻¹ * ‖z‖ := by
    intro i
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    have hcoord_i : |p.coord z i| ≤ ‖p.coord z‖ := norm_le_pi_norm (p.coord z) i
    calc |p.coord z i| * ‖Fi i‖
        ≤ ‖p.coord z‖ * (C₀ * (p.ν ^ k₀)⁻¹ * p.R ^ (8 / 11 : ℝ)) :=
          mul_le_mul hcoord_i (hFi_bd i) (norm_nonneg _) (norm_nonneg _)
      _ = C₀ * (p.ν ^ k₀)⁻¹ * (p.R ^ (8 / 11 : ℝ) * ‖p.coord z‖) := by ring
      _ ≤ C₀ * (p.ν ^ k₀)⁻¹ * ‖z‖ := by
          have : 0 ≤ C₀ * (p.ν ^ k₀)⁻¹ := by have := p.ν_pos; positivity
          gcongr
  calc ‖∑ i : Fin 2, (p.coord z i : ℂ) • Fi i‖
      ≤ ∑ i : Fin 2, ‖(p.coord z i : ℂ) • Fi i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 2, C₀ * (p.ν ^ k₀)⁻¹ * ‖z‖ := Finset.sum_le_sum fun i _ => hterm i
    _ = 2 * C₀ * (p.ν ^ k₀)⁻¹ * ‖z‖ := by
        rw [Fin.sum_univ_two]
        ring

/-! ## 4. Differentiated raw residual bound from `RingLiftSmoothExt` -/

/-- Quantitative `Yq` bound on the differentiated raw residual source in `gEWeak`: for each
`gF : Yq p.period q0E` with `p.RawRel gF` and each `j : Fin 3`, there is `Fr : Yq p.period q0E`
representing `Φ ↦ ⟨∂_jΦ, gF⟩` on solenoidal tests with
`‖Fr‖ ≤ C_raw * (p.ν ^ k_raw)⁻¹ * p.ε ^ (3 / 11 : ℝ)`. -/
def DiffEqRawBound : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∃ (C_raw : ℝ) (k_raw : ℕ) (ν_raw : ℝ), 0 < C_raw ∧ 0 < ν_raw ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν_raw →
      ∀ gF : Yq p.period q0E, p.RawRel gF → ∀ j : Fin 3,
        ∃ Fr : Yq p.period q0E,
          (∀ Φ, IsSolTest p.period Φ →
            phasePair p.period q0E (dy j Φ) gF = phasePair p.period q0E Φ Fr) ∧
          ‖Fr‖ ≤ C_raw * (p.ν ^ k_raw)⁻¹ * p.ε ^ (3 / 11 : ℝ)

/-- Proof of `DiffEqRawBound` from `hLift : RingLiftSmoothExt` (`PartII-b:R1/6`), using
`ringResidualBound_proved`, `rawResidualWeakIdentity_of_lift`, `sliceFieldElem_proof`, and
`sliceIntegrationByParts_thm`. -/
theorem diffEq_raw_bound_of_lift (hLift : RingLiftSmoothExt) : DiffEqRawBound := by
  intro dm dp hdm
  obtain ⟨ν₁, hν₁, C₁, d₁, H1⟩ :=
    ringResidualBound_proved 2 (11 / 4) (by norm_num) (by norm_num)
  obtain ⟨ν₂, hν₂, H2⟩ := UnforcedLeray.Short.PartIIIb.rawResidualWeakIdentity_of_lift hLift
  have hC₁ : 0 < max C₁ 1 := lt_max_of_lt_right one_pos
  set C_raw : ℝ := max C₁ 1 * 3 ^ d₁
  set k_raw : ℕ := 2 * d₁
  set ν_raw : ℝ := min (min (ν₁ / 2) (ν₂ / 2)) (min 1 (min dm (dm ^ 3 / 12)))
  have hC_raw : 0 < C_raw := by positivity
  have hν_raw : 0 < ν_raw :=
    lt_min (lt_min (by linarith) (by linarith))
      (lt_min one_pos (lt_min hdm (by positivity)))
  refine ⟨C_raw, k_raw, ν_raw, hC_raw, hν_raw, ?_⟩
  intro p d hreg hν gF hRel j
  have hνpos : 0 < p.ν := p.ν_pos
  have hν1 : p.ν < ν₁ :=
    lt_of_le_of_lt (hν.trans ((min_le_left _ _).trans (min_le_left _ _))) (by linarith)
  have hν2 : p.ν < ν₂ :=
    lt_of_le_of_lt (hν.trans ((min_le_left _ _).trans (min_le_right _ _))) (by linarith)
  have hν3 : p.ν ≤ 1 := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν4 : p.ν ≤ dm :=
    hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hν5 : p.ν ≤ dm ^ 3 / 12 :=
    hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hc : p.c = (p.ν ^ 2)⁻¹ := hreg.c_eq
  have hR : 2 ≤ p.R := two_le_R_of_regime hreg hν4
  obtain ⟨hper, G, hmem, hG, hbd, hcont⟩ :=
    H1 p.ν ⟨hνpos, hν1⟩ (trainStream p) (trainPressure p)
      (isExactPlanarTrain_params_rpow p hreg.train_buc hc) p.R hR
  have hper' : ∀ τ, Short.PartIIa.ringResidual p.R p.ν (trainStream p) (trainPressure p)
        (τ + p.period) =
      Short.PartIIa.ringResidual p.R p.ν (trainStream p) (trainPressure p) τ := fun τ => by
    rw [← period_eq_rpow p hc]; exact hper τ
  have hP0 : 0 < p.period := p.period_pos
  have hq : (q0E : ℝ≥0∞) = ENNReal.ofReal (11 / 4) := rfl
  have hGmem : ∀ τ, MemLp (G τ j) q0E volume := fun τ => by rw [hq]; exact (hG τ j).1
  have hGloc : ∀ τ, LocallyIntegrable (G τ j) volume := fun τ =>
    (hGmem τ).locallyIntegrable (by rw [hq]; exact ENNReal.one_le_ofReal.mpr (by norm_num))
  have hae1 : ∀ τ, G (τ + p.period) j =ᵐ[volume] G τ j := fun τ => by
    refine UnforcedLeray.Blueprint.L01.weakDerivative_ae_eq (i := j) ?_ (hG τ j).2
      (hGloc _) (hGloc _)
    have := (hG (τ + p.period) j).2
    rwa [hper' τ] at this
  have haeZ : ∀ n : ℤ, ∀ τ, G (τ + n * p.period) j =ᵐ[volume] G τ j := by
    intro n
    induction n using Int.induction_on with
    | zero => intro τ; simp
    | succ n ih =>
      intro τ
      have e : τ + ((n : ℤ) + 1 : ℤ) * p.period = (τ + n * p.period) + p.period := by
        push_cast; ring
      rw [e]
      exact (hae1 _).trans (ih τ)
    | pred n ih =>
      intro τ
      have e : τ + ((-(n : ℤ) - 1 : ℤ) : ℝ) * p.period + p.period =
          τ + ((-(n : ℤ) : ℤ) : ℝ) * p.period := by
        push_cast; ring
      have h1 := hae1 (τ + ((-(n : ℤ) - 1 : ℤ) : ℝ) * p.period)
      rw [e] at h1
      exact h1.symm.trans (ih τ)
  set P := p.period
  let Gf : ℝ → SpatialField := fun τ => G (τ - P * (⌊τ / P⌋ : ℤ)) j
  have hae : ∀ τ, Gf τ =ᵐ[volume] G τ j := fun τ => by
    have e : τ - P * (⌊τ / P⌋ : ℤ) = τ + ((-⌊τ / P⌋ : ℤ) : ℝ) * P := by push_cast; ring
    show G (τ - P * (⌊τ / P⌋ : ℤ)) j =ᵐ[volume] G τ j
    rw [e]; exact haeZ _ τ
  have hGf_per : ∀ τ, Gf (τ + P) = Gf τ := by
    intro τ
    have hfl : ⌊(τ + P) / P⌋ = ⌊τ / P⌋ + 1 := by
      rw [show (τ + P) / P = τ / P + 1 by field_simp, Int.floor_add_one]
    show G (τ + P - P * (⌊(τ + P) / P⌋ : ℤ)) j = G (τ - P * (⌊τ / P⌋ : ℤ)) j
    rw [hfl, show τ + P - P * ((⌊τ / P⌋ + 1 : ℤ) : ℝ) = τ - P * (⌊τ / P⌋ : ℤ) by push_cast; ring]
  have hGf_mem : ∀ τ, MemLp (Gf τ) q0E volume := fun τ => (hGmem τ).ae_eq (hae τ).symm
  have hF_mem : ∀ τ, MemLp (Short.PartIIa.ringResidual p.R p.ν (trainStream p)
      (trainPressure p) τ) q0E volume := fun τ => by rw [hq]; exact hmem τ
  have hF_cont : ∀ τ₀, Tendsto (fun τ => (eLpNorm
      (Short.PartIIa.ringResidual p.R p.ν (trainStream p) (trainPressure p) τ -
        Short.PartIIa.ringResidual p.R p.ν (trainStream p) (trainPressure p) τ₀)
      q0E volume).toReal) (𝓝 τ₀) (𝓝 0) := by
    intro τ₀
    rw [hq]
    refine squeeze_zero (fun _ => ENNReal.toReal_nonneg) (fun _ => ?_) (hcont τ₀)
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg)
  have hGf_cont : ∀ τ₀, Tendsto (fun τ => (eLpNorm (Gf τ - Gf τ₀) q0E volume).toReal)
      (𝓝 τ₀) (𝓝 0) := by
    intro τ₀
    rw [hq]
    refine squeeze_zero (fun _ => ENNReal.toReal_nonneg) (fun τ => ?_) (hcont τ₀)
    have e : eLpNorm (Gf τ - Gf τ₀) (ENNReal.ofReal (11 / 4)) volume =
        eLpNorm (G τ j - G τ₀ j) (ENNReal.ofReal (11 / 4)) volume :=
      eLpNorm_congr_ae ((hae τ).sub (hae τ₀))
    rw [e]
    refine le_add_of_nonneg_of_le ENNReal.toReal_nonneg ?_
    exact Finset.single_le_sum (f := fun i => (eLpNorm (G τ i - G τ₀ i)
      (ENNReal.ofReal (11 / 4)) volume).toReal) (fun _ _ => ENNReal.toReal_nonneg)
      (Finset.mem_univ j)
  have hGf_weak : ∀ τ, HasWeakSpatialDerivative j
      (Short.PartIIa.ringResidual p.R p.ν (trainStream p) (trainPressure p) τ) (Gf τ) :=
    fun τ => (hG τ j).2.congr (Filter.EventuallyEq.refl _ _) (hae τ).symm
  obtain ⟨Fr, hFr_pair, hFr_bd, -, -⟩ := sliceFieldElem_proof p (fun τ => -(Gf τ))
    (fun τ => congrArg Neg.neg (hGf_per τ))
    (fun τ => (hGf_mem τ).neg)
    (fun τ₀ => (hGf_cont τ₀).congr fun τ => by rw [neg_sub_neg, eLpNorm_sub_comm])
  set B₀ : ℝ := Short.PartIIa.polyConst C₁ d₁ p.ν (p.ν ^ (-(2 : ℝ))) *
    (p.R⁻¹) ^ (1 - 2 / (11 / 4 : ℝ))
  have hGf_norm_le : ∀ τ, (eLpNorm (-(Gf τ)) q0E volume).toReal ≤ B₀ := by
    intro τ
    rw [eLpNorm_neg, eLpNorm_congr_ae (hae τ), hq]
    refine (le_add_of_nonneg_of_le ENNReal.toReal_nonneg ?_).trans (hbd τ)
    exact Finset.single_le_sum (f := fun i => (eLpNorm (G τ i) (ENNReal.ofReal (11 / 4))
      volume).toReal) (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ j)
  refine ⟨Fr, ?_, ?_⟩
  · intro Φ hΦ
    have hΨ : IsSolTest p.period (dy j Φ) := gEW_isSolTest_dy hΦ j
    rw [hRel (dy j Φ) hΨ, H2 p hreg.train_buc hν2 hc hR (dy j Φ) hΨ, hFr_pair Φ hΦ.1]
    exact sliceIntegrationByParts_thm p.period p.period_pos j _ Gf
      hper' hGf_per hF_mem hGf_mem hF_cont hGf_cont hGf_weak Φ hΦ.1
  · refine (hFr_bd B₀ hGf_norm_le).trans ?_
    have hε : p.R⁻¹ = p.ε := by rw [Params.R, inv_inv]
    have hex : (1 : ℝ) - 2 / (11 / 4 : ℝ) = 3 / 11 := by norm_num
    have hE : 0 ≤ p.ε ^ (3 / 11 : ℝ) := Real.rpow_nonneg p.ε_pos.le _
    have hX : (1 + p.ν ^ (-(2 : ℝ)) + p.ν⁻¹) ^ d₁ ≤ 3 ^ d₁ * ((p.ν ^ (2 * d₁))⁻¹) := by
      calc (1 + p.ν ^ (-(2 : ℝ)) + p.ν⁻¹) ^ d₁ ≤ (3 * (p.ν ^ 2)⁻¹) ^ d₁ :=
            pow_le_pow_left₀ (by positivity) (one_add_inv_le hνpos hν3) d₁
        _ = 3 ^ d₁ * ((p.ν ^ (2 * d₁))⁻¹) := by rw [mul_pow, inv_pow, ← pow_mul]
    have hXn : 0 ≤ (1 + p.ν ^ (-(2 : ℝ)) + p.ν⁻¹) ^ d₁ := by
      apply pow_nonneg
      have : 0 < p.ν ^ (-(2 : ℝ)) := Real.rpow_pos_of_pos hνpos _
      have : 0 < p.ν⁻¹ := inv_pos.2 hνpos
      linarith
    dsimp [B₀, Short.PartIIa.polyConst, C_raw, k_raw]
    rw [hε, hex]
    calc C₁ * (1 + p.ν ^ (-(2 : ℝ)) + p.ν⁻¹) ^ d₁ * p.ε ^ (3 / 11 : ℝ)
        ≤ max C₁ 1 * (1 + p.ν ^ (-(2 : ℝ)) + p.ν⁻¹) ^ d₁ * p.ε ^ (3 / 11 : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hXn) hE
      _ ≤ max C₁ 1 * (3 ^ d₁ * ((p.ν ^ (2 * d₁))⁻¹)) * p.ε ^ (3 / 11 : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hX hC₁.le) hE
      _ = max C₁ 1 * 3 ^ d₁ * (p.ν ^ (2 * d₁))⁻¹ * p.ε ^ (3 / 11 : ℝ) := by ring

/-- Unconditional proof of `RingLiftSmoothExt` from `UnforcedLeray.Short.PartIIa.ringAxisSmooth`
(`PartII-a:R06`) and `ringLiftSmoothExt_of` (`PartII-b:R1/6`). -/
theorem ringLiftSmoothExt_proof : RingLiftSmoothExt :=
  ringLiftSmoothExt_of UnforcedLeray.Short.PartIIa.ringAxisSmooth

/-- Unconditional proof of `DiffEqRawBound` via `diffEq_raw_bound_of_lift` and
`ringLiftSmoothExt_proof`. -/
theorem diffEqRawBound_proof : DiffEqRawBound :=
  diffEq_raw_bound_of_lift ringLiftSmoothExt_proof

/-! ## 5. Unconditional exponential absorption (`2m < 3d₋/11`) -/

/-- When `0 < m`, `0 < dm`, and `2 * m < 3 * dm / 11`, in `BgRegime p d dm dp` one has
`Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) ≤ 1`. -/
theorem exp_eps_le_one_of_two_mul_lt {m dm dp d : ℝ} (hm : 0 < m)
    (h2m : 2 * m < 3 * dm / 11) {p : Params} (hreg : BgRegime p d dm dp) :
    Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) ≤ 1 := by
  have hν : 0 < p.ν := p.ν_pos
  have hdm_le : dm ≤ d := hreg.dm_le
  have hrpow : p.ε ^ (3 / 11 : ℝ) = Real.exp (-d / p.ν * (3 / 11)) := by
    rw [hreg.eps_eq, ← Real.exp_mul]
  rw [hrpow, ← Real.exp_add, Real.exp_le_one_iff]
  have hnum : m + -d * (3 / 11) ≤ 0 := by linarith
  have hdiv : m / p.ν + -d / p.ν * (3 / 11) = (m + -d * (3 / 11)) / p.ν := by ring
  rw [hdiv]
  exact div_nonpos_of_nonpos_of_nonneg hnum hν.le

end DiffEqSub

open DiffEqSub

/-! ## 6. Quantitative linear and quadratic differentiated source bounds and assembly -/

/-- **Quantitative differentiated linear raw-convection bound (`DiffEqLinBound`, `PartII-b:S1/1/1`)**
(`the November 2 reference manuscript`,
lines 2525-2531, 1217-1219): for fixed `(Σ, λ, q)` and `dm > 0`, the linear raw-convection term
`⟨(∇raw)ᵗ∂_jΦ - raw·∇∂_jΦ, w⟩` on solenoidal tests `Φ` is represented by `Fl ∈ Yq p.period q0E`
with `‖Fl‖ ≤ C_lin * (p.ν ^ k_lin)⁻¹ * ‖z‖`. -/
def DiffEqLinBound : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ (C_lin : ℝ) (k_lin : ℕ) (ν_lin : ℝ), 0 < C_lin ∧ 0 < ν_lin ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν_lin → p.ageCut = Sig → p.mode = q →
      ∀ (z : p.Z) (g₀ : Fin 3 → Yq p.period q0E) (h : Fin 3 → Fin 3 → Yq p.period q0E),
        GEData p z g₀ → (∀ j k : Fin 3, HasPhaseOp (fun Φ => -dy k Φ) (g₀ j) (h j k)) →
        ∀ j : Fin 3, ∃ Fl : Yq p.period q0E,
          (∀ Φ, IsSolTest p.period Φ →
            pairF p.period (convT p.raw (dy j Φ)) (fun x => rep (p.wOf z) x.1 x.2) =
              phasePair p.period q0E Φ Fl) ∧
          ‖Fl‖ ≤ C_lin * (p.ν ^ k_lin)⁻¹ * ‖z‖

/-- **Quantitative differentiated quadratic bound (`DiffEqQuadBound`, `PartII-b:S1/1/2`)**
(`the November 2 reference manuscript`,
lines 2525-2533, 2562-2564): for fixed `(Σ, λ, q)` and `dm > 0`, the differentiated quadratic term
`⟨∂_jΦ, gQ⟩` (`p.QuadRel z z gQ`) on solenoidal tests `Φ` is represented by
`Fq ∈ Yq p.period q0E` with `‖Fq‖ ≤ C_quad * (p.ν ^ k_quad)⁻¹ * ‖z‖ ^ 2`. -/
def DiffEqQuadBound : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ (C_quad : ℝ) (k_quad : ℕ) (ν_quad : ℝ), 0 < C_quad ∧ 0 < ν_quad ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν_quad → p.ageCut = Sig → p.mode = q →
      ∀ (z : p.Z) (g₀ : Fin 3 → Yq p.period q0E) (h : Fin 3 → Fin 3 → Yq p.period q0E)
        (gQ : Yq p.period q0E),
        GEData p z g₀ → (∀ j k : Fin 3, HasPhaseOp (fun Φ => -dy k Φ) (g₀ j) (h j k)) →
        p.QuadRel z z gQ → ∀ j : Fin 3,
          ∃ Fq : Yq p.period q0E,
            (∀ Φ, IsSolTest p.period Φ →
              phasePair p.period q0E (dy j Φ) gQ = phasePair p.period q0E Φ Fq) ∧
            ‖Fq‖ ≤ C_quad * (p.ν ^ k_quad)⁻¹ * ‖z‖ ^ 2

/-- **Conditional assembly of `DifferentiatedEquationGraphBound` (`PartII-b:S1/1`, SP 2525-2537)**
from `DiffEqRawBound`, `DiffEqLinBound`, `DiffEqQuadBound`, `h4 : AffineInletFacts`, and
`hQ1 : QuadBound`. -/
theorem differentiatedEquationGraphBound_of_parts
    (hRaw : DiffEqRawBound)
    (hLin : DiffEqLinBound)
    (hQuad : DiffEqQuadBound)
    (h4 : AffineInletFacts)
    (_hQ1 : QuadBound) :
    DifferentiatedEquationGraphBound := by
  obtain ⟨C_body, hC_body, Hbody⟩ := grad_graphNormD_of_weak_eq
  obtain ⟨C_GH, hC_GH, HGH⟩ := exists_grad_and_hess_bound
  intro Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν_w, hν_w, Hweak⟩ := gEWeak lam q hq dm dp hdm
  obtain ⟨C_raw, k_raw, ν_raw, hC_raw, hν_raw, Hraw⟩ := hRaw dm dp hdm
  obtain ⟨C_in, k_in, ν_in, hC_in, hν_in, Hin⟩ :=
    diffEq_inlet_bound_of_affineInletFacts h4 Sig lam q hSig hq dm dp hdm
  obtain ⟨C_lin, k_lin, ν_lin, hC_lin, hν_lin, Hlin⟩ :=
    hLin Sig lam q hSig hq dm dp hdm
  obtain ⟨C_quad, k_quad, ν_quad, hC_quad, hν_quad, Hquad⟩ :=
    hQuad Sig lam q hSig hq dm dp hdm
  obtain ⟨ν_per, hν_per, hper⟩ := poly_exp_small 2 dm 2 hdm
  set k₂ : ℕ :=
    max (max (max (k₁ + 1) k_raw) (max (k_in + k₁) (k_lin + k₁))) (k_quad + 2 * k₁)
  set C_src : ℝ := (1 / 2) * C_GH * C₁ + C_raw + C_quad * C₁ ^ 2 + C_lin * C₁ + C_in * C₁
  set C₂ : ℝ := C_body * C_src
  set ν₀ : ℝ :=
    min (min (min ν_w ν_raw) (min ν_in ν_lin)) (min (min ν_quad ν_per) 1)
  have hC_src : 0 < C_src := by positivity
  have hC₂ : 0 < C₂ := by positivity
  have hν₀ : 0 < ν₀ := lt_min
    (lt_min (lt_min hν_w hν_raw) (lt_min hν_in hν_lin))
    (lt_min (lt_min hν_quad hν_per) zero_lt_one)
  refine ⟨C₂, k₂, ν₀, hC₂, hν₀, ?_⟩
  intro p d hreg hν hSg hmode z hproj hz
  have hν_w' : p.ν ≤ ν_w :=
    hν.trans (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_left _ _))
  have hν_raw' : p.ν ≤ ν_raw :=
    hν.trans (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_right _ _))
  have hν_in' : p.ν ≤ ν_in :=
    hν.trans (((min_le_left _ _).trans (min_le_right _ _)).trans (min_le_left _ _))
  have hν_lin' : p.ν ≤ ν_lin :=
    hν.trans (((min_le_left _ _).trans (min_le_right _ _)).trans (min_le_right _ _))
  have hν_quad' : p.ν ≤ ν_quad :=
    hν.trans (((min_le_right _ _).trans (min_le_left _ _)).trans (min_le_left _ _))
  have hν_per' : p.ν ≤ ν_per :=
    hν.trans (((min_le_right _ _).trans (min_le_left _ _)).trans (min_le_right _ _))
  have hν_1 : p.ν ≤ 1 := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hP1 : p.period ≤ 1 := period_le_one_of hreg (hper p.ν p.ν_pos hν_per')
  obtain ⟨g₀, h, hg₀, hh, hg₀_bd, _hh_bd⟩ := HGH p hP1 hν_1 z
  have hd : GEData p z g₀ := ⟨hproj, hg₀⟩
  obtain ⟨gF, gL, gQ, hF, hL, hQ, hsum⟩ := hproj
  have W := Hweak p d hreg hν_w' hmode z g₀ hd gF gL gQ hF hL hQ hsum
  choose Fr hFr_pair hFr_bd using fun j : Fin 3 => Hraw p d hreg hν_raw' gF hF j
  choose Fi hFi_pair hFi_bd using fun j : Fin 3 => Hin p d hreg hν_in' hSg hmode z j
  choose Fl hFl_pair hFl_bd using fun j : Fin 3 => Hlin p d hreg hν_lin' hSg hmode z g₀ h hd hh j
  choose Fq hFq_pair hFq_bd using
    fun j : Fin 3 => Hquad p d hreg hν_quad' hSg hmode z g₀ h gQ hd hh hQ j
  let F_tot : Fin 3 → Yq p.period q0E := fun j =>
    (1 / 2 : ℂ) • g₀ j + Fr j + Fq j + Fl j + ∑ i : Fin 2, (p.coord z i : ℂ) • Fi j i
  have hF_tot : ∀ (j : Fin 3) Φ, IsSolTest p.period Φ →
      phasePair p.period q0E (L0T p.ν Φ) (g₀ j) = phasePair p.period q0E Φ (F_tot j) := by
    intro j Φ hΦ
    rw [W j Φ hΦ, hFr_pair j Φ hΦ, hFq_pair j Φ hΦ, hFl_pair j Φ hΦ]
    simp only [F_tot, map_add, map_smul, map_sum, smul_eq_mul]
    rw [Finset.sum_congr rfl (fun i _ => by rw [hFi_pair j i Φ hΦ])]
  obtain ⟨g, hg_eq, hg_gn⟩ := Hbody p hP1 z g₀ hd F_tot hF_tot
  refine ⟨g, fun j => by rw [hg_eq j]; exact hg₀ j, ?_⟩
  intro j
  set E : ℝ := Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ)
  have hνp : 0 < p.ν := p.ν_pos
  have hεp : 0 < p.ε := p.ε_pos
  have hE_pos : 0 < E := by positivity
  have hE_le1 : E ≤ 1 := exp_eps_le_one_of_two_mul_lt hm h2m hreg
  have hE_sq : E ^ 2 ≤ E := by nlinarith
  have hz' : ‖z‖ ≤ C₁ * (p.ν ^ k₁)⁻¹ * E := by
    calc ‖z‖ ≤ C₁ * (p.ν ^ k₁)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) := hz
      _ = C₁ * (p.ν ^ k₁)⁻¹ * E := by dsimp [E]; ring
  have hz_sq : ‖z‖ ^ 2 ≤ C₁ ^ 2 * (p.ν ^ (2 * k₁))⁻¹ * E := by
    have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
    have hsq1 : ‖z‖ ^ 2 ≤ (C₁ * (p.ν ^ k₁)⁻¹ * E) ^ 2 :=
      pow_le_pow_left₀ hz0 hz' 2
    have hpow2 : ((p.ν ^ k₁)⁻¹) ^ 2 = (p.ν ^ (2 * k₁))⁻¹ := by
      rw [inv_pow, ← pow_mul, mul_comm]
    have hring : (C₁ * (p.ν ^ k₁)⁻¹ * E) ^ 2 = C₁ ^ 2 * ((p.ν ^ k₁)⁻¹) ^ 2 * E ^ 2 := by ring
    calc ‖z‖ ^ 2
        ≤ C₁ ^ 2 * ((p.ν ^ k₁)⁻¹) ^ 2 * E ^ 2 := hsq1.trans_eq hring
      _ = C₁ ^ 2 * (p.ν ^ (2 * k₁))⁻¹ * E ^ 2 := by rw [hpow2]
      _ ≤ C₁ ^ 2 * (p.ν ^ (2 * k₁))⁻¹ * E := by gcongr
  have hk_g0 : (p.ν ^ 1)⁻¹ * (p.ν ^ k₁)⁻¹ ≤ (p.ν ^ k₂)⁻¹ := by
    rw [← mul_inv, ← pow_add, add_comm]
    exact S1Sub.s1_inv_pow_mono_of_le_one hνp hν_1
      (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _))
  have hk_raw : (p.ν ^ k_raw)⁻¹ ≤ (p.ν ^ k₂)⁻¹ :=
    S1Sub.s1_inv_pow_mono_of_le_one hνp hν_1
      (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _))
  have hk_in : (p.ν ^ k_in)⁻¹ * (p.ν ^ k₁)⁻¹ ≤ (p.ν ^ k₂)⁻¹ := by
    rw [← mul_inv, ← pow_add]
    exact S1Sub.s1_inv_pow_mono_of_le_one hνp hν_1
      (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _))
  have hk_lin : (p.ν ^ k_lin)⁻¹ * (p.ν ^ k₁)⁻¹ ≤ (p.ν ^ k₂)⁻¹ := by
    rw [← mul_inv, ← pow_add]
    exact S1Sub.s1_inv_pow_mono_of_le_one hνp hν_1
      (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _))
  have hk_quad : (p.ν ^ k_quad)⁻¹ * (p.ν ^ (2 * k₁))⁻¹ ≤ (p.ν ^ k₂)⁻¹ := by
    rw [← mul_inv, ← pow_add]
    exact S1Sub.s1_inv_pow_mono_of_le_one hνp hν_1 (le_max_right _ _)
  have hb_g0 : ‖(1 / 2 : ℂ) • g₀ j‖ ≤ (1 / 2) * C_GH * C₁ * (p.ν ^ k₂)⁻¹ * E := by
    have hsm : ‖(1 / 2 : ℂ) • g₀ j‖ = (1 / 2 : ℝ) * ‖g₀ j‖ := by
      rw [norm_smul]
      norm_num
    rw [hsm]
    calc (1 / 2 : ℝ) * ‖g₀ j‖
        ≤ (1 / 2 : ℝ) * (C_GH * (p.ν ^ 1)⁻¹ * ‖z‖) :=
          mul_le_mul_of_nonneg_left (hg₀_bd j) (by positivity)
      _ ≤ (1 / 2 : ℝ) * (C_GH * (p.ν ^ 1)⁻¹ * (C₁ * (p.ν ^ k₁)⁻¹ * E)) := by gcongr
      _ = ((1 / 2) * C_GH * C₁) * ((p.ν ^ 1)⁻¹ * (p.ν ^ k₁)⁻¹) * E := by ring
      _ ≤ ((1 / 2) * C_GH * C₁) * (p.ν ^ k₂)⁻¹ * E := by gcongr
      _ = (1 / 2) * C_GH * C₁ * (p.ν ^ k₂)⁻¹ * E := by ring
  have hb_raw : ‖Fr j‖ ≤ C_raw * (p.ν ^ k₂)⁻¹ * E := by
    have h1 : 1 ≤ Real.exp (m / p.ν) := Real.one_le_exp (div_pos hm hνp).le
    have h2 : p.ε ^ (3 / 11 : ℝ) ≤ E := by
      dsimp [E]
      calc p.ε ^ (3 / 11 : ℝ) = 1 * p.ε ^ (3 / 11 : ℝ) := (one_mul _).symm
        _ ≤ Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
    calc ‖Fr j‖
        ≤ C_raw * (p.ν ^ k_raw)⁻¹ * p.ε ^ (3 / 11 : ℝ) := hFr_bd j
      _ ≤ C_raw * (p.ν ^ k₂)⁻¹ * E := by gcongr
  have hb_quad : ‖Fq j‖ ≤ C_quad * C₁ ^ 2 * (p.ν ^ k₂)⁻¹ * E := by
    calc ‖Fq j‖
        ≤ C_quad * (p.ν ^ k_quad)⁻¹ * ‖z‖ ^ 2 := hFq_bd j
      _ ≤ C_quad * (p.ν ^ k_quad)⁻¹ * (C₁ ^ 2 * (p.ν ^ (2 * k₁))⁻¹ * E) := by gcongr
      _ = (C_quad * C₁ ^ 2) * ((p.ν ^ k_quad)⁻¹ * (p.ν ^ (2 * k₁))⁻¹) * E := by ring
      _ ≤ (C_quad * C₁ ^ 2) * (p.ν ^ k₂)⁻¹ * E := by gcongr
      _ = C_quad * C₁ ^ 2 * (p.ν ^ k₂)⁻¹ * E := by ring
  have hb_lin : ‖Fl j‖ ≤ C_lin * C₁ * (p.ν ^ k₂)⁻¹ * E := by
    calc ‖Fl j‖
        ≤ C_lin * (p.ν ^ k_lin)⁻¹ * ‖z‖ := hFl_bd j
      _ ≤ C_lin * (p.ν ^ k_lin)⁻¹ * (C₁ * (p.ν ^ k₁)⁻¹ * E) := by gcongr
      _ = (C_lin * C₁) * ((p.ν ^ k_lin)⁻¹ * (p.ν ^ k₁)⁻¹) * E := by ring
      _ ≤ (C_lin * C₁) * (p.ν ^ k₂)⁻¹ * E := by gcongr
      _ = C_lin * C₁ * (p.ν ^ k₂)⁻¹ * E := by ring
  have hb_in : ‖∑ i : Fin 2, (p.coord z i : ℂ) • Fi j i‖ ≤ C_in * C₁ * (p.ν ^ k₂)⁻¹ * E := by
    calc ‖∑ i : Fin 2, (p.coord z i : ℂ) • Fi j i‖
        ≤ C_in * (p.ν ^ k_in)⁻¹ * ‖z‖ := hFi_bd j
      _ ≤ C_in * (p.ν ^ k_in)⁻¹ * (C₁ * (p.ν ^ k₁)⁻¹ * E) := by gcongr
      _ = (C_in * C₁) * ((p.ν ^ k_in)⁻¹ * (p.ν ^ k₁)⁻¹) * E := by ring
      _ ≤ (C_in * C₁) * (p.ν ^ k₂)⁻¹ * E := by gcongr
      _ = C_in * C₁ * (p.ν ^ k₂)⁻¹ * E := by ring
  have hF_tot_norm : ‖F_tot j‖ ≤ C_src * (p.ν ^ k₂)⁻¹ * E := by
    have htri : ‖F_tot j‖ ≤
        ‖(1 / 2 : ℂ) • g₀ j‖ + ‖Fr j‖ + ‖Fq j‖ + ‖Fl j‖ +
          ‖∑ i : Fin 2, (p.coord z i : ℂ) • Fi j i‖ := by
      dsimp [F_tot]
      calc ‖(1 / 2 : ℂ) • g₀ j + Fr j + Fq j + Fl j +
              ∑ i : Fin 2, (p.coord z i : ℂ) • Fi j i‖
          ≤ ‖(1 / 2 : ℂ) • g₀ j + Fr j + Fq j + Fl j‖ +
              ‖∑ i : Fin 2, (p.coord z i : ℂ) • Fi j i‖ := norm_add_le _ _
        _ ≤ (‖(1 / 2 : ℂ) • g₀ j + Fr j + Fq j‖ + ‖Fl j‖) +
              ‖∑ i : Fin 2, (p.coord z i : ℂ) • Fi j i‖ :=
            add_le_add_left (norm_add_le _ _) _
        _ ≤ ((‖(1 / 2 : ℂ) • g₀ j + Fr j‖ + ‖Fq j‖) + ‖Fl j‖) +
              ‖∑ i : Fin 2, (p.coord z i : ℂ) • Fi j i‖ :=
            add_le_add_left (add_le_add_left (norm_add_le _ _) _) _
        _ ≤ (((‖(1 / 2 : ℂ) • g₀ j‖ + ‖Fr j‖) + ‖Fq j‖) + ‖Fl j‖) +
              ‖∑ i : Fin 2, (p.coord z i : ℂ) • Fi j i‖ :=
            add_le_add_left (add_le_add_left (add_le_add_left (norm_add_le _ _) _) _) _
        _ = ‖(1 / 2 : ℂ) • g₀ j‖ + ‖Fr j‖ + ‖Fq j‖ + ‖Fl j‖ +
              ‖∑ i : Fin 2, (p.coord z i : ℂ) • Fi j i‖ := by ring
    dsimp [C_src]
    linarith [htri, hb_g0, hb_raw, hb_quad, hb_lin, hb_in]
  calc B0411.graphNormD (g j)
      ≤ C_body * ‖F_tot j‖ := hg_gn j
    _ ≤ C_body * (C_src * (p.ν ^ k₂)⁻¹ * E) :=
        mul_le_mul_of_nonneg_left hF_tot_norm hC_body.le
    _ = C₂ * (p.ν ^ k₂)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) := by
        dsimp [C₂, E]
        ring

/-- **Conditional assembly of `DifferentiatedEquationGraphBound` (`PartII-b:S1/1`, SP 2525-2537)**
directly from `hLift : RingLiftSmoothExt` (`PartII-b:R1/6`), `DiffEqLinBound`, `DiffEqQuadBound`,
`h4 : AffineInletFacts`, and `hQ1 : QuadBound`. -/
theorem differentiatedEquationGraphBound_of_lift
    (hLift : RingLiftSmoothExt)
    (hLin : DiffEqLinBound)
    (hQuad : DiffEqQuadBound)
    (h4 : AffineInletFacts)
    (hQ1 : QuadBound) :
    DifferentiatedEquationGraphBound :=
  differentiatedEquationGraphBound_of_parts (diffEq_raw_bound_of_lift hLift) hLin hQuad h4 hQ1

/-- **Direct assembly of `DifferentiatedEquationGraphBound` (`PartII-b:S1/1`, SP 2525-2537)**
from the two remaining quantitative leaves `DiffEqLinBound` (`PartII-b:S1/1/1`) and
`DiffEqQuadBound` (`PartII-b:S1/1/2`), using `diffEqRawBound_proof` (`PartII-a:R06` + `PartII-b:R1/6`). -/
theorem differentiatedEquationGraphBound_of_leaves
    (hLin : DiffEqLinBound)
    (hQuad : DiffEqQuadBound)
    (h4 : AffineInletFacts)
    (hQ1 : QuadBound) :
    DifferentiatedEquationGraphBound :=
  differentiatedEquationGraphBound_of_parts diffEqRawBound_proof hLin hQuad h4 hQ1

end UnforcedLeray.Short.IIb

end
