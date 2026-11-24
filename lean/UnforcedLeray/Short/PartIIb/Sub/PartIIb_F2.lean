import UnforcedLeray.Short.PartIIb.Sub.FlatInverseDesign
import UnforcedLeray.Short.PartIIb.Tasks.FreeCylinderBound
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# `PartII-b:F2` (`Sub/PartII-b_F2.lean`): Block factorization and dichotomy decomposition

Source of record: `the November 2 reference manuscript` (SP), lines 2085–2171.

This module provides:
1. `bgRegime_c_ge_one` and `bgRegime_c_ge`: in `BgRegime` (`p.c = (p.ν ^ 2)⁻¹`), small `p.ν` gives
   arbitrarily large cylinder period `p.c ≥ c₀`;
2. `exists_block_grid`: uniform block-grid construction on `[0, H]` (`1 ≤ N`, `L₀ ≤ L ≤ 2 * L₀`,
   `N * L = H`) whenever `0 < L₀` and `2 * L₀ ≤ H`;
3. `norm_eq_norm_Jc_comp_Rc`: operator-norm isometry `‖J_c A R_c‖_{X_m → X_m} = ‖A‖_{X_{m,c} → X_{m,c}}`;
4. `HilbertSplitting` (Householder reflections and 2-vector Gram–Schmidt on any real Hilbert space):
   automatic construction of the reference closed complementary subspace `F = ker (π 0)` and
   isometric complementary embeddings/projections `κ_n : F →L[ℝ] H`, `ρ_n : H →L[ℝ] F` from any
   2D growing coordinate family `(ι_n, π_n)` with `π_n ∘ ι_n = id`, reducing all four block bounds of
   `BlockFactorizationData.Valid` to operator norms involving only `ι_n`, `π_n`, and `1 - ι_n ∘ π_n`;
5. `invertible_two_by_two_of_close`: Neumann-series perturbation of the 2×2 growing block `a_n`
   around the planar Euler growing block `a_pl`;
6. The frozen radial transport flow (`PartIIbF23Sub.frozenOmega`, `PartIIbF23Sub.frozenRadialFlow`),
   the frozen radial transport group `IsFrozenRadialTransport` (SP 841–852, 2104–2115), and the
   frozen planar Euler package `IsFrozenEulerPackage` (spectral commutation `euler_comm`, mild
   Duhamel form `euler_duhamel`);
7. The four leaf propositions of `PartII-b:F2`:
   * `TrainCloseRegime` (`PartII-b:F2/1`, SP 2085–2090),
   * `CoupledPropagatorStep` (`PartII-b:F2/2`, SP 2076–2083, 2141–2155),
   * `FrozenEulerSplittingStep` (`PartII-b:F2/3`, SP 931–953, 2145–2171),
   * `CompactDuhamelBlockStep` (`PartII-b:F2/4`, SP 2104–2115, 2145–2166),
   and the unconditional assembly theorem `blockDichotomy_of_leaves`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-! ## 1. Regime period bounds, block-grid construction, and `J_c A R_c` norm identity -/

/-- In `BgRegime p d dm dp` (`p.c = (p.ν ^ 2)⁻¹`), `p.ν ≤ 1` implies `1 ≤ p.c`. -/
theorem bgRegime_c_ge_one {p : Params} {d dm dp : ℝ}
    (hbg : BgRegime p d dm dp) (hν1 : p.ν ≤ 1) : 1 ≤ p.c := by
  have hν0 : 0 < p.ν := p.ν_pos
  have hν2_pos : 0 < p.ν ^ 2 := sq_pos_of_pos hν0
  have hν2_le : p.ν ^ 2 ≤ 1 := by nlinarith
  rw [hbg.c_eq, le_inv_comm₀ (by positivity) hν2_pos]
  linarith

/-- In `BgRegime p d dm dp` (`p.c = (p.ν ^ 2)⁻¹`), for any `c₀ > 0`, `p.ν ≤ (Real.sqrt c₀)⁻¹`
implies `c₀ ≤ p.c`. -/
theorem bgRegime_c_ge {p : Params} {d dm dp c₀ : ℝ}
    (hbg : BgRegime p d dm dp) (hc₀ : 0 < c₀) (hν : p.ν ≤ (Real.sqrt c₀)⁻¹) : c₀ ≤ p.c := by
  have hν0 : 0 < p.ν := p.ν_pos
  have hν2_pos : 0 < p.ν ^ 2 := sq_pos_of_pos hν0
  have hsq : p.ν ^ 2 ≤ c₀⁻¹ := by
    calc p.ν ^ 2 ≤ ((Real.sqrt c₀)⁻¹) ^ 2 := pow_le_pow_left₀ hν0.le hν 2
      _ = (Real.sqrt c₀ ^ 2)⁻¹ := inv_pow _ 2
      _ = c₀⁻¹ := by rw [Real.sq_sqrt hc₀.le]
  rw [hbg.c_eq, le_inv_comm₀ hc₀ hν2_pos]
  exact hsq

/-- Uniform block-grid construction on `[0, H]`: for `L₀ > 0` and `2 * L₀ ≤ H`, setting
`N = ⌊H / (2 * L₀)⌋₊ + 1` and `L = H / N` gives `1 ≤ N`, `L₀ ≤ L ≤ 2 * L₀`, and `N * L = H`. -/
theorem exists_block_grid {L₀ H : ℝ} (hL₀ : 0 < L₀) (hH : 2 * L₀ ≤ H) :
    ∃ (N : ℕ) (L : ℝ), 1 ≤ N ∧ (L₀ ≤ L ∧ L ≤ 2 * L₀) ∧ (N : ℝ) * L = H := by
  set k : ℕ := ⌊H / (2 * L₀)⌋₊
  have h2L₀ : 0 < 2 * L₀ := by linarith
  have hdiv_ge_one : 1 ≤ H / (2 * L₀) := (one_le_div h2L₀).2 hH
  have hk_ge_one : 1 ≤ k := Nat.one_le_iff_ne_zero.2 (Nat.floor_pos.2 hdiv_ge_one).ne'
  set N : ℕ := k + 1
  have hN_ge_one : 1 ≤ N := Nat.le_add_left 1 k
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  set L : ℝ := H / (N : ℝ)
  have hNL : (N : ℝ) * L = H := mul_div_cancel₀ H hN_pos.ne'
  have hk_le : (k : ℝ) ≤ H / (2 * L₀) := Nat.floor_le (by positivity)
  have hlt_N : H / (2 * L₀) < (N : ℝ) := by
    dsimp [N]
    push_cast
    exact Nat.lt_floor_add_one (H / (2 * L₀))
  have hH_lt : H ≤ 2 * L₀ * (N : ℝ) := by
    have h1 := (div_lt_iff₀ h2L₀).1 hlt_N
    linarith
  have hL_upper : L ≤ 2 * L₀ := (div_le_iff₀ hN_pos).2 hH_lt
  have h2k_ge_N : (N : ℝ) ≤ 2 * (k : ℝ) := by
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_ge_one
    dsimp [N]
    push_cast
    linarith
  have hH_ge : (k : ℝ) * (2 * L₀) ≤ H := (le_div_iff₀ h2L₀).1 hk_le
  have hL_lower : L₀ ≤ L := by
    rw [le_div_iff₀ hN_pos]
    calc L₀ * (N : ℝ) ≤ L₀ * (2 * (k : ℝ)) :=
          mul_le_mul_of_nonneg_left h2k_ge_N hL₀.le
      _ = (k : ℝ) * (2 * L₀) := by ring
      _ ≤ H := hH_ge
  exact ⟨N, L, hN_ge_one, ⟨hL_lower, hL_upper⟩, hNL⟩

/-- Operator-norm identity `‖J_c A R_c‖_{X_m → X_m} = ‖A‖_{X_{m,c} → X_{m,c}}`. -/
theorem norm_eq_norm_Jc_comp_Rc (c m : ℝ) (A : Xmc c m →L[ℝ] Xmc c m) :
    ‖(Jc c m).comp (A.comp (Rc c m))‖ = ‖A‖ := by
  refine le_antisymm (norm_Jc_comp_Rc_le c m A) ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun f => ?_
  have h1 : A f = A (Rc c m (Jc c m f)) := by rw [Rc_Jc]
  have h2 : ‖A f‖ = ‖(Jc c m).comp (A.comp (Rc c m)) (Jc c m f)‖ := by
    simp only [ContinuousLinearMap.comp_apply, norm_Jc_apply, ← h1]
  rw [h2]
  calc ‖(Jc c m).comp (A.comp (Rc c m)) (Jc c m f)‖
      ≤ ‖(Jc c m).comp (A.comp (Rc c m))‖ * ‖Jc c m f‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = ‖(Jc c m).comp (A.comp (Rc c m))‖ * ‖f‖ := by rw [norm_Jc_apply]

/-! ## 2. Hilbert-space Householder reflections and complementary subspace reduction -/

namespace PartIIbF2Splittings

set_option linter.unusedSectionVars false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Householder reflection along a vector `w : H` (identity when `w = 0`). -/
private def householderFun (w x : H) : H :=
  x - (2 * inner ℝ w x / ‖w‖ ^ 2) • w

private theorem householderFun_add (w x y : H) :
    householderFun w (x + y) = householderFun w x + householderFun w y := by
  unfold householderFun
  rw [inner_add_right, mul_add, add_div, add_smul]
  abel

private theorem householderFun_smul (w : H) (a : ℝ) (x : H) :
    householderFun w (a • x) = a • householderFun w x := by
  unfold householderFun
  rw [real_inner_smul_right, smul_sub, ← mul_assoc, mul_comm 2 a, mul_assoc, mul_div_assoc,
    mul_smul]

private theorem norm_householderFun (w x : H) :
    ‖householderFun w x‖ = ‖x‖ := by
  unfold householderFun
  by_cases hw : w = 0
  · simp [hw]
  · have hw_pos : 0 < ‖w‖ := norm_pos_iff.2 hw
    have hw2_ne : ‖w‖ ^ 2 ≠ 0 := pow_ne_zero 2 hw_pos.ne'
    set c : ℝ := 2 * inner ℝ w x / ‖w‖ ^ 2
    have hsq : ‖x - c • w‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
        mul_pow, sq_abs, real_inner_comm w x]
      dsimp [c]
      field_simp [hw2_ne]
      ring
    have h1 := congrArg Real.sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h1

private theorem householderFun_self (w x : H) :
    householderFun w (householderFun w x) = x := by
  by_cases hw : w = 0
  · simp [householderFun, hw]
  · have hw_pos : 0 < ‖w‖ := norm_pos_iff.2 hw
    have hw2_ne : ‖w‖ ^ 2 ≠ 0 := pow_ne_zero 2 hw_pos.ne'
    have hin : inner ℝ w (householderFun w x) = -inner ℝ w x := by
      unfold householderFun
      rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp [hw2_ne]
      ring
    nth_rw 1 [householderFun]
    rw [hin]
    unfold householderFun
    have hcoef : 2 * -inner ℝ w x / ‖w‖ ^ 2 = -(2 * inner ℝ w x / ‖w‖ ^ 2) := by ring
    rw [hcoef, neg_smul, sub_neg_eq_add, sub_add_cancel]

/-- Householder reflection as a surjective linear isometry `H ≃ₗᵢ[ℝ] H`. -/
private def householderIso (w : H) : H ≃ₗᵢ[ℝ] H where
  toFun := householderFun w
  invFun := householderFun w
  map_add' := householderFun_add w
  map_smul' := householderFun_smul w
  left_inv := householderFun_self w
  right_inv := householderFun_self w
  norm_map' := norm_householderFun w

private theorem householderIso_apply (w x : H) :
    householderIso w x = x - (2 * inner ℝ w x / ‖w‖ ^ 2) • w := rfl

private theorem householderIso_sub_apply_self {u v : H} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    householderIso (u - v) u = v := by
  rw [householderIso_apply]
  by_cases huv : u - v = 0
  · have heq : u = v := sub_eq_zero.1 huv
    simp [heq]
  · have hw_pos : 0 < ‖u - v‖ := norm_pos_iff.2 huv
    have hw2_ne : ‖u - v‖ ^ 2 ≠ 0 := pow_ne_zero 2 hw_pos.ne'
    have hw2 : ‖u - v‖ ^ 2 = 2 * (1 - inner ℝ u v) := by
      rw [norm_sub_sq_real, hu, hv]
      ring
    have hin : 2 * inner ℝ (u - v) u = ‖u - v‖ ^ 2 := by
      rw [inner_sub_left, real_inner_self_eq_norm_sq, hu, real_inner_comm u v, hw2]
      ring
    rw [hin, div_self hw2_ne, one_smul, sub_sub_cancel]

private theorem householderIso_sub_apply_of_orth {u v z : H}
    (hu : inner ℝ u z = 0) (hv : inner ℝ v z = 0) :
    householderIso (u - v) z = z := by
  rw [householderIso_apply, inner_sub_left, hu, hv, sub_zero, mul_zero, zero_div, zero_smul,
    sub_zero]

/-- Given two orthonormal pairs `(u₀, u₁)` and `(v₀, v₁)` in `H`, composition of two Householder
reflections gives a linear isometry equivalence `H ≃ₗᵢ[ℝ] H` sending `u₀ ↦ v₀` and `u₁ ↦ v₁`. -/
private def twoVecIso (u₀ u₁ v₀ v₁ : H) : H ≃ₗᵢ[ℝ] H :=
  (householderIso (u₀ - v₀)).trans (householderIso (householderIso (u₀ - v₀) u₁ - v₁))

private theorem twoVecIso_apply_fst {u₀ u₁ v₀ v₁ : H}
    (hu₀ : ‖u₀‖ = 1) (hv₀ : ‖v₀‖ = 1)
    (hu_orth : inner ℝ u₀ u₁ = 0) (hv_orth : inner ℝ v₀ v₁ = 0) :
    twoVecIso u₀ u₁ v₀ v₁ u₀ = v₀ := by
  unfold twoVecIso
  simp only [LinearIsometryEquiv.trans_apply]
  rw [householderIso_sub_apply_self hu₀ hv₀]
  refine householderIso_sub_apply_of_orth ?_ ?_
  · calc inner ℝ (householderIso (u₀ - v₀) u₁) v₀
        = inner ℝ (householderIso (u₀ - v₀) u₁) (householderIso (u₀ - v₀) u₀) := by
          rw [householderIso_sub_apply_self hu₀ hv₀]
      _ = inner ℝ u₁ u₀ := LinearIsometryEquiv.inner_map_map _ _ _
      _ = inner ℝ u₀ u₁ := real_inner_comm u₀ u₁
      _ = 0 := hu_orth
  · rw [real_inner_comm v₀ v₁, hv_orth]

private theorem twoVecIso_apply_snd {u₀ u₁ v₀ v₁ : H}
    (hu₁ : ‖u₁‖ = 1) (hv₁ : ‖v₁‖ = 1) :
    twoVecIso u₀ u₁ v₀ v₁ u₁ = v₁ := by
  unfold twoVecIso
  simp only [LinearIsometryEquiv.trans_apply]
  have hu₁' : ‖householderIso (u₀ - v₀) u₁‖ = 1 := by
    rw [LinearIsometryEquiv.norm_map, hu₁]
  exact householderIso_sub_apply_self hu₁' hv₁

/-- Standard basis vectors of `E2 = EuclideanSpace ℝ (Fin 2)`. -/
private def e2Basis (i : Fin 2) : E2 := EuclideanSpace.single i 1

/-- Coordinate projection `E2 →L[ℝ] ℝ`. -/
private def e2Proj (i : Fin 2) : E2 →L[ℝ] ℝ := EuclideanSpace.proj i

/-- Riesz representative of the `i`-th coordinate functional of `π : H →L[ℝ] E2`. -/
private def rieszRep (π : H →L[ℝ] E2) (i : Fin 2) : H :=
  (InnerProductSpace.toDual ℝ H).symm ((e2Proj i).comp π)

private theorem inner_rieszRep (π : H →L[ℝ] E2) (i : Fin 2) (x : H) :
    inner ℝ (rieszRep π i) x = π x i := by
  unfold rieszRep
  rw [InnerProductSpace.toDual_symm_apply]
  rfl

/-- First Gram–Schmidt vector of `(rieszRep π 0, rieszRep π 1)`. -/
private def gsVec0 (π : H →L[ℝ] E2) : H :=
  ‖rieszRep π 0‖⁻¹ • rieszRep π 0

/-- Orthogonalized second Riesz vector of `π`. -/
private def gsRaw1 (π : H →L[ℝ] E2) : H :=
  rieszRep π 1 - inner ℝ (gsVec0 π) (rieszRep π 1) • gsVec0 π

/-- Second Gram–Schmidt vector of `(rieszRep π 0, rieszRep π 1)`. -/
private def gsVec1 (π : H →L[ℝ] E2) : H :=
  ‖gsRaw1 π‖⁻¹ • gsRaw1 π

private theorem gs_orthonormal {ι : E2 →L[ℝ] H} {π : H →L[ℝ] E2}
    (hπι : π.comp ι = ContinuousLinearMap.id ℝ E2) :
    ‖gsVec0 π‖ = 1 ∧ ‖gsVec1 π‖ = 1 ∧ inner ℝ (gsVec0 π) (gsVec1 π) = 0 ∧
      ∀ x : H, π x = 0 ↔ (inner ℝ (gsVec0 π) x = 0 ∧ inner ℝ (gsVec1 π) x = 0) := by
  have h_app : ∀ α : E2, π (ι α) = α := fun α => DFunLike.congr_fun hπι α
  have hg0_e0 : inner ℝ (rieszRep π 0) (ι (e2Basis 0)) = 1 := by
    rw [inner_rieszRep, h_app]
    simp [e2Basis]
  have hg0_e1 : inner ℝ (rieszRep π 0) (ι (e2Basis 1)) = 0 := by
    rw [inner_rieszRep, h_app]
    simp [e2Basis]
  have hg1_e1 : inner ℝ (rieszRep π 1) (ι (e2Basis 1)) = 1 := by
    rw [inner_rieszRep, h_app]
    simp [e2Basis]
  have hg0_ne : rieszRep π 0 ≠ 0 := by
    intro h0
    rw [h0, inner_zero_left] at hg0_e0
    exact zero_ne_one hg0_e0
  have hg0_pos : 0 < ‖rieszRep π 0‖ := norm_pos_iff.2 hg0_ne
  have hu0_norm : ‖gsVec0 π‖ = 1 := by
    unfold gsVec0
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hg0_pos.le), inv_mul_cancel₀ hg0_pos.ne']
  have hu0_e1 : inner ℝ (gsVec0 π) (ι (e2Basis 1)) = 0 := by
    unfold gsVec0
    rw [real_inner_smul_left, hg0_e1, mul_zero]
  have hraw1_e1 : inner ℝ (gsRaw1 π) (ι (e2Basis 1)) = 1 := by
    unfold gsRaw1
    rw [inner_sub_left, real_inner_smul_left, hg1_e1, hu0_e1, mul_zero, sub_zero]
  have hraw1_ne : gsRaw1 π ≠ 0 := by
    intro h0
    rw [h0, inner_zero_left] at hraw1_e1
    exact zero_ne_one hraw1_e1
  have hraw1_pos : 0 < ‖gsRaw1 π‖ := norm_pos_iff.2 hraw1_ne
  have hu1_norm : ‖gsVec1 π‖ = 1 := by
    unfold gsVec1
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hraw1_pos.le), inv_mul_cancel₀ hraw1_pos.ne']
  have hu_orth : inner ℝ (gsVec0 π) (gsVec1 π) = 0 := by
    unfold gsVec1 gsRaw1
    rw [real_inner_smul_right, inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hu0_norm, one_pow, mul_one, sub_self, mul_zero]
  refine ⟨hu0_norm, hu1_norm, hu_orth, fun x => ?_⟩
  have h_pi0 : π x = 0 ↔ (π x 0 = 0 ∧ π x 1 = 0) := by
    constructor
    · intro hx
      rw [hx]
      exact ⟨rfl, rfl⟩
    · rintro ⟨h0, h1⟩
      ext i
      fin_cases i
      · exact h0
      · exact h1
  rw [h_pi0, ← inner_rieszRep π 0 x, ← inner_rieszRep π 1 x]
  constructor
  · rintro ⟨hx0, hx1⟩
    have hu0x : inner ℝ (gsVec0 π) x = 0 := by
      unfold gsVec0
      rw [real_inner_smul_left, hx0, mul_zero]
    have hu1x : inner ℝ (gsVec1 π) x = 0 := by
      unfold gsVec1 gsRaw1
      rw [real_inner_smul_left, inner_sub_left, real_inner_smul_left, hx1, hu0x, mul_zero,
        sub_zero, mul_zero]
    exact ⟨hu0x, hu1x⟩
  · rintro ⟨hu0x, hu1x⟩
    have hx0 : inner ℝ (rieszRep π 0) x = 0 := by
      unfold gsVec0 at hu0x
      rw [real_inner_smul_left] at hu0x
      exact (mul_eq_zero.1 hu0x).resolve_left (inv_ne_zero hg0_pos.ne')
    have hraw1x : inner ℝ (gsRaw1 π) x = 0 := by
      unfold gsVec1 at hu1x
      rw [real_inner_smul_left] at hu1x
      exact (mul_eq_zero.1 hu1x).resolve_left (inv_ne_zero hraw1_pos.ne')
    have hx1 : inner ℝ (rieszRep π 1) x = 0 := by
      unfold gsRaw1 at hraw1x
      rw [inner_sub_left, real_inner_smul_left, hu0x, mul_zero, sub_zero] at hraw1x
      exact hraw1x
    exact ⟨hx0, hx1⟩

/-- The closed kernel submodule `ker π ⊂ H`. -/
def kerSubmodule (π : H →L[ℝ] E2) : Submodule ℝ H :=
  LinearMap.ker (π : H →ₗ[ℝ] E2)

instance completeSpace_kerSubmodule (π : H →L[ℝ] E2) : CompleteSpace (kerSubmodule π) :=
  (ContinuousLinearMap.isClosed_ker π).completeSpace_coe

/-- Complementary projection `x ↦ x - ι (π x)` into `kerSubmodule π` when `π ∘ ι = id`. -/
def compToKer (ι : E2 →L[ℝ] H) (π : H →L[ℝ] E2)
    (hπι : π.comp ι = ContinuousLinearMap.id ℝ E2) : H →L[ℝ] kerSubmodule π :=
  (ContinuousLinearMap.id ℝ H - ι.comp π).codRestrict (kerSubmodule π) fun x => by
    change π (x - ι (π x)) = 0
    have h := DFunLike.congr_fun hπι (π x)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h
    rw [map_sub, h, sub_self]

theorem coe_compToKer_apply (ι : E2 →L[ℝ] H) (π : H →L[ℝ] E2)
    (hπι : π.comp ι = ContinuousLinearMap.id ℝ E2) (x : H) :
    (compToKer ι π hπι x : H) = (ContinuousLinearMap.id ℝ H - ι.comp π) x := rfl

theorem norm_compToKer_apply (ι : E2 →L[ℝ] H) (π : H →L[ℝ] E2)
    (hπι : π.comp ι = ContinuousLinearMap.id ℝ E2) (x : H) :
    ‖compToKer ι π hπι x‖ = ‖(ContinuousLinearMap.id ℝ H - ι.comp π) x‖ := rfl

/-- Linear isometry equivalence `kerSubmodule π₀ ≃ₗᵢ[ℝ] kerSubmodule π₁` when `π₀ ∘ ι₀ = id`
and `π₁ ∘ ι₁ = id`. -/
def kerLinearIsometryEquiv {ι₀ ι₁ : E2 →L[ℝ] H} {π₀ π₁ : H →L[ℝ] E2}
    (h₀ : π₀.comp ι₀ = ContinuousLinearMap.id ℝ E2)
    (h₁ : π₁.comp ι₁ = ContinuousLinearMap.id ℝ E2) :
    kerSubmodule π₀ ≃ₗᵢ[ℝ] kerSubmodule π₁ := by
  let U : H ≃ₗᵢ[ℝ] H := twoVecIso (gsVec0 π₀) (gsVec1 π₀) (gsVec0 π₁) (gsVec1 π₁)
  obtain ⟨hu0, hu1, hu_orth, hker0⟩ := gs_orthonormal h₀
  obtain ⟨hv0, hv1, hv_orth, hker1⟩ := gs_orthonormal h₁
  have hU0 : U (gsVec0 π₀) = gsVec0 π₁ := twoVecIso_apply_fst hu0 hv0 hu_orth hv_orth
  have hU1 : U (gsVec1 π₀) = gsVec1 π₁ := twoVecIso_apply_snd hu1 hv1
  have hmem : ∀ x : H, x ∈ kerSubmodule π₀ ↔ U x ∈ kerSubmodule π₁ := by
    intro x
    change π₀ x = 0 ↔ π₁ (U x) = 0
    rw [hker0 x, hker1 (U x), ← hU0, ← hU1, LinearIsometryEquiv.inner_map_map,
      LinearIsometryEquiv.inner_map_map]
  exact
    { toFun := fun x => ⟨U (x : H), (hmem (x : H)).1 x.2⟩
      invFun := fun y => ⟨U.symm (y : H), (hmem (U.symm (y : H))).2 (by simp)⟩
      map_add' := fun x y => by ext; exact map_add U (x : H) (y : H)
      map_smul' := fun a x => by ext; exact map_smul U a (x : H)
      left_inv := fun x => by ext; exact U.symm_apply_apply (x : H)
      right_inv := fun y => by ext; exact U.apply_symm_apply (y : H)
      norm_map' := fun x => U.norm_map (x : H) }

/-- Given a family of 2D growing embeddings `ι : ℕ → (E2 →L[ℝ] H)` and projections
`π : ℕ → (H →L[ℝ] E2)` with `(π n).comp (ι n) = id` for `n ≤ N`, construct the complementary
embedding `κ n : kerSubmodule (π 0) →L[ℝ] H`. -/
def buildKappa (N : ℕ) (ι : ℕ → (E2 →L[ℝ] H)) (π : ℕ → (H →L[ℝ] E2))
    (hπι : ∀ n ≤ N, (π n).comp (ι n) = ContinuousLinearMap.id ℝ E2) (n : ℕ) :
    kerSubmodule (π 0) →L[ℝ] H :=
  if hn : n ≤ N then
    (kerSubmodule (π n)).subtypeL.comp
      (kerLinearIsometryEquiv (hπι 0 (Nat.zero_le N)) (hπι n hn)).toLinearIsometry.toContinuousLinearMap
  else 0

/-- Construct the complementary projection `ρ n : H →L[ℝ] kerSubmodule (π 0)`. -/
def buildRho (N : ℕ) (ι : ℕ → (E2 →L[ℝ] H)) (π : ℕ → (H →L[ℝ] E2))
    (hπι : ∀ n ≤ N, (π n).comp (ι n) = ContinuousLinearMap.id ℝ E2) (n : ℕ) :
    H →L[ℝ] kerSubmodule (π 0) :=
  if hn : n ≤ N then
    (kerLinearIsometryEquiv (hπι 0 (Nat.zero_le N)) (hπι n hn)).symm.toLinearIsometry.toContinuousLinearMap.comp
      (compToKer (ι n) (π n) (hπι n hn))
  else 0

theorem buildKappa_norm_apply {N : ℕ} {ι : ℕ → (E2 →L[ℝ] H)} {π : ℕ → (H →L[ℝ] E2)}
    (hπι : ∀ n ≤ N, (π n).comp (ι n) = ContinuousLinearMap.id ℝ E2)
    {n : ℕ} (hn : n ≤ N) (y : kerSubmodule (π 0)) :
    ‖buildKappa N ι π hπι n y‖ = ‖y‖ := by
  unfold buildKappa
  rw [dif_pos hn]
  change ‖((kerLinearIsometryEquiv (hπι 0 (Nat.zero_le N)) (hπι n hn) y :
    kerSubmodule (π n)) : H)‖ = ‖y‖
  rw [Submodule.norm_coe, LinearIsometryEquiv.norm_map]

theorem buildKappa_norm_le {N : ℕ} {ι : ℕ → (E2 →L[ℝ] H)} {π : ℕ → (H →L[ℝ] E2)}
    (hπι : ∀ n ≤ N, (π n).comp (ι n) = ContinuousLinearMap.id ℝ E2)
    {n : ℕ} (hn : n ≤ N) :
    ‖buildKappa N ι π hπι n‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
  rw [buildKappa_norm_apply hπι hn y, one_mul]

theorem buildRho_norm_apply {N : ℕ} {ι : ℕ → (E2 →L[ℝ] H)} {π : ℕ → (H →L[ℝ] E2)}
    (hπι : ∀ n ≤ N, (π n).comp (ι n) = ContinuousLinearMap.id ℝ E2)
    {n : ℕ} (hn : n ≤ N) (x : H) :
    ‖buildRho N ι π hπι n x‖ = ‖(ContinuousLinearMap.id ℝ H - (ι n).comp (π n)) x‖ := by
  unfold buildRho
  rw [dif_pos hn]
  change ‖(kerLinearIsometryEquiv (hπι 0 (Nat.zero_le N)) (hπι n hn)).symm
    (compToKer (ι n) (π n) (hπι n hn) x)‖ = _
  rw [LinearIsometryEquiv.norm_map, norm_compToKer_apply]

theorem buildRho_norm_le {N : ℕ} {ι : ℕ → (E2 →L[ℝ] H)} {π : ℕ → (H →L[ℝ] E2)}
    (hπι : ∀ n ≤ N, (π n).comp (ι n) = ContinuousLinearMap.id ℝ E2)
    {n : ℕ} (hn : n ≤ N) :
    ‖buildRho N ι π hπι n‖ ≤ 1 + ‖ι n‖ * ‖π n‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  rw [buildRho_norm_apply hπι hn x]
  calc ‖(ContinuousLinearMap.id ℝ H - (ι n).comp (π n)) x‖
      ≤ ‖ContinuousLinearMap.id ℝ H - (ι n).comp (π n)‖ * ‖x‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ (‖ContinuousLinearMap.id ℝ H‖ + ‖(ι n).comp (π n)‖) * ‖x‖ :=
        mul_le_mul_of_nonneg_right (norm_sub_le _ _) (norm_nonneg x)
    _ ≤ (1 + ‖ι n‖ * ‖π n‖) * ‖x‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg x)
        exact add_le_add ContinuousLinearMap.norm_id_le (ContinuousLinearMap.opNorm_comp_le _ _)

theorem build_proj_id_F {N : ℕ} {ι : ℕ → (E2 →L[ℝ] H)} {π : ℕ → (H →L[ℝ] E2)}
    (hπι : ∀ n ≤ N, (π n).comp (ι n) = ContinuousLinearMap.id ℝ E2)
    {n : ℕ} (hn : n ≤ N) :
    (buildRho N ι π hπι n).comp (buildKappa N ι π hπι n) =
      ContinuousLinearMap.id ℝ (kerSubmodule (π 0)) := by
  unfold buildRho buildKappa
  rw [dif_pos hn, dif_pos hn]
  apply ContinuousLinearMap.ext
  intro y
  set z : kerSubmodule (π n) := kerLinearIsometryEquiv (hπι 0 (Nat.zero_le N)) (hπι n hn) y
  change (kerLinearIsometryEquiv (hπι 0 (Nat.zero_le N)) (hπι n hn)).symm
    (compToKer (ι n) (π n) (hπι n hn) (z : H)) = y
  have hz : compToKer (ι n) (π n) (hπι n hn) (z : H) = z := by
    ext
    rw [coe_compToKer_apply]
    simp only [sub_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply]
    have h0 : π n (z : H) = 0 := z.2
    rw [h0, map_zero, sub_zero]
  rw [hz]
  exact (kerLinearIsometryEquiv (hπι 0 (Nat.zero_le N)) (hπι n hn)).symm_apply_apply y

theorem build_proj_orth_EF {N : ℕ} {ι : ℕ → (E2 →L[ℝ] H)} {π : ℕ → (H →L[ℝ] E2)}
    (hπι : ∀ n ≤ N, (π n).comp (ι n) = ContinuousLinearMap.id ℝ E2)
    {n : ℕ} (hn : n ≤ N) :
    (π n).comp (buildKappa N ι π hπι n) = 0 := by
  unfold buildKappa
  rw [dif_pos hn]
  apply ContinuousLinearMap.ext
  intro y
  change π n ((kerLinearIsometryEquiv (hπι 0 (Nat.zero_le N)) (hπι n hn) y :
    kerSubmodule (π n)) : H) = 0
  exact (kerLinearIsometryEquiv (hπι 0 (Nat.zero_le N)) (hπι n hn) y).2

theorem build_proj_orth_FE {N : ℕ} {ι : ℕ → (E2 →L[ℝ] H)} {π : ℕ → (H →L[ℝ] E2)}
    (hπι : ∀ n ≤ N, (π n).comp (ι n) = ContinuousLinearMap.id ℝ E2)
    {n : ℕ} (hn : n ≤ N) :
    (buildRho N ι π hπι n).comp (ι n) = 0 := by
  unfold buildRho
  rw [dif_pos hn]
  apply ContinuousLinearMap.ext
  intro α
  change (kerLinearIsometryEquiv (hπι 0 (Nat.zero_le N)) (hπι n hn)).symm
    (compToKer (ι n) (π n) (hπι n hn) (ι n α)) = 0
  have h0 : compToKer (ι n) (π n) (hπι n hn) (ι n α) = 0 := by
    ext
    rw [coe_compToKer_apply]
    simp only [sub_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.comp_apply, Submodule.coe_zero]
    have h := DFunLike.congr_fun (hπι n hn) α
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h
    rw [h, sub_self]
  rw [h0, map_zero]

theorem build_decomp_id {N : ℕ} {ι : ℕ → (E2 →L[ℝ] H)} {π : ℕ → (H →L[ℝ] E2)}
    (hπι : ∀ n ≤ N, (π n).comp (ι n) = ContinuousLinearMap.id ℝ E2)
    {n : ℕ} (hn : n ≤ N) :
    (ι n).comp (π n) + (buildKappa N ι π hπι n).comp (buildRho N ι π hπι n) =
      ContinuousLinearMap.id ℝ H := by
  unfold buildKappa buildRho
  rw [dif_pos hn, dif_pos hn]
  apply ContinuousLinearMap.ext
  intro x
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
  change ι n (π n x) +
    (((kerLinearIsometryEquiv (hπι 0 (Nat.zero_le N)) (hπι n hn))
      ((kerLinearIsometryEquiv (hπι 0 (Nat.zero_le N)) (hπι n hn)).symm
        (compToKer (ι n) (π n) (hπι n hn) x)) : kerSubmodule (π n)) : H) = x
  rw [LinearIsometryEquiv.apply_symm_apply, coe_compToKer_apply]
  change ι n (π n x) + (x - ι n (π n x)) = x
  abel

theorem buildKappa_eq_sub_comp_apply {N : ℕ} {ι : ℕ → (E2 →L[ℝ] H)} {π : ℕ → (H →L[ℝ] E2)}
    (hπι : ∀ n ≤ N, (π n).comp (ι n) = ContinuousLinearMap.id ℝ E2)
    {n : ℕ} (hn : n ≤ N) (y : kerSubmodule (π 0)) :
    (ContinuousLinearMap.id ℝ H - (ι n).comp (π n)) (buildKappa N ι π hπι n y) =
      buildKappa N ι π hπι n y := by
  have h0 := DFunLike.congr_fun (build_proj_orth_EF hπι hn) y
  simp only [ContinuousLinearMap.comp_apply, zero_apply] at h0
  simp only [sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply, h0, map_zero, sub_zero]

theorem norm_block_b_le {N : ℕ} {ι : ℕ → (E2 →L[ℝ] H)} {π : ℕ → (H →L[ℝ] E2)}
    (hπι : ∀ n ≤ N, (π n).comp (ι n) = ContinuousLinearMap.id ℝ E2)
    {n : ℕ} (hn : n < N) (T : H →L[ℝ] H) :
    ‖(π (n + 1)).comp (T.comp (buildKappa N ι π hπι n))‖ ≤
      ‖(π (n + 1)).comp (T.comp (ContinuousLinearMap.id ℝ H - (ι n).comp (π n)))‖ := by
  have hn_le : n ≤ N := hn.le
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun y => ?_
  have h1 : (π (n + 1)).comp (T.comp (buildKappa N ι π hπι n)) y =
      ((π (n + 1)).comp (T.comp (ContinuousLinearMap.id ℝ H - (ι n).comp (π n))))
        (buildKappa N ι π hπι n y) := by
    simp only [ContinuousLinearMap.comp_apply, buildKappa_eq_sub_comp_apply hπι hn_le y]
  rw [h1]
  calc ‖((π (n + 1)).comp (T.comp (ContinuousLinearMap.id ℝ H - (ι n).comp (π n))))
          (buildKappa N ι π hπι n y)‖
      ≤ ‖(π (n + 1)).comp (T.comp (ContinuousLinearMap.id ℝ H - (ι n).comp (π n)))‖ *
          ‖buildKappa N ι π hπι n y‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = ‖(π (n + 1)).comp (T.comp (ContinuousLinearMap.id ℝ H - (ι n).comp (π n)))‖ * ‖y‖ := by
        rw [buildKappa_norm_apply hπι hn_le y]

theorem norm_block_c_le {N : ℕ} {ι : ℕ → (E2 →L[ℝ] H)} {π : ℕ → (H →L[ℝ] E2)}
    (hπι : ∀ n ≤ N, (π n).comp (ι n) = ContinuousLinearMap.id ℝ E2)
    {n : ℕ} (hn : n < N) (T : H →L[ℝ] H) :
    ‖(buildRho N ι π hπι (n + 1)).comp (T.comp (ι n))‖ ≤
      ‖(ContinuousLinearMap.id ℝ H - (ι (n + 1)).comp (π (n + 1))).comp (T.comp (ι n))‖ := by
  have hn1 : n + 1 ≤ N := hn
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun α => ?_
  simp only [ContinuousLinearMap.comp_apply, buildRho_norm_apply hπι hn1]
  exact ContinuousLinearMap.le_opNorm
    ((ContinuousLinearMap.id ℝ H - (ι (n + 1)).comp (π (n + 1))).comp (T.comp (ι n))) α

theorem norm_block_d_le {N : ℕ} {ι : ℕ → (E2 →L[ℝ] H)} {π : ℕ → (H →L[ℝ] E2)}
    (hπι : ∀ n ≤ N, (π n).comp (ι n) = ContinuousLinearMap.id ℝ E2)
    {n : ℕ} (hn : n < N) (T : H →L[ℝ] H) :
    ‖(buildRho N ι π hπι (n + 1)).comp (T.comp (buildKappa N ι π hπι n))‖ ≤
      ‖(ContinuousLinearMap.id ℝ H - (ι (n + 1)).comp (π (n + 1))).comp
        (T.comp (ContinuousLinearMap.id ℝ H - (ι n).comp (π n)))‖ := by
  have hn_le : n ≤ N := hn.le
  have hn1 : n + 1 ≤ N := hn
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun y => ?_
  simp only [ContinuousLinearMap.comp_apply, buildRho_norm_apply hπι hn1]
  rw [← buildKappa_eq_sub_comp_apply hπι hn_le y]
  calc ‖(ContinuousLinearMap.id ℝ H - (ι (n + 1)).comp (π (n + 1)))
          (T ((ContinuousLinearMap.id ℝ H - (ι n).comp (π n)) (buildKappa N ι π hπι n y)))‖
      ≤ ‖(ContinuousLinearMap.id ℝ H - (ι (n + 1)).comp (π (n + 1))).comp
          (T.comp (ContinuousLinearMap.id ℝ H - (ι n).comp (π n)))‖ *
            ‖buildKappa N ι π hπι n y‖ :=
        ContinuousLinearMap.le_opNorm
          ((ContinuousLinearMap.id ℝ H - (ι (n + 1)).comp (π (n + 1))).comp
            (T.comp (ContinuousLinearMap.id ℝ H - (ι n).comp (π n)))) _
    _ = ‖(ContinuousLinearMap.id ℝ H - (ι (n + 1)).comp (π (n + 1))).comp
          (T.comp (ContinuousLinearMap.id ℝ H - (ι n).comp (π n)))‖ * ‖y‖ := by
        rw [buildKappa_norm_apply hπι hn_le y]

end PartIIbF2Splittings

/-! ## 3. Neumann perturbation of the 2×2 growing block `a_n` around `a_pl` -/

/-- If `a_pl : E2 →L[ℝ] E2` has two-sided inverse `ainv_pl` with `‖ainv_pl‖ ≤ M` (`M > 0`) and
`‖a_n - a_pl‖ ≤ (2 * M)⁻¹`, then `a_n` has a two-sided inverse `ainv_n` with `‖ainv_n‖ ≤ 2 * M`. -/
theorem invertible_two_by_two_of_close
    {a_pl ainv_pl a_n : E2 →L[ℝ] E2} {M : ℝ}
    (hM_pos : 0 < M)
    (h_left : ainv_pl * a_pl = 1)
    (h_right : a_pl * ainv_pl = 1)
    (h_norm : ‖ainv_pl‖ ≤ M)
    (h_diff : ‖a_n - a_pl‖ ≤ (2 * M)⁻¹) :
    ∃ ainv_n : E2 →L[ℝ] E2,
      ainv_n * a_n = 1 ∧ a_n * ainv_n = 1 ∧ ‖ainv_n‖ ≤ 2 * M := by
  set E : E2 →L[ℝ] E2 := (a_n - a_pl) * ainv_pl
  have hE_le : ‖E‖ ≤ 1 / 2 := by
    calc ‖E‖ ≤ ‖a_n - a_pl‖ * ‖ainv_pl‖ := norm_mul_le _ _
      _ ≤ (2 * M)⁻¹ * M := mul_le_mul h_diff h_norm (norm_nonneg _) (by positivity)
      _ = 1 / 2 := by field_simp [hM_pos.ne']
  have hEn : ‖-E‖ < 1 := by
    rw [norm_neg]
    linarith
  obtain ⟨U, hU1, hU2⟩ : ∃ U : E2 →L[ℝ] E2, U * (1 + E) = 1 ∧ (1 + E) * U = 1 := by
    refine ⟨↑(Units.oneSub (-E) hEn)⁻¹, ?_, ?_⟩
    · have h := (Units.oneSub (-E) hEn).inv_mul
      rw [Units.val_oneSub, sub_neg_eq_add] at h
      exact h
    · have h := (Units.oneSub (-E) hEn).mul_inv
      rw [Units.val_oneSub, sub_neg_eq_add] at h
      exact h
  have hUn : ‖U‖ ≤ 2 := by
    have h1 : U = 1 - U * E := by
      have h : U * (1 + E) = U + U * E := by rw [mul_add, mul_one]
      rw [h] at hU1
      exact eq_sub_of_add_eq hU1
    have h3 : ‖(1 : E2 →L[ℝ] E2)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have h2 : ‖U‖ ≤ ‖(1 : E2 →L[ℝ] E2)‖ + ‖U‖ * ‖E‖ := by
      calc ‖U‖ = ‖1 - U * E‖ := by rw [← h1]
        _ ≤ ‖(1 : E2 →L[ℝ] E2)‖ + ‖U * E‖ := norm_sub_le _ _
        _ ≤ ‖(1 : E2 →L[ℝ] E2)‖ + ‖U‖ * ‖E‖ := add_le_add le_rfl (norm_mul_le _ _)
    nlinarith [norm_nonneg U, mul_le_mul_of_nonneg_left hE_le (norm_nonneg U)]
  have han_ainv : a_n * ainv_pl = 1 + E := by
    dsimp [E]
    rw [sub_mul, h_right, add_sub_cancel]
  set ainv_n : E2 →L[ℝ] E2 := ainv_pl * U
  refine ⟨ainv_n, ?_, ?_, ?_⟩
  · calc ainv_n * a_n
        = (ainv_pl * U * a_n) * 1 := (mul_one _).symm
      _ = (ainv_pl * U * a_n) * (ainv_pl * a_pl) := by rw [h_left]
      _ = ainv_pl * (U * (a_n * ainv_pl)) * a_pl := by noncomm_ring
      _ = ainv_pl * (U * (1 + E)) * a_pl := by rw [han_ainv]
      _ = ainv_pl * 1 * a_pl := by rw [hU1]
      _ = ainv_pl * a_pl := by rw [mul_one]
      _ = 1 := h_left
  · calc a_n * ainv_n
        = (a_n * ainv_pl) * U := (mul_assoc _ _ _).symm
      _ = (1 + E) * U := by rw [han_ainv]
      _ = 1 := hU2
  · calc ‖ainv_n‖ ≤ ‖ainv_pl‖ * ‖U‖ := norm_mul_le _ _
      _ ≤ M * 2 := mul_le_mul h_norm hUn (norm_nonneg _) hM_pos.le
      _ = 2 * M := by ring

/-! ## 4. Leaf propositions (`PartII-b:F2/1` .. `PartII-b:F2/4`) and assembly -/

/-- **Leaf 1 (`PartII-b:F2/1`, early-train comparison in the `m`-weighted derivative budget,
`short-bg:train-early`, SP 2085–2090)**: on `s ≤ Σ/ν`, for `(p, d)` in `BgRegime p d dm dp`, the
train difference `p.train.v - V_c` satisfies `TrainCloseM m p.train Sg δ` with `δ → 0` as
`p.ν → 0`. -/
def TrainCloseRegime : Prop :=
  ∀ m : ℝ, 8 < m → ∀ Sg : ℝ, 0 < Sg → ∀ dm dp : ℝ, 0 < dm →
    ∀ δ : ℝ, 0 < δ → ∃ ν₀ : ℝ, 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ →
        TrainCloseM m p.train Sg δ

/-- `Sc : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)` is the bounded linear evolution family of the free
cylinder vorticity equation `ω_s = (ν Δ - v_c(s)·∇) ω` on `[0, p.H]` (SP 2079–2102): it obeys the
evolution-family laws `Sc s s = I` and `Sc t r ∘ Sc r s = Sc t s` for `0 ≤ s ≤ r ≤ t ≤ p.H`, is
strongly continuous in `t`, and for every `s ∈ [0, p.H]` and `f ∈ Xmc p.c m`, `t ↦ Sc t s f` agrees
a.e. on `B0579.cell p.c` with a weak free cylinder flow `IsFreeCylFlow m p.train s f ω`. -/
structure IsFreeCylPropagator (m : ℝ) (p : Params)
    (Sc : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)) : Prop where
  id_self : ∀ s ∈ Icc 0 p.H, Sc s s = ContinuousLinearMap.id ℝ (Xmc p.c m)
  comp_cocycle : ∀ s r t : ℝ, 0 ≤ s → s ≤ r → r ≤ t → t ≤ p.H →
    (Sc t r).comp (Sc r s) = Sc t s
  strongCont : ∀ s ∈ Icc 0 p.H, ∀ f : Xmc p.c m,
    ContinuousOn (fun t => Sc t s f) (Icc s p.H)
  flow : ∀ s ∈ Icc 0 p.H, ∀ f : Xmc p.c m,
    ∃ ω : ℝ → B0579.Plane → ℝ, IsFreeCylFlow m p.train s f ω ∧
      ∀ t ∈ Icc s p.H, (Sc t s f : B0579.Plane → ℝ) =ᵐ[volume.restrict (B0579.cell p.c)] ω t

/-- `U` is the coupled cylinder vorticity propagator on `[0, p.H]` associated to the free propagator
`Sc` (`IsFreeCylPropagator m p Sc`) and a cylinder interaction family
`Ac : ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)` (`∀ s ∈ Icc 0 p.H, IsCylInteractionOp p.train m s (Ac s)`):
it satisfies `IsCoupledPropagator m p U` and the mild Duhamel equation
`U t s f = Sc t s f + ∫ r in s..t, Sc t r (Ac r (U r s f))` on `0 ≤ s ≤ t ≤ p.H`. -/
structure IsCoupledDuhamelPropagator (m : ℝ) (p : Params)
    (Sc : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m))
    (Ac : ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m))
    (U : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)) : Prop where
  free_prop : IsFreeCylPropagator m p Sc
  cyl_op : ∀ s ∈ Icc 0 p.H, IsCylInteractionOp p.train m s (Ac s)
  coupled_prop : IsCoupledPropagator m p U
  duhamel_integrable : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ p.H → ∀ f : Xmc p.c m,
    IntervalIntegrable (fun r => Sc t r (Ac r (U r s f))) volume s t
  duhamel_eq : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ p.H → ∀ f : Xmc p.c m,
    U t s f = Sc t s f + ∫ r in s..t, Sc t r (Ac r (U r s f))

/-- **Leaf 2 (`PartII-b:F2/2`, coupled cylinder vorticity propagator via Duhamel iteration,
SP 2076–2083, 2141–2155)**: for every `m > 8` and `Sig > 0`, there is a growth constant `K₀ > 0`
such that for every parameter point `(p, d)` in `BgRegime p d dm dp` with `p.ν ≤ 1`,
`p.ageCut = Sig`, `0 < δ ≤ 1`, `TrainCloseM m p.train Sig δ`, and every cylinder interaction family
`Ac : ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)` with `∀ s ∈ Icc 0 p.H, IsCylInteractionOp p.train m s (Ac s)`
and `∀ s ∈ Icc 0 p.H, ‖Ac s‖ ≤ M_A` (`0 ≤ M_A`), there exist the free cylinder propagator `Sc` and
coupled cylinder propagator `U` satisfying `IsCoupledDuhamelPropagator m p Sc Ac U` and the
exponential operator-norm bounds `‖Sc t s‖ ≤ exp (K₀ * (t - s))` and
`‖U t s‖ ≤ exp ((K₀ + M_A) * (t - s))` for all `0 ≤ s ≤ t ≤ p.H`. -/
def CoupledPropagatorStep : Prop :=
  ∀ m : ℝ, 8 < m → ∀ Sig : ℝ, 0 < Sig → ∃ K₀ : ℝ, 0 < K₀ ∧
    ∀ (p : Params) (d dm dp : ℝ), BgRegime p d dm dp → p.ν ≤ 1 → p.ageCut = Sig →
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 → TrainCloseM m p.train Sig δ →
    ∀ (M_A : ℝ) (Ac : ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)), 0 ≤ M_A →
      (∀ s ∈ Icc 0 p.H, IsCylInteractionOp p.train m s (Ac s) ∧ ‖Ac s‖ ≤ M_A) →
      ∃ (Sc U : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)),
        IsCoupledDuhamelPropagator m p Sc Ac U ∧
        ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ p.H →
          ‖Sc t s‖ ≤ Real.exp (K₀ * (t - s)) ∧
          ‖U t s‖ ≤ Real.exp ((K₀ + M_A) * (t - s))

namespace PartIIbF23Sub

/-- Frozen planar Gaussian angular velocity `Ω_{1+σ}(x) = (1 + σ)⁻² Ω₀(x / √(1 + σ))` at slow age
`σ` (`a = 1 + σ`, SP 931–953, 2104–2115). -/
def frozenOmega (σ : ℝ) (x : B0579.Plane) : ℝ :=
  ((1 + σ) ^ 2)⁻¹ * B0009.Omega (ofPlane (scalePlane (1 + σ) x))

/-- Pointwise flow map of the frozen planar radial transport group `T_pl σ τ` at slow age `σ`:
rotation by `-τ * frozenOmega σ x` on `B0579.Plane = ℝ × ℝ` (SP 841–852, 931–953, 2104–2115). -/
def frozenRadialFlow (σ τ : ℝ) (x : B0579.Plane) : B0579.Plane :=
  let θ : ℝ := -τ * frozenOmega σ x
  (Real.cos θ * x.1 - Real.sin θ * x.2, Real.sin θ * x.1 + Real.cos θ * x.2)

end PartIIbF23Sub

/-- `T_pl` is the frozen planar radial transport group on `X_m` at the slow ages `σ ∈ [0, Sig]`
(SP 841–852: `T(t)f(r, ϑ) = f(r, ϑ - Ω(r) t)`; SP 2104–2115: "The frozen radial transport is
unitary in this radial weighted space"): for each `σ ∈ [0, Sig]`, `τ ↦ T_pl σ τ` is a strongly
continuous isometric group on `X_m`, and `T_pl σ τ f` is composition of `f` with the rotation flow
`PartIIbF23Sub.frozenRadialFlow σ τ` of the frozen angular velocity `Ω_{1+σ}` (SP 931–953). -/
structure IsFrozenRadialTransport (m Sig : ℝ) (T_pl : ℝ → ℝ → (Xm m →L[ℝ] Xm m)) : Prop where
  zero : ∀ σ ∈ Icc 0 Sig, T_pl σ 0 = ContinuousLinearMap.id ℝ (Xm m)
  add : ∀ σ ∈ Icc 0 Sig, ∀ τ₁ τ₂ : ℝ, T_pl σ (τ₁ + τ₂) = (T_pl σ τ₁).comp (T_pl σ τ₂)
  isometry : ∀ σ ∈ Icc 0 Sig, ∀ τ : ℝ, ∀ f : Xm m, ‖T_pl σ τ f‖ = ‖f‖
  cont : ∀ σ ∈ Icc 0 Sig, ∀ f : Xm m, Continuous (fun τ => T_pl σ τ f)
  flow : ∀ σ ∈ Icc 0 Sig, ∀ τ : ℝ, ∀ f : Xm m,
    (T_pl σ τ f : B0579.Plane → ℝ) =ᵐ[planeMeasure m]
      fun x => f (PartIIbF23Sub.frozenRadialFlow σ τ x)

/-- Package of the frozen planar Euler evolution `E_pl(σ, τ)` and periodized/planar growing
coordinate maps `(ι_c, π_c, ι_pl, π_pl)` for fixed slow data `(m, Sig, lam, q)` (SP 841–852,
931–953, 2104–2115, 2145–2171). Besides the semigroup law and the action on the growing plane
(`euler_eigen`), `E_pl σ` commutes with the frozen spectral projection `ι_pl σ ∘ π_pl σ`
(`euler_comm`, SP 931–953: the projections `𝒫_a = J_a 𝒫 J_a⁻¹` are spectral projections of the
frozen generator) and is the mild Duhamel evolution of the frozen radial transport group `T_pl σ`
perturbed by the planar interaction `A_{pl,σ}` (`euler_duhamel`, SP 841–852, 2104–2115, 2147–2155),
so that `E_pl` is the frozen planar Euler evolution itself, on the complementary space as well. -/
structure IsFrozenEulerPackage (m Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile)
    (L₀ M_E c₀ : ℝ)
    (ι_pl : ℝ → (E2 →L[ℝ] Xm m)) (π_pl : ℝ → (Xm m →L[ℝ] E2))
    (E_pl : ℝ → ℝ → (Xm m →L[ℝ] Xm m))
    (ι_c : ∀ c : ℝ, ℝ → (E2 →L[ℝ] Xmc c m))
    (π_c : ∀ c : ℝ, ℝ → (Xmc c m →L[ℝ] E2)) : Prop where
  L₀_ge_one : 1 ≤ L₀
  M_E_ge_one : 1 ≤ M_E
  c₀_ge_one : 1 ≤ c₀
  cyl_direct_ae : ∀ c : ℝ, c₀ ≤ c → ∀ σ ∈ Icc 0 Sig, ∀ α : E2,
    (ι_c c σ α : B0579.Plane → ℝ) =ᵐ[B0579.cellMeasure c m]
      fun x => ∑ i : Fin 2, α i * frozenDirectMode q c (1 + σ) i x
  cyl_zeroCirc : ∀ c : ℝ, c₀ ≤ c → ∀ σ ∈ Icc 0 Sig, ∀ α : E2,
    HasZeroCirculationR c (ι_c c σ α)
  cyl_proj_id : ∀ c : ℝ, c₀ ≤ c → ∀ σ ∈ Icc 0 Sig,
    (π_c c σ).comp (ι_c c σ) = ContinuousLinearMap.id ℝ E2
  cyl_norm : ∀ c : ℝ, c₀ ≤ c → ∀ σ ∈ Icc 0 Sig,
    ‖ι_c c σ‖ ≤ M_E ∧ ‖π_c c σ‖ ≤ M_E
  pl_cont : ContinuousOn ι_pl (Icc 0 Sig) ∧ ContinuousOn π_pl (Icc 0 Sig)
  pl_proj_id : ∀ σ ∈ Icc 0 Sig,
    (π_pl σ).comp (ι_pl σ) = ContinuousLinearMap.id ℝ E2 ∧
      ‖ι_pl σ‖ ≤ M_E ∧ ‖π_pl σ‖ ≤ M_E
  coord_conv : ∀ ε : ℝ, 0 < ε → ∃ c₁ : ℝ, c₀ ≤ c₁ ∧ ∀ c : ℝ, c₁ ≤ c →
    ∀ σ ∈ Icc 0 Sig,
      ‖(Jc c m).comp (ι_c c σ) - ι_pl σ‖ ≤ ε ∧
      ‖(π_c c σ).comp (Rc c m) - π_pl σ‖ ≤ ε
  euler_semigroup : ∀ σ ∈ Icc 0 Sig,
    E_pl σ 0 = ContinuousLinearMap.id ℝ (Xm m) ∧
    (∀ τ₁ τ₂ : ℝ, 0 ≤ τ₁ → 0 ≤ τ₂ → E_pl σ (τ₁ + τ₂) = (E_pl σ τ₁).comp (E_pl σ τ₂)) ∧
    ∀ f : Xm m, ContinuousOn (fun τ => E_pl σ τ f) (Ici 0)
  euler_eigen : ∀ σ ∈ Icc 0 Sig, ∀ τ : ℝ, 0 ≤ τ →
    let θ : ℝ := lam.im * τ / (1 + σ) ^ 2
    let r : ℝ := Real.exp (lam.re * τ / (1 + σ) ^ 2)
    (E_pl σ τ).comp (ι_pl σ) =
      (ι_pl σ).comp
        (LinearMap.toContinuousLinearMap
          (Matrix.toEuclideanLin ![![r * Real.cos θ, -r * Real.sin θ],
                                   ![r * Real.sin θ,  r * Real.cos θ]]))
  euler_comm : ∀ σ ∈ Icc 0 Sig, ∀ τ : ℝ, 0 ≤ τ →
    (E_pl σ τ).comp ((ι_pl σ).comp (π_pl σ)) = ((ι_pl σ).comp (π_pl σ)).comp (E_pl σ τ)
  euler_duhamel : ∃ T_pl : ℝ → ℝ → (Xm m →L[ℝ] Xm m),
    IsFrozenRadialTransport m Sig T_pl ∧
    ∀ σ ∈ Icc 0 Sig, ∀ A : Xm m →L[ℝ] Xm m, IsPlanarInteractionOp m σ A →
      ∀ τ : ℝ, 0 ≤ τ → ∀ f : Xm m,
        IntervalIntegrable (fun r => T_pl σ (τ - r) (A (E_pl σ r f))) volume 0 τ ∧
        E_pl σ τ f = T_pl σ τ f + ∫ r in (0 : ℝ)..τ, T_pl σ (τ - r) (A (E_pl σ r f))

/-- **Leaf 3 (`PartII-b:F2/3`, frozen planar Euler dichotomy and periodized cylinder coordinate
projections, SP 931–953, 2145–2171)**: for every `m > 8`, `Sig > 0`, growing eigenpair `(lam, q)`,
and dichotomy exponents `0 < a' < b' < lam.re / (1 + Sig) ^ 2`, there exist `L₀, M_E, c₀ ≥ 1`,
planar coordinates `(ι_pl, π_pl)`, planar frozen Euler evolutions `E_pl`, and cylinder coordinates
`(ι_c, π_c)` forming an `IsFrozenEulerPackage` such that for all `σ ∈ [0, Sig]` and
`L ∈ [L₀, 2 * L₀]`, the planar growing block `π_pl σ ∘ E_pl σ L ∘ ι_pl σ` has two-sided inverse
bounded by `(1/4) * exp(-b' * L)`, the planar complementary block is bounded by
`(1/4) * exp(a' * L)`, and the planar off-diagonal blocks vanish. -/
def FrozenEulerSplittingStep : Prop :=
  ∀ m : ℝ, 8 < m →
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ a' b' : ℝ, 0 < a' → a' < b' → b' < lam.re / (1 + Sig) ^ 2 →
    ∃ (L₀ M_E c₀ : ℝ)
      (ι_pl : ℝ → (E2 →L[ℝ] Xm m)) (π_pl : ℝ → (Xm m →L[ℝ] E2))
      (E_pl : ℝ → ℝ → (Xm m →L[ℝ] Xm m))
      (ι_c : ∀ c : ℝ, ℝ → (E2 →L[ℝ] Xmc c m))
      (π_c : ∀ c : ℝ, ℝ → (Xmc c m →L[ℝ] E2)),
      IsFrozenEulerPackage m Sig lam q L₀ M_E c₀ ι_pl π_pl E_pl ι_c π_c ∧
      ∀ σ ∈ Icc 0 Sig, ∀ L ∈ Icc L₀ (2 * L₀),
        (∃ ainv_pl : E2 →L[ℝ] E2,
          ainv_pl * ((π_pl σ).comp ((E_pl σ L).comp (ι_pl σ))) = 1 ∧
          ((π_pl σ).comp ((E_pl σ L).comp (ι_pl σ))) * ainv_pl = 1 ∧
          ‖ainv_pl‖ ≤ (1 / 4 : ℝ) * Real.exp (-b' * L)) ∧
        ‖(ContinuousLinearMap.id ℝ (Xm m) - (ι_pl σ).comp (π_pl σ)).comp
          ((E_pl σ L).comp (ContinuousLinearMap.id ℝ (Xm m) - (ι_pl σ).comp (π_pl σ)))‖ ≤
            (1 / 4 : ℝ) * Real.exp (a' * L) ∧
        (π_pl σ).comp ((E_pl σ L).comp
          (ContinuousLinearMap.id ℝ (Xm m) - (ι_pl σ).comp (π_pl σ))) = 0 ∧
        (ContinuousLinearMap.id ℝ (Xm m) - (ι_pl σ).comp (π_pl σ)).comp
          ((E_pl σ L).comp (ι_pl σ)) = 0

/-- **Leaf 4 (`PartII-b:F2/4`, compact-Duhamel block approximation on `[t, t + L]`,
SP 2104–2115, 2145–2166)**: given an `IsFrozenEulerPackage`, the norm-continuous collectively
compact planar interaction family `AplOp` on `[0, Sig]`, and the cylinder-to-planar interaction
comparison bound `C_Sg * (p.c ^ (-2) + δ)`, for every tolerance `ε > 0` there exist `δ ∈ (0, 1]`
and `ν₀ ∈ (0, 1]` such that at every `BgRegime` point with `p.ν ≤ ν₀`, `c₀ ≤ p.c`, `p.ageCut = Sig`,
`p.mode = q`, `TrainCloseM m p.train Sig δ`, and any `IsCoupledDuhamelPropagator m p Sc Ac U`
satisfying the free/coupled exponential bounds and interaction comparison, the four block entries of
`U(t + L, t)` in `(ι_c, π_c)` are within `ε` of the corresponding block entries of
`E_pl(p.ν * t, L)` in `(ι_pl, π_pl)` for all `0 ≤ t ≤ t + L ≤ p.H` with `L ∈ [L₀, 2 * L₀]`. -/
def CompactDuhamelBlockStep : Prop :=
  ∀ m : ℝ, 8 < m →
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ (L₀ M_E c₀ : ℝ)
    (ι_pl : ℝ → (E2 →L[ℝ] Xm m)) (π_pl : ℝ → (Xm m →L[ℝ] E2))
    (E_pl : ℝ → ℝ → (Xm m →L[ℝ] Xm m))
    (ι_c : ∀ c : ℝ, ℝ → (E2 →L[ℝ] Xmc c m))
    (π_c : ∀ c : ℝ, ℝ → (Xmc c m →L[ℝ] E2)),
    IsFrozenEulerPackage m Sig lam q L₀ M_E c₀ ι_pl π_pl E_pl ι_c π_c →
  ∀ (K₀ C_Sg : ℝ) (AplOp : ℝ → (Xm m →L[ℝ] Xm m)),
    0 < K₀ → 0 < C_Sg →
    ContinuousOn AplOp (Icc 0 Sig) →
    (∀ σ ∈ Icc 0 Sig, IsPlanarInteractionOp m σ (AplOp σ) ∧ IsCompactOperator (AplOp σ)) →
    TotallyBounded (AplOp '' Icc 0 Sig) →
    (∀ R : ℝ, TotallyBounded (⋃ σ ∈ Icc 0 Sig, AplOp σ '' Metric.closedBall (0 : Xm m) R)) →
  ∀ dm dp : ℝ, 0 < dm →
  ∀ ε : ℝ, 0 < ε →
    ∃ (δ ν₀ : ℝ), 0 < δ ∧ δ ≤ 1 ∧ 0 < ν₀ ∧ ν₀ ≤ 1 ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → c₀ ≤ p.c →
        p.ageCut = Sig → p.mode = q → TrainCloseM m p.train Sig δ →
      ∀ (Sc U : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m))
        (Ac : ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)),
        IsCoupledDuhamelPropagator m p Sc Ac U →
        (∀ s ∈ Icc 0 p.H,
          IsCompactOperator (Ac s) ∧
          ‖(Jc p.c m).comp ((Ac s).comp (Rc p.c m)) - AplOp (p.ν * s)‖ ≤
            C_Sg * (p.c ^ (-2 : ℝ) + δ)) →
        (∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ p.H →
          ‖Sc t s‖ ≤ Real.exp (K₀ * (t - s))) →
        ∀ t L : ℝ, 0 ≤ t → t + L ≤ p.H → L ∈ Icc L₀ (2 * L₀) →
          let σ₀ : ℝ := p.ν * t
          let σ₁ : ℝ := p.ν * (t + L)
          let Pc₀ : Xmc p.c m →L[ℝ] Xmc p.c m := (ι_c p.c σ₀).comp (π_c p.c σ₀)
          let Pc₁ : Xmc p.c m →L[ℝ] Xmc p.c m := (ι_c p.c σ₁).comp (π_c p.c σ₁)
          let Ppl₀ : Xm m →L[ℝ] Xm m := (ι_pl σ₀).comp (π_pl σ₀)
          ‖(π_c p.c σ₁).comp ((U (t + L) t).comp (ι_c p.c σ₀)) -
              (π_pl σ₀).comp ((E_pl σ₀ L).comp (ι_pl σ₀))‖ ≤ ε ∧
          ‖(ContinuousLinearMap.id ℝ (Xmc p.c m) - Pc₁).comp
              ((U (t + L) t).comp (ContinuousLinearMap.id ℝ (Xmc p.c m) - Pc₀))‖ ≤
            ‖(ContinuousLinearMap.id ℝ (Xm m) - Ppl₀).comp
              ((E_pl σ₀ L).comp (ContinuousLinearMap.id ℝ (Xm m) - Ppl₀))‖ + ε ∧
          ‖(π_c p.c σ₁).comp
              ((U (t + L) t).comp (ContinuousLinearMap.id ℝ (Xmc p.c m) - Pc₀))‖ ≤ ε ∧
          ‖(ContinuousLinearMap.id ℝ (Xmc p.c m) - Pc₁).comp
              ((U (t + L) t).comp (ι_c p.c σ₀))‖ ≤ ε

/-- Norm bound on a continuous operator family on `Icc 0 Sig`. -/
private theorem exists_norm_bound_on_Icc {m Sig : ℝ} (hSig : 0 < Sig)
    (AplOp : ℝ → (Xm m →L[ℝ] Xm m)) (hcont : ContinuousOn AplOp (Icc 0 Sig)) :
    ∃ M_pl : ℝ, 0 ≤ M_pl ∧ ∀ σ ∈ Icc 0 Sig, ‖AplOp σ‖ ≤ M_pl := by
  have hne : (Icc (0 : ℝ) Sig).Nonempty := nonempty_Icc.2 hSig.le
  obtain ⟨σ₀, hσ₀_mem, hσ₀_max⟩ := isCompact_Icc.exists_isMaxOn hne hcont.norm
  refine ⟨max ‖AplOp σ₀‖ 0, le_max_right _ _, fun σ hσ => ?_⟩
  exact (hσ₀_max hσ).trans (le_max_left _ _)

/-- **Full assembly of `BlockDichotomy` (`PartII-b:F2`)** from `InteractionCylinderComparison`,
`InteractionCollectiveCompact` (`PartII-b:F1`), and the four leaves `TrainCloseRegime`
(`PartII-b:F2/1`), `CoupledPropagatorStep` (`PartII-b:F2/2`), `FrozenEulerSplittingStep`
(`PartII-b:F2/3`), and `CompactDuhamelBlockStep` (`PartII-b:F2/4`). -/
theorem blockDichotomy_of_leaves
    (hComp : InteractionCylinderComparison)
    (hColl : InteractionCollectiveCompact)
    (hTC : TrainCloseRegime)
    (hProp : CoupledPropagatorStep)
    (hSplit : FrozenEulerSplittingStep)
    (hDuh : CompactDuhamelBlockStep) :
    BlockDichotomy := by
  intro m hm Sig lam q hSig hEig a' b' ha' hab' hb' dm dp hdm
  obtain ⟨K₀, hK₀, hProp_op⟩ := hProp m hm Sig hSig
  obtain ⟨C_Sg, hC_Sg, hComp_op⟩ := hComp m hm Sig hSig
  obtain ⟨hColl_cyl, AplOp, hApl_cont, hApl_prop, hApl_tb, hApl_ball⟩ := hColl m hm Sig hSig
  obtain ⟨M_pl, hM_pl_nn, hM_pl_bd⟩ := exists_norm_bound_on_Icc hSig AplOp hApl_cont
  obtain ⟨L₀, M_E, c₀, ι_pl, π_pl, E_pl, ι_c, π_c, hPkg, hDich⟩ :=
    hSplit m hm Sig lam q hSig hEig a' b' ha' hab' hb'
  have hL₀ : 1 ≤ L₀ := hPkg.L₀_ge_one
  have hL₀_pos : 0 < L₀ := lt_of_lt_of_le zero_lt_one hL₀
  have hM_E : 1 ≤ M_E := hPkg.M_E_ge_one
  have hc₀ : 1 ≤ c₀ := hPkg.c₀_ge_one
  have hc₀_pos : 0 < c₀ := lt_of_lt_of_le zero_lt_one hc₀
  set M_A : ℝ := M_pl + C_Sg * 2
  have hM_A_nn : 0 ≤ M_A := by dsimp [M_A]; positivity
  set M_prop : ℝ := Real.exp ((K₀ + M_A) * (2 * L₀))
  set M_coord : ℝ := max (1 + M_E ^ 2) M_prop
  have hM_coord : 1 ≤ M_coord := by
    refine le_trans ?_ (le_max_left _ _)
    nlinarith
  refine ⟨L₀, M_coord, hL₀, hM_coord, ?_⟩
  intro η hη
  set ε : ℝ := min η (min (Real.exp (-2 * b' * L₀)) ((1 / 4 : ℝ) * Real.exp (a' * L₀)))
  have hε_pos : 0 < ε := by
    dsimp [ε]
    refine lt_min hη (lt_min (Real.exp_pos _) ?_)
    positivity
  obtain ⟨δ, ν₁, hδ_pos, hδ_le_1, hν₁_pos, hν₁_le_1, hDuh_op⟩ :=
    hDuh m hm Sig lam q hSig hEig L₀ M_E c₀ ι_pl π_pl E_pl ι_c π_c hPkg
      K₀ C_Sg AplOp hK₀ hC_Sg hApl_cont hApl_prop hApl_tb hApl_ball dm dp hdm ε hε_pos
  obtain ⟨ν₂, hν₂_pos, hTC_op⟩ := hTC m hm Sig hSig dm dp hdm δ hδ_pos
  set ν_grid : ℝ := Sig / (2 * L₀)
  have hν_grid_pos : 0 < ν_grid := by dsimp [ν_grid]; positivity
  set ν_c₀ : ℝ := (Real.sqrt c₀)⁻¹
  have hν_c₀_pos : 0 < ν_c₀ := by dsimp [ν_c₀]; positivity
  set ν₀ : ℝ := min (min ν₁ ν₂) (min ν_grid ν_c₀)
  have hν₀_pos : 0 < ν₀ := lt_min (lt_min hν₁_pos hν₂_pos) (lt_min hν_grid_pos hν_c₀_pos)
  refine ⟨ν₀, hν₀_pos, ?_⟩
  intro p d hbg hν hAge hMode
  have hν0 : 0 < p.ν := p.ν_pos
  have hν_le_ν₁ : p.ν ≤ ν₁ := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν_le_ν₂ : p.ν ≤ ν₂ := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν_le_grid : p.ν ≤ ν_grid := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν_le_c₀ : p.ν ≤ ν_c₀ := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hν_le_1 : p.ν ≤ 1 := hν_le_ν₁.trans hν₁_le_1
  have hc_ge_c₀ : c₀ ≤ p.c := bgRegime_c_ge hbg hc₀_pos hν_le_c₀
  have hc1 : 1 ≤ p.c := hc₀.trans hc_ge_c₀
  have hcloseM : TrainCloseM m p.train Sig δ := hTC_op p d hbg hν_le_ν₂
  have hH_eq : p.H = Sig / p.ν := by
    change p.ageCut / p.ν = Sig / p.ν
    rw [hAge]
  have h2L₀_le_H : 2 * L₀ ≤ p.H := by
    rw [hH_eq, le_div_iff₀ hν0]
    have h1 := (le_div_iff₀ (by positivity : 0 < 2 * L₀)).1 hν_le_grid
    linarith
  obtain ⟨N, L, hN_pos, hL_bounds, hNL⟩ := exists_block_grid hL₀_pos h2L₀_le_H
  -- Construct the cylinder interaction family `Ac` on `[0, p.H]`
  have hAc_ex : ∀ s : ℝ, ∃ A : Xmc p.c m →L[ℝ] Xmc p.c m,
      s ∈ Icc 0 p.H →
        IsCylInteractionOp p.train m s A ∧
        IsCompactOperator A ∧
        ‖(Jc p.c m).comp (A.comp (Rc p.c m)) - AplOp (p.ν * s)‖ ≤
          C_Sg * (p.c ^ (-2 : ℝ) + δ) ∧
        ‖A‖ ≤ M_A := by
    intro s
    by_cases hs : s ∈ Icc 0 p.H
    · set σ : ℝ := p.ν * s
      have hσ : σ ∈ Icc 0 Sig := by
        refine ⟨mul_nonneg hν0.le hs.1, ?_⟩
        have hsH : s ≤ Sig / p.ν := hH_eq ▸ hs.2
        calc p.ν * s ≤ p.ν * (Sig / p.ν) := mul_le_mul_of_nonneg_left hsH hν0.le
          _ = Sig := mul_div_cancel₀ Sig hν0.ne'
      have hs_div : σ / p.ν = s := mul_div_cancel_left₀ s hν0.ne'
      have hs_mem' : s ∈ Icc 0 (Sig / p.ν) := hH_eq ▸ hs
      obtain ⟨⟨Ac₀, _, hAc₀_op, _⟩, hAc₀_bd⟩ := hComp_op p d dm dp hbg hc1 δ hδ_pos.le hcloseM σ hσ
      have hAc₀_op_s : IsCylInteractionOp p.train m s Ac₀ := hs_div ▸ hAc₀_op
      have hAc₀_comp := (hColl_cyl p d dm dp hbg hc1 δ hδ_pos.le hcloseM s hs_mem').2 Ac₀ hAc₀_op_s
      have hdiff_bd :
          ‖(Jc p.c m).comp (Ac₀.comp (Rc p.c m)) - AplOp σ‖ ≤ C_Sg * (p.c ^ (-2 : ℝ) + δ) :=
        hAc₀_bd Ac₀ (AplOp σ) hAc₀_op (hApl_prop σ hσ).1
      have hAc₀_norm : ‖Ac₀‖ ≤ M_A := by
        rw [← norm_eq_norm_Jc_comp_Rc p.c m Ac₀]
        have htri : ‖(Jc p.c m).comp (Ac₀.comp (Rc p.c m))‖ ≤
            ‖AplOp σ‖ + ‖(Jc p.c m).comp (Ac₀.comp (Rc p.c m)) - AplOp σ‖ := by
          simpa only [add_sub_cancel] using
            norm_add_le (AplOp σ) ((Jc p.c m).comp (Ac₀.comp (Rc p.c m)) - AplOp σ)
        have hc_inv : p.c ^ (-2 : ℝ) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
        have hApl_le : ‖AplOp σ‖ ≤ M_pl := hM_pl_bd σ hσ
        have hdiff_le_2 : C_Sg * (p.c ^ (-2 : ℝ) + δ) ≤ C_Sg * 2 :=
          mul_le_mul_of_nonneg_left (by linarith) hC_Sg.le
        dsimp [M_A]
        linarith
      exact ⟨Ac₀, fun _ => ⟨hAc₀_op_s, hAc₀_comp.1, hdiff_bd, hAc₀_norm⟩⟩
    · exact ⟨0, fun h => False.elim (hs h)⟩
  choose Ac hAc using hAc_ex
  obtain ⟨Sc, U, hCD, hScU_bd⟩ :=
    hProp_op p d dm dp hbg hν_le_1 hAge δ hδ_pos hδ_le_1 hcloseM M_A Ac hM_A_nn
      (fun s hs => ⟨(hAc s hs).1, (hAc s hs).2.2.2⟩)
  -- Define grid growing coordinates `ι n` and `π n`
  let σ_grid : ℕ → ℝ := fun n => p.ν * ((n : ℝ) * L)
  have hσ_grid_mem : ∀ n ≤ N, σ_grid n ∈ Icc 0 Sig := by
    intro n hn
    dsimp [σ_grid]
    have hL_nn : 0 ≤ L := hL₀_pos.le.trans hL_bounds.1
    have htn_le : (n : ℝ) * L ≤ p.H := by
      rw [← hNL]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hL_nn
    refine ⟨by positivity, ?_⟩
    have htn_le' : (n : ℝ) * L ≤ Sig / p.ν := hH_eq ▸ htn_le
    calc p.ν * ((n : ℝ) * L) ≤ p.ν * (Sig / p.ν) := mul_le_mul_of_nonneg_left htn_le' hν0.le
      _ = Sig := mul_div_cancel₀ Sig hν0.ne'
  let ι_grid : ℕ → (E2 →L[ℝ] Xmc p.c m) := fun n => ι_c p.c (σ_grid n)
  let π_grid : ℕ → (Xmc p.c m →L[ℝ] E2) := fun n => π_c p.c (σ_grid n)
  have hπι_grid : ∀ n ≤ N, (π_grid n).comp (ι_grid n) = ContinuousLinearMap.id ℝ E2 :=
    fun n hn => hPkg.cyl_proj_id p.c hc_ge_c₀ (σ_grid n) (hσ_grid_mem n hn)
  -- Block bounds and `ainv` at each `n < N`
  have hainv_ex : ∀ n : ℕ, ∃ ainv_n : E2 →L[ℝ] E2,
      n < N →
        let tn : ℝ := (n : ℝ) * L
        let tn1 : ℝ := (((n + 1 : ℕ) : ℝ) * L)
        let a_n : E2 →L[ℝ] E2 := (π_grid (n + 1)).comp ((U tn1 tn).comp (ι_grid n))
        ainv_n * a_n = 1 ∧
        a_n * ainv_n = 1 ∧
        ‖ainv_n‖ ≤ (1 / 2 : ℝ) * Real.exp (-b' * L) ∧
        ‖(ContinuousLinearMap.id ℝ (Xmc p.c m) - (ι_grid (n + 1)).comp (π_grid (n + 1))).comp
          ((U tn1 tn).comp
            (ContinuousLinearMap.id ℝ (Xmc p.c m) - (ι_grid n).comp (π_grid n)))‖ ≤
          (1 / 2 : ℝ) * Real.exp (a' * L) ∧
        ‖(π_grid (n + 1)).comp
          ((U tn1 tn).comp
            (ContinuousLinearMap.id ℝ (Xmc p.c m) - (ι_grid n).comp (π_grid n)))‖ ≤ η ∧
        ‖(ContinuousLinearMap.id ℝ (Xmc p.c m) - (ι_grid (n + 1)).comp (π_grid (n + 1))).comp
          ((U tn1 tn).comp (ι_grid n))‖ ≤ η := by
    intro n
    by_cases hn : n < N
    · have hn_le : n ≤ N := hn.le
      have hn1_le : n + 1 ≤ N := hn
      set tn : ℝ := (n : ℝ) * L
      have hL_nn : 0 ≤ L := hL₀_pos.le.trans hL_bounds.1
      have htn_nn : 0 ≤ tn := by dsimp [tn]; positivity
      have htn1_eq : ((n + 1 : ℕ) : ℝ) * L = tn + L := by
        dsimp [tn]
        push_cast
        ring
      have htnL_le : tn + L ≤ p.H := by
        rw [← htn1_eq, ← hNL]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn1_le) hL_nn
      obtain ⟨⟨ainv_pl, h_pl_l, h_pl_r, h_pl_norm⟩, h_pl_d, _, _⟩ :=
        hDich (p.ν * tn) (hσ_grid_mem n hn_le) L hL_bounds
      obtain ⟨h_err_a, h_err_d, h_err_b, h_err_c⟩ :=
        hDuh_op p d hbg hν_le_ν₁ hc_ge_c₀ hAge hMode hcloseM Sc U Ac hCD
          (fun s hs => ⟨(hAc s hs).2.1, (hAc s hs).2.2.1⟩)
          (fun s t hs hst htH => (hScU_bd s t hs hst htH).1)
          tn L htn_nn htnL_le hL_bounds
      set M_inv : ℝ := (1 / 4 : ℝ) * Real.exp (-b' * L)
      have hM_inv_pos : 0 < M_inv := by dsimp [M_inv]; positivity
      have hε_le_inv : ε ≤ (2 * M_inv)⁻¹ := by
        have h1 : ε ≤ Real.exp (-2 * b' * L₀) :=
          (min_le_right _ _).trans (min_le_left _ _)
        have h2 : Real.exp (-2 * b' * L₀) ≤ (2 * M_inv)⁻¹ := by
          dsimp [M_inv]
          have hb'_pos : 0 < b' := lt_trans ha' hab'
          have h_exp_le : Real.exp (-2 * b' * L₀) ≤ Real.exp (b' * L) :=
            Real.exp_le_exp.2 (by nlinarith [hL_bounds.1])
          have h_inv_eq : (2 * ((1 / 4 : ℝ) * Real.exp (-b' * L)))⁻¹ = 2 * Real.exp (b' * L) := by
            rw [← mul_assoc]
            norm_num
            rw [← Real.exp_neg, neg_neg, mul_comm]
          rw [h_inv_eq]
          linarith [Real.exp_pos (b' * L)]
        exact h1.trans h2
      obtain ⟨ainv_n, hainv_l, hainv_r, hainv_norm⟩ :=
        invertible_two_by_two_of_close hM_inv_pos h_pl_l h_pl_r h_pl_norm (h_err_a.trans hε_le_inv)
      have hainv_norm' : ‖ainv_n‖ ≤ (1 / 2 : ℝ) * Real.exp (-b' * L) := by
        dsimp [M_inv] at hainv_norm
        linarith
      have hε_le_d : ε ≤ (1 / 4 : ℝ) * Real.exp (a' * L) := by
        have h1 : ε ≤ (1 / 4 : ℝ) * Real.exp (a' * L₀) :=
          (min_le_right _ _).trans (min_le_right _ _)
        have h2 : Real.exp (a' * L₀) ≤ Real.exp (a' * L) :=
          Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hL_bounds.1 ha'.le)
        linarith
      have hε_le_η : ε ≤ η := min_le_left _ _
      have hd_bd :
          ‖(ContinuousLinearMap.id ℝ (Xmc p.c m) -
              (ι_c p.c (p.ν * (tn + L))).comp (π_c p.c (p.ν * (tn + L)))).comp
            ((U (tn + L) tn).comp
              (ContinuousLinearMap.id ℝ (Xmc p.c m) -
                (ι_c p.c (p.ν * tn)).comp (π_c p.c (p.ν * tn))))‖ ≤
            (1 / 2 : ℝ) * Real.exp (a' * L) := by
        linarith
      have hb_bd := h_err_b.trans hε_le_η
      have hc_bd := h_err_c.trans hε_le_η
      refine ⟨ainv_n, fun _ => ?_⟩
      dsimp only [ι_grid, π_grid, σ_grid]
      rw [htn1_eq]
      exact ⟨hainv_l, hainv_r, hainv_norm', hd_bd, hb_bd, hc_bd⟩
    · exact ⟨0, fun h => False.elim (hn h)⟩
  choose ainv hainv using hainv_ex
  let D : BlockFactorizationData m p U :=
    { N := N
      L := L
      F := PartIIbF2Splittings.kerSubmodule (π_grid 0)
      complete_F := inferInstance
      ι := ι_grid
      π := π_grid
      κ := PartIIbF2Splittings.buildKappa N ι_grid π_grid hπι_grid
      ρ := PartIIbF2Splittings.buildRho N ι_grid π_grid hπι_grid
      ainv := ainv }
  refine ⟨U, D, hCD.coupled_prop, ?_⟩
  refine
    { N_pos := hN_pos
      L_bounds := hL_bounds
      total_age := hNL
      entrance_eq := ?_
      zeroCirc_ι := fun n hn α => hPkg.cyl_zeroCirc p.c hc_ge_c₀ (σ_grid n) (hσ_grid_mem n hn) α
      proj_id_E := hπι_grid
      proj_id_F := fun n hn => PartIIbF2Splittings.build_proj_id_F hπι_grid hn
      proj_orth_EF := fun n hn => PartIIbF2Splittings.build_proj_orth_EF hπι_grid hn
      proj_orth_FE := fun n hn => PartIIbF2Splittings.build_proj_orth_FE hπι_grid hn
      decomp_id := fun n hn => PartIIbF2Splittings.build_decomp_id hπι_grid hn
      coord_norm := ?_
      short_prop_norm := ?_
      block_inv_left := ?_
      block_inv_right := ?_
      block_ainv_norm := ?_
      block_d_norm := ?_
      block_b_norm := ?_
      block_c_norm := ?_ }
  · intro α
    have hσ0 : σ_grid 0 = 0 := by
      dsimp [σ_grid]
      ring
    have hae := hPkg.cyl_direct_ae p.c hc_ge_c₀ 0 ⟨le_rfl, hSig.le⟩ α
    change (ι_c p.c (σ_grid 0) α : B0579.Plane → ℝ) =ᵐ[B0579.cellMeasure p.c m]
      entranceVorticityComb p α
    rw [hσ0]
    refine hae.trans (Eventually.of_forall fun x => ?_)
    unfold entranceVorticityComb entranceVorticity
    rw [hMode, add_zero]
  · intro n hn
    obtain ⟨hι_bd, hπ_bd⟩ := hPkg.cyl_norm p.c hc_ge_c₀ (σ_grid n) (hσ_grid_mem n hn)
    have hM1 : M_E ≤ M_coord := by
      refine le_trans ?_ (le_max_left _ _)
      nlinarith
    have hκ_bd :=
      (PartIIbF2Splittings.buildKappa_norm_le hπι_grid hn).trans hM_coord
    have hρ0 := PartIIbF2Splittings.buildRho_norm_le hπι_grid hn
    have hρ1 : 1 + ‖ι_grid n‖ * ‖π_grid n‖ ≤ M_coord := by
      calc 1 + ‖ι_grid n‖ * ‖π_grid n‖
          ≤ 1 + M_E * M_E :=
            add_le_add le_rfl (mul_le_mul hι_bd hπ_bd (norm_nonneg _) (by positivity))
        _ = 1 + M_E ^ 2 := by ring
        _ ≤ M_coord := le_max_left _ _
    exact ⟨hι_bd.trans hM1, hπ_bd.trans hM1, hκ_bd, hρ0.trans hρ1⟩
  · intro s t hs hst htH hts_le
    calc ‖U t s‖ ≤ Real.exp ((K₀ + M_A) * (t - s)) := (hScU_bd s t hs hst htH).2
      _ ≤ Real.exp ((K₀ + M_A) * (2 * L₀)) :=
          Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hts_le (by positivity))
      _ ≤ M_coord := le_max_right _ _
  · intro n hn
    exact (hainv n hn).1
  · intro n hn
    exact (hainv n hn).2.1
  · intro n hn
    exact (hainv n hn).2.2.1
  · intro n hn
    have h1 := PartIIbF2Splittings.norm_block_d_le hπι_grid hn (U (D.t (n + 1)) (D.t n))
    have h2 := (hainv n hn).2.2.2.1
    exact h1.trans h2
  · intro n hn
    have h1 := PartIIbF2Splittings.norm_block_b_le hπι_grid hn (U (D.t (n + 1)) (D.t n))
    have h2 := (hainv n hn).2.2.2.2.1
    exact h1.trans h2
  · intro n hn
    have h1 := PartIIbF2Splittings.norm_block_c_le hπι_grid hn (U (D.t (n + 1)) (D.t n))
    have h2 := (hainv n hn).2.2.2.2.2
    exact h1.trans h2

end UnforcedLeray.Short.IIb

end
