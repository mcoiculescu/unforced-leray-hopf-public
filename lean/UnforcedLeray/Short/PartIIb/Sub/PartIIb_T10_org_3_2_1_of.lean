import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_3_2_1_defs
import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedPotentialSourceCellL1
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_3_2_of
import UnforcedLeray.Short.PartIIa.Sub.F05
import UnforcedLeray.Lib.PhaseSpace.Leibniz

/-!
# `PartII-b:T10/org/3/2/1`: assembly of `LerayTestSchwartz`

Source of record `the November 2 reference manuscript`,
lines 119-120 (`𝔓 = ℙ`), 1364 (the projected inverse is the Cartesian Leray projection of the
datum), 1474-1475 (Leray commutes with heat, dilation and phase translation), 1498-1500
(representatives in `C(ℝ/Pℤ; L^r)`).

`lerayTestSchwartz_of` proves `LerayTestSchwartz` (`Sub/PartII-b_T10_org_3_2_of.lean`) with
`Ψ = LTS.lerayTest2 Φ` (`Sub/PartII-b_T10_org_3_2_1_defs.lean`), from the accepted
`PartIIa.SliceContOfDecay` and the four leaves of the defs file:

* far field: off the support of `Φ`, `lerayTest2 Φ = Σₖ ∂ₖψ_R eₖ + Σₖ ∂ₖψ_I (i eₖ)`; the first
  derivatives of the Newton potentials decay like `|y|⁻²` (`abs_newtonPair_le_of_far`), the second
  ones like `|y|⁻³` (`NewtonHessFar`), the third ones `∂ⱼ∂ⱼ∂ₖψ = ∂ⱼ∂ⱼ(N ∗ ∂ₖD)` like `|y|⁻³`, and
  `∂_τ∂ₖψ = ∂ₖ(N ∗ ∂_τ D)` like `|y|⁻²` (`NewtonJointFDeriv`), uniformly for phases in `[0, P]`
  (`exists_uniform_spatialL1_of_isPhaseTest`);
* `DecayOfFarBound` turns these into global bounds `C (1 + |y|)^{-n}` for `Ψ` (`n = 2`), `∂ⱼΨ`,
  `ΔΨ` (`n = 3`) and `T₀ᵗΨ = -∂_τΨ + ½ y·∇Ψ + 3/2 Ψ` (`n = 2`, using `|y| |∇Ψ| ≲ |y|⁻²`);
* `SliceContOfDecay` at `q = 2' = 2` (`2n > 3`) gives the slice continuity, so `Ψ` is a
  Schwartz-type `L²` phase test;
* the pairing identity is `PhasePairLerayY` and `testElem_lerayTest2`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIb.LTS

open UnforcedLeray.PhaseSpace UnforcedLeray.RieszLp UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PressureAnalysis

/-! ### Elementary bookkeeping -/

theorem lts_sum3_le {f : Fin 3 → ℝ} {B : ℝ} (h : ∀ k, f k ≤ B) : ∑ k, f k ≤ 3 * B := by
  calc ∑ k, f k ≤ ∑ _k : Fin 3, B := Finset.sum_le_sum fun k _ => h k
    _ = 3 * B := by simp

theorem lts_far_mul_le {a w I L C : ℝ} (ha : 0 ≤ a) (hw : 0 ≤ w) (hI : I ≤ L)
    (hC : a * L ≤ C) : a * w * I ≤ C * w :=
  calc a * w * I ≤ a * w * L := mul_le_mul_of_nonneg_left hI (mul_nonneg ha hw)
    _ = (a * L) * w := by ring
    _ ≤ C * w := mul_le_mul_of_nonneg_right hC hw

theorem lts_far_mul_le' {a w I L C : ℝ} (ha : 0 ≤ a) (hw : 0 ≤ w) (hI : I ≤ L)
    (hC : a * L ≤ C) : a * I * w ≤ C * w :=
  (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hI ha) hw).trans
    (mul_le_mul_of_nonneg_right hC hw)

theorem lts_norm_ofReV_coord (k : Fin 3) : ‖ofReV (coordinateVector k)‖ = 1 := by
  rw [show ofReV (coordinateVector k) = ofReVLin (coordinateVector k) from rfl, norm_ofReVLin,
    RieszLp.norm_coordinateVector]

theorem lts_norm_ofImV_coord (k : Fin 3) : ‖ofImV (coordinateVector k)‖ = 1 := by
  rw [show ofImV (coordinateVector k) = ofImVLin (coordinateVector k) from rfl, norm_ofImVLin,
    RieszLp.norm_coordinateVector]

theorem lts_norm_combo_le (x : CVec3) (c d : Fin 3 → ℝ) :
    ‖x + ∑ k, c k • ofReV (coordinateVector k) + ∑ k, d k • ofImV (coordinateVector k)‖ ≤
      ‖x‖ + ∑ k, |c k| + ∑ k, |d k| := by
  have hR : ‖∑ k, c k • ofReV (coordinateVector k)‖ ≤ ∑ k, |c k| := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
    rw [norm_smul, lts_norm_ofReV_coord, mul_one, Real.norm_eq_abs]
  have hI : ‖∑ k, d k • ofImV (coordinateVector k)‖ ≤ ∑ k, |d k| := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
    rw [norm_smul, lts_norm_ofImV_coord, mul_one, Real.norm_eq_abs]
  calc _ ≤ ‖x + ∑ k, c k • ofReV (coordinateVector k)‖ +
        ‖∑ k, d k • ofImV (coordinateVector k)‖ := norm_add_le _ _
    _ ≤ ‖x‖ + ‖∑ k, c k • ofReV (coordinateVector k)‖ +
        ‖∑ k, d k • ofImV (coordinateVector k)‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ‖x‖ + ∑ k, |c k| + ∑ k, |d k| := by gcongr

/-- Directional derivatives of `q ↦ Φ q + Σₖ gₖ(q) aₖ + Σₖ hₖ(q) bₖ`. -/
theorem lts_fderiv_combo {Φ : ℝ × Space → CVec3} {g h : Fin 3 → ℝ × Space → ℝ}
    (hΦ : Differentiable ℝ Φ) (hg : ∀ k, Differentiable ℝ (g k))
    (hh : ∀ k, Differentiable ℝ (h k)) (a b : Fin 3 → CVec3) (p v : ℝ × Space) :
    fderiv ℝ (fun q => Φ q + ∑ k, g k q • a k + ∑ k, h k q • b k) p v =
      fderiv ℝ Φ p v + ∑ k, fderiv ℝ (g k) p v • a k + ∑ k, fderiv ℝ (h k) p v • b k := by
  have hG : HasFDerivAt (fun q => ∑ k, g k q • a k)
      (∑ k, (fderiv ℝ (g k) p).smulRight (a k)) p :=
    HasFDerivAt.fun_sum fun k _ => ((hg k) p).hasFDerivAt.smul_const (a k)
  have hH : HasFDerivAt (fun q => ∑ k, h k q • b k)
      (∑ k, (fderiv ℝ (h k) p).smulRight (b k)) p :=
    HasFDerivAt.fun_sum fun k _ => ((hh k) p).hasFDerivAt.smul_const (b k)
  have hT := (((hΦ p).hasFDerivAt.fun_add hG).fun_add hH).fderiv
  rw [hT]
  simp

/-! ### Derivatives of `lerayTest2` -/

theorem dy_lerayTest2_apply {P : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) (j : Fin 3)
    (q : ℝ × Space) :
    dy j (lerayTest2 Φ) q = dy j Φ q +
      ∑ k : Fin 3, dy j (dy k (newtonJoint (projectedPotentialReDiv Φ))) q •
        ofReV (coordinateVector k) +
      ∑ k : Fin 3, dy j (dy k (newtonJoint (projectedPotentialImDiv Φ))) q •
        ofImV (coordinateVector k) := by
  have hR := contDiff_newtonJoint (isPhaseTest_projectedPotentialReDiv hΦ)
  have hI := contDiff_newtonJoint (isPhaseTest_projectedPotentialImDiv hΦ)
  exact lts_fderiv_combo (hΦ.smooth.differentiable (by simp))
    (fun k => (contDiff_dy_real hR k).differentiable (by simp))
    (fun k => (contDiff_dy_real hI k).differentiable (by simp))
    (fun k => ofReV (coordinateVector k)) (fun k => ofImV (coordinateVector k)) q
    (0, coordinateVector j)

theorem dτ_lerayTest2_apply {P : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    (q : ℝ × Space) :
    dτ (lerayTest2 Φ) q = dτ Φ q +
      ∑ k : Fin 3, dτ (dy k (newtonJoint (projectedPotentialReDiv Φ))) q •
        ofReV (coordinateVector k) +
      ∑ k : Fin 3, dτ (dy k (newtonJoint (projectedPotentialImDiv Φ))) q •
        ofImV (coordinateVector k) := by
  have hR := contDiff_newtonJoint (isPhaseTest_projectedPotentialReDiv hΦ)
  have hI := contDiff_newtonJoint (isPhaseTest_projectedPotentialImDiv hΦ)
  exact lts_fderiv_combo (hΦ.smooth.differentiable (by simp))
    (fun k => (contDiff_dy_real hR k).differentiable (by simp))
    (fun k => (contDiff_dy_real hI k).differentiable (by simp))
    (fun k => ofReV (coordinateVector k)) (fun k => ofImV (coordinateVector k)) q (1, 0)

theorem dy_dy_lerayTest2_apply {P : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    (j : Fin 3) (q : ℝ × Space) :
    dy j (dy j (lerayTest2 Φ)) q = dy j (dy j Φ) q +
      ∑ k : Fin 3, dy j (dy j (dy k (newtonJoint (projectedPotentialReDiv Φ)))) q •
        ofReV (coordinateVector k) +
      ∑ k : Fin 3, dy j (dy j (dy k (newtonJoint (projectedPotentialImDiv Φ)))) q •
        ofImV (coordinateVector k) := by
  have hR := contDiff_newtonJoint (isPhaseTest_projectedPotentialReDiv hΦ)
  have hI := contDiff_newtonJoint (isPhaseTest_projectedPotentialImDiv hΦ)
  have he : dy j (lerayTest2 Φ) = fun q => dy j Φ q +
      ∑ k : Fin 3, dy j (dy k (newtonJoint (projectedPotentialReDiv Φ))) q •
        ofReV (coordinateVector k) +
      ∑ k : Fin 3, dy j (dy k (newtonJoint (projectedPotentialImDiv Φ))) q •
        ofImV (coordinateVector k) := funext (dy_lerayTest2_apply hΦ j)
  rw [he]
  exact lts_fderiv_combo ((contDiff_dy hΦ.smooth j).differentiable (by simp))
    (fun k => (contDiff_dy_real (contDiff_dy_real hR k) j).differentiable (by simp))
    (fun k => (contDiff_dy_real (contDiff_dy_real hI k) j).differentiable (by simp))
    (fun k => ofReV (coordinateVector k)) (fun k => ofImV (coordinateVector k)) q
    (0, coordinateVector j)

/-! ### Far-field bounds -/

/-- First derivatives of the Newton potential of a compact test, far out. -/
theorem lts_newton_first_far {f : Space → ℝ} (hf : IsSpatialTest f) {ρ : ℝ}
    (hsupp : ∀ x, ρ < ‖x‖ → f x = 0) {y : Space} (hy : 2 * ρ ≤ ‖y‖) (hy0 : y ≠ 0)
    (k : Fin 3) :
    |spatialTestDerivative k (newtonConv f) y| ≤ Real.pi⁻¹ * (‖y‖ ^ 2)⁻¹ * ∫ x, |f x| := by
  rw [spatialTestDerivative_newtonConv hf k, newtonConv_partial hf k y, abs_neg]
  exact abs_newtonPair_le_of_far k hf.integrable hsupp hy hy0

theorem lts_dy_newtonJoint_comm (h2 : NewtonJointFDeriv) {P : ℝ} {D : ℝ × Space → ℝ}
    (hD : IsPhaseTest P D) (k : Fin 3) : dy k (newtonJoint D) = newtonJoint (dy k D) :=
  funext fun p => h2 P D hD p (0, coordinateVector k)

theorem lts_dτ_newtonJoint_comm (h2 : NewtonJointFDeriv) {P : ℝ} {D : ℝ × Space → ℝ}
    (hD : IsPhaseTest P D) : dτ (newtonJoint D) = newtonJoint (dτ D) :=
  funext fun p => h2 P D hD p (1, 0)

/-- Far-field bounds, uniform for phases in `[0, P]`, for the derivatives of the joint Newton
potential of a scalar phase test that enter `lerayTest2` and its derivatives. -/
theorem lts_scalar_far (h2 : NewtonJointFDeriv) (h3 : NewtonHessFar) {P : ℝ} [Fact (0 < P)]
    {D : ℝ × Space → ℝ} (hD : IsPhaseTest P D) :
    ∃ ρ C : ℝ, 1 ≤ ρ ∧ 0 ≤ C ∧ ∀ τ ∈ Icc (0 : ℝ) P, ∀ y : Space, ρ ≤ ‖y‖ →
      (∀ k, |dy k (newtonJoint D) (τ, y)| ≤ C * (‖y‖ ^ 2)⁻¹) ∧
      (∀ j k, |dy j (dy k (newtonJoint D)) (τ, y)| ≤ C * (‖y‖ ^ 3)⁻¹) ∧
      (∀ j k, |dy j (dy j (dy k (newtonJoint D))) (τ, y)| ≤ C * (‖y‖ ^ 3)⁻¹) ∧
      (∀ k, |dτ (dy k (newtonJoint D)) (τ, y)| ≤ C * (‖y‖ ^ 2)⁻¹) := by
  obtain ⟨R, hR⟩ := hD.bounded_support
  have hρ0n : 0 ≤ max R 0 := le_max_right _ _
  have hsD : ∀ τ x, max R 0 < ‖x‖ → D (τ, x) = 0 := fun τ x hx =>
    hR τ x (lt_of_le_of_lt (le_max_left _ _) hx)
  have hsdy : ∀ (k : Fin 3) τ x, max R 0 < ‖x‖ → dy k D (τ, x) = 0 := by
    intro k τ x hx
    show fderiv ℝ D (τ, x) (0, coordinateVector k) = 0
    rw [fderiv_eq_zero_of_far hR (lt_of_le_of_lt (le_max_left _ _) hx)]
    simp
  have hsdτ : ∀ τ x, max R 0 < ‖x‖ → dτ D (τ, x) = 0 := by
    intro τ x hx
    show fderiv ℝ D (τ, x) (1, 0) = 0
    rw [fderiv_eq_zero_of_far hR (lt_of_le_of_lt (le_max_left _ _) hx)]
    simp
  obtain ⟨L0, hL0n, hL0⟩ := exists_uniform_spatialL1_of_isPhaseTest hD
  choose Lk hLkn hLk using fun k : Fin 3 => exists_uniform_spatialL1_of_isPhaseTest (hD.dy k)
  obtain ⟨Lt, hLtn, hLt⟩ := exists_uniform_spatialL1_of_isPhaseTest hD.dτ
  have hsum : 0 ≤ ∑ k : Fin 3, Lk k := Finset.sum_nonneg fun k _ => hLkn k
  have hLkS : ∀ k, Lk k ≤ ∑ k : Fin 3, Lk k := fun k =>
    Finset.single_le_sum (f := Lk) (fun i _ => hLkn i) (Finset.mem_univ k)
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = L0 + ∑ k : Fin 3, Lk k + Lt := ⟨_, rfl⟩
  have hSn : 0 ≤ S := by rw [hS]; linarith
  have hL0S : L0 ≤ S := by rw [hS]; linarith
  have hLtS : Lt ≤ S := by rw [hS]; linarith
  have hLkS' : ∀ k, Lk k ≤ S := fun k => by rw [hS]; linarith [hLkS k]
  have hπ : 0 ≤ Real.pi⁻¹ := inv_nonneg.2 Real.pi_pos.le
  have hπ8 : 0 ≤ 8 * Real.pi⁻¹ := mul_nonneg (by norm_num) hπ
  have hC1 : Real.pi⁻¹ * S ≤ 8 * Real.pi⁻¹ * S := by
    have := mul_nonneg hπ hSn
    linarith
  refine ⟨2 * max R 0 + 1, 8 * Real.pi⁻¹ * S, by linarith, mul_nonneg hπ8 hSn, ?_⟩
  intro τ hτ y hy
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, norm_zero] at hy
    linarith
  have hy2 : 2 * max R 0 ≤ ‖y‖ := by linarith
  have hw2 : 0 ≤ (‖y‖ ^ 2)⁻¹ := by positivity
  have hw3 : 0 ≤ (‖y‖ ^ 3)⁻¹ := by positivity
  refine ⟨fun k => ?_, fun j k => ?_, fun j k => ?_, fun k => ?_⟩
  · rw [dy_newtonJoint_eq hD k τ y]
    exact (lts_newton_first_far (isSpatialTest_slice hD τ) (hsD τ) hy2 hy0 k).trans
      (lts_far_mul_le hπ hw2 ((hL0 τ hτ).trans hL0S) hC1)
  · rw [dy_dy_newtonJoint_eq hD j k τ y]
    exact (h3 _ (isSpatialTest_slice hD τ) (max R 0) hρ0n (hsD τ) j k y hy).trans
      (lts_far_mul_le' hπ8 hw3 ((hL0 τ hτ).trans hL0S) le_rfl)
  · rw [lts_dy_newtonJoint_comm h2 hD k, dy_dy_newtonJoint_eq (hD.dy k) j j τ y]
    exact (h3 _ (isSpatialTest_slice (hD.dy k) τ) (max R 0) hρ0n (hsdy k τ) j j y hy).trans
      (lts_far_mul_le' hπ8 hw3 ((hLk k τ hτ).trans (hLkS' k)) le_rfl)
  · rw [dτ_dy_comm_real (contDiff_newtonJoint hD) k, lts_dτ_newtonJoint_comm h2 hD,
      dy_newtonJoint_eq hD.dτ k τ y]
    exact (lts_newton_first_far (isSpatialTest_slice hD.dτ τ) (hsdτ τ) hy2 hy0 k).trans
      (lts_far_mul_le hπ hw2 ((hLt τ hτ).trans hLtS) hC1)

/-- Far-field bounds, uniform for phases in `[0, P]`, for `lerayTest2 Φ`, `∂ⱼ`, `Δ` and `∂_τ` of
it. -/
theorem lts_vector_far (h2 : NewtonJointFDeriv) (h3 : NewtonHessFar) {P : ℝ} [Fact (0 < P)]
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) :
    ∃ ρ C : ℝ, 1 ≤ ρ ∧ 0 ≤ C ∧ ∀ τ ∈ Icc (0 : ℝ) P, ∀ y : Space, ρ ≤ ‖y‖ →
      ‖lerayTest2 Φ (τ, y)‖ ≤ C * (‖y‖ ^ 2)⁻¹ ∧
      (∀ j, ‖dy j (lerayTest2 Φ) (τ, y)‖ ≤ C * (‖y‖ ^ 3)⁻¹) ∧
      ‖lapT (lerayTest2 Φ) (τ, y)‖ ≤ C * (‖y‖ ^ 3)⁻¹ ∧
      ‖dτ (lerayTest2 Φ) (τ, y)‖ ≤ C * (‖y‖ ^ 2)⁻¹ := by
  obtain ⟨ρR, CR, hρR, hCR, hR⟩ := lts_scalar_far h2 h3 (isPhaseTest_projectedPotentialReDiv hΦ)
  obtain ⟨ρI, CI, hρI, hCI, hI⟩ := lts_scalar_far h2 h3 (isPhaseTest_projectedPotentialImDiv hΦ)
  obtain ⟨RΦ, hRΦ⟩ := hΦ.bounded_support
  have hdyΦ : ∀ (j : Fin 3) τ y, RΦ < ‖y‖ → dy j Φ (τ, y) = 0 := by
    intro j τ y hy
    show fderiv ℝ Φ (τ, y) (0, coordinateVector j) = 0
    rw [fderiv_eq_zero_of_far hRΦ hy]
    simp
  have hdτΦ : ∀ τ y, RΦ < ‖y‖ → dτ Φ (τ, y) = 0 := by
    intro τ y hy
    show fderiv ℝ Φ (τ, y) (1, 0) = 0
    rw [fderiv_eq_zero_of_far hRΦ hy]
    simp
  have hdyyΦ : ∀ (j : Fin 3) τ y, RΦ < ‖y‖ → dy j (dy j Φ) (τ, y) = 0 := by
    intro j τ y hy
    show fderiv ℝ (dy j Φ) (τ, y) (0, coordinateVector j) = 0
    rw [fderiv_eq_zero_of_far (hdyΦ j) hy]
    simp
  have hCRI : 0 ≤ CR + CI := add_nonneg hCR hCI
  refine ⟨max (max ρR ρI) (|RΦ| + 1), 9 * (CR + CI),
    le_trans hρR (le_trans (le_max_left _ _) (le_max_left _ _)),
    mul_nonneg (by norm_num) hCRI, ?_⟩
  intro τ hτ y hy
  have hyR : ρR ≤ ‖y‖ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
  have hyI : ρI ≤ ‖y‖ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hy
  have hyΦ : RΦ < ‖y‖ := by
    have h1 : |RΦ| + 1 ≤ ‖y‖ := le_trans (le_max_right _ _) hy
    linarith [le_abs_self RΦ]
  obtain ⟨hR1, hR2, hR3, hR4⟩ := hR τ hτ y hyR
  obtain ⟨hI1, hI2, hI3, hI4⟩ := hI τ hτ y hyI
  have hw2 : 0 ≤ (‖y‖ ^ 2)⁻¹ := by positivity
  have hw3 : 0 ≤ (‖y‖ ^ 3)⁻¹ := by positivity
  have hm2 : 0 ≤ (CR + CI) * (‖y‖ ^ 2)⁻¹ := mul_nonneg hCRI hw2
  have hm3 : 0 ≤ (CR + CI) * (‖y‖ ^ 3)⁻¹ := mul_nonneg hCRI hw3
  refine ⟨?_, fun j => ?_, ?_, ?_⟩
  · have hb := lts_norm_combo_le (Φ (τ, y))
      (fun k => dy k (newtonJoint (projectedPotentialReDiv Φ)) (τ, y))
      (fun k => dy k (newtonJoint (projectedPotentialImDiv Φ)) (τ, y))
    beta_reduce at hb
    have hs1 : ∑ k : Fin 3, |dy k (newtonJoint (projectedPotentialReDiv Φ)) (τ, y)| ≤
        3 * (CR * (‖y‖ ^ 2)⁻¹) := lts_sum3_le fun k => hR1 k
    have hs2 : ∑ k : Fin 3, |dy k (newtonJoint (projectedPotentialImDiv Φ)) (τ, y)| ≤
        3 * (CI * (‖y‖ ^ 2)⁻¹) := lts_sum3_le fun k => hI1 k
    rw [hRΦ τ y hyΦ, norm_zero] at hb
    have he : lerayTest2 Φ (τ, y) = Φ (τ, y) +
        ∑ k : Fin 3, dy k (newtonJoint (projectedPotentialReDiv Φ)) (τ, y) •
          ofReV (coordinateVector k) +
        ∑ k : Fin 3, dy k (newtonJoint (projectedPotentialImDiv Φ)) (τ, y) •
          ofImV (coordinateVector k) := rfl
    rw [he, hRΦ τ y hyΦ]
    linarith
  · rw [dy_lerayTest2_apply hΦ j (τ, y)]
    have hb := lts_norm_combo_le (dy j Φ (τ, y))
      (fun k => dy j (dy k (newtonJoint (projectedPotentialReDiv Φ))) (τ, y))
      (fun k => dy j (dy k (newtonJoint (projectedPotentialImDiv Φ))) (τ, y))
    beta_reduce at hb
    have hs1 : ∑ k : Fin 3, |dy j (dy k (newtonJoint (projectedPotentialReDiv Φ))) (τ, y)| ≤
        3 * (CR * (‖y‖ ^ 3)⁻¹) := lts_sum3_le fun k => hR2 j k
    have hs2 : ∑ k : Fin 3, |dy j (dy k (newtonJoint (projectedPotentialImDiv Φ))) (τ, y)| ≤
        3 * (CI * (‖y‖ ^ 3)⁻¹) := lts_sum3_le fun k => hI2 j k
    rw [hdyΦ j τ y hyΦ, norm_zero] at hb
    rw [hdyΦ j τ y hyΦ]
    linarith
  · have hl : lapT (lerayTest2 Φ) (τ, y) = ∑ j : Fin 3, dy j (dy j (lerayTest2 Φ)) (τ, y) := rfl
    have hj : ∀ j : Fin 3, ‖dy j (dy j (lerayTest2 Φ)) (τ, y)‖ ≤
        3 * ((CR + CI) * (‖y‖ ^ 3)⁻¹) := by
      intro j
      rw [dy_dy_lerayTest2_apply hΦ j (τ, y)]
      have hb := lts_norm_combo_le (dy j (dy j Φ) (τ, y))
        (fun k => dy j (dy j (dy k (newtonJoint (projectedPotentialReDiv Φ)))) (τ, y))
        (fun k => dy j (dy j (dy k (newtonJoint (projectedPotentialImDiv Φ)))) (τ, y))
      beta_reduce at hb
      have hs1 : ∑ k : Fin 3,
          |dy j (dy j (dy k (newtonJoint (projectedPotentialReDiv Φ)))) (τ, y)| ≤
          3 * (CR * (‖y‖ ^ 3)⁻¹) := lts_sum3_le fun k => hR3 j k
      have hs2 : ∑ k : Fin 3,
          |dy j (dy j (dy k (newtonJoint (projectedPotentialImDiv Φ)))) (τ, y)| ≤
          3 * (CI * (‖y‖ ^ 3)⁻¹) := lts_sum3_le fun k => hI3 j k
      rw [hdyyΦ j τ y hyΦ, norm_zero] at hb
      rw [hdyyΦ j τ y hyΦ]
      linarith
    rw [hl]
    calc ‖∑ j : Fin 3, dy j (dy j (lerayTest2 Φ)) (τ, y)‖
        ≤ ∑ j : Fin 3, ‖dy j (dy j (lerayTest2 Φ)) (τ, y)‖ := norm_sum_le _ _
      _ ≤ 3 * (3 * ((CR + CI) * (‖y‖ ^ 3)⁻¹)) := lts_sum3_le hj
      _ = 9 * (CR + CI) * (‖y‖ ^ 3)⁻¹ := by ring
  · rw [dτ_lerayTest2_apply hΦ (τ, y)]
    have hb := lts_norm_combo_le (dτ Φ (τ, y))
      (fun k => dτ (dy k (newtonJoint (projectedPotentialReDiv Φ))) (τ, y))
      (fun k => dτ (dy k (newtonJoint (projectedPotentialImDiv Φ))) (τ, y))
    beta_reduce at hb
    have hs1 : ∑ k : Fin 3, |dτ (dy k (newtonJoint (projectedPotentialReDiv Φ))) (τ, y)| ≤
        3 * (CR * (‖y‖ ^ 2)⁻¹) := lts_sum3_le fun k => hR4 k
    have hs2 : ∑ k : Fin 3, |dτ (dy k (newtonJoint (projectedPotentialImDiv Φ))) (τ, y)| ≤
        3 * (CI * (‖y‖ ^ 2)⁻¹) := lts_sum3_le fun k => hI4 k
    rw [hdτΦ τ y hyΦ, norm_zero] at hb
    rw [hdτΦ τ y hyΦ]
    linarith

/-- The far-field bound for `T₀ᵗ(lerayTest2 Φ) = -∂_τΨ + ½ y·∇Ψ + 3/2 Ψ` from those of `Ψ`,
`∂ⱼΨ` and `∂_τΨ`: `|y| |∂ⱼΨ| ≤ C |y|⁻²`. -/
theorem lts_driftT_far {Ψ : ℝ × Space → CVec3} {C : ℝ} {τ : ℝ} {y : Space} (hy : 0 < ‖y‖)
    (h0 : ‖Ψ (τ, y)‖ ≤ C * (‖y‖ ^ 2)⁻¹) (h1 : ∀ j, ‖dy j Ψ (τ, y)‖ ≤ C * (‖y‖ ^ 3)⁻¹)
    (h3 : ‖dτ Ψ (τ, y)‖ ≤ C * (‖y‖ ^ 2)⁻¹) :
    ‖driftT Ψ (τ, y)‖ ≤ (4 * C) * (‖y‖ ^ 2)⁻¹ := by
  have hrad : ‖radialT Ψ (τ, y)‖ ≤ 3 * C * (‖y‖ ^ 2)⁻¹ := by
    have hs : ‖radialT Ψ (τ, y)‖ ≤ ∑ _j : Fin 3, ‖y‖ * (C * (‖y‖ ^ 3)⁻¹) := by
      show ‖∑ j : Fin 3, (y j) • dy j Ψ (τ, y)‖ ≤ _
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_smul]
      exact mul_le_mul (PiLp.norm_apply_le y j) (h1 j) (norm_nonneg _) (norm_nonneg _)
    have he : ∑ _j : Fin 3, ‖y‖ * (C * (‖y‖ ^ 3)⁻¹) = 3 * C * (‖y‖ ^ 2)⁻¹ := by
      have hy' : ‖y‖ ≠ 0 := hy.ne'
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_ofNat]
      field_simp
    linarith
  have hsplit : ‖driftT Ψ (τ, y)‖ ≤ ‖dτ Ψ (τ, y)‖ + (1 / 2 : ℝ) * ‖radialT Ψ (τ, y)‖ +
      (3 / 2 : ℝ) * ‖Ψ (τ, y)‖ := by
    have e : driftT Ψ (τ, y) = -dτ Ψ (τ, y) + (1 / 2 : ℝ) • radialT Ψ (τ, y) +
        (3 / 2 : ℝ) • Ψ (τ, y) := rfl
    rw [e]
    calc ‖-dτ Ψ (τ, y) + (1 / 2 : ℝ) • radialT Ψ (τ, y) + (3 / 2 : ℝ) • Ψ (τ, y)‖
        ≤ ‖-dτ Ψ (τ, y) + (1 / 2 : ℝ) • radialT Ψ (τ, y)‖ + ‖(3 / 2 : ℝ) • Ψ (τ, y)‖ :=
          norm_add_le _ _
      _ ≤ ‖-dτ Ψ (τ, y)‖ + ‖(1 / 2 : ℝ) • radialT Ψ (τ, y)‖ + ‖(3 / 2 : ℝ) • Ψ (τ, y)‖ := by
          gcongr
          exact norm_add_le _ _
      _ = ‖dτ Ψ (τ, y)‖ + (1 / 2 : ℝ) * ‖radialT Ψ (τ, y)‖ + (3 / 2 : ℝ) * ‖Ψ (τ, y)‖ := by
          rw [norm_neg, norm_smul, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
            Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2)]
  linarith

end UnforcedLeray.Short.IIb.LTS

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.RieszLp UnforcedLeray.Cons.C03.Concrete

/-- **`LerayTestSchwartz` from the leaves** (source lines 119-120, 1364, 1474-1475, 1498-1500):
`Ψ = LTS.lerayTest2 Φ`, the smooth slice-wise Cartesian Leray projection of the phase test `Φ`,
is a Schwartz-type `L²` phase test with `⟪Φ, ℙf⟫ = ⟪Ψ, f⟫` for every `f ∈ Y_2`. -/
theorem lerayTestSchwartz_of (h0 : PartIIa.SliceContOfDecay) (h1 : LTS.DecayOfFarBound)
    (h2 : LTS.NewtonJointFDeriv) (h3 : LTS.NewtonHessFar) (h4 : LTS.PhasePairLerayY) :
    LerayTestSchwartz := by
  intro P _ Φ hΦ
  have hP : 0 < P := Fact.out
  have hΨs : ContDiff ℝ ∞ (LTS.lerayTest2 Φ) := LTS.contDiff_lerayTest2 hΦ
  have hΨp : ∀ τ y, LTS.lerayTest2 Φ (τ + P, y) = LTS.lerayTest2 Φ (τ, y) :=
    LTS.lerayTest2_periodic hΦ
  obtain ⟨ρ, C, hρ, hC, hfar⟩ := LTS.lts_vector_far h2 h3 hΦ
  have hρ0 : 0 < ρ := by linarith
  obtain ⟨C0, hC0⟩ := h1 P hP 2 (LTS.lerayTest2 Φ) hΨs.continuous hΨp ρ C hρ0
    fun τ hτ y hy => (hfar τ hτ y hy).1
  choose Cd hCd using fun j : Fin 3 => h1 P hP 3 (dy j (LTS.lerayTest2 Φ))
    (contDiff_dy hΨs j).continuous (periodic_dy hΨp j) ρ C hρ0
    fun τ hτ y hy => (hfar τ hτ y hy).2.1 j
  obtain ⟨Cl, hCl⟩ := h1 P hP 3 (lapT (LTS.lerayTest2 Φ)) (contDiff_lapT hΨs).continuous
    (periodic_lapT hΨp) ρ C hρ0 fun τ hτ y hy => (hfar τ hτ y hy).2.2.1
  have hcont : Continuous (driftT (LTS.lerayTest2 Φ)) := by
    have hτc := (contDiff_dτ hΨs).continuous
    have hrc := (contDiff_radialT hΨs).continuous
    exact (hτc.neg.add (hrc.const_smul (1 / 2 : ℝ))).add (hΨs.continuous.const_smul (3 / 2 : ℝ))
  obtain ⟨Ct, hCt⟩ := h1 P hP 2 (driftT (LTS.lerayTest2 Φ)) hcont (periodic_driftT hΨp) ρ
    (4 * C) hρ0 fun τ hτ y hy => by
      obtain ⟨hf0, hf1, -, hf3⟩ := hfar τ hτ y hy
      exact LTS.lts_driftT_far (by linarith) hf0 hf1 hf3
  have hsl : ∀ (n : ℕ) (G : ℝ × Space → CVec3) (K : ℝ), 2 ≤ n → Continuous G →
      (∀ τ y, ‖G (τ, y)‖ ≤ K * (1 + ‖y‖) ^ (-(n : ℝ))) → SliceCont (conjExp 2) G := by
    intro n G K hn hG hb
    refine h0 (conjExp 2) LTS.conjExp_two_ne_top (n : ℝ) K ?_ G hG hb
    rw [LTS.toReal_conjExp_two]
    have h2n : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hS : IsPhaseSchwartz P (conjExp 2) (LTS.lerayTest2 Φ) :=
    ⟨hΨs, hΨp, hsl 2 _ C0 le_rfl hΨs.continuous hC0,
      fun j => hsl 3 _ (Cd j) (by norm_num) (contDiff_dy hΨs j).continuous (hCd j),
      hsl 3 _ Cl (by norm_num) (contDiff_lapT hΨs).continuous hCl,
      hsl 2 _ Ct le_rfl hcont hCt⟩
  refine ⟨LTS.lerayTest2 Φ, hS, fun f => ?_⟩
  rw [h4 P Φ (hΦ.isSliceTest (conjExp 2)) f]
  exact congrArg (fun T => phasePairing P 2 T f) (LTS.testElem_lerayTest2 hΦ hS.sliceTest).symm

#print axioms lerayTestSchwartz_of

end UnforcedLeray.Short.IIb
