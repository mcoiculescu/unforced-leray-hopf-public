import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_2.Statements
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1
import UnforcedLeray.Short.PartIIb.Tasks.OrdRelUnique.Complexify
import UnforcedLeray.Lib.PhaseSpace.CutoffCalc
import UnforcedLeray.Lib.AxisymmetricB.Bridge
import UnforcedLeray.Units.B0411

/-!
# `PartIII-b:C/ward/12/3/1/2/8/2/1/2`: `L0TSolApprox` from the leaf statements

Source `the November 2 reference manuscript`
lines 119-120, 1356-1366, 1446-1455, 1464-1466 (see `Statements.lean`).

Proved here (no further hypotheses):
* `projSmooth_eq_curlRepC`: from `NewtonCurlRepSliceAE`, `projSmooth Φ = curlRepC Φ` (both are
  continuous and a.e. equal on every phase slice to `projTest P Φ`, `projSmooth_slice_ae`);
* `L0T_add_csmul`: `L₀ᵗ(A + c B) = L₀ᵗA + c L₀ᵗB` for smooth `A, B`, `c ∈ ℂ`;
* `curlCutoffL0TErrorBound_of`: `NewtonCurlSliceDecay`, `NewtonCurlTimeComm`, `CurlCutoffL0TCalc`
  give `CurlCutoffL0TErrorBound`;
* `l0TSolApprox_of`: `NewtonCurlRepSliceAE`, `CurlCutoffL0TErrorBound`,
  `UniformCutoffLimitSliceTest`, `UniformCutoffLimitPairing` give `L0TSolApprox`;
* `newtonCurlSliceDecayFar_of`: `(2)`, `(3)` give `(4)`;
* `curlCutoffL0TCalc_of`: `(8)`-`(13)` give `(14)`;
* `l0TSolApprox_of_leaves`, `l0TSolApprox_of_fine`: the composites.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.SolApprox

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.B0412 UnforcedLeray.RieszLp
open UnforcedLeray.Cons.C03.Concrete
open NavierStokesR3.ComparisonCutoffs

/-! ### Smoothness and identification of the limit -/

theorem realC_eq_cplxV : (realC : Space → CVec3) = ⇑UnforcedLeray.Axi.cplxV := by
  funext x
  ext i
  simp [realC_apply, UnforcedLeray.Axi.cplxV_apply]

theorem contDiff_newtonCurl {P : ℝ} {φ : ℝ × Space → Space} (hφ : IsPhaseTest P φ) :
    ContDiff ℝ ∞ (projectedTestNewtonVectorPotentialCurl φ) :=
  contDiff_spatialCurlST_of_contDiff (contDiff_projectedTestNewtonVectorPotential hφ)

theorem contDiff_curlRepR {P : ℝ} {φ : ℝ × Space → Space} (hφ : IsPhaseTest P φ) :
    ContDiff ℝ ∞ (curlRepR φ) := by
  have hC := contDiff_spatialCurlST_of_contDiff (contDiff_newtonCurl hφ)
  unfold curlRepR
  rw [realC_eq_cplxV]
  exact UnforcedLeray.Axi.cplxV.contDiff.comp hC

theorem contDiff_curlRepC {P : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) :
    ContDiff ℝ ∞ (curlRepC Φ) :=
  (contDiff_curlRepR (hΦ.clm_comp reV)).add
    ((contDiff_curlRepR (hΦ.clm_comp imV)).const_smul Complex.I)

/-- `projSmooth Φ` is the Newton-curl representative `curlRepC Φ`. -/
theorem projSmooth_eq_curlRepC (hAE : NewtonCurlRepSliceAE) {P : ℝ} [Fact (0 < P)]
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) : projSmooth Φ = curlRepC Φ := by
  funext z
  obtain ⟨τ, y⟩ := z
  have hin : Continuous (fun x : Space => ((τ, x) : ℝ × Space)) :=
    continuous_const.prodMk continuous_id
  have hc1 : Continuous (fun x : Space => projSmooth Φ (τ, x)) :=
    (contDiff_projSmooth hΦ).continuous.comp hin
  have hc2 : Continuous (fun x : Space => curlRepC Φ (τ, x)) :=
    (contDiff_curlRepC hΦ).continuous.comp hin
  have hae : (fun x : Space => projSmooth Φ (τ, x)) =ᵐ[volume]
      fun x : Space => curlRepC Φ (τ, x) :=
    (projSmooth_slice_ae hΦ τ).symm.trans (hAE P Φ hΦ τ).symm
  exact congrFun ((Continuous.ae_eq_iff_eq volume hc1 hc2).1 hae) y

/-! ### Linearity of `L₀ᵗ` on smooth fields -/

section Lin

variable {A B : ℝ × Space → CVec3}

theorem dτ_add' (hA : Differentiable ℝ A) (hB : Differentiable ℝ B) :
    dτ (A + B) = dτ A + dτ B := by
  funext p
  simp [dτ, fderiv_add (hA p) (hB p)]

theorem dτ_csmul (hB : Differentiable ℝ B) (c : ℂ) : dτ (c • B) = c • dτ B := by
  funext p
  simp [dτ, fderiv_const_smul (hB p) c]

theorem dy_csmul (hB : Differentiable ℝ B) (c : ℂ) (j : Fin 3) :
    dy j (c • B) = c • dy j B := by
  funext p
  simp [dy, fderiv_const_smul (hB p) c]

theorem L0T_add_csmul (ν : ℝ) (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) (c : ℂ) :
    L0T ν (A + c • B) = L0T ν A + c • L0T ν B := by
  have dA : Differentiable ℝ A := hA.differentiable (by simp)
  have dB : Differentiable ℝ B := hB.differentiable (by simp)
  have dcB : Differentiable ℝ (c • B) := fun p => (dB p).const_smul c
  have dyA : ∀ j, Differentiable ℝ (dy j A) := fun j =>
    (contDiff_dy hA j).differentiable (by simp)
  have dyB : ∀ j, Differentiable ℝ (dy j B) := fun j =>
    (contDiff_dy hB j).differentiable (by simp)
  have hdy1 : ∀ j, dy j (A + c • B) = dy j A + c • dy j B := fun j => by
    rw [dy_add dA dcB j, dy_csmul dB c j]
  have hdy2 : ∀ j, dy j (dy j (A + c • B)) = dy j (dy j A) + c • dy j (dy j B) := fun j => by
    rw [hdy1 j, dy_add (dyA j) (fun p => (dyB j p).const_smul c) j, dy_csmul (dyB j) c j]
  have hτ : dτ (A + c • B) = dτ A + c • dτ B := by
    rw [dτ_add' dA dcB, dτ_csmul dB c]
  have hrad : radialT (A + c • B) = radialT A + c • radialT B := by
    funext p
    simp only [radialT, hdy1, Pi.add_apply, Pi.smul_apply, smul_add, Finset.sum_add_distrib,
      Finset.smul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _
  have hlap : lapT (A + c • B) = lapT A + c • lapT B := by
    funext p
    simp only [lapT, hdy2, Pi.add_apply, Pi.smul_apply, Finset.sum_add_distrib, Finset.smul_sum]
  funext p
  simp only [L0T, nuLapT, driftT, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, hτ, hrad, hlap]
  module

end Lin

/-! ### The error bound for the Newton curl potential -/

theorem curlCutoffL0TErrorBound_of (hD : NewtonCurlSliceDecay) (hT : NewtonCurlTimeComm)
    (hC : CurlCutoffL0TCalc) : CurlCutoffL0TErrorBound := by
  intro P _ φ hφ
  obtain ⟨K, hK, hcalc⟩ := hC
  obtain ⟨M₁, hM₁, h₁⟩ := hD P φ hφ
  obtain ⟨M₂, hM₂, h₂⟩ := hD P (dτ φ) hφ.dτ
  have hM : 0 ≤ M₁ + M₂ := add_nonneg hM₁ hM₂
  refine ⟨K * (M₁ + M₂), mul_nonneg hK hM, fun ν hν R hR τ y => ?_⟩
  have hb1 : ∀ (τ : ℝ) (y : Space) (k : ℕ), k ≤ 3 →
      ‖iteratedFDeriv ℝ k (fun x => projectedTestNewtonVectorPotentialCurl φ (τ, x)) y‖ ≤
        (M₁ + M₂) * powWeight ((k : ℝ) + 1) y := fun τ y k hk =>
    (h₁ τ y k hk).trans (mul_le_mul_of_nonneg_right (by linarith) (powWeight_nonneg _ _))
  have hb2 : ∀ (τ : ℝ) (y : Space) (k : ℕ), k ≤ 1 →
      ‖iteratedFDeriv ℝ k (fun x => dτ (projectedTestNewtonVectorPotentialCurl φ) (τ, x)) y‖ ≤
        (M₁ + M₂) * powWeight ((k : ℝ) + 1) y := by
    intro τ y k hk
    rw [hT P φ hφ]
    exact (h₂ τ y k (by omega)).trans
      (mul_le_mul_of_nonneg_right (by linarith) (powWeight_nonneg _ _))
  have h := hcalc _ (contDiff_newtonCurl hφ) (M₁ + M₂) hM hb1 hb2 ν hν R hR τ y
  calc _ ≤ K * (1 + ν) * (M₁ + M₂) * ((1 - cutoff (R / 2) y) * powWeight 2 y) := h
    _ = K * (M₁ + M₂) * (1 + ν) * ((1 - cutoff (R / 2) y) * powWeight 2 y) := by ring

/-! ### Assemblies of the decay and calculus leaves -/

/-- (4) from (2) and (3): `B = curl A`, so `‖D^k_y B‖ ≤ 3 ‖D^{k+1}_y A‖ ≤ 3M |y|^{-(k+2)}`. -/
theorem newtonCurlSliceDecayFar_of (h2 : NewtonVectorPotentialFarDeriv)
    (h3 : SpatialCurlSliceDerivBound) : NewtonCurlSliceDecayFar := by
  intro P _ φ hφ
  obtain ⟨ρ, M, hρ, hM, hfar⟩ := h2 P φ hφ
  refine ⟨ρ, 3 * M, hρ, by positivity, fun τ y hy k hk => ?_⟩
  have e := h3 (projectedTestNewtonVectorPotential φ)
    (contDiff_projectedTestNewtonVectorPotential hφ) k τ y
  have f := hfar τ y hy (k + 1) (by omega)
  have hexp : (-(((k + 1 : ℕ) : ℝ) + 1)) = -((k : ℝ) + 2) := by push_cast; ring
  rw [hexp] at f
  calc ‖iteratedFDeriv ℝ k (fun x => projectedTestNewtonVectorPotentialCurl φ (τ, x)) y‖
      ≤ 3 * ‖iteratedFDeriv ℝ (k + 1)
          (fun x => projectedTestNewtonVectorPotential φ (τ, x)) y‖ := e
    _ ≤ 3 * (M * ‖y‖ ^ (-((k : ℝ) + 2))) := mul_le_mul_of_nonneg_left f (by norm_num)
    _ = 3 * M * ‖y‖ ^ (-((k : ℝ) + 2)) := by ring

/-- (14) from (8)-(13). -/
theorem curlCutoffL0TCalc_of (h8 : L0TSliceBound) (h9 : RealCCurlSliceDerivBound)
    (h10 : CutoffSmulDeriv1) (h11 : CutoffSmulDeriv23) (h12 : CurlCutoffTimeComm)
    (h13 : CurlCutoffL0TDiff) : CurlCutoffL0TCalc := by
  obtain ⟨C₁, hC₁, hd1⟩ := h10
  obtain ⟨C₂, hC₂, hd23⟩ := h11
  refine ⟨9 * C₁ + 9 * C₂, by linarith, ?_⟩
  intro B hB M hM hBk hTk ν hν R hR τ y
  have hR0 : (0 : ℝ) < R := by linarith
  have hin : ContDiff ℝ ∞ (fun x : Space => ((τ, x) : ℝ × Space)) :=
    contDiff_const.prodMk contDiff_id
  have hG : ∀ D : ℝ × Space → Space, ContDiff ℝ ∞ D →
      ContDiff ℝ ∞ (fun w : ℝ × Space => (cutoff R w.2 - 1) • D w) := fun D hD =>
    (((cutoff_smooth R).comp contDiff_snd).sub contDiff_const).smul hD
  have hErr : ∀ D : ℝ × Space → Space, ContDiff ℝ ∞ D → ContDiff ℝ ∞ (cutoffErr R D) := by
    intro D hD
    have hC := contDiff_spatialCurlST_of_contDiff (hG D hD)
    unfold cutoffErr
    rw [realC_eq_cplxV]
    exact UnforcedLeray.Axi.cplxV.contDiff.comp hC
  have hdτB : ContDiff ℝ ∞ (dτ B) := by
    unfold dτ
    exact (hB.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  set w : ℝ := (1 - cutoff (R / 2) y) * powWeight 2 y with hw
  have hw0 : 0 ≤ w := mul_nonneg (by linarith [cutoff_le_one (R / 2) y]) (powWeight_nonneg _ _)
  have hE0 : ∀ D : ℝ × Space → Space, ContDiff ℝ ∞ D →
      (∀ (y : Space) (k : ℕ), k ≤ 1 →
        ‖iteratedFDeriv ℝ k (fun x => D (τ, x)) y‖ ≤ M * powWeight ((k : ℝ) + 1) y) →
      ‖cutoffErr R D (τ, y)‖ ≤ 3 * (C₁ * M * w) := by
    intro D hD hDk
    have e1 := h9 _ (hG D hD) 0 τ y
    rw [norm_iteratedFDeriv_zero] at e1
    have e2 := hd1 (fun x => D (τ, x)) (hD.comp hin) M hM hDk R hR y
    exact e1.trans (mul_le_mul_of_nonneg_left e2 (by norm_num))
  rw [h13 B hB R ν hR0 (τ, y)]
  have hL := h8 (cutoffErr R B) (hErr B hB) ν hν τ y
  rw [h12 B hB R] at hL
  have b0 : ‖cutoffErr R (dτ B) (τ, y)‖ ≤ 3 * (C₁ * M * w) :=
    hE0 (dτ B) hdτB (fun y k hk => hTk τ y k hk)
  have b1 : ‖cutoffErr R B (τ, y)‖ ≤ 3 * (C₁ * M * w) :=
    hE0 B hB (fun y k hk => hBk τ y k (by omega))
  obtain ⟨b2', b3'⟩ := hd23 (fun x => B (τ, x)) (hB.comp hin) M hM
    (fun y k hk => hBk τ y k hk) R hR y
  have b2 : ‖y‖ * ‖iteratedFDeriv ℝ 1 (fun x => cutoffErr R B (τ, x)) y‖ ≤
      3 * (C₂ * M * w) := by
    have e := h9 _ (hG B hB) 1 τ y
    calc ‖y‖ * ‖iteratedFDeriv ℝ 1 (fun x => cutoffErr R B (τ, x)) y‖
        ≤ ‖y‖ * (3 * ‖iteratedFDeriv ℝ 2 (fun x => (cutoff R x - 1) • B (τ, x)) y‖) :=
          mul_le_mul_of_nonneg_left e (norm_nonneg _)
      _ = 3 * (‖y‖ * ‖iteratedFDeriv ℝ 2 (fun x => (cutoff R x - 1) • B (τ, x)) y‖) := by
          ring
      _ ≤ 3 * (C₂ * M * w) := mul_le_mul_of_nonneg_left b2' (by norm_num)
  have b3 : ‖iteratedFDeriv ℝ 2 (fun x => cutoffErr R B (τ, x)) y‖ ≤ 3 * (C₂ * M * w) :=
    (h9 _ (hG B hB) 2 τ y).trans (mul_le_mul_of_nonneg_left b3' (by norm_num))
  have hy3 : 3 * ‖y‖ * ‖iteratedFDeriv ℝ 1 (fun x => cutoffErr R B (τ, x)) y‖ ≤
      3 * (3 * (C₂ * M * w)) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left b2 (by norm_num)
  have hν3 : 3 * ν * ‖iteratedFDeriv ℝ 2 (fun x => cutoffErr R B (τ, x)) y‖ ≤
      3 * ν * (3 * (C₂ * M * w)) :=
    mul_le_mul_of_nonneg_left b3 (mul_nonneg (by norm_num) hν)
  have hpos : 0 ≤ ν * C₁ * M * w := mul_nonneg (mul_nonneg (mul_nonneg hν hC₁) hM) hw0
  nlinarith [hL, b0, b1, hy3, hν3, hpos]

/-! ### The graph-sense approximation -/

theorem l0TSolApprox_of (hAE : NewtonCurlRepSliceAE) (hE : CurlCutoffL0TErrorBound)
    (hS : UniformCutoffLimitSliceTest) (hL : UniformCutoffLimitPairing) : L0TSolApprox := by
  intro P _ ν hν Φ hΦ
  have hP : (0 : ℝ) < P := Fact.out
  have h1 : IsPhaseTest P (fun z => reV (Φ z)) := hΦ.clm_comp reV
  have h2 : IsPhaseTest P (fun z => imV (Φ z)) := hΦ.clm_comp imV
  have hsol1 : ∀ n : ℕ, IsSolTest P (projectedPotentialCurlCutoff ((n : ℝ) + 1)
      (projectedTestNewtonVectorPotentialCurl (fun z => reV (Φ z)))) := fun n =>
    isSolTest_projectedTestNewtonVectorPotentialCurlCutoff hP h1 (by positivity)
  have hsol2 : ∀ n : ℕ, IsSolTest P (projectedPotentialCurlCutoff ((n : ℝ) + 1)
      (projectedTestNewtonVectorPotentialCurl (fun z => imV (Φ z)))) := fun n =>
    isSolTest_projectedTestNewtonVectorPotentialCurlCutoff hP h2 (by positivity)
  have hsol : ∀ n, IsSolTest P (curlCutoffSeq Φ n) := fun n =>
    UnforcedLeray.Short.IIb.isSolTest_add_smul Complex.I (hsol1 n) (hsol2 n)
  refine ⟨curlCutoffSeq Φ, hsol, ?_⟩
  rw [projSmooth_eq_curlRepC hAE hΦ]
  obtain ⟨K₁, hK₁, hb₁⟩ := hE P _ h1
  obtain ⟨K₂, hK₂, hb₂⟩ := hE P _ h2
  have hlin : ∀ n, L0T ν (curlCutoffSeq Φ n) =
      L0T ν (projectedPotentialCurlCutoff ((n : ℝ) + 1)
          (projectedTestNewtonVectorPotentialCurl (fun z => reV (Φ z)))) +
        Complex.I • L0T ν (projectedPotentialCurlCutoff ((n : ℝ) + 1)
          (projectedTestNewtonVectorPotentialCurl (fun z => imV (Φ z)))) := fun n =>
    L0T_add_csmul ν (hsol1 n).1.smooth (hsol2 n).1.smooth Complex.I
  have hlin' : L0T ν (curlRepC Φ) = L0T ν (curlRepR (fun z => reV (Φ z))) +
      Complex.I • L0T ν (curlRepR (fun z => imV (Φ z))) :=
    L0T_add_csmul ν (contDiff_curlRepR h1) (contDiff_curlRepR h2) Complex.I
  have hbound : ∀ (n : ℕ) (τ : ℝ) (y : Space),
      ‖L0T ν (curlCutoffSeq Φ n) (τ, y) - L0T ν (curlRepC Φ) (τ, y)‖ ≤
        ((K₁ + K₂) * (1 + ν)) * ((1 - cutoff (((n : ℝ) + 1) / 2) y) * powWeight 2 y) := by
    intro n τ y
    have hR : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have e1 := hb₁ ν hν.le ((n : ℝ) + 1) hR τ y
    have e2 := hb₂ ν hν.le ((n : ℝ) + 1) hR τ y
    rw [hlin n, hlin']
    simp only [Pi.add_apply, Pi.smul_apply]
    set a₁ := L0T ν (projectedPotentialCurlCutoff ((n : ℝ) + 1)
      (projectedTestNewtonVectorPotentialCurl (fun z => reV (Φ z)))) (τ, y)
    set a₂ := L0T ν (projectedPotentialCurlCutoff ((n : ℝ) + 1)
      (projectedTestNewtonVectorPotentialCurl (fun z => imV (Φ z)))) (τ, y)
    set b₁ := L0T ν (curlRepR (fun z => reV (Φ z))) (τ, y)
    set b₂ := L0T ν (curlRepR (fun z => imV (Φ z))) (τ, y)
    have hsplit : a₁ + Complex.I • a₂ - (b₁ + Complex.I • b₂) =
        (a₁ - b₁) + Complex.I • (a₂ - b₂) := by
      rw [smul_sub]; abel
    rw [hsplit]
    calc ‖(a₁ - b₁) + Complex.I • (a₂ - b₂)‖ ≤ ‖a₁ - b₁‖ + ‖Complex.I • (a₂ - b₂)‖ :=
          norm_add_le _ _
      _ = ‖a₁ - b₁‖ + ‖a₂ - b₂‖ := by rw [norm_smul, Complex.norm_I, one_mul]
      _ ≤ K₁ * (1 + ν) * ((1 - cutoff (((n : ℝ) + 1) / 2) y) * powWeight 2 y) +
          K₂ * (1 + ν) * ((1 - cutoff (((n : ℝ) + 1) / 2) y) * powWeight 2 y) :=
          add_le_add e1 e2
      _ = ((K₁ + K₂) * (1 + ν)) * ((1 - cutoff (((n : ℝ) + 1) / 2) y) * powWeight 2 y) := by
          ring
  have hΘ : ∀ n, IsPhaseTest P (L0T ν (curlCutoffSeq Φ n)) := fun n =>
    isPhaseTest_L0T (hsol n).1 ν
  exact hL P _ _ _ hΘ (hS P _ _ _ hΘ hbound) hbound

/-- **`L0TSolApprox` from the leaves.** -/
theorem l0TSolApprox_of_leaves (h1 : NewtonCurlRepSliceAE) (h6 : NewtonCurlSliceDecay)
    (h7 : NewtonCurlTimeComm) (h14 : CurlCutoffL0TCalc) (h15 : UniformCutoffLimitSliceTest)
    (h16 : UniformCutoffLimitPairing) : L0TSolApprox :=
  l0TSolApprox_of h1 (curlCutoffL0TErrorBound_of h6 h7 h14) h15 h16

/-- **`L0TSolApprox` from the finest leaves** (`(6)` and `(14)` still as Props: `(6)` is assembled
from `(4)`, `(5)` by task `.../2/1/2/6`). -/
theorem l0TSolApprox_of_fine (h1 : NewtonCurlRepSliceAE) (h6 : NewtonCurlSliceDecay)
    (h7 : NewtonCurlTimeComm) (h8 : L0TSliceBound) (h9 : RealCCurlSliceDerivBound)
    (h10 : CutoffSmulDeriv1) (h11 : CutoffSmulDeriv23) (h12 : CurlCutoffTimeComm)
    (h13 : CurlCutoffL0TDiff) (h15 : UniformCutoffLimitSliceTest)
    (h16 : UniformCutoffLimitPairing) : L0TSolApprox :=
  l0TSolApprox_of_leaves h1 h6 h7 (curlCutoffL0TCalc_of h8 h9 h10 h11 h12 h13) h15 h16

end UnforcedLeray.Short.PartIIIb.Concrete.SolApprox
