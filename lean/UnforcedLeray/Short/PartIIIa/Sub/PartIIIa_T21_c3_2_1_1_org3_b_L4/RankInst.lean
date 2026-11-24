import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_b_L4.RankAux2

/-!
# Leaf B4, finite-rank part: the instance estimates (SP 2898-2925)

On one block instance (fixed `ν`, train, age `r` with `θ(r) ≥ b`):
* `memLp_R`: the mode residual `R_j = movOscRes + movEulerRes` is `O(1/θ)` in `X_{m,d}`;
* `movM0_sub_eq`: `M₀_{ij} - λ_j δ_{ij} = Λ_i(R_j)` (biorthogonality);
* `lam'_close`, `movH0_close`: `H₀_i(Φ) - λ_i Λ_i(Φ) = O(1/θ) ‖W‖` (the dual generator bounds and
  the direct frame error identify the eigenvalue `λ'` of the dual bound with `λ_i` up to `O(1/θ)`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric UnforcedLeray.Blueprint.Planar

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub

namespace BlockPropagatorInteriorSub

open OrgSplit
open scoped ComplexConjugate ContDiff InnerProductSpace InnerProduct ENNReal

namespace OrgSplit3

namespace PlanarB

namespace L4

theorem ofReal_norm_le_of_ofReal {x : ℂ} {a : ℝ} (ha : 0 ≤ a)
    (h : ENNReal.ofReal ‖x‖ ≤ ENNReal.ofReal a) : ‖x‖ ≤ a :=
  (ENNReal.ofReal_le_ofReal_iff ha).1 h

/-- The mode residual `R_j = movOscRes + movEulerRes` in `X_{m,d}`. -/
theorem memLp_R (κ : PlanarFrameKernels) (P : PlanarData) {ν m : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ) (j : Fin 2) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hO : AEStronglyMeasurable (movOscRes κ ν r j)
        (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m) ∧
      xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (movOscRes κ ν r j) ≤ ENNReal.ofReal A)
    (hE : AEStronglyMeasurable (movEulerRes κ P tr r j)
        (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m) ∧
      xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (movEulerRes κ P tr r j) ≤
        ENNReal.ofReal B) :
    MemLp (fun x => movOscRes κ ν r j x + movEulerRes κ P tr r j x) 2
        (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m) ∧
      xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m
          (fun x => movOscRes κ ν r j x + movEulerRes κ P tr r j x) ≤
        ENNReal.ofReal (A + B) := by
  have hle : xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m
      (fun x => movOscRes κ ν r j x + movEulerRes κ P tr r j x) ≤ ENNReal.ofReal (A + B) := by
    unfold xNorm
    refine (eLpNorm_add_le hO.1 hE.1 (by norm_num)).trans ?_
    rw [ENNReal.ofReal_add hA hB]
    exact add_le_add hO.2 hE.2
  exact ⟨⟨hO.1.add hE.1, lt_of_le_of_lt hle ENNReal.ofReal_lt_top⟩, hle⟩

/-- `M₀_{ij} - λ_j δ_{ij} = Λ_i(R_j)` on a biorthogonal frame. -/
theorem movM0_sub_eq (κ : PlanarFrameKernels) (P : PlanarData) {ν m b K : ℝ} (hm : 8 < m)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) {r : ℝ} (hr : 0 ≤ r)
    (hθ : b ≤ clockTheta ν r) (hd : 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
    (hF : PerFrameFacts κ ν m b K) (i j : Fin 2)
    (hR : MemLp (fun x => movOscRes κ ν r j x + movEulerRes κ P tr r j x) 2
        (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m))
    (hE : MemLp (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j) 2
        (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m)) :
    movM0 κ P tr r i j - (if i = j then modeEigen P j else 0) =
      movLamPair κ ν r i (fun x => movOscRes κ ν r j x + movEulerRes κ P tr r j x) := by
  have hI1 := ComplCouplingSub.integrableOn_perLam_mul κ hm hd i hR
  have hI2 := ComplCouplingSub.integrableOn_perLam_mul κ hm hd i hE
  have hbi : movLamPair κ ν r i (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j) =
      if i = j then 1 else 0 := hF.1 r hr hθ i j
  have hkey : movM0 κ P tr r i j =
      movLamPair κ ν r i (fun x => movOscRes κ ν r j x + movEulerRes κ P tr r j x) +
        modeEigen P j * movLamPair κ ν r i (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j) := by
    unfold movM0 movLamPair movingCell
    rw [← integral_const_mul, ← integral_add hI1 (hI2.const_mul _)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [movK0]
    ring
  rw [hkey, hbi]
  split_ifs with hij
  · subst hij; ring
  · ring

theorem norm_modeEigen (P : PlanarData) (i : Fin 2) : ‖modeEigen P i‖ = ‖P.eigenvalue‖ := by
  unfold modeEigen
  split_ifs
  · rfl
  · exact Complex.norm_conj _

theorem norm_modeKappa (P : PlanarData) (i : Fin 2) : ‖modeKappa P i‖ = ‖P.kappa‖ := by
  unfold modeKappa
  split_ifs
  · rfl
  · exact Complex.norm_conj _

/-- The dual-bound eigenvalue `λ'` agrees with `λ_i` up to `O(1/θ)`, and
`H₀_i(Φ) - λ_i Λ_i(Φ) = O(1/θ) ‖W‖`. -/
theorem movH0_close (κ : PlanarFrameKernels) (P : PlanarData) {ν m b K : ℝ} (hm : 8 < m)
    (hν : 0 < ν) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) {r : ℝ} (hr : 0 ≤ r)
    (hθ : b ≤ clockTheta ν r) (hd : 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
    (hF : PerFrameFacts κ ν m b K) (lam' : ℂ) {C_S C_D : ℝ} (hC_S : 0 ≤ C_S) (hC_D : 0 ≤ C_D)
    (i : Fin 2)
    (hSub : MemLp (movLamDualSub κ lam' tr r i) 2
        (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m)) ∧
      xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m) (movLamDualSub κ lam' tr r i) ≤
        ENNReal.ofReal (C_S / clockTheta ν r))
    (hDir : ‖movH0 κ tr r i (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i) -
        modeDiag P ν r i‖ ≤ C_D / clockTheta ν r)
    {Φ : ℝ × ℝ → ℂ} (hΦ : MemLp Φ 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m))
    {w : ℝ} (hw0 : 0 ≤ w)
    (hw : xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m Φ ≤ ENNReal.ofReal w) :
    ‖movH0 κ tr r i Φ - modeEigen P i * movLamPair κ ν r i Φ‖ ≤
      ((C_S + (C_D + ‖P.kappa‖ + C_S * max K 0) * max K 0) / clockTheta ν r) * w := by
  set d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r) with hd_def
  set θ := clockTheta ν r with hθ_def
  have hθ0 : 0 < θ := by
    rw [hθ_def]; unfold clockTheta clockA
    exact inv_pos.2 (mul_pos hν (by nlinarith))
  set Kp := max K 0 with hKp
  have hKp0 : 0 ≤ Kp := le_max_right _ _
  -- the frame column
  have hEc : Continuous (perE κ d i) := perE_continuous_aux κ (lt_of_lt_of_le one_pos hd) i
  have hEx : xNorm d m (perE κ d i) ≤ ENNReal.ofReal Kp :=
    (hF.2.1 r hr hθ i).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hEm : MemLp (perE κ d i) 2 (B0579.cellMeasure d m) :=
    ⟨hEc.aestronglyMeasurable, lt_of_le_of_lt hEx ENNReal.ofReal_lt_top⟩
  -- `H(V) = λ' Λ(V) + ⟨Sub, V⟩`
  have hHE := movH0_eq_add κ tr r lam' hm hd i hEm hSub.1
  have hHΦ := movH0_eq_add κ tr r lam' hm hd i hΦ hSub.1
  have hbi : (∫ x in B0579.cell d, perLam κ d i x * perE κ d i x) = 1 := by
    have := hF.1 r hr hθ i i
    rw [if_pos rfl] at this
    exact this
  -- pairing bounds
  have hpE := (ComplCouplingSub.xNorm_pairing_bound hSub.1 hEm).2
  have hpΦ := (ComplCouplingSub.xNorm_pairing_bound hSub.1 hΦ).2
  have hpE' : ‖∫ x in B0579.cell d, movLamDualSub κ lam' tr r i x * perE κ d i x‖ ≤
      C_S / θ * Kp := by
    refine ofReal_norm_le_of_ofReal (by positivity) (hpE.trans ?_)
    rw [ENNReal.ofReal_mul (by positivity)]
    exact mul_le_mul' hSub.2 hEx
  have hpΦ' : ‖∫ x in B0579.cell d, movLamDualSub κ lam' tr r i x * Φ x‖ ≤ C_S / θ * w := by
    refine ofReal_norm_le_of_ofReal (by positivity) (hpΦ.trans ?_)
    rw [ENNReal.ofReal_mul (by positivity)]
    exact mul_le_mul' hSub.2 hw
  -- `Λ_i(Φ)` is bounded
  have hΛ : ‖movLamPair κ ν r i Φ‖ ≤ Kp * w := by
    refine ofReal_norm_le_of_ofReal (by positivity) ((hF.2.2 r hr hθ i Φ).trans ?_)
    rw [ENNReal.ofReal_mul hKp0]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) hw
  -- the eigenvalue of the dual bound
  have hlam : ‖seedModeEigen lam' i - modeEigen P i‖ ≤ (C_D + ‖P.kappa‖ + C_S * Kp) / θ := by
    have h1 : seedModeEigen lam' i - modeEigen P i =
        (movH0 κ tr r i (perE κ d i) - modeDiag P ν r i) + modeKappa P i / (θ : ℂ) -
          ∫ x in B0579.cell d, movLamDualSub κ lam' tr r i x * perE κ d i x := by
      rw [hHE, hbi]; unfold modeDiag; ring
    rw [h1]
    have h2 : ‖modeKappa P i / (θ : ℂ)‖ = ‖P.kappa‖ / θ := by
      rw [norm_div, norm_modeKappa, Complex.norm_real, Real.norm_of_nonneg hθ0.le]
    calc ‖(movH0 κ tr r i (perE κ d i) - modeDiag P ν r i) + modeKappa P i / (θ : ℂ) -
          ∫ x in B0579.cell d, movLamDualSub κ lam' tr r i x * perE κ d i x‖
        ≤ ‖movH0 κ tr r i (perE κ d i) - modeDiag P ν r i‖ + ‖modeKappa P i / (θ : ℂ)‖ +
            ‖∫ x in B0579.cell d, movLamDualSub κ lam' tr r i x * perE κ d i x‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ C_D / θ + ‖P.kappa‖ / θ + C_S / θ * Kp := by rw [h2]; linarith [hDir, hpE']
      _ = (C_D + ‖P.kappa‖ + C_S * Kp) / θ := by ring
  have h3 : movH0 κ tr r i Φ - modeEigen P i * movLamPair κ ν r i Φ =
      (seedModeEigen lam' i - modeEigen P i) * movLamPair κ ν r i Φ +
        ∫ x in B0579.cell d, movLamDualSub κ lam' tr r i x * Φ x := by
    rw [hHΦ]; unfold movLamPair movingCell; ring
  rw [h3]
  calc ‖(seedModeEigen lam' i - modeEigen P i) * movLamPair κ ν r i Φ +
        ∫ x in B0579.cell d, movLamDualSub κ lam' tr r i x * Φ x‖
      ≤ ‖seedModeEigen lam' i - modeEigen P i‖ * ‖movLamPair κ ν r i Φ‖ +
          ‖∫ x in B0579.cell d, movLamDualSub κ lam' tr r i x * Φ x‖ := by
        rw [← norm_mul]; exact norm_add_le _ _
    _ ≤ (C_D + ‖P.kappa‖ + C_S * Kp) / θ * (Kp * w) + C_S / θ * w := by
        gcongr
    _ = ((C_S + (C_D + ‖P.kappa‖ + C_S * Kp) * Kp) / θ) * w := by ring

end L4

end PlanarB

end OrgSplit3
end BlockPropagatorInteriorSub
end UnforcedLeray.Short.IIIa
