import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org_1_a.PointBound

/-!
# Helper for `PartIII-a:T21/c3/2/1/1/org/1/a`: the uniform pointwise-in-age package

`goodAt_package`: there are `K_A ≥ 0` and `b₀ ≥ 1` such that for `b ≥ b₀` and small `ν`, at every
age `r ≥ 0` with `b ≤ θ(r)`, the map `W ↦ movDampedComplInt κ P tr r W` sends `X_{m,d(r)}` to
itself with norm at most `K_A` and is additive a.e. (SP 2920-2925, 2974-2978).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit.RelIntA

open UnforcedLeray.Short.IIIa.CompactDuhamelGapSub UnforcedLeray.Short.IIIa.ComplCouplingSub
  UnforcedLeray.Short.IIIa.EulerErrorSub

/-- The good-age package at `r`: `d(r) ≥ 1`, the bound with constant `K_A` on `X_{m,d(r)}`, and
a.e. additivity. -/
def GoodAt (κ : PlanarFrameKernels) (P : PlanarData) (m K_A : ℝ) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ) : Prop :=
  1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) ∧
  (∀ W : ℝ × ℝ → ℂ,
    MemLp W 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m) →
    MemLp (movDampedComplInt κ P tr r W) 2
        (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m) ∧
      xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (movDampedComplInt κ P tr r W) ≤
        ENNReal.ofReal K_A * xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m W) ∧
  (∀ W₁ W₂ : ℝ × ℝ → ℂ,
    MemLp W₁ 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m) →
    MemLp W₂ 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m) →
    movDampedComplInt κ P tr r (fun y => W₁ y + W₂ y)
      =ᵐ[B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m]
      fun y => movDampedComplInt κ P tr r W₁ y + movDampedComplInt κ P tr r W₂ y)

theorem norm_seedModeEigen (lam : ℂ) (i : Fin 2) : ‖seedModeEigen lam i‖ = ‖lam‖ := by
  unfold seedModeEigen
  split_ifs
  · rfl
  · exact Complex.norm_conj lam

theorem ofReal_combo_Ψ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    ENNReal.ofReal (a + b * c + 2 * (c * a * c)) = ENNReal.ofReal a +
      ENNReal.ofReal b * ENNReal.ofReal c + 2 * (ENNReal.ofReal (c * a) * ENNReal.ofReal c) := by
  rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_add ha (by positivity),
    ENNReal.ofReal_mul hb, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_ofNat]

theorem ofReal_combo_A (a b c e : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (he : 0 ≤ e) :
    ENNReal.ofReal (a + 2 * (b * c) + 2 * (c * e)) = ENNReal.ofReal a +
      2 * (ENNReal.ofReal b * ENNReal.ofReal c) + 2 * (ENNReal.ofReal c * ENNReal.ofReal e) := by
  rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_add ha (by positivity),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_mul hb,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_mul hc, ENNReal.ofReal_ofNat]

theorem aesm_sum2 {μ : Measure (ℝ × ℝ)} (c : Fin 2 → ℂ) (f : Fin 2 → ℝ × ℝ → ℂ)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ) :
    AEStronglyMeasurable (fun y => ∑ i, c i * f i y) μ := by
  simp only [Fin.sum_univ_two]
  exact ((hf 0).const_mul _).add ((hf 1).const_mul _)

theorem aesm_sum2' {μ : Measure (ℝ × ℝ)} (c : Fin 2 → ℂ) (f : Fin 2 → ℝ × ℝ → ℂ)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ) :
    AEStronglyMeasurable (fun y => ∑ i, f i y * c i) μ := by
  simp only [Fin.sum_univ_two]
  exact ((hf 0).mul_const _).add ((hf 1).mul_const _)

set_option maxHeartbeats 1000000 in
theorem goodAt_package (κ : PlanarFrameKernels) (hκ : IsSeedKernels κ) (P : PlanarData)
    (m : ℝ) (hm : 8 < m) (K : ℝ) :
    ∃ K_A b₀ : ℝ, 0 ≤ K_A ∧ 1 ≤ b₀ ∧ ∀ b : ℝ, b₀ ≤ b → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ν₀ ≤ 1 ∧
      ∀ ν ∈ Ioc 0 ν₀, PerFrameFacts κ ν m b K →
        ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
          UnforcedLeray.Short.PartI.IsBUCTrain tr →
          ∀ r : ℝ, 0 ≤ r → b ≤ clockTheta ν r → GoodAt κ P m K_A tr r := by
  obtain ⟨C_T, b_T, ν_T, hCT, hνT, hTr⟩ := trainCoeff_bounds m
  obtain ⟨C_h, b_h, hCh, hbh, Hh⟩ := UnforcedLeray.Short.IIIa.movLamDualHeatBound κ hκ m hm
  obtain ⟨lam, C_e, b_e, hCe, hbe, He⟩ := _root_.movLamDualEulerSubBound κ hκ m hm
  obtain ⟨C₁, b₁, hC₁, hb₁, H₁⟩ := UnforcedLeray.Short.IIIa.complModeForceOscillator κ hκ m hm
  obtain ⟨M_E, hME, hMEb⟩ := perE_and_pdCx_gauss_bounds hκ
  obtain ⟨K_g, hKg, hgauss⟩ := UnforcedLeray.Short.IIIa.xNorm_le_of_gauss (m := m) (by linarith)
  set K' : ℝ := max K 0 with hK'
  have hK'0 : 0 ≤ K' := le_max_right _ _
  have hKK' : K ≤ K' := le_max_left _ _
  have hcyl0 : 0 ≤ IIb.cylKernelBoundConst m := (IIb.cylKernelBoundConst_pos m).le
  set C_I : ℝ := 2 * IIb.cylKernelBoundConst m * C_T with hCI
  have hCI0 : 0 ≤ C_I := by positivity
  set C_H : ℝ := C_h + C_e + ‖lam‖ * K' with hCH
  have hCH0 : 0 ≤ C_H := by positivity
  set C_K0 : ℝ := C₁ + 2 * C_T * M_E * K_g + C_I * K' with hCK0
  have hCK00 : 0 ≤ C_K0 := by positivity
  set C_β : ℝ := |P.eigenvalue.re| + |P.kappa.re| + 1 with hCβ
  have hCβ0 : 0 ≤ C_β := by positivity
  set C_Ψ : ℝ := C_K0 + C_β * K' + 2 * (K' * C_K0 * K') with hCΨ
  have hCΨ0 : 0 ≤ C_Ψ := by positivity
  set K_A : ℝ := C_I + 2 * (C_H * K') + 2 * (K' * C_Ψ) with hKA
  refine ⟨K_A, max (max (max b_T b_h) (max b_e b₁)) 1, by positivity, le_max_right _ _,
    fun b hb => ?_⟩
  have hb_T : b_T ≤ b := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _)
    (le_max_left _ _))) hb
  have hb_h : b_h ≤ b := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _)
    (le_max_left _ _))) hb
  have hb_e : b_e ≤ b := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
    (le_max_left _ _))) hb
  have hb_1 : b₁ ≤ b := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
    (le_max_left _ _))) hb
  have hb1 : 1 ≤ b := le_trans (le_max_right _ _) hb
  obtain ⟨ν_h, hνh, Hh'⟩ := Hh b hb_h
  obtain ⟨ν_e, hνe, He'⟩ := He b hb_e
  obtain ⟨ν₁, hν₁, H₁'⟩ := H₁ b hb_1
  refine ⟨min (min (min ν_T ν_h) (min ν_e ν₁)) 1,
    lt_min (lt_min (lt_min hνT hνh) (lt_min hνe hν₁)) one_pos, min_le_right _ _,
    fun ν hν hF tr htr r hr hbr => ?_⟩
  have hν0 : 0 < ν := hν.1
  have hνle : ν ≤ min (min (min ν_T ν_h) (min ν_e ν₁)) 1 := hν.2
  have hν1 : ν ≤ 1 := hνle.trans (min_le_right _ _)
  have hνT' : ν ∈ Ioc 0 ν_T :=
    ⟨hν0, hνle.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))⟩
  have hνh' : ν ∈ Ioc 0 ν_h :=
    ⟨hν0, hνle.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))⟩
  have hνe' : ν ∈ Ioc 0 ν_e :=
    ⟨hν0, hνle.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))⟩
  have hν₁' : ν ∈ Ioc 0 ν₁ :=
    ⟨hν0, hνle.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))⟩
  have hθ1 : 1 ≤ clockTheta ν r := hb1.trans hbr
  have hθpos : 0 < clockTheta ν r := theta_pos hν0 hr
  have hd : 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) := one_le_cellLen_of_theta hν0 hν1 hr hθ1
  have hd0 : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν r) := by linarith
  have hmc : movingCell ν (ν ^ (-2 : ℝ)) r = B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) :=
    rfl
  obtain ⟨hVb, hcoef⟩ := hTr ν hνT' tr htr r hr (hb_T.trans hbr)
  -- the localized interaction
  have hInt : ∀ W : ℝ × ℝ → ℂ,
      MemLp W 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m) →
      AEStronglyMeasurable (movLInt tr r W)
          (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m) ∧
        xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (movLInt tr r W) ≤
          ENNReal.ofReal C_I * xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m W :=
    fun W hW => cxInter_bound hd (by linarith) hCT hcoef hW
  -- the periodized modes
  have hEcont : ∀ i, Continuous (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i) :=
    fun i => continuous_perE hκ hd0 i
  have hEx : ∀ i, xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m
      (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i) ≤ ENNReal.ofReal K' :=
    fun i => (hF.2.1 r hr hbr i).trans (ENNReal.ofReal_le_ofReal hKK')
  have hEm : ∀ i, MemLp (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i) 2
      (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m) :=
    fun i => ⟨(hEcont i).aestronglyMeasurable, (hEx i).trans_lt ENNReal.ofReal_lt_top⟩
  -- the dual rows
  have hΛ : ∀ (j : Fin 2) (W : ℝ × ℝ → ℂ), ENNReal.ofReal ‖movLamPair κ ν r j W‖ ≤
      ENNReal.ofReal K' * xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m W := by
    intro j W
    have h := hF.2.2 r hr hbr j W
    exact h.trans (by gcongr)
  -- the dual generator pairing `H₀`
  have hH : ∀ (i : Fin 2) (W : ℝ × ℝ → ℂ),
      MemLp W 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m) →
      IntegrableOn (fun y => movLamDual κ tr r i y * W y)
          (B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))) ∧
        ENNReal.ofReal ‖movH0 κ tr r i W‖ ≤
          ENNReal.ofReal C_H * xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m W := by
    intro i W hW
    obtain ⟨hm1, hx1⟩ := Hh' ν hνh' r hr hbr i
    obtain ⟨hm2, hx2⟩ := He' ν hνe' tr htr r hr hbr i
    have hSub_eq : movLamDualSub κ lam tr r i =
        fun y => movLamDualHeat κ ν r i y + movLamDualEulerSub κ lam tr r i y :=
      funext (movLamDualSub_eq_add κ lam tr r i)
    have hSub_mem : MemLp (movLamDualSub κ lam tr r i) 2
        (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m)) := by
      rw [hSub_eq]
      exact hm1.add hm2
    obtain ⟨hI1, hB1⟩ := xNorm_pairing_bound hSub_mem hW
    have hI2 := integrableOn_perLam_mul κ hm hd i hW
    have hdual : ∀ y, movLamDual κ tr r i y = movLamDualSub κ lam tr r i y +
        seedModeEigen lam i * perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i y := by
      intro y
      unfold movLamDualSub
      ring
    have hint : IntegrableOn (fun y => movLamDual κ tr r i y * W y)
        (B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))) := by
      have h := hI1.add (hI2.const_mul (seedModeEigen lam i))
      refine h.congr_fun (fun y _ => ?_) (B0579.measurableSet_cell _)
      simp only [Pi.add_apply]
      rw [hdual y]
      ring
    refine ⟨hint, ?_⟩
    have hval : movH0 κ tr r i W =
        (∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)),
          movLamDualSub κ lam tr r i y * W y) +
        seedModeEigen lam i * ∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)),
          perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i y * W y := by
      rw [movH0_eq_integral_movLamDual, hmc, ← integral_const_mul,
        ← integral_add hI1 (hI2.const_mul _)]
      refine setIntegral_congr_fun (B0579.measurableSet_cell _) (fun y _ => ?_)
      rw [hdual y]
      ring
    have hN : xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m W ≠ ⊤ := hW.2.ne
    have hsub_x : xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m)
        (movLamDualSub κ lam tr r i) ≤ ENNReal.ofReal (C_h + C_e) := by
      have hθinv : 1 / clockTheta ν r ≤ 1 := by
        rw [div_le_one hθpos]; exact hθ1
      calc xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m) (movLamDualSub κ lam tr r i)
          ≤ xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m) (movLamDualHeat κ ν r i) +
              xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m)
                (movLamDualEulerSub κ lam tr r i) := by
            rw [hSub_eq]
            exact xNorm_add_le hm1.1 hm2.1
        _ ≤ ENNReal.ofReal (C_h * (1 / clockTheta ν r)) +
              ENNReal.ofReal (C_e * (1 / clockTheta ν r)) := add_le_add hx1 hx2
        _ ≤ ENNReal.ofReal C_h + ENNReal.ofReal C_e := by
            gcongr
            · exact mul_le_of_le_one_right hCh hθinv
            · exact mul_le_of_le_one_right hCe hθinv
        _ = ENNReal.ofReal (C_h + C_e) := (ENNReal.ofReal_add hCh hCe).symm
    have h1 : ‖∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)),
        movLamDualSub κ lam tr r i y * W y‖ ≤
        (C_h + C_e) * (xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m W).toReal :=
      le_toReal_of_ofReal_le hN (by positivity) (hB1.trans (by gcongr))
    have h2 : ‖∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)),
        perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i y * W y‖ ≤
        K' * (xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m W).toReal :=
      le_toReal_of_ofReal_le hN hK'0 (hΛ i W)
    refine ofReal_le_of_le_toReal hN hCH0 ?_
    rw [hval]
    calc ‖(∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)),
            movLamDualSub κ lam tr r i y * W y) +
          seedModeEigen lam i * ∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)),
            perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i y * W y‖
        ≤ ‖∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)),
            movLamDualSub κ lam tr r i y * W y‖ +
          ‖seedModeEigen lam i‖ * ‖∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)),
            perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i y * W y‖ := by
          rw [← norm_mul]; exact norm_add_le _ _
      _ ≤ (C_h + C_e) * (xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m W).toReal +
          ‖lam‖ * (K' * (xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m W).toReal) := by
          rw [norm_seedModeEigen]
          exact add_le_add h1 (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
      _ = C_H * (xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m W).toReal := by
          rw [hCH]; ring
  -- the unprojected mode residual `K₀`
  have hK0 : ∀ j : Fin 2,
      AEStronglyMeasurable (movK0 κ P tr r j)
          (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m) ∧
        xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (movK0 κ P tr r j) ≤
          ENNReal.ofReal C_K0 := by
    intro j
    obtain ⟨hOm, hOx⟩ := H₁' ν hν₁' r hr hbr j
    have hRm := aesm_movEulerRes hκ P hν0 tr hr m j
    have hmeas : AEStronglyMeasurable (movK0 κ P tr r j)
        (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m) :=
      (hOm.add hRm).add ((hEcont j).aestronglyMeasurable.const_mul _)
    refine ⟨hmeas, ?_⟩
    obtain ⟨hIm, hIx⟩ := hInt _ (hEm j)
    set T : ℝ × ℝ → ℂ := fun y =>
      ((movingTrainV tr r y 0 : ℝ) : ℂ) * pdCx 0 (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j) y +
        ((movingTrainV tr r y 1 : ℝ) : ℂ) *
          pdCx 1 (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j) y with hTdef
    have hdec : movK0 κ P tr r j = fun y => movOscRes κ ν r j y +
        (-(T y) + movLInt tr r (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j) y) := by
      funext y
      unfold movK0 movEulerRes
      rw [movL_eq_drift_add_movLInt]
      simp only [hTdef]
      ring
    have hTm : AEStronglyMeasurable T
        (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m) := by
      have hTeq : T = fun y => movLInt tr r (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j) y -
          (movK0 κ P tr r j y - movOscRes κ ν r j y) := by
        funext y
        rw [hdec]
        ring
      rw [hTeq]
      exact hIm.sub (hmeas.sub hOm)
    have hTx : xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m T ≤
        ENNReal.ofReal (2 * C_T * M_E * K_g) := by
      have hgb := hMEb _ hd j
      have h := hgauss (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (2 * C_T * M_E) T (by positivity)
        (fun x hx => ?_)
      · calc xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m T
            ≤ ENNReal.ofReal (2 * C_T * M_E * K_g) := h
          _ = ENNReal.ofReal (2 * C_T * M_E * K_g) := rfl
      · have hg0 := hgb.2.2 0 x hx
        have hg1 := hgb.2.2 1 x hx
        have hV0 := hVb x 0
        have hV1 := hVb x 1
        have hexp : 0 ≤ Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16) := (Real.exp_pos _).le
        calc ‖T x‖ ≤ ‖((movingTrainV tr r x 0 : ℝ) : ℂ) *
                pdCx 0 (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j) x‖ +
              ‖((movingTrainV tr r x 1 : ℝ) : ℂ) *
                pdCx 1 (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j) x‖ := norm_add_le _ _
          _ = |movingTrainV tr r x 0| *
                ‖pdCx 0 (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j) x‖ +
              |movingTrainV tr r x 1| *
                ‖pdCx 1 (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j) x‖ := by
              rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
                Real.norm_eq_abs]
          _ ≤ C_T * (M_E * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16)) +
              C_T * (M_E * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16)) := by
              gcongr
          _ = 2 * C_T * M_E * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16) := by ring
    have hOx' : xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (movOscRes κ ν r j) ≤
        ENNReal.ofReal C₁ := by
      refine hOx.trans (ENNReal.ofReal_le_ofReal ?_)
      rw [div_le_iff₀ hθpos]
      nlinarith
    have hIx' : xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m
        (movLInt tr r (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j)) ≤
        ENNReal.ofReal (C_I * K') := by
      rw [ENNReal.ofReal_mul hCI0]
      exact hIx.trans (by gcongr; exact hEx j)
    have hTm' : AEStronglyMeasurable (fun y => -(T y))
        (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m) := hTm.neg
    have hsm : AEStronglyMeasurable (fun y => -(T y) +
        movLInt tr r (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j) y)
        (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m) := hTm'.add hIm
    have hneg : xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (fun y => -(T y)) =
        xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m T := xNorm_neg_eq T
    rw [hdec]
    calc xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (fun y => movOscRes κ ν r j y +
          (-(T y) + movLInt tr r (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j) y))
        ≤ xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (movOscRes κ ν r j) +
          xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (fun y => -(T y) +
            movLInt tr r (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j) y) :=
          xNorm_add_le hOm hsm
      _ ≤ xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (movOscRes κ ν r j) +
          (xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (fun y => -(T y)) +
            xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m
              (movLInt tr r (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j))) :=
          add_le_add le_rfl (xNorm_add_le hTm' hIm)
      _ ≤ ENNReal.ofReal C₁ + (ENNReal.ofReal (2 * C_T * M_E * K_g) +
            ENNReal.ofReal (C_I * K')) := by
          rw [hneg]
          exact add_le_add hOx' (add_le_add hTx hIx')
      _ = ENNReal.ofReal C_K0 := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add hC₁ (by positivity), hCK0]
          congr 1
          ring
  -- the rate `β₀ - 1`
  have hβ : ‖(((movBeta0 P ν r - 1 : ℝ)) : ℂ)‖ ≤ C_β := by
    obtain ⟨hβ1, hβ2⟩ := movBeta0_bounds P hν0 hr (by linarith : (0 : ℝ) < b) hbr
    have hdiv : |P.kappa.re| / b ≤ |P.kappa.re| := div_le_self (abs_nonneg _) hb1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor
    · linarith [neg_abs_le P.eigenvalue.re, abs_nonneg P.kappa.re]
    · linarith [le_abs_self P.eigenvalue.re, abs_nonneg P.kappa.re]
  -- the matrix `M₀`
  have hM0 : ∀ i j : Fin 2, ‖movM0 κ P tr r i j‖ ≤ K' * C_K0 := by
    intro i j
    have hfin : xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (movK0 κ P tr r j) ≠ ⊤ :=
      ((hK0 j).2.trans_lt ENNReal.ofReal_lt_top).ne
    have h' := le_toReal_of_ofReal_le hfin hK'0 (hΛ i (movK0 κ P tr r j))
    have hK0r : (xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (movK0 κ P tr r j)).toReal ≤
        C_K0 := ENNReal.toReal_le_of_le_ofReal hCK00 (hK0 j).2
    calc ‖movM0 κ P tr r i j‖ = ‖movLamPair κ ν r i (movK0 κ P tr r j)‖ := rfl
      _ ≤ K' * (xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (movK0 κ P tr r j)).toReal := h'
      _ ≤ K' * C_K0 := mul_le_mul_of_nonneg_left hK0r hK'0
  -- the finite-rank column `Ψ_j = -K₀_j + (β₀ - 1) E_j + ∑ᵢ M₀_{ij} E_i`
  set Ψ : Fin 2 → ℝ × ℝ → ℂ := fun j y => -movK0 κ P tr r j y +
      (((movBeta0 P ν r - 1 : ℝ)) : ℂ) * perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j y +
      ∑ i : Fin 2, movM0 κ P tr r i j * perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i y
    with hΨdef
  have hEm' : ∀ i, AEStronglyMeasurable (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i)
      (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m) :=
    fun i => (hEcont i).aestronglyMeasurable
  have hΨm : ∀ j, AEStronglyMeasurable (Ψ j)
      (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m) := fun j =>
    (((hK0 j).1.neg).add ((hEm' j).const_mul _)).add (aesm_sum2 _ _ hEm')
  have hΨx : ∀ j, xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (Ψ j) ≤ ENNReal.ofReal C_Ψ := by
    intro j
    have hsum : xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (fun y =>
        ∑ i : Fin 2, movM0 κ P tr r i j * perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i y) ≤
        2 * (ENNReal.ofReal (K' * C_K0) * ENNReal.ofReal K') :=
      xNorm_sum2_le _ _ hEm' _ (fun i => by
        gcongr
        · exact hM0 i j
        · exact hEx i)
    have hfirst : xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (fun y => -movK0 κ P tr r j y +
        (((movBeta0 P ν r - 1 : ℝ)) : ℂ) * perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j y) ≤
        ENNReal.ofReal C_K0 + ENNReal.ofReal C_β * ENNReal.ofReal K' := by
      calc xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (fun y => -movK0 κ P tr r j y +
            (((movBeta0 P ν r - 1 : ℝ)) : ℂ) * perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j y)
          ≤ xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (fun y => -movK0 κ P tr r j y) +
            xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (fun y =>
              (((movBeta0 P ν r - 1 : ℝ)) : ℂ) *
                perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j y) :=
            xNorm_add_le (hK0 j).1.neg ((hEm' j).const_mul _)
        _ ≤ ENNReal.ofReal C_K0 + ENNReal.ofReal C_β * ENNReal.ofReal K' := by
            rw [xNorm_neg_eq]
            refine add_le_add (hK0 j).2 ((xNorm_const_mul_le _ _).trans ?_)
            gcongr
            exact hEx j
    calc xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (Ψ j)
        ≤ xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (fun y => -movK0 κ P tr r j y +
            (((movBeta0 P ν r - 1 : ℝ)) : ℂ) * perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j y) +
          xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (fun y =>
            ∑ i : Fin 2, movM0 κ P tr r i j * perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i y) :=
          xNorm_add_le (((hK0 j).1.neg).add ((hEm' j).const_mul _)) (aesm_sum2 _ _ hEm')
      _ ≤ (ENNReal.ofReal C_K0 + ENNReal.ofReal C_β * ENNReal.ofReal K') +
          2 * (ENNReal.ofReal (K' * C_K0) * ENNReal.ofReal K') := add_le_add hfirst hsum
      _ = ENNReal.ofReal C_Ψ := (ofReal_combo_Ψ C_K0 C_β K' hCK00 hCβ0 hK'0).symm
  -- the decomposition of `movDampedComplInt`
  have hdecomp : ∀ W : ℝ × ℝ → ℂ, movDampedComplInt κ P tr r W = fun y => movLInt tr r W y +
      ((-∑ i : Fin 2, movH0 κ tr r i W * perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i y) +
        ∑ j : Fin 2, Ψ j y * movLamPair κ ν r j W) := fun W => rfl
  refine ⟨hd, fun W hW => ?_, fun W₁ W₂ h₁ h₂ => ?_⟩
  · -- the bound
    have hN : xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m W ≠ ⊤ := hW.2.ne
    obtain ⟨hLm, hLx⟩ := hInt W hW
    have hAm : AEStronglyMeasurable (fun y => -∑ i : Fin 2, movH0 κ tr r i W *
        perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i y)
        (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m) :=
      (aesm_sum2 _ _ hEm').neg
    have hBm : AEStronglyMeasurable (fun y => ∑ j : Fin 2, Ψ j y * movLamPair κ ν r j W)
        (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m) :=
      aesm_sum2' _ _ hΨm
    have hAx : xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (fun y => -∑ i : Fin 2,
        movH0 κ tr r i W * perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i y) ≤
        2 * ((ENNReal.ofReal C_H * xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m W) *
          ENNReal.ofReal K') := by
      rw [xNorm_neg_eq]
      exact xNorm_sum2_le _ _ hEm' _ (fun i => mul_le_mul' (hH i W hW).2 (hEx i))
    have hBx : xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m
        (fun y => ∑ j : Fin 2, Ψ j y * movLamPair κ ν r j W) ≤
        2 * ((ENNReal.ofReal K' * xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m W) *
          ENNReal.ofReal C_Ψ) :=
      xNorm_sum2_le' _ _ hΨm _ (fun j => mul_le_mul' (hΛ j W) (hΨx j))
    have hmeas : AEStronglyMeasurable (movDampedComplInt κ P tr r W)
        (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m) := by
      rw [hdecomp W]
      exact hLm.add (hAm.add hBm)
    have hbound : xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (movDampedComplInt κ P tr r W) ≤
        ENNReal.ofReal K_A * xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m W := by
      have e1 : ENNReal.ofReal K_A = ENNReal.ofReal C_I +
          2 * (ENNReal.ofReal C_H * ENNReal.ofReal K') +
          2 * (ENNReal.ofReal K' * ENNReal.ofReal C_Ψ) :=
        ofReal_combo_A C_I C_H K' C_Ψ hCI0 hCH0 hK'0 hCΨ0
      rw [hdecomp W]
      calc xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (fun y => movLInt tr r W y +
            ((-∑ i : Fin 2, movH0 κ tr r i W * perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i y) +
              ∑ j : Fin 2, Ψ j y * movLamPair κ ν r j W))
          ≤ xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (movLInt tr r W) +
            (xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (fun y => -∑ i : Fin 2,
                movH0 κ tr r i W * perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i y) +
              xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m
                (fun y => ∑ j : Fin 2, Ψ j y * movLamPair κ ν r j W)) :=
            (xNorm_add_le hLm (hAm.add hBm)).trans (add_le_add le_rfl (xNorm_add_le hAm hBm))
        _ ≤ ENNReal.ofReal C_I * xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m W +
            (2 * ((ENNReal.ofReal C_H * xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m W) *
              ENNReal.ofReal K') +
            2 * ((ENNReal.ofReal K' * xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m W) *
              ENNReal.ofReal C_Ψ)) := add_le_add hLx (add_le_add hAx hBx)
        _ = ENNReal.ofReal K_A * xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m W := by
            rw [e1]
            ring
    exact ⟨⟨hmeas, hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hW.2)⟩, hbound⟩
  · -- additivity
    have hk₁ := (B0579.cellMeasure_ac _ m).ae_le (ae_integrableOn_kerVelCx hd (by linarith) h₁)
    have hk₂ := (B0579.cellMeasure_ac _ m).ae_le (ae_integrableOn_kerVelCx hd (by linarith) h₂)
    have hH₁ : ∀ i, movH0 κ tr r i (fun y => W₁ y + W₂ y) =
        movH0 κ tr r i W₁ + movH0 κ tr r i W₂ := by
      intro i
      rw [movH0_eq_integral_movLamDual, movH0_eq_integral_movLamDual,
        movH0_eq_integral_movLamDual, hmc, ← integral_add (hH i W₁ h₁).1 (hH i W₂ h₂).1]
      congr 1
      funext y
      ring
    have hΛ₁ : ∀ j, movLamPair κ ν r j (fun y => W₁ y + W₂ y) =
        movLamPair κ ν r j W₁ + movLamPair κ ν r j W₂ := by
      intro j
      unfold movLamPair
      rw [hmc, ← integral_add (integrableOn_perLam_mul κ hm hd j h₁)
        (integrableOn_perLam_mul κ hm hd j h₂)]
      congr 1
      funext y
      ring
    filter_upwards [hk₁, hk₂] with y hy₁ hy₂
    refine movDampedComplInt_add_of κ P tr r W₁ W₂ y (fun k => ?_) hH₁ hΛ₁
    unfold kerVelCx
    rw [← integral_add (hy₁ k) (hy₂ k)]
    congr 1
    funext z
    ring

end UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit.RelIntA
