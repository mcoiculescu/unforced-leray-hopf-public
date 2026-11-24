import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.DirectError.EulerSubBound.Pullback

/-!
# Train-comparison part of the moving Euler residual (helper for `PartIII-a:T21/c5/3/2`)

Source of record: `the November 2 reference manuscript` (SP), lines 2866-2889,
2905-2918 (the rescaled train differs from the periodized Gaussian by a Gaussian-small error).

Verbatim copy (namespace `EulerSubTrain`) of the compiled sections 1-3 of
`Clock/FrameAmplitudeProof/DirectError/EulerSubBound/SubBound.lean` (whose final assembly does not
compile, so that module cannot be imported): the periodized Gaussian adjoint `movEulerAdjGauss`,
the Gaussian-cylinder residual `movLam0EulerGaussSub`, and the proved `O(ν³/θ)` bound
`memLp_and_xNorm_movEulerAdj_trainDiff` for the train comparison defect.
-/
set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace EulerSubTrain

open DirectEulerSub

open ComplCouplingSub ComplCouplingHeat ComplCouplingEuler CutFTCDual CutFTCAux EulerErrorSub

/-! ## 1. Gaussian-cylinder moving Euler adjoint and decomposition of `movLam0DualEulerSub` -/

/-- Moving linearised Euler adjoint along the periodized Gaussian vortex `Train.datum d`:
`movEulerAdjGauss d Φ y = E0.transCx (fun z l => Train.datum d z l) Φ y - kerAdj d (fun l w => Φ w * (B0579.pd l (Cyl.curl (Train.datum d)) w : ℂ)) y`
(SP 2862-2865, 2905-2918). -/
def movEulerAdjGauss (d : ℝ) (Φ : ℝ × ℝ → ℂ) (y : ℝ × ℝ) : ℂ :=
  E0.transCx (fun z l => UnforcedLeray.Train.datum d z l) Φ y -
    kerAdj d (fun l w => Φ w *
      ((B0579.pd l (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) w : ℝ) : ℂ)) y

/-- Pure Gaussian-cylinder dual seed residual on the unnormalised periodized row `perLam0 κ d k`:
`movEulerAdjGauss d (perLam0 κ d k) - seedModeEigen lam k * perLam0 κ d k`
(SP 2876-2889, 2905-2918). -/
def movLam0EulerGaussSub (κ : PlanarFrameKernels) (lam : ℂ) (d : ℝ) (k : Fin 2)
    (y : ℝ × ℝ) : ℂ :=
  movEulerAdjGauss d (perLam0 κ d k) y - seedModeEigen lam k * perLam0 κ d k y

/-- Transport velocity BUC train difference on `perLam0 κ d(r) k`. -/
def transCxTrainDiff (κ : PlanarFrameKernels) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ) (k : Fin 2)
    (y : ℝ × ℝ) : ℂ :=
  let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
  E0.transCx (movingTrainV tr r) (perLam0 κ d k) y -
    E0.transCx (fun z l => UnforcedLeray.Train.datum d z l) (perLam0 κ d k) y

/-- Nonlocal Biot-Savart `kerAdj` BUC train difference on `perLam0 κ d(r) k`. -/
def kerAdjTrainDiff (κ : PlanarFrameKernels) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ) (k : Fin 2)
    (y : ℝ × ℝ) : ℂ :=
  let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
  kerAdj d (fun l w => perLam0 κ d k w * ((B0579.pd l (movingTrainE tr r) w : ℝ) : ℂ)) y -
    kerAdj d (fun l w => perLam0 κ d k w *
      ((B0579.pd l (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) w : ℝ) : ℂ)) y

/-- Unconditional decomposition of `movLam0DualEulerSub κ lam tr r k` into the BUC train comparison
defect plus the Gaussian-cylinder dual seed residual `movLam0EulerGaussSub κ lam d k`. -/
theorem movLam0DualEulerSub_eq_trainDiff_add_gauss (κ : PlanarFrameKernels) (lam : ℂ) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) {r : ℝ}
    (hν : 0 < ν) (hr : 0 ≤ r) (k : Fin 2) (y : ℝ × ℝ) :
    let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
    UnforcedLeray.Short.IIIa.movLam0DualEulerSub κ lam tr r k y =
      (movEulerAdj d (movingTrainV tr r) (movingTrainE tr r) (perLam0 κ d k) y -
        movEulerAdjGauss d (perLam0 κ d k) y) +
      movLam0EulerGaussSub κ lam d k y := by
  intro d
  rw [movLam0DualEulerSub_eq_movEulerAdj_sub κ lam tr hν hr k y]
  unfold ComplCouplingEuler.movLam0DualEulerSub movLam0EulerGaussSub
  ring

/-- Algebraic split of `movEulerAdj - movEulerAdjGauss` on `perLam0 κ d k` into
`transCxTrainDiff - kerAdjTrainDiff`. -/
theorem movEulerAdj_sub_gauss_eq (κ : PlanarFrameKernels) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ) (k : Fin 2) (y : ℝ × ℝ) :
    let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
    movEulerAdj d (movingTrainV tr r) (movingTrainE tr r) (perLam0 κ d k) y -
      movEulerAdjGauss d (perLam0 κ d k) y =
      transCxTrainDiff κ tr r k y + (-kerAdjTrainDiff κ tr r k y) := by
  intro d
  unfold movEulerAdj movEulerAdjGauss transCxTrainDiff kerAdjTrainDiff
  ring

/-! ## 2. Unconditional `O(ν³ / clockTheta ν r)` bound for `kerAdjTrainDiff` in `X_{-m, d(r)}` -/

/-- For any strongly measurable vector field `F : Fin 2 → ℝ × ℝ → ℂ`, `kerAdj d F` is strongly
measurable. -/
theorem stronglyMeasurable_kerAdj (d : ℝ) {F : Fin 2 → ℝ × ℝ → ℂ}
    (hF : ∀ l : Fin 2, StronglyMeasurable (F l)) :
    StronglyMeasurable (kerAdj d F) := by
  unfold kerAdj
  have hterm : ∀ l : Fin 2, StronglyMeasurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      F l p.2 * ((kerD d (p.2 - p.1) l : ℝ) : ℂ)) := by
    intro l
    have hk : StronglyMeasurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
        ((kerD d (p.2 - p.1) l : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.measurable.comp
        ((measurable_kerD d l).comp (measurable_snd.sub measurable_fst))).stronglyMeasurable
    exact ((hF l).comp_measurable measurable_snd).mul hk
  have hsum : StronglyMeasurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      ∑ l : Fin 2, F l p.2 * ((kerD d (p.2 - p.1) l : ℝ) : ℂ)) := by
    simp only [Fin.sum_univ_two]
    exact (hterm 0).add (hterm 1)
  exact hsum.integral_prod_right'

/-- When the `kerAdj` integrands of `F` and `F - G` are integrable on `B0579.cell d`,
`kerAdj d F y - kerAdj d G y = kerAdj d (fun l w => F l w - G l w) y`. -/
theorem kerAdj_sub_eq_of_integrableOn (d : ℝ) (F G : Fin 2 → ℝ × ℝ → ℂ) (y : ℝ × ℝ)
    (hF : ∀ l : Fin 2, IntegrableOn (fun w => F l w * ((kerD d (w - y) l : ℝ) : ℂ)) (B0579.cell d))
    (hFG : ∀ l : Fin 2,
      IntegrableOn (fun w => (F l w - G l w) * ((kerD d (w - y) l : ℝ) : ℂ)) (B0579.cell d)) :
    kerAdj d F y - kerAdj d G y = kerAdj d (fun l w => F l w - G l w) y := by
  have hG : ∀ l : Fin 2,
      IntegrableOn (fun w => G l w * ((kerD d (w - y) l : ℝ) : ℂ)) (B0579.cell d) := by
    intro l
    have heq : (fun w => G l w * ((kerD d (w - y) l : ℝ) : ℂ)) =
        (fun w => F l w * ((kerD d (w - y) l : ℝ) : ℂ) -
          (F l w - G l w) * ((kerD d (w - y) l : ℝ) : ℂ)) := by
      funext w
      ring
    rw [heq]
    exact (hF l).sub (hFG l)
  unfold kerAdj
  simp only [Fin.sum_univ_two]
  have hsub0 : (fun w => (F 0 w - G 0 w) * ((kerD d (w - y) 0 : ℝ) : ℂ)) =
      (fun w => F 0 w * ((kerD d (w - y) 0 : ℝ) : ℂ) -
        G 0 w * ((kerD d (w - y) 0 : ℝ) : ℂ)) := by
    funext w; ring
  have hsub1 : (fun w => (F 1 w - G 1 w) * ((kerD d (w - y) 1 : ℝ) : ℂ)) =
      (fun w => F 1 w * ((kerD d (w - y) 1 : ℝ) : ℂ) -
        G 1 w * ((kerD d (w - y) 1 : ℝ) : ℂ)) := by
    funext w; ring
  rw [integral_add (hF 0) (hF 1), integral_add (hG 0) (hG 1), integral_add (hFG 0) (hFG 1),
    hsub0, hsub1, integral_sub (hF 0) (hG 0), integral_sub (hF 1) (hG 1)]
  ring

/-- **Unconditional `O(ν³ / clockTheta ν r)` bound in `X_{-m, d(r)}` for `kerAdjTrainDiff`**:
for `8 < m`, there exist `C_ker ≥ 0` and `ν_ker > 0` such that for `ν ∈ Ioc 0 ν_ker`, any BUC train
`tr`, `0 ≤ r`, `1 ≤ clockTheta ν r`, and `k : Fin 2`:
`MemLp (kerAdjTrainDiff κ tr r k) 2 (B0579.cellMeasure d (-m))` and
`xNorm d (-m) (kerAdjTrainDiff κ tr r k) ≤ ENNReal.ofReal (C_ker * ν ^ 3 / clockTheta ν r)`. -/
theorem memLp_and_xNorm_kerAdjTrainDiff (κ : PlanarFrameKernels) {m : ℝ} (hm : 8 < m) :
    ∃ C_ker ν_ker : ℝ, 0 ≤ C_ker ∧ 0 < ν_ker ∧
      ∀ ν ∈ Ioc 0 ν_ker,
        ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
          PartI.IsBUCTrain tr →
          ∀ r : ℝ, 0 ≤ r → 1 ≤ clockTheta ν r → ∀ k : Fin 2,
            let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
            MemLp (-kerAdjTrainDiff κ tr r k) 2 (B0579.cellMeasure d (-m)) ∧
            xNorm d (-m) (-kerAdjTrainDiff κ tr r k) ≤
              ENNReal.ofReal (C_ker * ν ^ 3 / clockTheta ν r) := by
  have hm1 : 1 < m := by linarith
  obtain ⟨ν_bdd, hν_bdd, hBddAll⟩ := ladTrainBddAll_unconditional 2
  obtain ⟨C_E, ν_E, hCE_pos, hνE_pos, hE_bd⟩ := movingTrainGradE_sub_datum_bound 2
  obtain ⟨B_0, hB0_pos, hB0⟩ := Lam0B.perLam0_sup κ
  obtain ⟨C_K, hCK_pos, hKerInt⟩ := kerAdj_term_integrableOn_and_bound
  set W_m : ℝ := (B0592.weightConst m).toReal
  set C_ker : ℝ := W_m * (2 * C_K * B_0 * C_E)
  set ν_ker : ℝ := min 1 (min ν_bdd ν_E)
  refine ⟨C_ker, ν_ker, by positivity, lt_min zero_lt_one (lt_min hν_bdd hνE_pos),
    fun ν hν tr hbuc r hr hθ k => ?_⟩
  intro d
  have hν_pos : 0 < ν := hν.1
  have hν_le1 : ν ≤ 1 := hν.2.trans (min_le_left _ _)
  have hν_b : ν ∈ Ioc 0 ν_bdd :=
    ⟨hν_pos, hν.2.trans (le_trans (min_le_right _ _) (min_le_left _ _))⟩
  have hν_e : ν ∈ Ioc 0 ν_E :=
    ⟨hν_pos, hν.2.trans (le_trans (min_le_right _ _) (min_le_right _ _))⟩
  have hd1 : 1 ≤ d := one_le_cellLen_of_theta hν_pos hν_le1 hr hθ
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  have ha1 : 1 ≤ clockA ν r := one_le_clockA hν_pos.le hr
  have ha0 : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one ha1
  have hsa1 : 1 ≤ Real.sqrt (clockA ν r) := Real.one_le_sqrt.2 ha1
  have hsa0 : 0 < Real.sqrt (clockA ν r) := lt_of_lt_of_le zero_lt_one hsa1
  have hθ_pos : 0 < clockTheta ν r := lt_of_lt_of_le zero_lt_one hθ
  set q : ℝ := ν ^ 3 / clockTheta ν r
  have hq_nn : 0 ≤ q := by dsimp [q]; positivity
  -- Define `F_tr`, `F_G`, and `ΔF = F_tr - F_G`
  set F_tr : Fin 2 → ℝ × ℝ → ℂ :=
    fun l w => perLam0 κ d k w * ((B0579.pd l (movingTrainE tr r) w : ℝ) : ℂ)
  set F_G : Fin 2 → ℝ × ℝ → ℂ :=
    fun l w => perLam0 κ d k w *
      ((B0579.pd l (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) w : ℝ) : ℂ)
  set ΔF : Fin 2 → ℝ × ℝ → ℂ := fun l w => F_tr l w - F_G l w
  -- Continuity of `F_tr l` and `ΔF l`
  have hFtr_cont : ∀ l : Fin 2, Continuous (F_tr l) := by
    intro l
    have h1 : Continuous (perLam0 κ d k) := Lam0B.perLam0_continuous κ hd0 k
    have h2 : Continuous (fun w => ((B0579.pd l (movingTrainE tr r) w : ℝ) : ℂ)) := by
      have heq : (fun w => ((B0579.pd l (movingTrainE tr r) w : ℝ) : ℂ)) =
          (fun w => ((movingTrainGradE tr r w l : ℝ) : ℂ)) :=
        funext fun w => congrArg Complex.ofReal
          (pd_movingTrainE_eq_movingTrainGradE tr hν_pos hr l w)
      rw [heq]
      exact Complex.continuous_ofReal.comp (continuous_movingTrainGradE tr hr l)
    exact h1.mul h2
  have hFG_cont : ∀ l : Fin 2, Continuous (F_G l) := by
    intro l
    have h1 : Continuous (perLam0 κ d k) := Lam0B.perLam0_continuous κ hd0 k
    have hcurl_sm : ContDiff ℝ ∞ (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) :=
      dcs_contDiff_curl (UnforcedLeray.Train.datum_contDiff hd0.ne')
    have h2 : Continuous
        (B0579.pd l (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d))) :=
      ((hcurl_sm.fderiv_right (m := (1 : ℕ)) (by simp)).clm_apply contDiff_const).continuous
    exact h1.mul (Complex.continuous_ofReal.comp h2)
  have hΔF_cont : ∀ l : Fin 2, Continuous (ΔF l) := fun l => (hFtr_cont l).sub (hFG_cont l)
  -- `jb ^ 2` bound for `F_tr l` on `B0579.cell d`
  obtain ⟨C_tr, hBdd⟩ := hBddAll ν hν_b tr hbuc r hr
  set M_tr : ℝ := B_0 * ((clockA ν r) ^ ((5 : ℝ) / 2) * max C_tr 0)
  have hMtr_pos : 0 ≤ M_tr := by positivity
  have hFtr_int : ∀ (y : ℝ × ℝ) (l : Fin 2),
      IntegrableOn (fun w => F_tr l w * ((kerD d (w - y) l : ℝ) : ℂ)) (B0579.cell d) := by
    intro y l
    refine (hKerInt hd1 hMtr_pos (hFtr_cont l).aestronglyMeasurable (fun w hw => ?_) y l).1
    set z : ℝ × ℝ := (Real.sqrt (clockA ν r) * w.1, Real.sqrt (clockA ν r) * w.2)
    have hz_cell : z ∈ B0579.cell (ν ^ (-2 : ℝ)) := by
      simp only [B0579.cell, mem_prod, mem_Ico, mem_univ, and_true, z]
      have hw1 := hw.1.1
      have hw2 := hw.1.2
      have hmul : Real.sqrt (clockA ν r) * (d / 2) = ν ^ (-2 : ℝ) / 2 := by
        dsimp [d, cellLen]
        field_simp [hsa0.ne']
      refine ⟨by linarith [mul_le_mul_of_nonneg_left hw1 hsa0.le, hmul],
        by linarith [mul_lt_mul_of_pos_left hw2 hsa0, hmul]⟩
    have hjb_le : B0579.jb w ≤ B0579.jb z := by
      unfold B0579.jb
      dsimp [z]
      have h1 : w.1 ^ 2 ≤ (Real.sqrt (clockA ν r) * w.1) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt ha0.le]
        exact le_mul_of_one_le_left (sq_nonneg w.1) ha1
      have h2 : w.2 ^ 2 ≤ (Real.sqrt (clockA ν r) * w.2) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt ha0.le]
        exact le_mul_of_one_le_left (sq_nonneg w.2) ha1
      linarith
    have hjb_sq : B0579.jb w ^ 2 ≤ B0579.jb z ^ ((2 + 2 : ℝ) / 2) := by
      have hexp : (2 + 2 : ℝ) / 2 = (2 : ℕ) := by norm_num
      rw [hexp, Real.rpow_natCast]
      exact pow_le_pow_left₀ (B0579.jb_pos w).le hjb_le 2
    have hEc_bd : B0579.jb z ^ ((2 + 2 : ℝ) / 2) *
        |B0579.pd l (UnforcedLeray.B0238.Ec tr r) z| ≤ max C_tr 0 :=
      ((hBdd r ⟨hr, le_rfl⟩ z hz_cell).2 l).trans (le_max_left _ _)
    have hgrad_bd : B0579.jb w ^ 2 * |B0579.pd l (movingTrainE tr r) w| ≤
        (clockA ν r) ^ ((5 : ℝ) / 2) * max C_tr 0 := by
      rw [pd_movingTrainE_eq_movingTrainGradE tr hν_pos hr l w]
      unfold movingTrainGradE
      rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos ha0 _), ← mul_left_comm]
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg ha0.le _)
      exact (mul_le_mul_of_nonneg_right hjb_sq (abs_nonneg _)).trans hEc_bd
    have hlam_bd : ‖perLam0 κ d k w‖ ≤ B_0 := hB0 d hd1 k w hw
    dsimp [F_tr]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc B0579.jb w ^ 2 * (‖perLam0 κ d k w‖ * |B0579.pd l (movingTrainE tr r) w|)
        = ‖perLam0 κ d k w‖ * (B0579.jb w ^ 2 * |B0579.pd l (movingTrainE tr r) w|) := by ring
      _ ≤ B_0 * ((clockA ν r) ^ ((5 : ℝ) / 2) * max C_tr 0) :=
          mul_le_mul hlam_bd hgrad_bd (by positivity) hB0_pos
  -- `jb ^ 2` bound for `ΔF l` on `B0579.cell d` from `movingTrainGradE_sub_datum_bound 2`
  set M_diff : ℝ := B_0 * (C_E * q)
  have hMdiff_pos : 0 ≤ M_diff := by positivity
  have hΔF_ker : ∀ (y : ℝ × ℝ) (l : Fin 2),
      IntegrableOn (fun w => ΔF l w * ((kerD d (w - y) l : ℝ) : ℂ)) (B0579.cell d) ∧
      ‖∫ w in B0579.cell d, ΔF l w * ((kerD d (w - y) l : ℝ) : ℂ)‖ ≤ C_K * M_diff := by
    intro y l
    refine hKerInt hd1 hMdiff_pos (hΔF_cont l).aestronglyMeasurable (fun w hw => ?_) y l
    have hlam_bd : ‖perLam0 κ d k w‖ ≤ B_0 := hB0 d hd1 k w hw
    have hE_w := hE_bd ν hν_e tr hbuc r hr hθ w hw l
    have hΔF_eq : ΔF l w = perLam0 κ d k w *
        ((movingTrainGradE tr r w l -
          B0579.pd l (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) w : ℝ) : ℂ) := by
      dsimp [ΔF, F_tr, F_G]
      rw [pd_movingTrainE_eq_movingTrainGradE tr hν_pos hr l w]
      push_cast
      ring
    rw [hΔF_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc B0579.jb w ^ 2 *
          (‖perLam0 κ d k w‖ *
            |movingTrainGradE tr r w l -
              B0579.pd l (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) w|)
        = ‖perLam0 κ d k w‖ *
            (B0579.jb w ^ 2 *
              |movingTrainGradE tr r w l -
                B0579.pd l (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) w|) := by ring
      _ ≤ B_0 * (C_E * ν ^ 3 / clockTheta ν r) :=
          mul_le_mul hlam_bd hE_w (by positivity) hB0_pos
      _ = M_diff := by dsimp [M_diff, q]; ring
  -- Identify `kerAdjTrainDiff κ tr r k` with `kerAdj d ΔF`
  have hker_eq : kerAdjTrainDiff κ tr r k = kerAdj d ΔF := by
    funext y
    exact kerAdj_sub_eq_of_integrableOn d F_tr F_G y (hFtr_int y) (fun l => (hΔF_ker y l).1)
  have hneg_sm : StronglyMeasurable (-kerAdjTrainDiff κ tr r k) := by
    rw [hker_eq]
    exact (stronglyMeasurable_kerAdj d (fun l => (hΔF_cont l).stronglyMeasurable)).neg
  have hneg_sup : ∀ y ∈ B0579.cell d, ‖(-kerAdjTrainDiff κ tr r k) y‖ ≤
      2 * C_K * B_0 * C_E * q := by
    intro y _hy
    rw [Pi.neg_apply, norm_neg, hker_eq]
    unfold kerAdj
    simp only [Fin.sum_univ_two]
    rw [integral_add (hΔF_ker y 0).1 (hΔF_ker y 1).1]
    calc ‖(∫ w in B0579.cell d, ΔF 0 w * ((kerD d (w - y) 0 : ℝ) : ℂ)) +
            (∫ w in B0579.cell d, ΔF 1 w * ((kerD d (w - y) 1 : ℝ) : ℂ))‖
        ≤ ‖∫ w in B0579.cell d, ΔF 0 w * ((kerD d (w - y) 0 : ℝ) : ℂ)‖ +
            ‖∫ w in B0579.cell d, ΔF 1 w * ((kerD d (w - y) 1 : ℝ) : ℂ)‖ := norm_add_le _ _
      _ ≤ C_K * M_diff + C_K * M_diff := add_le_add (hΔF_ker y 0).2 (hΔF_ker y 1).2
      _ = 2 * C_K * B_0 * C_E * q := by dsimp [M_diff]; ring
  obtain ⟨hmem, hx⟩ := memLp_and_xNorm_neg_le_of_cell_bdd hm1 (by positivity)
    hneg_sm.aestronglyMeasurable hneg_sup
  refine ⟨hmem, hx.trans (le_of_eq ?_)⟩
  congr 1
  dsimp [C_ker, W_m, q]
  ring

/-! ## 3. `O(ν³ / clockTheta ν r)` bound for `transCxTrainDiff` and full BUC train comparison -/

/-- Pointwise multiplication by an a.e. strongly measurable complex function bounded by `M ≥ 0`
preserves `MemLp · 2 (B0579.cellMeasure d (-m))` and scales `xNorm d (-m)` by at most `M`. -/
theorem memLp_and_xNorm_mul_bdd {m d M K : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K)
    {a G : ℝ × ℝ → ℂ}
    (ha_sm : AEStronglyMeasurable a (B0579.cellMeasure d (-m)))
    (ha_bd : ∀ y : ℝ × ℝ, ‖a y‖ ≤ M)
    (hG : MemLp G 2 (B0579.cellMeasure d (-m)))
    (hG_x : xNorm d (-m) G ≤ ENNReal.ofReal K) :
    MemLp (fun y => a y * G y) 2 (B0579.cellMeasure d (-m)) ∧
    xNorm d (-m) (fun y => a y * G y) ≤ ENNReal.ofReal (M * K) := by
  have hpt : ∀ y : ℝ × ℝ, ‖a y * G y‖ ≤ ‖(M : ℂ) * G y‖ := by
    intro y
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hM]
    exact mul_le_mul_of_nonneg_right (ha_bd y) (norm_nonneg _)
  have hle : xNorm d (-m) (fun y => a y * G y) ≤ ENNReal.ofReal (M * K) := by
    calc xNorm d (-m) (fun y => a y * G y)
        ≤ xNorm d (-m) (fun y => (M : ℂ) * G y) := eLpNorm_mono hpt
      _ ≤ ENNReal.ofReal (‖(M : ℂ)‖ * K) := xNorm_const_mul_le hK hG_x
      _ = ENNReal.ofReal (M * K) := by
          rw [Complex.norm_real, Real.norm_of_nonneg hM]
  refine ⟨⟨ha_sm.mul hG.1, lt_of_le_of_lt hle ENNReal.ofReal_lt_top⟩, hle⟩

/-- **`O(ν³ / clockTheta ν r)` bound in `X_{-m, d(r)}` for `transCxTrainDiff`** from
`SeedLamGradPerSum κ` (`PartIII-a:T21/c5/1/1/1`) and `movingTrainV_sub_datum_bound`. -/
theorem memLp_and_xNorm_transCxTrainDiff (κ : PlanarFrameKernels)
    (hGrad : SeedLamGradPerSum κ) (hκ : IsSeedKernels κ) {m : ℝ} (hm : 8 < m) :
    ∃ C_Vtr ν_V : ℝ, 0 ≤ C_Vtr ∧ 0 < ν_V ∧
      ∀ ν ∈ Ioc 0 ν_V,
        ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
          PartI.IsBUCTrain tr →
          ∀ r : ℝ, 0 ≤ r → 1 ≤ clockTheta ν r → ∀ k : Fin 2,
            let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
            MemLp (transCxTrainDiff κ tr r k) 2 (B0579.cellMeasure d (-m)) ∧
            xNorm d (-m) (transCxTrainDiff κ tr r k) ≤
              ENNReal.ofReal (C_Vtr * ν ^ 3 / clockTheta ν r) := by
  have hm1 : 1 < m := by linarith
  obtain ⟨C_g, _, hcont, hdecay, hder0⟩ := hGrad hκ
  obtain ⟨K00, hK00, hB00⟩ :=
    memLp_and_xNorm_perSum_of_inv_sq_decay hm1 (hcont 0 0) (hdecay 0 0)
  obtain ⟨K01, hK01, hB01⟩ :=
    memLp_and_xNorm_perSum_of_inv_sq_decay hm1 (hcont 0 1) (hdecay 0 1)
  obtain ⟨K10, hK10, hB10⟩ :=
    memLp_and_xNorm_perSum_of_inv_sq_decay hm1 (hcont 1 0) (hdecay 1 0)
  obtain ⟨K11, hK11, hB11⟩ :=
    memLp_and_xNorm_perSum_of_inv_sq_decay hm1 (hcont 1 1) (hdecay 1 1)
  set K_g : ℝ := max (max K00 K01) (max K10 K11)
  have hK_g0 : 0 ≤ K_g := le_trans hK00 (le_trans (le_max_left _ _) (le_max_left _ _))
  have hPerLam0Grad : ∀ {d : ℝ}, 1 ≤ d → ∀ j l : Fin 2,
      MemLp (pdCx l (perLam0 κ d j)) 2 (B0579.cellMeasure d (-m)) ∧
      xNorm d (-m) (pdCx l (perLam0 κ d j)) ≤ ENNReal.ofReal K_g := by
    intro d hd j l
    have hfun : pdCx l (perLam0 κ d j) = perSum d (pdCx l (κ.lamP j)) :=
      funext fun y => (hder0 hd j l y).2
    rw [hfun]
    fin_cases j <;> fin_cases l
    · exact ⟨(hB00 d hd).1, (hB00 d hd).2.trans (ENNReal.ofReal_le_ofReal
        (le_trans (le_max_left _ _) (le_max_left _ _)))⟩
    · exact ⟨(hB01 d hd).1, (hB01 d hd).2.trans (ENNReal.ofReal_le_ofReal
        (le_trans (le_max_right _ _) (le_max_left _ _)))⟩
    · exact ⟨(hB10 d hd).1, (hB10 d hd).2.trans (ENNReal.ofReal_le_ofReal
        (le_trans (le_max_left _ _) (le_max_right _ _)))⟩
    · exact ⟨(hB11 d hd).1, (hB11 d hd).2.trans (ENNReal.ofReal_le_ofReal
        (le_trans (le_max_right _ _) (le_max_right _ _)))⟩
  obtain ⟨C_V, ν_V0, hCV_pos, hνV0_pos, hV_bd⟩ := movingTrainV_sub_datum_bound
  set C_Vtr : ℝ := 2 * C_V * K_g
  refine ⟨C_Vtr, min 1 ν_V0, by positivity, lt_min zero_lt_one hνV0_pos,
    fun ν hν tr hbuc r hr hθ k => ?_⟩
  intro d
  have hν_pos : 0 < ν := hν.1
  have hν_le1 : ν ≤ 1 := hν.2.trans (min_le_left _ _)
  have hν_V : ν ∈ Ioc 0 ν_V0 := ⟨hν_pos, hν.2.trans (min_le_right _ _)⟩
  have hd1 : 1 ≤ d := one_le_cellLen_of_theta hν_pos hν_le1 hr hθ
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  have hθ_pos : 0 < clockTheta ν r := lt_of_lt_of_le zero_lt_one hθ
  set q_V : ℝ := C_V * ν ^ 3 / clockTheta ν r
  have hqV_nn : 0 ≤ q_V := by dsimp [q_V]; positivity
  -- Bound each directional derivative term `l = 0, 1`
  have hterm : ∀ l : Fin 2,
      MemLp (fun y =>
        ((movingTrainV tr r y l - UnforcedLeray.Train.datum d y l : ℝ) : ℂ) *
          pdCx l (perLam0 κ d k) y) 2 (B0579.cellMeasure d (-m)) ∧
      xNorm d (-m) (fun y =>
        ((movingTrainV tr r y l - UnforcedLeray.Train.datum d y l : ℝ) : ℂ) *
          pdCx l (perLam0 κ d k) y) ≤ ENNReal.ofReal (q_V * K_g) := by
    intro l
    have ha_cont : Continuous (fun y : ℝ × ℝ =>
        ((movingTrainV tr r y l - UnforcedLeray.Train.datum d y l : ℝ) : ℂ)) := by
      have hc1 := continuous_movingTrainV tr hr l
      have hc2 : Continuous (fun y => UnforcedLeray.Train.datum d y l) :=
        (PiLp.continuous_apply 2 _ l).comp (UnforcedLeray.Train.datum_contDiff hd0.ne').continuous
      exact Complex.continuous_ofReal.comp (hc1.sub hc2)
    have ha_bd : ∀ y : ℝ × ℝ,
        ‖((movingTrainV tr r y l - UnforcedLeray.Train.datum d y l : ℝ) : ℂ)‖ ≤ q_V := by
      intro y
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hV_bd ν hν_V tr hbuc r hr hθ y l
    exact memLp_and_xNorm_mul_bdd hqV_nn hK_g0 ha_cont.aestronglyMeasurable ha_bd
      (hPerLam0Grad hd1 k l).1 (hPerLam0Grad hd1 k l).2
  have hfun : transCxTrainDiff κ tr r k =
      fun y =>
        ((movingTrainV tr r y 0 - UnforcedLeray.Train.datum d y 0 : ℝ) : ℂ) *
          pdCx 0 (perLam0 κ d k) y +
        ((movingTrainV tr r y 1 - UnforcedLeray.Train.datum d y 1 : ℝ) : ℂ) *
          pdCx 1 (perLam0 κ d k) y := by
    funext y
    unfold transCxTrainDiff E0.transCx
    dsimp only
    push_cast
    ring
  rw [hfun]
  obtain ⟨hm01, hx01⟩ := memLp_and_xNorm_add_le (by positivity) (by positivity)
    (hterm 0).1 (hterm 1).1 (hterm 0).2 (hterm 1).2
  refine ⟨hm01, hx01.trans (le_of_eq ?_)⟩
  congr 1
  dsimp [C_Vtr, q_V]
  ring

/-- **Combined `O(ν³ / clockTheta ν r)` BUC train comparison bound in `X_{-m, d(r)}`** for
`movEulerAdj d (movingTrainV tr r) (movingTrainE tr r) (perLam0 κ d k) - movEulerAdjGauss d (perLam0 κ d k)`. -/
theorem memLp_and_xNorm_movEulerAdj_trainDiff (κ : PlanarFrameKernels)
    (hGrad : SeedLamGradPerSum κ) (hκ : IsSeedKernels κ) {m : ℝ} (hm : 8 < m) :
    ∃ C_tr ν_tr : ℝ, 0 ≤ C_tr ∧ 0 < ν_tr ∧
      ∀ ν ∈ Ioc 0 ν_tr,
        ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
          PartI.IsBUCTrain tr →
          ∀ r : ℝ, 0 ≤ r → 1 ≤ clockTheta ν r → ∀ k : Fin 2,
            let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
            MemLp (fun y =>
              movEulerAdj d (movingTrainV tr r) (movingTrainE tr r) (perLam0 κ d k) y -
                movEulerAdjGauss d (perLam0 κ d k) y) 2 (B0579.cellMeasure d (-m)) ∧
            xNorm d (-m) (fun y =>
              movEulerAdj d (movingTrainV tr r) (movingTrainE tr r) (perLam0 κ d k) y -
                movEulerAdjGauss d (perLam0 κ d k) y) ≤
              ENNReal.ofReal (C_tr * ν ^ 3 / clockTheta ν r) := by
  obtain ⟨C_Vtr, ν_V, hCVtr_pos, hνV_pos, hVtr⟩ :=
    memLp_and_xNorm_transCxTrainDiff κ hGrad hκ hm
  obtain ⟨C_ker, ν_ker, hCker_pos, hνker_pos, hKer⟩ :=
    memLp_and_xNorm_kerAdjTrainDiff κ hm
  refine ⟨C_Vtr + C_ker, min ν_V ν_ker, by positivity, lt_min hνV_pos hνker_pos,
    fun ν hν tr hbuc r hr hθ k => ?_⟩
  intro d
  have hν_pos : 0 < ν := hν.1
  have hνV : ν ∈ Ioc 0 ν_V := ⟨hν_pos, hν.2.trans (min_le_left _ _)⟩
  have hνK : ν ∈ Ioc 0 ν_ker := ⟨hν_pos, hν.2.trans (min_le_right _ _)⟩
  have hθ_pos : 0 < clockTheta ν r := lt_of_lt_of_le zero_lt_one hθ
  have h1 := hVtr ν hνV tr hbuc r hr hθ k
  have h2 := hKer ν hνK tr hbuc r hr hθ k
  have heq : (fun y =>
      movEulerAdj d (movingTrainV tr r) (movingTrainE tr r) (perLam0 κ d k) y -
        movEulerAdjGauss d (perLam0 κ d k) y) =
      (fun y => transCxTrainDiff κ tr r k y + (-kerAdjTrainDiff κ tr r k) y) :=
    funext fun y => movEulerAdj_sub_gauss_eq κ tr r k y
  rw [heq]
  obtain ⟨hm12, hx12⟩ := memLp_and_xNorm_add_le (by positivity) (by positivity)
    h1.1 h2.1 h1.2 h2.2
  refine ⟨hm12, hx12.trans (le_of_eq ?_)⟩
  congr 1
  ring

end EulerSubTrain

end UnforcedLeray.Short.IIIa
