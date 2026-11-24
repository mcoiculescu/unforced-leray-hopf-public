import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.ShortBlock.EulerError.Velocity
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.ShortBlock.EulerError.Eigen
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.TrainBdd
import UnforcedLeray.Units.B0238.Partials

/-!
# The Gaussian-cylinder eigenmode residual (helper for `PartIII-a:T21/c3/3/3`)

Source of record: `the November 2 reference manuscript` (SP), lines 2866-2888,
2991-2995.

On the cell of period `d`, the residual
`(L_{d} E_j - L_∞ e_j) - λ_j (E_j - e_j)` (`E_j = P_d e_j`, `L_d` linearised around the
periodized Gaussian `P_d v₀`, `L_∞` around `v₀`) splits into
`(P_d v₀ - v₀)·∇E_j + v₀·∇(E_j - e_j) + (K_d E_j - K_∞ e_j)·∇ω₀ + K_d E_j·∇(P_dω₀ - ω₀)
 + λ_j(E_j - e_j)`.
All periodization errors are `O(d⁻² e^{-|y|²/16})` (`tail_gauss`), and the velocity error is
`O(d⁻²(1 + |y|))` for `|y| ≤ d/8` (`vel_compare`) and bounded elsewhere, where `∇ω₀` is
Gaussian-small. Hence the residual is `≤ C d⁻² e^{-|y|²/16}` on the cell
(`residual_pointwise`), and `≤ C d⁻²` in `X_{m,d}` (`movEulerGaussTailBound_seed`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace EulerErrorTail

/-! ## 1. Bounds of the seed modes and their periodizations -/

theorem seed_bounds {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) :
    ∃ C_e : ℝ, 0 ≤ C_e ∧ ∀ (j : Fin 2) (y : ℝ × ℝ),
      ‖κ.e j y‖ ≤ C_e * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) ∧
      ∀ k : Fin 2, ‖pdCx k (κ.e j) y‖ ≤ C_e * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by
  have hdec := (OscillatorForceSub.seed_e_smooth_decay hκ).2
  obtain ⟨C00, h00p, h00⟩ := hdec 0 0
  obtain ⟨C01, h01p, h01⟩ := hdec 0 1
  obtain ⟨C10, h10p, h10⟩ := hdec 1 0
  obtain ⟨C11, h11p, h11⟩ := hdec 1 1
  set C := C00 + C01 + C10 + C11 with hC
  refine ⟨C, by positivity, fun j y => ?_⟩
  have hE := Real.exp_pos (-(y.1 ^ 2 + y.2 ^ 2) / 8)
  have hy1 : 1 ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
  have hval : ∀ C' : ℝ, (∀ y : ℝ × ℝ, (1 + ‖y‖) * ‖iteratedFDeriv ℝ 0 (κ.e j) y‖ ≤
      C' * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) → C' ≤ C →
      ‖κ.e j y‖ ≤ C * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by
    intro C' h hC'
    have h1 := h y
    rw [norm_iteratedFDeriv_zero] at h1
    calc ‖κ.e j y‖ ≤ (1 + ‖y‖) * ‖κ.e j y‖ := le_mul_of_one_le_left (norm_nonneg _) hy1
      _ ≤ C' * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := h1
      _ ≤ C * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := mul_le_mul_of_nonneg_right hC' hE.le
  have hder : ∀ C' : ℝ, (∀ y : ℝ × ℝ, (1 + ‖y‖) * ‖iteratedFDeriv ℝ 1 (κ.e j) y‖ ≤
      C' * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) → C' ≤ C →
      ∀ k : Fin 2, ‖pdCx k (κ.e j) y‖ ≤ C * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by
    intro C' h hC' k
    have h1 := h y
    rw [norm_iteratedFDeriv_one] at h1
    have hdir : ‖B0579.dir k‖ ≤ 1 := by fin_cases k <;> simp [B0579.dir]
    have h2 : ‖pdCx k (κ.e j) y‖ ≤ ‖fderiv ℝ (κ.e j) y‖ := by
      unfold pdCx
      exact ((fderiv ℝ (κ.e j) y).le_opNorm _).trans
        (mul_le_of_le_one_right (norm_nonneg _) hdir)
    calc ‖pdCx k (κ.e j) y‖ ≤ ‖fderiv ℝ (κ.e j) y‖ := h2
      _ ≤ (1 + ‖y‖) * ‖fderiv ℝ (κ.e j) y‖ := le_mul_of_one_le_left (norm_nonneg _) hy1
      _ ≤ C' * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := h1
      _ ≤ C * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := mul_le_mul_of_nonneg_right hC' hE.le
  fin_cases j
  · exact ⟨hval C00 h00 (by linarith), hder C01 h01 (by linarith)⟩
  · exact ⟨hval C10 h10 (by linarith), hder C11 h11 (by linarith)⟩

/-- `∂_k (P_d e_j) = P_d (∂_k e_j)`. -/
theorem pdCx_perE_eq {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) {d : ℝ} (hd0 : 0 < d)
    (j k : Fin 2) (x : ℝ × ℝ) :
    pdCx k (perE κ d j) x = perSum d (pdCx k (κ.e j)) x := by
  have hsm_inf : ContDiff ℝ ∞ (κ.e j) := (OscillatorForceSub.seed_e_smooth_decay hκ).1 j
  have hsm2 : ContDiff ℝ 2 (κ.e j) := hsm_inf.of_le (by simp)
  obtain ⟨C_tr, _, h0, h1, _⟩ := OscillatorForceSub.seed_e_translate_bounds hκ j
  have h1' : ∀ z, ‖fderiv ℝ (κ.e j) z‖ ≤ C_tr * (1 + |z.1|) ^ (-(2 : ℝ)) := by
    intro z
    refine (le_mul_of_one_le_left (norm_nonneg _) ?_).trans (h1 z)
    linarith [norm_nonneg z]
  have hper_eq : perE κ d j =
      fun y => ∑' n : ℤ, κ.e j (y - UnforcedLeray.Gaussian.shiftVec d n) := by
    funext z
    unfold perE
    rw [perSum_eq_periodize, UnforcedLeray.Gaussian.periodize_eq]
  have hF := UnforcedLeray.Gaussian.hasFDerivAt_tsum_translates
    (hsm2.differentiable (by norm_num)) (by norm_num) hd0.ne' h0 h1' x
  have hfderiv_per : fderiv ℝ (perE κ d j) x =
      ∑' n : ℤ, fderiv ℝ (κ.e j) (x - UnforcedLeray.Gaussian.shiftVec d n) := by
    rw [hper_eq, hF.fderiv]
    simp_rw [fderiv_comp_sub]
  have hsumD : Summable (fun n : ℤ =>
      fderiv ℝ (κ.e j) (x - UnforcedLeray.Gaussian.shiftVec d n)) :=
    Summable.of_norm_bounded
      ((UnforcedLeray.Gaussian.summable_translate (s := 2) (by norm_num) hd0.ne' x.1).mul_left C_tr)
      (fun n => by rw [UnforcedLeray.Gaussian.sub_shiftVec]; exact h1' _)
  have hev : (∑' n : ℤ, fderiv ℝ (κ.e j) (x - UnforcedLeray.Gaussian.shiftVec d n))
      (B0579.dir k) =
      ∑' n : ℤ, fderiv ℝ (κ.e j) (x - UnforcedLeray.Gaussian.shiftVec d n) (B0579.dir k) :=
    (hsumD.hasSum.mapL (ContinuousLinearMap.apply ℝ ℂ (B0579.dir k))).tsum_eq.symm
  unfold pdCx perSum
  rw [hfderiv_per, hev, ← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr (fun n => ?_)
  change fderiv ℝ (κ.e j) (x - UnforcedLeray.Gaussian.shiftVec d (-n)) (B0579.dir k) =
    fderiv ℝ (κ.e j) (x.1 + (n : ℝ) * d, x.2) (B0579.dir k)
  congr 2
  ext <;> simp [UnforcedLeray.Gaussian.shiftVec, sub_eq_add_neg]

theorem perE_tails {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ d : ℝ, 1 ≤ d → ∀ (j : Fin 2), ∀ x ∈ B0579.cell d,
      ‖perE κ d j x - κ.e j x‖ ≤ T / d ^ 2 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16) ∧
      ∀ k : Fin 2, ‖pdCx k (perE κ d j) x - pdCx k (κ.e j) x‖ ≤
        T / d ^ 2 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16) := by
  obtain ⟨C_e, hCe, hseed⟩ := seed_bounds hκ
  refine ⟨256 * C_e * sZ, by have := sZ_nonneg; positivity, fun d hd j x hx => ?_⟩
  have hd0 : 0 < d := by linarith
  have hx1 := abs_fst_le_of_mem_cell hx
  refine ⟨?_, fun k => ?_⟩
  · exact tail_gauss hCe (fun z => (hseed j z).1) hd hx1
  · rw [pdCx_perE_eq hκ hd0 j k x]
    exact tail_gauss hCe (fun z => (hseed j z).2 k) hd hx1

/-! ## 2. The periodized Gaussian vortex -/

theorem v0_gauss : ∃ A : ℝ, 0 ≤ A ∧ ∀ z : ℝ × ℝ,
    ‖Train.v0 z‖ ≤ A * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := by
  obtain ⟨A, hA, hb⟩ := Train.norm_iteratedFDeriv_v0_le 0
  refine ⟨A, hA, fun z => ?_⟩
  have := hb z
  rwa [norm_iteratedFDeriv_zero] at this

theorem datum_tail_g : ∃ T_v : ℝ, 0 ≤ T_v ∧ ∀ d : ℝ, 1 ≤ d → ∀ y ∈ B0579.cell d,
    ‖Train.datum d y - Train.v0 y‖ ≤ T_v / d ^ 2 := by
  obtain ⟨A, hA, hb⟩ := v0_gauss
  refine ⟨256 * A * sZ, by have := sZ_nonneg; positivity, fun d hd y hy => ?_⟩
  have h := tail_gauss' hA hb hd (abs_fst_le_of_mem_cell hy)
  rw [Train.datum_apply]
  refine h.trans ?_
  have hE : Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg y.1, sq_nonneg y.2])
  have hq : 0 ≤ 256 * A * sZ / d ^ 2 := by have := sZ_nonneg; positivity
  exact mul_le_of_le_one_right hq hE

theorem curl_eq_pd (v : ℝ × ℝ → EuclideanSpace ℝ (Fin 2)) (hv : ContDiff ℝ 1 v) :
    UnforcedLeray.Cyl.curl v =
      fun z => B0579.pd 0 (fun w => v w 1) z - B0579.pd 1 (fun w => v w 0) z := by
  funext z
  rw [UnforcedLeray.B0238.curl_eq_fderiv hv z]
  simp [B0579.pd, B0579.dir]

theorem pd_sub' {A B : ℝ × ℝ → ℝ} {x : ℝ × ℝ} (j : Fin 2) (hA : DifferentiableAt ℝ A x)
    (hB : DifferentiableAt ℝ B x) :
    B0579.pd j (fun z => A z - B z) x = B0579.pd j A x - B0579.pd j B x := by
  unfold B0579.pd
  rw [fderiv_fun_sub hA hB]
  simp

theorem pd_curl_sub (u w : ℝ × ℝ → EuclideanSpace ℝ (Fin 2)) (hu : ContDiff ℝ ∞ u)
    (hw : ContDiff ℝ ∞ w) (l : Fin 2) (x : ℝ × ℝ) :
    B0579.pd l (UnforcedLeray.Cyl.curl u) x - B0579.pd l (UnforcedLeray.Cyl.curl w) x =
      B0579.pd l (UnforcedLeray.Cyl.curl (u - w)) x := by
  have hc2 : ∀ v : ℝ × ℝ → EuclideanSpace ℝ (Fin 2), ContDiff ℝ ∞ v → ∀ i : Fin 2,
      ContDiff ℝ 2 (fun z => v z i) := fun v hv i =>
    (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp (hv.of_le (by simp))
  have hdiff : ∀ v : ℝ × ℝ → EuclideanSpace ℝ (Fin 2), ContDiff ℝ ∞ v →
      ∀ (i j : Fin 2) (z : ℝ × ℝ),
      DifferentiableAt ℝ (fun z => B0579.pd j (fun w => v w i) z) z := fun v hv i j z =>
    TrainBddAux.pd_differentiableAt (hc2 v hv i) j z
  have huw : ContDiff ℝ ∞ (u - w) := hu.sub hw
  have hcu := curl_eq_pd u (hu.of_le (by simp))
  have hcw := curl_eq_pd w (hw.of_le (by simp))
  have hcuw := curl_eq_pd (u - w) (huw.of_le (by simp))
  have hcomp : ∀ (i j : Fin 2) (z : ℝ × ℝ), B0579.pd j (fun y => (u - w) y i) z =
      B0579.pd j (fun y => u y i) z - B0579.pd j (fun y => w y i) z := by
    intro i j z
    have : (fun y => (u - w) y i) = fun y => u y i - w y i := by
      funext y; simp [Pi.sub_apply]
    rw [this]
    exact pd_sub' j ((hc2 u hu i).differentiable (by norm_num) z)
      ((hc2 w hw i).differentiable (by norm_num) z)
  have hcurl : UnforcedLeray.Cyl.curl (u - w) =
      fun z => UnforcedLeray.Cyl.curl u z - UnforcedLeray.Cyl.curl w z := by
    rw [hcuw, hcu, hcw]
    funext z
    rw [hcomp 1 0 z, hcomp 0 1 z]
    ring
  rw [hcurl, pd_sub' l]
  · rw [hcu]; exact (hdiff u hu 1 0 x).sub (hdiff u hu 0 1 x)
  · rw [hcw]; exact (hdiff w hw 1 0 x).sub (hdiff w hw 0 1 x)

theorem g_bound : ∃ C_g : ℝ, 0 ≤ C_g ∧ ∀ (y : ℝ × ℝ) (k : Fin 2),
    |B0579.pd k Train.omega0 y| ≤ C_g * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by
  obtain ⟨A, hA, hbA⟩ := Train.norm_iteratedFDeriv_v0_le 2
  refine ⟨2 * A, by positivity, fun y k => ?_⟩
  rw [EulerErrorEig.omega0_eq_curl_v0]
  refine (TrainBddAux.pd_curl_le _ Train.contDiff_v0 k y).trans ?_
  have := hbA y
  linarith

theorem gradE_tail : ∃ T_g : ℝ, 0 ≤ T_g ∧ ∀ d : ℝ, 1 ≤ d → ∀ y ∈ B0579.cell d, ∀ k : Fin 2,
    |B0579.pd k (Cyl.curl (Train.datum d)) y - B0579.pd k Train.omega0 y| ≤
      T_g / d ^ 2 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by
  obtain ⟨A, hA, hbA⟩ := Train.norm_iteratedFDeriv_v0_le 2
  refine ⟨2 * (256 * A * sZ), by have := sZ_nonneg; positivity, fun d hd y hy k => ?_⟩
  have hd0 : d ≠ 0 := by positivity
  have hv0 : ContDiff ℝ ∞ Train.v0 := Train.contDiff_v0
  have hdat : ContDiff ℝ ∞ (Train.datum d) := Train.datum_contDiff hd0
  rw [EulerErrorEig.omega0_eq_curl_v0, pd_curl_sub _ _ hdat hv0 k y]
  have hle := TrainBddAux.pd_curl_le (Train.datum d - Train.v0) (hdat.sub hv0) k y
  rw [iteratedFDeriv_sub_apply (hdat.contDiffAt.of_le (by simp))
    (hv0.contDiffAt.of_le (by simp))] at hle
  have hjet : iteratedFDeriv ℝ 2 (Train.datum d) y =
      ∑' n : ℤ, iteratedFDeriv ℝ 2 Train.v0 (y.1 - n * d, y.2) := by
    have h := congrFun (Train.jet_datum hd0 2) y
    simpa only [Train.jet, Gaussian.periodize] using h
  rw [hjet] at hle
  have ht := tail_gauss' hA hbA hd (abs_fst_le_of_mem_cell hy)
  refine hle.trans ?_
  have : 2 * (256 * A * sZ / d ^ 2 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16)) =
      2 * (256 * A * sZ) / d ^ 2 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by ring
  linarith

/-! ## 3. Velocity bounds -/

theorem planar_vel_bound {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) :
    ∃ C_U : ℝ, 0 ≤ C_U ∧ ∀ (j : Fin 2) (y : ℝ × ℝ) (k : Fin 2),
      ‖kerVelPlanarCx (κ.e j) y k‖ ≤ C_U := by
  obtain ⟨C_e, hCe, hseed⟩ := seed_bounds hκ
  set f : Fin 2 → ℂ → ℂ := fun j w => κ.e j (B0009.toPlane w) with hf
  have hfc : ∀ j, Continuous (f j) := fun j =>
    (κ.e_cont j).comp (Complex.continuous_re.prodMk Complex.continuous_im)
  have he_sup : ∀ j z, ‖κ.e j z‖ ≤ C_e := fun j z =>
    (hseed j z).1.trans (mul_le_of_le_one_right hCe (Real.exp_le_one_iff.2 (by
      have : 0 ≤ z.1 ^ 2 + z.2 ^ 2 := by positivity
      linarith)))
  have he_int : ∀ j, Integrable (κ.e j) := fun j =>
    Integrable.mono' ((integrable_gauss (a := 8) (by norm_num)).const_mul C_e)
      (κ.e_cont j).aestronglyMeasurable (Eventually.of_forall fun z => (hseed j z).1)
  have hfi : ∀ j, Integrable (f j) := fun j => integrable_toPlane (he_int j)
  set Kb : Fin 2 → ℝ := fun i => ∫ t in Metric.ball (0 : ℂ) 1, ‖B0009.kernel i t‖ with hKb
  have hKb0 : ∀ i, 0 ≤ Kb i := fun i => integral_nonneg (fun t => norm_nonneg _)
  set If : Fin 2 → ℝ := fun j => ∫ t, ‖f j t‖ with hIf
  have hIf0 : ∀ j, 0 ≤ If j := fun j => integral_nonneg (fun t => norm_nonneg _)
  refine ⟨C_e * (Kb 0 + Kb 1) + (2 * Real.pi)⁻¹ * (If 0 + If 1), by
    have := hKb0 0; have := hKb0 1; have := hIf0 0; have := hIf0 1; positivity,
    fun j y k => ?_⟩
  have h := norm_biotSavart_le (hfc j) (fun z => he_sup j _) (hfi j) k (planeToC y)
  have hKk : Kb k ≤ Kb 0 + Kb 1 := by
    fin_cases k
    · have := hKb0 1; simp only [Fin.zero_eta]; linarith
    · have := hKb0 0; simp only [Fin.mk_one]; linarith
  have hIj : If j ≤ If 0 + If 1 := by
    fin_cases j
    · have := hIf0 1; simp only [Fin.zero_eta]; linarith
    · have := hIf0 0; simp only [Fin.mk_one]; linarith
  unfold kerVelPlanarCx
  refine h.trans ?_
  have hpi : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
  have h1 : C_e * Kb k ≤ C_e * (Kb 0 + Kb 1) := mul_le_mul_of_nonneg_left hKk hCe
  have h2 : (2 * Real.pi)⁻¹ * If j ≤ (2 * Real.pi)⁻¹ * (If 0 + If 1) :=
    mul_le_mul_of_nonneg_left hIj hpi
  simp only [hKb, hIf] at h1 h2
  linarith

/-! ## 4. The pointwise residual -/

theorem norm_five (A B C D E : ℂ) : ‖-A - B - C - D - E‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ + ‖E‖ := by
  calc ‖-A - B - C - D - E‖ ≤ ‖-A - B - C - D‖ + ‖E‖ := norm_sub_le _ _
    _ ≤ ‖-A - B - C‖ + ‖D‖ + ‖E‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ ‖-A - B‖ + ‖C‖ + ‖D‖ + ‖E‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ ‖-A‖ + ‖B‖ + ‖C‖ + ‖D‖ + ‖E‖ := by gcongr; exact norm_sub_le _ _
    _ = ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ + ‖E‖ := by rw [norm_neg]

theorem norm_pair (x y z w : ℂ) : ‖x * y + z * w‖ ≤ ‖x‖ * ‖y‖ + ‖z‖ * ‖w‖ := by
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]

theorem norm_seedModeEigen_le (lam : ℂ) (j : Fin 2) : ‖seedModeEigen lam j‖ ≤ ‖lam‖ := by
  unfold seedModeEigen
  split_ifs
  · exact le_rfl
  · rw [Complex.norm_conj]

theorem norm_comp_sub_le (u v : EuclideanSpace ℝ (Fin 2)) (k : Fin 2) :
    ‖(((u k : ℝ) : ℂ) - ((v k : ℝ) : ℂ))‖ ≤ ‖u - v‖ := by
  rw [← Complex.ofReal_sub, Complex.norm_real]
  have := PiLp.norm_apply_le (u - v) k
  simpa using this

theorem norm_comp_le (u : EuclideanSpace ℝ (Fin 2)) (k : Fin 2) :
    ‖((u k : ℝ) : ℂ)‖ ≤ ‖u‖ := by
  rw [Complex.norm_real]
  exact PiLp.norm_apply_le u k

/-- **Pointwise Gaussian-cylinder residual** (SP 2866-2888). -/
theorem residual_pointwise {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) (lam : ℂ) :
    ∃ C_R : ℝ, 0 ≤ C_R ∧ ∀ d : ℝ, 1 ≤ d → ∀ j : Fin 2, ∀ y ∈ B0579.cell d,
      ‖(movLGauss d (perE κ d j) y - movLPlanar (κ.e j) y) -
          seedModeEigen lam j * (perE κ d j y - κ.e j y)‖ ≤
        C_R * (1 / d ^ 2) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by
  obtain ⟨C_e, hCe, hseed⟩ := seed_bounds hκ
  obtain ⟨T, hT, htail⟩ := perE_tails hκ
  obtain ⟨T_v, hTv, hdat⟩ := datum_tail_g
  obtain ⟨T_g, hTg, hgrad⟩ := gradE_tail
  obtain ⟨C_g, hCg, hg⟩ := g_bound
  obtain ⟨A₀, hA₀, hv0⟩ := v0_gauss
  obtain ⟨C_U, hCU, hU⟩ := planar_vel_bound hκ
  obtain ⟨C_vel, hCvel, hV⟩ := EulerErrorSub.kerVelCx_perE_bound hκ
  obtain ⟨M_E, hME, hME_bd⟩ := EulerErrorSub.perE_and_pdCx_gauss_bounds hκ
  obtain ⟨K_V, hKV, hVC⟩ := vel_compare
  set X : ℝ := 4 * K_V * (T + C_e) * C_g + 1024 * (C_vel + C_U) * C_g with hX
  set C_R : ℝ := 2 * (T_v * M_E + A₀ * T + X + C_vel * T_g) + ‖lam‖ * T with hCR
  refine ⟨C_R, by positivity, fun d hd j y hy => ?_⟩
  have hd0 : 0 < d := by linarith
  set q : ℝ := 1 / d ^ 2 with hq
  have hq0 : 0 < q := by positivity
  set Γ : ℝ := Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) with hΓ
  have hΓ0 : 0 < Γ := Real.exp_pos _
  have hΓ1 : Γ ≤ 1 := Real.exp_le_one_iff.2 (by
    have : 0 ≤ y.1 ^ 2 + y.2 ^ 2 := by positivity
    linarith)
  have hTd : ∀ S : ℝ, S / d ^ 2 = S * q := fun S => by rw [hq]; ring
  set W := perE κ d j with hW
  set e := κ.e j with he
  obtain ⟨hWe, hpWe⟩ := htail d hd j y hy
  obtain ⟨hME_cell, -, hME_pd⟩ := hME_bd d hd j
  -- the individual bounds
  have hA_k : ∀ k : Fin 2,
      ‖((Train.datum d y k : ℝ) : ℂ) - ((Train.v0 y k : ℝ) : ℂ)‖ * ‖pdCx k W y‖ +
        ‖((Train.v0 y k : ℝ) : ℂ)‖ * ‖pdCx k W y - pdCx k e y‖ ≤
      (T_v * M_E + A₀ * T) * q * Γ := by
    intro k
    have h1 : ‖((Train.datum d y k : ℝ) : ℂ) - ((Train.v0 y k : ℝ) : ℂ)‖ ≤ T_v * q := by
      refine (norm_comp_sub_le _ _ k).trans ?_
      rw [← hTd]; exact hdat d hd y hy
    have h2 : ‖pdCx k W y‖ ≤ M_E * Γ := hME_pd k y hy
    have h3 : ‖((Train.v0 y k : ℝ) : ℂ)‖ ≤ A₀ := by
      refine (norm_comp_le _ k).trans ((hv0 y).trans ?_)
      exact mul_le_of_le_one_right hA₀ (Real.exp_le_one_iff.2 (by
        have : 0 ≤ y.1 ^ 2 + y.2 ^ 2 := by positivity
        linarith))
    have h4 : ‖pdCx k W y - pdCx k e y‖ ≤ T * q * Γ := by
      rw [← hTd]; exact hpWe k
    calc ‖((Train.datum d y k : ℝ) : ℂ) - ((Train.v0 y k : ℝ) : ℂ)‖ * ‖pdCx k W y‖ +
          ‖((Train.v0 y k : ℝ) : ℂ)‖ * ‖pdCx k W y - pdCx k e y‖
        ≤ (T_v * q) * (M_E * Γ) + A₀ * (T * q * Γ) := by
          gcongr
      _ = (T_v * M_E + A₀ * T) * q * Γ := by ring
  have hρsq : y.1 ^ 2 + y.2 ^ 2 = ‖planeToC y‖ ^ 2 := norm_planeToC_sq' y
  set ρ : ℝ := ‖planeToC y‖ with hρ
  have hρ0 : 0 ≤ ρ := norm_nonneg _
  have hC_k : ∀ k : Fin 2,
      ‖kerVelCx d W y k - kerVelPlanarCx e y k‖ * ‖((B0579.pd k Train.omega0 y : ℝ) : ℂ)‖ +
        ‖kerVelCx d W y k‖ * ‖((B0579.pd k (Cyl.curl (Train.datum d)) y : ℝ) : ℂ) -
          ((B0579.pd k Train.omega0 y : ℝ) : ℂ)‖ ≤
      (X + C_vel * T_g) * q * Γ := by
    intro k
    have hgk : ‖((B0579.pd k Train.omega0 y : ℝ) : ℂ)‖ ≤
        C_g * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact hg y k
    have hpart1 : ‖kerVelCx d W y k - kerVelPlanarCx e y k‖ *
        ‖((B0579.pd k Train.omega0 y : ℝ) : ℂ)‖ ≤ X * q * Γ := by
      by_cases hY : ρ ≤ d / 8
      · have hvc := hVC hd hCe hT (κ.e_cont j) (EulerErrorSub.continuous_perE hκ hd0 j)
          (fun z => (hseed j z).1) (fun z hz => (htail d hd j z hz).1) y k hY
        have hpoly : (1 + ρ) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) ≤ 4 * Γ := by
          have h1 := one_add_mul_exp_le hρ0
          have hsplit : Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) =
              Real.exp (-(ρ ^ 2) / 16) * Real.exp (-(ρ ^ 2) / 16) := by
            rw [hρsq, ← Real.exp_add]; ring_nf
          have hΓρ : Γ = Real.exp (-(ρ ^ 2) / 16) := by rw [hΓ, hρsq]
          rw [hsplit, hΓρ, ← mul_assoc]
          exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        calc ‖kerVelCx d W y k - kerVelPlanarCx e y k‖ * ‖((B0579.pd k Train.omega0 y : ℝ) : ℂ)‖
            ≤ (K_V * (T + C_e) * (1 + ρ) / d ^ 2) *
                (C_g * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) :=
              mul_le_mul hvc hgk (norm_nonneg _) (by positivity)
          _ = K_V * (T + C_e) * C_g * q * ((1 + ρ) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) := by
              rw [hq]; ring
          _ ≤ K_V * (T + C_e) * C_g * q * (4 * Γ) := by gcongr
          _ = (4 * K_V * (T + C_e) * C_g) * q * Γ := by ring
          _ ≤ X * q * Γ := by
              gcongr
              rw [hX]
              have : 0 ≤ 1024 * (C_vel + C_U) * C_g := by positivity
              linarith
      · have hρd : d / 8 ≤ ρ := le_of_lt (lt_of_not_ge hY)
        have hVU : ‖kerVelCx d W y k - kerVelPlanarCx e y k‖ ≤ C_vel + C_U :=
          (norm_sub_le _ _).trans (add_le_add (hV d hd j k y) (hU j y k))
        have hsq : (d / 8) ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (by positivity) hρd 2
        have hE8 : Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) ≤ Γ * (1024 * q) := by
          have h1 := exp_split (r := ρ) (ρ := d / 8) hsq
          have h2 : Real.exp (-((d / 8) ^ 2) / 16) ≤ 1024 * q := by
            have := exp_neg_le_inv (x := d ^ 2 / 1024) (by positivity)
            calc Real.exp (-((d / 8) ^ 2) / 16) = Real.exp (-(d ^ 2 / 1024)) := by ring_nf
              _ ≤ 1 / (d ^ 2 / 1024) := this
              _ = 1024 * q := by rw [hq]; field_simp
          have hΓρ : Γ = Real.exp (-(ρ ^ 2) / 16) := by rw [hΓ, hρsq]
          rw [hρsq, hΓρ]
          exact h1.trans (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le)
        calc ‖kerVelCx d W y k - kerVelPlanarCx e y k‖ * ‖((B0579.pd k Train.omega0 y : ℝ) : ℂ)‖
            ≤ (C_vel + C_U) * (C_g * (Γ * (1024 * q))) :=
              mul_le_mul hVU (hgk.trans (mul_le_mul_of_nonneg_left hE8 hCg)) (norm_nonneg _)
                (by positivity)
          _ = (1024 * (C_vel + C_U) * C_g) * q * Γ := by ring
          _ ≤ X * q * Γ := by
              gcongr
              rw [hX]
              have : 0 ≤ 4 * K_V * (T + C_e) * C_g := by positivity
              linarith
    have hpart2 : ‖kerVelCx d W y k‖ * ‖((B0579.pd k (Cyl.curl (Train.datum d)) y : ℝ) : ℂ) -
        ((B0579.pd k Train.omega0 y : ℝ) : ℂ)‖ ≤ C_vel * T_g * q * Γ := by
      have h1 : ‖((B0579.pd k (Cyl.curl (Train.datum d)) y : ℝ) : ℂ) -
          ((B0579.pd k Train.omega0 y : ℝ) : ℂ)‖ ≤ T_g * q * Γ := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, ← hTd]
        exact hgrad d hd y hy k
      calc ‖kerVelCx d W y k‖ * ‖((B0579.pd k (Cyl.curl (Train.datum d)) y : ℝ) : ℂ) -
            ((B0579.pd k Train.omega0 y : ℝ) : ℂ)‖ ≤ C_vel * (T_g * q * Γ) :=
            mul_le_mul (hV d hd j k y) h1 (norm_nonneg _) hCvel
        _ = C_vel * T_g * q * Γ := by ring
    linarith
  have hE_term : ‖seedModeEigen lam j * (W y - e y)‖ ≤ ‖lam‖ * T * q * Γ := by
    rw [norm_mul]
    have h1 : ‖W y - e y‖ ≤ T * q * Γ := by rw [← hTd]; exact hWe
    calc ‖seedModeEigen lam j‖ * ‖W y - e y‖ ≤ ‖lam‖ * (T * q * Γ) :=
          mul_le_mul (norm_seedModeEigen_le lam j) h1 (norm_nonneg _) (norm_nonneg _)
      _ = ‖lam‖ * T * q * Γ := by ring
  have hid : (movLGauss d W y - movLPlanar e y) - seedModeEigen lam j * (W y - e y) =
      -((((Train.datum d y 0 : ℝ) : ℂ) - ((Train.v0 y 0 : ℝ) : ℂ)) * pdCx 0 W y +
          ((Train.v0 y 0 : ℝ) : ℂ) * (pdCx 0 W y - pdCx 0 e y)) -
        ((((Train.datum d y 1 : ℝ) : ℂ) - ((Train.v0 y 1 : ℝ) : ℂ)) * pdCx 1 W y +
          ((Train.v0 y 1 : ℝ) : ℂ) * (pdCx 1 W y - pdCx 1 e y)) -
        ((kerVelCx d W y 0 - kerVelPlanarCx e y 0) * ((B0579.pd 0 Train.omega0 y : ℝ) : ℂ) +
          kerVelCx d W y 0 * (((B0579.pd 0 (Cyl.curl (Train.datum d)) y : ℝ) : ℂ) -
            ((B0579.pd 0 Train.omega0 y : ℝ) : ℂ))) -
        ((kerVelCx d W y 1 - kerVelPlanarCx e y 1) * ((B0579.pd 1 Train.omega0 y : ℝ) : ℂ) +
          kerVelCx d W y 1 * (((B0579.pd 1 (Cyl.curl (Train.datum d)) y : ℝ) : ℂ) -
            ((B0579.pd 1 Train.omega0 y : ℝ) : ℂ))) -
        seedModeEigen lam j * (W y - e y) := by
    unfold movLGauss movLPlanar
    ring
  rw [hid]
  refine (norm_five _ _ _ _ _).trans ?_
  have hA0 := (norm_pair _ _ _ _).trans (hA_k 0)
  have hA1 := (norm_pair _ _ _ _).trans (hA_k 1)
  have hC0 := (norm_pair _ _ _ _).trans (hC_k 0)
  have hC1 := (norm_pair _ _ _ _).trans (hC_k 1)
  have hfin : C_R * q * Γ = 2 * ((T_v * M_E + A₀ * T) * q * Γ) +
      2 * ((X + C_vel * T_g) * q * Γ) + ‖lam‖ * T * q * Γ := by
    rw [hCR]; ring
  rw [hfin]
  linarith

/-! ## 5. The `X_{m,d}` bound -/

/-- **Gaussian-cylinder eigenmode residual in `X_{m,d}`** (SP 2866-2888, 2991-2995). -/
theorem movEulerGaussTailBound_seed {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ)
    (lam : ℂ) (m : ℝ) (hm : 8 < m) :
    ∃ C_G D_G : ℝ, 0 ≤ C_G ∧ 1 ≤ D_G ∧
      ∀ d : ℝ, D_G ≤ d → ∀ j : Fin 2,
        xNorm d m (fun y =>
          (movLGauss d (perE κ d j) y - movLPlanar (κ.e j) y) -
            seedModeEigen lam j * (perE κ d j y - κ.e j y)) ≤
          ENNReal.ofReal (C_G / d ^ 2) := by
  obtain ⟨C_R, hCR, hres⟩ := residual_pointwise hκ lam
  obtain ⟨K_m, hKm, hxN⟩ := xNorm_le_of_gauss (m := m) (by linarith)
  refine ⟨C_R * K_m, 1, by positivity, le_rfl, fun d hd j => ?_⟩
  have hd0 : 0 < d := by linarith
  have h := hxN d (C_R * (1 / d ^ 2)) _ (by positivity) (fun x hx => hres d hd j x hx)
  refine h.trans (le_of_eq ?_)
  congr 1
  ring

/-- `MovEulerGaussSubBound κ` for the Part I seed kernels. -/
theorem movEulerGaussSubBound_seed (κ : PlanarFrameKernels) (hκ : IsSeedKernels κ) :
    MovEulerGaussSubBound κ := by
  intro lam h hh ℓ hSeed he0 he1 m hm
  have heig := EulerErrorEig.seedPlanarPointwiseEigen κ lam h hh ℓ hSeed he0 he1
  obtain ⟨C_G, D_G, hCG, hDG, hbd⟩ := movEulerGaussTailBound_seed hκ lam m hm
  refine ⟨C_G, D_G, hCG, hDG, fun d hd j => ?_⟩
  have hfun : movEulerResGauss κ lam d j = fun y =>
      (movLGauss d (perE κ d j) y - movLPlanar (κ.e j) y) -
        seedModeEigen lam j * (perE κ d j y - κ.e j y) := by
    funext y
    unfold movEulerResGauss
    rw [heig j y]
    ring
  rw [hfun]
  exact hbd d hd j

end EulerErrorTail

end UnforcedLeray.Short.IIIa
