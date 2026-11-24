import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_b0
import UnforcedLeray.Lib.PlanarSectorsB.TransportDuhamel
import UnforcedLeray.Short.PartI.Tasks.MemHjMGaussian
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
# Planar frame objects on `L²_m` (Leaf B3, SP 2926-2935)

`planarE κ m i` is the growing vector `e_i` as an element of `L²_m` (Gaussian tails `κ.e_decay`),
`planarEll κ hm i` the bounded planar pairing `ℓ_i = ∫ λ_i ·` (`κ.lamP` bounded, `m > 1`),
`planarProj κ hm = Σ ℓ_i(·) e_i` (SP 2926-2927), with `ℓ_i(e_j) = δ_ij` (`κ.biorth`).
`A0_eq_of`: the planar damped interaction is `couplingW + Σ (γ - 1 - λ_i) ℓ_i(·) e_i` on all of
`L²_m` (density of smooth compactly supported fields, `Lp.dense_hasCompactSupport_contDiff`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa.PlanarDysonL3

open UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit3.PlanarB

theorem mp_planeToC :
    MeasurePreserving planeToC (volume : Measure (ℝ × ℝ)) (volume : Measure ℂ) :=
  Complex.volume_preserving_equiv_real_prod.symm

theorem me_planeToC : MeasurableEmbedding planeToC :=
  Complex.measurableEquivRealProd.symm.measurableEmbedding

theorem cToPlane_planeToC' (y : ℝ × ℝ) : cToPlane (planeToC y) = y := rfl

theorem integral_planeToC' (g : ℂ → ℂ) : ∫ y, g (planeToC y) = ∫ z, g z :=
  mp_planeToC.integral_comp me_planeToC g

theorem ae_comp_planeToC {f g : ℂ → ℂ} (h : f =ᵐ[volume] g) :
    (fun y => f (planeToC y)) =ᵐ[volume] fun y => g (planeToC y) :=
  mp_planeToC.quasiMeasurePreserving.ae_eq_comp h

/-! ### The growing vectors in `L²_m` -/

theorem poly_gauss_le (K : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (1 + t) ^ K * Real.exp (-(t ^ 2) / 8) ≤
      Real.exp (4 * (K : ℝ) ^ 2) * Real.exp (-(t ^ 2) / 16) := by
  have h1 : (1 + t) ^ K ≤ Real.exp t ^ K :=
    pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp t]) K
  have h1' : Real.exp t ^ K = Real.exp ((K : ℝ) * t) := (Real.exp_nat_mul t K).symm
  have h2 : Real.exp ((K : ℝ) * t) * Real.exp (-(t ^ 2) / 8) ≤
      Real.exp (4 * (K : ℝ) ^ 2) * Real.exp (-(t ^ 2) / 16) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (t / 4 - 2 * (K : ℝ))]
  calc (1 + t) ^ K * Real.exp (-(t ^ 2) / 8)
      ≤ Real.exp ((K : ℝ) * t) * Real.exp (-(t ^ 2) / 8) :=
        mul_le_mul_of_nonneg_right (h1.trans h1'.le) (Real.exp_pos _).le
    _ ≤ _ := h2

theorem memLp_gauss16 : MemLp (fun z : ℂ => Real.exp (-(‖z‖ ^ 2) / 16)) 2 volume := by
  have hmeas : AEStronglyMeasurable (fun z : ℂ => Real.exp (-(‖z‖ ^ 2) / 16)) volume :=
    (by fun_prop : Continuous fun z : ℂ => Real.exp (-(‖z‖ ^ 2) / 16)).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  refine (PartI.s03_integrable_exp_neg_mul_sq (b := 1 / 8) (by norm_num)).congr
    (Filter.Eventually.of_forall fun z => ?_)
  dsimp only
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem continuous_cToPlane' : Continuous cToPlane := by
  unfold cToPlane
  fun_prop

theorem memLp_planarE (κ : PlanarFrameKernels) (m : ℝ) (i : Fin 2) :
    MemLp (fun z : ℂ => κ.e i (cToPlane z)) 2 (Planar.wMeasure m) := by
  obtain ⟨C, hC⟩ := κ.e_decay
  have hcont : Continuous fun z : ℂ => κ.e i (cToPlane z) :=
    (κ.e_cont i).comp continuous_cToPlane'
  rw [Planar.wMeasure_eq_B0008, B0008.memLp_wMeasure_iff]
  refine MemLp.mono' (memLp_gauss16.const_mul (|C| * Real.exp (4 * ((⌈m⌉₊ : ℕ) : ℝ) ^ 2)))
    ((B0008.continuous_bracket_rpow m).smul hcont).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  have hbr0 : 0 ≤ B0008.bracket z ^ m := Real.rpow_nonneg (B0008.bracket_pos z).le m
  have he : ‖κ.e i (cToPlane z)‖ ≤ |C| * Real.exp (-(‖z‖ ^ 2) / 8) := by
    have h := hC i (cToPlane z)
    have hn : (cToPlane z).1 ^ 2 + (cToPlane z).2 ^ 2 = ‖z‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [cToPlane]
      ring
    rw [hn] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le)
  show ‖B0008.bracket z ^ m • κ.e i (cToPlane z)‖ ≤
    |C| * Real.exp (4 * ((⌈m⌉₊ : ℕ) : ℝ) ^ 2) * Real.exp (-(‖z‖ ^ 2) / 16)
  calc ‖B0008.bracket z ^ m • κ.e i (cToPlane z)‖
      = B0008.bracket z ^ m * ‖κ.e i (cToPlane z)‖ := by
        rw [norm_smul, Real.norm_of_nonneg hbr0]
    _ ≤ (1 + ‖z‖) ^ ⌈m⌉₊ * (|C| * Real.exp (-(‖z‖ ^ 2) / 8)) :=
        mul_le_mul (PartI.s03_bracket_rpow_le m z) he (norm_nonneg _)
          (pow_nonneg (by positivity) _)
    _ = |C| * ((1 + ‖z‖) ^ ⌈m⌉₊ * Real.exp (-(‖z‖ ^ 2) / 8)) := by ring
    _ ≤ |C| * (Real.exp (4 * ((⌈m⌉₊ : ℕ) : ℝ) ^ 2) * Real.exp (-(‖z‖ ^ 2) / 16)) :=
        mul_le_mul_of_nonneg_left (poly_gauss_le _ (norm_nonneg z)) (abs_nonneg C)
    _ = |C| * Real.exp (4 * ((⌈m⌉₊ : ℕ) : ℝ) ^ 2) * Real.exp (-(‖z‖ ^ 2) / 16) := by ring

/-- The growing vector `e_i ∈ L²_m`. -/
def planarE (κ : PlanarFrameKernels) (m : ℝ) (i : Fin 2) : Planar.L2w m :=
  (memLp_planarE κ m i).toLp _

theorem coeFn_planarE (κ : PlanarFrameKernels) (m : ℝ) (i : Fin 2) :
    ⇑(planarE κ m i) =ᵐ[Planar.wMeasure m] fun z => κ.e i (cToPlane z) :=
  (memLp_planarE κ m i).coeFn_toLp

theorem coeFn_planarE_vol (κ : PlanarFrameKernels) (m : ℝ) (i : Fin 2) :
    ⇑(planarE κ m i) =ᵐ[volume] fun z => κ.e i (cToPlane z) :=
  (Planar.volume_ac m).ae_le (coeFn_planarE κ m i)

/-! ### The planar pairings -/

theorem memLp_inv_bracket {m : ℝ} (hm : 1 < m) :
    MemLp (fun z : ℂ => (B0008.bracket z ^ m)⁻¹) 2 volume := by
  have hc : Continuous fun z : ℂ => (B0008.bracket z ^ m)⁻¹ :=
    (B0008.continuous_bracket_rpow m).inv₀ fun z =>
      (Real.rpow_pos_of_pos (B0008.bracket_pos z) m).ne'
  rw [memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable]
  have hI := integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) (r := 2 * m)
    (by rw [Complex.finrank_real_complex]; push_cast; linarith)
  refine hI.congr (Filter.Eventually.of_forall fun z => ?_)
  dsimp only
  have hb := B0008.bracket_rpow_sq m z
  have hpos : 0 < 1 + ‖z‖ ^ 2 := by positivity
  rw [Real.norm_of_nonneg (inv_nonneg.2 (Real.rpow_nonneg (B0008.bracket_pos z).le m)), inv_pow, hb,
    ← Real.rpow_neg hpos.le]
  congr 1
  ring

theorem memLp_dualFun_lamP (κ : PlanarFrameKernels) {m : ℝ} (hm : 1 < m) (i : Fin 2) :
    MemLp (B0008.dualFun m fun z => κ.lamP i (cToPlane z)) 2 (B0008.wMeasure m) := by
  obtain ⟨C, hC⟩ := κ.lamP_decay
  have hψ : Continuous fun z : ℂ => κ.lamP i (cToPlane z) :=
    (κ.lamP_cont i).comp continuous_cToPlane'
  have hcd : Continuous (B0008.dualFun m fun z => κ.lamP i (cToPlane z)) := by
    unfold B0008.dualFun
    exact (continuous_star.comp hψ).mul (Complex.continuous_ofReal.comp
      ((B0008.continuous_coe_density m).inv₀ fun y => (B0008.density_pos m y).ne'))
  rw [B0008.memLp_wMeasure_iff]
  refine MemLp.mono' ((memLp_inv_bracket hm).const_mul |C|)
    ((B0008.continuous_bracket_rpow m).smul hcd).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  have hbr : 0 < B0008.bracket z ^ m := Real.rpow_pos_of_pos (B0008.bracket_pos z) m
  have hden : (B0008.density m z : ℝ) = (B0008.bracket z ^ m) ^ 2 := by
    rw [B0008.coe_density, B0008.bracket_rpow_sq]
  have hψb : ‖κ.lamP i (cToPlane z)‖ ≤ |C| := by
    have h := hC i (cToPlane z)
    have h0 : 0 ≤ (1 + |(cToPlane z).1| + |(cToPlane z).2|)⁻¹ := by positivity
    have h1 : (1 + |(cToPlane z).1| + |(cToPlane z).2|)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (by linarith [abs_nonneg (cToPlane z).1, abs_nonneg (cToPlane z).2])
    have h2 : (1 + |(cToPlane z).1| + |(cToPlane z).2|)⁻¹ ^ 2 ≤ 1 := pow_le_one₀ h0 h1
    calc ‖κ.lamP i (cToPlane z)‖ ≤ C * (1 + |(cToPlane z).1| + |(cToPlane z).2|)⁻¹ ^ 2 := h
      _ ≤ |C| * (1 + |(cToPlane z).1| + |(cToPlane z).2|)⁻¹ ^ 2 :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ ≤ |C| * 1 := mul_le_mul_of_nonneg_left h2 (abs_nonneg C)
      _ = |C| := mul_one _
  show ‖B0008.bracket z ^ m • B0008.dualFun m (fun z => κ.lamP i (cToPlane z)) z‖ ≤
    |C| * (B0008.bracket z ^ m)⁻¹
  rw [norm_smul, Real.norm_of_nonneg hbr.le, B0008.dualFun, norm_mul, norm_star,
    Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 (B0008.density_pos m z).le), hden]
  calc B0008.bracket z ^ m * (‖κ.lamP i (cToPlane z)‖ * ((B0008.bracket z ^ m) ^ 2)⁻¹)
      = ‖κ.lamP i (cToPlane z)‖ * (B0008.bracket z ^ m)⁻¹ := by
        field_simp
    _ ≤ |C| * (B0008.bracket z ^ m)⁻¹ :=
        mul_le_mul_of_nonneg_right hψb (inv_nonneg.2 hbr.le)

/-- The planar pairing `ℓ_i = ∫ λ_i ·` as a bounded functional on `L²_m`. -/
def planarEll (κ : PlanarFrameKernels) {m : ℝ} (hm : 1 < m) (i : Fin 2) :
    Planar.L2w m →L[ℂ] ℂ :=
  innerSL ℂ (B0008.dualVec m (fun z => κ.lamP i (cToPlane z)) (memLp_dualFun_lamP κ hm i))

theorem planarEll_apply (κ : PlanarFrameKernels) {m : ℝ} (hm : 1 < m) (i : Fin 2)
    (W : Planar.L2w m) : planarEll κ hm i W = ∫ y, κ.lamP i y * W (planeToC y) := by
  have h := B0008.inner_dualVec m (memLp_dualFun_lamP κ hm i) W
  have h2 : planarEll κ hm i W = ∫ y, W y * κ.lamP i (cToPlane y) := h
  rw [h2, ← integral_planeToC']
  congr 1
  funext y
  rw [cToPlane_planeToC', mul_comm]

theorem planarEll_eq_lamPair (κ : PlanarFrameKernels) {m : ℝ} (hm : 1 < m) (i : Fin 2)
    {W : Planar.L2w m} {Φ : ℂ → ℂ} (hW : ⇑W =ᵐ[volume] Φ) :
    planarEll κ hm i W = planarLamPair κ i Φ := by
  rw [planarEll_apply, planarLamPair]
  apply integral_congr_ae
  filter_upwards [ae_comp_planeToC hW] with y hy
  rw [hy]

/-- Biorthogonality `ℓ_i(e_j) = δ_ij` (`κ.biorth`). -/
theorem planarEll_planarE (κ : PlanarFrameKernels) {m : ℝ} (hm : 1 < m) (i j : Fin 2) :
    planarEll κ hm i (planarE κ m j) = if i = j then 1 else 0 := by
  rw [planarEll_eq_lamPair κ hm i (coeFn_planarE_vol κ m j), planarLamPair, ← κ.biorth i j]
  rfl

/-- The rank-two projection `𝒫 = Σ ℓ_i(·) e_i` (SP 2926-2927). -/
def planarProj (κ : PlanarFrameKernels) {m : ℝ} (hm : 1 < m) :
    Planar.L2w m →L[ℂ] Planar.L2w m :=
  ∑ i : Fin 2, (planarEll κ hm i).smulRight (planarE κ m i)

theorem planarProj_apply (κ : PlanarFrameKernels) {m : ℝ} (hm : 1 < m) (W : Planar.L2w m) :
    planarProj κ hm W = ∑ i : Fin 2, planarEll κ hm i W • planarE κ m i := by
  simp [planarProj, ContinuousLinearMap.smulRight_apply]

theorem planarEll_planarProj (κ : PlanarFrameKernels) {m : ℝ} (hm : 1 < m) (i : Fin 2)
    (W : Planar.L2w m) : planarEll κ hm i (planarProj κ hm W) = planarEll κ hm i W := by
  rw [planarProj_apply, map_sum]
  simp only [map_smul, planarEll_planarE, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem planarProj_planarE (κ : PlanarFrameKernels) {m : ℝ} (hm : 1 < m) (i : Fin 2) :
    planarProj κ hm (planarE κ m i) = planarE κ m i := by
  rw [planarProj_apply]
  simp only [planarEll_planarE, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-! ### The planar damped interaction on all of `L²_m` -/

/-- `c_i = (γ - 1) - λ_i`. -/
def dampCoef (P : UnforcedLeray.Blueprint.Planar.PlanarData) (lam : ℂ) (i : Fin 2) : ℂ :=
  ((P.eigenvalue.re - 1 : ℝ) : ℂ) - seedEigen lam i

/-- The explicit operator `𝒜 + Σ_i c_i ℓ_i(·) e_i`. -/
def dampOp (κ : PlanarFrameKernels) (P : UnforcedLeray.Blueprint.Planar.PlanarData) {m : ℝ} (hm : 1 < m) (lam : ℂ) :
    Planar.L2w m →L[ℂ] Planar.L2w m :=
  Planar.couplingW hm + ∑ i : Fin 2, dampCoef P lam i • (planarEll κ hm i).smulRight (planarE κ m i)

theorem dampOp_apply (κ : PlanarFrameKernels) (P : UnforcedLeray.Blueprint.Planar.PlanarData) {m : ℝ} (hm : 1 < m) (lam : ℂ)
    (W : Planar.L2w m) :
    dampOp κ P hm lam W = Planar.couplingW hm W +
      ∑ i : Fin 2, (dampCoef P lam i * planarEll κ hm i W) • planarE κ m i := by
  simp [dampOp, ContinuousLinearMap.smulRight_apply, smul_smul]

/-- **The interaction formula on all of `L²_m`** (density of smooth compactly supported fields). -/
theorem A0_eq_of (κ : PlanarFrameKernels) (P : UnforcedLeray.Blueprint.Planar.PlanarData) {m : ℝ} (hm : 1 < m)
    (A0 : Planar.L2w m →L[ℂ] Planar.L2w m) (lam : ℂ)
    (hA : ∀ Φ : ℂ → ℂ, ContDiff ℝ ∞ Φ → HasCompactSupport Φ →
      ∀ W : Planar.L2w m, (⇑W =ᵐ[volume] Φ) →
        ⇑(A0 W) =ᵐ[volume] fun z =>
          Planar.couplingW hm W z +
            ∑ i : Fin 2, (((P.eigenvalue.re - 1 : ℝ) : ℂ) - seedEigen lam i) *
              planarLamPair κ i Φ * κ.e i (cToPlane z)) :
    A0 = dampOp κ P hm lam := by
  haveI : IsLocallyFiniteMeasure (Planar.wMeasure m) :=
    inferInstanceAs (IsLocallyFiniteMeasure (B0008.wMeasure m))
  have hD := Lp.dense_hasCompactSupport_contDiff (μ := Planar.wMeasure m) (F := ℂ) (p := 2)
    (by simp)
  refine DFunLike.coe_injective (Continuous.ext_on hD A0.continuous
    (dampOp κ P hm lam).continuous ?_)
  rintro W ⟨Φ, hWΦ, hcs, hsm⟩
  have hWv : ⇑W =ᵐ[volume] Φ := (Planar.volume_ac m).ae_le hWΦ
  have h1 := (Planar.wMeasure_ac m).ae_le (hA Φ hsm hcs W hWv)
  have hℓ : ∀ i, planarEll κ hm i W = planarLamPair κ i Φ := fun i =>
    planarEll_eq_lamPair κ hm i hWv
  show A0 W = dampOp κ P hm lam W
  rw [dampOp_apply, Fin.sum_univ_two]
  set a0 : ℂ := dampCoef P lam 0 * planarEll κ hm 0 W
  set a1 : ℂ := dampCoef P lam 1 * planarEll κ hm 1 W
  set E0 := planarE κ m 0
  set E1 := planarE κ m 1
  set cW := Planar.couplingW hm W
  apply Lp.ext
  filter_upwards [h1, Lp.coeFn_add cW (a0 • E0 + a1 • E1), Lp.coeFn_add (a0 • E0) (a1 • E1),
    Lp.coeFn_smul a0 E0, Lp.coeFn_smul a1 E1, coeFn_planarE κ m 0, coeFn_planarE κ m 1]
    with z h1 h2 h3 h4 h5 h6 h7
  rw [h1, h2, Pi.add_apply, h3, Pi.add_apply, h4, h5, Pi.smul_apply, Pi.smul_apply, h6, h7,
    Fin.sum_univ_two, ← hℓ 0, ← hℓ 1]
  simp only [smul_eq_mul, a0, a1, dampCoef]

end UnforcedLeray.Short.IIIa.PlanarDysonL3
