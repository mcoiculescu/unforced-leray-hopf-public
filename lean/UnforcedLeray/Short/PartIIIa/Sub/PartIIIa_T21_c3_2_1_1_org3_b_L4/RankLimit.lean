import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_b_L4.RankInst
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.ShortBlock.OscillatorForce
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.ShortBlock.EulerError
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.DirectError
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.ComplCoupling.HeatBound
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.ComplCoupling.EulerSubBound

/-!
# Leaf B4, finite-rank part: proof of `RankLimitLeaf` (SP 2898-2925)

By `frp_decomp`, `1_cell·(movFrameRankPert Φ) - Σ_i (γ-1-λ_i) ℓ_i(Φ) e_i` is
`Σ_i δa_i 1_cell E_i + Σ_i (γ-1-λ_i) ℓ_i (1_cell E_i - e_i) - Σ_j Λ_j(Φ) 1_cell R_j` with
`δa_i = -(H₀_i - λ_iΛ_i) + (β₀-γ)Λ_i + (γ-1-λ_i)(Λ_i - ℓ_i) + Σ_j (M₀_{ij} - λ_jδ_{ij})Λ_j`.
Every coefficient and every field is `O(1/θ + 1/d) = O(b^{-1/2})` (`ComplModeForceOscillator`,
`ComplModeForceEulerError`, `MovLamDualHeatBound`, `MovLamDualEulerSubBound`, `AmplDirectError`,
`lam_sub_ell`, `cellE_sub_e`), uniformly in the train and the age.
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

theorem eLpNorm_cmul_le {μ : Measure ℂ} {f : ℂ → ℂ} (c : ℂ) {a : ℝ}
    (h : eLpNorm f 2 μ ≤ ENNReal.ofReal a) :
    eLpNorm (fun z => c * f z) 2 μ ≤ ENNReal.ofReal (‖c‖ * a) := by
  have : (fun z => c * f z) = c • f := rfl
  rw [this, eLpNorm_const_smul, ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm_eq_enorm]
  exact mul_le_mul' le_rfl h

theorem eLpNorm_add_le_of {μ : Measure ℂ} {f g : ℂ → ℂ} {a b : ℝ}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h1 : eLpNorm f 2 μ ≤ ENNReal.ofReal a) (h2 : eLpNorm g 2 μ ≤ ENNReal.ofReal b) :
    eLpNorm (fun z => f z + g z) 2 μ ≤ ENNReal.ofReal (a + b) := by
  rw [ENNReal.ofReal_add ha hb]
  exact (eLpNorm_add_le hf hg (by norm_num)).trans (add_le_add h1 h2)

theorem eLpNorm_sub_le_of {μ : Measure ℂ} {f g : ℂ → ℂ} {a b : ℝ}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h1 : eLpNorm f 2 μ ≤ ENNReal.ofReal a) (h2 : eLpNorm g 2 μ ≤ ENNReal.ofReal b) :
    eLpNorm (fun z => f z - g z) 2 μ ≤ ENNReal.ofReal (a + b) := by
  rw [ENNReal.ofReal_add ha hb]
  exact (eLpNorm_sub_le hf hg (by norm_num)).trans (add_le_add h1 h2)

/-- **The finite-rank leaf** (SP 2898-2925). -/
theorem rankLimitLeaf (κ : PlanarFrameKernels) : RankLimitLeaf κ := by
  intro hκ P hP m hm K ε hε
  have hm1 : 1 < m := by linarith
  have hm0 : 0 ≤ m := by linarith
  obtain ⟨C_o, b_o, hC_o, hb_o, hOsc⟩ := complModeForceOscillator κ hκ m hm
  obtain ⟨C_u, b_u, hC_u, hb_u, hEul⟩ := complModeForceEulerError κ hκ P hP m hm
  obtain ⟨C_h, b_h, hC_h, hb_h, hHeat⟩ := movLamDualHeatBound κ hκ m hm
  obtain ⟨lam', C_e, b_e, hC_e, hb_e, hESub⟩ := _root_.movLamDualEulerSubBound κ hκ m hm
  obtain ⟨C_D, b_D, hC_D, hb_D, hDir⟩ := _root_.amplDirectError κ hκ P hP m hm K
  obtain ⟨C_L, D_L, hC_L, hD_L, hLam⟩ := lam_sub_ell κ hκ hm
  obtain ⟨C_ee, hC_ee, hEe⟩ := cellE_sub_e κ m hm0
  set Kp := max K 0 with hKp
  have hKp0 : 0 ≤ Kp := le_max_right _ _
  set Kap := ‖P.kappa‖ with hKap
  have hKap0 : 0 ≤ Kap := norm_nonneg _
  set Cc := |P.eigenvalue.re - 1| + ‖P.eigenvalue‖ with hCc
  have hCc0 : 0 ≤ Cc := by positivity
  set C_R := C_o + C_u with hC_R
  have hC_R0 : 0 ≤ C_R := by positivity
  set C_S := C_h + C_e with hC_S
  have hC_S0 : 0 ≤ C_S := by positivity
  set C_H := C_S + (C_D + Kap + C_S * Kp) * Kp with hC_H
  have hC_H0 : 0 ≤ C_H := by positivity
  set C_δ := C_H + Kap * Kp + Cc * C_L + 2 * (Kp * C_R) * Kp with hC_δ
  have hC_δ0 : 0 ≤ C_δ := by positivity
  set C_tot := 2 * C_δ * Kp + 2 * (Cc * (Kp + C_L)) * C_ee + 2 * Kp * C_R + 1 with hC_tot
  have hC_tot0 : 0 < C_tot := by positivity
  set B₀ := max (max (max 1 b_o) (max b_u b_h)) (max (max b_e b_D) (max (D_L ^ 2) ((C_tot / ε) ^ 2)))
    with hB₀
  refine ⟨B₀, fun b hb => ?_⟩
  rw [hB₀] at hb
  simp only [max_le_iff] at hb
  obtain ⟨⟨⟨hb1, hbo⟩, ⟨hbu, hbh⟩⟩, ⟨⟨hbe, hbD⟩, ⟨hbL, hbC⟩⟩⟩ := hb
  obtain ⟨ν_o, hν_o, hOsc'⟩ := hOsc b hbo
  obtain ⟨ν_u, hν_u, hEul'⟩ := hEul b hbu
  obtain ⟨ν_h, hν_h, hHeat'⟩ := hHeat b hbh
  obtain ⟨ν_e, hν_e, hESub'⟩ := hESub b hbe
  obtain ⟨ν_D, hν_D, hDir'⟩ := hDir b hbD
  refine ⟨min (min (min ν_o ν_u) (min ν_h ν_e)) (min ν_D 1),
    lt_min (lt_min (lt_min hν_o hν_u) (lt_min hν_h hν_e)) (lt_min hν_D one_pos),
    fun ν hν hF tr htr r hr hθ Φ hΦs hΦc W hW => ?_⟩
  have hν0 : 0 < ν := hν.1
  have hνo : ν ∈ Ioc 0 ν_o := ⟨hν0, hν.2.trans
    ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))⟩
  have hνu : ν ∈ Ioc 0 ν_u := ⟨hν0, hν.2.trans
    ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))⟩
  have hνh : ν ∈ Ioc 0 ν_h := ⟨hν0, hν.2.trans
    ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))⟩
  have hνe : ν ∈ Ioc 0 ν_e := ⟨hν0, hν.2.trans
    ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))⟩
  have hνD : ν ∈ Ioc 0 ν_D := ⟨hν0, hν.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hν1 : ν ≤ 1 := hν.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  -- clocks, cell length and the small parameter
  set θ := clockTheta ν r with hθ_def
  have hθ1 : 1 ≤ θ := hb1.trans hθ
  have hθ0 : 0 < θ := lt_of_lt_of_le one_pos hθ1
  set d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r) with hd_def
  have hd1 : 1 ≤ d := ComplCouplingSub.one_le_cellLen_of_theta hν0 hν1 hr hθ1
  have hd0 : 0 < d := lt_of_lt_of_le one_pos hd1
  have hb0 : 0 < b := lt_of_lt_of_le one_pos hb1
  have hdd : 1 / d ^ 2 = ν ^ 3 / θ := ComplCouplingSub.inv_cellLen_sq_eq_nu_cube_div_theta hν0 hr
  have hν3 : ν ^ 3 ≤ 1 := pow_le_one₀ hν0.le hν1
  have hθinv : 1 / θ ≤ 1 / b := one_div_le_one_div_of_le hb0 hθ
  have hdb : b ≤ d ^ 2 := by
    have h1 : 1 / d ^ 2 ≤ 1 / b := by
      rw [hdd]
      exact (div_le_div_of_nonneg_right hν3 hθ0.le).trans hθinv
    rwa [one_div_le_one_div (by positivity) hb0] at h1
  set sb := Real.sqrt b with hsb
  have hsb1 : 1 ≤ sb := by rw [hsb]; exact Real.one_le_sqrt.2 hb1
  have hsb0 : 0 < sb := lt_of_lt_of_le one_pos hsb1
  have hsbd : sb ≤ d := by
    rw [hsb]; exact Real.sqrt_le_iff.2 ⟨hd0.le, hdb⟩
  have hsbb : sb ≤ b := by
    rw [hsb]; exact Real.sqrt_le_iff.2 ⟨hb0.le, le_self_pow₀ hb1 (by norm_num)⟩
  set η := 1 / sb with hη
  have hη0 : 0 ≤ η := by positivity
  have hθη : 1 / θ ≤ η := hθinv.trans (one_div_le_one_div_of_le hsb0 hsbb)
  have hdη : 1 / d ≤ η := one_div_le_one_div_of_le hsb0 hsbd
  have hd2η : 1 / d ^ 2 ≤ η := by
    refine le_trans ?_ hdη
    rw [one_div_le_one_div (by positivity) hd0]; exact le_self_pow₀ hd1 (by norm_num)
  have hdL : D_L ≤ d := by
    have h1 : D_L ≤ sb := by
      rw [hsb]; exact Real.le_sqrt_of_sq_le hbL
    exact h1.trans hsbd
  have hCη : C_tot * η ≤ ε := by
    have h1 : C_tot / ε ≤ sb := by rw [hsb]; exact Real.le_sqrt_of_sq_le hbC
    rw [hη, mul_one_div, div_le_iff₀ hsb0]
    rw [div_le_iff₀ hε] at h1
    linarith
  -- the field `Φ`
  obtain ⟨hΦm, hΦn⟩ := memLp_plane_of_rep W hW
  have hΦcell : MemLp Φ 2 (B0579.cellMeasure d m) := by
    rw [IIb.cellMeasure_eq_restrict_planeMeasure]; exact hΦm.restrict _
  have hxΦ : xNorm d m Φ ≤ ENNReal.ofReal ‖W‖ := by
    unfold xNorm
    rw [← hΦn, IIb.cellMeasure_eq_restrict_planeMeasure]
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  set w := ‖W‖ with hw
  have hw0 : 0 ≤ w := norm_nonneg _
  -- frame columns
  have hEx : ∀ i : Fin 2, xNorm d m (perE κ d i) ≤ ENNReal.ofReal Kp := fun i =>
    (hF.2.1 r hr hθ i).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hEm : ∀ i : Fin 2, MemLp (perE κ d i) 2 (B0579.cellMeasure d m) := fun i =>
    ⟨(perE_continuous_aux κ hd0 i).aestronglyMeasurable,
      lt_of_le_of_lt (hEx i) ENNReal.ofReal_lt_top⟩
  -- dual rows
  have hΛ : ∀ j : Fin 2, ‖movLamPair κ ν r j Φ‖ ≤ Kp * w := by
    intro j
    refine ofReal_norm_le_of_ofReal (by positivity) ((hF.2.2 r hr hθ j Φ).trans ?_)
    rw [ENNReal.ofReal_mul hKp0]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) hxΦ
  have hΛℓ : ∀ j : Fin 2, ‖movLamPair κ ν r j Φ - ∫ y, κ.lamP j y * Φ y‖ ≤ C_L * η * w := by
    intro j
    have h := hLam d hdL j Φ hΦs.continuous hΦc W hW
    refine h.trans ?_
    have : C_L / d ≤ C_L * η := by
      rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hdη hC_L
    exact mul_le_mul_of_nonneg_right this hw0
  have hη1 : η ≤ 1 := by rw [hη]; exact (div_le_one hsb0).2 hsb1
  have hℓ : ∀ j : Fin 2, ‖∫ y, κ.lamP j y * Φ y‖ ≤ (Kp + C_L) * w := by
    intro j
    have h1 : ‖∫ y, κ.lamP j y * Φ y‖ ≤ ‖movLamPair κ ν r j Φ‖ +
        ‖movLamPair κ ν r j Φ - ∫ y, κ.lamP j y * Φ y‖ := by
      have := norm_sub_le (movLamPair κ ν r j Φ)
        (movLamPair κ ν r j Φ - ∫ y, κ.lamP j y * Φ y)
      simpa using this
    have h2 : C_L * η * w ≤ C_L * w := by
      have h3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hη1 hC_L) hw0
      rwa [mul_one] at h3
    have e : (Kp + C_L) * w = Kp * w + C_L * w := by ring
    rw [e]
    linarith [hΛ j, hΛℓ j]
  -- mode residuals
  have hR : ∀ j : Fin 2,
      MemLp (fun x => movOscRes κ ν r j x + movEulerRes κ P tr r j x) 2
          (B0579.cellMeasure d m) ∧
        xNorm d m (fun x => movOscRes κ ν r j x + movEulerRes κ P tr r j x) ≤
          ENNReal.ofReal (C_R * η) := by
    intro j
    have hO := hOsc' ν hνo r hr hθ j
    have hE := hEul' ν hνu tr htr r hr hθ j
    obtain ⟨h1, h2⟩ := memLp_R κ P tr r j (by positivity) (by positivity) hO hE
    refine ⟨h1, h2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    have e1 : C_o / θ ≤ C_o * η := by
      rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hθη hC_o
    have e2 : C_u * ν ^ 3 / θ ≤ C_u * η := by
      rw [mul_div_assoc]
      refine mul_le_mul_of_nonneg_left (le_trans ?_ hθη) hC_u
      exact div_le_div_of_nonneg_right hν3 hθ0.le
    rw [hC_R]; linarith
  -- the coefficients `μ_{ij} = M₀_{ij} - λ_j δ_{ij}`
  have hμ : ∀ i j : Fin 2,
      ‖movM0 κ P tr r i j - (if i = j then modeEigen P j else 0)‖ ≤ Kp * (C_R * η) := by
    intro i j
    rw [movM0_sub_eq κ P hm tr hr hθ hd1 hF i j (hR j).1 (hEm j)]
    refine ofReal_norm_le_of_ofReal (by positivity)
      ((hF.2.2 r hr hθ i _).trans ?_)
    rw [ENNReal.ofReal_mul hKp0]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) (hR j).2
  -- the dual generator
  have hSub : ∀ i : Fin 2, MemLp (movLamDualSub κ lam' tr r i) 2 (B0579.cellMeasure d (-m)) ∧
      xNorm d (-m) (movLamDualSub κ lam' tr r i) ≤ ENNReal.ofReal (C_S / θ) := by
    intro i
    obtain ⟨hh1, hh2⟩ := hHeat' ν hνh r hr hθ i
    obtain ⟨he1, he2⟩ := hESub' ν hνe tr htr r hr hθ i
    have hfun : movLamDualSub κ lam' tr r i =
        fun y => movLamDualHeat κ ν r i y + movLamDualEulerSub κ lam' tr r i y := by
      funext y; exact ComplCouplingSub.movLamDualSub_eq_add κ lam' tr r i y
    rw [hfun]
    refine ⟨hh1.add he1, ?_⟩
    unfold xNorm
    refine (eLpNorm_add_le hh1.1 he1.1 (by norm_num)).trans ?_
    have e : C_S / θ = C_h * (1 / θ) + C_e * (1 / θ) := by rw [hC_S]; ring
    rw [e, ENNReal.ofReal_add (by positivity) (by positivity)]
    exact add_le_add hh2 he2
  -- the direct frame error on the diagonal
  have hDiag : ∀ i : Fin 2,
      ‖movH0 κ tr r i (perE κ d i) - modeDiag P ν r i‖ ≤ C_D / θ := by
    intro i
    have h := hDir' ν hνD hF tr htr r hr hθ i
    have h1 : ‖amplDirectMat κ P (periodizedFrame κ ν m b K hνD.1 hF) tr r i i‖ ≤
        ∑ i' : Fin 2, ‖amplDirectMat κ P (periodizedFrame κ ν m b K hνD.1 hF) tr r i' i‖ :=
      Finset.single_le_sum (f := fun i' =>
        ‖amplDirectMat κ P (periodizedFrame κ ν m b K hνD.1 hF) tr r i' i‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
    have h2 : amplDirectMat κ P (periodizedFrame κ ν m b K hνD.1 hF) tr r i i =
        movH0 κ tr r i (perE κ d i) - modeDiag P ν r i := by
      unfold amplDirectMat; rw [if_pos rfl]; rfl
    rw [← h2]
    refine (h1.trans h).trans ?_
    rw [mul_div_assoc]
    calc C_D * (ν ^ 3 / θ) ≤ C_D * (1 / θ) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hν3 hθ0.le) hC_D
      _ = C_D / θ := by ring
  -- `H₀_i - λ_i Λ_i`
  have hH : ∀ i : Fin 2,
      ‖movH0 κ tr r i Φ - modeEigen P i * movLamPair κ ν r i Φ‖ ≤ C_H * η * w := by
    intro i
    have h := movH0_close κ P hm hν0 tr hr hθ hd1 hF lam' hC_S0 hC_D i (hSub i) (hDiag i)
      hΦcell hw0 hxΦ
    refine h.trans ?_
    have : (C_S + (C_D + Kap + C_S * Kp) * Kp) / θ ≤ C_H * η := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hθη hC_H0
    exact mul_le_mul_of_nonneg_right this hw0
  -- the coefficients `c_i` and `β₀ - γ`
  have hc : ∀ i : Fin 2, ‖(((P.eigenvalue.re - 1 : ℝ) : ℂ) - modeEigen P i)‖ ≤ Cc := by
    intro i
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, norm_modeEigen]
  have hβ : ‖(((movBeta0 P ν r - P.eigenvalue.re : ℝ) : ℂ))‖ ≤ Kap * η := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    unfold movBeta0
    rw [show P.eigenvalue.re + P.kappa.re / clockTheta ν r - P.eigenvalue.re =
      P.kappa.re / θ by rw [hθ_def]; ring, abs_div, abs_of_pos hθ0, div_eq_mul_one_div]
    exact mul_le_mul (Complex.abs_re_le_norm _) hθη (by positivity) hKap0
  -- the coefficient `δa_i`
  set Λ := fun j => movLamPair κ ν r j Φ with hΛdef
  set ℓ := fun j => ∫ y, κ.lamP j y * Φ y with hℓdef
  set lamE := modeEigen P with hlamE
  set c := fun i => (((P.eigenvalue.re - 1 : ℝ) : ℂ) - lamE i) with hcdef
  set μ := fun i j => movM0 κ P tr r i j - if i = j then lamE j else 0 with hμdef
  set δa := fun i => -(movH0 κ tr r i Φ - lamE i * Λ i) +
      (((movBeta0 P ν r - P.eigenvalue.re : ℝ) : ℂ)) * Λ i + c i * (Λ i - ℓ i) +
      ∑ j : Fin 2, μ i j * Λ j with hδadef
  have hδa : ∀ i : Fin 2, ‖δa i‖ ≤ C_δ * η * w := by
    intro i
    have h1 : ‖δa i‖ ≤ ‖movH0 κ tr r i Φ - lamE i * Λ i‖ +
        ‖(((movBeta0 P ν r - P.eigenvalue.re : ℝ) : ℂ))‖ * ‖Λ i‖ + ‖c i‖ * ‖Λ i - ℓ i‖ +
        (‖μ i 0‖ * ‖Λ 0‖ + ‖μ i 1‖ * ‖Λ 1‖) := by
      simp only [hδadef, Fin.sum_univ_two]
      refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (le_of_eq (norm_neg _)) (le_of_eq (norm_mul _ _))))
        (le_of_eq (norm_mul _ _)))) ((norm_add_le _ _).trans (add_le_add
          (le_of_eq (norm_mul _ _)) (le_of_eq (norm_mul _ _)))))
    have hHi := hH i
    have hci := hc i
    have hΛi := hΛ i
    have hΛℓi := hΛℓ i
    have hμ0 := hμ i 0
    have hμ1 := hμ i 1
    have hΛ0 := hΛ 0
    have hΛ1 := hΛ 1
    have t2 : ‖(((movBeta0 P ν r - P.eigenvalue.re : ℝ) : ℂ))‖ * ‖Λ i‖ ≤ Kap * η * (Kp * w) :=
      mul_le_mul hβ hΛi (norm_nonneg _) (by positivity)
    have t3 : ‖c i‖ * ‖Λ i - ℓ i‖ ≤ Cc * (C_L * η * w) :=
      mul_le_mul hci hΛℓi (norm_nonneg _) hCc0
    have t4 : ‖μ i 0‖ * ‖Λ 0‖ ≤ Kp * (C_R * η) * (Kp * w) :=
      mul_le_mul hμ0 hΛ0 (norm_nonneg _) (by positivity)
    have t5 : ‖μ i 1‖ * ‖Λ 1‖ ≤ Kp * (C_R * η) * (Kp * w) :=
      mul_le_mul hμ1 hΛ1 (norm_nonneg _) (by positivity)
    calc ‖δa i‖ ≤ _ := h1
      _ ≤ C_H * η * w + Kap * η * (Kp * w) + Cc * (C_L * η * w) +
          (Kp * (C_R * η) * (Kp * w) + Kp * (C_R * η) * (Kp * w)) := by
          gcongr
      _ = C_δ * η * w := by rw [hC_δ]; ring
  -- the pointwise decomposition
  set R := fun j : Fin 2 => fun x => movOscRes κ ν r j x + movEulerRes κ P tr r j x with hRdef
  have hdec : (fun z => cellZeroExt d (movFrameRankPert κ P tr r Φ) (cToPlane z) -
      ∑ i : Fin 2, (((P.eigenvalue.re - 1 : ℝ) : ℂ) - modeEigen P i) *
        (∫ y, κ.lamP i y * Φ y) * κ.e i (cToPlane z)) = fun z =>
      (δa 0 * cellZeroExt d (perE κ d 0) (cToPlane z) +
          δa 1 * cellZeroExt d (perE κ d 1) (cToPlane z)) +
        (c 0 * ℓ 0 * (cellZeroExt d (perE κ d 0) (cToPlane z) - κ.e 0 (cToPlane z)) +
          c 1 * ℓ 1 * (cellZeroExt d (perE κ d 1) (cToPlane z) - κ.e 1 (cToPlane z))) -
        (Λ 0 * cellZeroExt d (R 0) (cToPlane z) + Λ 1 * cellZeroExt d (R 1) (cToPlane z)) := by
    funext z
    have h := frp_decomp κ P tr r Φ ℓ (cToPlane z)
    simp only [hδadef, hcdef, hℓdef, hΛdef, hμdef, hRdef, hd_def, Fin.sum_univ_two] at h ⊢
    exact h
  rw [hdec]
  -- measurability and norms of the fields
  have hA : ∀ i : Fin 2, AEStronglyMeasurable (fun z => cellZeroExt d (perE κ d i) (cToPlane z))
      (Planar.wMeasure m) ∧
      eLpNorm (fun z => cellZeroExt d (perE κ d i) (cToPlane z)) 2 (Planar.wMeasure m) ≤
        ENNReal.ofReal Kp := by
    intro i
    refine ⟨(BlockPropagatorSub.memLp_cellZeroExt_cToPlane d m (hEm i)).1, ?_⟩
    rw [BlockPropagatorSub.eLpNorm_cellZeroExt_cToPlane d m (hEm i).1]
    exact hEx i
  have hB : ∀ i : Fin 2, AEStronglyMeasurable
      (fun z => cellZeroExt d (perE κ d i) (cToPlane z) - κ.e i (cToPlane z))
      (Planar.wMeasure m) ∧
      eLpNorm (fun z => cellZeroExt d (perE κ d i) (cToPlane z) - κ.e i (cToPlane z)) 2
        (Planar.wMeasure m) ≤ ENNReal.ofReal (C_ee * η) := by
    intro i
    refine ⟨(hA i).1.sub ((κ.e_cont i).measurable.comp
      BlockPropagatorSub.measurable_cToPlane).aestronglyMeasurable, ?_⟩
    refine (hEe d hd1 i).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hd2η hC_ee
  have hRf : ∀ j : Fin 2, AEStronglyMeasurable (fun z => cellZeroExt d (R j) (cToPlane z))
      (Planar.wMeasure m) ∧
      eLpNorm (fun z => cellZeroExt d (R j) (cToPlane z)) 2 (Planar.wMeasure m) ≤
        ENNReal.ofReal (C_R * η) := by
    intro j
    refine ⟨(BlockPropagatorSub.memLp_cellZeroExt_cToPlane d m (hR j).1).1, ?_⟩
    rw [BlockPropagatorSub.eLpNorm_cellZeroExt_cToPlane d m (hR j).1.1]
    exact (hR j).2
  -- assembly of the six terms
  have h1 := eLpNorm_add_le_of ((hA 0).1.const_mul (δa 0)) ((hA 1).1.const_mul (δa 1))
    (by positivity) (by positivity) (eLpNorm_cmul_le (δa 0) (hA 0).2)
    (eLpNorm_cmul_le (δa 1) (hA 1).2)
  have h2 := eLpNorm_add_le_of ((hB 0).1.const_mul (c 0 * ℓ 0)) ((hB 1).1.const_mul (c 1 * ℓ 1))
    (by positivity) (by positivity) (eLpNorm_cmul_le (c 0 * ℓ 0) (hB 0).2)
    (eLpNorm_cmul_le (c 1 * ℓ 1) (hB 1).2)
  have h3 := eLpNorm_add_le_of ((hRf 0).1.const_mul (Λ 0)) ((hRf 1).1.const_mul (Λ 1))
    (by positivity) (by positivity) (eLpNorm_cmul_le (Λ 0) (hRf 0).2)
    (eLpNorm_cmul_le (Λ 1) (hRf 1).2)
  have h12 := eLpNorm_add_le_of
    (((hA 0).1.const_mul (δa 0)).add ((hA 1).1.const_mul (δa 1)))
    (((hB 0).1.const_mul (c 0 * ℓ 0)).add ((hB 1).1.const_mul (c 1 * ℓ 1)))
    (by positivity) (by positivity) h1 h2
  have hall := eLpNorm_sub_le_of
    ((((hA 0).1.const_mul (δa 0)).add ((hA 1).1.const_mul (δa 1))).add
      (((hB 0).1.const_mul (c 0 * ℓ 0)).add ((hB 1).1.const_mul (c 1 * ℓ 1))))
    (((hRf 0).1.const_mul (Λ 0)).add ((hRf 1).1.const_mul (Λ 1)))
    (by positivity) (by positivity) h12 h3
  refine hall.trans (ENNReal.ofReal_le_ofReal ?_)
  have ha : ∀ i : Fin 2, ‖δa i‖ * Kp ≤ C_δ * η * w * Kp := fun i =>
    mul_le_mul_of_nonneg_right (hδa i) hKp0
  have hq : ∀ i : Fin 2, ‖c i * ℓ i‖ * (C_ee * η) ≤ Cc * ((Kp + C_L) * w) * (C_ee * η) := by
    intro i
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hc i) (hℓ i) (norm_nonneg _) hCc0)
      (by positivity)
  have hs : ∀ j : Fin 2, ‖Λ j‖ * (C_R * η) ≤ Kp * w * (C_R * η) := fun j =>
    mul_le_mul_of_nonneg_right (hΛ j) (by positivity)
  have hfinal : 2 * (C_δ * η * w * Kp) + 2 * (Cc * ((Kp + C_L) * w) * (C_ee * η)) +
      2 * (Kp * w * (C_R * η)) ≤ ε * w := by
    have e : 2 * (C_δ * η * w * Kp) + 2 * (Cc * ((Kp + C_L) * w) * (C_ee * η)) +
        2 * (Kp * w * (C_R * η)) = (C_tot - 1) * η * w := by rw [hC_tot]; ring
    rw [e]
    have hηw : 0 ≤ η * w := mul_nonneg hη0 hw0
    have e1 : (C_tot - 1) * η * w ≤ C_tot * η * w := by
      have : (C_tot - 1) * η * w = C_tot * η * w - η * w := by ring
      rw [this]; linarith
    have e2 : C_tot * η * w ≤ ε * w := mul_le_mul_of_nonneg_right hCη hw0
    linarith
  linarith [ha 0, ha 1, hq 0, hq 1, hs 0, hs 1]

end L4

end PlanarB

end OrgSplit3
end BlockPropagatorInteriorSub
end UnforcedLeray.Short.IIIa
