import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G2Org
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G2.g2ModeBounds
import UnforcedLeray.Short.PartIIIa.Sub.T21_c1_a_4.Sectors
import UnforcedLeray.Short.PartIIIa.Sub.T21_c1_a_4_1.LeftDCT

/-!
# `PartIII-b:IIIb-D3/2/G2/4`: `g2SectorOrth` (sector orthogonality of the seed kernels, SP 593-610, 2891-2897)
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory
open scoped ComplexConjugate ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G2

open FlatSettingInst

private def sC (z : ℂ) : ℝ := z.re ^ 2 + z.im ^ 2

private lemma sC_eq_norm_sq (z : ℂ) : sC z = ‖z‖ ^ 2 := by
  unfold sC
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

private lemma contDiff_sC : ContDiff ℝ ∞ sC :=
  (Complex.reCLM.contDiff.pow 2).add (Complex.imCLM.contDiff.pow 2)

private def bumpR : ContDiffBump (0 : ℝ) :=
  { rIn := 1, rOut := 2, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }

private def radChi (z : ℂ) : ℝ := bumpR (sC z)

private lemma contDiff_radChi : ContDiff ℝ ∞ radChi :=
  bumpR.contDiff.comp contDiff_sC

private lemma hasCompactSupport_radChi : HasCompactSupport radChi := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) 2) ?_
  intro z hz
  rw [Function.mem_support] at hz
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hlt
  have hlt' : 2 < ‖z‖ := not_le.mp hlt
  apply hz
  unfold radChi
  apply bumpR.zero_of_le_dist
  rw [Real.dist_eq, sub_zero, sC_eq_norm_sq, abs_of_nonneg (sq_nonneg _)]
  show (2 : ℝ) ≤ ‖z‖ ^ 2
  nlinarith

private lemma radChi_bounds (z : ℂ) : 0 ≤ radChi z ∧ radChi z ≤ 1 :=
  ⟨bumpR.nonneg, bumpR.le_one⟩

private lemma radChi_one {z : ℂ} (hz : ‖z‖ ≤ 1) : radChi z = 1 := by
  unfold radChi
  apply bumpR.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, sC_eq_norm_sq, abs_of_nonneg (sq_nonneg _)]
  show ‖z‖ ^ 2 ≤ 1
  nlinarith [norm_nonneg z]

private lemma radChi_circle {r c : ℝ} (hr : 0 ≤ r) (hc : 0 ≤ c) (θ : ℝ) :
    radChi (((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) / (c : ℂ)) = bumpR ((r / c) ^ 2) := by
  unfold radChi
  rw [sC_eq_norm_sq, norm_div, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hr, Real.norm_of_nonneg hc]

private lemma angularSector_radChi_mul (f : ℂ → ℂ) (n : ℕ) (k : ℤ) {r : ℝ} (hr : 0 < r) :
    Planar.NUE.Polar.angularSector
        (fun z => ((radChi (z / ((n : ℂ) + 1)) : ℝ) : ℂ) * f z) k r =
      ((bumpR ((r / ((n : ℝ) + 1)) ^ 2) : ℝ) : ℂ) *
        Planar.NUE.Polar.angularSector f k r := by
  unfold Planar.NUE.Polar.angularSector
  have hcast : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
  have hpt : ∀ θ : ℝ,
      (((radChi (((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) / ((n : ℂ) + 1)) : ℝ) : ℂ) *
        f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) *
          Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I)) =
      ((bumpR ((r / ((n : ℝ) + 1)) ^ 2) : ℝ) : ℂ) *
        (f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
          Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I))) := by
    intro θ
    rw [hcast, radChi_circle hr.le (by positivity) θ, mul_assoc]
  simp_rw [hpt, intervalIntegral.integral_const_mul]
  ring

private theorem integral_lamP_zero_of_sector_zero (κ : IIIa.PlanarFrameKernels)
    (hκ : IIIa.IsSeedKernels κ) {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hdec : ∃ C : ℝ, ∀ y : ℝ × ℝ, ‖f (IIIa.planeToC y)‖ ≤ C * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) :
    ((∀ r : ℝ, 0 < r → Planar.NUE.Polar.angularSector f 2 r = 0) →
      ∫ y, κ.lamP 0 y * f (IIIa.planeToC y) = 0) ∧
    ((∀ r : ℝ, 0 < r → Planar.NUE.Polar.angularSector f (-2) r = 0) →
      ∫ y, κ.lamP 1 y * f (IIIa.planeToC y) = 0) := by
  obtain ⟨lam, h, hh, ℓ, hIS, -, -, hcl⟩ := hκ
  set fn : ℕ → ℂ → ℂ := fun n z => ((radChi (z / ((n : ℂ) + 1)) : ℝ) : ℂ) * f z
  have hn0 : ∀ n : ℕ, ((n : ℂ) + 1) ≠ 0 := fun n => by
    have : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [this]; exact_mod_cast Nat.succ_ne_zero n
  have hfnS : ∀ n, ContDiff ℝ ∞ (fn n) := fun n =>
    (Complex.ofRealCLM.contDiff.comp (contDiff_radChi.comp (contDiff_id.div_const _))).mul hf
  have hfnC : ∀ n, HasCompactSupport (fn n) := by
    intro n
    have h1 : HasCompactSupport (fun z : ℂ => radChi (z / ((n : ℂ) + 1))) := by
      have := hasCompactSupport_radChi.comp_smul (c := ((n : ℂ) + 1)⁻¹) (inv_ne_zero (hn0 n))
      simpa [div_eq_inv_mul] using this
    exact (h1.comp_left Complex.ofReal_zero).mul_right
  have hzero : PartI.seedEll h (fun _ => (0 : ℂ)) = 0 := by simp [PartI.seedEll]
  constructor
  · intro hs2
    have L0 := (extLeftDCT_proof (κ.lamP 0) (κ.lamP_cont 0)
      (κ.lamP_decay.imp fun C hC y => hC 0 y) f hf.continuous hdec
      radChi contDiff_radChi.continuous radChi_bounds (fun _ hz => radChi_one hz)).2
    have hseq : ∀ n : ℕ,
        ∫ y, κ.lamP 0 y * (((radChi (IIIa.planeToC y / ((n : ℂ) + 1)) : ℝ) : ℂ) *
          f (IIIa.planeToC y)) = 0 := by
      intro n
      rw [(hcl (fn n) (hfnS n) (hfnC n)).1]
      rw [IIIa.seedEll_congr h _ (fun _ => 0) fun r hr => by
        rw [angularSector_radChi_mul f n 2 hr, hs2 r hr, mul_zero]]
      exact hzero
    exact tendsto_nhds_unique L0 (tendsto_const_nhds.congr fun n => (hseq n).symm)
  · intro hsm2
    have L1 := (extLeftDCT_proof (κ.lamP 1) (κ.lamP_cont 1)
      (κ.lamP_decay.imp fun C hC y => hC 1 y) f hf.continuous hdec
      radChi contDiff_radChi.continuous radChi_bounds (fun _ hz => radChi_one hz)).2
    have hseq : ∀ n : ℕ,
        ∫ y, κ.lamP 1 y * (((radChi (IIIa.planeToC y / ((n : ℂ) + 1)) : ℝ) : ℂ) *
          f (IIIa.planeToC y)) = 0 := by
      intro n
      rw [(hcl (fn n) (hfnS n) (hfnC n)).2]
      rw [IIIa.seedEll_congr h _ (fun _ => 0) fun r hr => by
        show conj (Planar.NUE.Polar.angularSector
          (fun z => ((radChi (z / ((n : ℂ) + 1)) : ℝ) : ℂ) * f z) (-2) r) = 0
        rw [angularSector_radChi_mul f n (-2) hr, hsm2 r hr, mul_zero, map_zero]]
      simp [hzero]
    exact tendsto_nhds_unique L1 (tendsto_const_nhds.congr fun n => (hseq n).symm)

private def fH (z : ℂ) : ℂ :=
  ((-((1 / 2 : ℝ) * (4 - sC z / 2) * Real.exp (-sC z / 4)) : ℝ) : ℂ) * z ^ 2

private def fR (z : ℂ) : ℂ :=
  ((-((sC z / 2) * (4 - sC z / 2) * Real.exp (-sC z / 4)) +
    2 * ((1 ^ 2)⁻¹ * (2 - sC z / (2 * 1)) * Real.exp (-sC z / (4 * 1))) : ℝ) : ℂ)

private lemma contDiff_fH : ContDiff ℝ ∞ fH := by
  unfold fH
  have h1 : ContDiff ℝ ∞ (fun z : ℂ => -((1 / 2 : ℝ) * (4 - sC z / 2) * Real.exp (-sC z / 4))) := by
    have := contDiff_sC
    fun_prop
  exact (Complex.ofRealCLM.contDiff.comp h1).mul (contDiff_id.pow 2)

private lemma contDiff_fR : ContDiff ℝ ∞ fR := by
  unfold fR
  have h1 : ContDiff ℝ ∞ (fun z : ℂ =>
      -((sC z / 2) * (4 - sC z / 2) * Real.exp (-sC z / 4)) +
        2 * ((1 ^ 2)⁻¹ * (2 - sC z / (2 * 1)) * Real.exp (-sC z / (4 * 1)))) := by
    have := contDiff_sC
    fun_prop
  exact Complex.ofRealCLM.contDiff.comp h1

private lemma fH_eq_seedPlanar (z : ℂ) :
    fH z = PartI.seedPlanar (fun r => ((gaussRdE 1 r : ℝ) : ℂ)) z := by
  unfold fH PartI.seedPlanar Planar.NUE.Ang.ofProfile Planar.NUE.Ang.angPhase
  dsimp only
  rw [g2mb_gaussRdE_one ‖z‖, ← sC_eq_norm_sq z, zpow_ofNat, div_pow, ← Complex.ofReal_pow,
    ← sC_eq_norm_sq z]
  by_cases hz : sC z = 0
  · have hz0 : z = 0 := by
      have h1 := sC_eq_norm_sq z
      rw [hz, eq_comm, sq_eq_zero_iff, norm_eq_zero] at h1
      exact h1
    simp [hz0]
  · have hzC : ((sC z : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hz
    push_cast
    field_simp

private lemma hMode_eq_fH (y : ℝ × ℝ) : hMode 1 y = fH (IIIa.planeToC y) := by
  have hplane : ((y.1 : ℂ) + (y.2 : ℂ) * Complex.I) = IIIa.planeToC y := by
    apply Complex.ext <;> simp [IIIa.planeToC]
  have hs : y.1 ^ 2 + y.2 ^ 2 = sC (IIIa.planeToC y) := rfl
  unfold hMode IIIa.angTwo fH
  rw [g2mb_gaussRdE_one (planeR y), g2mb_planeR_sq y, hplane, hs]
  by_cases hz : sC (IIIa.planeToC y) = 0
  · have hz0 : IIIa.planeToC y = 0 := by
      have h1 := sC_eq_norm_sq (IIIa.planeToC y)
      rw [hz, eq_comm, sq_eq_zero_iff, norm_eq_zero] at h1
      exact h1
    simp [hz0]
  · have hzC : ((sC (IIIa.planeToC y) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hz
    push_cast
    field_simp

private lemma rMode_eq_fR (y : ℝ × ℝ) : rMode 1 y = fR (IIIa.planeToC y) := by
  unfold rMode gaussE fR
  rw [g2mb_gaussRdE_one (planeR y), g2mb_planeR_sq y]
  rfl

private lemma fR_rot_invariant (θ : ℝ) (z : ℂ) :
    fR (Planar.NUE.rot θ z) = fR z := by
  unfold fR
  have : sC (Planar.NUE.rot θ z) = sC z := by
    rw [sC_eq_norm_sq, sC_eq_norm_sq, Planar.NUE.Polar.norm_rot]
  rw [this]

theorem g2SectorOrth : UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G2.SectorOrth := by
  intro κ hκ
  obtain ⟨-, -, K, hK⟩ := g2ModeBounds
  have hdecH : ∃ C : ℝ, ∀ y : ℝ × ℝ, ‖fH (IIIa.planeToC y)‖ ≤
      C * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) :=
    ⟨K, fun y => by rw [← hMode_eq_fH]; exact (hK y).1⟩
  have hdecHc : ∃ C : ℝ, ∀ y : ℝ × ℝ, ‖(fun z => conj (fH z)) (IIIa.planeToC y)‖ ≤
      C * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) :=
    ⟨K, fun y => by simp only [Complex.norm_conj, ← hMode_eq_fH]; exact (hK y).1⟩
  have hdecR : ∃ C : ℝ, ∀ y : ℝ × ℝ, ‖fR (IIIa.planeToC y)‖ ≤
      C * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) :=
    ⟨K, fun y => by rw [← rMode_eq_fR]; exact (hK y).2⟩
  have hH_eq : fH = PartI.seedPlanar (fun r => ((gaussRdE 1 r : ℝ) : ℂ)) :=
    funext fH_eq_seedPlanar
  have hHc_eq : (fun z => conj (fH z)) =
      fun z => conj (PartI.seedPlanar (fun r => ((gaussRdE 1 r : ℝ) : ℂ)) z) := by
    funext z; rw [fH_eq_seedPlanar]
  have hHc_diff : ContDiff ℝ ∞ (fun z => conj (fH z)) :=
    Complex.conjCLE.contDiff.comp contDiff_fH
  have hS := seedSectors_proof (fun r => ((gaussRdE 1 r : ℝ) : ℂ))
  have h1 : ∫ y, κ.lamP 1 y * hMode 1 y = 0 := by
    simp_rw [hMode_eq_fH]
    apply (integral_lamP_zero_of_sector_zero κ hκ contDiff_fH hdecH).2
    intro r hr
    rw [hH_eq]
    exact (hS r hr).2.1
  have h2 : ∫ y, κ.lamP 0 y * conj (hMode 1 y) = 0 := by
    simp_rw [hMode_eq_fH]
    apply (integral_lamP_zero_of_sector_zero κ hκ hHc_diff hdecHc).1
    intro r hr
    rw [hHc_eq]
    exact (hS r hr).2.2.1
  have h30 : ∫ y, κ.lamP 0 y * rMode 1 y = 0 := by
    simp_rw [rMode_eq_fR]
    apply (integral_lamP_zero_of_sector_zero κ hκ contDiff_fR hdecR).1
    intro r _
    exact Planar.NUE.Polar.angularSector_eq_zero_of_rot_invariant fR_rot_invariant (by decide) r
  have h31 : ∫ y, κ.lamP 1 y * rMode 1 y = 0 := by
    simp_rw [rMode_eq_fR]
    apply (integral_lamP_zero_of_sector_zero κ hκ contDiff_fR hdecR).2
    intro r _
    exact Planar.NUE.Polar.angularSector_eq_zero_of_rot_invariant fR_rot_invariant (by decide) r
  refine ⟨h1, h2, fun i => ?_⟩
  fin_cases i
  · exact h30
  · exact h31

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G2
