import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S3_1_comoving
import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth.HigherOrderPhaseDeriv.SmoothLeraySlice
import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth.HigherOrderPhaseDeriv.ProjectedEvolutionTower.RadialDriftTower.LerayComm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# `PartII-b:S3/1/2/3` (`SmoothLerayComovingComm`, SP 2519-2523, 2552, 2559-2562)

Proof: along the comoving ray through `(τ, y)` consider the bounded reparametrised family
`Φ s z = F (τ + sin s) (e^{-sin s/2} z)`.  It is a uniform smooth `L⁴` family with phase jet
derivative `Ψ s z = cos s • F' (τ + sin s) (e^{-sin s/2} z)`; the accepted
`smoothLeraySliceRegularity_proof` and the dilation covariance of the Leray projection
(`smoothLerayProj_comp_scale`) then give the comoving jet derivative of `smoothLeraySlice F`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff BigOperators

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace
open UnforcedLeray.Short.IIb.SmoothLerayRadialDriftCommAux

local instance fact_one_le_four_lcc : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

namespace SmoothLerayComovingCommAux

/-- Ray scale `e^{-sin s / 2}`. -/
def lam (s : ℝ) : ℝ := Real.exp (-(Real.sin s) / 2)

theorem lam_pos (s : ℝ) : 0 < lam s := Real.exp_pos _

theorem half_le_lam (s : ℝ) : (1 / 2 : ℝ) ≤ lam s := by
  have h := Real.add_one_le_exp (-(Real.sin s) / 2)
  have h2 := Real.sin_le_one s
  unfold lam; linarith

theorem lam_le_two (s : ℝ) : lam s ≤ 2 := by
  have h1 := Real.add_one_le_exp (Real.sin s / 2)
  have hs := (abs_le.1 (Real.abs_sin_le_one s)).1
  have hmul : lam s * Real.exp (Real.sin s / 2) = 1 := by
    unfold lam
    rw [← Real.exp_add]
    have : -(Real.sin s) / 2 + Real.sin s / 2 = 0 := by ring
    rw [this, Real.exp_zero]
  have hE : (1 / 2 : ℝ) ≤ Real.exp (Real.sin s / 2) := by linarith
  nlinarith [mul_nonneg (sub_nonneg.2 hE) (lam_pos s).le]

theorem lam_ne_zero (s : ℝ) : lam s ≠ 0 := (lam_pos s).ne'

theorem abs_lam_le_two (s : ℝ) : |lam s| ≤ 2 := by
  rw [abs_of_pos (lam_pos s)]; exact lam_le_two s

theorem abs_inv_cube_lam_le_eight (s : ℝ) : |((lam s) ^ 3)⁻¹| ≤ 8 := by
  have hhalf : (1 / 2 : ℝ) ≤ lam s := half_le_lam s
  have hpos : (0 : ℝ) < (lam s) ^ 3 := pow_pos (lam_pos s) 3
  have hcube : (1 / 8 : ℝ) ≤ (lam s) ^ 3 := by
    calc (1 / 8 : ℝ) = (1 / 2 : ℝ) ^ 3 := by norm_num
      _ ≤ (lam s) ^ 3 := pow_le_pow_left₀ (by norm_num) hhalf 3
  rw [abs_inv, abs_of_pos hpos]
  calc ((lam s) ^ 3)⁻¹ ≤ (1 / 8 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hcube
    _ = 8 := by norm_num

theorem hasDerivAt_lam (s : ℝ) :
    HasDerivAt lam (lam s * (-(Real.cos s) / 2)) s := by
  unfold lam
  have h := ((Real.hasDerivAt_sin s).neg.div_const 2).exp
  simpa using h

/-- Uniformity of the reparametrised dilated family. -/
theorem sliceFamily_smul_comp_path {G : ℝ → SpatialField}
    (hG : IsUniformSmoothL4SliceFamily G) (σ : ℝ → ℝ)
    (c : ℝ → ℝ) {C_c : ℝ} (hCc0 : 0 ≤ C_c) (hc : ∀ s : ℝ, |c s| ≤ C_c) :
    IsUniformSmoothL4SliceFamily (fun s y => c s • G (σ s) (lam s • y)) := by
  have hf : ∀ s, ContDiff ℝ ∞ (G (σ s)) := fun s => HigherPhaseSub.sliceFamily_contDiff_infty hG (σ s)
  refine ⟨?_, ?_, ?_⟩
  · intro k s
    exact (contDiff_infty_smul_comp_scale (hf s) (c s) (lam s)).of_le (by exact_mod_cast le_top)
  · intro k
    obtain ⟨M, hM⟩ := hG.iteratedFDeriv_bounded k
    set M' : ℝ := max M 0
    have hM'0 : 0 ≤ M' := le_max_right M 0
    refine ⟨C_c * (2 : ℝ) ^ k * M', fun s y => ?_⟩
    rw [iteratedFDeriv_smul_comp_scale (hf s) (c s) (lam s) k y, norm_smul, Real.norm_eq_abs,
      abs_mul, abs_pow]
    have ha : |lam s| ^ k ≤ (2 : ℝ) ^ k :=
      pow_le_pow_left₀ (abs_nonneg _) (abs_lam_le_two s) k
    have hcoeff : |c s| * |lam s| ^ k ≤ C_c * (2 : ℝ) ^ k :=
      mul_le_mul (hc s) ha (pow_nonneg (abs_nonneg _) k) hCc0
    have hf_le : ‖iteratedFDeriv ℝ k (G (σ s)) (lam s • y)‖ ≤ M' :=
      (hM (σ s) (lam s • y)).trans (le_max_left M 0)
    exact mul_le_mul hcoeff hf_le (norm_nonneg _) (by positivity)
  · intro k
    obtain ⟨M, hM⟩ := hG.l4_bounded k
    set M' : ℝ := max M 0
    have hM'0 : 0 ≤ M' := le_max_right M 0
    set J : ℝ := (8 : ℝ) ^ (1 / (4 : ℝ≥0∞)).toReal
    have hJ0 : 0 ≤ J := Real.rpow_nonneg (by norm_num) _
    refine ⟨C_c * (2 : ℝ) ^ k * J * M', fun s => ?_⟩
    have hfun : (fun y : Space =>
        iteratedFDeriv ℝ k (fun z : Space => c s • G (σ s) (lam s • z)) y) =
        (c s * (lam s) ^ k) • fun y : Space => iteratedFDeriv ℝ k (G (σ s)) (lam s • y) := by
      funext y
      exact iteratedFDeriv_smul_comp_scale (hf s) (c s) (lam s) k y
    rw [hfun, eLpNorm_const_smul,
      eLpNorm_comp_dilation_any (lam_ne_zero s) (fun y => iteratedFDeriv ℝ k (G (σ s)) y)]
    have hcoeff_real : |c s * (lam s) ^ k| ≤ C_c * (2 : ℝ) ^ k := by
      rw [abs_mul, abs_pow]
      exact mul_le_mul (hc s)
        (pow_le_pow_left₀ (abs_nonneg _) (abs_lam_le_two s) k)
        (pow_nonneg (abs_nonneg _) k) hCc0
    have hcoeff : ‖c s * (lam s) ^ k‖ₑ ≤ ENNReal.ofReal (C_c * (2 : ℝ) ^ k) := by
      rw [Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal hcoeff_real
    have hjac : (ENNReal.ofReal |((lam s) ^ 3)⁻¹|) ^ (1 / (4 : ℝ≥0∞)).toReal ≤
        ENNReal.ofReal J := by
      rw [← ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by positivity)]
      exact ENNReal.rpow_le_rpow
        (ENNReal.ofReal_le_ofReal (abs_inv_cube_lam_le_eight s))
        (by positivity)
    have hf_l4 : eLpNorm (fun y : Space => iteratedFDeriv ℝ k (G (σ s)) y) 4 volume ≤
        ENNReal.ofReal M' :=
      (hM (σ s)).trans (ENNReal.ofReal_le_ofReal (le_max_left M 0))
    calc ‖c s * (lam s) ^ k‖ₑ *
          ((ENNReal.ofReal |((lam s) ^ 3)⁻¹|) ^ (1 / (4 : ℝ≥0∞)).toReal *
            eLpNorm (fun y : Space => iteratedFDeriv ℝ k (G (σ s)) y) 4 volume)
        ≤ ENNReal.ofReal (C_c * (2 : ℝ) ^ k) * (ENNReal.ofReal J * ENNReal.ofReal M') :=
          mul_le_mul' hcoeff (mul_le_mul' hjac hf_l4)
      _ = ENNReal.ofReal (C_c * (2 : ℝ) ^ k * J * M') := by
          rw [← ENNReal.ofReal_mul hJ0, ← ENNReal.ofReal_mul (by positivity)]
          ring_nf

theorem lam_pow_eq (n : ℕ) (s : ℝ) : lam s ^ n = Real.exp (-(n : ℝ) * Real.sin s / 2) := by
  unfold lam
  rw [← Real.exp_nat_mul]
  congr 1; ring

/-- Undo the reparametrisation `t = sin s` at `0`. -/
theorem hasDerivAt_of_sin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ℝ → E) (n : ℕ) (D : E)
    (hu : HasDerivAt (fun s : ℝ => lam s ^ n • v (Real.sin s)) D 0) :
    HasDerivAt v (D + ((n : ℝ) / 2) • v 0) 0 := by
  set w : ℝ → E := fun t => Real.exp (-(n : ℝ) * t / 2) • v t with hw
  have hu' : HasDerivAt (fun s : ℝ => w (Real.sin s)) D 0 := by
    refine hu.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
    simp only [hw, lam_pow_eq]
  have harc : HasDerivAt Real.arcsin 1 0 := by
    have := Real.hasDerivAt_arcsin (x := 0) (by norm_num) (by norm_num)
    simpa using this
  have hcomp : HasDerivAt ((fun s : ℝ => w (Real.sin s)) ∘ Real.arcsin) ((1 : ℝ) • D) 0 :=
    HasDerivAt.scomp_of_eq (x := 0) (y := 0) hu' harc (by simp)
  have hw' : HasDerivAt w D 0 := by
    rw [one_smul] at hcomp
    refine hcomp.congr_of_eventuallyEq ?_
    have hmem : Set.Ioo (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
    filter_upwards [hmem] with t ht
    simp [Function.comp, Real.sin_arcsin ht.1.le ht.2.le]
  have hexp : HasDerivAt (fun t : ℝ => Real.exp ((n : ℝ) * t / 2)) ((n : ℝ) / 2) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).const_mul (n : ℝ) |>.div_const 2).exp
    simpa using this
  have hv := hexp.smul hw'
  have hpt : ∀ t, v t = Real.exp ((n : ℝ) * t / 2) • w t := by
    intro t
    simp only [hw, smul_smul, ← Real.exp_add]
    have : (n : ℝ) * t / 2 + -(n : ℝ) * t / 2 = 0 := by ring
    rw [this]; simp
  have hv2 : HasDerivAt (fun t => Real.exp ((n : ℝ) * t / 2) • w t)
      (D + ((n : ℝ) / 2) • v 0) 0 := by
    have hv' : HasDerivAt (fun t => Real.exp ((n : ℝ) * t / 2) • w t)
        (Real.exp ((n : ℝ) * 0 / 2) • D + ((n : ℝ) / 2) • w 0) 0 := hv
    refine hv'.congr_deriv ?_
    simp [hw]
  exact hv2.congr_of_eventuallyEq (Eventually.of_forall hpt)

theorem hasPhaseJetDeriv_path {F F' : ℝ → SpatialField}
    (hF : IsUniformSmoothL4SliceFamily F) (hF' : IsUniformSmoothL4SliceFamily F')
    (hD : HasComovingJetDeriv F F') (τ : ℝ) :
    HasPhaseJetDeriv (fun s y => F (τ + Real.sin s) (lam s • y))
      (fun s y => Real.cos s • F' (τ + Real.sin s) (lam s • y)) := by
  intro ws s0 y
  have hfun : (fun s' : ℝ => dirSpatialJet (fun z : Space => F (τ + Real.sin s') (lam s' • z)) ws y) =
      fun s' => lam s' ^ ws.length • dirSpatialJet (F (τ + Real.sin s')) ws (lam s' • y) := by
    funext s'
    exact congrFun (dirSpatialJet_comp_scale
      (HigherPhaseSub.sliceFamily_contDiff_infty hF _) (lam s') ws) y
  have hrhs : dirSpatialJet (fun z : Space => Real.cos s0 • F' (τ + Real.sin s0) (lam s0 • z)) ws y =
      (Real.cos s0 * lam s0 ^ ws.length) •
        dirSpatialJet (F' (τ + Real.sin s0)) ws (lam s0 • y) :=
    congrFun (dirSpatialJet_smul_comp_scale
      (HigherPhaseSub.sliceFamily_contDiff_infty hF' _) _ _ ws) y
  show HasDerivAt (fun s' : ℝ => dirSpatialJet (fun z : Space => F (τ + Real.sin s') (lam s' • z)) ws y)
    (dirSpatialJet (fun z : Space => Real.cos s0 • F' (τ + Real.sin s0) (lam s0 • z)) ws y) s0
  rw [hfun, hrhs]
  set n := ws.length with hn
  set τ0 := τ + Real.sin s0 with hτ0
  set y0 := lam s0 • y with hy0
  set r : ℝ → ℝ := fun s => Real.sin s - Real.sin s0 with hrdef
  have hr : HasDerivAt r (Real.cos s0) s0 := (Real.hasDerivAt_sin s0).sub_const _
  set h : ℝ → Space := fun t => dirSpatialJet (F (τ0 + t)) ws (Real.exp (-t / 2) • y0) with hhdef
  have hh : HasDerivAt h (dirSpatialJet (F' τ0) ws y0 + ((n : ℝ) / 2) • dirSpatialJet (F τ0) ws y0) 0 :=
    hD ws τ0 y0
  have hcomp : HasDerivAt (h ∘ r)
      (Real.cos s0 • (dirSpatialJet (F' τ0) ws y0 + ((n : ℝ) / 2) • dirSpatialJet (F τ0) ws y0)) s0 :=
    HasDerivAt.scomp_of_eq (x := s0) (y := 0) hh hr (by simp [r])
  have hq : HasDerivAt (fun s => -(n : ℝ) * r s / 2) (-(n : ℝ) * Real.cos s0 / 2) s0 :=
    (hr.const_mul (-(n : ℝ))).div_const 2
  have hc : HasDerivAt (fun s => lam s0 ^ n * Real.exp (-(n : ℝ) * r s / 2))
      (lam s0 ^ n * (Real.exp (-(n : ℝ) * r s0 / 2) * (-(n : ℝ) * Real.cos s0 / 2))) s0 :=
    hq.exp.const_mul _
  have hprod := hc.smul hcomp
  have hkey : ∀ s, lam s ^ n • dirSpatialJet (F (τ + Real.sin s)) ws (lam s • y) =
      (lam s0 ^ n * Real.exp (-(n : ℝ) * r s / 2)) • (h ∘ r) s := by
    intro s
    have hl : lam s = lam s0 * Real.exp (-(r s) / 2) := by
      unfold lam; rw [← Real.exp_add]; congr 1; simp only [r]; ring
    have hpow : lam s ^ n = lam s0 ^ n * Real.exp (-(n : ℝ) * r s / 2) := by
      rw [hl, mul_pow, ← Real.exp_nat_mul]; congr 2; ring
    have hτ : τ0 + r s = τ + Real.sin s := by simp [τ0, r]
    have hy : Real.exp (-(r s) / 2) • y0 = lam s • y := by
      simp only [y0]; rw [smul_smul, hl, mul_comm]
    simp only [Function.comp, h]
    rw [hτ, hy, hpow]
  have hfun2 : (fun s => lam s ^ n • dirSpatialJet (F (τ + Real.sin s)) ws (lam s • y)) =
      fun s => (lam s0 ^ n * Real.exp (-(n : ℝ) * r s / 2)) • (h ∘ r) s := funext hkey
  rw [hfun2]
  refine hprod.congr_deriv ?_
  have hr0 : r s0 = 0 := by simp [r]
  have hh0 : (h ∘ r) s0 = dirSpatialJet (F τ0) ws y0 := by
    simp [Function.comp, hr0, h]
  rw [hh0, hr0]
  simp only [mul_zero, zero_div, Real.exp_zero, mul_one, one_mul, smul_add, smul_smul]
  module


end SmoothLerayComovingCommAux

end UnforcedLeray.Short.IIb

open UnforcedLeray UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.Short.IIb
  UnforcedLeray.Short.IIb.SmoothLerayComovingCommAux
  UnforcedLeray.Short.IIb.SmoothLerayRadialDriftCommAux in
theorem smoothLerayComovingComm_proof : UnforcedLeray.Short.IIb.SmoothLerayComovingComm := by
  intro F F' hF hF' hD ws τ y
  set Φ : ℝ → SpatialField := fun s z => F (τ + Real.sin s) (lam s • z) with hΦdef
  set Ψ : ℝ → SpatialField := fun s z => Real.cos s • F' (τ + Real.sin s) (lam s • z) with hΨdef
  have hΦ : IsUniformSmoothL4SliceFamily Φ := by
    have := sliceFamily_smul_comp_path hF (fun s => τ + Real.sin s) (fun _ => (1 : ℝ))
      (C_c := 1) (by norm_num) (fun _ => by norm_num)
    simpa [Φ, one_smul] using this
  have hΨ : IsUniformSmoothL4SliceFamily Ψ :=
    sliceFamily_smul_comp_path hF' (fun s => τ + Real.sin s) Real.cos (C_c := 1) (by norm_num)
      Real.abs_cos_le_one
  have hdΦ : HasPhaseJetDeriv Φ Ψ := hasPhaseJetDeriv_path hF hF' hD τ
  have hreg := smoothLeraySliceRegularity_proof
  have hderiv := hreg.2 Φ Ψ hΦ hΨ hdΦ ws 0 y
  have hrep : ∀ σ : ℝ, IsSmoothLerayRep (F σ) (smoothLeraySlice F σ) :=
    fun σ => (hreg.1 F hF).1 σ
  have hslice : ∀ s : ℝ, smoothLeraySlice Φ s =
      fun z => smoothLeraySlice F (τ + Real.sin s) (lam s • z) := fun s =>
    smoothLerayProj_comp_scale (f := F (τ + Real.sin s)) (hrep _) (lam_pos s)
  have hjet : ∀ s : ℝ, dirSpatialJet (smoothLeraySlice Φ s) ws y =
      lam s ^ ws.length • dirSpatialJet (smoothLeraySlice F (τ + Real.sin s)) ws (lam s • y) := by
    intro s
    rw [hslice s]
    exact congrFun (dirSpatialJet_comp_scale (hrep _).2.1 (lam s) ws) y
  have hΨ0 : smoothLeraySlice Ψ 0 = smoothLeraySlice F' τ := by
    have : Ψ 0 = F' τ := by
      funext z; simp [Ψ, lam]
    change smoothLerayProj (Ψ 0) = smoothLerayProj (F' τ)
    rw [this]
  have hu : HasDerivAt (fun s : ℝ => lam s ^ ws.length •
      dirSpatialJet (smoothLeraySlice F (τ + Real.sin s)) ws
        (Real.exp (-(Real.sin s) / 2) • y))
      (dirSpatialJet (smoothLeraySlice F' τ) ws y) 0 := by
    rw [hΨ0] at hderiv
    refine hderiv.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
    show _ = dirSpatialJet (smoothLeraySlice Φ s) ws y
    rw [hjet s]
    rfl
  have := hasDerivAt_of_sin
    (fun t : ℝ => dirSpatialJet (smoothLeraySlice F (τ + t)) ws (Real.exp (-t / 2) • y))
    ws.length _ hu
  simpa using this

end
