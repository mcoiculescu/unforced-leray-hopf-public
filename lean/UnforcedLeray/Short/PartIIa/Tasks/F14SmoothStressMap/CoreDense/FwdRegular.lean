import UnforcedLeray.Short.PartIIa.Sub.F14_1_org.Defs
import UnforcedLeray.Short.PartIIa.Sub.F05_1
import UnforcedLeray.Short.PartIIa.Tasks.F05aAdjResolventSolution.HeatGaussSmooth
import UnforcedLeray.Short.PartIIa.Tasks.F05aAdjResolventSolution.HeatGaussInitial

/-!
# Part II-a, task `PartII-a:F14/1/1/1`: regularity of the forward integrand

Target: `FwdIntegrandRegular` (defined in `Sub/F14_1_org/Defs.lean`).

Source of record: `the November 2 reference manuscript`, lines 1370-1376.

Proof. Write `c(t) = exp(-(μ - 1/2) t)`, `s(t) = exp(t/2)`, `w(t) = fwdW ν t`, and
`fwdIntegrand ν μ f t p = c(t) • heatGauss f (w t) (p.1 + (-t), s(t) • p.2)`.
This is the forward analogue of `AdjIntegrandRegular`, with the shift `-t` in place of `+t` and the
dilation `s(t) = exp(t/2) ≥ 1` in place of `exp(-t/2) ≤ 1`. Since the dilation is at most
`exp(M/2)` on `[0, M]`, the bounds in (iv) use `‖s‖ ≤ exp(M/2)` in place of `‖s‖ ≤ 1`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

namespace UnforcedLeray.Short.PartIIa

namespace FwdIntegrandRegularAux

/-- The joint heat-flow map `(w, (τ, z)) ↦ heatGauss Φ₀ w (τ, z)`. -/
def fwJoint (Φ₀ : ℝ × Space → CVec3) : ℝ × (ℝ × Space) → CVec3 :=
  fun q => heatGauss Φ₀ q.1 q.2

/-- The linear part `(τ, y) ↦ (τ, s • y)`. -/
def fwScale (s : ℝ) : (ℝ × Space) →L[ℝ] (ℝ × Space) :=
  ContinuousLinearMap.prod (ContinuousLinearMap.fst ℝ ℝ Space)
    (s • ContinuousLinearMap.snd ℝ ℝ Space)

theorem fwScale_apply (s : ℝ) (p : ℝ × Space) : fwScale s p = (p.1, s • p.2) := rfl

/-- The linear map `p ↦ (0, (p.1, s • p.2))` into `ℝ × (ℝ × Space)`. -/
def fwLam (s : ℝ) : (ℝ × Space) →L[ℝ] (ℝ × (ℝ × Space)) :=
  ContinuousLinearMap.prod (0 : (ℝ × Space) →L[ℝ] ℝ) (fwScale s)

theorem fwLam_apply (s : ℝ) (p : ℝ × Space) : fwLam s p = (0, (p.1, s • p.2)) := rfl

/-- The translation vector `(-t, 0)`. -/
def fwShift (t : ℝ) : ℝ × Space := (-t, 0)

/-- The base point `(w(t), (-t, 0))` of the joint affine map. -/
def fwBase (ν t : ℝ) : ℝ × (ℝ × Space) := (fwdW ν t, fwShift t)

theorem norm_pair_scale_ge {s : ℝ} (hs1 : 1 ≤ s) (p : ℝ × Space) :
    ‖(p.1, s • p.2)‖ ≤ s * ‖p‖ := by
  have hs0 : 0 ≤ s := by linarith
  have hp1 : ‖p.1‖ ≤ s * ‖p‖ :=
    (norm_fst_le p).trans (le_mul_of_one_le_left (norm_nonneg p) hs1)
  have hs : ‖s • p.2‖ ≤ s * ‖p‖ := by
    rw [norm_smul, Real.norm_of_nonneg hs0]
    exact mul_le_mul_of_nonneg_left (norm_snd_le p) hs0
  exact norm_prod_le_iff.2 ⟨hp1, hs⟩

theorem norm_fwScale_le {s : ℝ} (hs1 : 1 ≤ s) : ‖fwScale s‖ ≤ s := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by linarith) (fun p => ?_)
  rw [fwScale_apply]
  exact norm_pair_scale_ge hs1 p

theorem continuous_fwScale : Continuous (fun t : ℝ => fwScale (Real.exp (t / 2))) := by
  have hexp : Continuous (fun t : ℝ => Real.exp (t / 2)) :=
    Real.continuous_exp.comp (continuous_id.div_const 2)
  have hfst : Continuous (fun _ : ℝ => ContinuousLinearMap.fst ℝ ℝ Space) := continuous_const
  have hsnd : Continuous (fun t : ℝ => Real.exp (t / 2) • ContinuousLinearMap.snd ℝ ℝ Space) :=
    hexp.smul continuous_const
  exact (ContinuousLinearMap.prodₗᵢ ℝ).continuous.comp (hfst.prodMk hsnd)

theorem continuous_fwLam : Continuous (fun t : ℝ => fwLam (Real.exp (t / 2))) := by
  have h0 : Continuous (fun _ : ℝ => (0 : (ℝ × Space) →L[ℝ] ℝ)) := continuous_const
  exact (ContinuousLinearMap.prodₗᵢ ℝ).continuous.comp (h0.prodMk continuous_fwScale)

theorem continuous_fwdW (ν : ℝ) : Continuous (fun t : ℝ => fwdW ν t) := by
  show Continuous (fun t : ℝ => Real.sqrt (ν * (Real.exp t - 1)))
  have h1 : Continuous (fun t : ℝ => Real.exp t - 1) :=
    Real.continuous_exp.sub continuous_const
  exact ((continuous_const : Continuous fun _ : ℝ => ν).mul h1).sqrt

theorem continuous_fwBase (ν : ℝ) : Continuous (fun t : ℝ => fwBase ν t) :=
  (continuous_fwdW ν).prodMk ((continuous_neg.prodMk (continuous_const : Continuous fun _ : ℝ => (0 : Space))))

theorem continuous_cExp (a : ℂ) :
    Continuous (fun t : ℝ => Complex.exp (-(a * (t : ℂ)))) := by
  have h : Continuous (fun t : ℝ => a * (t : ℂ)) :=
    continuous_const.mul Complex.continuous_ofReal
  exact Complex.continuous_exp.comp h.neg

/-- The slice form: `fwdIntegrand t = c(t) • heatGauss Φ₀ (w t) ∘ (· + (-t, 0)) ∘ scale`. -/
theorem fwdIntegrand_eq_slice (ν : ℝ) (μ : ℂ) (f : ℝ × Space → CVec3) (t : ℝ) :
    fwdIntegrand ν μ f t = fun p => Complex.exp (-((μ - 1 / 2) * (t : ℂ))) •
      heatGauss f (fwdW ν t) (fwScale (Real.exp (t / 2)) p + fwShift t) := by
  funext p
  simp only [fwdIntegrand, fwScale_apply, fwShift, Prod.mk_add_mk, add_zero, sub_eq_add_neg]

/-- The joint form: `fwdIntegrand t = c(t) • fwJoint Φ₀ ∘ (· + fwBase ν t) ∘ fwLam`. -/
theorem fwdIntegrand_eq_joint (ν : ℝ) (μ : ℂ) (f : ℝ × Space → CVec3) (t : ℝ) :
    fwdIntegrand ν μ f t = fun p => Complex.exp (-((μ - 1 / 2) * (t : ℂ))) •
      fwJoint f (fwLam (Real.exp (t / 2)) p + fwBase ν t) := by
  funext p
  simp only [fwdIntegrand, fwJoint, fwLam_apply, fwBase, fwShift, Prod.mk_add_mk,
    zero_add, add_zero, sub_eq_add_neg]

/-- The `k`-th derivative in terms of the slice `heatGauss Φ₀ (w t)`. -/
theorem iteratedFDeriv_fwd_slice (ν : ℝ) (μ : ℂ) (Φ₀ : ℝ × Space → CVec3)
    (hS : ∀ w : ℝ, ContDiff ℝ ∞ (heatGauss Φ₀ w)) (t : ℝ) (k : ℕ) (p : ℝ × Space) :
    iteratedFDeriv ℝ k (fwdIntegrand ν μ Φ₀ t) p =
      Complex.exp (-((μ - 1 / 2) * (t : ℂ))) •
        (iteratedFDeriv ℝ k (heatGauss Φ₀ (fwdW ν t))
          (fwScale (Real.exp (t / 2)) p + fwShift t)).compContinuousLinearMap
          (fun _ : Fin k => fwScale (Real.exp (t / 2))) := by
  have hf : ContDiff ℝ ∞ (fun z : ℝ × Space => heatGauss Φ₀ (fwdW ν t) (z + fwShift t)) :=
    (hS (fwdW ν t)).comp (contDiff_id.add contDiff_const)
  have hg : ContDiff ℝ ∞ ((fun z : ℝ × Space => heatGauss Φ₀ (fwdW ν t) (z + fwShift t)) ∘
      fwScale (Real.exp (t / 2))) :=
    hf.comp (fwScale (Real.exp (t / 2))).contDiff
  have hgk : ContDiffAt ℝ (k : WithTop ℕ∞)
      ((fun z : ℝ × Space => heatGauss Φ₀ (fwdW ν t) (z + fwShift t)) ∘
        fwScale (Real.exp (t / 2))) p :=
    hg.contDiffAt.of_le (by exact_mod_cast le_top)
  have e1 : (fun x : ℝ × Space => Complex.exp (-((μ - 1 / 2) * (t : ℂ))) •
      heatGauss Φ₀ (fwdW ν t) (fwScale (Real.exp (t / 2)) x + fwShift t)) =
      Complex.exp (-((μ - 1 / 2) * (t : ℂ))) •
        ((fun z : ℝ × Space => heatGauss Φ₀ (fwdW ν t) (z + fwShift t)) ∘
          fwScale (Real.exp (t / 2))) := rfl
  rw [fwdIntegrand_eq_slice ν μ Φ₀ t, e1, iteratedFDeriv_const_smul_apply hgk,
    (fwScale (Real.exp (t / 2))).iteratedFDeriv_comp_right (i := k) hf p
      (by exact_mod_cast le_top),
    iteratedFDeriv_comp_add_right]

/-- The `k`-th derivative in terms of the joint map `fwJoint Φ₀`. -/
theorem iteratedFDeriv_fwd_joint (ν : ℝ) (μ : ℂ) (Φ₀ : ℝ × Space → CVec3)
    (hJ : ContDiff ℝ ∞ (fwJoint Φ₀)) (t : ℝ) (k : ℕ) (p : ℝ × Space) :
    iteratedFDeriv ℝ k (fwdIntegrand ν μ Φ₀ t) p =
      Complex.exp (-((μ - 1 / 2) * (t : ℂ))) •
        (iteratedFDeriv ℝ k (fwJoint Φ₀)
          (fwLam (Real.exp (t / 2)) p + fwBase ν t)).compContinuousLinearMap
          (fun _ : Fin k => fwLam (Real.exp (t / 2))) := by
  have hf : ContDiff ℝ ∞ (fun z : ℝ × (ℝ × Space) => fwJoint Φ₀ (z + fwBase ν t)) :=
    hJ.comp (contDiff_id.add contDiff_const)
  have hg : ContDiff ℝ ∞ ((fun z : ℝ × (ℝ × Space) => fwJoint Φ₀ (z + fwBase ν t)) ∘
      fwLam (Real.exp (t / 2))) :=
    hf.comp (fwLam (Real.exp (t / 2))).contDiff
  have hgk : ContDiffAt ℝ (k : WithTop ℕ∞)
      ((fun z : ℝ × (ℝ × Space) => fwJoint Φ₀ (z + fwBase ν t)) ∘
        fwLam (Real.exp (t / 2))) p :=
    hg.contDiffAt.of_le (by exact_mod_cast le_top)
  have e1 : (fun x : ℝ × Space => Complex.exp (-((μ - 1 / 2) * (t : ℂ))) •
      fwJoint Φ₀ (fwLam (Real.exp (t / 2)) x + fwBase ν t)) =
      Complex.exp (-((μ - 1 / 2) * (t : ℂ))) •
        ((fun z : ℝ × (ℝ × Space) => fwJoint Φ₀ (z + fwBase ν t)) ∘
          fwLam (Real.exp (t / 2))) := rfl
  rw [fwdIntegrand_eq_joint ν μ Φ₀ t, e1, iteratedFDeriv_const_smul_apply hgk,
    (fwLam (Real.exp (t / 2))).iteratedFDeriv_comp_right (i := k) hf p
      (by exact_mod_cast le_top),
    iteratedFDeriv_comp_add_right]

/-- The phase factor has norm `exp(-(Re μ - 1/2) t)`. -/
theorem norm_cExp (μ : ℂ) (t : ℝ) :
    ‖Complex.exp (-((μ - 1 / 2) * (t : ℂ)))‖ = Real.exp (-(μ.re - 1 / 2) * t) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [Complex.neg_re, Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.sub_im, Complex.one_im, Complex.div_re, Complex.div_im]
  norm_num
  ring

/-- Norm bound for the `k`-th derivative: `‖D^k F_t(p)‖ ≤ e^{-(Re μ - 1/2)t} M (e^{t/2})^k`, for `t ≥ 0`,
when every slice has `‖D^k heatGauss Φ₀ w‖ ≤ M`. -/
theorem norm_iteratedFDeriv_fwdIntegrand_le (ν : ℝ) (μ : ℂ) (Φ₀ : ℝ × Space → CVec3)
    (hS : ∀ w : ℝ, ContDiff ℝ ∞ (heatGauss Φ₀ w)) (k : ℕ) (M : ℝ)
    (hM : ∀ (w : ℝ) (q : ℝ × Space), ‖iteratedFDeriv ℝ k (heatGauss Φ₀ w) q‖ ≤ M)
    (t : ℝ) (ht : 0 ≤ t) (p : ℝ × Space) :
    ‖iteratedFDeriv ℝ k (fwdIntegrand ν μ Φ₀ t) p‖ ≤
      Real.exp (-(μ.re - 1 / 2) * t) * (M * Real.exp (t / 2) ^ k) := by
  rw [iteratedFDeriv_fwd_slice ν μ Φ₀ hS t k p, norm_smul, norm_cExp]
  have hs1 : 1 ≤ Real.exp (t / 2) := Real.one_le_exp (by linarith)
  have h1 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ k (heatGauss Φ₀ (fwdW ν t)) (fwScale (Real.exp (t / 2)) p + fwShift t))
    (fun _ : Fin k => fwScale (Real.exp (t / 2)))
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
  have hpow : ‖fwScale (Real.exp (t / 2))‖ ^ k ≤ Real.exp (t / 2) ^ k :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_fwScale_le hs1) k
  have hX : ‖(iteratedFDeriv ℝ k (heatGauss Φ₀ (fwdW ν t))
      (fwScale (Real.exp (t / 2)) p + fwShift t)).compContinuousLinearMap
      (fun _ : Fin k => fwScale (Real.exp (t / 2)))‖ ≤ M * Real.exp (t / 2) ^ k := by
    refine h1.trans ?_
    have hB := hM (fwdW ν t) (fwScale (Real.exp (t / 2)) p + fwShift t)
    have hBn : 0 ≤ ‖iteratedFDeriv ℝ k (heatGauss Φ₀ (fwdW ν t))
        (fwScale (Real.exp (t / 2)) p + fwShift t)‖ := norm_nonneg _
    have hM0 : 0 ≤ M := hBn.trans hB
    exact mul_le_mul hB hpow (by positivity) hM0
  exact mul_le_mul_of_nonneg_left hX (Real.exp_pos _).le

/-- Continuity in `t` of the `k`-th derivative at each fixed point `p`, for all `t ∈ ℝ`. -/
theorem continuous_iteratedFDeriv_fwdIntegrand (ν : ℝ) (μ : ℂ) (Φ₀ : ℝ × Space → CVec3)
    (hJ : ContDiff ℝ ∞ (fwJoint Φ₀)) (k : ℕ) (p : ℝ × Space) :
    Continuous (fun t : ℝ => iteratedFDeriv ℝ k (fwdIntegrand ν μ Φ₀ t) p) := by
  have hT : Continuous (iteratedFDeriv ℝ k (fwJoint Φ₀)) :=
    hJ.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  have hp : Continuous (fun _ : ℝ => p) := continuous_const
  have hS : Continuous (fun t : ℝ => iteratedFDeriv ℝ k (fwJoint Φ₀)
      (fwLam (Real.exp (t / 2)) p + fwBase ν t)) :=
    hT.comp ((continuous_fwLam.clm_apply hp).add (continuous_fwBase ν))
  have hΨ : Continuous (fun t : ℝ =>
      (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
        ℝ (fun _ : Fin k => ℝ × Space) (fun _ : Fin k => ℝ × (ℝ × Space)) CVec3)
        (fun _ : Fin k => fwLam (Real.exp (t / 2)))) :=
    (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
      ℝ (fun _ : Fin k => ℝ × Space) (fun _ : Fin k => ℝ × (ℝ × Space)) CVec3).cont.comp
        (continuous_pi fun _ => continuous_fwLam)
  have hκ : Continuous (fun t : ℝ => Complex.exp (-((μ - 1 / 2) * (t : ℂ)))) :=
    continuous_cExp (μ - 1 / 2)
  have heq : (fun t : ℝ => iteratedFDeriv ℝ k (fwdIntegrand ν μ Φ₀ t) p) =
      fun t : ℝ => Complex.exp (-((μ - 1 / 2) * (t : ℂ))) •
        (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
          ℝ (fun _ : Fin k => ℝ × Space) (fun _ : Fin k => ℝ × (ℝ × Space)) CVec3)
          (fun _ : Fin k => fwLam (Real.exp (t / 2)))
          (iteratedFDeriv ℝ k (fwJoint Φ₀) (fwLam (Real.exp (t / 2)) p + fwBase ν t)) := by
    funext t
    rw [iteratedFDeriv_fwd_joint ν μ Φ₀ hJ t k p]
    rfl
  rw [heq]
  exact hκ.smul (hΨ.clm_apply hS)

end FwdIntegrandRegularAux

open FwdIntegrandRegularAux

theorem fwdIntegrandRegular : FwdIntegrandRegular := by
  intro P ν hP _hν μ f hf
  obtain ⟨hJ, hS, hB⟩ := heatGaussSmooth_proof P hP f hf
  have hI := heatGaussInitial_proof P hP f hf
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (i) smoothness for every `t`
    intro t
    have hF : ContDiff ℝ ∞
        (fun z : ℝ × Space => heatGauss f (fwdW ν t) (z + fwShift t)) :=
      (hS (fwdW ν t)).comp (contDiff_id.add contDiff_const)
    rw [fwdIntegrand_eq_slice ν μ f t]
    exact (hF.comp (fwScale (Real.exp (t / 2))).contDiff).const_smul
      (Complex.exp (-((μ - 1 / 2) * (t : ℂ))))
  · -- (ii) `P`-periodicity in `τ`
    intro t τ y
    simp only [fwdIntegrand]
    rw [show τ + P - t = τ - t + P by ring, hI.2]
  · -- (iii) continuity in `t`
    intro k p
    exact continuous_iteratedFDeriv_fwdIntegrand ν μ f hJ k p
  · -- (iv) uniform bound on `[0, M]`
    intro M k
    obtain ⟨Mk, hMk0, hMk⟩ := hB k
    refine ⟨Real.exp (|μ.re - 1 / 2| * M) * (Mk * Real.exp (M / 2) ^ k),
      by positivity, fun t ht p => ?_⟩
    obtain ⟨ht0, htM⟩ := ht
    have hA : -(μ.re - 1 / 2) * t ≤ |μ.re - 1 / 2| * M := by
      have h1 := mul_le_mul_of_nonneg_right (neg_le_abs (μ.re - 1 / 2)) ht0
      have h2 := mul_le_mul_of_nonneg_left htM (abs_nonneg (μ.re - 1 / 2))
      linarith
    have hE : Real.exp (t / 2) ^ k ≤ Real.exp (M / 2) ^ k :=
      pow_le_pow_left₀ (Real.exp_pos _).le (Real.exp_le_exp.2 (by linarith)) k
    have hbound := norm_iteratedFDeriv_fwdIntegrand_le ν μ f hS k Mk hMk t ht0 p
    refine hbound.trans ?_
    apply mul_le_mul (Real.exp_le_exp.2 hA) _ (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_left hE hMk0

end UnforcedLeray.Short.PartIIa
