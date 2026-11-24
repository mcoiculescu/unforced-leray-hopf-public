import UnforcedLeray.Short.PartIIa.Sub.F05_1
import UnforcedLeray.Short.PartIIa.Tasks.F05aAdjResolventSolution.HeatGaussSmooth
import UnforcedLeray.Short.PartIIa.Tasks.F05aAdjResolventSolution.HeatGaussInitial

/-!
# Part II-a, task `PartII-a:F05a`: regularity of the adjoint-resolvent integrand

Target: `AdjIntegrandRegular` (defined in `Short/PartII-a/Sub/F05_1.lean`).

Source of record: `the November 2 reference manuscript`, lines 1403-1413.

Proof. With `c(t) = exp(-(μ+1) t)`, `s(t) = exp(-t/2)` and `w(t) = adjW ν t`,
`adjIntegrand ν μ Φ₀ t p = c(t) • heatGauss Φ₀ (w t) (p.1 + t, s(t) • p.2)`.
* (i) Smoothness: slice `heatGauss Φ₀ w` (smooth by `HeatGaussSmooth`) composed with an affine map.
* (ii) Periodicity: `HeatGaussInitial`, after `(τ + P) + t = (τ + t) + P`.
* (iii) Measurability: the derivatives are continuous in `t` on all of `ℝ`. They are written through
  the joint map `(w, q) ↦ heatGauss Φ₀ w q`, whose derivatives are jointly continuous.
* (iv) Bound: the linear part `p ↦ (p.1, s • p.2)` has norm `≤ 1` for `0 ≤ s ≤ 1`, so the slice
  bound controls the integrand, and `‖c(t)‖ = exp(-(Re μ + 1) t)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

namespace UnforcedLeray.Short.PartIIa

namespace AdjIntegrandRegularAux

/-- The joint heat-flow map `(w, (τ, z)) ↦ heatGauss Φ₀ w (τ, z)`. -/
def arJoint (Φ₀ : ℝ × Space → CVec3) : ℝ × (ℝ × Space) → CVec3 :=
  fun q => heatGauss Φ₀ q.1 q.2

/-- The linear part `(τ, y) ↦ (τ, s • y)` of the affine map `p ↦ (p.1 + t, s • p.2)`. -/
def arScale (s : ℝ) : (ℝ × Space) →L[ℝ] (ℝ × Space) :=
  ContinuousLinearMap.prod (ContinuousLinearMap.fst ℝ ℝ Space)
    (s • ContinuousLinearMap.snd ℝ ℝ Space)

theorem arScale_apply (s : ℝ) (p : ℝ × Space) : arScale s p = (p.1, s • p.2) := rfl

/-- The linear map `p ↦ (0, (p.1, s • p.2))` into `ℝ × (ℝ × Space)`. -/
def arLam (s : ℝ) : (ℝ × Space) →L[ℝ] (ℝ × (ℝ × Space)) :=
  ContinuousLinearMap.prod (0 : (ℝ × Space) →L[ℝ] ℝ) (arScale s)

theorem arLam_apply (s : ℝ) (p : ℝ × Space) : arLam s p = (0, (p.1, s • p.2)) := rfl

/-- The translation vector `(t, 0)`. -/
def arShift (t : ℝ) : ℝ × Space := (t, 0)

/-- The base point `(w(t), (t, 0))` of the joint affine map. -/
def arBase (ν t : ℝ) : ℝ × (ℝ × Space) := (adjW ν t, (t, 0))

theorem norm_pair_scale_le {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) (p : ℝ × Space) :
    ‖(p.1, s • p.2)‖ ≤ ‖p‖ := by
  have hp1 : ‖p.1‖ ≤ ‖p‖ := norm_fst_le p
  have hp2 : ‖p.2‖ ≤ ‖p‖ := norm_snd_le p
  have hs : ‖s • p.2‖ ≤ ‖p‖ := by
    rw [norm_smul, Real.norm_of_nonneg h0]
    exact (mul_le_of_le_one_left (norm_nonneg _) h1).trans hp2
  exact norm_prod_le_iff.2 ⟨hp1, hs⟩

theorem norm_arScale_le {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) : ‖arScale s‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun p => ?_)
  rw [one_mul, arScale_apply]
  exact norm_pair_scale_le h0 h1 p

theorem norm_arLam_le {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) : ‖arLam s‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun p => ?_)
  rw [one_mul, arLam_apply]
  exact norm_prod_le_iff.2 ⟨by simp, norm_pair_scale_le h0 h1 p⟩

theorem continuous_arScale : Continuous (fun t : ℝ => arScale (Real.exp (-t / 2))) := by
  have hexp : Continuous (fun t : ℝ => Real.exp (-t / 2)) :=
    Real.continuous_exp.comp (continuous_neg.div_const 2)
  have hfst : Continuous (fun _ : ℝ => ContinuousLinearMap.fst ℝ ℝ Space) := continuous_const
  have hsnd : Continuous (fun t : ℝ => Real.exp (-t / 2) • ContinuousLinearMap.snd ℝ ℝ Space) :=
    hexp.smul continuous_const
  exact (ContinuousLinearMap.prodₗᵢ ℝ).continuous.comp (hfst.prodMk hsnd)

theorem continuous_arLam : Continuous (fun t : ℝ => arLam (Real.exp (-t / 2))) := by
  have h0 : Continuous (fun _ : ℝ => (0 : (ℝ × Space) →L[ℝ] ℝ)) := continuous_const
  exact (ContinuousLinearMap.prodₗᵢ ℝ).continuous.comp (h0.prodMk continuous_arScale)

theorem continuous_adjW (ν : ℝ) : Continuous (fun t : ℝ => adjW ν t) := by
  show Continuous (fun t : ℝ => Real.sqrt (ν * (1 - Real.exp (-t))))
  have h1 : Continuous (fun t : ℝ => 1 - Real.exp (-t)) :=
    continuous_const.sub (Real.continuous_exp.comp continuous_neg)
  exact ((continuous_const : Continuous fun _ : ℝ => ν).mul h1).sqrt

theorem continuous_arBase (ν : ℝ) : Continuous (fun t : ℝ => arBase ν t) :=
  (continuous_adjW ν).prodMk
    (continuous_id.prodMk (continuous_const : Continuous fun _ : ℝ => (0 : Space)))

theorem continuous_cExp (μ : ℂ) :
    Continuous (fun t : ℝ => Complex.exp (-((μ + 1) * (t : ℂ)))) := by
  have h : Continuous (fun t : ℝ => (μ + 1) * (t : ℂ)) :=
    continuous_const.mul Complex.continuous_ofReal
  exact Complex.continuous_exp.comp h.neg

/-- The slice form: `adjIntegrand t = c(t) • heatGauss Φ₀ (w t) ∘ (· + (t, 0)) ∘ scale`. -/
theorem adjIntegrand_eq_slice (ν : ℝ) (μ : ℂ) (Φ₀ : ℝ × Space → CVec3) (t : ℝ) :
    adjIntegrand ν μ Φ₀ t = fun p => Complex.exp (-((μ + 1) * (t : ℂ))) •
      heatGauss Φ₀ (adjW ν t) (arScale (Real.exp (-t / 2)) p + arShift t) := by
  funext p
  simp only [adjIntegrand, arScale_apply, arShift, Prod.mk_add_mk, add_zero]

/-- The joint form: `adjIntegrand t = c(t) • arJoint Φ₀ ∘ (· + arBase ν t) ∘ arLam`. -/
theorem adjIntegrand_eq_joint (ν : ℝ) (μ : ℂ) (Φ₀ : ℝ × Space → CVec3) (t : ℝ) :
    adjIntegrand ν μ Φ₀ t = fun p => Complex.exp (-((μ + 1) * (t : ℂ))) •
      arJoint Φ₀ (arLam (Real.exp (-t / 2)) p + arBase ν t) := by
  funext p
  simp only [adjIntegrand, arJoint, arLam_apply, arBase, Prod.mk_add_mk, zero_add, add_zero]

/-- The `k`-th derivative in terms of the slice `heatGauss Φ₀ (w t)`. -/
theorem iteratedFDeriv_adjIntegrand_slice (ν : ℝ) (μ : ℂ) (Φ₀ : ℝ × Space → CVec3)
    (hS : ∀ w : ℝ, ContDiff ℝ ∞ (heatGauss Φ₀ w)) (t : ℝ) (k : ℕ) (p : ℝ × Space) :
    iteratedFDeriv ℝ k (adjIntegrand ν μ Φ₀ t) p =
      Complex.exp (-((μ + 1) * (t : ℂ))) •
        (iteratedFDeriv ℝ k (heatGauss Φ₀ (adjW ν t))
          (arScale (Real.exp (-t / 2)) p + arShift t)).compContinuousLinearMap
          (fun _ : Fin k => arScale (Real.exp (-t / 2))) := by
  have hf : ContDiff ℝ ∞ (fun z : ℝ × Space => heatGauss Φ₀ (adjW ν t) (z + arShift t)) :=
    (hS (adjW ν t)).comp (contDiff_id.add contDiff_const)
  have hg : ContDiff ℝ ∞ ((fun z : ℝ × Space => heatGauss Φ₀ (adjW ν t) (z + arShift t)) ∘
      arScale (Real.exp (-t / 2))) :=
    hf.comp (arScale (Real.exp (-t / 2))).contDiff
  have hgk : ContDiffAt ℝ (k : WithTop ℕ∞)
      ((fun z : ℝ × Space => heatGauss Φ₀ (adjW ν t) (z + arShift t)) ∘
        arScale (Real.exp (-t / 2))) p :=
    hg.contDiffAt.of_le (by exact_mod_cast le_top)
  have e1 : (fun x : ℝ × Space => Complex.exp (-((μ + 1) * (t : ℂ))) •
      heatGauss Φ₀ (adjW ν t) (arScale (Real.exp (-t / 2)) x + arShift t)) =
      Complex.exp (-((μ + 1) * (t : ℂ))) •
        ((fun z : ℝ × Space => heatGauss Φ₀ (adjW ν t) (z + arShift t)) ∘
          arScale (Real.exp (-t / 2))) := rfl
  rw [adjIntegrand_eq_slice ν μ Φ₀ t, e1, iteratedFDeriv_const_smul_apply hgk,
    (arScale (Real.exp (-t / 2))).iteratedFDeriv_comp_right (i := k) hf p
      (by exact_mod_cast le_top),
    iteratedFDeriv_comp_add_right]

/-- The `k`-th derivative in terms of the joint map `arJoint Φ₀`. -/
theorem iteratedFDeriv_adjIntegrand_joint (ν : ℝ) (μ : ℂ) (Φ₀ : ℝ × Space → CVec3)
    (hJ : ContDiff ℝ ∞ (arJoint Φ₀)) (t : ℝ) (k : ℕ) (p : ℝ × Space) :
    iteratedFDeriv ℝ k (adjIntegrand ν μ Φ₀ t) p =
      Complex.exp (-((μ + 1) * (t : ℂ))) •
        (iteratedFDeriv ℝ k (arJoint Φ₀)
          (arLam (Real.exp (-t / 2)) p + arBase ν t)).compContinuousLinearMap
          (fun _ : Fin k => arLam (Real.exp (-t / 2))) := by
  have hf : ContDiff ℝ ∞ (fun z : ℝ × (ℝ × Space) => arJoint Φ₀ (z + arBase ν t)) :=
    hJ.comp (contDiff_id.add contDiff_const)
  have hg : ContDiff ℝ ∞ ((fun z : ℝ × (ℝ × Space) => arJoint Φ₀ (z + arBase ν t)) ∘
      arLam (Real.exp (-t / 2))) :=
    hf.comp (arLam (Real.exp (-t / 2))).contDiff
  have hgk : ContDiffAt ℝ (k : WithTop ℕ∞)
      ((fun z : ℝ × (ℝ × Space) => arJoint Φ₀ (z + arBase ν t)) ∘
        arLam (Real.exp (-t / 2))) p :=
    hg.contDiffAt.of_le (by exact_mod_cast le_top)
  have e1 : (fun x : ℝ × Space => Complex.exp (-((μ + 1) * (t : ℂ))) •
      arJoint Φ₀ (arLam (Real.exp (-t / 2)) x + arBase ν t)) =
      Complex.exp (-((μ + 1) * (t : ℂ))) •
        ((fun z : ℝ × (ℝ × Space) => arJoint Φ₀ (z + arBase ν t)) ∘
          arLam (Real.exp (-t / 2))) := rfl
  rw [adjIntegrand_eq_joint ν μ Φ₀ t, e1, iteratedFDeriv_const_smul_apply hgk,
    (arLam (Real.exp (-t / 2))).iteratedFDeriv_comp_right (i := k) hf p
      (by exact_mod_cast le_top),
    iteratedFDeriv_comp_add_right]

/-- Norm bound: `‖D^k F_t(p)‖ ≤ M exp(-(Re μ + 1) t)` for `t ≥ 0`, when every slice has
`‖D^k heatGauss Φ₀ w‖ ≤ M`. -/
theorem norm_iteratedFDeriv_adjIntegrand_le (ν : ℝ) (μ : ℂ) (Φ₀ : ℝ × Space → CVec3)
    (hS : ∀ w : ℝ, ContDiff ℝ ∞ (heatGauss Φ₀ w)) (k : ℕ) (M : ℝ)
    (hM : ∀ (w : ℝ) (q : ℝ × Space), ‖iteratedFDeriv ℝ k (heatGauss Φ₀ w) q‖ ≤ M)
    (t : ℝ) (ht : 0 ≤ t) (p : ℝ × Space) :
    ‖iteratedFDeriv ℝ k (adjIntegrand ν μ Φ₀ t) p‖ ≤ M * Real.exp (-(μ.re + 1) * t) := by
  rw [iteratedFDeriv_adjIntegrand_slice ν μ Φ₀ hS t k p, norm_smul]
  have hc : ‖Complex.exp (-((μ + 1) * (t : ℂ)))‖ = Real.exp (-(μ.re + 1) * t) := by
    rw [Complex.norm_exp]
    congr 1
    simp only [Complex.neg_re, Complex.mul_re, Complex.add_re, Complex.one_re,
      Complex.ofReal_re, Complex.add_im, Complex.one_im, Complex.ofReal_im]
    ring
  rw [hc]
  have hs0 : 0 ≤ Real.exp (-t / 2) := (Real.exp_pos _).le
  have hs1 : Real.exp (-t / 2) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h1 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ k (heatGauss Φ₀ (adjW ν t)) (arScale (Real.exp (-t / 2)) p + arShift t))
    (fun _ : Fin k => arScale (Real.exp (-t / 2)))
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
  have hpow : ‖arScale (Real.exp (-t / 2))‖ ^ k ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) (norm_arScale_le hs0 hs1)
  have hX : ‖(iteratedFDeriv ℝ k (heatGauss Φ₀ (adjW ν t))
      (arScale (Real.exp (-t / 2)) p + arShift t)).compContinuousLinearMap
      (fun _ : Fin k => arScale (Real.exp (-t / 2)))‖ ≤ M :=
    h1.trans ((mul_le_of_le_one_right (norm_nonneg _) hpow).trans (hM _ _))
  rw [mul_comm M]
  exact mul_le_mul_of_nonneg_left hX (Real.exp_pos _).le

/-- Continuity in `t` of the `k`-th derivative at each fixed point `p`, for all `t ∈ ℝ`. -/
theorem continuous_iteratedFDeriv_adjIntegrand (ν : ℝ) (μ : ℂ) (Φ₀ : ℝ × Space → CVec3)
    (hJ : ContDiff ℝ ∞ (arJoint Φ₀)) (k : ℕ) (p : ℝ × Space) :
    Continuous (fun t : ℝ => iteratedFDeriv ℝ k (adjIntegrand ν μ Φ₀ t) p) := by
  have hT : Continuous (iteratedFDeriv ℝ k (arJoint Φ₀)) :=
    hJ.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  have hp : Continuous (fun _ : ℝ => p) := continuous_const
  have hS : Continuous (fun t : ℝ => iteratedFDeriv ℝ k (arJoint Φ₀)
      (arLam (Real.exp (-t / 2)) p + arBase ν t)) :=
    hT.comp ((continuous_arLam.clm_apply hp).add (continuous_arBase ν))
  have hΨ : Continuous (fun t : ℝ =>
      (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
        ℝ (fun _ : Fin k => ℝ × Space) (fun _ : Fin k => ℝ × (ℝ × Space)) CVec3)
        (fun _ : Fin k => arLam (Real.exp (-t / 2)))) :=
    (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
      ℝ (fun _ : Fin k => ℝ × Space) (fun _ : Fin k => ℝ × (ℝ × Space)) CVec3).cont.comp
        (continuous_pi fun _ => continuous_arLam)
  have hκ : Continuous (fun t : ℝ => Complex.exp (-((μ + 1) * (t : ℂ)))) := continuous_cExp μ
  have heq : (fun t : ℝ => iteratedFDeriv ℝ k (adjIntegrand ν μ Φ₀ t) p) =
      fun t : ℝ => Complex.exp (-((μ + 1) * (t : ℂ))) •
        (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
          ℝ (fun _ : Fin k => ℝ × Space) (fun _ : Fin k => ℝ × (ℝ × Space)) CVec3)
          (fun _ : Fin k => arLam (Real.exp (-t / 2)))
          (iteratedFDeriv ℝ k (arJoint Φ₀) (arLam (Real.exp (-t / 2)) p + arBase ν t)) := by
    funext t
    rw [iteratedFDeriv_adjIntegrand_joint ν μ Φ₀ hJ t k p]
    rfl
  rw [heq]
  exact hκ.smul (hΨ.clm_apply hS)

end AdjIntegrandRegularAux

open AdjIntegrandRegularAux

theorem adjIntegrandRegular_proof : UnforcedLeray.Short.PartIIa.AdjIntegrandRegular := by
  intro P ν hP _hν μ _hμ Φ₀ hΦ
  obtain ⟨hJ, hS, hB⟩ := heatGaussSmooth_proof P hP Φ₀ hΦ
  have hI := heatGaussInitial_proof P hP Φ₀ hΦ
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (i) smoothness for `t > 0` (in fact for all `t`)
    intro t _
    have hf : ContDiff ℝ ∞
        (fun z : ℝ × Space => heatGauss Φ₀ (adjW ν t) (z + arShift t)) :=
      (hS (adjW ν t)).comp (contDiff_id.add contDiff_const)
    rw [adjIntegrand_eq_slice ν μ Φ₀ t]
    exact (hf.comp (arScale (Real.exp (-t / 2))).contDiff).const_smul
      (Complex.exp (-((μ + 1) * (t : ℂ))))
  · -- (ii) `P`-periodicity in `τ`
    intro t τ y
    simp only [adjIntegrand]
    rw [show τ + P + t = τ + t + P by ring, hI.2]
  · -- (iii) a.e.-measurability in `t` on `(0, ∞)`
    intro k p
    exact (continuous_iteratedFDeriv_adjIntegrand ν μ Φ₀ hJ k p).aestronglyMeasurable
  · -- (iv) uniform exponential bound
    intro k
    obtain ⟨M, hM0, hM⟩ := hB k
    exact ⟨M, hM0, fun t ht p =>
      norm_iteratedFDeriv_adjIntegrand_le ν μ Φ₀ hS k M hM t ht.le p⟩

end UnforcedLeray.Short.PartIIa
