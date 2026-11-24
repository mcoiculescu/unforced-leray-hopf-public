import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.Defs
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Group.Integral

/-!
# `BSSol`: the Biot-Savart potential is weakly solenoidal

Source `the November 2 reference manuscript` lines 1334-1337 (`Y_r` is the plain
`L^r` of `(ℝ/Pℤ) × ℝ³`), 1351-1362 (the Coulomb-gauge stream potential `ψ = curl(N * Φ)` of the
solenoidal cutoff, `div ψ = 0`), 1470-1480 (radial cutoffs).

For `Φ ∈ Y_2` and a scalar phase test `φ`, `⟨∇φ, bsPot Φ⟩ = 0`.  For a.e. phase `t` the slice
`Φ(t,·)` is in `L²` (`BSSliceL2`) and the Fubini swap (`BSFubiniSwap`) moves the `y`-integral onto
the kernel:
`∫ ∇φ(t,y) · bsPot Φ(t,y) dy = ∫ Φ(t,z) · (∫ K(y-z) × ∇φ(t,y) dy) dz`.
The new ingredient is that gradients are curl-free against the kernel (`BSGradCurlFree`):
`∫ K_j(y-z) ∂ₖφ(t,y) dy = ∫ N(y-z) ∂ⱼ∂ₖφ(t,y) dy` (`BSKernelWeakDeriv`, `K = -∇N`) is symmetric
in `j, k` by symmetry of second derivatives, so every component of `∫ K(y-z) × ∇φ(t,y) dy`
vanishes.  The weak solenoidality of `Φ` is not used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-! ## Calculus on slices -/

/-- The `k`-th component of the phase gradient is the `k`-th spatial derivative. -/
theorem bsSol_gradT_apply (φ : ℝ × Space → ℂ) (p : ℝ × Space) (k : Fin 3) :
    gradT φ p k = dy k φ p := by
  simp [gradT, Pi.single_apply]

/-- The spatial derivative of a phase function is the derivative of its slice. -/
theorem bsSol_dy_slice {φ : ℝ × Space → ℂ} (hφ : Differentiable ℝ φ) (t : ℝ) (y : Space)
    (k : Fin 3) :
    dy k φ (t, y) =
      fderiv ℝ (fun y' : Space => φ (t, y')) y (EuclideanSpace.single k (1 : ℝ)) := by
  have hemb : HasFDerivAt (fun y' : Space => ((t, y') : ℝ × Space))
      (ContinuousLinearMap.inr ℝ ℝ Space) y :=
    (hasFDerivAt_const t y).prodMk (hasFDerivAt_id y)
  have hcomp : HasFDerivAt (fun y' : Space => φ (t, y'))
      ((fderiv ℝ φ (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ Space)) y :=
    (hφ (t, y)).hasFDerivAt.comp y hemb
  rw [hcomp.fderiv]
  rfl

theorem bsSol_fderiv_apply_formula {h : Space → ℂ} (hh : ContDiff ℝ ∞ h) (v w x : Space) :
    fderiv ℝ (fun y => fderiv ℝ h y w) x v = fderiv ℝ (fderiv ℝ h) x v w := by
  have hd : Differentiable ℝ (fderiv ℝ h) :=
    (hh.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have hx : HasFDerivAt (fun y => fderiv ℝ h y w) ((fderiv ℝ (fderiv ℝ h) x).flip w) x := by
    simpa using (hd x).hasFDerivAt.clm_apply (hasFDerivAt_const w x)
  rw [hx.fderiv]
  rfl

/-- Symmetry of second derivatives of a smooth `ℂ`-valued function on `ℝ³`. -/
theorem bsSol_fderiv_apply_comm {h : Space → ℂ} (hh : ContDiff ℝ ∞ h) (v w x : Space) :
    fderiv ℝ (fun y => fderiv ℝ h y w) x v = fderiv ℝ (fun y => fderiv ℝ h y v) x w := by
  rw [bsSol_fderiv_apply_formula hh v w x, bsSol_fderiv_apply_formula hh w v x]
  exact (hh.contDiffAt.isSymmSndFDerivAt (by simp)).eq v w

/-! ## The kernel against gradients -/

/-- `K = -∇N` componentwise (`PressureAnalysis.newtonGradientKernel` is `∂ᵢN`). -/
theorem bsSol_kernel_apply (w : Space) (a : Fin 3) :
    bsKernel w a = ((-(UnforcedLeray.PressureAnalysis.newtonGradientKernel a w) : ℝ) : ℂ) := by
  simp only [bsKernel, PiLp.toLp_apply, UnforcedLeray.PressureAnalysis.newtonGradientKernel]
  push_cast
  ring

/-- `y ↦ K_a(y - z) g(y)` is integrable for continuous compactly supported `g` (`K` is locally
integrable). -/
theorem bsSol_integrable_kernel_mul (a : Fin 3) {g : Space → ℂ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (z : Space) :
    Integrable (fun y : Space => bsKernel (y - z) a * g y) := by
  have hg' : Continuous (fun w : Space => g (w + z)) := hg.comp (continuous_add_const z)
  have hgc' : HasCompactSupport (fun w : Space => g (w + z)) :=
    hgc.comp_homeomorph (Homeomorph.addRight z)
  have h0 : Integrable (fun w : Space =>
      (-UnforcedLeray.PressureAnalysis.newtonGradientKernel a) w • g (w + z)) :=
    (UnforcedLeray.PressureAnalysis.newtonGradientKernel_locallyIntegrable a).neg.integrable_smul_right_of_hasCompactSupport
      hg' hgc'
  have h1 := h0.comp_sub_right z
  refine h1.congr (Eventually.of_forall fun y => ?_)
  simp only [Pi.neg_apply, sub_add_cancel, bsSol_kernel_apply, Complex.real_smul]

/-- Kernel symmetry: `∫ K_j(y-z) ∂ₖh(y) dy = ∫ K_k(y-z) ∂ⱼh(y) dy`, both being
`∫ N(y-z) ∂ⱼ∂ₖh(y) dy` (`BSKernelWeakDeriv`, symmetry of second derivatives). -/
theorem bsSol_kernel_symm (hW : BSKernelWeakDeriv) {h : Space → ℂ} (hh : ContDiff ℝ ∞ h)
    (hc : HasCompactSupport h) (z : Space) (j k : Fin 3) :
    ∫ y : Space, bsKernel (y - z) j * fderiv ℝ h y (EuclideanSpace.single k (1 : ℝ)) =
      ∫ y : Space, bsKernel (y - z) k * fderiv ℝ h y (EuclideanSpace.single j (1 : ℝ)) := by
  have hd : ∀ v : Space, ContDiff ℝ ∞ (fun y => fderiv ℝ h y v) := fun v =>
    (hh.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hdc : ∀ v : Space, HasCompactSupport (fun y => fderiv ℝ h y v) := fun v =>
    hc.fderiv_apply ℝ v
  have e1 := hW (fun y => fderiv ℝ h y (EuclideanSpace.single k (1 : ℝ))) (hd _) (hdc _) z j
  have e2 := hW (fun y => fderiv ℝ h y (EuclideanSpace.single j (1 : ℝ))) (hd _) (hdc _) z k
  beta_reduce at e1 e2
  rw [← e1, ← e2]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [bsSol_fderiv_apply_comm hh]

/-- **Gradients are curl-free against the Biot-Savart kernel** (source 1351-1362, the Coulomb
gauge `div ψ = 0` of `ψ = curl(N * Φ)`: `K = -∇N`, so
`∫ K(y-z) × ∇φ(t,y) dy = ∫ N(y-z) curl ∇φ(t,y) dy = 0`): for every scalar phase test `φ`,
every phase `t` and every point `z`. -/
def BSGradCurlFree : Prop :=
  ∀ (P : ℝ) (φ : ℝ × Space → ℂ), IsPhaseTest P φ → ∀ (t : ℝ) (z : Space),
    ∫ y : Space, crossC (bsKernel (y - z)) (gradT φ (t, y)) = 0

theorem bsGradCurlFree_of (hW : BSKernelWeakDeriv) : BSGradCurlFree := by
  intro P φ hφ t z
  have hh : ContDiff ℝ ∞ (fun y : Space => φ (t, y)) :=
    hφ.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hc : HasCompactSupport (fun y : Space => φ (t, y)) := hφ.hasCompactSupport_slice t
  have hdiff : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
  have hg : ∀ (y : Space) (k : Fin 3), gradT φ (t, y) k =
      fderiv ℝ (fun y' : Space => φ (t, y')) y (EuclideanSpace.single k (1 : ℝ)) := by
    intro y k
    rw [bsSol_gradT_apply, bsSol_dy_slice hdiff]
  have hcont : ∀ k : Fin 3, Continuous (fun y : Space =>
      fderiv ℝ (fun y' : Space => φ (t, y')) y (EuclideanSpace.single k (1 : ℝ))) := fun k =>
    (hh.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcs : ∀ k : Fin 3, HasCompactSupport (fun y : Space =>
      fderiv ℝ (fun y' : Space => φ (t, y')) y (EuclideanSpace.single k (1 : ℝ))) := fun k =>
    hc.fderiv_apply ℝ _
  have hint : ∀ a k : Fin 3, Integrable (fun y : Space => bsKernel (y - z) a *
      fderiv ℝ (fun y' : Space => φ (t, y')) y (EuclideanSpace.single k (1 : ℝ))) :=
    fun a k => bsSol_integrable_kernel_mul a (hcont k) (hcs k) z
  have hcomp : ∀ a b : Fin 3, ∫ y : Space, (bsKernel (y - z) a * gradT φ (t, y) b -
      bsKernel (y - z) b * gradT φ (t, y) a) = 0 := by
    intro a b
    simp only [hg]
    rw [integral_sub (hint a b) (hint b a), bsSol_kernel_symm hW hh hc z a b, sub_self]
  by_cases hF : Integrable (fun y : Space => crossC (bsKernel (y - z)) (gradT φ (t, y)))
  · have e : ∀ i : Fin 3, (∫ y : Space, crossC (bsKernel (y - z)) (gradT φ (t, y))) i =
        ∫ y : Space, (crossC (bsKernel (y - z)) (gradT φ (t, y))) i := by
      intro i
      simpa using ((EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).integral_comp_comm hF).symm
    ext i
    rw [e i]
    fin_cases i
    · simpa [crossC] using hcomp 1 2
    · simpa [crossC] using hcomp 2 0
    · simpa [crossC] using hcomp 0 1
  · exact integral_undef hF

/-! ## Assembly -/

/-- **`BSSol` from the Fubini infrastructure**: for a.e. phase the slice is `L²`, the Fubini swap
moves the pairing onto the kernel, and the kernel annihilates gradients. -/
theorem bsSol_of (hSw : BSFubiniSwap) (hL2 : BSSliceL2) (hC : BSGradCurlFree) : BSSol := by
  intro P hP Φ hΦ _ φ hφ
  have hG : IsPhaseTest P (gradT φ) := hφ.gradT
  have hae : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Ioc (0 : ℝ) P)),
      ∫ y : Space, dotL (gradT φ (t, y)) (bsPot Φ (t, y)) = 0 := by
    refine ae_restrict_of_ae ?_
    filter_upwards [hL2 P hP Φ hΦ] with t ht
    have h1 := hSw (fun y => gradT φ (t, y)) (hG.continuous_slice t)
      (hG.hasCompactSupport_slice t) (fun z => Φ (t, z)) ht
    have h2 : ∀ z : Space, ∫ y : Space, crossC (bsKernel (y - z)) (gradT φ (t, y)) = 0 :=
      hC P φ hφ t
    simp only [h2, map_zero, integral_zero] at h1
    exact h1
  have hzero : ∫ t in Ioc (0 : ℝ) P, ∫ y : Space, dotL (gradT φ (t, y)) (bsPot Φ (t, y)) = 0 :=
    integral_eq_zero_of_ae hae
  unfold pairF phaseInt
  simp only [hzero, smul_zero]

/-- `BSSol` from the Fubini swap, the slice `L²` property and the weak derivative of the Newton
potential (all in `Fubini/Defs.lean`). -/
theorem bsSol_of' (hSw : BSFubiniSwap) (hL2 : BSSliceL2) (hW : BSKernelWeakDeriv) : BSSol :=
  bsSol_of hSw hL2 (bsGradCurlFree_of hW)

end UnforcedLeray.Short.PartIIIb.Concrete
