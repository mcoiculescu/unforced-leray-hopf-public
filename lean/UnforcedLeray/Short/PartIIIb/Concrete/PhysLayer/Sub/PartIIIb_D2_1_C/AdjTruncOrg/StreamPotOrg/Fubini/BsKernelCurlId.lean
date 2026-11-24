import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.BsKernelWeakDeriv
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.BsNewtonLaplace
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.BsKernelLocInt
import UnforcedLeray.Analysis.Pressure.NewtonIdentity
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The kernel curl identity (BSKernelCurlId)

For `Θ ∈ C_c^∞(ℝ³; ℂ³)`:  `∫ K(y-z) × curl Θ(y) dy = Θ(z) + ∫ div Θ(y) K(y-z) dy`, where
`K = bsKernel = -(Newton gradient kernel)` and `P = 1/(4π|x|)`.

Componentwise, `(K × curl Θ)_a = ∑_b K_b (∂_a Θ_b - ∂_b Θ_a)`.  The weak derivative of `P`
(`bsKernelWeakDeriv`) turns `∫ K_b ∂_a Θ_b` into `∫ P ∂_b∂_a Θ_b`; summing over `b` and using
symmetry of second derivatives gives `∫ P ∂_a div Θ = ∫ K_a div Θ`; the Newton identity
(`bsNewtonLaplace`) gives `∑_b ∫ P ∂_b∂_b Θ_a = -Θ_a(z)`.

Source: `the November 2 reference manuscript`, the stream potential
`ψ = curl(Newton * Φ)`, `curl ψ = Φ` (the spec's line range 1351-1362 is the free Cartesian equation).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The Newton potential `1/(4π|x|)` as a complex-valued kernel. -/
private abbrev newtonC (w : Space) : ℂ := ((UnforcedLeray.PressureAnalysis.newtonPotential w : ℝ) : ℂ)

private theorem newtonC_comm (y z : Space) : newtonC (z - y) = newtonC (y - z) := by
  unfold newtonC UnforcedLeray.PressureAnalysis.newtonPotential
  rw [norm_sub_rev]

private theorem newtonC_locInt : LocallyIntegrable newtonC volume := by
  have h2 := Complex.ofRealCLM.locallyIntegrableOn_comp
    (UnforcedLeray.PressureAnalysis.newtonPotential_locallyIntegrable.locallyIntegrableOn univ)
  rw [locallyIntegrableOn_univ] at h2
  have heq : newtonC = Complex.ofRealCLM ∘ UnforcedLeray.PressureAnalysis.newtonPotential := by
    funext w
    simp [newtonC]
  rw [heq]
  exact h2

/-- `y ↦ newtonC (y - z) * g y` is integrable for continuous compactly supported `g`. -/
private theorem P_mul_integrable (z : Space) (g : Space → ℂ) (hg : Continuous g)
    (hgc : HasCompactSupport g) : Integrable (fun y : Space => newtonC (y - z) * g y) := by
  have h1 : Integrable (fun x : Space => newtonC x * g (x + z)) := by
    have hcont : Continuous (fun x : Space => g (x + z)) :=
      hg.comp (continuous_id.add continuous_const)
    have hcs : HasCompactSupport (fun x : Space => g (x + z)) :=
      hgc.comp_homeomorph (Homeomorph.addRight z)
    have := newtonC_locInt.integrable_smul_right_of_hasCompactSupport hcont hcs
    simpa [smul_eq_mul] using this
  have h2 := h1.comp_sub_right z
  simpa using h2

/-- `y ↦ g(y) • K(y - z)` is integrable for continuous compactly supported `g`. -/
private theorem bsKernel_shift_integrable (g : Space → ℂ) (hg : Continuous g)
    (hgc : HasCompactSupport g) (z : Space) :
    Integrable (fun y : Space => g y • bsKernel (y - z)) := by
  have h1 : Integrable (fun x : Space => g (x + z) • bsKernel x) := by
    have hcont : Continuous (fun x : Space => g (x + z)) :=
      hg.comp (continuous_id.add continuous_const)
    have hcs : HasCompactSupport (fun x : Space => g (x + z)) :=
      hgc.comp_homeomorph (Homeomorph.addRight z)
    exact bsKernelLocInt.integrable_smul_left_of_hasCompactSupport hcont hcs
  have h2 := h1.comp_sub_right z
  simpa using h2

/-- `y ↦ K_b(y - z) * g y` is integrable for continuous compactly supported `g`. -/
private theorem K_mul_integrable (z : Space) (b : Fin 3) (g : Space → ℂ) (hg : Continuous g)
    (hgc : HasCompactSupport g) : Integrable (fun y : Space => bsKernel (y - z) b * g y) := by
  have h := bsKernel_shift_integrable g hg hgc z
  have h3 := (EuclideanSpace.proj b : EuclideanSpace ℂ (Fin 3) →L[ℂ] ℂ).integrable_comp h
  refine h3.congr (ae_of_all _ fun y => ?_)
  simp [mul_comm]

/-- A vector-valued function with integrable components is integrable. -/
private theorem integrable_of_comps (F : Space → EuclideanSpace ℂ (Fin 3))
    (hF : ∀ i : Fin 3, Integrable (fun y => F y i)) : Integrable F := by
  have hsum : Integrable (fun y : Space =>
      ∑ i : Fin 3, F y i • (EuclideanSpace.single i (1 : ℂ) : EuclideanSpace ℂ (Fin 3))) :=
    integrable_finsetSum _ (fun i _ => (hF i).smul_const _)
  refine hsum.congr (ae_of_all _ fun y => ?_)
  ext j
  fin_cases j <;> simp [Fin.sum_univ_three]

/-- Integral of a vector-valued function, componentwise. -/
private theorem integral_comp_apply (F : Space → EuclideanSpace ℂ (Fin 3)) (hF : Integrable F)
    (a : Fin 3) : (∫ y, F y) a = ∫ y, F y a := by
  have h := ContinuousLinearMap.integral_comp_comm
    (EuclideanSpace.proj a : EuclideanSpace ℂ (Fin 3) →L[ℂ] ℂ) hF
  simpa using h.symm

/-- Fréchet derivative of a continuous linear image. -/
private theorem cc_fderiv {V W G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (ℓ : (V →L[ℝ] W) →L[ℝ] G) {f : V → W} {y : V} (hD : DifferentiableAt ℝ (fderiv ℝ f) y)
    (w : V) :
    fderiv ℝ (fun x => ℓ (fderiv ℝ f x)) y w = ℓ (fderiv ℝ (fderiv ℝ f) y w) := by
  have h := (ℓ.hasFDerivAt (x := fderiv ℝ f y)).comp y hD.hasFDerivAt
  show fderiv ℝ (ℓ ∘ fderiv ℝ f) y w = _
  rw [h.fderiv]
  rfl

/-- Derivative of a component of a differentiable vector field. -/
private theorem fderiv_proj_apply {Θ : Space → EuclideanSpace ℂ (Fin 3)} {y : Space}
    (hΘ : DifferentiableAt ℝ Θ y) (c : Fin 3) (v : Space) :
    fderiv ℝ (fun x => Θ x c) y v = fderiv ℝ Θ y v c := by
  have hL := ((EuclideanSpace.proj c : EuclideanSpace ℂ (Fin 3) →L[ℂ] ℂ).restrictScalars ℝ).hasFDerivAt
    (x := Θ y)
  have h := hL.comp y hΘ.hasFDerivAt
  show fderiv ℝ (((EuclideanSpace.proj c : EuclideanSpace ℂ (Fin 3) →L[ℂ] ℂ).restrictScalars ℝ) ∘ Θ) y v = _
  rw [h.fderiv]
  rfl

/-- Second derivative of a component. -/
private theorem fderiv_comp_v_b {Θ : Space → EuclideanSpace ℂ (Fin 3)} {y : Space}
    (hD : DifferentiableAt ℝ (fderiv ℝ Θ) y) (v w : Space) (b : Fin 3) :
    fderiv ℝ (fun x => fderiv ℝ Θ x v b) y w = fderiv ℝ (fderiv ℝ Θ) y w v b :=
  cc_fderiv (((EuclideanSpace.proj b : EuclideanSpace ℂ (Fin 3) →L[ℂ] ℂ).restrictScalars ℝ).comp
    (ContinuousLinearMap.apply ℝ (EuclideanSpace ℂ (Fin 3)) v)) hD w

/-- Divergence derivative. -/
private theorem fderiv_divS {Θ : Space → EuclideanSpace ℂ (Fin 3)} {y : Space}
    (hD : DifferentiableAt ℝ (fderiv ℝ Θ) y) (v : Space) :
    fderiv ℝ (bsDivS Θ) y v
      = ∑ c : Fin 3, fderiv ℝ (fderiv ℝ Θ) y v (EuclideanSpace.single c (1 : ℝ)) c := by
  have hfun : bsDivS Θ = fun x => (∑ c : Fin 3,
      ((EuclideanSpace.proj c : EuclideanSpace ℂ (Fin 3) →L[ℂ] ℂ).restrictScalars ℝ).comp
        (ContinuousLinearMap.apply ℝ (EuclideanSpace ℂ (Fin 3)) (EuclideanSpace.single c (1 : ℝ))))
          (fderiv ℝ Θ x) := by
    funext x
    simp [bsDivS, ContinuousLinearMap.sum_apply]
  rw [hfun, cc_fderiv _ hD v]
  simp [ContinuousLinearMap.sum_apply]

/-- Pointwise curl formula in components. -/
private theorem crossC_curl_apply (K : EuclideanSpace ℂ (Fin 3))
    (Θ : Space → EuclideanSpace ℂ (Fin 3)) (y : Space) (a : Fin 3) :
    (crossC K (bsCurlS Θ y)) a = ∑ b : Fin 3,
      K b * (fderiv ℝ Θ y (EuclideanSpace.single a (1 : ℝ)) b
        - fderiv ℝ Θ y (EuclideanSpace.single b (1 : ℝ)) a) := by
  simp only [bsCurlS, crossC, Fin.sum_univ_three]
  fin_cases a <;> simp [EuclideanSpace.single_apply] <;> ring

/-- Smoothness and compact support of a directional derivative. -/
private theorem cs_fderiv_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : Space → E} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hc : HasCompactSupport φ)
    (v : Space) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => fderiv ℝ φ y v) ∧
      HasCompactSupport (fun y => fderiv ℝ φ y v) := by
  refine ⟨?_, ?_⟩
  · have hD := (contDiff_infty_iff_fderiv.mp hφ).2
    exact (ContinuousLinearMap.apply ℝ E v).contDiff.comp hD
  · exact (hc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Space →L[ℝ] E => L v) (by simp)

/-- Smoothness and compact support of a component. -/
private theorem cs_comp {φ : Space → EuclideanSpace ℂ (Fin 3)}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hc : HasCompactSupport φ) (b : Fin 3) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => φ y b) ∧ HasCompactSupport (fun y => φ y b) :=
  ⟨((EuclideanSpace.proj b : EuclideanSpace ℂ (Fin 3) →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp hφ,
    hc.comp_left (g := fun c : EuclideanSpace ℂ (Fin 3) => c b) (by simp)⟩

/-- **Kernel curl identity**. -/
theorem bsKernelCurlId : BSKernelCurlId := by
  intro Θ hΘ hΘc z
  have hΘd : ∀ y : Space, DifferentiableAt ℝ Θ y := fun y => hΘ.differentiable (by simp) y
  have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ Θ) := (contDiff_infty_iff_fderiv.mp hΘ).2
  have hDiff : ∀ y : Space, DifferentiableAt ℝ (fderiv ℝ Θ) y :=
    fun y => hD.differentiable (by simp) y
  have hsym : ∀ (y v w : Space), fderiv ℝ (fderiv ℝ Θ) y v w = fderiv ℝ (fderiv ℝ Θ) y w v :=
    fun y v w => (hΘ.contDiffAt (x := y)).isSymmSndFDerivAt (by simp) v w
  have hcΘ : ∀ v : Space, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => fderiv ℝ Θ y v) ∧
      HasCompactSupport (fun y => fderiv ℝ Θ y v) :=
    fun v => cs_fderiv_apply hΘ hΘc v
  have hA : ∀ a b : Fin 3, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y => fderiv ℝ Θ y (EuclideanSpace.single a (1 : ℝ)) b) ∧
      HasCompactSupport (fun y => fderiv ℝ Θ y (EuclideanSpace.single a (1 : ℝ)) b) :=
    fun a b => cs_comp (φ := fun y => fderiv ℝ Θ y (EuclideanSpace.single a (1 : ℝ)))
      (hcΘ _).1 (hcΘ _).2 b
  have hθ : ∀ a : Fin 3, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => Θ y a) ∧
      HasCompactSupport (fun y => Θ y a) :=
    fun a => cs_comp hΘ hΘc a
  have hB : ∀ a b : Fin 3, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y => fderiv ℝ (fun x => Θ x a) y (EuclideanSpace.single b (1 : ℝ))) ∧
      HasCompactSupport (fun y => fderiv ℝ (fun x => Θ x a) y (EuclideanSpace.single b (1 : ℝ))) :=
    fun a b => cs_fderiv_apply (hθ a).1 (hθ a).2 _
  have hAA : ∀ a b c : Fin 3, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y => fderiv ℝ (fun x => fderiv ℝ Θ x (EuclideanSpace.single a (1 : ℝ)) b) y
        (EuclideanSpace.single c (1 : ℝ))) ∧
      HasCompactSupport (fun y => fderiv ℝ (fun x => fderiv ℝ Θ x (EuclideanSpace.single a (1 : ℝ)) b) y
        (EuclideanSpace.single c (1 : ℝ))) :=
    fun a b c => cs_fderiv_apply (hA a b).1 (hA a b).2 _
  have hBB : ∀ a b : Fin 3, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y => fderiv ℝ (fun x => fderiv ℝ (fun x => Θ x a) x (EuclideanSpace.single b (1 : ℝ))) y
        (EuclideanSpace.single b (1 : ℝ))) ∧
      HasCompactSupport (fun y => fderiv ℝ (fun x => fderiv ℝ (fun x => Θ x a) x
        (EuclideanSpace.single b (1 : ℝ))) y (EuclideanSpace.single b (1 : ℝ))) :=
    fun a b => cs_fderiv_apply (hB a b).1 (hB a b).2 _
  have hdiv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (bsDivS Θ) ∧ HasCompactSupport (bsDivS Θ) := by
    have e : bsDivS Θ = fun y => fderiv ℝ Θ y (EuclideanSpace.single 0 (1 : ℝ)) 0
        + fderiv ℝ Θ y (EuclideanSpace.single 1 (1 : ℝ)) 1
        + fderiv ℝ Θ y (EuclideanSpace.single 2 (1 : ℝ)) 2 := by
      funext y
      simp [bsDivS, Fin.sum_univ_three, add_assoc]
    rw [e]
    exact ⟨((hA 0 0).1.add (hA 1 1).1).add (hA 2 2).1,
      ((hA 0 0).2.add (hA 1 1).2).add (hA 2 2).2⟩
  have hkey : ∀ (y : Space) (a : Fin 3), ∑ b : Fin 3,
      fderiv ℝ (fun x => fderiv ℝ Θ x (EuclideanSpace.single a (1 : ℝ)) b) y
        (EuclideanSpace.single b (1 : ℝ))
      = fderiv ℝ (bsDivS Θ) y (EuclideanSpace.single a (1 : ℝ)) := by
    intro y a
    rw [fderiv_divS (hDiff y)]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [fderiv_comp_v_b (hDiff y), hsym y]
  have P1 : ∀ (y : Space) (a : Fin 3),
      (crossC (bsKernel (y - z)) (bsCurlS Θ y)) a = ∑ b : Fin 3, bsKernel (y - z) b *
        (fderiv ℝ Θ y (EuclideanSpace.single a (1 : ℝ)) b
          - fderiv ℝ (fun x => Θ x a) y (EuclideanSpace.single b (1 : ℝ))) := by
    intro y a
    rw [crossC_curl_apply]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [fderiv_proj_apply (hΘd y) a (EuclideanSpace.single b (1 : ℝ))]
  have intKA : ∀ a b : Fin 3, Integrable (fun y : Space =>
      bsKernel (y - z) b * fderiv ℝ Θ y (EuclideanSpace.single a (1 : ℝ)) b) :=
    fun a b => K_mul_integrable z b (fun y => fderiv ℝ Θ y (EuclideanSpace.single a (1 : ℝ)) b)
      (hA a b).1.continuous (hA a b).2
  have intKB : ∀ a b : Fin 3, Integrable (fun y : Space =>
      bsKernel (y - z) b * fderiv ℝ (fun x => Θ x a) y (EuclideanSpace.single b (1 : ℝ))) :=
    fun a b => K_mul_integrable z b (fun y => fderiv ℝ (fun x => Θ x a) y (EuclideanSpace.single b (1 : ℝ)))
      (hB a b).1.continuous (hB a b).2
  have hintL : Integrable (fun y : Space => crossC (bsKernel (y - z)) (bsCurlS Θ y)) := by
    apply integrable_of_comps
    intro i
    refine (integrable_finsetSum Finset.univ (fun b _ => (intKA i b).sub (intKB i b))).congr
      (ae_of_all _ fun y => ?_)
    simp only [P1, mul_sub, Pi.sub_apply]
  have hintR : Integrable (fun y : Space => bsDivS Θ y • bsKernel (y - z)) :=
    bsKernel_shift_integrable (bsDivS Θ) hdiv.1.continuous hdiv.2 z
  have WD : ∀ (h : Space → ℂ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h → HasCompactSupport h →
      ∀ j : Fin 3, ∫ y : Space, bsKernel (y - z) j * h y
        = ∫ y : Space, newtonC (y - z) * fderiv ℝ h y (EuclideanSpace.single j (1 : ℝ)) :=
    fun h hh hc j => (bsKernelWeakDeriv h hh hc z j).symm
  have NL : ∀ a : Fin 3, ∫ y : Space, newtonC (y - z) * bsLapS (fun y => Θ y a) y = -(Θ z a) :=
    fun a => bsNewtonLaplace (fun y => Θ y a) (hθ a).1 (hθ a).2 z
  have hsumA : ∀ a : Fin 3, ∑ b : Fin 3, ∫ y : Space, bsKernel (y - z) b * fderiv ℝ Θ y
      (EuclideanSpace.single a (1 : ℝ)) b
      = ∫ y : Space, bsKernel (y - z) a * bsDivS Θ y := by
    intro a
    calc ∑ b : Fin 3, ∫ y : Space, bsKernel (y - z) b * fderiv ℝ Θ y
          (EuclideanSpace.single a (1 : ℝ)) b
        = ∑ b : Fin 3, ∫ y : Space, newtonC (y - z) * fderiv ℝ
            (fun y => fderiv ℝ Θ y (EuclideanSpace.single a (1 : ℝ)) b) y
              (EuclideanSpace.single b (1 : ℝ)) :=
          Finset.sum_congr rfl (fun b _ => WD _ (hA a b).1 (hA a b).2 b)
      _ = ∫ y : Space, ∑ b : Fin 3, newtonC (y - z) * fderiv ℝ
            (fun y => fderiv ℝ Θ y (EuclideanSpace.single a (1 : ℝ)) b) y
              (EuclideanSpace.single b (1 : ℝ)) :=
          (integral_finsetSum _ (fun b _ => P_mul_integrable z _
            (hAA a b b).1.continuous (hAA a b b).2)).symm
      _ = ∫ y : Space, newtonC (y - z) * fderiv ℝ (bsDivS Θ) y
            (EuclideanSpace.single a (1 : ℝ)) := by
          congr 1
          funext y
          rw [← Finset.mul_sum, hkey y a]
      _ = ∫ y : Space, bsKernel (y - z) a * bsDivS Θ y :=
          (WD (bsDivS Θ) hdiv.1 hdiv.2 a).symm
  have hsumB : ∀ a : Fin 3, ∑ b : Fin 3, ∫ y : Space, bsKernel (y - z) b * fderiv ℝ
      (fun x => Θ x a) y (EuclideanSpace.single b (1 : ℝ)) = -(Θ z a) := by
    intro a
    calc ∑ b : Fin 3, ∫ y : Space, bsKernel (y - z) b * fderiv ℝ (fun x => Θ x a) y
          (EuclideanSpace.single b (1 : ℝ))
        = ∑ b : Fin 3, ∫ y : Space, newtonC (y - z) * fderiv ℝ
            (fun y => fderiv ℝ (fun x => Θ x a) y (EuclideanSpace.single b (1 : ℝ))) y
              (EuclideanSpace.single b (1 : ℝ)) :=
          Finset.sum_congr rfl (fun b _ => WD _ (hB a b).1 (hB a b).2 b)
      _ = ∫ y : Space, ∑ b : Fin 3, newtonC (y - z) * fderiv ℝ
            (fun y => fderiv ℝ (fun x => Θ x a) y (EuclideanSpace.single b (1 : ℝ))) y
              (EuclideanSpace.single b (1 : ℝ)) :=
          (integral_finsetSum _ (fun b _ => P_mul_integrable z _
            (hBB a b).1.continuous (hBB a b).2)).symm
      _ = ∫ y : Space, newtonC (y - z) * bsLapS (fun y => Θ y a) y := by
          congr 1
          funext y
          rw [← Finset.mul_sum]
          rfl
      _ = -(Θ z a) := NL a
  ext a
  have hLa : ∫ y : Space, (crossC (bsKernel (y - z)) (bsCurlS Θ y)) a
      = ∑ b : Fin 3, ((∫ y : Space, bsKernel (y - z) b * fderiv ℝ Θ y
          (EuclideanSpace.single a (1 : ℝ)) b)
        - (∫ y : Space, bsKernel (y - z) b * fderiv ℝ (fun x => Θ x a) y
          (EuclideanSpace.single b (1 : ℝ)))) := by
    have hfun : (fun y : Space => (crossC (bsKernel (y - z)) (bsCurlS Θ y)) a)
        = fun y : Space => ∑ b : Fin 3, (bsKernel (y - z) b * fderiv ℝ Θ y
            (EuclideanSpace.single a (1 : ℝ)) b
          - bsKernel (y - z) b * fderiv ℝ (fun x => Θ x a) y (EuclideanSpace.single b (1 : ℝ))) := by
      funext y
      rw [P1 y a]
      simp only [mul_sub]
    rw [hfun, integral_finsetSum (f := fun b y => bsKernel (y - z) b * fderiv ℝ Θ y
        (EuclideanSpace.single a (1 : ℝ)) b
          - bsKernel (y - z) b * fderiv ℝ (fun x => Θ x a) y (EuclideanSpace.single b (1 : ℝ)))
        Finset.univ (fun b _ => (intKA a b).sub (intKB a b))]
    exact Finset.sum_congr rfl (fun b _ => integral_sub (intKA a b) (intKB a b))
  have hRa : ∀ y : Space, (bsDivS Θ y • bsKernel (y - z)) a = bsKernel (y - z) a * bsDivS Θ y :=
    fun y => by simp [mul_comm]
  rw [PiLp.add_apply, integral_comp_apply _ hintL a, hLa, Finset.sum_sub_distrib, hsumA a, hsumB a,
    integral_comp_apply _ hintR a]
  simp only [hRa]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
