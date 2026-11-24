import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

namespace GradAux

theorem diffC {G : ℝ × Space → ℂ} (h : ContDiff ℝ ∞ G) : Differentiable ℝ G :=
  h.differentiable (by simp)

theorem cdDy {φ : ℝ × Space → ℂ} (h : ContDiff ℝ ∞ φ) (j : Fin 3) :
    ContDiff ℝ ∞ (dy j φ) := by
  unfold dy
  exact (h.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem cdDτ {φ : ℝ × Space → ℂ} (h : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (dτ φ) := by
  unfold dτ
  exact (h.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem fdFormula {Φ : ℝ × Space → ℂ} (h : ContDiff ℝ ∞ Φ) (v w p : ℝ × Space) :
    fderiv ℝ (fun q => fderiv ℝ Φ q w) p v = fderiv ℝ (fderiv ℝ Φ) p v w := by
  have hd : Differentiable ℝ (fderiv ℝ Φ) :=
    (h.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have hx : HasFDerivAt (fun y => fderiv ℝ Φ y w) ((fderiv ℝ (fderiv ℝ Φ) p).flip w) p := by
    simpa using (hd p).hasFDerivAt.clm_apply (hasFDerivAt_const w p)
  rw [hx.fderiv]
  rfl

theorem fdComm {Φ : ℝ × Space → ℂ} (h : ContDiff ℝ ∞ Φ) (v w p : ℝ × Space) :
    fderiv ℝ (fun q => fderiv ℝ Φ q w) p v = fderiv ℝ (fun q => fderiv ℝ Φ q v) p w := by
  rw [fdFormula h v w p, fdFormula h w v p]
  exact (h.contDiffAt.isSymmSndFDerivAt (by simp)).eq v w

theorem dy_dy_comm' {Φ : ℝ × Space → ℂ} (h : ContDiff ℝ ∞ Φ) (j k : Fin 3) :
    dy j (dy k Φ) = dy k (dy j Φ) :=
  funext fun p => fdComm h _ _ p

theorem dy_dτ_comm' {Φ : ℝ × Space → ℂ} (h : ContDiff ℝ ∞ Φ) (j : Fin 3) :
    dy j (dτ Φ) = dτ (dy j Φ) :=
  funext fun p => fdComm h _ _ p

/-- Fderiv of a sum of `ℂ`-scalar multiples of the basis vectors. -/
theorem fderiv_sum_e {G : Fin 3 → ℝ × Space → ℂ} (hG : ∀ j, ContDiff ℝ ∞ (G j))
    (v p : ℝ × Space) :
    fderiv ℝ (fun q => ∑ j : Fin 3, G j q • EuclideanSpace.single j (1 : ℂ)) p v =
      ∑ j : Fin 3, fderiv ℝ (G j) p v • EuclideanSpace.single j (1 : ℂ) := by
  have hd : ∀ j ∈ (Finset.univ : Finset (Fin 3)),
      DifferentiableAt ℝ (fun q => G j q • EuclideanSpace.single j (1 : ℂ)) p :=
    fun j _ => (diffC (hG j) p).smul_const _
  rw [fderiv_fun_sum hd]
  simp only [ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [fderiv_smul_const (diffC (hG j) p)]
  simp

theorem dy_sum_e {G : Fin 3 → ℝ × Space → ℂ} (hG : ∀ j, ContDiff ℝ ∞ (G j)) (k : Fin 3) :
    dy k (fun q => ∑ j : Fin 3, G j q • EuclideanSpace.single j (1 : ℂ)) =
      fun q => ∑ j : Fin 3, dy k (G j) q • EuclideanSpace.single j (1 : ℂ) := by
  funext q
  exact fderiv_sum_e hG _ q

theorem dy_sum_c {ι : Type*} (s : Finset ι) {F : ι → ℝ × Space → ℂ}
    (hF : ∀ i ∈ s, ContDiff ℝ ∞ (F i)) (j : Fin 3) :
    dy j (fun q => ∑ i ∈ s, F i q) = fun q => ∑ i ∈ s, dy j (F i) q := by
  funext q
  have hd : ∀ i ∈ s, DifferentiableAt ℝ (F i) q := fun i hi => diffC (hF i hi) q
  simp only [dy]
  rw [fderiv_fun_sum hd]
  simp

theorem dy_add_c {f g : ℝ × Space → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (j : Fin 3) :
    dy j (fun q => f q + g q) = fun q => dy j f q + dy j g q := by
  funext q
  simp only [dy]
  rw [fderiv_fun_add (diffC hf q) (diffC hg q)]
  simp

theorem dy_smul_c {f : ℝ × Space → ℂ} (hf : ContDiff ℝ ∞ f) (c : ℝ) (j : Fin 3) :
    dy j (fun q => c • f q) = fun q => c • dy j f q := by
  funext q
  simp only [dy]
  rw [fderiv_fun_const_smul (diffC hf q) c]
  simp

theorem fderiv_coord (k : Fin 3) (q v : ℝ × Space) :
    fderiv ℝ (fun q : ℝ × Space => q.2 k) q v = v.2 k := by
  have h : HasFDerivAt (fun q : ℝ × Space => q.2 k)
      ((EuclideanSpace.proj k : Space →L[ℝ] ℝ).comp (ContinuousLinearMap.snd ℝ ℝ Space)) q :=
    (EuclideanSpace.proj k : Space →L[ℝ] ℝ).hasFDerivAt.comp q hasFDerivAt_snd
  rw [h.fderiv]
  rfl

theorem cdCoord (k : Fin 3) : ContDiff ℝ ∞ (fun q : ℝ × Space => q.2 k) :=
  (EuclideanSpace.proj k : Space →L[ℝ] ℝ).contDiff.comp contDiff_snd

theorem cdRadial {φ : ℝ × Space → ℂ} (h : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (radialT φ) := by
  show ContDiff ℝ ∞ (fun p : ℝ × Space => ∑ k : Fin 3, p.2 k • dy k φ p)
  exact ContDiff.sum fun k _ => (cdCoord k).smul (cdDy h k)

theorem cdLap {φ : ℝ × Space → ℂ} (h : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (lapT φ) :=
  ContDiff.sum fun k _ => cdDy (cdDy h k) k

/-- `∂ⱼ (y·∇φ) = y·∇(∂ⱼφ) + ∂ⱼφ` for smooth scalar `φ`. -/
theorem dy_radial {φ : ℝ × Space → ℂ} (h : ContDiff ℝ ∞ φ) (j : Fin 3) :
    dy j (radialT φ) = fun q => radialT (dy j φ) q + dy j φ q := by
  funext q
  have hd : ∀ k ∈ (Finset.univ : Finset (Fin 3)),
      DifferentiableAt ℝ (fun q : ℝ × Space => q.2 k • dy k φ q) q :=
    fun k _ => diffC ((cdCoord k).smul (cdDy h k)) q
  have hterm : ∀ k : Fin 3,
      fderiv ℝ (fun q : ℝ × Space => q.2 k • dy k φ q) q (0, coordinateVector j) =
        q.2 k • dy j (dy k φ) q + (if k = j then dy k φ q else 0) := by
    intro k
    rw [fderiv_fun_smul ((cdCoord k).differentiable (by simp) q) (diffC (cdDy h k) q)]
    simp [dy, fderiv_coord, coordinateVector]
  show fderiv ℝ (fun q => ∑ k : Fin 3, q.2 k • dy k φ q) q (0, coordinateVector j) = _
  rw [fderiv_fun_sum hd]
  simp only [ContinuousLinearMap.sum_apply]
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  have hs : ∑ k : Fin 3, (if k = j then dy k φ q else 0) = dy j φ q := by
    simp
  rw [Finset.sum_add_distrib, hs]
  congr 1
  rw [show radialT (dy j φ) q = ∑ k : Fin 3, q.2 k • dy k (dy j φ) q from rfl]
  apply Finset.sum_congr rfl
  intro k _
  rw [dy_dy_comm' h j k]

/-- `∂ⱼ (ΔΦ) = Δ (∂ⱼ Φ)` for smooth scalar `φ`. -/
theorem dy_lap {φ : ℝ × Space → ℂ} (h : ContDiff ℝ ∞ φ) (j : Fin 3) :
    dy j (lapT φ) = lapT (dy j φ) := by
  show dy j (fun q => ∑ k : Fin 3, dy k (dy k φ) q) = fun q => ∑ k : Fin 3, dy k (dy k (dy j φ)) q
  rw [dy_sum_c Finset.univ (fun k _ => cdDy (cdDy h k) k) j]
  funext q
  apply Finset.sum_congr rfl
  intro k _
  rw [dy_dy_comm' (cdDy h k) j k, dy_dy_comm' h j k]

/-- `∇φ` as a sum of the basis vectors. -/
theorem gradT_eq (φ : ℝ × Space → ℂ) :
    gradT φ = fun q => ∑ j : Fin 3, dy j φ q • EuclideanSpace.single j (1 : ℂ) := rfl

theorem dy_gradT {φ : ℝ × Space → ℂ} (h : ContDiff ℝ ∞ φ) (k : Fin 3) :
    dy k (gradT φ) = fun q => ∑ j : Fin 3, dy k (dy j φ) q • EuclideanSpace.single j (1 : ℂ) := by
  rw [gradT_eq, dy_sum_e (fun j => cdDy h j) k]

theorem gr_dτ {φ : ℝ × Space → ℂ} (h : ContDiff ℝ ∞ φ) : dτ (gradT φ) = gradT (dτ φ) := by
  funext p
  rw [gradT_eq, gradT_eq]
  show fderiv ℝ (fun q => ∑ j : Fin 3, dy j φ q • EuclideanSpace.single j (1 : ℂ)) p (1, 0) = _
  rw [fderiv_sum_e (fun j => cdDy h j) (1, 0) p]
  apply Finset.sum_congr rfl
  intro j _
  rw [dy_dτ_comm' h j]
  rfl

theorem gr_lap {φ : ℝ × Space → ℂ} (h : ContDiff ℝ ∞ φ) : lapT (gradT φ) = gradT (lapT φ) := by
  funext p
  have hVV : ∀ k : Fin 3, dy k (dy k (gradT φ)) = fun q => ∑ j : Fin 3,
      dy k (dy k (dy j φ)) q • EuclideanSpace.single j (1 : ℂ) := by
    intro k
    rw [dy_gradT h k, dy_sum_e (fun j => cdDy (cdDy h j) k) k]
  have hL2 : lapT (gradT φ) p = ∑ k : Fin 3, dy k (dy k (gradT φ)) p := rfl
  have hL : gradT (lapT φ) p = ∑ j : Fin 3, dy j (lapT φ) p • EuclideanSpace.single j (1 : ℂ) := rfl
  rw [hL2, hL]
  simp only [hVV]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [dy_lap h j]
  simp only [lapT, Finset.sum_smul]

theorem gr_radial {φ : ℝ × Space → ℂ} (h : ContDiff ℝ ∞ φ) :
    gradT (radialT φ) = fun q => radialT (gradT φ) q + gradT φ q := by
  funext q
  have hR : ∀ j : Fin 3, dy j (radialT φ) q = radialT (dy j φ) q + dy j φ q := by
    intro j
    rw [dy_radial h j]
  have hL : gradT (radialT φ) q = ∑ j : Fin 3, dy j (radialT φ) q • EuclideanSpace.single j (1 : ℂ) := rfl
  rw [hL]
  simp only [hR, add_smul, Finset.sum_add_distrib]
  simp only [radialT, dy_gradT h]
  rw [gradT_eq φ]
  simp only [add_smul, Finset.sum_smul, Finset.smul_sum, smul_assoc, Finset.sum_add_distrib]
  rw [Finset.sum_comm]

/-- The scalar test `χ = (L₀ + μ - ½)φ`-type combination used for the gradient identity. -/
def chiFun (ν μ : ℝ) (φ : ℝ × Space → ℂ) : ℝ × Space → ℂ :=
  fun q => dτ φ q + (-(1 / 2 : ℝ)) • radialT φ q + (-ν) • lapT φ q + (μ - 1 / 2 : ℝ) • φ q

theorem gradT_add_fun {f g : ℝ × Space → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    gradT (fun q => f q + g q) = fun q => gradT f q + gradT g q := by
  funext q
  simp only [gradT_eq, dy_add_c hf hg, add_smul, Finset.sum_add_distrib]

theorem gradT_smul_fun {f : ℝ × Space → ℂ} (hf : ContDiff ℝ ∞ f) (c : ℝ) :
    gradT (fun q => c • f q) = fun q => c • gradT f q := by
  funext q
  simp only [gradT_eq, dy_smul_c hf, smul_assoc, Finset.smul_sum]

theorem gradT_chi {ν μ : ℝ} {φ : ℝ × Space → ℂ} (h : ContDiff ℝ ∞ φ) :
    gradT (chiFun ν μ φ) = fun q => gradT (dτ φ) q + (-(1 / 2 : ℝ)) • gradT (radialT φ) q
      + (-ν) • gradT (lapT φ) q + (μ - 1 / 2 : ℝ) • gradT φ q := by
  have hA : ContDiff ℝ ∞ (fun q => dτ φ q + (-(1 / 2 : ℝ)) • radialT φ q) :=
    (cdDτ h).add ((cdRadial h).const_smul _)
  have hB : ContDiff ℝ ∞ (fun q => dτ φ q + (-(1 / 2 : ℝ)) • radialT φ q + (-ν) • lapT φ q) :=
    hA.add ((cdLap h).const_smul _)
  show gradT (fun q => (dτ φ q + (-(1 / 2 : ℝ)) • radialT φ q + (-ν) • lapT φ q)
    + (μ - 1 / 2 : ℝ) • φ q) = _
  rw [gradT_add_fun hB (h.const_smul _), gradT_add_fun hA ((cdLap h).const_smul _),
    gradT_add_fun (cdDτ h) ((cdRadial h).const_smul _), gradT_smul_fun (cdRadial h),
    gradT_smul_fun (cdLap h), gradT_smul_fun h]

theorem wOpT_gradT {ν μ : ℝ} {φ : ℝ × Space → ℂ} (h : ContDiff ℝ ∞ φ) :
    wOpT ν μ (gradT φ) = gradT (chiFun ν μ φ) := by
  rw [gradT_chi h]
  funext p
  have e1 : dτ (gradT φ) p = gradT (dτ φ) p := congrFun (gr_dτ h) p
  have e2 : radialT (gradT φ) p = gradT (radialT φ) p - gradT φ p := by
    have := congrFun (gr_radial h) p
    rw [this]
    abel
  have e3 : lapT (gradT φ) p = gradT (lapT φ) p := congrFun (gr_lap h) p
  simp only [wOpT, L0, T0, e1, e2, e3, Complex.coe_smul]
  module

end GradAux

theorem intertwineGrad : IntertwineGrad := by
  intro P ν μ hP hP1 hν hμ Φ g ψ w Dψ Dw hdom hψ hw φ hφ
  have hχ : IsPhaseTest P (GradAux.chiFun ν μ φ) :=
    (((hφ.dτ.add (hφ.radialT.const_smul (-(1 / 2 : ℝ)))).add
      (hφ.lapT.const_smul (-ν))).add (hφ.const_smul (μ - 1 / 2 : ℝ)))
  unfold IntertwineDefect
  rw [GradAux.wOpT_gradT hφ.smooth, hψ.sol _ hχ, hw.sol φ hφ]
  simp

end UnforcedLeray.Short.PartIIIb.Concrete
