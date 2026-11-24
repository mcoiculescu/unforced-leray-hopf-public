import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_3.Bound.Jet
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_3.Formula.Line

/-!
# The dilation lift of the ring-chart profile operators
(`PartIII-b:C/rep/8/2/1/3/b`, helper 3)

Source lines 5036-5045, 5464-5465.  With `φ(σ, x) = (e^σ, x)` and `F̂ = F ∘ φ` one has
`(Dρ F)∘φ = e^{σ/2} (∂_q - ε(2∂_σ + η∂_η)) F̂` and `(Dz F)∘φ = e^{σ/2} ∂_η F̂`; the weights
`e^{ασ}` pass through the operators with the shift `m ↦ m + 2α`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.RingFrameD2BoundAux

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Axi

/-- The dilation map `(σ, x) ↦ (e^σ, x)`. -/
def phi (z : Zc) : Zc := (Real.exp z.1, z.2)

/-- The weight `e^{ασ}`. -/
def wt (α : ℝ) (z : Zc) : ℝ := Real.exp (α * z.1)

/-- `P_m = ∂_q - ε(2∂_σ + η∂_η + m)`. -/
def Pm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (ε m : ℝ) (F : Zc → E) : Zc → E :=
  Gop 1 (-2 * ε) 0 (-ε) (-(m * ε)) F

/-- `∂_η`. -/
def Zo {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : Zc → E) : Zc → E :=
  Gop 0 0 1 0 0 F

theorem hasFDerivAt_phi (z : Zc) :
    HasFDerivAt phi ((Real.exp z.1 • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) z := by
  have h1 : HasFDerivAt (fun x : Zc => Real.exp x.1) (Real.exp z.1 • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) z :=
    (Real.hasDerivAt_exp z.1).comp_hasFDerivAt z (hasFDerivAt_fst)
  exact h1.prodMk (hasFDerivAt_snd)

theorem fderiv_lift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Zc → E} {z : Zc}
    (hF : DifferentiableAt ℝ F (phi z)) (w : Zc) :
    fderiv ℝ (fun z' => F (phi z')) z w = fderiv ℝ F (phi z) (Real.exp z.1 * w.1, w.2) := by
  have h := hF.hasFDerivAt.comp z (hasFDerivAt_phi z)
  have : fderiv ℝ (fun z' => F (phi z')) z = _ := h.fderiv
  rw [this]
  simp

theorem exp_half_eq (σ : ℝ) : Real.exp (1 / 2 * σ) = Real.sqrt (Real.exp σ) := by
  rw [← Real.exp_half]; ring_nf

theorem lift_Drho {F : Zc → Merid} {z : Zc} (ε : ℝ) (hF : DifferentiableAt ℝ F (phi z)) :
    Drho ε F (phi z) = wt (1 / 2) z • Pm ε 0 (fun z' => F (phi z')) z := by
  unfold Drho Pm Gop wt
  simp only [UnforcedLeray.Axi.dQ, UnforcedLeray.Axi.dS, UnforcedLeray.Axi.dEta]
  rw [fderiv_lift hF, fderiv_lift hF, fderiv_lift hF, exp_half_eq]
  have e1 : ((Real.exp z.1 * 0, ((1 : ℝ), (0 : ℝ))) : Zc) = ((0 : ℝ), ((1 : ℝ), (0 : ℝ))) := by simp
  have e2 : ((Real.exp z.1 * 1, ((0 : ℝ), (0 : ℝ))) : Zc) =
      Real.exp z.1 • ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) := by simp
  have e3 : ((Real.exp z.1 * 0, ((0 : ℝ), (1 : ℝ))) : Zc) = ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) := by simp
  rw [e1, e2, e3, map_smul]
  show Real.sqrt (Real.exp z.1) • _ = _
  simp only [phi, smul_sub, smul_add, smul_smul]
  module

theorem lift_Dz {F : Zc → Merid} {z : Zc} (hF : DifferentiableAt ℝ F (phi z)) :
    Dz F (phi z) = wt (1 / 2) z • Zo (fun z' => F (phi z')) z := by
  unfold Dz Zo Gop wt
  simp only [UnforcedLeray.Axi.dEta]
  rw [fderiv_lift hF ((0 : ℝ), ((0 : ℝ), (1 : ℝ))), exp_half_eq]
  have e3 : ((Real.exp z.1 * 0, ((0 : ℝ), (1 : ℝ))) : Zc) = ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) := by simp
  rw [e3]
  simp [phi]

/-! ### Weights -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasFDerivAt_wt (α : ℝ) (z : Zc) :
    HasFDerivAt (wt α) (Real.exp (α * z.1) • (α • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))) z := by
  have h1 : HasFDerivAt (fun x : Zc => α * x.1) (α • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) z :=
    (hasFDerivAt_fst).const_mul α
  exact (Real.hasDerivAt_exp (α * z.1)).comp_hasFDerivAt z h1

theorem Gop_wt (a b c d e α : ℝ) {G : Zc → E} (hG : ContDiff ℝ ∞ G) :
    Gop a b c d e (fun z => wt α z • G z) =
      fun z => wt α z • Gop a b c d (e + b * α) G z := by
  funext z
  have hGd : DifferentiableAt ℝ G z := (hG.differentiable (by simp)) z
  have h : fderiv ℝ (fun z => wt α z • G z) z = _ := ((hasFDerivAt_wt α z).smul hGd.hasFDerivAt).fderiv
  simp only [Gop]
  rw [h]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst', smul_eq_mul]
  simp only [wt, mul_zero, mul_one, zero_smul, add_zero]
  module

theorem Pm_wt (ε m α : ℝ) {G : Zc → E} (hG : ContDiff ℝ ∞ G) :
    Pm ε m (fun z => wt α z • G z) = fun z => wt α z • Pm ε (m + 2 * α) G z := by
  unfold Pm
  rw [Gop_wt _ _ _ _ _ _ hG]
  funext z
  congr 2
  ring

theorem Zo_wt (α : ℝ) {G : Zc → E} (hG : ContDiff ℝ ∞ G) :
    Zo (fun z => wt α z • G z) = fun z => wt α z • Zo G z := by
  unfold Zo
  rw [Gop_wt _ _ _ _ _ _ hG]
  funext z
  simp

theorem contDiff_Pm (ε m : ℝ) {F : Zc → E} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (Pm ε m F) :=
  contDiff_Gop _ _ _ _ _ hF

theorem contDiff_Zo {F : Zc → E} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (Zo F) :=
  contDiff_Gop _ _ _ _ _ hF

theorem wt_mul (α β : ℝ) (z : Zc) : wt α z * wt β z = wt (α + β) z := by
  unfold wt
  rw [← Real.exp_add]; ring_nf

end

end UnforcedLeray.Short.PartIIIb.Concrete.RingFrameD2BoundAux
