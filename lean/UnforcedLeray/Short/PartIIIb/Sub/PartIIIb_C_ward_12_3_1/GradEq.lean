import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEqSub
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEWeak
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEHess
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEGradL2p
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GERaw
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELin
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuad
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELift
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_2_2.Bound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_2_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.rawJointSmooth
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_2.Jets
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.rawDerivBdd
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3.Far
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1.CylMemLp
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1.Meas
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5.IBP.Identity
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5.Rep

/-!
# Differentiated background equation `BgCorrGradEq`

Source: `the November 2 reference manuscript`
lines 2525-2551.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff
open UnforcedLeray.Cons.C03.Concrete (Params advT)
open UnforcedLeray.PhaseSpace

namespace UnforcedLeray.Short.PartIIIb.Concrete

open Jets in
private theorem dy_slice' {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : ℝ × UnforcedLeray.Space → V)
    (hF : Differentiable ℝ F) (j : Fin 3) (τ : ℝ) (y : UnforcedLeray.Space) :
    dy j F (τ, y) = fderiv ℝ (fun x : UnforcedLeray.Space => F (τ, x)) y (ek j) :=
  (DerivAux.fderiv_slice_eq F hF τ y (ek j)).symm

open Jets in
private theorem inletSrc_slice' (p : Params) (i : Fin 2) (hE : ContDiff ℝ ∞ (p.Efun i)) (τ : ℝ)
    (x : UnforcedLeray.Space) :
    inletSrc p i (τ, x) = Sfun (fun z => p.Efun i (τ, z)) (fun z => dτ (p.Efun i) (τ, z))
      (p.raw τ) p.ν x := by
  have hD : ∀ {G : ℝ × UnforcedLeray.Space → CVec3}, ContDiff ℝ ∞ G → Differentiable ℝ G :=
    fun hG => hG.differentiable (by simp)
  have h1 : ∀ k : Fin 3, ∀ z, dy k (p.Efun i) (τ, z) =
      fderiv ℝ (fun w => p.Efun i (τ, w)) z (ek k) := fun k z => dy_slice' _ (hD hE) k τ z
  have h2 : ∀ k : Fin 3, dy k (dy k (p.Efun i)) (τ, x) =
      fderiv ℝ (fun z => fderiv ℝ (fun w => p.Efun i (τ, w)) z (ek k)) x (ek k) := fun k => by
    rw [dy_slice' _ (hD (UnforcedLeray.PhaseSpace.contDiff_dy hE k)) k τ x]
    congr 2
    funext z
    exact h1 k z
  unfold inletSrc Sfun
  simp only [Pi.add_apply, UnforcedLeray.B0411.L0, UnforcedLeray.B0411.T0, radialT, lapT, advT,
    gradAlong]
  simp only [h1, h2]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [UnforcedLeray.B0412.realC_apply]
  · ext l
    simp [UnforcedLeray.B0412.realC_apply]

open Jets in
private theorem inletSrcDerivBound' : InletSrcDerivBound := by
  refine ⟨20, by norm_num, fun p i j hν hE hR τ y => ?_⟩
  have hν1 : |p.ν| ≤ 1 := by rw [abs_of_pos p.ν_pos]; exact hν
  have hsl : ContDiff ℝ ∞ (fun x : UnforcedLeray.Space => ((τ, x) : ℝ × UnforcedLeray.Space)) :=
    contDiff_const.prodMk contDiff_id
  have he : ContDiff ℝ ∞ (fun z : UnforcedLeray.Space => p.Efun i (τ, z)) := by
    have := ContDiff.comp (g := p.Efun i) hE hsl
    exact this
  have hr : ContDiff ℝ ∞ (p.raw τ) := by
    have := ContDiff.comp (g := fun x : ℝ × UnforcedLeray.Space => p.raw x.1 x.2) hR hsl
    exact this
  have hd : ContDiff ℝ ∞ (fun z : UnforcedLeray.Space => dτ (p.Efun i) (τ, z)) := by
    have := ContDiff.comp (g := dτ (p.Efun i)) (contDiff_dτ hE) hsl
    exact this
  have hS : ContDiff ℝ ∞ (inletSrc p i) := inletSrc_contDiff hE hR
  have key : inletFn p i j (τ, y) =
      -(fderiv ℝ (Sfun (fun z => p.Efun i (τ, z)) (fun z => dτ (p.Efun i) (τ, z)) (p.raw τ) p.ν)
        y (ek j)) := by
    have e1 : (fun x : UnforcedLeray.Space => inletSrc p i (τ, x)) =
        Sfun (fun z => p.Efun i (τ, z)) (fun z => dτ (p.Efun i) (τ, z)) (p.raw τ) p.ν := by
      funext x; exact inletSrc_slice' p i hE τ x
    unfold inletFn
    simp only [Pi.neg_apply]
    rw [dy_slice' _ (hS.differentiable (by simp)) j τ y, e1]
  rw [key, norm_neg]
  exact norm_fderiv_Sfun_le he hd hr hν1 y j

private theorem gEInlet' : GEInlet :=
  gEInlet_of
    (gEInletIBP_of
      (inletFnMemLp_of cylProfile_memLp inletFnMeas
        (inletFnEnvelope_of inletFnFarDecay
          (inletFnNearBound_of inletENearJets
            (inletFnNearOfJets_of rawJointSmooth inletSrcDerivBound')
            rawDerivBdd)))
      inletIBPIdentity)
    (fun p => inletRepYq p.period)

/-- Differentiated background equation (source 2525-2551). -/
theorem bgCorrGradEq : BgCorrGradEq :=
  bgCorrGradEq_of gEWeak gEHess gEGradL2p gERaw gEInlet' gELin gEQuad gELift

end UnforcedLeray.Short.PartIIIb.Concrete

end
