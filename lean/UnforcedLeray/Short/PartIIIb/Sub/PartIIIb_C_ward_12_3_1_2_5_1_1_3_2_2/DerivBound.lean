import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_2_2.Bound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_2_2

/-!
# `inletSrcDerivBound`

Source `the November 2 reference manuscript`
2545-2551, 2563-2569.  The time slice of `inletSrc` equals `Jets.Sfun` (spatial derivatives only);
`inletFn = -∂_j inletSrc` is its derivative in the direction `e_j`, bounded by
`Jets.norm_fderiv_Sfun_le`.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff
open UnforcedLeray.Cons.C03.Concrete (Params advT)
open UnforcedLeray.PhaseSpace

namespace UnforcedLeray.Short.PartIIIb.Concrete

open Jets in
theorem dy_slice {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (F : ℝ × UnforcedLeray.Space → V)
    (hF : Differentiable ℝ F) (j : Fin 3) (τ : ℝ) (y : UnforcedLeray.Space) :
    dy j F (τ, y) = fderiv ℝ (fun x : UnforcedLeray.Space => F (τ, x)) y (ek j) :=
  (DerivAux.fderiv_slice_eq F hF τ y (ek j)).symm

open Jets in
theorem inletSrc_slice (p : Params) (i : Fin 2) (hE : ContDiff ℝ ∞ (p.Efun i)) (τ : ℝ)
    (x : UnforcedLeray.Space) :
    inletSrc p i (τ, x) = Sfun (fun z => p.Efun i (τ, z)) (fun z => dτ (p.Efun i) (τ, z))
      (p.raw τ) p.ν x := by
  have hD : ∀ {G : ℝ × UnforcedLeray.Space → CVec3}, ContDiff ℝ ∞ G → Differentiable ℝ G :=
    fun hG => hG.differentiable (by simp)
  have h1 : ∀ k : Fin 3, ∀ z, dy k (p.Efun i) (τ, z) =
      fderiv ℝ (fun w => p.Efun i (τ, w)) z (ek k) := fun k z => dy_slice _ (hD hE) k τ z
  have h2 : ∀ k : Fin 3, dy k (dy k (p.Efun i)) (τ, x) =
      fderiv ℝ (fun z => fderiv ℝ (fun w => p.Efun i (τ, w)) z (ek k)) x (ek k) := fun k => by
    rw [dy_slice _ (hD (UnforcedLeray.PhaseSpace.contDiff_dy hE k)) k τ x]
    congr 2
    funext z
    exact h1 k z
  unfold inletSrc Sfun
  simp only [Pi.add_apply, UnforcedLeray.B0411.L0, UnforcedLeray.B0411.T0, radialT, lapT, advT,
    Pi.sub_apply, Pi.smul_apply, gradAlong]
  simp only [h1, h2]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [UnforcedLeray.B0412.realC_apply]
  · ext l
    simp [UnforcedLeray.B0412.realC_apply]

open Jets in
theorem inletSrcDerivBound : InletSrcDerivBound := by
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
      funext x; exact inletSrc_slice p i hE τ x
    unfold inletFn
    simp only [Pi.neg_apply]
    rw [dy_slice _ (hS.differentiable (by simp)) j τ y, e1]
  rw [key, norm_neg]
  exact norm_fderiv_Sfun_le he hd hr hν1 y j

end UnforcedLeray.Short.PartIIIb.Concrete

end
