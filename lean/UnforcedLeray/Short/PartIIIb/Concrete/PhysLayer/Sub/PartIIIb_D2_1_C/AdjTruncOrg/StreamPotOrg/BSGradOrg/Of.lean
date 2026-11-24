import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.BSGradOrg.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.Defs
import UnforcedLeray.Short.PartIIb.Bridge.Dict
import UnforcedLeray.Lib.PhaseTrace.Trace

/-!
# `BSGrad` from the slice ingredients

Source `the November 2 reference manuscript` lines 1334-1337, 1351-1362.

* `bsgSliceId_of`: the slice weak identity `∫ (-∂ⱼθ) · (f ×∗ K) = ∫ θ · bsGradL2 j f` from the
  Fubini swap (`BSFubiniSwap`), the kernel identity (`BSGKernelVec`) and the `L²` duality
  (`BSGDualVec`).
* `bsGrad_of`: the phase gradient `Dψ j` is the `Y_2` representative of
  `τ ↦ bsGradL2 j (Φ(τ))` (`Yq` dictionary: `exists_hasRepY_q`, `exists_isInYr_hasRepY_q`), so
  `Dψ j ∈ Y_2` is automatic and the phase-test identity is the slice identity integrated over the
  period.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.RieszLp
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt)

/-- The slice weak identity from the Fubini swap, the kernel identity and the duality. -/
theorem bsgSliceId_of (hF : BSFubiniSwap) (hK : BSGKernelVec) (hD : BSGDualVec) :
    BSGSliceId := by
  intro θ hθ hθc f hf j
  have hAc : Continuous (fun y => fderiv ℝ θ y (EuclideanSpace.single j 1)) :=
    (hθ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hAs : HasCompactSupport (fun y => fderiv ℝ θ y (EuclideanSpace.single j 1)) :=
    hθc.fderiv_apply ℝ _
  have h1 : ∫ y : Space, dotL (-fderiv ℝ θ y (EuclideanSpace.single j 1))
        (∫ z : Space, crossC (f z) (bsKernel (y - z))) =
      -∫ y : Space, dotL (fderiv ℝ θ y (EuclideanSpace.single j 1))
        (∫ z : Space, crossC (f z) (bsKernel (y - z))) := by
    rw [← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [map_neg, neg_apply]
  have h2 : ∫ y : Space, dotL (fderiv ℝ θ y (EuclideanSpace.single j 1))
        (∫ z : Space, crossC (f z) (bsKernel (y - z))) =
      ∫ z : Space, dotL (f z)
        (∫ y : Space, crossC (bsKernel (y - z)) (fderiv ℝ θ y (EuclideanSpace.single j 1))) :=
    hF _ hAc hAs f hf
  have h3 : ∫ z : Space, dotL (f z)
        (∫ y : Space, crossC (bsKernel (y - z)) (fderiv ℝ θ y (EuclideanSpace.single j 1))) =
      ∫ z : Space, dotL (f z) (bsgW j θ z) := by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [hK θ hθ hθc j z]
  rw [h1, h2, h3, hD θ hθ hθc f hf j, neg_neg]

/-- The `y`-derivative of a phase test is the derivative of its slice. -/
theorem bsg_dy_slice {P : ℝ} {Θ : ℝ × Space → CVec3} (hΘ : IsPhaseTest P Θ) (j : Fin 3)
    (t : ℝ) (y : Space) :
    dy j Θ (t, y) = fderiv ℝ (fun y' : Space => Θ (t, y')) y (EuclideanSpace.single j 1) := by
  have hdiff : DifferentiableAt ℝ Θ (t, y) :=
    (hΘ.smooth.differentiable (by simp)).differentiableAt
  have hemb : HasFDerivAt (fun y' : Space => ((t, y') : ℝ × Space))
      (ContinuousLinearMap.inr ℝ ℝ Space) y :=
    (hasFDerivAt_const t y).prodMk (hasFDerivAt_id y)
  have hcomp : HasFDerivAt (fun y' : Space => Θ (t, y'))
      ((fderiv ℝ Θ (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ Space)) y :=
    hdiff.hasFDerivAt.comp y hemb
  rw [hcomp.fderiv]
  rfl

/-- **`BSGrad` from the slice weak identity.** -/
theorem bsGrad_of (hS : BSGSliceId) : BSGrad := by
  intro P hP Φ hΦ _
  have : Fact (0 < P) := ⟨hP⟩
  obtain ⟨F, hF, -⟩ := UnforcedLeray.Short.IIb.exists_hasRepY_q P 2 two_pos (q := 2)
    ENNReal.ofNat_ne_top (by simp) Φ hΦ
  have hW : ∀ j : Fin 3, ∃ W : ℝ × Space → CVec3, UnforcedLeray.Short.IIb.IsInYr P 2 W ∧
      UnforcedLeray.Short.IIb.HasRepY ((bsGradL2 j).compLp F) W := fun j => by
    obtain ⟨W, h1, h2, -⟩ := UnforcedLeray.Short.IIb.exists_isInYr_hasRepY_q P 2 two_pos (q := 2)
      ENNReal.ofNat_ne_top (by simp) ((bsGradL2 j).compLp F)
    exact ⟨W, h1, h2⟩
  choose W hWY hWR using hW
  refine ⟨W, fun j => ⟨hWY j, ?_⟩⟩
  intro Θ hΘ
  simp only [pairF, phaseInt]
  congr 1
  refine setIntegral_congr_ae measurableSet_Ioc ?_
  have hcomp : ∀ᵐ t : ℝ, ((bsGradL2 j).compLp F) (t : AddCircle P) =
      bsGradL2 j (F (t : AddCircle P)) :=
    UnforcedLeray.PhaseTrace.ae_comp_mk ((bsGradL2 j).coeFn_compLp F)
  filter_upwards [hF.slice, (hWR j).slice, hcomp] with t h1 h2 h3 _
  have hmem : MemLp (fun y : Space => Φ (t, y)) 2 volume := (Lp.memLp _).ae_eq h1.symm
  have hto : hmem.toLp (fun y : Space => Φ (t, y)) = F (t : AddCircle P) := by
    rw [← Lp.toLp_coeFn (F (t : AddCircle P)) (Lp.memLp _)]
    exact MemLp.toLp_congr _ _ h1
  have hθ : ContDiff ℝ ∞ (fun y : Space => Θ (t, y)) :=
    hΘ.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hθc : HasCompactSupport (fun y : Space => Θ (t, y)) := hΘ.hasCompactSupport_slice t
  have key := hS (fun y : Space => Θ (t, y)) hθ hθc (fun y : Space => Φ (t, y)) hmem j
  have hR : ∫ y : Space, dotL (Θ (t, y)) (W j (t, y)) =
      ∫ y : Space, dotL (Θ (t, y)) (bsGradL2 j (hmem.toLp (fun y : Space => Φ (t, y))) y) := by
    refine integral_congr_ae ?_
    rw [hto, ← h3]
    filter_upwards [h2] with y hy
    rw [hy]
  have hL : ∫ y : Space, dotL ((-dy j Θ) (t, y)) (bsPot Φ (t, y)) =
      ∫ y : Space, dotL (-fderiv ℝ (fun y' : Space => Θ (t, y')) y (EuclideanSpace.single j 1))
        (∫ z : Space, crossC (Φ (t, z)) (bsKernel (y - z))) := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [Pi.neg_apply, bsg_dy_slice hΘ j t y]
    rfl
  rw [hL, key, hR]

/-- **`BSGrad` from the three slice ingredients.** -/
theorem bsGrad_of' (hF : BSFubiniSwap) (hK : BSGKernelVec) (hD : BSGDualVec) : BSGrad :=
  bsGrad_of (bsgSliceId_of hF hK hD)

end UnforcedLeray.Short.PartIIIb.Concrete
