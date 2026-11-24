import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.MeanShift.Harmonic

/-!
# Directional derivatives of the uncut Newton field and its scaling (source 4776-4782)

* `fderiv_newtonV_apply`: differentiation under the `t`-integral in an arbitrary direction;
* `Gint_scale`: the homogeneity `G(t,y) = t⁻⁴ G(1, y/t)` of the inner `x'`-integral, from the
  degree `-4` homogeneity of `newtonD3`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The inner `x'`-integral `G(t,y)_i`. -/
def Gint (c ν : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (t : ℝ) (i : Fin 3) (y : Vec3) : ℝ :=
  ∫ a : ℝ × ℝ, NewtonFam.famF c ν χo M t i a y

theorem newtonFam_eq_Gint (c ν p : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (i : Fin 3) (t : ℝ) :
    newtonFam c ν p χo M i t = fun y => t ^ (2 * p + 2) * Gint c ν χo M t i y := rfl

theorem Gint_contDiffOn {c ν : ℝ} {χo : ℝ → ℝ} {M : Chart → Mat3} (hc : 0 < c) (hν : 0 < ν)
    (hχ : IsOutwardCutoff χo) (hM : OldThinFinite c ν M) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1)
    (i : Fin 3) :
    ContDiffOn ℝ ∞ (Gint c ν χo M t i) {x : Vec3 | 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2} :=
  NewtonFam.famF_integral_contDiffOn c ν χo M hc hν hχ hM t ht i

theorem Gint_differentiableAt {c ν : ℝ} {χo : ℝ → ℝ} {M : Chart → Mat3} (hc : 0 < c) (hν : 0 < ν)
    (hχ : IsOutwardCutoff χo) (hM : OldThinFinite c ν M) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1)
    (i : Fin 3) {x : Vec3} (hx : 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2) :
    DifferentiableAt ℝ (Gint c ν χo M t i) x :=
  ((Gint_contDiffOn hc hν hχ hM ht i).contDiffAt
    ((isOpen_newtonRegion ν).mem_nhds hx)).differentiableAt (by simp)

/-- The `t`-derivative family is integrable. -/
theorem newtonFam_fderiv_integrable {c ν p : ℝ} {χo : ℝ → ℝ} {M : Chart → Mat3} (hc : 0 < c)
    (hν : 0 < ν) (hp : 0 < p) (hχ : IsOutwardCutoff χo) (hM : OldThinFinite c ν M) (i : Fin 3)
    {x : Vec3} (hx : 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2) (v : Vec3) :
    Integrable (fun t : ℝ => fderiv ℝ (newtonFam c ν p χo M i t) x v)
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have hi1 := (newtonFam_locDom hc hν hp hχ hM i).integrable
    (fun n y hy => newtonFamMeas c ν p χo M hc hν hp hχ hM i n y hy) 1 hx
  have hL := ((continuousMultilinearCurryFin1 ℝ Vec3 ℝ).toContinuousLinearEquiv.toContinuousLinearMap).integrable_comp hi1
  have hL2 := (ContinuousLinearMap.apply ℝ ℝ v).integrable_comp hL
  refine hL2.congr (Filter.Eventually.of_forall fun t => ?_)
  simp [iteratedFDeriv_one_apply]

/-- Differentiation of the Newton field under the `t`-integral, in any direction. -/
theorem fderiv_newtonV_apply {c ν p : ℝ} {χo : ℝ → ℝ} {M : Chart → Mat3} (hc : 0 < c)
    (hν : 0 < ν) (hp : 0 < p) (hχ : IsOutwardCutoff χo) (hM : OldThinFinite c ν M) {x : Vec3}
    (hx : 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2) (v : Vec3) (i : Fin 3) :
    fderiv ℝ (newtonV c ν p χo M) x v i =
      -2 * ∫ t in Ioc (0 : ℝ) 1, fderiv ℝ (newtonFam c ν p χo M i t) x v := by
  have hU : IsOpen {x : Vec3 | 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2} := isOpen_newtonRegion ν
  have hVS := newtonVSmooth_of newtonFamSmooth newtonFamMeas newtonFamDom c ν p χo M hc hν hp hχ hM
  have hV : DifferentiableAt ℝ (newtonV c ν p χo M) x :=
    (hVS.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)
  have hLD : HasFDerivAt (fun z : Vec3 => ∫ t in Ioc (0 : ℝ) 1, newtonFam c ν p χo M i t z)
      (∫ t in Ioc (0 : ℝ) 1, fderiv ℝ (newtonFam c ν p χo M i t) x) x := by
    refine UnforcedLeray.L09.hasFDerivAt_integral_of_locDominated
      (μ := volume.restrict (Ioc (0 : ℝ) 1)) (F := newtonFam c ν p χo M i) hU
      (newtonFam_smooth_ae hc hν hp hχ hM i)
      (fun n y hy => newtonFamMeas c ν p χo M hc hν hp hχ hM i n y hy)
      (newtonFam_locDom hc hν hp hχ hM i) hx
  have hint : Integrable (fun t : ℝ => fderiv ℝ (newtonFam c ν p χo M i t) x)
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
    have hi1 := (newtonFam_locDom hc hν hp hχ hM i).integrable
      (fun n y hy => newtonFamMeas c ν p χo M hc hν hp hχ hM i n y hy) 1 hx
    have hL := ((continuousMultilinearCurryFin1 ℝ Vec3 ℝ).toContinuousLinearEquiv.toContinuousLinearMap).integrable_comp hi1
    refine hL.congr (Filter.Eventually.of_forall fun t => ?_)
    ext w
    simp [iteratedFDeriv_one_apply]
  have hproj := hasFDerivAt_pi'.1 hV.hasFDerivAt i
  have hfun : (fun z : Vec3 => newtonV c ν p χo M z i) =
      fun z => -2 * ∫ t in Ioc (0 : ℝ) 1, newtonFam c ν p χo M i t z :=
    funext fun z => newtonV_apply c ν p χo M z i
  have hD : HasFDerivAt (fun z : Vec3 => newtonV c ν p χo M z i)
      ((-2 : ℝ) • ∫ t in Ioc (0 : ℝ) 1, fderiv ℝ (newtonFam c ν p χo M i t) x) x := by
    rw [hfun]
    exact hLD.const_mul (-2)
  have hu := hproj.unique hD
  have hv := congrArg (fun T : Vec3 →L[ℝ] ℝ => T v) hu
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    smul_apply, smul_eq_mul] at hv
  rw [ContinuousLinearMap.integral_apply hint v] at hv
  exact hv

end UnforcedLeray.Short.PartIIIb.Concrete
