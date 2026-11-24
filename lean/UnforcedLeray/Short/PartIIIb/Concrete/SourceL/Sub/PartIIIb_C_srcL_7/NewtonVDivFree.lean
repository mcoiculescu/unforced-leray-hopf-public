import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_7
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_7.NewtonInnerDiv
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_srcL_6_1_1
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_6_1_1_1
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_6_1_1_2
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_6_1_1_3
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_6_1_1_3.Helpers
import UnforcedLeray.Loc.L09CompactDatum.ParamIntegral

/-!
# `NewtonVDivFree`: the zero-width Newton field is solenoidal off the old disc
(task `PartIII-b:C/srcL/7/10`)

Source of record: `the November 2 reference manuscript`, lines 4797-4800.
`newtonV x i = -2 ∫_{(0,1]} newtonFam i t x dt`.  The field is differentiable on the open region
(`newtonVSmooth_of`), so each component derivative is the `t`-integral of the component
derivatives (`hasFDerivAt_integral_of_locDominated`), and for each `t ∈ (0,1]` the divergence of
the integrand vanishes (`newtonInnerDiv`, after pulling out the factor `t^(2μ+2)`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **(b4)** The zero-width Newton field is solenoidal off the old disc. -/
theorem newtonVDivFree : NewtonVDivFree := by
  intro c ν μ χo M hc hν hμ hχ hM x hx
  have hU : IsOpen {x : Vec3 | 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2} := isOpen_newtonRegion ν
  -- differentiability of `newtonV` at `x`
  have hVS := newtonVSmooth_of newtonFamSmooth newtonFamMeas newtonFamDom c ν μ χo M hc hν hμ hχ hM
  have hV : DifferentiableAt ℝ (newtonV c ν μ χo M) x :=
    (hVS.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)
  -- local domination of the `t`-family
  have hdomfn : ∀ i : Fin 3, UnforcedLeray.L09.LocDominated (volume.restrict (Ioc (0 : ℝ) 1))
      (newtonFam c ν μ χo M i) {x : Vec3 | 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2} := by
    intro i
    unfold UnforcedLeray.L09.LocDominated
    intro n y hy
    obtain ⟨s, hs, g, hg, hb⟩ := newtonFamDom c ν μ χo M hc hν hμ hχ hM i n y hy
    refine ⟨s, hs, g, hg, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact fun z hz => hb t ht z hz
  -- integrability of the component derivatives in `t`
  have hint : ∀ i : Fin 3, Integrable (fun t : ℝ => fderiv ℝ (newtonFam c ν μ χo M i t) x)
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
    intro i
    have hi1 := (hdomfn i).integrable
      (fun n y hy => newtonFamMeas c ν μ χo M hc hν hμ hχ hM i n y hy) 1 hx
    have hL := ((continuousMultilinearCurryFin1 ℝ Vec3 ℝ).toContinuousLinearEquiv.toContinuousLinearMap).integrable_comp hi1
    refine hL.congr (Filter.Eventually.of_forall fun t => ?_)
    ext v
    simp [iteratedFDeriv_one_apply]
  -- differentiation under the `t`-integral
  have hLD : ∀ i : Fin 3, HasFDerivAt (fun z : Vec3 => ∫ t in Ioc (0 : ℝ) 1, newtonFam c ν μ χo M i t z)
      (∫ t in Ioc (0 : ℝ) 1, fderiv ℝ (newtonFam c ν μ χo M i t) x) x := by
    intro i
    refine UnforcedLeray.L09.hasFDerivAt_integral_of_locDominated
      (μ := volume.restrict (Ioc (0 : ℝ) 1)) (F := newtonFam c ν μ χo M i) hU ?_
      (fun n y hy => newtonFamMeas c ν μ χo M hc hν hμ hχ hM i n y hy) (hdomfn i) hx
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact newtonFamSmooth c ν μ χo M hc hν hμ hχ hM i t ht
  -- each component of the derivative of `newtonV`
  have hterm : ∀ i : Fin 3, fderiv ℝ (newtonV c ν μ χo M) x (Pi.single i 1) i =
      -2 * ∫ t in Ioc (0 : ℝ) 1, fderiv ℝ (newtonFam c ν μ χo M i t) x (Pi.single i 1) := by
    intro i
    have hproj := hasFDerivAt_pi'.1 hV.hasFDerivAt i
    have hfun : (fun z : Vec3 => newtonV c ν μ χo M z i) =
        fun z => -2 * ∫ t in Ioc (0 : ℝ) 1, newtonFam c ν μ χo M i t z :=
      funext fun z => newtonV_apply c ν μ χo M z i
    have hD : HasFDerivAt (fun z : Vec3 => newtonV c ν μ χo M z i)
        ((-2 : ℝ) • ∫ t in Ioc (0 : ℝ) 1, fderiv ℝ (newtonFam c ν μ χo M i t) x) x := by
      rw [hfun]
      exact (hLD i).const_mul (-2)
    have hu := hproj.unique hD
    have hv := congrArg (fun T : Vec3 →L[ℝ] ℝ => T (Pi.single i 1)) hu
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      smul_apply, smul_eq_mul] at hv
    rw [ContinuousLinearMap.integral_apply (hint i) (Pi.single i 1)] at hv
    exact hv
  -- for each `t ∈ (0,1]` the divergence of the integrand vanishes
  have hpt : ∀ t ∈ Ioc (0 : ℝ) 1,
      ∑ i : Fin 3, fderiv ℝ (newtonFam c ν μ χo M i t) x (Pi.single i 1) = 0 := by
    intro t ht
    have hGd : ∀ i : Fin 3, DifferentiableAt ℝ (fun y : Vec3 => ∫ a : ℝ × ℝ,
        ∑ j, ∑ k, newtonD3 (y - t • embPlane a) i j k * sigmaM c ν χo M a j k) x := by
      intro i
      have hC := NewtonFam.famF_integral_contDiffOn c ν χo M hc hν hχ hM t ht i
      exact (hC.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)
    have hfd : ∀ i : Fin 3, fderiv ℝ (newtonFam c ν μ χo M i t) x = (t ^ (2 * μ + 2)) •
        fderiv ℝ (fun y : Vec3 => ∫ a : ℝ × ℝ,
          ∑ j, ∑ k, newtonD3 (y - t • embPlane a) i j k * sigmaM c ν χo M a j k) x := by
      intro i
      rw [show newtonFam c ν μ χo M i t = fun z => t ^ (2 * μ + 2) * ∫ a : ℝ × ℝ,
        ∑ j, ∑ k, newtonD3 (z - t • embPlane a) i j k * sigmaM c ν χo M a j k from rfl]
      exact fderiv_const_mul (hGd i) _
    simp only [hfd, smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, newtonInnerDiv c ν χo M hc hν hχ hM t ht x hx, mul_zero]
  -- assembly: swap the finite sum with the `t`-integral
  have hsum : ∫ t in Ioc (0 : ℝ) 1,
      ∑ i : Fin 3, fderiv ℝ (newtonFam c ν μ χo M i t) x (Pi.single i 1)
      = ∑ i : Fin 3, ∫ t in Ioc (0 : ℝ) 1, fderiv ℝ (newtonFam c ν μ χo M i t) x (Pi.single i 1) := by
    refine integral_finsetSum _ fun i _ => ?_
    exact (ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1)).integrable_comp (hint i)
  have hzero : ∫ t in Ioc (0 : ℝ) 1,
      ∑ i : Fin 3, fderiv ℝ (newtonFam c ν μ χo M i t) x (Pi.single i 1) = 0 := by
    have hae : (fun t : ℝ => ∑ i : Fin 3, fderiv ℝ (newtonFam c ν μ χo M i t) x (Pi.single i 1))
        =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] fun _ => (0 : ℝ) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact hpt t ht
    rw [integral_congr_ae hae, integral_zero]
  simp only [hterm]
  rw [← Finset.mul_sum, ← hsum, hzero, mul_zero]

end UnforcedLeray.Short.PartIIIb.Concrete
