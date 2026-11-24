import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_5

/-!
# Lemma `/4` of `PartIII-a:T21/3/5`: the components of the physical flux.

For `r ≥ 0` the flux `actualTrainFluxB hm P r w` is the physical flux built from `Vc tr r`, `Ec tr r`
(`actualTrainFluxB_eq_trainFlux`), whose `i`-th component is, a.e. on the cell,
`w x * v_i(x) + E(x) * (realBiotSavart w)_i(x)` (`physicalFlux`, `physicalFluxComponentCLM_apply`).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa.Exist.L4Aux

open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution
open UnforcedLeray.B0579
open UnforcedLeray.Train (Vec)

/-- The `i`-th component of the physical flux kernel, a.e. on the cell, in the physical formula. -/
theorem fluxFn_ae {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m) (v : Plane → Vec) (E : Plane → ℝ)
    (hv : Continuous v) (hE : Continuous E) {Cv CE : ℝ} (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hvBound : ∀ x i, |v x i| ≤ Cv)
    (hEBound : ∀ x ∈ UnforcedLeray.B0579.cell c, |bracket x ^ m * E x| ≤ CE)
    (w : zeroCirculationSubmodule (c := c) (m := m) (by linarith : 1 / 2 < m)) (i : Fin 2) :
    ∀ᵐ x ∂(volume.restrict (UnforcedLeray.B0579.cell c)),
      fluxFn (physicalFluxKernelCLM hm v E hv hE hCv hCE hvBound hEBound w) i x =
        (w.1 : X c m) x * v x i +
          E x * ((realBiotSavart hm w.1 ((mem_zeroCirculationSubmodule_iff (by linarith : 1 / 2 < m)
            w.1).1 w.2) x : Vec) i) := by
  have hk : physicalFluxKernelCLM hm v E hv hE hCv hCE hvBound hEBound w i =
      physicalFluxX hm v E w.1 ((mem_zeroCirculationSubmodule_iff (by linarith : 1 / 2 < m) w.1).1 w.2)
        hCv hCE hv hE hvBound hEBound i :=
    physicalFluxComponentCLM_apply hm v E hv hE hCv hCE hvBound hEBound w i
  have hae : ∀ᵐ x ∂(UnforcedLeray.B0579.cellMeasure c m),
      (physicalFluxX hm v E w.1 ((mem_zeroCirculationSubmodule_iff (by linarith : 1 / 2 < m) w.1).1 w.2)
        hCv hCE hv hE hvBound hEBound i : X c m) x =
        w.1 x * v x i + E x * ((realBiotSavart hm w.1 ((mem_zeroCirculationSubmodule_iff
          (by linarith : 1 / 2 < m) w.1).1 w.2) x : Vec) i) := by
    have h := MemLp.coeFn_toLp (memLp_physicalFlux hm v E w.1
      ((mem_zeroCirculationSubmodule_iff (by linarith : 1 / 2 < m) w.1).1 w.2)
      hCv hCE hv hE hvBound hEBound i)
    filter_upwards [h] with x hx
    unfold physicalFluxX
    rw [hx]
    simp [physicalFlux, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  filter_upwards [(UnforcedLeray.B0579.ac_cellMeasure c m).ae_le hae] with x hx
  unfold fluxFn
  rw [hk]
  exact hx

end UnforcedLeray.Short.IIIa.Exist.L4Aux

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.Short.IIIa
open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution
open UnforcedLeray.Short.IIIa.Exist.L4Aux

theorem fluxFnAe_all : ∀ (ν c m : ℝ) [Fact (0 < c)] (hm : 1 ≤ m) (tr : UnforcedLeray.B0140.TrainSol ν c) (P : UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualTrainFluxPath (c := c) (m := m) hm (ν := ν) tr), UnforcedLeray.Short.IIIa.Exist.FluxFnAe hm tr P := by
  intro ν c m _ hm tr P
  unfold FluxFnAe
  intro r hr w φ hφ
  rw [actualTrainFluxB_eq_trainFlux hm P hr w]
  have hvS : ContDiff ℝ ∞ (tr.v r) := UnforcedLeray.B0238.contDiff_Vc tr hr
  have hEc : Continuous (UnforcedLeray.B0238.Ec tr r) := by
    unfold UnforcedLeray.B0238.Ec
    exact UnforcedLeray.B0238.continuous_curl (v := tr.v r) (hvS.of_le (by exact_mod_cast le_top))
  have h0 := fluxFn_ae hm (UnforcedLeray.B0238.Vc tr r) (UnforcedLeray.B0238.Ec tr r)
    (UnforcedLeray.B0238.contDiff_Vc tr hr).continuous hEc P.hCv P.hCE
    (by rw [← P.velocity_eq r hr]; exact P.velocity_bound r hr)
    (by rw [← P.curl_eq r hr]; exact P.weighted_curl_bound r hr) w 0
  have h1 := fluxFn_ae hm (UnforcedLeray.B0238.Vc tr r) (UnforcedLeray.B0238.Ec tr r)
    (UnforcedLeray.B0238.contDiff_Vc tr hr).continuous hEc P.hCv P.hCE
    (by rw [← P.velocity_eq r hr]; exact P.velocity_bound r hr)
    (by rw [← P.curl_eq r hr]; exact P.weighted_curl_bound r hr) w 1
  filter_upwards [h0, h1] with x hx0 hx1
  rw [hx0, hx1]
  unfold stripVel cplx vortFn
  simp only [UnforcedLeray.B0238.Vc]
  push_cast
  ring

end UnforcedLeray.Short.IIIa.Exist
