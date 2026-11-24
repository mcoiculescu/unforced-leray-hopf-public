import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.Flux
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ZeroModeLinearity

/-!
# Linearity of the concrete train flux on the circulation kernel

With fixed actual coefficients and their centered-cell bounds, the physical two-component flux is
linear in the real zero-circulation vorticity. This keeps the B0583 reconstruction and the actual
transport product visible in the map.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

open MeasureTheory
open UnforcedLeray.B0579
open UnforcedLeray.B0581 (cellVol)
open UnforcedLeray.Train (Vec)

/-- `toLp` preserves addition, with the representative equality kept explicit. -/
theorem memLp_toLp_add {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (hf.add hg).toLp (fun x => f x + g x) = hf.toLp f + hg.toLp g := by
  change (hf.add hg).toLp (f + g) = hf.toLp f + hg.toLp g
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (hf.add hg),
    Lp.coeFn_add (hf.toLp f) (hg.toLp g),
    MemLp.coeFn_toLp hf, MemLp.coeFn_toLp hg] with x h1 h2 h3 h4
  rw [h1, h2]
  change f x + g x = (hf.toLp f : Lp ℝ 2 μ) x + (hg.toLp g : Lp ℝ 2 μ) x
  rw [h3, h4]

/-- The actual physical flux as a real-linear map on the closed zero-circulation state space,
for fixed coefficients satisfying the physical centered-cell bounds. -/
def physicalFluxKernelLinearMap {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)
    (v : Plane → Vec) (E : Plane → ℝ) (hv : Continuous v) (hE : Continuous E)
    {Cv CE : ℝ} (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hvBound : ∀ x i, |v x i| ≤ Cv)
    (hEBound : ∀ x ∈ cell c, |bracket x ^ m * E x| ≤ CE) :
    zeroCirculationSubmodule (c := c) (m := m) (by linarith : 1 / 2 < m) →ₗ[ℝ]
      Fin 2 → X c m := by
  let Z := zeroCirculationSubmodule (c := c) (m := m) (by linarith : 1 / 2 < m)
  refine {
    toFun := fun w => physicalFluxX hm v E w.1
      ((mem_zeroCirculationSubmodule_iff (by linarith : 1 / 2 < m) w.1).1 w.2)
      hCv hCE hv hE hvBound hEBound
    map_add' := ?_
    map_smul' := ?_ }
  · intro w z
    have hw0 := (mem_zeroCirculationSubmodule_iff (by linarith : 1 / 2 < m) w.1).1 w.2
    have hz0 := (mem_zeroCirculationSubmodule_iff (by linarith : 1 / 2 < m) z.1).1 z.2
    have hwz0 := (mem_zeroCirculationSubmodule_iff (by linarith : 1 / 2 < m)
      (w + z).1).1 (Z.add_mem w.2 z.2)
    funext i
    have hW : (↑(w.1 + z.1) : Plane → ℝ) =ᵐ[cellMeasure c m]
        fun x => w.1 x + z.1 x := Lp.coeFn_add w.1 z.1
    have hKlp := realBiotSavart_add hm w.1 z.1 hw0 hz0 hwz0
    have hK : (realBiotSavart hm (w.1 + z.1) hwz0 : Plane → Vec) =ᵐ[cellVol c]
        fun x => realBiotSavart hm w.1 hw0 x + realBiotSavart hm z.1 hz0 x := by
      rw [hKlp]
      exact Lp.coeFn_add _ _
    have hK' : (realBiotSavart hm (w.1 + z.1) hwz0 : Plane → Vec) =ᵐ[cellMeasure c m]
        fun x => realBiotSavart hm w.1 hw0 x + realBiotSavart hm z.1 hz0 x :=
      (cellMeasure_ac c m).ae_le hK
    have hF : physicalFlux hm v E (w.1 + z.1) hwz0 =ᵐ[cellMeasure c m]
        fun x => physicalFlux hm v E w.1 hw0 x + physicalFlux hm v E z.1 hz0 x := by
      filter_upwards [hW, hK'] with x hx hk
      change (w.1 + z.1) x • v x + E x • realBiotSavart hm (w.1 + z.1) hwz0 x = _
      rw [hx, hk]
      simp only [physicalFlux, add_smul, smul_add]
      abel
    have hFi : (fun x => physicalFlux hm v E (w.1 + z.1) hwz0 x i) =ᵐ[cellMeasure c m]
        fun x => physicalFlux hm v E w.1 hw0 x i + physicalFlux hm v E z.1 hz0 x i :=
      hF.mono fun x hx => by exact congrArg (fun q : Vec => q i) hx
    have hLp := MemLp.toLp_congr
      (memLp_physicalFlux hm v E (w.1 + z.1) hwz0 hCv hCE hv hE hvBound hEBound i)
      ((memLp_physicalFlux hm v E w.1 hw0 hCv hCE hv hE hvBound hEBound i).add
        (memLp_physicalFlux hm v E z.1 hz0 hCv hCE hv hE hvBound hEBound i)) hFi
    have hAdd := memLp_toLp_add
      (memLp_physicalFlux hm v E w.1 hw0 hCv hCE hv hE hvBound hEBound i)
      (memLp_physicalFlux hm v E z.1 hz0 hCv hCE hv hE hvBound hEBound i)
    simpa [physicalFluxX] using hLp.trans hAdd

  · intro a w
    have hw0 := (mem_zeroCirculationSubmodule_iff (by linarith : 1 / 2 < m) w.1).1 w.2
    have haw0 := (mem_zeroCirculationSubmodule_iff (by linarith : 1 / 2 < m)
      (a • w).1).1 (Z.smul_mem a w.2)
    funext i
    have hW : (↑(a • w.1) : Plane → ℝ) =ᵐ[cellMeasure c m]
        fun x => a • w.1 x := Lp.coeFn_smul a w.1
    have hKlp := realBiotSavart_smul hm a w.1 hw0 haw0
    have hK : (realBiotSavart hm (a • w.1) haw0 : Plane → Vec) =ᵐ[cellVol c]
        fun x => a • realBiotSavart hm w.1 hw0 x := by
      rw [hKlp]
      exact Lp.coeFn_smul a (realBiotSavart hm w.1 hw0)
    have hK' : (realBiotSavart hm (a • w.1) haw0 : Plane → Vec) =ᵐ[cellMeasure c m]
        fun x => a • realBiotSavart hm w.1 hw0 x := (cellMeasure_ac c m).ae_le hK
    have hF : physicalFlux hm v E (a • w.1) haw0 =ᵐ[cellMeasure c m]
        fun x => a • physicalFlux hm v E w.1 hw0 x := by
      filter_upwards [hW, hK'] with x hx hk
      change (a • w.1) x • v x + E x • realBiotSavart hm (a • w.1) haw0 x = _
      rw [hx, hk]
      simp only [physicalFlux]
      simp [smul_smul, smul_add, mul_comm]
    have hFi : (fun x => physicalFlux hm v E (a • w.1) haw0 x i) =ᵐ[cellMeasure c m]
        fun x => a • physicalFlux hm v E w.1 hw0 x i :=
      hF.mono fun x hx => by exact congrArg (fun q : Vec => q i) hx
    have hWmem := memLp_physicalFlux hm v E w.1 hw0 hCv hCE hv hE hvBound hEBound i
    have hsmem := hWmem.const_smul a
    have hLp := MemLp.toLp_congr
      (memLp_physicalFlux hm v E (a • w.1) haw0 hCv hCE hv hE hvBound hEBound i) hsmem hFi
    have hsmul : hsmem.toLp (fun x => a • physicalFlux hm v E w.1 hw0 x i) =
        a • hWmem.toLp (fun x => physicalFlux hm v E w.1 hw0 x i) := by
      exact MemLp.toLp_const_smul a hWmem
    simpa [physicalFluxX] using hLp.trans hsmul


end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution
