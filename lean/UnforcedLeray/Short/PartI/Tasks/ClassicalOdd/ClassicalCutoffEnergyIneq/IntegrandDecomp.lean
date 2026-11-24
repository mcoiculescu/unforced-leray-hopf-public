import UnforcedLeray.Short.PartI.Sub.T02_3_11
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.IntegrandDecomp

/-!
# Part I, task `PartI:T02/3/11`: the integrand decomposition `CcIntegrandDecomp`

Source of record: `the November 2 reference manuscript`, lines 276-288.

Target: `ccIntegrandDecomp (hI : CellIntegrableOfSupport) (hS : CcSliceSmooth) (hM : CcDiffMomentum) :
CcIntegrandDecomp` (`Short/PartI/Sub/T02_3_11.lean`, the leaf `CcIntegrandDecomp`).

Mathematics. Fix `s ∈ (0, T)`, put `w = v - v'`, `π = p - p'` and `φ = etaCutoff R`. The momentum
equations of both classical solutions give, at every point (`CcDiffMomentum`),
`∂_s w = -((v·∇)w + (w·∇)v') + ν Δw - ∇π`.  Multiplying `2⟨w, ∂_s w⟩` by `φ` and integrating over the
cell splits the integral into four integrals, one for each term; each integrand is continuous and
vanishes for `|η| ≥ 2R`, hence is integrable on the cell by `hI`.

Proof layout. The calculus helpers `cid_*` of `Tasks/TrainCutoffEnergyProof/IntegrandDecomp.lean` are
generic statements about plain fields on the plane and are reused by import.  The four integrands are
`ccIDA`, `ccIDB`, `ccIDL`, `ccIDG`.  The slices `v(s)`, `v'(s)`, `p(s)`, `p'(s)` are `C^∞` by
`CcSliceSmooth`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-! ### The four integrands -/

/-- The transport integrand `φ_R(η) ⟨w, (v·∇)w⟩`. -/
def ccIDA (v v' : ℝ → Plane → Vec) (R s : ℝ) (z : Plane) : ℝ :=
  etaCutoff R z.2 * inner ℝ (ccDiffV v v' s z) (bilinAdv (v s) (ccDiffV v v' s) z)

/-- The stretching integrand `φ_R(η) ⟨w, (w·∇)v'⟩`. -/
def ccIDB (v v' : ℝ → Plane → Vec) (R s : ℝ) (z : Plane) : ℝ :=
  etaCutoff R z.2 * inner ℝ (ccDiffV v v' s z) (bilinAdv (ccDiffV v v' s) (v' s) z)

/-- The viscous integrand `φ_R(η) ⟨w, Δw⟩`. -/
def ccIDL (v v' : ℝ → Plane → Vec) (R s : ℝ) (z : Plane) : ℝ :=
  etaCutoff R z.2 * inner ℝ (ccDiffV v v' s z) (Train.vecLaplacian (ccDiffV v v' s) z)

/-- The pressure integrand `φ_R(η) ⟨w, ∇π⟩`. -/
def ccIDG (v v' : ℝ → Plane → Vec) (p p' : ℝ → Plane → ℝ) (R s : ℝ) (z : Plane) : ℝ :=
  etaCutoff R z.2 * inner ℝ (ccDiffV v v' s z) (Train.gradS (ccDiffP p p' s) z)

/-! ### The theorem -/

/-- **`PartI:T02/3/11`, `CcIntegrandDecomp`.** For `s ∈ (0, T)` the cutoff integral
`∫_cell φ_R · 2⟨w, ∂_s w⟩` is the sum of the viscous, transport, stretching and pressure terms. -/
theorem ccIntegrandDecomp (hI : CellIntegrableOfSupport) (hS : CcSliceSmooth) (hM : CcDiffMomentum) :
    CcIntegrandDecomp := by
  intro ν c T M v v' p p' h R hR s hs
  have hRpos : 0 < R := by linarith
  have hc : 0 < c := by linarith [h.c_ge]
  obtain ⟨hv, hp⟩ := hS ν c T v p h.cl s (Ioo_subset_Icc_self hs)
  obtain ⟨hv', hp'⟩ := hS ν c T v' p' h.cl' s (Ioo_subset_Icc_self hs)
  have hwd : ContDiff ℝ ∞ (ccDiffV v v' s) := hv.sub hv'
  have hPd : ContDiff ℝ ∞ (ccDiffP p p' s) := hp.sub hp'
  -- continuity of the four integrands
  have hcφ : Continuous (fun z : Plane => etaCutoff R z.2) := cid_etaCutoff_cont R
  have hwc : Continuous (ccDiffV v v' s) := hwd.continuous
  have hcA : Continuous (ccIDA v v' R s) :=
    hcφ.mul (hwc.inner (cid_bilin_cont hv hwd))
  have hcB : Continuous (ccIDB v v' R s) :=
    hcφ.mul (hwc.inner (cid_bilin_cont hwd hv'))
  have hcL : Continuous (ccIDL v v' R s) :=
    hcφ.mul (hwc.inner (cid_vecLap_cont hwd))
  have hcG : Continuous (ccIDG v v' p p' R s) :=
    hcφ.mul (hwc.inner (cid_gradS_cont hPd))
  -- support: the cutoff vanishes for `|η| ≥ 2R`
  have hsupp : ∀ z : Plane, 2 * R ≤ |z.2| → etaCutoff R z.2 = 0 :=
    fun z hz => cid_etaCutoff_eq_zero hRpos hz
  have iA : IntegrableOn (ccIDA v v' R s) (Cyl.cell c) :=
    hI c R hc hRpos _ hcA (fun z hz => by simp only [ccIDA, hsupp z hz, zero_mul])
  have iB : IntegrableOn (ccIDB v v' R s) (Cyl.cell c) :=
    hI c R hc hRpos _ hcB (fun z hz => by simp only [ccIDB, hsupp z hz, zero_mul])
  have iL : IntegrableOn (ccIDL v v' R s) (Cyl.cell c) :=
    hI c R hc hRpos _ hcL (fun z hz => by simp only [ccIDL, hsupp z hz, zero_mul])
  have iG : IntegrableOn (ccIDG v v' p p' R s) (Cyl.cell c) :=
    hI c R hc hRpos _ hcG (fun z hz => by simp only [ccIDG, hsupp z hz, zero_mul])
  have jA : Integrable (fun z => (-2 : ℝ) * ccIDA v v' R s z)
      (volume.restrict (Cyl.cell c)) := Integrable.const_mul iA (-2)
  have jB : Integrable (fun z => (-2 : ℝ) * ccIDB v v' R s z)
      (volume.restrict (Cyl.cell c)) := Integrable.const_mul iB (-2)
  have jL : Integrable (fun z => (2 * ν) * ccIDL v v' R s z)
      (volume.restrict (Cyl.cell c)) := Integrable.const_mul iL (2 * ν)
  have jG : Integrable (fun z => (-2 : ℝ) * ccIDG v v' p p' R s z)
      (volume.restrict (Cyl.cell c)) := Integrable.const_mul iG (-2)
  -- the integrand splits pointwise, by the equation for `w`
  have hsplit : (∫ z in Cyl.cell c, etaCutoff R z.2 *
        (2 * inner ℝ (ccDiffV v v' s z) (deriv (fun t => ccDiffV v v' t z) s))) =
      ∫ z in Cyl.cell c, ((-2 : ℝ) * ccIDA v v' R s z + (-2 : ℝ) * ccIDB v v' R s z +
        (2 * ν) * ccIDL v v' R s z + (-2 : ℝ) * ccIDG v v' p p' R s z) := by
    congr 1
    funext z
    rw [hM ν c T M v v' p p' h s hs z]
    simp only [ccIDA, ccIDB, ccIDL, ccIDG, inner_add_right, inner_sub_right,
      inner_neg_right, real_inner_smul_right]
    ring
  have k1 : Integrable (fun z => (-2 : ℝ) * ccIDA v v' R s z +
      (-2 : ℝ) * ccIDB v v' R s z) (volume.restrict (Cyl.cell c)) := jA.add jB
  have k2 : Integrable (fun z => (-2 : ℝ) * ccIDA v v' R s z +
      (-2 : ℝ) * ccIDB v v' R s z + (2 * ν) * ccIDL v v' R s z)
      (volume.restrict (Cyl.cell c)) := k1.add jL
  have e2 : (∫ z in Cyl.cell c, ((-2 : ℝ) * ccIDA v v' R s z +
        (-2 : ℝ) * ccIDB v v' R s z + (2 * ν) * ccIDL v v' R s z +
        (-2 : ℝ) * ccIDG v v' p p' R s z)) =
      (∫ z in Cyl.cell c, ((-2 : ℝ) * ccIDA v v' R s z +
        (-2 : ℝ) * ccIDB v v' R s z + (2 * ν) * ccIDL v v' R s z)) +
      ∫ z in Cyl.cell c, (-2 : ℝ) * ccIDG v v' p p' R s z :=
    integral_add k2 jG
  have e1 : (∫ z in Cyl.cell c, ((-2 : ℝ) * ccIDA v v' R s z +
        (-2 : ℝ) * ccIDB v v' R s z + (2 * ν) * ccIDL v v' R s z)) =
      (∫ z in Cyl.cell c, ((-2 : ℝ) * ccIDA v v' R s z +
        (-2 : ℝ) * ccIDB v v' R s z)) +
      ∫ z in Cyl.cell c, (2 * ν) * ccIDL v v' R s z :=
    integral_add k1 jL
  have e0 : (∫ z in Cyl.cell c, ((-2 : ℝ) * ccIDA v v' R s z +
        (-2 : ℝ) * ccIDB v v' R s z)) =
      (∫ z in Cyl.cell c, (-2 : ℝ) * ccIDA v v' R s z) +
      ∫ z in Cyl.cell c, (-2 : ℝ) * ccIDB v v' R s z :=
    integral_add jA jB
  unfold ccDt ccViscous ccTransport ccStretch ccPressure
  rw [hsplit, e2, e1, e0]
  simp only [integral_const_mul, ccIDA, ccIDB, ccIDL, ccIDG]
  ring

end UnforcedLeray.Short.PartI
