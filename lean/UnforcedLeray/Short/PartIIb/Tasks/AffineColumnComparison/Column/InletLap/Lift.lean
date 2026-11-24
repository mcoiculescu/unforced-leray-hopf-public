import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.InletLap.Comm
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.InletT0

/-!
# Helper for `PartII-b:G4/3/3` (`InletLapPtw`): the complex lift of a real smooth profile

Source of record: `the November 2 reference manuscript`, lines 1651-1658, 2367-2369.

For a smooth real profile `F`, `classQ ε (cplx F) = cplx (qEps ε F)`, `classEta (cplx F) =
cplx (∂_η F)`, hence `lapProf ν ε (cplx F) (Q²) (∂_η²) = cplx (s ν L_ε F)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.InletLap

open UnforcedLeray.Short.IIb.InletT0

theorem fderiv_cplx {G : Coord → Axi.Merid} (hG : ContDiff ℝ ∞ G) (x v : Coord) :
    fderiv ℝ (cplx G) x v = mToC (fderiv ℝ G x v) := by
  have h := cplx_hasFDerivAt ((hG.differentiable (by simp)) x).hasFDerivAt
  rw [h.fderiv]
  rfl

theorem classQ_cplx {G : Coord → Axi.Merid} (hG : ContDiff ℝ ∞ G) (ε : ℝ) :
    classQ ε (cplx G) = cplx (qEps ε G) := by
  funext x
  have hv := fderiv_cplx hG x
  have hc : cplx (qEps ε G) x = mToC (qEps ε G x) := congrFun (cplx_eq_mToC _) x
  have hc2 : cplx G x = mToC (G x) := congrFun (cplx_eq_mToC _) x
  have e0 : cdir 0 = ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) := rfl
  have e1 : cdir 1 = ((0 : ℝ), ((1 : ℝ), (0 : ℝ))) := rfl
  have e2 : cdir 2 = ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) := rfl
  have v0 : vQ ε x 0 = -2 * ε * x.1 := rfl
  have v1 : vQ ε x 1 = 1 := rfl
  have v2 : vQ ε x 2 = -ε * x.2.2 := rfl
  simp only [classQ, Fin.sum_univ_three, e0, e1, e2, v0, v1, v2, hv, hc, hc2]
  simp only [dQ, qEps, kAge, Axi.dS, Axi.dQ, Axi.dEta, map_add, map_sub, map_smul]
  module

theorem classEta_cplx {G : Coord → Axi.Merid} (hG : ContDiff ℝ ∞ G) :
    classEta (cplx G) = cplx (Axi.dEta G) := by
  funext x
  have hc : cplx (Axi.dEta G) x = mToC (Axi.dEta G x) := congrFun (cplx_eq_mToC _) x
  have e2 : cdir 2 = ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) := rfl
  simp only [classEta, e2, fderiv_cplx hG, hc]
  rfl

theorem cd_qEps {G : Coord → Axi.Merid} (hG : ContDiff ℝ ∞ G) (ε : ℝ) :
    ContDiff ℝ ∞ (qEps ε G) := by
  have h : qEps ε G = fun y => Axi.dQ G y - ε • (kAge G y + G y) := by
    funext y; rfl
  rw [h]
  exact (cd_partial hG _).sub (((cd_kAge hG).add hG).const_smul ε)

theorem hoopE_mToC (v : Axi.Merid) : hoopE (mToC v) = mToC (hoopR v) := by
  ext i
  fin_cases i <;> simp [hoopE, hoopR, mToC_apply, Axi.m0]

/-- **The chart form of the Laplacian profile of a smooth real lift.** -/
theorem lapProf_cplx {F : Coord → Axi.Merid} (hF : ContDiff ℝ ∞ F) (ε ν : ℝ) :
    lapProf ν ε (cplx F) (classQ ε (classQ ε (cplx F))) (classEta (classEta (cplx F))) =
      cplx (fun y => y.1 • (ν • vecDiffEps ε F y)) := by
  have hη : ContDiff ℝ ∞ (Axi.dEta F) := cd_partial hF _
  funext x
  rw [classQ_cplx hF, classQ_cplx (cd_qEps hF ε), classEta_cplx hF,
    classEta_cplx hη]
  have hid := qEps_qEps_eq hF ε x
  have h1 : cplx (qEps ε (qEps ε F)) x = mToC (qEps ε (qEps ε F) x) :=
    congrFun (cplx_eq_mToC _) x
  have h2 : cplx (Axi.dEta (Axi.dEta F)) x = mToC (Axi.dEta (Axi.dEta F) x) :=
    congrFun (cplx_eq_mToC _) x
  have h3 : cplx F x = mToC (F x) := congrFun (cplx_eq_mToC _) x
  have h4 : cplx (fun y => y.1 • (ν • vecDiffEps ε F y)) x =
      mToC (x.1 • (ν • vecDiffEps ε F x)) := congrFun (cplx_eq_mToC _) x
  rw [h4, ← hid]
  simp only [lapProf, h1, h2, h3]
  have e : ∀ (a : ℝ) (v : Axi.Merid), ((a : ℝ) : ℂ) • mToC v = mToC (a • v) := by
    intro a v
    ext i
    simp [mToC_apply]
  rw [hoopE_mToC, e (ε ^ 2), ← map_add, ← map_sub, e]
  congr 1
  module

end UnforcedLeray.Short.IIb.InletLap
