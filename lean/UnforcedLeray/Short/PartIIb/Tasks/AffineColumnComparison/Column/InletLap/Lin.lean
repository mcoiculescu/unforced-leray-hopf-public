import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.InletLap.Comm

/-!
# Helper for `PartII-b:G4/3/3` (`InletLapPtw`): linearity of `L_ε` on smooth profiles

Source of record: `the November 2 reference manuscript`, lines 2367-2369.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.InletLap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem dif {F : Coord → E} (hF : ContDiff ℝ ∞ F) : Differentiable ℝ F :=
  hF.differentiable (by simp)

theorem partial_lin {F G : Coord → E} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (a b : ℝ)
    (e x : Coord) :
    fderiv ℝ (fun y => a • F y + b • G y) x e = a • fderiv ℝ F x e + b • fderiv ℝ G x e := by
  have h : HasFDerivAt (fun y => a • F y + b • G y) _ x :=
    ((dif hF x).hasFDerivAt.const_smul a).add ((dif hG x).hasFDerivAt.const_smul b)
  rw [h.fderiv]
  rfl

theorem lin_dS {F G : Coord → E} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (a b : ℝ) :
    Axi.dS (fun y => a • F y + b • G y) = fun y => a • Axi.dS F y + b • Axi.dS G y :=
  funext fun y => partial_lin hF hG a b _ y

theorem lin_dQ {F G : Coord → E} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (a b : ℝ) :
    Axi.dQ (fun y => a • F y + b • G y) = fun y => a • Axi.dQ F y + b • Axi.dQ G y :=
  funext fun y => partial_lin hF hG a b _ y

theorem lin_dEta {F G : Coord → E} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (a b : ℝ) :
    Axi.dEta (fun y => a • F y + b • G y) = fun y => a • Axi.dEta F y + b • Axi.dEta G y :=
  funext fun y => partial_lin hF hG a b _ y

theorem lin_kAge {F G : Coord → E} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (a b : ℝ) :
    kAge (fun y => a • F y + b • G y) = fun y => a • kAge F y + b • kAge G y := by
  funext y
  simp only [kAge, lin_dS hF hG a b, lin_dEta hF hG a b]
  module

theorem hoopR_lin (a b : ℝ) (u v : Axi.Merid) : hoopR (a • u + b • v) = a • hoopR u + b • hoopR v := by
  ext i
  fin_cases i <;> simp [hoopR, Axi.m0]

/-- `L_ε` is linear on smooth profiles. -/
theorem vecDiffEps_lin {F G : Coord → Axi.Merid} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (ε a b : ℝ) (x : Coord) :
    vecDiffEps ε (fun y => a • F y + b • G y) x = a • vecDiffEps ε F x + b • vecDiffEps ε G x := by
  have hdF : ContDiff ℝ ∞ (Axi.dQ F) := cd_partial hF _
  have hdG : ContDiff ℝ ∞ (Axi.dQ G) := cd_partial hG _
  have hkF : ContDiff ℝ ∞ (fun y => kAge F y + F y) := (cd_kAge hF).add hF
  have hkG : ContDiff ℝ ∞ (fun y => kAge G y + G y) := (cd_kAge hG).add hG
  have hEF : ContDiff ℝ ∞ (Axi.dEta F) := cd_partial hF _
  have hEG : ContDiff ℝ ∞ (Axi.dEta G) := cd_partial hG _
  have e1 : (fun y => a • kAge F y + b • kAge G y + (a • F y + b • G y)) =
      fun y => a • (kAge F y + F y) + b • (kAge G y + G y) := by
    funext y
    module
  unfold vecDiffEps
  rw [lin_dQ hF hG a b, lin_dQ hdF hdG a b, lin_dEta hF hG a b, lin_dEta hEF hEG a b,
    lin_kAge hdF hdG a b, lin_kAge hF hG a b]
  simp only []
  rw [e1, lin_kAge hkF hkG a b, hoopR_lin]
  module

end UnforcedLeray.Short.IIb.InletLap
