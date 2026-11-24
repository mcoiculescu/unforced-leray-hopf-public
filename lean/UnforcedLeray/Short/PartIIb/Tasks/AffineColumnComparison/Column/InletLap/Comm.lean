import UnforcedLeray.Short.PartIIb.Sub.G4_3_org
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T09_5

/-!
# Helper for `PartII-b:G4/3/3` (`InletLapPtw`): chart calculus on real profiles

Source of record: `the November 2 reference manuscript`, lines 1651-1658, 2367-2369.

For `C²` profiles `F : Coord → E`: `∂_q` commutes with `K = 2s∂_s + η∂_η` (symmetry of second
derivatives), and `Q_ε = ∂_q - ε(K+1)` is the classical `classQ` of the complex lift.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.InletLap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem le2' : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  first
  | exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)
  | exact (by norm_cast; exact le_top)
  | simp
  | exact ENat.LEInfty.out

/-- The partial derivative `fderiv F · e` is differentiable with derivative read off `D²F`. -/
theorem hasFDerivAt_partial {F : Coord → E} (hF : ContDiff ℝ 2 F) (e : Coord) (x : Coord) :
    HasFDerivAt (fun y => fderiv ℝ F y e)
      ((ContinuousLinearMap.apply ℝ E e).comp (fderiv ℝ (fderiv ℝ F) x)) x := by
  have hD : DifferentiableAt ℝ (fderiv ℝ F) x :=
    ((hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
  exact (ContinuousLinearMap.apply ℝ E e).hasFDerivAt.comp x hD.hasFDerivAt

theorem partial_partial {F : Coord → E} (hF : ContDiff ℝ 2 F) (e v : Coord) (x : Coord) :
    fderiv ℝ (fun y => fderiv ℝ F y e) x v = fderiv ℝ (fderiv ℝ F) x v e := by
  rw [(hasFDerivAt_partial hF e x).fderiv]
  rfl

theorem partial_comm {F : Coord → E} (hF : ContDiff ℝ 2 F) (e v : Coord) (x : Coord) :
    fderiv ℝ (fun y => fderiv ℝ F y e) x v = fderiv ℝ (fun y => fderiv ℝ F y v) x e := by
  rw [partial_partial hF, partial_partial hF]
  exact (hF.contDiffAt.isSymmSndFDerivAt (by simp)) v e

/-- `∂_q` commutes with `K = 2s∂_s + η∂_η` on `C²` profiles. -/
theorem dQ_kAge {F : Coord → E} (hF : ContDiff ℝ 2 F) (x : Coord) :
    Axi.dQ (kAge F) x = kAge (Axi.dQ F) x := by
  have h1 : HasFDerivAt (fun y : Coord => (2 * y.1)) ((2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) x := by
    simpa using (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ × ℝ) (p := x)).const_mul 2
  have h2 : HasFDerivAt (fun y : Coord => y.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) x :=
    (hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ)).comp x
      (hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ × ℝ))
  have hS := hasFDerivAt_partial hF (1, (0, 0)) x
  have hH := hasFDerivAt_partial hF (0, (0, 1)) x
  have hk := (h1.smul hS).add (h2.smul hH)
  unfold Axi.dQ
  show fderiv ℝ (fun y => (2 * y.1) • Axi.dS F y + y.2.2 • Axi.dEta F y) x (0, (1, 0)) = _
  have hk' : HasFDerivAt (fun y : Coord => (2 * y.1) • Axi.dS F y + y.2.2 • Axi.dEta F y) _ x := hk
  rw [hk'.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.apply_apply, kAge, Axi.dS, Axi.dQ, Axi.dEta]
  have e1 := partial_comm hF (1, (0, 0)) (0, (1, 0)) x
  have e2 := partial_comm hF (0, (0, 1)) (0, (1, 0)) x
  rw [partial_partial hF] at e1 e2
  simp
  rw [e1, e2]

/-! ### Linearity and smoothness of the chart operators -/

theorem cd_partial {F : Coord → E} (hF : ContDiff ℝ ∞ F) (e : Coord) :
    ContDiff ℝ ∞ (fun y => fderiv ℝ F y e) :=
  (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem cd_kAge {F : Coord → E} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (kAge F) := by
  unfold kAge Axi.dS Axi.dEta
  exact ((contDiff_const.mul contDiff_fst).smul (cd_partial hF _)).add
    ((contDiff_snd.comp contDiff_snd).smul (cd_partial hF _))

theorem partial_sub_smul {G H : Coord → E} {x : Coord} (hG : DifferentiableAt ℝ G x)
    (hH : DifferentiableAt ℝ H x) (c : ℝ) (e : Coord) :
    fderiv ℝ (fun y => G y - c • H y) x e = fderiv ℝ G x e - c • fderiv ℝ H x e := by
  have h : HasFDerivAt (fun y => G y - c • H y) _ x :=
    hG.hasFDerivAt.sub (hH.hasFDerivAt.const_smul c)
  rw [h.fderiv]
  rfl

theorem kAge_sub_smul {G H : Coord → E} {x : Coord} (hG : DifferentiableAt ℝ G x)
    (hH : DifferentiableAt ℝ H x) (c : ℝ) :
    kAge (fun y => G y - c • H y) x = kAge G x - c • kAge H x := by
  simp only [kAge, Axi.dS, Axi.dEta, partial_sub_smul hG hH]
  module

theorem partial_add {G H : Coord → E} {x : Coord} (hG : DifferentiableAt ℝ G x)
    (hH : DifferentiableAt ℝ H x) (e : Coord) :
    fderiv ℝ (fun y => G y + H y) x e = fderiv ℝ G x e + fderiv ℝ H x e := by
  have h : HasFDerivAt (fun y => G y + H y) _ x := hG.hasFDerivAt.add hH.hasFDerivAt
  rw [h.fderiv]
  rfl

/-- `Q_ε² F + ∂_η² F - ε² diag(1,0) F` is the exact vector diffusion `L_ε F` (SP 2367-2369), for
smooth `F`: `∂_q` commutes with `K` and `Q_ε = ∂_q - ε(K+1)`. -/
theorem qEps_qEps_eq {F : Coord → Axi.Merid} (hF : ContDiff ℝ ∞ F) (ε : ℝ) (x : Coord) :
    qEps ε (qEps ε F) x + Axi.dEta (Axi.dEta F) x - ε ^ 2 • hoopR (F x) = vecDiffEps ε F x := by
  have hF2 : ContDiff ℝ 2 F := hF.of_le le2'
  have hdQ : ContDiff ℝ ∞ (Axi.dQ F) := cd_partial hF _
  have hK : ContDiff ℝ ∞ (kAge F) := cd_kAge hF
  have hH : ContDiff ℝ ∞ (fun y => kAge F y + F y) := hK.add hF
  have hdQd : DifferentiableAt ℝ (Axi.dQ F) x := (hdQ.differentiable (by simp)) x
  have hHd : DifferentiableAt ℝ (fun y => kAge F y + F y) x := (hH.differentiable (by simp)) x
  have hqE : qEps ε F = fun y => Axi.dQ F y - ε • (kAge F y + F y) := by
    funext y; rfl
  have hdQH : Axi.dQ (fun y => kAge F y + F y) x = kAge (Axi.dQ F) x + Axi.dQ F x := by
    unfold Axi.dQ
    rw [partial_add ((hK.differentiable (by simp)) x) ((hF.differentiable (by simp)) x)]
    exact congrArg (· + _) (dQ_kAge hF2 x)
  unfold qEps
  unfold vecDiffEps
  rw [show Axi.dQ (fun y => Axi.dQ F y - ε • (kAge F y + F y)) x =
      Axi.dQ (Axi.dQ F) x - ε • Axi.dQ (fun y => kAge F y + F y) x from
    partial_sub_smul hdQd hHd ε _, hdQH, kAge_sub_smul hdQd hHd ε]
  module

end UnforcedLeray.Short.IIb.InletLap
