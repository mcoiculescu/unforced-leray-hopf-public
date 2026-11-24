import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.Defs
import UnforcedLeray.Short.PartIIIb.NearInst.Body.Proofs.BodyRealForms
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.Compose
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymMu

/-!
# `PartIII-b:C/cont/R`: `R_μ` is norm continuous on the window (source 5701-5704, 1675-1677)

Source of record: `the November 2 reference manuscript` (73 pages).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short.PartIIIb.NearInst
open UnforcedLeray.Blueprint.Planar (PlanarData)

/-- `μ ↦ T_ε(μ)` is norm continuous on `(-1/4, ∞)` (source 1675-1677: `T_ε = R_ε^{vec}(μ)P_ε`,
`R^{vec}` holomorphic in `Re μ > -1/4`). -/
theorem teps_continuousOn (p : UnforcedLeray.Cons.C03.Concrete.Params) :
    ContinuousOn (fun μ : ℝ => UnforcedLeray.Short.PartIIa.Teps (P := p.period) p.ν_pos
      p.ε_pos p.c_pos rfl (μ : ℂ)) (Ioi (-(1 / 4 : ℝ))) := by
  have h := (UnforcedLeray.B0223.differentiableOn_RepsVec (P := p.period) p.ν_pos p.ε_pos
    p.c_pos rfl).continuousOn
  have h2 : ContinuousOn (fun μ : ℝ => UnforcedLeray.B0223.RepsVec (P := p.period) p.ν_pos
      p.ε_pos p.c_pos rfl (μ : ℂ)) (Ioi (-(1 / 4 : ℝ))) :=
    h.comp Complex.continuous_ofReal.continuousOn (fun μ hμ => by
      have : -(1 / 4 : ℝ) < μ := hμ
      show 0 < (μ : ℂ).re + 1 / 4
      rw [Complex.ofReal_re]; linarith)
  exact h2.clm_comp continuousOn_const

/-- **Body transports are unique** (source 1641-1646, 2676-2683): an `IsBodyTransport` real form
of `R'` is determined by `R'`, since `cellPt` carries the velocity measure to a multiple of
`ageμ (-3/2)` (`CellPtH`). -/
theorem isBodyTransport_unique {c : ℝ} (hc : 0 < c) {R₁ R₂ : Hsp c →L[ℝ] Hsp c}
    {R' : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC →L[ℂ]
      UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC}
    (h₁ : IsBodyTransport R₁ R') (h₂ : IsBodyTransport R₂ R') : R₁ = R₂ := by
  have hH : Masked.CellPtH c := Masked.cellPtH_eq c hc
  ext1 f
  have hf' := Body.cplxH_ae c hH f
  have e : (fun p => merC ((R₁ f : Chart → Merid) (cellPt c p))) =ᵐ[UnforcedLeray.B0220.measureH c]
      fun p => merC ((R₂ f : Chart → Merid) (cellPt c p)) := (h₁ f _ hf').symm.trans (h₂ f _ hf')
  have e' : (fun p => (R₁ f : Chart → Merid) (cellPt c p)) =ᵐ[UnforcedLeray.B0220.measureH c]
      fun p => (R₂ f : Chart → Merid) (cellPt c p) := by
    filter_upwards [e] with p hp
    simpa [Masked.merReL_merC] using congrArg Masked.merReL hp
  have hm : AEMeasurable (cellPt c) (UnforcedLeray.B0220.measureH c) :=
    (Masked.measurable_cellPt c).aemeasurable
  have hmap : Measure.map (cellPt c) (UnforcedLeray.B0220.measureH c) =
      ENNReal.ofReal c • ageμ c (-3 / 2) := hH
  have hs1 : AEStronglyMeasurable (R₁ f : Chart → Merid)
      (Measure.map (cellPt c) (UnforcedLeray.B0220.measureH c)) := by
    rw [hmap]; exact (Lp.aestronglyMeasurable (R₁ f)).smul_measure _
  have hs2 : AEStronglyMeasurable (R₂ f : Chart → Merid)
      (Measure.map (cellPt c) (UnforcedLeray.B0220.measureH c)) := by
    rw [hmap]; exact (Lp.aestronglyMeasurable (R₂ f)).smul_measure _
  have k1 := hs1.ae_eq_mk
  have k2 := hs2.ae_eq_mk
  have k12 : hs1.mk _ =ᵐ[Measure.map (cellPt c) (UnforcedLeray.B0220.measureH c)] hs2.mk _ := by
    have hmeas : MeasurableSet {x | hs1.mk _ x = hs2.mk _ x} :=
      measurableSet_eq_fun hs1.stronglyMeasurable_mk.measurable hs2.stronglyMeasurable_mk.measurable
    rw [Filter.EventuallyEq, ae_map_iff hm hmeas]
    filter_upwards [e', ae_of_ae_map hm k1, ae_of_ae_map hm k2] with p a b c'
    rw [← b, ← c', a]
  have hfin : (R₁ f : Chart → Merid) =ᵐ[Measure.map (cellPt c)
      (UnforcedLeray.B0220.measureH c)] (R₂ f : Chart → Merid) := k1.trans (k12.trans k2.symm)
  rw [hmap] at hfin
  have hne : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.2 hc).ne'
  have hfin' : (R₁ f : Chart → Merid) =ᵐ[ageμ c (-3 / 2)] (R₂ f : Chart → Merid) := by
    simpa [Filter.EventuallyEq, Measure.ae_ennreal_smul_measure_eq hne] using hfin
  exact Lp.ext hfin'

/-- On `μ > -1/4`, the pinned body real form `R_ε` is `bodyForm (T_ε)` (source 1641-1646,
1675-1677): both are `IsBodyTransport` of `T_ε` (`isBodyTransport_bodyForm`, `teps_conj`), and
transports are unique (`isBodyTransport_unique`). -/
theorem bodyReps_eq_bodyForm (Pl : PlanarData) (L : ReturnLevel) {K : ReturnConsts} {μ : ℝ}
    (hμ : -(1 / 4) < μ) (hpin : RegimePins Pl K L μ) :
    bodyReps Pl L μ = Body.bodyForm (cOf L.ν) (Masked.cellPtH_eq _ (cOf_pos L.ν_pos)) (ct_cellPtInvH _ (cOf_pos L.ν_pos))
      (UnforcedLeray.Short.PartIIa.Teps (P := (L.params Pl).period) (L.params Pl).ν_pos
        (L.params Pl).ε_pos (L.params Pl).c_pos rfl (μ : ℂ)) := by
  have hc := cOf_pos L.ν_pos
  have h1 : IsBodyTransport (bodyReps Pl L μ)
      (UnforcedLeray.Short.PartIIa.Teps (P := (L.params Pl).period) (L.params Pl).ν_pos
        (L.params Pl).ε_pos (L.params Pl).c_pos rfl (μ : ℂ)) :=
    Classical.epsilon_spec hpin.body
  have h2 := Body.isBodyTransport_bodyForm (Masked.cellPtH_eq _ hc) (ct_cellPtInvH _ hc)
    (UnforcedLeray.Short.PartIIa.Teps (P := (L.params Pl).period) (L.params Pl).ν_pos
        (L.params Pl).ε_pos (L.params Pl).c_pos rfl (μ : ℂ))
    (fun g => Body.teps_conj Body.solenoidalConj Body.liftVecConj Body.outerSConj _ _ _ _
      (by linarith) g)
  exact isBodyTransport_unique hc h1 h2


end UnforcedLeray.Short.PartIIIb.Concrete
