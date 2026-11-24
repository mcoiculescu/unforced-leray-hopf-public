import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Sub.PartIIIb_C_near_pins_5
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_4

/-!
# `PartIII-b:C/near/pins/5/2`: `SWSmooth` from two elementary facts about `div_ε`

Source `the November 2 reference manuscript`
3888-3890, 1675-1679 (`S_ε = T_ε s div_ε`), 1660-1665 (`div_ε`), 1556-1572 (`free:weak-stress`).

The assembly follows the proof sketched in `SWSmooth`: `G = Re (s div_ε M)` is a real chart field
(`SWDivEpsReal`), `s div_ε M ∈ H` (`TensorTestDivMem`), the chart `cellPt` does not see the
`q`-recentring because `M` and `div_ε M` are `c`-periodic (`SWDivEpsPer`); `IsStressMap` and
`IsStressTransport` identify `T_ε h'` with the chart function of `S_ε F`; `TepsWeakSol` (applied to
the body velocity `velOfH (S_ε F)`), `VelPairAE` and `ChartDivPair` finish.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.PartIIIb.NearInst.Masked (zsumL zsumL_ae cplxT cplxT_ae)

/-- **Leaf (reality of `div_ε`)** (source 1660-1665): for a smooth tensor test whose components
`tv4 (M x)` are real, `div_ε` of it has zero imaginary parts: `Q_ε`, `∂_η` are real-linear
differential operators and `M_rr, M_rz, M_zz, M_φφ` are real-valued (the imaginary part of the
`fderiv` of a complex function is the `fderiv` of its imaginary part, here `0`). -/
def SWDivEpsReal : Prop :=
  ∀ (c ε : ℝ) (M : Chart → Ten3),
    UnforcedLeray.Short.PartIIa.IsTensorTest c (fun x => tv4 (M x)) →
      ∀ (x : Chart) (i : Fin 2),
        (UnforcedLeray.Short.PartIIa.divEps ε (fun y => tv4 (M y)) x i).im = 0

/-- **Leaf (`q`-periodicity of `div_ε`)** (source 1660-1665, 2667): for a `c`-periodic test `M₀`,
the values of `M₀` and of `div_ε M₀` at the recentred point `cellPt c p` (`q ↦ q` or `q - c`)
equal those at `p`.  `div_ε` involves only `∂_s, ∂_q, ∂_η` and values of `M₀` at the point, and
translation in `q` commutes with these derivatives. -/
def SWDivEpsPer : Prop :=
  ∀ (c ε : ℝ) (M0 : Profile → UnforcedLeray.Short.PartIIa.TensorVal),
    UnforcedLeray.Short.PartIIa.IsTensorTest c M0 → ∀ p : Profile,
      M0 (cellPt c p) = M0 p ∧
        UnforcedLeray.Short.PartIIa.divEps ε M0 (cellPt c p) = UnforcedLeray.Short.PartIIa.divEps ε M0 p

theorem swSmooth_of (hV : VelPairAE) (hR : SWDivEpsReal) (hP : SWDivEpsPer) : SWSmooth := by
  intro hyp p μ hPer hμ mZ ρb hmZ hρ Seps Seps' hS hSt M hMt F v hF hv
  obtain ⟨hT, hC, hD, hM, hHT, hH, hHi⟩ := hyp
  have hc := p.c_pos
  have hε := p.ε_pos
  set M0 : Profile → UnforcedLeray.Short.PartIIa.TensorVal := fun y => tv4 (M y) with hM0
  have hmem := hM p.c p.ε hc M0 hMt
  let G : Chart → Merid := fun x =>
    Masked.merReL ((x.1 : ℂ) • UnforcedLeray.Short.PartIIa.divEps p.ε M0 x)
  have hGreal : ∀ x : Chart, merC (G x) =
      (x.1 : ℂ) • UnforcedLeray.Short.PartIIa.divEps p.ε M0 x := by
    intro x
    refine Masked.merC_merReL (fun i => ?_)
    have := hR p.c p.ε M hMt x i
    simp only [smul_eq_mul]
    simp
    exact Or.inr this
  let h' : HSpace p.c MeridC := hmem.toLp _
  have hh'0 : (h' : Profile → MeridC) =ᵐ[measureH p.c]
      fun q => (q.1 : ℂ) • UnforcedLeray.Short.PartIIa.divEps p.ε M0 q := hmem.coeFn_toLp
  have hh' : (h' : Profile → MeridC) =ᵐ[measureH p.c] fun q => merC (G (cellPt p.c q)) := by
    filter_upwards [hh'0] with q hq
    rw [hq, hGreal, (hP p.c p.ε M0 hMt q).2]
    rfl
  -- transfer of a.e. statements along `cellPt` for the tensor measure
  have hacT : ∀ {P : Chart → Prop}, (∀ᵐ x ∂ageμ p.c (-1 / 2), P x) →
      ∀ᵐ q ∂UnforcedLeray.Short.PartIIa.measureHT p.c, P (cellPt p.c q) := by
    intro P h
    have hle := (hHT p.c hc).le
    have hac := Measure.absolutelyContinuous_of_le_smul hle
    exact ae_of_ae_map (Masked.measurable_cellPt p.c).aemeasurable (hac.ae_le h)
  set F' := cplxT p.c (hHT p.c hc) (zsumL p.c mZ ρb hmZ hρ F) with hF'
  have hF'z : (F' : Profile → UnforcedLeray.Short.PartIIa.TensorVal) =ᵐ[
      UnforcedLeray.Short.PartIIa.measureHT p.c] fun q => tv4 (zsum F (cellPt p.c q)) := by
    have h1 := cplxT_ae p.c (hHT p.c hc) (zsumL p.c mZ ρb hmZ hρ F)
    have h2 := hacT (zsumL_ae p.c mZ ρb hmZ hρ F)
    filter_upwards [h1, h2] with q hq1 hq2
    rw [hq1, hq2]
  have hF'M : (F' : Profile → UnforcedLeray.Short.PartIIa.TensorVal) =ᵐ[
      UnforcedLeray.Short.PartIIa.measureHT p.c] M0 := by
    have h2 := hacT hF
    filter_upwards [hF'z, h2] with q hq1 hq2
    rw [hq1, hq2]
    exact (hP p.c p.ε M0 hMt q).1
  have hSF' : Seps' F' = UnforcedLeray.Short.PartIIa.Teps (P := p.period) p.ν_pos p.ε_pos p.c_pos rfl
      (μ : ℂ) h' := hS M0 hMt F' h' hF'M hh'0
  have hTr := hSt F F' hF'z
  rw [hSF'] at hTr
  -- the body velocity
  set w : VelG p.c 0 p.ν := velOfH p.c 0 p.ν_pos (Seps F) with hw
  have hwae : (w : Chart → Merid) =ᵐ[ageμ p.c (-3 / 2)] (Seps F : Chart → Merid) :=
    coeFn_velOfH p.ν_pos (Seps F)
  have hwc : ∀ᵐ q ∂measureH p.c, (w : Chart → Merid) (cellPt p.c q) = (Seps F : Chart → Merid) (cellPt p.c q) :=
    ae_cellPt_of (hH p.c hc) hwae
  have hTw : (UnforcedLeray.Short.PartIIa.Teps (P := p.period) p.ν_pos p.ε_pos p.c_pos rfl (μ : ℂ) h' :
        Profile → MeridC) =ᵐ[measureH p.c] (fun q => merC ((w : Chart → Merid) (cellPt p.c q))) := by
    filter_upwards [hTr, hwc] with q h1 h2
    rw [h1, h2]
  have hW := hT p μ hPer hμ 0 G h' w hh' hTw
  have hvw : v =ᵐ[ageμ p.c (-3 / 2)] (w : Chart → Merid) := hv.trans hwae.symm
  have hpair : ∀ Φ : ℝ × Space → CVec3, pairF (2 * p.ε * p.c) Φ (velPhys p.ε⁻¹ p.c v) =
      pairF (2 * p.ε * p.c) Φ (velPhys p.ε⁻¹ p.c w) :=
    fun Φ => hV p.c p.ε hc hε v w hvw Φ
  refine ⟨fun φ hφ => ?_, fun Φ hΦ => ?_⟩
  · rw [hpair]
    exact hW.solenoidal φ hφ
  · rw [hpair, hW.equation Φ hΦ]
    refine hC p.c p.ε hc hε M hMt G ?_ Φ hΦ.1
    exact Filter.Eventually.of_forall hGreal

end UnforcedLeray.Short.PartIIIb.NearInst
