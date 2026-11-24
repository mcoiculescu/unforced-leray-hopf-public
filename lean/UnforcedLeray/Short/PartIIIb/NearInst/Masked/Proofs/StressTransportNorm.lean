import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Lemmas
import UnforcedLeray.Short.PartIIIb.NearInst.Body.Proofs.BodyFormNorm
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.OpBoundOfBox
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.CompactWindow.Comparison.WindowNorm.ZsumTransportNorm

/-!
# `PartIII-b:C/near/masked/10`: `StressTransportNorm` (source 1641-1646, 2676-2679, 3564-3565)

For a real form `S` of a complex stress transport `S'` and `F ∈ Z`, the transported input
`F' = cplxT (zsumL F)` satisfies the pin of `IsStressTransport` (`stressTransport_zsum_ae`), so
`√c ‖S F‖ = ‖S' F'‖ ≤ ‖S'‖ ‖F'‖ ≤ ‖S'‖ √c ‖F‖`, using `norm_sq_cellPt` (the velocity map
`‖G‖² = c‖g‖²`), `cplxT_norm_le_sqrt_aux` and `ob_zsumL_norm_le`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

/-- The transported zsum agrees with `zsum` after `cellPt`, `measureHT`-a.e. (the map `cellPt`
carries `measureHT` to `c • ageμ(-1/2)`, `CellPtHT`). -/
theorem stressTransport_zsum_ae {c mZ ρb : ℝ} (hc : 0 < c) (hT : CellPtHT c) (hmZ : 0 ≤ mZ)
    (hρ : 0 < ρb) (F : Zsp c mZ ρb) :
    ∀ᵐ p ∂UnforcedLeray.Short.PartIIa.measureHT c,
      (zsumL c mZ ρb hmZ hρ F : Chart → Ten3) (cellPt c p) = zsum F (cellPt c p) := by
  have hT' : Measure.map (cellPt c) (UnforcedLeray.Short.PartIIa.measureHT c) =
      ENNReal.ofReal c • ageμ c (-1 / 2) := hT
  have hac : Measure.map (cellPt c) (UnforcedLeray.Short.PartIIa.measureHT c) ≪
      ageμ c (-1 / 2) := Measure.absolutelyContinuous_of_le_smul hT'.le
  have hmap : ∀ᵐ x ∂Measure.map (cellPt c) (UnforcedLeray.Short.PartIIa.measureHT c),
      (zsumL c mZ ρb hmZ hρ F : Chart → Ten3) x = zsum F x :=
    hac.ae_le (zsumL_ae c mZ ρb hmZ hρ F)
  exact ae_of_ae_map (measurable_cellPt c).aemeasurable hmap

/-- **Norm of the real form** (source 1641-1646, 2676-2679, 3564-3565). -/
theorem stressTransportNorm_of (hT : ∀ c : ℝ, 0 < c → CellPtHT c)
    (hH : ∀ c : ℝ, 0 < c → CellPtH c) : StressTransportNorm := by
  intro c mZ ρb hc hmZ hρ hρ1 S' S hS
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  apply ContinuousLinearMap.opNorm_le_bound S (norm_nonneg S')
  intro F
  have hae : (cplxT c (hT c hc) (zsumL c mZ ρb hmZ hρ F) :
      UnforcedLeray.B0220.Profile → UnforcedLeray.Short.PartIIa.TensorVal)
        =ᵐ[UnforcedLeray.Short.PartIIa.measureHT c]
      fun p => tv4 (zsum F (cellPt c p)) := by
    filter_upwards [cplxT_ae c (hT c hc) (zsumL c mZ ρb hmZ hρ F),
      stressTransport_zsum_ae hc (hT c hc) hmZ hρ F] with p h1 h2
    rw [h1, h2]
  have hS' := hS F _ hae
  have hsq : ‖S' (cplxT c (hT c hc) (zsumL c mZ ρb hmZ hρ F))‖ ^ 2 = c * ‖S F‖ ^ 2 :=
    Body.norm_sq_cellPt hc.le (hH c hc) merC Body.norm_merC_eq (S F)
      (S' (cplxT c (hT c hc) (zsumL c mZ ρb hmZ hρ F))) hS'
  have hF'norm : ‖cplxT c (hT c hc) (zsumL c mZ ρb hmZ hρ F)‖ ≤ Real.sqrt c * ‖F‖ :=
    (cplxT_norm_le_sqrt_aux c (hT c hc) (zsumL c mZ ρb hmZ hρ F)).trans
      (mul_le_mul_of_nonneg_left (ob_zsumL_norm_le hmZ hρ hρ1 F) hsc.le)
  have hEq : ‖S' (cplxT c (hT c hc) (zsumL c mZ ρb hmZ hρ F))‖ = Real.sqrt c * ‖S F‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (S' (cplxT c (hT c hc) (zsumL c mZ ρb hmZ hρ F)))), hsq,
      Real.sqrt_mul hc.le, Real.sqrt_sq (norm_nonneg _)]
  have hop := S'.le_opNorm (cplxT c (hT c hc) (zsumL c mZ ρb hmZ hρ F))
  have key : Real.sqrt c * ‖S F‖ ≤ Real.sqrt c * (‖S'‖ * ‖F‖) := by
    calc Real.sqrt c * ‖S F‖
        = ‖S' (cplxT c (hT c hc) (zsumL c mZ ρb hmZ hρ F))‖ := hEq.symm
      _ ≤ ‖S'‖ * ‖cplxT c (hT c hc) (zsumL c mZ ρb hmZ hρ F)‖ := hop
      _ ≤ ‖S'‖ * (Real.sqrt c * ‖F‖) := mul_le_mul_of_nonneg_left hF'norm (norm_nonneg _)
      _ = Real.sqrt c * (‖S'‖ * ‖F‖) := by ring
  exact le_of_mul_le_mul_left key hsc

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
