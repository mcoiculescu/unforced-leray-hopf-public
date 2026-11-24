import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Sub.PartIIIb_C_near_delta_8_2
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.CellPtHT

/-!
# Decomposition of `windowNormTransport` (item `PartIII-b:C/near/delta/8/2/4`)

Source of record `the November 2 reference manuscript`,
3956-3967 (step (d): `1_bin ≤ χ`, `inRestr` has norm `≤ 1`), 1641-1646 and 2676-2679 (the cell
recentring `cellPt`: `map cellPt μ_HT = c • s^{-1/2}`, `map cellPt μ_H = c • s^{-3/2}`; the factor
`√c` appears once on the input and once on the output and cancels).

Four lemmas:

* `InRestrNormLeOne`   : `‖inRestr c mZ ρb A‖ ≤ 1` for measurable `A`;
* `ZsumTransportNorm`  : `‖cplxT (zsumL X)‖_{H_T} ≤ √c ‖X‖_Z` (`W ≥ 1`, `ρ_b ≤ 1`, `CellPtHT`);
* `CplxZsumAE`         : `cplxT (zsumL X) = tv4 (zsum X ∘ cellPt)` a.e. (the `hin` step of
  `Masked.isStressTransport_realForm`, using `cplxT_ae` and `zsumL_ae`);
* `OutRestrBinTransport` : `√c ‖1_bin g‖_H ≤ ‖χ g'‖_H` when `g' = merC (g ∘ cellPt)` a.e. and
  `χ = 1` on the bin box (`cellPt` preserves `s` and `η`; `CellPtH`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.Blueprint.Planar

/-- The input restriction has norm `≤ 1` (source 3956-3967: "`inRestr` has norm `≤ 1`"). -/
def InRestrNormLeOne : Prop :=
  ∀ (c mZ ρb : ℝ) (A : Set Chart), MeasurableSet A → ‖inRestr c mZ ρb A‖ ≤ 1

/-- The transport of the summed input has norm `≤ √c ‖X‖` (source 1641-1646, 2676-2679, 3564-3571:
`‖F₁+F₂‖_{H_T} ≤ ‖F‖_Z` for `W ≥ 1`, `ρ_b ≤ 1`, and `map cellPt μ_HT = c • s^{-1/2}`). -/
def ZsumTransportNorm : Prop :=
  ∀ (c mZ ρb : ℝ) (hT : Masked.CellPtHT c) (hmZ : 0 ≤ mZ) (hρ : 0 < ρb), ρb ≤ 1 →
    ∀ X : Zsp c mZ ρb,
      ‖Masked.cplxT c hT (Masked.zsumL c mZ ρb hmZ hρ X)‖ ≤ Real.sqrt c * ‖X‖

/-- The transported summed input represents `tv4 (zsum X ∘ cellPt)` (source 1641-1646; the `hin`
step of `Masked.isStressTransport_realForm`). -/
def CplxZsumAE : Prop :=
  ∀ (c mZ ρb : ℝ) (hT : Masked.CellPtHT c) (hmZ : 0 ≤ mZ) (hρ : 0 < ρb) (X : Zsp c mZ ρb),
    (Masked.cplxT c hT (Masked.zsumL c mZ ρb hmZ hρ X) :
        UnforcedLeray.B0220.Profile → UnforcedLeray.Short.PartIIa.TensorVal)
      =ᵐ[UnforcedLeray.Short.PartIIa.measureHT c] fun p => tv4 (zsum X (cellPt c p))

/-- The bin restriction is dominated by the cutoff `χ = 1` on the bin box, after the transport
`map cellPt μ_H = c • s^{-3/2}` (source 3956-3967 step (d), 2676-2679): for `g' = merC (g ∘ cellPt)`
a.e. for `g = g₁ - g₂` (the difference of two real forms), `√c ‖1_bin g‖_H ≤ ‖χ g'‖_H`. -/
def OutRestrBinTransport : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (l r L : ℝ) (χ : UnforcedLeray.B0220.Profile → ℝ) (hm : Measurable χ)
    (B : ℝ) (hB : ∀ p, |χ p| ≤ B),
    (∀ p : UnforcedLeray.B0220.Profile, l ≤ p.1 → p.1 < r → |p.2.2| ≤ L → χ p = 1) →
    ∀ (g₁ g₂ : Hsp c) (g' : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC),
      (g' : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
          =ᵐ[UnforcedLeray.B0220.measureH c]
            (fun p => merC (g₁ (cellPt c p)) - merC (g₂ (cellPt c p))) →
        Real.sqrt c * ‖outRestr c (binSet l r L) (g₁ - g₂)‖ ≤
          ‖UnforcedLeray.Short.PartIIa.mulChi (UnforcedLeray.B0220.measureH c) χ hm hB g'‖

theorem windowNormTransport_of (h1 : InRestrNormLeOne) (h2 : ZsumTransportNorm)
    (h3 : CplxZsumAE) (h4 : OutRestrBinTransport) : WindowNormTransport := by
  intro c mZ ρb hc hmZ hρ hρ1 Seps S0 Seps' S0' hSeps hS0 l r L A hA χ hm B hB C hC0 hχ hbound
  have hT : Masked.CellPtHT c := Masked.cellPtHT_eq c hc
  refine ContinuousLinearMap.opNorm_le_bound _ hC0 fun G => ?_
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  set X := inRestr c mZ ρb A G with hX
  set F' := Masked.cplxT c hT (Masked.zsumL c mZ ρb hmZ hρ X) with hF'
  have hF'ae := h3 c mZ ρb hT hmZ hρ X
  have e1 := hSeps X F' hF'ae
  have e2 := hS0 X F' hF'ae
  have e3 : ((Seps' - S0') F' : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
      =ᵐ[UnforcedLeray.B0220.measureH c]
        (fun p => merC ((Seps X) (cellPt c p)) - merC ((S0 X) (cellPt c p))) := by
    filter_upwards [Lp.coeFn_sub (Seps' F') (S0' F'), e1, e2] with p hp e1p e2p
    rw [ContinuousLinearMap.sub_apply, hp, Pi.sub_apply, e1p, e2p]
  have k0 := h4 c hc l r L χ hm B hB hχ (Seps X) (S0 X) ((Seps' - S0') F') e3
  have k : Real.sqrt c * ‖(outRestr c (binSet l r L) ∘L (Seps - S0) ∘L inRestr c mZ ρb A) G‖ ≤
      ‖UnforcedLeray.Short.PartIIa.mulChi (UnforcedLeray.B0220.measureH c) χ hm hB
        ((Seps' - S0') F')‖ := by
    have : (outRestr c (binSet l r L) ∘L (Seps - S0) ∘L inRestr c mZ ρb A) G =
        outRestr c (binSet l r L) (Seps X - S0 X) := rfl
    rw [this]; exact k0
  have k2 := hbound F'
  have k3 := h2 c mZ ρb hT hmZ hρ hρ1 X
  have k4 : ‖X‖ ≤ ‖G‖ := by
    calc ‖X‖ = ‖inRestr c mZ ρb A G‖ := rfl
      _ ≤ ‖inRestr c mZ ρb A‖ * ‖G‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖G‖ := mul_le_mul_of_nonneg_right (h1 c mZ ρb A hA) (norm_nonneg _)
      _ = ‖G‖ := one_mul _
  have k6 : Real.sqrt c * ‖(outRestr c (binSet l r L) ∘L (Seps - S0) ∘L inRestr c mZ ρb A) G‖ ≤
      Real.sqrt c * (C * ‖G‖) := by
    have : ‖F'‖ ≤ Real.sqrt c * ‖G‖ :=
      k3.trans (mul_le_mul_of_nonneg_left k4 hsc.le)
    calc _ ≤ _ := k
      _ ≤ C * ‖F'‖ := k2
      _ ≤ C * (Real.sqrt c * ‖G‖) := mul_le_mul_of_nonneg_left this hC0
      _ = _ := by ring
  exact le_of_mul_le_mul_left k6 hsc

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
