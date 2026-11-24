import UnforcedLeray.Short.PartIIa.Sub.N02_3_7

/-!


Source of record: `the November 2 reference manuscript`, lines 1728-1735.
Twin of `Sub/N02_3_7.lean` (gradient ansatz) for the stream ansatz.  Error field
`e = (f_r, 0) - streamC ε (-χ_L Φ)`, `Φ = zPrimC f_r`, `Φ_S = zPrimC (opS f_r)`.
Pointwise (from `ZeroPrimSmooth`, `ZeroPrimComm`, `∂_q = 0`):
`‖e‖ ≤ 2ε W_S + ε |η| ‖f_r‖ + (2Mε + M L⁻¹ + ε) W + L⁻¹ |η| ‖f_r‖`
with `W = 1_{|η|≤2L} ‖Φ‖`, `W_S = 1_{|η|≤2L} ‖Φ_S‖`, `M ≥ |χ'|`.  The reused Minkowski Prop is
`ZeroGradCutErrorAux.GCEMinkowski` (task `N02/3/7/3`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

namespace ZeroStreamCutErrorAux

open ZeroGradCutErrorAux

/-- The error field `(f_r, 0) - streamC ε (-χ_L Φ)`, `Φ = zPrimC f_r`. -/
def errS (ε L : ℝ) (f : Profile → MeridC) : Profile → MeridC := fun p =>
  (!₂[f p 0, 0] : MeridC) -
    streamC ε (zCut L (fun r => -zPrimC (fun r' => f r' 0) r)) p

/-- Weighted radial component `|η| ‖f_r‖`. -/
def etaFr (f : Profile → MeridC) : Profile → ℝ := fun p => |p.2.2| * ‖f p 0‖

/-- **Pointwise bound (tex 1731-1735).** With `ψ = -χ_L Φ`, `pdQ ψ = 0` (`QInvariant`),
`-pdEta ψ = χ_L f_r + L⁻¹ χ'(η/L) Φ` (`ZeroPrimSmooth`), `opS Φ = zPrimC (opS f_r)`
(`ZeroPrimComm`), `opK ψ = 2 opS ψ + η pdEta ψ`: for `M ≥ |χ'|`,
`‖e p‖ ≤ 2ε W_S + ε |η|‖f_r‖ + (2Mε + M L⁻¹ + ε) W + L⁻¹ |η|‖f_r‖`.  Uses `0 ≤ χ ≤ 1`,
`χ(t) = 1` for `|t| ≤ 1`, `χ(t) = 0` for `|t| ≥ 2`, `(1-χ_L)|f_r| ≤ 1_{|η|≥L}(|η|/L)|f_r|`,
`|f_r p| ≤ ‖f p‖`, `ε ‖χ_L Φ‖ ≤ ε W`. -/
def SCEPointwise : Prop :=
  ZeroPrimSmooth → ZeroPrimComm →
    ∀ (M c ε L : ℝ) (f : Profile → MeridC), (∀ t, |deriv zChi t| ≤ M) → 0 ≤ ε → 0 < L → 0 < c →
      IsMeridTest c f → QInvariant c f → ∀ p : Profile,
        ‖errS ε L f p‖ ≤ 2 * ε * winP L (fun r => (opS (fun r' => f r' 0)) r) p
          + ε * etaFr f p + (2 * M * ε + M * L⁻¹ + ε) * winP L (fun r => f r 0) p
          + L⁻¹ * etaFr f p

/-- **Square-integrability of the four terms and the error.** -/
def SCEIntegrable : Prop :=
  ZeroPrimSmooth → ZeroPrimComm →
    ∀ (c ε L : ℝ) (f : Profile → MeridC), 0 ≤ ε → 0 < L → 0 < c →
      IsMeridTest c f → QInvariant c f →
        MemLp (fun p => ‖errS ε L f p‖) 2 (measureH c) ∧
        MemLp (winP L (fun r => f r 0)) 2 (measureH c) ∧
        MemLp (winP L (fun r => (opS (fun r' => f r' 0)) r)) 2 (measureH c) ∧
        MemLp (etaFr f) 2 (measureH c)

/-- **Window bound, `S⁰` part**: `ZeroWindowBound` with `g = f_r`, `R = 2L`. -/
def SCEWin0 : Prop :=
  ZeroWindowBound → ∃ K : ℝ, 0 ≤ K ∧ ∀ (c L : ℝ) (f : Profile → MeridC), 0 < c → 0 < L →
    IsMeridTest c f →
      (∫ p, winP L (fun r => f r 0) p ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) ≤
        K * L ^ (1 / 2 : ℝ) * (zMom c 0 0 f + zMom c 0 1 f)

/-- **Window bound, `S¹` part**: `ZeroWindowBound` with `g = opS f_r`, `R = 2L`. -/
def SCEWin1 : Prop :=
  ZeroWindowBound → ∃ K : ℝ, 0 ≤ K ∧ ∀ (c L : ℝ) (f : Profile → MeridC), 0 < c → 0 < L →
    IsMeridTest c f →
      (∫ p, winP L (fun r => (opS (fun r' => f r' 0)) r) p ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) ≤
        K * L ^ (1 / 2 : ℝ) * (zMom c 1 0 f + zMom c 1 1 f)

/-- **Tail bound.** `‖|η| ‖f_r‖‖_{L²} ≤ zMom c 0 1 f`. -/
def SCEMom : Prop :=
  ∀ (c : ℝ) (f : Profile → MeridC), 0 < c → IsMeridTest c f →
    (∫ p, etaFr f p ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) ≤ zMom c 0 1 f

theorem etaFr_nonneg (f : Profile → MeridC) (p : Profile) : 0 ≤ etaFr f p := by
  unfold etaFr; positivity

end ZeroStreamCutErrorAux

open ZeroGradCutErrorAux ZeroStreamCutErrorAux in
/-- **`ZeroStreamCutError` from the lemma Props** (Minkowski is `GCEMinkowski`). -/
theorem zeroStreamCutError_of (hC : ZeroCutoff) (hS : ZeroPrimSmooth) (hK : ZeroPrimComm)
    (hP : SCEPointwise) (hI : SCEIntegrable) (hM : GCEMinkowski)
    (hW : ZeroWindowBound) (hW0 : SCEWin0) (hW1 : SCEWin1) (hm : SCEMom) :
    ZeroStreamCutError := by
  obtain ⟨-, -, -, -, M, hM0, hMb⟩ := hC
  obtain ⟨K0, hK0, hB0⟩ := hW0 hW
  obtain ⟨K1, hK1, hB1⟩ := hW1 hW
  set K := K0 + K1 with hKdef
  have hK' : 0 ≤ K := by positivity
  refine ⟨1 + 2 * K + 3 * M * K + K0, by positivity, fun c ε L f hc hε hL hf hq => ?_⟩
  obtain ⟨hIe, hI0, hI1, hIm⟩ := hI hS hK c ε L f hε hL hc hf hq
  have hk3 : 0 ≤ 2 * M * ε + M * L⁻¹ + ε := by positivity
  have hmain := hM (measureH c) (fun p => ‖errS ε L f p‖)
    (winP L (fun r => (opS (fun r' => f r' 0)) r)) (etaFr f) (winP L (fun r => f r 0)) (etaFr f)
    (2 * ε) ε (2 * M * ε + M * L⁻¹ + ε) (L⁻¹) (by positivity) hε hk3 (by positivity)
    (fun p => norm_nonneg _) (winP_nonneg L _) (etaFr_nonneg f) (winP_nonneg L _)
    (etaFr_nonneg f)
    hIe hI1 hIm hI0 hIm
    (fun p => hP hS hK M c ε L f hMb hε hL hc hf hq p)
  have e1 := hB1 c L f hc hL hf
  have e0 := hB0 c L f hc hL hf
  have e2 := hm c f hc hf
  have hm00 := zMom_nonneg c 0 0 f
  have hm01 := zMom_nonneg c 0 1 f
  have hm10 := zMom_nonneg c 1 0 f
  have hm11 := zMom_nonneg c 1 1 f
  have hX : zMomSum c f = zMom c 0 0 f + zMom c 0 1 f + (zMom c 1 0 f + zMom c 1 1 f) := by
    simp [zMomSum, Finset.sum_range_succ]
  set X := zMomSum c f with hXd
  set s := L ^ (1 / 2 : ℝ) with hs
  have hspos : 0 < s := Real.rpow_pos_of_pos hL _
  have hLs : L = s * s := by
    rw [hs, ← Real.rpow_add hL]; norm_num
  have hneg : L ^ (-(1 / 2 : ℝ)) = s⁻¹ := by
    rw [Real.rpow_neg hL.le]
  rw [hneg]
  have hLi : L⁻¹ = s⁻¹ * s⁻¹ := by rw [hLs, mul_inv]
  have hss : s * s⁻¹ = 1 := mul_inv_cancel₀ hspos.ne'
  have hu : 0 < s⁻¹ := inv_pos.2 hspos
  set u := s⁻¹ with hud
  have hLu : L⁻¹ = u * u := hLi
  rw [hLu] at hmain ⊢
  have hk3' : 0 ≤ 2 * M * ε + M * (u * u) + ε := by positivity
  refine hmain.trans ?_
  have hA1 : (∫ p, winP L (fun r => (opS (fun r' => f r' 0)) r) p ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ)
      ≤ K1 * s * X := by
    refine e1.trans ?_
    have : zMom c 1 0 f + zMom c 1 1 f ≤ X := by rw [hX]; linarith
    have h0 : 0 ≤ K1 * s := by positivity
    exact mul_le_mul_of_nonneg_left this h0
  have hA0 : (∫ p, winP L (fun r => f r 0) p ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) ≤ K0 * s * X := by
    refine e0.trans ?_
    have : zMom c 0 0 f + zMom c 0 1 f ≤ X := by rw [hX]; linarith
    have h0 : 0 ≤ K0 * s := by positivity
    exact mul_le_mul_of_nonneg_left this h0
  have hA2 : (∫ p, etaFr f p ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) ≤ X := by
    refine e2.trans ?_
    rw [hX]; linarith
  have hXn : 0 ≤ X := by rw [hX]; linarith
  have t1 : 2 * ε * (∫ p, winP L (fun r => (opS (fun r' => f r' 0)) r) p ^ 2 ∂(measureH c)) ^
      (1 / 2 : ℝ) ≤ 2 * ε * (K1 * s * X) := mul_le_mul_of_nonneg_left hA1 (by positivity)
  have t2 : ε * (∫ p, etaFr f p ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) ≤ ε * X :=
    mul_le_mul_of_nonneg_left hA2 hε
  have t3 : (2 * M * ε + M * (u * u) + ε) *
      (∫ p, winP L (fun r => f r 0) p ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) ≤
      (2 * M * ε + M * (u * u) + ε) * (K0 * s * X) :=
    mul_le_mul_of_nonneg_left hA0 hk3'
  have t4 : u * u * (∫ p, etaFr f p ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) ≤ u * u * X :=
    mul_le_mul_of_nonneg_left hA2 (by positivity)
  have hal := alg M K0 K1 ε s u X hM0 hK0 hK1 hε hspos hu hss hXn
  have hex : (2 * M * ε + M * (u * u) + ε) * (K0 * s * X)
      = (2 * M * ε + M * (u * u)) * (K0 * s * X) + K0 * (ε * s) * X := by ring
  have hex2 : K0 * (ε * s) * X ≤ K0 * (u * u + u + ε * s + ε) * X := by
    have : 0 ≤ K0 * X := mul_nonneg hK0 hXn
    have h2 : 0 ≤ u * u + u + ε := by positivity
    nlinarith [mul_nonneg this h2]
  have hfin : (1 + 2 * (K0 + K1) + 3 * M * (K0 + K1)) * (u * u + u + ε * s + ε) * X
      + K0 * (u * u + u + ε * s + ε) * X
      = (1 + 2 * K + 3 * M * K + K0) * (u * u + u + ε * s + ε) * X := by
    rw [hKdef]; ring
  have := add_le_add (add_le_add (add_le_add t1 t2) t3) t4
  rw [hex] at this
  linarith
end UnforcedLeray.Short.PartIIa
