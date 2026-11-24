import UnforcedLeray.Short.PartIIa.Sub.N02_3

/-!


Source of record: `the November 2 reference manuscript`, lines 1728-1735
("Cutoff differentiation costs `L₀^{-1/2}`, geometric correction costs `ε L₀^{1/2}`, the omitted
field tail costs `L₀^{-1}`").

Error field `e = (0, f_z) - cgradC ε (χ_L Φ)`, `Φ = zPrimC f_z`, `Φ_S = zPrimC (opS f_z)`.
Pointwise (from `ZeroPrimSmooth`, `ZeroPrimComm`, `∂_q = 0`):
`‖e‖ ≤ 2ε W_S + ε |η| ‖f_z‖ + (2Mε + M L⁻¹) W + L⁻¹ |η| ‖f_z‖`
with `W = 1_{|η|≤2L} ‖Φ‖`, `W_S = 1_{|η|≤2L} ‖Φ_S‖`, `M ≥ |χ'|`. Then Minkowski in `L²(measureH c)`,
the window bound (`ZeroWindowBound`, `R = 2L`) and the tail bound, and constant absorption.
`zeroGradCutError_of` below proves the target from the six lemma Props.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

namespace ZeroGradCutErrorAux

/-- The error field `(0, f_z) - cgradC ε (χ_L Φ)`. -/
def errG (ε L : ℝ) (f : Profile → MeridC) : Profile → MeridC := fun p =>
  (!₂[0, f p 1] : MeridC) - cgradC ε (zCut L (zPrimC (fun r => f r 1))) p

/-- Window `1_{|η| ≤ 2L} ‖Φ‖` of the primitive `Φ = zPrimC g`. -/
def winP (L : ℝ) (g : Profile → ℂ) : Profile → ℝ :=
  {p : Profile | |p.2.2| ≤ 2 * L}.indicator (fun p => ‖zPrimC g p‖)

/-- Weighted axial component `|η| ‖f_z‖`. -/
def etaFz (f : Profile → MeridC) : Profile → ℝ := fun p => |p.2.2| * ‖f p 1‖

/-- **Pointwise bound (tex 1731-1735).** With `pdQ Φ = 0`, `pdEta Φ = f_z` (`ZeroPrimSmooth`),
`opS Φ = zPrimC (opS f_z)` (`ZeroPrimComm`), `opK ψ = 2 opS ψ + η pdEta ψ`,
`pdEta (χ_L Φ) = χ_L f_z + L⁻¹ χ'(η/L) Φ`: for `M ≥ |χ'|`,
`‖e p‖ ≤ 2ε W_S + ε |η|‖f_z‖ + (2Mε + M L⁻¹) W + L⁻¹ |η|‖f_z‖`. Uses `0 ≤ χ ≤ 1`, `χ(t) = 1` for
`|t| ≤ 1`, `χ(t) = 0` for `|t| ≥ 2` (so `χ' = 0` outside `L ≤ |η| ≤ 2L`; `zChi_eq_one/zero` in
`Tasks/.../ZeroMode/Cutoff.lean`), `(1-χ_L)|f_z| ≤ 1_{|η|≥L}(|η|/L)|f_z|`, `|f_z p| ≤ ‖f p‖`. -/
def GCEPointwise : Prop :=
  ZeroPrimSmooth → ZeroPrimComm →
    ∀ (M c ε L : ℝ) (f : Profile → MeridC), (∀ t, |deriv zChi t| ≤ M) → 0 ≤ ε → 0 < L → 0 < c →
      IsMeridTest c f → QInvariant c f → ∀ p : Profile,
        ‖errG ε L f p‖ ≤ 2 * ε * winP L (fun r => (opS (fun r' => f r' 1)) r) p
          + ε * etaFz f p + (2 * M * ε + M * L⁻¹) * winP L (fun r => f r 1) p
          + L⁻¹ * etaFz f p

/-- **Square-integrability of the four terms and the error** (continuous, compact band support,
finite measure on the cell; `errG` continuous by `ZeroPrimSmooth`). -/
def GCEIntegrable : Prop :=
  ZeroPrimSmooth → ZeroPrimComm →
    ∀ (c ε L : ℝ) (f : Profile → MeridC), 0 ≤ ε → 0 < L → 0 < c →
      IsMeridTest c f → QInvariant c f →
        MemLp (fun p => ‖errG ε L f p‖) 2 (measureH c) ∧
        MemLp (winP L (fun r => f r 1)) 2 (measureH c) ∧
        MemLp (winP L (fun r => (opS (fun r' => f r' 1)) r)) 2 (measureH c) ∧
        MemLp (etaFz f) 2 (measureH c)

/-- **Minkowski for four nonnegative terms** (`eLpNorm_add_le`, `MemLp.eLpNorm_eq_integral_rpow_norm`;
pattern of `zLpNorm_eq`). -/
def GCEMinkowski : Prop :=
  ∀ (μ : Measure Profile) (g a₁ a₂ a₃ a₄ : Profile → ℝ) (k₁ k₂ k₃ k₄ : ℝ),
    0 ≤ k₁ → 0 ≤ k₂ → 0 ≤ k₃ → 0 ≤ k₄ → (∀ p, 0 ≤ g p) → (∀ p, 0 ≤ a₁ p) → (∀ p, 0 ≤ a₂ p) →
    (∀ p, 0 ≤ a₃ p) → (∀ p, 0 ≤ a₄ p) →
    MemLp g 2 μ → MemLp a₁ 2 μ → MemLp a₂ 2 μ → MemLp a₃ 2 μ → MemLp a₄ 2 μ →
    (∀ p, g p ≤ k₁ * a₁ p + k₂ * a₂ p + k₃ * a₃ p + k₄ * a₄ p) →
      (∫ p, g p ^ 2 ∂μ) ^ (1 / 2 : ℝ) ≤
        k₁ * (∫ p, a₁ p ^ 2 ∂μ) ^ (1 / 2 : ℝ) + k₂ * (∫ p, a₂ p ^ 2 ∂μ) ^ (1 / 2 : ℝ)
          + k₃ * (∫ p, a₃ p ^ 2 ∂μ) ^ (1 / 2 : ℝ) + k₄ * (∫ p, a₄ p ^ 2 ∂μ) ^ (1 / 2 : ℝ)

/-- **Window bound, `S⁰` part.** From `ZeroWindowBound` with `g = f_z`, `R = 2L`
(`‖f_z p‖ ≤ ‖f p‖`, monotone integrals; `(2L)^{1/2} ≤ 2 L^{1/2}`). -/
def GCEWin0 : Prop :=
  ZeroWindowBound → ∃ K : ℝ, 0 ≤ K ∧ ∀ (c L : ℝ) (f : Profile → MeridC), 0 < c → 0 < L →
    IsMeridTest c f →
      (∫ p, winP L (fun r => f r 1) p ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) ≤
        K * L ^ (1 / 2 : ℝ) * (zMom c 0 0 f + zMom c 0 1 f)

/-- **Window bound, `S¹` part.** From `ZeroWindowBound` with `g = opS f_z` (smooth band function,
`(opS f_z) p = (opS f p) 1`, `‖(opS f p) 1‖ ≤ ‖opS f p‖`, `opS^[1] f = opS f`), `R = 2L`. -/
def GCEWin1 : Prop :=
  ZeroWindowBound → ∃ K : ℝ, 0 ≤ K ∧ ∀ (c L : ℝ) (f : Profile → MeridC), 0 < c → 0 < L →
    IsMeridTest c f →
      (∫ p, winP L (fun r => (opS (fun r' => f r' 1)) r) p ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) ≤
        K * L ^ (1 / 2 : ℝ) * (zMom c 1 0 f + zMom c 1 1 f)

/-- **Tail bound.** `‖|η| ‖f_z‖‖_{L²} ≤ zMom c 0 1 f` (since `‖f p 1‖ ≤ ‖f p‖`, `opS^[0] f = f`). -/
def GCEMom : Prop :=
  ∀ (c : ℝ) (f : Profile → MeridC), 0 < c → IsMeridTest c f →
    (∫ p, etaFz f p ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) ≤ zMom c 0 1 f

theorem zMom_nonneg (c : ℝ) (a j : ℕ) (f : Profile → MeridC) : 0 ≤ zMom c a j f :=
  Real.rpow_nonneg (integral_nonneg fun p => by positivity) _

theorem winP_nonneg (L : ℝ) (g : Profile → ℂ) (p : Profile) : 0 ≤ winP L g p := by
  unfold winP
  exact Set.indicator_nonneg (fun _ _ => norm_nonneg _) p

theorem etaFz_nonneg (f : Profile → MeridC) (p : Profile) : 0 ≤ etaFz f p := by
  unfold etaFz; positivity

theorem alg (M K0 K1 ε s u X : ℝ) (hM0 : 0 ≤ M) (hK0 : 0 ≤ K0) (hK1 : 0 ≤ K1) (hε : 0 ≤ ε)
    (hs : 0 < s) (hu : 0 < u) (hss : s * u = 1) (hX : 0 ≤ X) :
    2 * ε * (K1 * s * X) + ε * X + (2 * M * ε + M * (u * u)) * (K0 * s * X) + u * u * X
      ≤ (1 + 2 * (K0 + K1) + 3 * M * (K0 + K1)) * (u * u + u + ε * s + ε) * X := by
  have hk : (2 * M * ε + M * (u * u)) * (K0 * s) = 2 * M * K0 * ε * s + M * K0 * u := by
    have : u * u * s = u := by rw [mul_assoc, mul_comm u s, hss, mul_one]
    linear_combination (M * K0) * this
  have e : (2 * M * ε + M * (u * u)) * (K0 * s * X)
      = ((2 * M * ε + M * (u * u)) * (K0 * s)) * X := by ring
  rw [e, hk]
  have hMK0 := mul_nonneg hM0 hK0
  have hMK1 := mul_nonneg hM0 hK1
  have hd : (1 + 2 * (K0 + K1) + 3 * M * (K0 + K1)) * (u * u + u + ε * s + ε) * X
      - (2 * ε * (K1 * s * X) + ε * X + (2 * M * K0 * ε * s + M * K0 * u) * X + u * u * X)
      = ((2 * (K0 + K1) + 3 * M * (K0 + K1)) * (u * u)
        + (1 + 2 * (K0 + K1) + 3 * M * (K0 + K1) - M * K0) * u
        + (1 + 2 * (K0 + K1) + 3 * M * (K0 + K1) - 2 * K1 - 2 * M * K0) * (ε * s)
        + (2 * (K0 + K1) + 3 * M * (K0 + K1)) * ε) * X := by ring
  have a1 : 0 ≤ 1 + 2 * (K0 + K1) + 3 * M * (K0 + K1) - M * K0 := by nlinarith
  have a2 : 0 ≤ 1 + 2 * (K0 + K1) + 3 * M * (K0 + K1) - 2 * K1 - 2 * M * K0 := by nlinarith
  have a3 : 0 ≤ 2 * (K0 + K1) + 3 * M * (K0 + K1) := by nlinarith
  have hnn : 0 ≤ ((2 * (K0 + K1) + 3 * M * (K0 + K1)) * (u * u)
        + (1 + 2 * (K0 + K1) + 3 * M * (K0 + K1) - M * K0) * u
        + (1 + 2 * (K0 + K1) + 3 * M * (K0 + K1) - 2 * K1 - 2 * M * K0) * (ε * s)
        + (2 * (K0 + K1) + 3 * M * (K0 + K1)) * ε) * X := by
    apply mul_nonneg _ hX
    have b1 := mul_nonneg a1 hu.le
    have b2 := mul_nonneg a2 (mul_nonneg hε hs.le)
    have b3 := mul_nonneg a3 (mul_nonneg hu.le hu.le)
    have b4 := mul_nonneg a3 hε
    linarith
  linarith

end ZeroGradCutErrorAux

open ZeroGradCutErrorAux in
/-- **`ZeroGradCutError` from the six lemma Props.** -/
theorem zeroGradCutError_of (hC : ZeroCutoff) (hS : ZeroPrimSmooth) (hK : ZeroPrimComm)
    (hW : ZeroWindowBound) (hP : GCEPointwise) (hI : GCEIntegrable) (hM : GCEMinkowski)
    (hW0 : GCEWin0) (hW1 : GCEWin1) (hm : GCEMom) : ZeroGradCutError := by
  obtain ⟨-, -, -, -, M, hM0, hMb⟩ := hC
  obtain ⟨K0, hK0, hB0⟩ := hW0 hW
  obtain ⟨K1, hK1, hB1⟩ := hW1 hW
  set K := K0 + K1 with hKdef
  have hK' : 0 ≤ K := by positivity
  refine ⟨1 + 2 * K + 3 * M * K, by positivity, fun c ε L f hc hε hL hf hq => ?_⟩
  obtain ⟨hIe, hI0, hI1, hIm⟩ := hI hS hK c ε L f hε hL hc hf hq
  have hk3 : 0 ≤ 2 * M * ε + M * L⁻¹ := by positivity
  have hmain := hM (measureH c) (fun p => ‖errG ε L f p‖)
    (winP L (fun r => (opS (fun r' => f r' 1)) r)) (etaFz f) (winP L (fun r => f r 1)) (etaFz f)
    (2 * ε) ε (2 * M * ε + M * L⁻¹) (L⁻¹) (by positivity) hε hk3 (by positivity)
    (fun p => norm_nonneg _) (winP_nonneg L _) (etaFz_nonneg f) (winP_nonneg L _) (etaFz_nonneg f)
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
  have hk3' : 0 ≤ 2 * M * ε + M * (u * u) := by positivity
  refine hmain.trans ?_
  have hA1 : (∫ p, winP L (fun r => (opS (fun r' => f r' 1)) r) p ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ)
      ≤ K1 * s * X := by
    refine e1.trans ?_
    have : zMom c 1 0 f + zMom c 1 1 f ≤ X := by rw [hX]; linarith
    have h0 : 0 ≤ K1 * s := by positivity
    exact mul_le_mul_of_nonneg_left this h0
  have hA0 : (∫ p, winP L (fun r => f r 1) p ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) ≤ K0 * s * X := by
    refine e0.trans ?_
    have : zMom c 0 0 f + zMom c 0 1 f ≤ X := by rw [hX]; linarith
    have h0 : 0 ≤ K0 * s := by positivity
    exact mul_le_mul_of_nonneg_left this h0
  have hA2 : (∫ p, etaFz f p ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) ≤ X := by
    refine e2.trans ?_
    rw [hX]; linarith
  have hXn : 0 ≤ X := by rw [hX]; linarith
  have t1 : 2 * ε * (∫ p, winP L (fun r => (opS (fun r' => f r' 1)) r) p ^ 2 ∂(measureH c)) ^
      (1 / 2 : ℝ) ≤ 2 * ε * (K1 * s * X) := mul_le_mul_of_nonneg_left hA1 (by positivity)
  have t2 : ε * (∫ p, etaFz f p ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) ≤ ε * X :=
    mul_le_mul_of_nonneg_left hA2 hε
  have t3 : (2 * M * ε + M * (u * u)) * (∫ p, winP L (fun r => f r 1) p ^ 2 ∂(measureH c)) ^
      (1 / 2 : ℝ) ≤ (2 * M * ε + M * (u * u)) * (K0 * s * X) :=
    mul_le_mul_of_nonneg_left hA0 hk3'
  have t4 : u * u * (∫ p, etaFz f p ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) ≤ u * u * X :=
    mul_le_mul_of_nonneg_left hA2 (by positivity)
  exact (add_le_add (add_le_add (add_le_add t1 t2) t3) t4).trans
    (alg M K0 K1 ε s u X hM0 hK0 hK1 hε hspos hu hss hXn)

end UnforcedLeray.Short.PartIIa
