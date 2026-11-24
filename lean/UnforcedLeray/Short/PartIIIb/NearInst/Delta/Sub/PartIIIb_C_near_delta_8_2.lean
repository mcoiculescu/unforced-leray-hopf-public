import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Sub.PartIIIb_C_near_delta_8
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Exists

/-!
# Decomposition of `compactWindowComparison` (item `PartIII-b:C/near/delta/8/2`)

Source of record `the November 2 reference manuscript`,
3956-3967 (the complete-block comparison with `χ = 1` on the bin box and `Γ^K ≤ P_ν ε^{-K(a+b)}`),
using `PartIIa.NearCompactFreeComparison` (1692-1722) in real form, `PartIIa.NearStressMapExists`
(1678-1690) and uniqueness of the causal solution (`IIIa.FreeCausalExistsUnique`, 3427-3440).

Steps, as four lemmas:

* `WindowCutoffExists` : a smooth cutoff `χ = 1` on the bin box, supported in
  `[l/2, r+1] × {|η| ≤ |L|+1}`, with `C⁸` norms `≤ C₀ (1 + l⁻¹)⁸`;
* `GammaWindowBound` : the constant `Γ` of that cutoff is `≤ A ν^{-m} ε^{-8(a+b)}`
  (`σ = l/2 ≥ ε^a/2`, `H₁ = r+1 ≤ 2ε^{-b}`, `L₁ = |L_⊥|+1`, `c = ν^{-2}`);
* `FlatStressTransport` : `S₀` (the flat free causal response, `IsFreeStress`) is the real form of a
  `PartIIa.IsStressMap c 0 (T0flat)` map (existence from `NearStressMapExists`, identification by
  uniqueness of the causal solution);
* `WindowNormTransport` : if `‖χ(S'_ε - S'_0)F'‖ ≤ C‖F'‖` for `χ = 1` on the bin box and
  `S_ε, S_0` are real forms of `S'_ε, S'_0`, then `‖1_{bin}(S_ε - S_0)1_{A}‖_{Z→H} ≤ C`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.Blueprint.Planar

open UnforcedLeray.Short.PartIIa in
/-- **The window cutoff** (source 3956-3967, "`χ = 1` on the bin box"): there is a universal `C₀`
such that for every `c > 0`, `0 < l < r` and every `L` there are `χ, χ₁` with `χ` a near cutoff
(`IsNearCutoff c (l/2) (r+1) (|L|+1)`: smooth, `c`-periodic in `q`, supported in
`l/2 ≤ s ≤ r+1`, `|η| ≤ |L|+1`), `χ₁` a larger cutoff, `0 ≤ χ ≤ 1`, `χ = 1` on the bin box
`{l ≤ s < r, |η| ≤ L}` (all `q`), and `‖χ‖_{C⁸} + ‖χ₁‖_{C⁸} ≤ C₀ (1 + l⁻¹)⁸`. -/
def WindowCutoffExists : Prop :=
  ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ (c l r L : ℝ), 0 < c → 0 < l → l < r →
    ∃ χ χ1 : UnforcedLeray.B0220.Profile → ℝ,
      IsNearCutoff c (l / 2) (r + 1) (|L| + 1) χ ∧ IsLargerCutoff c χ χ1 ∧
      (∀ p, 0 ≤ χ p ∧ χ p ≤ 1) ∧
      (∀ p : UnforcedLeray.B0220.Profile, l ≤ p.1 → p.1 < r → |p.2.2| ≤ L → χ p = 1) ∧
      cNorm8 χ + cNorm8 χ1 ≤ C0 * (1 + l⁻¹) ^ 8

open UnforcedLeray.Short.PartIIa in
/-- **The polynomial bound on `Γ`** (source 3962-3967, `Γ^K ≤ P_ν ε^{-K(a+b)}`): for `C₀ ≥ 0` there
is `m` such that for every `C_⊥` there is `A ≥ 0` with, for `0 < ν ≤ 1`, `c = ν^{-2}`,
`0 < ε ≤ 1`, `a, b > 0`, `ε^a ≤ l`, `r ≤ ε^{-b}` and cutoffs with
`‖χ‖_{C⁸} + ‖χ₁‖_{C⁸} ≤ C₀(1 + l⁻¹)⁸`:
`Γ(ν, c, l/2, r+1, |L_⊥|+1, 1/4, 1/4, χ, χ₁) ≤ A ν^{-m} ε^{-8(a+b)}`, `L_⊥ = transL C_⊥ c ν ε^{-b}`. -/
def GammaWindowBound : Prop :=
  ∀ C0 : ℝ, 0 ≤ C0 → ∃ m : ℕ, ∀ Cperp : ℝ, ∃ A : ℝ, 0 ≤ A ∧
    ∀ (ν c ε a b l r : ℝ) (χ χ1 : UnforcedLeray.B0220.Profile → ℝ),
      0 < ν → ν ≤ 1 → c = (ν ^ 2)⁻¹ → 0 < ε → ε ≤ 1 → 0 < a → 0 < b → ε ^ a ≤ l →
      r ≤ ε ^ (-b) → cNorm8 χ + cNorm8 χ1 ≤ C0 * (1 + l⁻¹) ^ 8 →
        Gamma ν c (l / 2) (r + 1) (|transL Cperp c ν (ε ^ (-b))| + 1) (1 / 4) (1 / 4) χ χ1 ≤
          A * ν⁻¹ ^ m * ε ^ (-(8 * (a + b)))

open UnforcedLeray.Short.PartIIa in
/-- **`S₀` is a real form of the flat stress map** (source 3956-3967 with 1686-1689, 3427-3440):
given `NearStressMapExists` and `IIIa.FreeCausalExistsUnique`, for `K ⋐ (0, 1/4)` and small `ν`,
`c = ν^{-2}`, every `S₀` with `IsFreeStress` is the real form of a
`IsStressMap c 0 (T0flat)` map `S₀'` (take `S₀'` from `NearStressMapExists`; for a real tensor
`F'` transported from `F ∈ Z` its output is a causal energy solution of the free equation, hence
equals `S₀F` by uniqueness). -/
def FlatStressTransport : Prop :=
  NearStressMapExists → UnforcedLeray.Short.IIIa.FreeCausalExistsUnique →
  ∀ Kset : Set ℝ, IsCompact Kset → Kset ⊆ Ioo 0 (1 / 4) →
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ (ν c μ mZ ρb : ℝ) (hc : 0 < c), 0 < ν → ν ≤ ν₀ → c = (ν ^ 2)⁻¹ →
      μ ∈ Kset → 0 ≤ mZ → 0 < ρb → ρb ≤ 1 →
      ∀ S0 : Zsp c mZ ρb →L[ℝ] Hsp c, IsFreeStress S0 ν μ →
        ∃ S0' : HTSpace c →L[ℂ] UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC,
          IsStressMap c 0 (T0flat hc ν (μ : ℂ)) S0' ∧ IsStressTransport S0 S0'

open UnforcedLeray.Short.PartIIa in
/-- **Real-form norm transport** (source 3956-3967, step (d): "`1_{bin} ≤ χ` so
`‖1_{bin}X‖ ≤ ‖χX‖`, and `inRestr` has norm `≤ 1`"; the transport of the norms is that of
`StressTransportNorm`, `‖F₁ + F₂‖_{H_T} ≤ ‖F‖_Z`, and of `CellPtH`): if `S_ε, S_0` are real forms
of `S'_ε, S'_0`, `χ = 1` on the bin box, and `‖χ(S'_ε - S'_0)F'‖_H ≤ C‖F'‖_{H_T}` for all `F'`,
then `‖1_{bin}(S_ε - S_0)1_A‖_{Z→H} ≤ C` for measurable `A`. -/
def WindowNormTransport : Prop :=
  ∀ (c mZ ρb : ℝ), 0 < c → 0 ≤ mZ → 0 < ρb → ρb ≤ 1 →
    ∀ (Seps S0 : Zsp c mZ ρb →L[ℝ] Hsp c)
      (Seps' S0' : HTSpace c →L[ℂ] UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC),
      IsStressTransport Seps Seps' → IsStressTransport S0 S0' →
      ∀ (l r L : ℝ) (A : Set Chart), MeasurableSet A →
        ∀ (χ : UnforcedLeray.B0220.Profile → ℝ) (hm : Measurable χ) (B : ℝ)
          (hB : ∀ p, |χ p| ≤ B) (C : ℝ), 0 ≤ C →
          (∀ p : UnforcedLeray.B0220.Profile, l ≤ p.1 → p.1 < r → |p.2.2| ≤ L → χ p = 1) →
          (∀ F' : HTSpace c,
            ‖mulChi (UnforcedLeray.B0220.measureH c) χ hm hB ((Seps' - S0') F')‖ ≤ C * ‖F'‖) →
            ‖outRestr c (binSet l r L) ∘L (Seps - S0) ∘L inRestr c mZ ρb A‖ ≤ C

open UnforcedLeray.Short.PartIIa in
/-- **`CompactWindowComparison` from its four lemmas and the three source hypotheses.** -/
theorem compactWindowComparison_of (hCut : WindowCutoffExists) (hG : GammaWindowBound)
    (hF : FlatStressTransport) (hN : WindowNormTransport)
    (hC : NearCompactFreeComparison) (hS : NearStressMapExists)
    (hU : UnforcedLeray.Short.IIIa.FreeCausalExistsUnique) : CompactWindowComparison := by
  intro Kset hK hKs mZ hmZ dm dp hdm
  obtain ⟨C0, hC00, hcut⟩ := hCut
  obtain ⟨k, Ck, hCk0, hCmain⟩ := hC
  obtain ⟨m, hm⟩ := hG C0 hC00
  obtain ⟨ν₁, hν₁, hper⟩ := UnforcedLeray.Short.PartIIIb.NearInst.Masked.exists_period_le_one hdm
  obtain ⟨ν₂, hν₂, hflat⟩ := hF hS hU Kset hK hKs
  refine ⟨8 * k, ?_⟩
  intro a b δ Cperp ha hb hb1 hδ
  obtain ⟨A, hA0, hAg⟩ := hm Cperp
  refine ⟨Ck * A ^ k, m * k, min (min ν₁ ν₂) 1, lt_min (lt_min hν₁ hν₂) one_pos, ?_⟩
  intro p d hreg hν ρb hρ hρ1 μ hμ Seps S0 Seps' hSeps htr hS0 l r hal hlr hr hrS
  have hν1 : p.ν ≤ ν₁ := le_trans hν (le_trans (min_le_left _ _) (min_le_left _ _))
  have hν2 : p.ν ≤ ν₂ := le_trans hν (le_trans (min_le_left _ _) (min_le_right _ _))
  have hν3 : p.ν ≤ 1 := le_trans hν (min_le_right _ _)
  have hμ' : μ ∈ Ioo (0 : ℝ) (1 / 4) := hKs hμ
  have hε1 : p.ε ≤ 1 := UnforcedLeray.Short.PartIIIb.NearInst.Masked.eps_le_one_of_regime hreg
  have hP1 : p.period ≤ 1 := hper p d dp hreg hν1
  have hlpos : 0 < l := lt_of_lt_of_le (Real.rpow_pos_of_pos p.ε_pos a) hal
  have hcν : p.c = (p.ν ^ 2)⁻¹ := hreg.c_eq
  obtain ⟨S0', hS0', htr0⟩ := hflat p.ν p.c μ mZ ρb p.c_pos p.ν_pos hν2 hcν hμ hmZ hρ hρ1 S0 hS0
  obtain ⟨χ, χ1, hχ, hχ1, hχ01, hχ1b, hnorm⟩ :=
    hcut p.c l r (transL Cperp p.c p.ν (p.ε ^ (-b))) p.c_pos hlpos hlr
  have hΓ := hAg p.ν p.c p.ε a b l r χ χ1 p.ν_pos hν3 hcν p.ε_pos hε1 ha hb hal hrS hnorm
  have hmeas : Measurable χ := hχ.smooth.continuous.measurable
  have hB : ∀ q, |χ q| ≤ 1 := fun q => by
    rw [abs_of_nonneg (hχ01 q).1]; exact (hχ01 q).2
  have hμn : ‖(μ : ℂ)‖ ≤ 1 / 4 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hμ'.1]
    exact hμ'.2.le
  have hμr : (1 / 4 : ℝ) ≤ (μ : ℂ).re + 1 / 4 := by
    rw [Complex.ofReal_re]
    linarith [hμ'.1]
  have hmain := (hCmain p.ν p.c (l / 2) (r + 1) (|transL Cperp p.c p.ν (p.ε ^ (-b))| + 1)
    (1 / 4) (1 / 4) χ χ1 p.ν_pos p.c_pos (by positivity) (by linarith) (by positivity)
    (by norm_num) hχ hχ1 hmeas 1 hB p.ε p.ε_pos hε1 p.period rfl hP1 (μ : ℂ) hμn hμr).2
    Seps' S0' hSeps hS0'
  have hGnn : 0 ≤ Gamma p.ν p.c (l / 2) (r + 1) (|transL Cperp p.c p.ν (p.ε ^ (-b))| + 1)
      (1 / 4) (1 / 4) χ χ1 := by
    have h8 : ∀ f : UnforcedLeray.B0220.Profile → ℝ, 0 ≤ cNorm8 f := fun f =>
      Finset.sum_nonneg fun j _ => Real.iSup_nonneg fun q => norm_nonneg _
    unfold Gamma GammaBox
    have := p.ν_pos
    have := p.c_pos
    have : 0 < r + 1 := by linarith
    have := h8 χ
    have := h8 χ1
    have := abs_nonneg (transL Cperp p.c p.ν (p.ε ^ (-b)))
    positivity
  set Γ := Gamma p.ν p.c (l / 2) (r + 1) (|transL Cperp p.c p.ν (p.ε ^ (-b))| + 1)
      (1 / 4) (1 / 4) χ χ1 with hΓdef
  have hCnn : 0 ≤ Ck * Γ ^ k * p.ε ^ (1 / 50 : ℝ) :=
    mul_nonneg (mul_nonneg hCk0 (pow_nonneg hGnn _)) (Real.rpow_nonneg p.ε_pos.le _)
  have hnb := hN p.c mZ ρb p.c_pos hmZ hρ hρ1 Seps S0 Seps' S0' htr htr0 l r
    (transL Cperp p.c p.ν (p.ε ^ (-b))) (ageBelow (Real.exp δ * l)) (measurableSet_ageBelow _) χ hmeas 1 hB _ hCnn hχ1b
    (fun F' => by
      have := hmain F'
      linarith)
  refine hnb.trans ?_
  have hε0 := p.ε_pos
  have hpow : Γ ^ k ≤ (A * p.ν⁻¹ ^ m * p.ε ^ (-(8 * (a + b)))) ^ k :=
    pow_le_pow_left₀ hGnn hΓ k
  calc Ck * Γ ^ k * p.ε ^ (1 / 50 : ℝ)
      ≤ Ck * (A * p.ν⁻¹ ^ m * p.ε ^ (-(8 * (a + b)))) ^ k * p.ε ^ (1 / 50 : ℝ) := by
        gcongr
    _ = Ck * A ^ k * p.ν⁻¹ ^ (m * k) * p.ε ^ (1 / 50 - ((8 * k : ℕ) : ℝ) * (a + b)) := by
        have e1 : (p.ε ^ (-(8 * (a + b)))) ^ k = p.ε ^ (-(8 * (a + b)) * (k : ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hε0.le]
        have e2 : p.ε ^ (1 / 50 - ((8 * k : ℕ) : ℝ) * (a + b)) =
            p.ε ^ (-(8 * (a + b)) * (k : ℝ)) * p.ε ^ (1 / 50 : ℝ) := by
          rw [← Real.rpow_add hε0]
          congr 1
          push_cast
          ring
        rw [e2, mul_pow, mul_pow, ← pow_mul, e1]
        ring

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
