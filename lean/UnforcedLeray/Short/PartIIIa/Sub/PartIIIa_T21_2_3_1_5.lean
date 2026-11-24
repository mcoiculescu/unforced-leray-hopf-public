import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDualitySub

/-!
# Part III-a, `PartIII-a:T21/2/3/1/5`: the product rule for the cut pairing (decomposition)

Source of record: `the November 2 reference manuscript` (SP), lines 3074-3075.

`LadProductRule` is assembled (`ladProductRule_of`) from six leaves:

* `LadPRTest`: `χ_R φ(ρ)` has cylinder-test real and imaginary parts for `ρ ∈ [t, s)`;
* `LadPRWeak`: the weak identity of `IsLinearisedFlow` between two times `a ≤ b`, for a fixed
  complex test (real and imaginary parts cylinder tests);
* `LadPRG`: joint continuity of `G(σ, ρ) = ∫ ladFlowCx (w σ) (u σ) σ (χ_R φ(ρ))` on `[t, r]²`;
* `LadPRK`: continuity of `ρ ↦ ∫ w(ρ) χ_R ∂_ρφ(ρ)` on `(t, r]` and existence of its right limit
  at `t` (`ladDt` is the two-sided derivative, so the value at `t` itself is not constrained by
  `φ` on `[t, s)`);
* `LadPRPair`: continuity of the cut pairing on `[t, r]`;
* `LadPRDeriv`: `d/dρ` of the cut pairing equals `ladRate` on `(t, r)` (the difference-quotient
  argument: `P(ρ+h) - P(ρ) = ∫_ρ^{ρ+h} G(σ, ρ+h) dσ + ∫ w(ρ)(Ψ(ρ+h) - Ψ(ρ))`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

/-- The common hypotheses of `LadProductRule`. -/
structure LadPRSetup (ν c m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t s : ℝ)
    (f : ℝ × ℝ → ℂ) (w : ℝ → ℝ × ℝ → ℂ) (u : ℝ → ℝ × ℝ → Fin 2 → ℂ)
    (φ : ℝ → ℝ × ℝ → ℂ) : Prop where
  hν : 0 < ν
  hc : 0 < c
  ht : 0 ≤ t
  hts : t < s
  flow : IsLinearisedFlow ν c m tr t f w u
  lip : ∃ C : ℝ, ∀ ρ ρ' : ℝ, t ≤ ρ → t ≤ ρ' → ∀ j : Fin 2,
      eLpNorm (fun x => u ρ x j - u ρ' x j) 2 (volume.restrict (B0579.cell c)) ≤
        ENNReal.ofReal C * xNorm c m (w ρ - w ρ')
  smooth : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ)
  periodic : ∀ r ∈ Ico t s, ∀ x : ℝ × ℝ, φ r (x.1 + c, x.2) = φ r x

/-- `G(σ, ρ) = ∫_{C_c} ladFlowCx (w σ) (u σ) σ (χ_R φ(ρ))`. -/
def ladG {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (w : ℝ → ℝ × ℝ → ℂ)
    (u : ℝ → ℝ × ℝ → Fin 2 → ℂ) (φ : ℝ → ℝ × ℝ → ℂ) (R : ℝ) (p : ℝ × ℝ) : ℂ :=
  ∫ x in B0579.cell c, ladFlowCx tr (w p.1) (u p.1) p.1 (ladCutPhi φ R p.2) x

/-- `K(ρ) = ∫_{C_c} w(ρ) χ_R ∂_ρφ(ρ)`. -/
def ladK (c : ℝ) (w φ : ℝ → ℝ × ℝ → ℂ) (R ρ : ℝ) : ℂ :=
  ∫ x in B0579.cell c, w ρ x * ((ladCut R x : ℂ) * ladDt φ ρ x)

theorem ladRate_eq {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (w : ℝ → ℝ × ℝ → ℂ)
    (u : ℝ → ℝ × ℝ → Fin 2 → ℂ) (φ : ℝ → ℝ × ℝ → ℂ) (R ρ : ℝ) :
    ladRate tr w u φ R ρ = ladG tr w u φ R (ρ, ρ) + ladK c w φ R ρ := rfl

/-- **Leaf 1** (cut-off adjoint is a cylinder test; use `ladCutProps`): for `φ` jointly smooth on
`[t, s) × ℝ²` and `c`-periodic, `R > 0`, `ρ ∈ [t, s)`: `Re` and `Im` of `χ_R φ(ρ)` are cylinder
tests (smooth: `φ ρ` is the composite of the jointly smooth map with `x ↦ (ρ, x)`; periodic;
vanish for `|η| > √2 R`). -/
def LadPRTest : Prop :=
  ∀ (c : ℝ) (t s : ℝ) (φ : ℝ → ℝ × ℝ → ℂ), 0 < c →
    ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ) →
    (∀ r ∈ Ico t s, ∀ x : ℝ × ℝ, φ r (x.1 + c, x.2) = φ r x) →
    ∀ R : ℝ, 0 < R → ∀ ρ ∈ Ico t s,
      B0579.IsCylTest c (fun x => (ladCutPhi φ R ρ x).re) ∧
        B0579.IsCylTest c (fun x => (ladCutPhi φ R ρ x).im)

/-- **Leaf 2** (weak identity between two times, SP 2819-2830 via `IsLinearisedFlow.weak` at `a`
and `b` and `timeIntegrable`; `∫_t^b - ∫_t^a = ∫_a^b`; `flowIntegrand` of a real test equals
`ladFlowCx` of its complexification, and `ladFlowCx` is `ℂ`-linear in the test, so apply it to
`Re Ψ`, `Im Ψ`; note `pdCx` of `fun x => (ψ x : ℂ)` is `(pd ψ : ℂ)`). -/
def LadPRWeak : Prop :=
  ∀ (ν c m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t : ℝ) (f : ℝ × ℝ → ℂ)
    (w : ℝ → ℝ × ℝ → ℂ) (u : ℝ → ℝ × ℝ → Fin 2 → ℂ),
    IsLinearisedFlow ν c m tr t f w u →
    ∀ Ψ : ℝ × ℝ → ℂ, B0579.IsCylTest c (fun x => (Ψ x).re) →
      B0579.IsCylTest c (fun x => (Ψ x).im) → ∀ a b : ℝ, t ≤ a → a ≤ b →
        (∫ x in B0579.cell c, w b x * Ψ x) - (∫ x in B0579.cell c, w a x * Ψ x) =
          ∫ σ in a..b, ∫ x in B0579.cell c, ladFlowCx tr (w σ) (u σ) σ Ψ x

/-- **Leaf 3** (joint continuity of `G`; `w` continuous into `X_m` by `strongCont`, `u` continuous
into `L²` by the Lipschitz hypothesis, `jb^m` bounded below on the strip, train velocity and
`∇E` continuous on `[0, ∞) × ℝ²` (`tr.isTrain.smooth_v`, `B0238.Ec tr = Cyl.curl (tr.v ·)`),
the test `χ_Rφ(ρ)` and its `x`-derivatives up to order 2 jointly continuous and supported in
`|η| ≤ √2 R`, cell bounded in `q`, so uniformly continuous on compacts). -/
def LadPRG : Prop :=
  ∀ (ν c m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t s : ℝ) (f : ℝ × ℝ → ℂ)
    (w : ℝ → ℝ × ℝ → ℂ) (u : ℝ → ℝ × ℝ → Fin 2 → ℂ) (φ : ℝ → ℝ × ℝ → ℂ),
    LadPRSetup ν c m tr t s f w u φ → ∀ R : ℝ, 0 < R → ∀ r ∈ Ico t s,
      ContinuousOn (ladG tr w u φ R) (Icc t r ×ˢ Icc t r)

/-- **Leaf 4** (continuity of `ρ ↦ ∫ w(ρ) χ_R ∂_ρφ(ρ)` on `(t, r]` and a right limit at `t`; `ladDt φ` is jointly
continuous on `Ico t s × ℝ²` as a partial derivative of the jointly smooth `φ`, supported in
`|η| ≤ √2 R` after the factor `χ_R`; `w` strongly continuous). -/
def LadPRK : Prop :=
  ∀ (ν c m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t s : ℝ) (f : ℝ × ℝ → ℂ)
    (w : ℝ → ℝ × ℝ → ℂ) (u : ℝ → ℝ × ℝ → Fin 2 → ℂ) (φ : ℝ → ℝ × ℝ → ℂ),
    LadPRSetup ν c m tr t s f w u φ → ∀ R : ℝ, 0 < R → ∀ r ∈ Ico t s,
      ContinuousOn (ladK c w φ R) (Ioc t r) ∧
        ∃ L : ℂ, Tendsto (ladK c w φ R) (𝓝[>] t) (𝓝 L)

/-- **Leaf 5** (continuity of `ρ ↦ ∫ w(ρ) χ_Rφ(ρ)` on `[t, r]`: split
`w(ρ)Ψ(ρ) - w(ρ')Ψ(ρ') = (w(ρ) - w(ρ'))Ψ(ρ) + w(ρ')(Ψ(ρ) - Ψ(ρ'))`, Cauchy-Schwarz in `X_m`
against `X_{-m}`, `Ψ` uniformly continuous in `ρ` with compact `η`-support). -/
def LadPRPair : Prop :=
  ∀ (ν c m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t s : ℝ) (f : ℝ × ℝ → ℂ)
    (w : ℝ → ℝ × ℝ → ℂ) (u : ℝ → ℝ × ℝ → Fin 2 → ℂ) (φ : ℝ → ℝ × ℝ → ℂ),
    LadPRSetup ν c m tr t s f w u φ → ∀ R : ℝ, 0 < R → ∀ r ∈ Ico t s,
      ContinuousOn (ladCutPair c R w φ) (Icc t r)

/-- **Leaf 6** (the derivative; no cutoff analysis needed beyond what the hypotheses give): given
the continuity of `G` and the frozen-test weak identity for every `Ψ(ρ)`, `ρ ∈ [t, r]`,
`P_R(ρ+h) - P_R(ρ) = ∫_ρ^{ρ+h} G(σ, ρ+h) dσ + ∫ w(ρ)(Ψ(ρ+h) - Ψ(ρ))` for small `|h|`;
divide by `h`: the first term tends to `G(ρ, ρ)` by joint continuity of `G` at `(ρ, ρ)`
(use `intervalIntegral` mean-value / `HasDerivAt` of parameter-dependent integrals), the second
to `∫ w(ρ) χ_R ∂_ρφ(ρ)` since the difference quotients of `χ_Rφ` in `ρ` converge uniformly on
`|η| ≤ √2 R`, `0 ≤ q ≤ c` (joint `C¹`, compactness) and `w(ρ) ∈ L²`. -/
def LadPRDeriv : Prop :=
  ∀ (ν c m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t s : ℝ) (f : ℝ × ℝ → ℂ)
    (w : ℝ → ℝ × ℝ → ℂ) (u : ℝ → ℝ × ℝ → Fin 2 → ℂ) (φ : ℝ → ℝ × ℝ → ℂ),
    LadPRSetup ν c m tr t s f w u φ → ∀ R : ℝ, 0 < R → ∀ r ∈ Ico t s,
      ContinuousOn (ladG tr w u φ R) (Icc t r ×ˢ Icc t r) →
      (∀ ρ ∈ Icc t r, ∀ a b : ℝ, t ≤ a → a ≤ b →
        (∫ x in B0579.cell c, w b x * ladCutPhi φ R ρ x) -
            (∫ x in B0579.cell c, w a x * ladCutPhi φ R ρ x) =
          ∫ σ in a..b, ladG tr w u φ R (σ, ρ)) →
      ∀ ρ ∈ Ioo t r, HasDerivAt (ladCutPair c R w φ) (ladRate tr w u φ R ρ) ρ

/-- **Assembly**: `LadProductRule` from the six leaves (FTC on `[t, r]`). -/
theorem ladProductRule_of (h1 : LadPRTest) (h2 : LadPRWeak) (h3 : LadPRG) (h4 : LadPRK)
    (h5 : LadPRPair) (h6 : LadPRDeriv) : LadProductRule := by
  intro ν c m tr t s f w u φ hν hc ht hts hw hLip hφs hper R hR r hr
  have hS : LadPRSetup ν c m tr t s f w u φ := ⟨hν, hc, ht, hts, hw, hLip, hφs, hper⟩
  rcases eq_or_lt_of_le hr.1 with hrt | hrt
  · subst hrt
    exact ⟨IntervalIntegrable.refl, by simp⟩
  have hG := h3 ν c m tr t s f w u φ hS R hR r hr
  have hK := h4 ν c m tr t s f w u φ hS R hR r hr
  have hP := h5 ν c m tr t s f w u φ hS R hR r hr
  have hdiag : ContinuousOn (fun ρ => ladG tr w u φ R (ρ, ρ)) (Icc t r) :=
    hG.comp (continuousOn_id.prodMk continuousOn_id) (fun ρ hρ => ⟨hρ, hρ⟩)
  obtain ⟨hKc, L, hL⟩ := hK
  have hdt : Tendsto (fun ρ => ladG tr w u φ R (ρ, ρ)) (𝓝[>] t)
      (𝓝 (ladG tr w u φ R (t, t))) :=
    (hdiag t ⟨le_rfl, hrt.le⟩).tendsto.mono_left (nhdsWithin_le_of_mem (Icc_mem_nhdsGT hrt))
  have hRt : Tendsto (fun ρ => ladRate tr w u φ R ρ) (𝓝[>] t)
      (𝓝 (ladG tr w u φ R (t, t) + L)) :=
    (hdt.add hL).congr (fun ρ => (ladRate_eq tr w u φ R ρ).symm)
  obtain ⟨Rate', hR'⟩ : ∃ f : ℝ → ℂ, f = Function.update (fun ρ => ladRate tr w u φ R ρ) t
      (ladG tr w u φ R (t, t) + L) := ⟨_, rfl⟩
  have hEq : ∀ ρ ∈ Ioc t r, Rate' ρ = ladRate tr w u φ R ρ := fun ρ hρ => by
    rw [hR']; exact Function.update_of_ne (ne_of_gt hρ.1) _ _
  have hEt : Rate' t = ladG tr w u φ R (t, t) + L := by rw [hR']; exact Function.update_self _ _ _
  have hRateIoc : ContinuousOn (fun ρ => ladRate tr w u φ R ρ) (Ioc t r) := by
    have := (hdiag.mono Ioc_subset_Icc_self).add hKc
    exact this.congr (fun ρ _ => ladRate_eq tr w u φ R ρ)
  have hRate : ContinuousOn Rate' (Icc t r) := by
    intro ρ hρ
    rcases eq_or_lt_of_le hρ.1 with h | h
    · rw [← h]
      refine ContinuousWithinAt.mono ?_ (fun x hx => (mem_Ici.2 hx.1))
      rw [← continuousWithinAt_Ioi_iff_Ici]
      show Tendsto Rate' (𝓝[>] t) (𝓝 (Rate' t))
      rw [hEt]
      refine hRt.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hrt] with x hx
      exact (hEq x ⟨hx.1, hx.2.le⟩).symm
    · rw [← continuousWithinAt_inter (Ioi_mem_nhds h)]
      have e : Icc t r ∩ Ioi t = Ioc t r := by
        ext x; simp only [mem_inter_iff, mem_Icc, mem_Ioi, mem_Ioc]
        constructor
        · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
        · rintro ⟨h3, h2⟩; exact ⟨⟨h3.le, h2⟩, h3⟩
      rw [e]
      exact (hRateIoc.congr (fun x hx => hEq x hx)) ρ ⟨h, hρ.2⟩
  have hRateI : IntervalIntegrable Rate' volume t r := hRate.intervalIntegrable_of_Icc hrt.le
  have hRateI' : IntervalIntegrable (fun ρ => ladRate tr w u φ R ρ) volume t r := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hrt.le] at hRateI ⊢
    exact hRateI.congr_fun hEq measurableSet_Ioc
  have hInt : ∫ ρ in t..r, Rate' ρ = ∫ ρ in t..r, ladRate tr w u φ R ρ := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun ρ hρ => ?_)
    rw [uIoc_of_le hrt.le] at hρ
    exact hEq ρ hρ
  have hweak : ∀ ρ ∈ Icc t r, ∀ a b : ℝ, t ≤ a → a ≤ b →
      (∫ x in B0579.cell c, w b x * ladCutPhi φ R ρ x) -
          (∫ x in B0579.cell c, w a x * ladCutPhi φ R ρ x) =
        ∫ σ in a..b, ladG tr w u φ R (σ, ρ) := by
    intro ρ hρ a b hta hab
    have hρs : ρ ∈ Ico t s := ⟨hρ.1, lt_of_le_of_lt hρ.2 hr.2⟩
    obtain ⟨hre, him⟩ := h1 c t s φ hc hφs hper R hR ρ hρs
    exact h2 ν c m tr t f w u hw (ladCutPhi φ R ρ) hre him a b hta hab
  have hD := h6 ν c m tr t s f w u φ hS R hR r hr hG hweak
  refine ⟨hRateI', ?_⟩
  rw [← hInt]
  symm
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hrt.le hP
    (fun ρ hρ => by rw [hEq ρ ⟨hρ.1, hρ.2.le⟩]; exact hD ρ hρ) hRateI

end UnforcedLeray.Short.IIIa
