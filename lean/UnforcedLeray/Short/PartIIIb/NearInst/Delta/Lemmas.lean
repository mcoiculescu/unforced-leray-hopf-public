import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Defs
import UnforcedLeray.Short.PartIIIa.StressInputs

/-!
# The lemmas of the proof of `near:deltaN` (source 3956-4053)

Source of record: `the November 2 reference manuscript`.  One `Prop` per source
paragraph of the proof of `near:deltaN` (3927-3942), over the concrete objects of `NearInst.lean`,
`NearInst/Chart.lean` and `NearInst/Delta/Defs.lean` (no free predicates).  The assembly
`nearDeltaBoundC_of` is in `NearInst/Delta/Assembly.lean`.

The proof decomposes (`F ∈ Z`, `w = g⁻¹S_N g F`, `y = (S_N - S₀)gF`)
`G⁻¹(D_N - D₀)G F = G⁻¹(M_U - M₀)g w + G⁻¹M₀ y` (source 4036-4040), splits `M_U - M₀` into its thin
and broad output components (`fstZ`, `sndZ`) and `y` by the output partition
(`OutPartitionSum`): the young end `s < s₋`, the old end `s ≥ S`, the transverse tail and the bins
`[l_j, l_{j+1}) × {|η| ≤ L_⊥}`; on each bin the input is split into the complete block
`t < e^δ l_j` and the rest `t ≥ e^δ l_j` (`inRestr_below_add_above`).  Broad inputs `F₂` need no
separate estimate: every response bound below is on all of `Z`, where
`‖F₁ + F₂‖_{H_T} ≤ ‖F‖_Z` (source 3564-3565, `W ≥ 1`, `ρ_b ≤ 1`).

## Structural

* `OutPartitionSum` (3958-3977): the output regions partition the chart.

## Multipliers (2758-2778)

* `TrainMultRestr` : `‖G⁻¹M₀1_A g‖ ≤ 2 sup_A √s W|v_flat|`.
* `ThinDiffMult` : `‖G⁻¹ fst (M_U - M₀) g‖ ≤ 2 sup √s W|v - v_flat|` (4032-4034).
* `BroadMult` : `‖G⁻¹ snd (M_U - M₀) g‖ ≤ 2√ρ_b` when `√s|v_b| ≤ ρ_b` (2766-2769, 4045-4049).

## Coefficients (2703-2745)

* `RawStreamCompletion` : `√s W|v_raw - v_flat| ≤ P_ν ε` (2724-2726 the `ε` stream completion,
  4032-4034).
* `RepairCoeffBound` : `√s|v_b| ≤ ρ_b` (2706-2711, 2775).
* Reused (PartIII-a, `StressInputs.lean`): `RawCoeffEarly`, `RawCoeffLate`, `InletCoeffBounds`,
  `RawTransverseTail`; (`Targets.lean`) `FlatTrainMultBound`.

## Responses (3956-4031)

* `FlatFreeGainBound` : `‖g⁻¹S₀g‖_{Z→H} ≤ P_ν` (3420-3440 with `v = 0`, 3564-3565).
* `CompactWindowBlock` (paragraph 3956-3994) : the complete block on a bin,
  `≤ P_ν ε^{1/50-K(a+b)} e^{η_δ/ν}`.
* `PartialStripBlock` (paragraph 3996-4009) : the partial strip on a bin, `≤ P_ν ε^{1-b/2}e^{η_δ/ν}`.
* `YoungEndResponse`, `OldEndResponse` (paragraph 4011-4020) : the end regions, `≤ P_ν`.
* Reused (`Targets.lean`): `NearMaskedFreeBoundC` (4022-4030).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.Blueprint.Planar

/-! ## Structural -/

/-- **The output partition** (source 3958-3977: output end regions `s < s₋`, `s > S`, the window
`[s₋, S]` cut into bins `[l, r]` with `r/l < e^{δ/2}`, and the transverse box `|η| ≤ L_⊥`, outside
of which the train coefficient is small, 3965-3969).  For `0 < s₋ < S`, `δ > 0` and every `L`, the
regions `{s < s₋}`, `{s ≥ S}`, `tailSet s₋ S L` and the `N = binCount s₋ S δ` bins
`binSet l_j l_{j+1} L` (`l_j = binEdge s₋ S N j`, `l_0 = s₋`, `l_N = S`, increasing) partition the
chart, so the restrictions sum to the identity of `H`. -/
def OutPartitionSum : Prop :=
  ∀ (c sm S δ L : ℝ), 0 < sm → sm < S → 0 < δ → ∀ u : Hsp c,
    outRestr c (ageBelow sm) u + outRestr c (ageAbove S) u + outRestr c (tailSet sm S L) u +
      ∑ j ∈ Finset.range (binCount sm S δ),
        outRestr c (binSet (binEdge sm S (binCount sm S δ) j)
          (binEdge sm S (binCount sm S δ) (j + 1)) L) u = u

/-! ## Multipliers (source 2758-2778) -/

/-- **The restricted flat train multiplier** (source 2763-2775: `M₀u = (v⊗u + u⊗v, 0)`, "the
ratio of stress and velocity age densities is `s`", `|a⊗b + b⊗a| ≤ 2|a||b|`; 2777-2778: the bounds
hold after multiplication by a common positive age weight, here the gain).  If `M₀` is the flat
multiplier of the train `tr` and `√s W|v_flat| ≤ B` on the output region `A`, then
`‖G⁻¹M₀1_Ag‖_{H→Z} ≤ 2B` (`G⁻¹ ⋯ g` cancels pointwise: `M₀` acts in the age variable). -/
def TrainMultRestr : Prop :=
  ∀ (c mZ ρb γ ν : ℝ) (hν : 0 < ν) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (M : Hsp c →L[ℝ] Zsp c mZ ρb) (A : Set Chart) (B : ℝ),
    0 < c → MeasurableSet A → 0 ≤ B → IsFlatMult M tr →
    (∀ p ∈ A, 0 < p.1 →
      Real.sqrt p.1 * UnforcedLeray.Short.IIIa.transWeight mZ p * ‖trainMer tr p‖ ≤ B) →
    ‖gainRestrM γ hν A M‖ ≤ 2 * B

/-- **The thin coefficient difference as a multiplier** (source 4032-4040: `M_thin - M₀` is
multiplication by the difference of the exact thin coefficient `v = s^{-1/2}V` and the flat train;
2764-2775 for the multiplier norm).  If `M₀`, `M_U` have the flat and split pins and
`√s W|v - v_flat| ≤ B` for `s > 0`, then the thin component satisfies
`‖G⁻¹ fst(M_U - M₀) g‖_{H→Z} ≤ 2B`. -/
def ThinDiffMult : Prop :=
  ∀ (c mZ ρb γ ν R : ℝ) (hν : 0 < ν) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (V rb : ℝ → UnforcedLeray.SpatialField) (M0 MU : Hsp c →L[ℝ] Zsp c mZ ρb) (B : ℝ),
    0 < c → 0 ≤ B → IsFlatMult M0 tr → IsSplitMult MU R V rb →
    (∀ p : Chart, 0 < p.1 →
      Real.sqrt p.1 * UnforcedLeray.Short.IIIa.transWeight mZ p *
        ‖UnforcedLeray.Short.IIIa.chartCoeff R V p - trainMer tr p‖ ≤ B) →
    ‖gainConjM γ hν (fstZ c mZ ρb ∘L (MU - M0))‖ ≤ 2 * B

/-- **The broad repair coupling** (source 2766-2769, second bound of `stress-short:multiplier`:
`‖(M_U b)_2‖_{ρ_b^{-1/2}H_T} ≤ 2√ρ_b‖b‖_H`, from `√s v_b = r_b`, 2775-2776; 4045-4049).  If `M₀`,
`M_U` have the flat and split pins (the flat multiplier has zero second output) and
`√s|v_b| ≤ ρ_b` almost everywhere, then `‖G⁻¹ snd(M_U - M₀) g‖_{H→Z} ≤ 2√ρ_b`. -/
def BroadMult : Prop :=
  ∀ (c mZ ρb γ ν R : ℝ) (hν : 0 < ν) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (V rb : ℝ → UnforcedLeray.SpatialField) (M0 MU : Hsp c →L[ℝ] Zsp c mZ ρb),
    0 < c → 0 < ρb → IsFlatMult M0 tr → IsSplitMult MU R V rb →
    (∀ᵐ p ∂(ageμ c (-1 / 2)),
      Real.sqrt p.1 * ‖UnforcedLeray.Short.IIIa.chartCoeff R rb p‖ ≤ ρb) →
    ‖gainConjM γ hν (sndZ c mZ ρb ∘L (MU - M0))‖ ≤ 2 * Real.sqrt ρb

/-! ## Coefficients (source 2703-2745) -/

/-- **The stream completion** (source 2724-2726: "the stream completion `ε(1-η∂_η-2s∂_s)ψ` has
size `P_ν ε(1+s)^{-1/2}`", with the fixed weights of 2728-2729; 4032-4034).  The raw lift
`U_raw = √s[v₁e_r + (v₂ + εH)e_z]` (`Params.raw`, `Cons.C03.rawProfile`, `H = (1-η∂_η-2s∂_s)ψ`)
differs from the flat train only by `εH e_z`: for `m_Z > 3/2` there are `C, k, ν₀` with
`√s W|v_raw - v_flat| ≤ C ν^{-k} ε` for `s > 0` at every level of the regime with `ν ≤ ν₀`. -/
def RawStreamCompletion : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∀ mZ : ℝ, 3 / 2 < mZ → ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ pt : Chart, 0 < pt.1 →
        Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt *
          ‖UnforcedLeray.Short.IIIa.chartCoeff p.R p.raw pt - trainMer p.trainData pt‖ ≤
            C * p.ν⁻¹ ^ k * p.ε

/-- **The repair coefficient** (source 2706-2711: `sup_τ ‖r_b(τ)‖_∞ ≤ ρ_b`; 2775: `√s v_b = r_b`).
At every level of the regime with `ν ≤ ν₀` and every exact split, the chart coefficient
`v_b = chartCoeff R r_b` satisfies `√s|v_b| ≤ ρ_b` almost everywhere for `s^{-1/2}dς`. -/
def RepairCoeffBound : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ (ρb S_in : ℝ) (V rb : ℝ → UnforcedLeray.SpatialField),
        UnforcedLeray.Short.IIb.ExactSplitII p ρb S_in V rb →
        ∀ᵐ pt ∂(ageμ p.c (-1 / 2)),
          Real.sqrt pt.1 * ‖UnforcedLeray.Short.IIIa.chartCoeff p.R rb pt‖ ≤ ρb

/-! ## Responses (source 3956-4031) -/

/-- **The flat free response in the gain norm** (source 3420-3440, `eq:short-causal-bound` with
`v = 0`: `‖g⁻¹b‖_𝓗 ≤ Cν^{-M}‖g⁻¹F‖_𝒯`; 3564-3565: `‖F₁ + F₂‖_𝒯 ≤ ‖F₁‖_{Z₁} +
√ρ_b‖F₂‖_{ρ_b^{-1/2}𝒯}` for `W ≥ 1`; the flat map acts on the meridional block, 3569-3571).  For a
planar reference (gain exponent `γ = Re λ`), `K ⋐ (0, 1/4)` and `m_Z ≥ 0`: at every level of the
regime with `ν ≤ ν₀`, `0 < ρ_b ≤ 1` and `μ ∈ K`, `‖g⁻¹S₀g‖_{Z→H} ≤ C ν^{-k}`. -/
def FlatFreeGainBound : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ Kset : Set ℝ, IsCompact Kset →
    Kset ⊆ Ioo 0 (1 / 4) → ∀ mZ : ℝ, 0 ≤ mZ → ∀ dm dp : ℝ, 0 < dm →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ ρb : ℝ, 0 < ρb → ρb ≤ 1 → ∀ μ ∈ Kset, ∀ S0 : Zsp p.c mZ ρb →L[ℝ] Hsp p.c,
        IsFreeStress S0 p.ν μ → ‖gainConjS P.eigenvalue.re p.ν_pos S0‖ ≤ C * p.ν⁻¹ ^ k

/-- **The compact window: complete blocks** (source paragraph 3956-3994).  There is a fixed integer
`K` (chosen before `a, b`) such that for `a, b, δ` and every transverse constant `C_⊥`: at every
level of the regime with `ν ≤ ν₀`, `0 < ρ_b ≤ 1`, `μ ∈ K`, `S_N` with the masked pin at gap `δ`
and cut `S = ε^{-b}`, `S₀` with the free pin, and every bin `[l, r)` with `ε^a ≤ l < r ≤ e^{δ/2}l`,
`r ≤ S`, the complete block (output `l ≤ s < r`, `|η| ≤ L_⊥ = C_⊥(c/ν + √S + 1)`; input
`t < e^δ l`) satisfies
`‖g⁻¹1_{bin}(S_N - S₀)1_{t<e^δ l}g‖_{Z→H} ≤ C ν^{-k} ε^{1/50-K(a+b)} e^{η_δ/ν}`.
Route (source): on the complete block `S_far` vanishes (it only sees `t > e^δ s ≥ e^δ l`,
3908-3916), so the block is `1_{bin}(S_ε - S₀)1_{t<e^δ l}`; the gain costs `g(e^δ l)/g(l) ≤
e^{η_δ/ν}` (3978-3990, `GainRatioSup`, `GainRatioTanh`, `η_δ = γ tanh(3δ/8)`); the compact-output
comparison `‖χ(S_ε - S₀)‖_{H_T→H} ≤ CΓ^Kε^{1/50}` (3956-3961, `PartIIa.NearCompactFreeComparison`
in real form, with a smooth cutoff `χ = 1` on the bin box and `S₀` identified with the real form of
the `PartIIa` flat stress map) and `Γ^K ≤ P_ν ε^{-K(a+b)}` (3962-3967). -/
def CompactWindowBlock : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ Kset : Set ℝ, IsCompact Kset →
    Kset ⊆ Ioo 0 (1 / 4) → ∀ mZ : ℝ, 0 ≤ mZ → ∀ dm dp : ℝ, 0 < dm →
    ∃ K : ℕ, ∀ a b δ Cperp : ℝ, 0 < a → 0 < b → b < 1 → 0 < δ →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ ρb : ℝ, 0 < ρb → ρb ≤ 1 → ∀ μ ∈ Kset, ∀ SN S0 : Zsp p.c mZ ρb →L[ℝ] Hsp p.c,
        IsMaskedNear p μ δ (p.ε ^ (-b)) SN → IsFreeStress S0 p.ν μ →
        ∀ l r : ℝ, p.ε ^ a ≤ l → l < r → r ≤ Real.exp (δ / 2) * l → r ≤ p.ε ^ (-b) →
          ‖gainBlockS P.eigenvalue.re p.ν_pos
              (binSet l r (transL Cperp p.c p.ν (p.ε ^ (-b))))
              (ageBelow (Real.exp δ * l)) (SN - S0)‖ ≤
            C * p.ν⁻¹ ^ k *
              (p.ε ^ (1 / 50 - (K : ℝ) * (a + b)) *
                Real.exp (etaDelta P.eigenvalue.re δ / p.ν))

/-- **The partial strips** (source paragraph 3996-4009).  For `a, b, δ`: at every level of the
regime with `ν ≤ ν₀`, `0 < ρ_b ≤ 1`, `μ ∈ K`, the pinned `S_N`, `S₀`, every bin `[l, r)` with
`ε^a ≤ l < r ≤ e^{δ/2}l`, `r ≤ S = ε^{-b}` and every transverse box `L`, the inputs `t ≥ e^δ l`
on the bin satisfy `‖g⁻¹1_{bin}(S_N - S₀)1_{t≥e^δ l}g‖_{Z→H} ≤ C ν^{-k} ε^{1-b/2} e^{η_δ/ν}`.
Route (source): the flat causal inverse is zero there (`t ≥ e^δ l > r > s`, causality of the
zero-entrance solution, 3541-3545); `S_N = S_ε - S_far` keeps only `e^δ l ≤ t ≤ e^δ s` (the mask,
3908-3916), where the source radius is separated from the output radius by a fixed multiple of
`R/√r`; the heat-Leray kernel has the positive majorant `C|x|^{-4}` (`sep:kernel`,
`IIIa.SepKernelBounds`), whose `L¹` norm outside distance `d` is `C/d`; the dilation integral has
power `λ^{2Re μ+1/2}`; Young (`sep:young`) and normalized-phase Minkowski give `P_ν ε √r`
(3996-4005); the gain ratio on `t/s ≤ e^{3δ/2}` is `e^{η_δ/ν}` and `√r ≤ ε^{-b/2}` (4006-4007). -/
def PartialStripBlock : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ Kset : Set ℝ, IsCompact Kset →
    Kset ⊆ Ioo 0 (1 / 4) → ∀ mZ : ℝ, 0 ≤ mZ → ∀ dm dp : ℝ, 0 < dm →
    ∀ a b δ : ℝ, 0 < a → 0 < b → b < 1 → 0 < δ →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ ρb : ℝ, 0 < ρb → ρb ≤ 1 → ∀ μ ∈ Kset, ∀ SN S0 : Zsp p.c mZ ρb →L[ℝ] Hsp p.c,
        IsMaskedNear p μ δ (p.ε ^ (-b)) SN → IsFreeStress S0 p.ν μ →
        ∀ l r L : ℝ, p.ε ^ a ≤ l → l < r → r ≤ Real.exp (δ / 2) * l → r ≤ p.ε ^ (-b) →
          ‖gainBlockS P.eigenvalue.re p.ν_pos (binSet l r L) (ageAbove (Real.exp δ * l))
              (SN - S0)‖ ≤
            C * p.ν⁻¹ ^ k *
              (p.ε ^ (1 - b / 2) * Real.exp (etaDelta P.eigenvalue.re δ / p.ν))

/-- **The young end** (source 4011-4015).  For `a, b, δ`: at every level of the regime with
`ν ≤ ν₀`, `0 < ρ_b ≤ 1`, `μ ∈ K` and the pinned `S_N`, `S₀`, the output region `s < s₋ = ε^a`
satisfies `‖g⁻¹1_{s<s₋}(S_N - S₀)g‖_{Z→H} ≤ C ν^{-k}`.  Route (source): retained inputs have
`t < e^δ s₋` (the mask), where the gain ratio is `≤ e^{γe^δ s₋} = 1 + o(1)`; the forbidden
separated subblock `1_{s<s₋}S_far1_{t<e^δ s₋}` costs `P_ν ε √s₋` by the positive-kernel estimate of
`PartialStripBlock`; `S_ε` and `S₀` are bounded by the free energy (`PartIIa.NearStressMapExists`,
`FlatFreeGainBound`, `S₀` causal). -/
def YoungEndResponse : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ Kset : Set ℝ, IsCompact Kset →
    Kset ⊆ Ioo 0 (1 / 4) → ∀ mZ : ℝ, 0 ≤ mZ → ∀ dm dp : ℝ, 0 < dm →
    ∀ a b δ : ℝ, 0 < a → 0 < b → b < 1 → 0 < δ →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ ρb : ℝ, 0 < ρb → ρb ≤ 1 → ∀ μ ∈ Kset, ∀ SN S0 : Zsp p.c mZ ρb →L[ℝ] Hsp p.c,
        IsMaskedNear p μ δ (p.ε ^ (-b)) SN → IsFreeStress S0 p.ν μ →
          ‖gainRestrS P.eigenvalue.re p.ν_pos (ageBelow (p.ε ^ a)) (SN - S0)‖ ≤ C * p.ν⁻¹ ^ k

/-- **The old end** (source 4015-4020).  For `b, δ`: at every level of the regime with `ν ≤ ν₀`,
`0 < ρ_b ≤ 1`, `μ ∈ K` and the pinned `S_N`, `S₀`, the output region `s ≥ S = ε^{-b}` satisfies
`‖g⁻¹1_{s≥S}(S_N - S₀)g‖_{Z→H} ≤ C ν^{-k}`.  Route (source): there `S_far = 0` (`IsFarMask` has the
factor `1_{s<S}`), so `S_N = S_ε` ("use the full free inverse"); the gain ratio is at most
`e^{γ/ν}/g(S) = exp{γ/[ν(1+νS)]} = 1 + o(1)` (4016-4018) since `νS = νe^{bd/ν} → ∞`; `S_ε`, `S₀` are
bounded by the free energy. -/
def OldEndResponse : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ Kset : Set ℝ, IsCompact Kset →
    Kset ⊆ Ioo 0 (1 / 4) → ∀ mZ : ℝ, 0 ≤ mZ → ∀ dm dp : ℝ, 0 < dm →
    ∀ b δ : ℝ, 0 < b → b < 1 → 0 < δ →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ ρb : ℝ, 0 < ρb → ρb ≤ 1 → ∀ μ ∈ Kset, ∀ SN S0 : Zsp p.c mZ ρb →L[ℝ] Hsp p.c,
        IsMaskedNear p μ δ (p.ε ^ (-b)) SN → IsFreeStress S0 p.ν μ →
          ‖gainRestrS P.eigenvalue.re p.ν_pos (ageAbove (p.ε ^ (-b))) (SN - S0)‖ ≤
            C * p.ν⁻¹ ^ k

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
