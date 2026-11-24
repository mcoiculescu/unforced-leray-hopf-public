import UnforcedLeray.Short.Spine.Sub.SP_CAN4_5
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.PointwiseEquation.DClassical.IntByParts
import UnforcedLeray.Lib.PlanarSpectralB.AdjointDomain
import UnforcedLeray.Cons.L2.CanonicalBranch.CanonicalRadialOscillator

/-!
# Spine: `DClassicalAe` cut into its leaf statements (task `Spine:SP-CAN/4/5/3`)

Target (`Short/Spine/Sub/SP_CAN4_5.lean`): `DClassicalAe`. If `u ∈ 𝒟(D)` has a representative `g`
that is `C^∞` on `(0, ∞)`, then `oscillatorD g =ᵐ[xGMeasure] D u`.

Source of record: `the November 2 reference manuscript` line 1086 ("smooth for
positive `θ`", so the equation is used pointwise) and lines 1134-1140 (conjugation by `G^{1/2}`
turns `D` into a shifted harmonic oscillator); the classical formula `D = Δ + ½ y·∇ + 2` in the old
manuscript `paper/main.tex` 1879-1888 (read only).



* `DClassicalAux.weighted_fundamental` (`WeightedFund.lean`): the fundamental lemma on `(0, ∞)`
  for the weight `w r = 4π e^{r²/4} r`;
* `DClassicalAux.oscillatorD_ibp` (`IntByParts.lean`): the weighted integration by parts
  `∫ (oscillatorD ψ) g w = ∫ ψ (oscillatorD g) w` for `ψ` smooth with support in `[a, b] ⊂ (0, ∞)`
  and `g` smooth on `(0, ∞)`;
* `B0094.D_symm` (library): `⟪D x, y⟫ = ⟪x, D y⟫` on `𝒟(D)`.

## The cut

* `TestBeta`, `TestBetaDerivBound`, `TestMemLp`: three elementary facts about a smooth test
  function `ψ` supported in `[a, b] ⊂ (0, ∞)`;
* `TestDAction`: such a `ψ` lies in `𝒟(D)` and `D ψ =ᵐ oscillatorD ψ`. It follows from the three
  previous facts and the library (`testDAction_of`, proved below);
* `ConjOscillatorD`: `oscillatorD` has real coefficients;
* `IntegralXGEq`: the `xGMeasure` integral is the weighted Lebesgue integral;
* `LocIntXGMulW`: `v w` is locally integrable on `(0, ∞)` for `v ∈ X_G`.

`dClassicalAe_of` is the assembly (test-function argument).

Status: nothing here is proved except the two assemblies `testDAction_of` and `dClassicalAe_of`.
No `sorry`, `admit`, `axiom` or `native_decide`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology InnerProductSpace

namespace UnforcedLeray.Short.Spine

open UnforcedLeray.B0010 Blueprint.Planar ComplexODEC UnforcedLeray.Cons.C01
open UnforcedLeray.Cons.G3b
open UnforcedLeray.Short.Spine.DClassicalAux

/-- **Leaf 1, the radial-square profile of a test function.** A smooth `ψ` vanishing on
`(-∞, a)` and `(b, ∞)` with `0 < a` is `ψ(r) = r² β(r²)` on `(0, ∞)` with `β` smooth on `ℝ` and
vanishing on `(-∞, a²)` and `(b², ∞)`.

Proof: `β s = ψ(√s)/s` for `s > 0` and `β s = 0` for `s ≤ 0`. `β` is smooth on `(0, ∞)`
(composition and quotient) and is `0` on the open set `(-∞, a²)`, which contains every `s ≤ 0`;
these two open sets cover `ℝ`, so `β` is `C^∞` (`contDiff_iff_contDiffAt`). For `r > 0`,
`r² β(r²) = r² ψ(r)/r² = ψ(r)`. For `s < a²`, `√s < a` so `ψ(√s) = 0`; for `s > b²`, `√s > b`. -/
def TestBeta : Prop :=
  ∀ (ψ : ℝ → ℂ), ContDiff ℝ ∞ ψ → ∀ a b : ℝ, 0 < a →
    (∀ r : ℝ, r < a → ψ r = 0) → (∀ r : ℝ, b < r → ψ r = 0) →
    ∃ β : ℝ → ℂ, ContDiff ℝ ∞ β ∧ (∀ r : ℝ, 0 < r → ψ r = (r : ℂ) ^ 2 * β (r ^ 2)) ∧
      (∀ s : ℝ, s < a ^ 2 → β s = 0) ∧ (∀ s : ℝ, b ^ 2 < s → β s = 0)

/-- **Leaf 2, the Gaussian derivative bound for a compactly supported `β`.** A smooth `β`
vanishing on `(-∞, A)` and `(B, ∞)` satisfies `DerivBound (s ↦ e^{-s/4}) [0, ∞) β`
(`Lib/ComplexODEC/Bounds.lean`: every `iteratedDeriv m β` is bounded by `C (1+|s|)^N e^{-s/4}`
on `[0, ∞)`).

Proof: `iteratedDeriv m β` is continuous (`ContDiff.continuous_iteratedDeriv`) and vanishes off
`[A, B]` (`β` is eventually `0` there: `Filter.EventuallyEq.iteratedDeriv_eq`), so it is bounded
by some `M` (`IsCompact.exists_bound_of_continuousOn` on `Icc A B`). For `s ∈ [0, B]`,
`e^{-s/4} ≥ e^{-B/4}`, so `M ≤ (M e^{|B|/4}) e^{-s/4}`; take `N = 0`, `C = M e^{|B|/4}`. -/
def TestBetaDerivBound : Prop :=
  ∀ (β : ℝ → ℂ), ContDiff ℝ ∞ β → ∀ A B : ℝ,
    (∀ s : ℝ, s < A → β s = 0) → (∀ s : ℝ, B < s → β s = 0) →
    DerivBound (fun s => Real.exp ((-1 / 4) * s)) (Ici 0) β

/-- **Leaf 3, a continuous function supported in `[a, b]` is in `L²(xGMeasure)`.**

Proof: `ψ` is bounded by `M` on `[a, b]` and zero elsewhere; `xGMeasure` of a bounded set is
finite (`B0010.xGMeasure_apply`, the density `4π e^{r²/4} r` is bounded on bounded sets), so
`∫ ‖ψ‖² dxGMeasure ≤ M² xGMeasure (Icc 0 b) < ∞`. Use `memLp_two_iff_integrable_sq_norm` or
`MemLp.of_bound` with `IsFiniteMeasure` on the restricted measure
`xGMeasure.restrict (Icc (min a 0) (max b 0))`, and `memLp_of_...ae_eq_zero` off the interval. -/
def TestMemLp : Prop :=
  ∀ (ψ : ℝ → ℂ), Continuous ψ → ∀ a b : ℝ,
    (∀ r : ℝ, r < a → ψ r = 0) → (∀ r : ℝ, b < r → ψ r = 0) →
    MemLp ψ 2 xGMeasure

/-- **Leaf 4, the action of `D` on a test function** (`eq:st18-t00011` of the old manuscript,
`paper/main.tex` 1879-1888; the same pattern as
`PlanarSpectral.exists_modeVort_Ddomain_action`). A smooth `ψ` vanishing on `(-∞, a)` and `(b, ∞)`
with `0 < a` defines an element of `𝒟(D)` whose image is `oscillatorD ψ` a.e. It is proved from
`TestBeta`, `TestBetaDerivBound`, `TestMemLp` by `testDAction_of` below. -/
def TestDAction : Prop :=
  ∀ (ψ : ℝ → ℂ), ContDiff ℝ ∞ ψ → ∀ a b : ℝ, 0 < a →
    (∀ r : ℝ, r < a → ψ r = 0) → (∀ r : ℝ, b < r → ψ r = 0) →
    ∃ hm : MemLp ψ 2 xGMeasure, ∃ hd : hm.toLp ψ ∈ B0094.D.domain,
      (⇑(B0094.D ⟨hm.toLp ψ, hd⟩) : ℝ → ℂ) =ᵐ[xGMeasure] oscillatorD ψ

/-- **Leaf 5, `oscillatorD` of a real function is real.** For `ψ : ℝ → ℝ` smooth, viewed as a
complex function, `conj (oscillatorD ψ r) = oscillatorD ψ r` for every `r` (all coefficients of
`oscillatorD` are real; for `r = 0` the divisions by `0` give `0`).

Proof: `deriv (fun s => (ψ s : ℂ)) = fun s => (deriv ψ s : ℂ)` (`HasDerivAt.ofReal_comp`), twice,
using that `ψ` and `deriv ψ` are differentiable (`ContDiff.differentiable`,
`contDiff_infty_iff_deriv`); then `Complex.conj_ofReal`, `map_add`, `map_mul`, `map_div₀`. -/
def ConjOscillatorD : Prop :=
  ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → ∀ r : ℝ,
    starRingEnd ℂ (oscillatorD (fun s => (ψ s : ℂ)) r) = oscillatorD (fun s => (ψ s : ℂ)) r

/-- **Leaf 6, the `xGMeasure` integral as a weighted Lebesgue integral.** For `F` vanishing on
`(-∞, a)` and `(b, ∞)` with `0 < a`: `∫ F dxGMeasure = ∫ w F dr`, `w = 4π e^{r²/4} r`
(`DClassicalAux.wC`).

Proof: `xGMeasure = (volume.restrict (Ioi 0)).withDensity (xGDensity)` with `xGDensity` the
`ℝ≥0`-valued density (`B0010.xGMeasure`), so `integral_withDensity_eq_integral_smul`
(`B0010.measurable_xGDensity`) gives `∫ F dxG = ∫_{Ioi 0} xGDensity r • F r`; by
`B0010.xGDensity_eq` and positivity of `r ↦ 4π e^{r²/4} r` on `Ioi 0`, `xGDensity r = wDens r`
there; finally `F = 0` off `Ioi 0` (as `a > 0`), so
`setIntegral_eq_integral_of_forall_compl_eq_zero` turns the set integral into the integral over `ℝ`. -/
def IntegralXGEq : Prop :=
  ∀ (F : ℝ → ℂ) (a b : ℝ), 0 < a → (∀ r : ℝ, r < a → F r = 0) → (∀ r : ℝ, b < r → F r = 0) →
    ∫ r, F r ∂xGMeasure = ∫ r, wC r * F r

/-- **Leaf 7, `v w` is locally integrable on `(0, ∞)` for `v ∈ X_G`.**

Proof: for a compact `K ⊆ (0, ∞)`, `∫_K ‖v‖ w dr = ∫_K ‖v‖ dxGMeasure` (as in `IntegralXGEq`, but
for the restricted measure; `xGMeasure` has density `w` on `(0, ∞)` and `w` is bounded above and
below on `K`) and `‖v‖ ∈ L²(xGMeasure) ⊆ L¹(xGMeasure.restrict K)` because `xGMeasure K < ∞`
(`MemLp.integrable` for a finite measure, `B0010.xGMeasure_apply`). Equivalently: on a compact
`K ⊆ Ioi 0` the weight `w` is bounded below by `c > 0`, so `Integrable (v w) (volume.restrict K)`
follows from `Integrable v (xGMeasure.restrict K)` and `c ≤ w`
(`integrable_withDensity_iff_integrable_smul`). The function `v` is `xGMeasure`-a.e. strongly
measurable, hence `volume.restrict (Ioi 0)`-a.e. strongly measurable by `B0012.restrict_ac`
(`volume.restrict (Ioi 0) ≪ xGMeasure`, `AbsolutelyContinuous.aestronglyMeasurable`... or
`AEStronglyMeasurable.mono_ac`). -/
def LocIntXGMulW : Prop :=
  ∀ v : XG, LocallyIntegrableOn (fun r : ℝ => (v : ℝ → ℂ) r * wC r) (Ioi 0)

/-- `T1` from its three elementary facts and the library (the same pattern as
`PlanarSpectral.exists_modeVort_Ddomain_action`). -/
theorem testDAction_of (h1 : TestBeta) (h2 : TestBetaDerivBound) (h3 : TestMemLp) :
    TestDAction := by
  intro ψ hψ a b ha hψa hψb
  obtain ⟨β, hβ, hψβ, hβa, hβb⟩ := h1 ψ hψ a b ha hψa hψb
  have hdb : DerivBound (fun s => Real.exp ((-1 / 4) * s)) (Ici 0) β :=
    h2 β hβ (a ^ 2) (b ^ 2) hβa hβb
  have hmem : MemLp ψ 2 xGMeasure := h3 ψ hψ.continuous a b hψa hψb
  have hfg : ψ =ᵐ[xGMeasure] (fun r : ℝ => (r : ℂ) ^ 2 * β (r ^ 2)) := by
    filter_upwards [B0012.ae_xG_pos] with r hr
    exact hψβ r hr
  obtain ⟨hD, DF, hDact, df, hfield, hDFae⟩ :=
    PlanarSpectral.exists_Ddomain_of_gaussClass_profile_ae hfg
      (PlanarSpectral.gaussClass_angularTwo_of_derivBound hβ hdb)
      (PlanarSpectral.isAngularTwo_angularTwoField_radialSq β) hmem
  refine ⟨hmem, hD, ?_⟩
  rw [hDact]
  have hgauss := PlanarSpectral.gaussianOperator_angularTwoField_radialSq hβ
  have hprofile : B0010.angularTwoField df =
      B0010.angularTwoField (fun r : ℝ => (r : ℂ) ^ 2 *
        (4 * (r ^ 2 : ℝ) * deriv (deriv β) (r ^ 2) +
          ((r ^ 2 + 12 : ℝ) : ℂ) * deriv β (r ^ 2) + 3 * β (r ^ 2))) := by
    rw [hfield, hgauss]
  have hEq : EqOn ψ (fun x : ℝ => (x : ℂ) ^ 2 * β (x ^ 2)) (Ioi 0) := fun x hx => hψβ x hx
  filter_upwards [hDFae, B0012.ae_xG_pos] with r hdf hr
  have h := congrFun hprofile (r, 0)
  rw [B0010.angularTwoField_profile df hr, B0010.angularTwoField_profile _ hr] at h
  have hd1 : deriv ψ r = deriv (fun x : ℝ => (x : ℂ) ^ 2 * β (x ^ 2)) r := by
    simpa only [iteratedDeriv_one] using (hEq.iteratedDeriv_of_isOpen isOpen_Ioi 1) hr
  have hd2 : deriv (deriv ψ) r =
      deriv (deriv (fun x : ℝ => (x : ℂ) ^ 2 * β (x ^ 2))) r := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using
      (hEq.iteratedDeriv_of_isOpen isOpen_Ioi 2) hr
  have hosc : oscillatorD ψ r = oscillatorD (fun x : ℝ => (x : ℂ) ^ 2 * β (x ^ 2)) r := by
    unfold oscillatorD
    rw [hEq hr, hd1, hd2]
  rw [hdf, h, hosc, oscillatorD_radialSq hβ hr.ne']

/-- A function that is integrable on `[a, b]` and zero off it is integrable. -/
theorem integrable_of_zero_off_Icc {f : ℝ → ℂ} {a b : ℝ} (hf : IntegrableOn f (Icc a b))
    (h0 : ∀ r : ℝ, r ∉ Icc a b → f r = 0) : Integrable f := by
  have hsupp : Function.support f ⊆ Icc a b := by
    intro r hr
    by_contra hnot
    exact hr (h0 r hnot)
  exact (integrableOn_iff_integrable_of_support_subset hsupp).1 hf

/-- Complement of `Icc a b`. -/
theorem lt_or_lt_of_notMem_Icc {r a b : ℝ} (h : r ∉ Icc a b) : r < a ∨ b < r := by
  by_contra hc
  rw [not_or, not_lt, not_lt] at hc
  exact h ⟨hc.1, hc.2⟩

/-- A compactly supported real function with support in `(0, ∞)` vanishes outside `[a, b]`, with
`0 < a < b`. -/
theorem exists_Icc_of_compactSupport {ψ : ℝ → ℝ} (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ Ioi 0) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ (∀ r : ℝ, r < a → ψ r = 0) ∧ (∀ r : ℝ, b < r → ψ r = 0) := by
  have hcpt : IsCompact (tsupport ψ) := hc
  obtain ⟨a, ha, hmin⟩ := hcpt.exists_forall_le' (f := fun x : ℝ => x) (a := (0 : ℝ))
    (continuousOn_id' _) (fun x hx => hs hx)
  obtain ⟨b, hb⟩ := hcpt.bddAbove
  refine ⟨a, max b (a + 1), ha, lt_of_lt_of_le (lt_add_one a) (le_max_right _ _),
    fun r hr => ?_, fun r hr => ?_⟩
  · by_contra hne
    have hmem : r ∈ tsupport ψ := subset_tsupport _ (Function.mem_support.2 hne)
    have h' : a ≤ r := hmin r hmem
    linarith
  · by_contra hne
    have hmem : r ∈ tsupport ψ := subset_tsupport _ (Function.mem_support.2 hne)
    have h1 := hb hmem
    have h2 : b < r := lt_of_le_of_lt (le_max_left _ _) hr
    linarith

/-- **`DClassicalAe` from its leaf statements** (test-function argument). -/
theorem dClassicalAe_of (h1 : TestDAction) (h2 : ConjOscillatorD) (h3 : IntegralXGEq)
    (h4 : LocIntXGMulW) (h5 : SmoothnessFacts) : DClassicalAe := by
  intro u hu g hgu hg
  set Du : XG := B0094.D ⟨u, hu⟩ with hDu
  have hloc : LocallyIntegrableOn
      (fun r : ℝ => (oscillatorD g r - (Du : ℝ → ℂ) r) * (wDens r : ℂ)) (Ioi 0) := by
    have hA : LocallyIntegrableOn (fun r : ℝ => oscillatorD g r * wC r) (Ioi 0) :=
      ((h5.2 g hg).mul continuous_wC.continuousOn).locallyIntegrableOn measurableSet_Ioi
    have hB := h4 Du
    have e : (fun r : ℝ => (oscillatorD g r - (Du : ℝ → ℂ) r) * (wDens r : ℂ)) =
        (fun r : ℝ => oscillatorD g r * wC r) - (fun r : ℝ => (Du : ℝ → ℂ) r * wC r) := by
      funext r
      simp only [Pi.sub_apply, wC, sub_mul]
    rw [e]
    exact hA.sub hB
  have hzero : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ioi 0 →
      ∫ r, ψ r • ((oscillatorD g r - (Du : ℝ → ℂ) r) * (wDens r : ℂ)) = 0 := by
    intro ψ hψ hψc hψs
    obtain ⟨a, b, ha, hab, hψa, hψb⟩ := exists_Icc_of_compactSupport hψc hψs
    set ψC : ℝ → ℂ := fun r => (ψ r : ℂ) with hψC
    have hψCs : ContDiff ℝ ∞ ψC := Complex.ofRealCLM.contDiff.comp hψ
    have hψCa : ∀ r : ℝ, r < a → ψC r = 0 := fun r hr => by simp [hψC, hψa r hr]
    have hψCb : ∀ r : ℝ, b < r → ψC r = 0 := fun r hr => by simp [hψC, hψb r hr]
    obtain ⟨hm, hd, hDae⟩ := h1 ψC hψCs a b ha hψCa hψCb
    set Ψ : XG := hm.toLp ψC with hΨ
    have hΨae : (Ψ : ℝ → ℂ) =ᵐ[xGMeasure] ψC := hm.coeFn_toLp
    have hDΨ : (⇑(B0094.D ⟨Ψ, hd⟩) : ℝ → ℂ) =ᵐ[xGMeasure] oscillatorD ψC := hDae
    -- `oscillatorD ψC` vanishes off `[a, b]`
    have hEz : ∀ r : ℝ, (r < a ∨ b < r) → oscillatorD ψC r = 0 := by
      intro r hr
      apply oscillatorD_eq_zero_of_eventually
      rcases hr with hr | hr
      · exact Filter.eventuallyEq_of_mem (isOpen_Iio.mem_nhds hr) (fun x hx => hψCa x hx)
      · exact Filter.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hr) (fun x hx => hψCb x hx)
    -- weighted integration by parts
    have hibp := oscillatorD_ibp hψCs hg ha hab hψCa hψCb
    -- transfer of the two pairings to `xGMeasure`
    have hX1 : ∫ r, oscillatorD ψC r * g r ∂xGMeasure =
        ∫ r, wC r * (oscillatorD ψC r * g r) :=
      h3 (fun r => oscillatorD ψC r * g r) a b ha
        (fun r hr => by simp only [hEz r (Or.inl hr), zero_mul])
        (fun r hr => by simp only [hEz r (Or.inr hr), zero_mul])
    have hX2 : ∫ r, ψC r * (Du : ℝ → ℂ) r ∂xGMeasure =
        ∫ r, wC r * (ψC r * (Du : ℝ → ℂ) r) :=
      h3 (fun r => ψC r * (Du : ℝ → ℂ) r) a b ha
        (fun r hr => by simp only [hψCa r hr, zero_mul])
        (fun r hr => by simp only [hψCb r hr, zero_mul])
    -- the two inner products
    have hinner1 : inner ℂ (B0094.D ⟨Ψ, hd⟩) u = ∫ r, oscillatorD ψC r * u r ∂xGMeasure := by
      rw [MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hDΨ] with r hr
      rw [RCLike.inner_apply', hr]
      have hc : starRingEnd ℂ (oscillatorD ψC r) = oscillatorD ψC r := h2 ψ hψ r
      rw [hc]
    have hinner2 : inner ℂ Ψ Du = ∫ r, ψC r * (Du : ℝ → ℂ) r ∂xGMeasure := by
      rw [MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hΨae] with r hr
      rw [RCLike.inner_apply', hr]
      have hc : starRingEnd ℂ (ψC r) = ψC r := Complex.conj_ofReal (ψ r)
      rw [hc]
    have hsymm : inner ℂ (B0094.D ⟨Ψ, hd⟩) u = inner ℂ Ψ Du :=
      B0094.D_symm ⟨Ψ, hd⟩ ⟨u, hu⟩
    -- the two weighted integrals agree
    have hA : ∫ r, ψC r * oscillatorD g r * wC r = ∫ r, oscillatorD ψC r * u r ∂xGMeasure := by
      rw [← hibp]
      have e1 : (fun r => oscillatorD ψC r * g r * wC r) =
          fun r => wC r * (oscillatorD ψC r * g r) := funext fun r => by ring
      rw [e1, ← hX1]
      refine integral_congr_ae ?_
      filter_upwards [hgu] with r hr
      rw [hr]
    have hB : ∫ r, ψC r * (Du : ℝ → ℂ) r * wC r = ∫ r, ψC r * (Du : ℝ → ℂ) r ∂xGMeasure := by
      rw [hX2]
      refine integral_congr_ae (Eventually.of_forall fun r => ?_)
      ring
    have hAB : ∫ r, ψC r * oscillatorD g r * wC r = ∫ r, ψC r * (Du : ℝ → ℂ) r * wC r := by
      rw [hA, hB, ← hinner1, hsymm, hinner2]
    -- integrability of the two pieces
    have hint1 : Integrable (fun r : ℝ => ψC r * oscillatorD g r * wC r) := by
      have hcont : ContinuousOn (fun r : ℝ => ψC r * oscillatorD g r * wC r) (Icc a b) := by
        have h2c : ContinuousOn (oscillatorD g) (Icc a b) :=
          (h5.2 g hg).mono (fun r hr => lt_of_lt_of_le ha hr.1)
        exact (hψCs.continuous.continuousOn.mul h2c).mul continuous_wC.continuousOn
      refine integrable_of_zero_off_Icc hcont.integrableOn_Icc (fun r hr => ?_)
      rcases lt_or_lt_of_notMem_Icc hr with h | h
      · simp only [hψCa r h, zero_mul]
      · simp only [hψCb r h, zero_mul]
    have hint2 : Integrable (fun r : ℝ => ψC r * (Du : ℝ → ℂ) r * wC r) := by
      have hK : IntegrableOn (fun r : ℝ => (Du : ℝ → ℂ) r * wC r) (Icc a b) :=
        (h4 Du).integrableOn_compact_subset (fun r hr => lt_of_lt_of_le ha hr.1) isCompact_Icc
      have hK2 : IntegrableOn (fun r : ℝ => ψC r * ((Du : ℝ → ℂ) r * wC r)) (Icc a b) :=
        IntegrableOn.continuousOn_mul hψCs.continuous.continuousOn hK isCompact_Icc
      have hK3 : IntegrableOn (fun r : ℝ => ψC r * (Du : ℝ → ℂ) r * wC r) (Icc a b) :=
        hK2.congr_fun (fun r _ => (mul_assoc _ _ _).symm) measurableSet_Icc
      refine integrable_of_zero_off_Icc hK3 (fun r hr => ?_)
      rcases lt_or_lt_of_notMem_Icc hr with h | h
      · simp only [hψCa r h, zero_mul]
      · simp only [hψCb r h, zero_mul]
    -- conclusion
    have hpt : (fun r : ℝ => ψ r • ((oscillatorD g r - (Du : ℝ → ℂ) r) * (wDens r : ℂ))) =
        fun r : ℝ => ψC r * oscillatorD g r * wC r - ψC r * (Du : ℝ → ℂ) r * wC r := by
      funext r
      simp only [Complex.real_smul, hψC, wC]
      ring
    rw [hpt, integral_sub hint1 hint2, hAB, sub_self]
  have hfund := weighted_fundamental (fun r => oscillatorD g r - (Du : ℝ → ℂ) r) hloc hzero
  filter_upwards [hfund] with r hr
  have hr' : oscillatorD g r - (Du : ℝ → ℂ) r = 0 := hr
  exact sub_eq_zero.mp hr'

end UnforcedLeray.Short.Spine
