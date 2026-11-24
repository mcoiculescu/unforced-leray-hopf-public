import UnforcedLeray.Lib.Sobolev.WeakDeriv
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Weights and unweighted test pairings on weighted `L^p` (INF11 target S2, first part)

Scoping note `INF11-INF14-Sobolev.md` §5.0, §5.1 (S2) and Risk 3 of §6 ("The defining
functionals use the *unweighted* integral on a *weighted* L^p").

The manuscript's weighted spaces are `X_m = L²(ρ_ℓ^m dq dη)` with an unweighted
distribution pairing (tex 13876–13886), and the cylinder weights are smooth, periodic,
uniformly comparable to `1 + q² + η²` and do not vanish at the seams (tex 13876–13879,
4573–4577). A `Weight E` is a measurable, pointwise positive function that is bounded above
and below by positive constants on every compact set. This covers every weight of the
manuscript (`⟨y⟩^{2M}`, `G^{-1}`, `ρ_ℓ^{±m}`, `ρ_w`, and the centred seam weight `ρ_c`, which is
not continuous across the seam but is locally bounded) and is exactly what makes the
unweighted pairing `f ↦ ∫ ψ f dμ` continuous on `L^p(ρ dμ)` for a bounded `ψ` with compact
support: `∫ ψ f dμ = ∫ (ψ/ρ) f ρ dμ` and `ψ/ρ ∈ L^{p'}(ρ dμ)`.

## Main declarations
* `Sob.Weight E`, with `1`, products, real powers and `Weight.ofContinuous`;
* `Sob.wμ μ ρ = ρ dμ` (`withDensity`), `wμ_one`, `wμ_ac : wμ μ ρ ≪ μ`, `ac_wμ : μ ≪ wμ μ ρ`;
* `Sob.CompactlyBounded μ ψ`: measurable, bounded on a compact `K`, zero `μ`-a.e. off `K`;
* `integrable_smul_of_memLp`: `ψ • f ∈ L¹(μ)` for `f ∈ L^p(ρ dμ)`;
* `locallyIntegrable_of_memLp`: `L^p(ρ dμ) ⊂ L¹_loc(μ)`;
* `testPair μ ρ ψ hψ : Lp F p (wμ μ ρ) →L[𝕜] F`, `testPair_apply : … = ∫ x, ψ x • f x ∂μ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace UnforcedLeray.Sob

/-! ### Weights -/

/-- An admissible weight: measurable, positive, and on every compact set bounded above and
below by positive constants. -/
structure Weight (E : Type*) [TopologicalSpace E] [MeasurableSpace E] where
  toFun : E → ℝ
  measurable : Measurable toFun
  pos : ∀ x, 0 < toFun x
  locBdd : ∀ K : Set E, IsCompact K → ∃ a b : ℝ, 0 < a ∧ ∀ x ∈ K, a ≤ toFun x ∧ toFun x ≤ b

namespace Weight

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E]

instance : CoeFun (Weight E) (fun _ => E → ℝ) := ⟨Weight.toFun⟩

@[ext] theorem ext {ρ σ : Weight E} (h : ∀ x, ρ x = σ x) : ρ = σ := by
  cases ρ; cases σ; congr; funext x; exact h x

/-- The constant weight `1`. -/
instance : One (Weight E) :=
  ⟨⟨fun _ => 1, measurable_const, fun _ => one_pos,
    fun _ _ => ⟨1, 1, one_pos, fun _ _ => ⟨le_rfl, le_rfl⟩⟩⟩⟩

@[simp] theorem one_apply (x : E) : (1 : Weight E) x = 1 := rfl

/-- A continuous positive function is a weight. -/
def ofContinuous [OpensMeasurableSpace E] (ρ : E → ℝ) (hc : Continuous ρ)
    (hpos : ∀ x, 0 < ρ x) : Weight E where
  toFun := ρ
  measurable := hc.measurable
  pos := hpos
  locBdd K hK := by
    rcases K.eq_empty_or_nonempty with rfl | hne
    · exact ⟨1, 1, one_pos, fun x hx => absurd hx (Set.notMem_empty x)⟩
    obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hne hc.continuousOn
    obtain ⟨x₁, hx₁, hmax⟩ := hK.exists_isMaxOn hne hc.continuousOn
    exact ⟨ρ x₀, ρ x₁, hpos x₀, fun x hx => ⟨hmin hx, hmax hx⟩⟩

@[simp] theorem ofContinuous_apply [OpensMeasurableSpace E] (ρ : E → ℝ) (hc : Continuous ρ)
    (hpos : ∀ x, 0 < ρ x) (x : E) : ofContinuous ρ hc hpos x = ρ x := rfl

/-- The product of two weights. -/
instance : Mul (Weight E) :=
  ⟨fun ρ σ => ⟨fun x => ρ x * σ x, ρ.measurable.mul σ.measurable,
    fun x => mul_pos (ρ.pos x) (σ.pos x), fun K hK => by
      obtain ⟨a, b, ha, hab⟩ := ρ.locBdd K hK
      obtain ⟨a', b', ha', hab'⟩ := σ.locBdd K hK
      refine ⟨a * a', b * b', mul_pos ha ha', fun x hx => ⟨?_, ?_⟩⟩
      · exact mul_le_mul (hab x hx).1 (hab' x hx).1 ha'.le (ρ.pos x).le
      · exact mul_le_mul (hab x hx).2 (hab' x hx).2 (σ.pos x).le
          (ha.le.trans (hab x hx).1 |>.trans (hab x hx).2)⟩⟩

@[simp] theorem mul_apply (ρ σ : Weight E) (x : E) : (ρ * σ) x = ρ x * σ x := rfl

/-- The real power `ρ ^ m` of a weight. -/
instance : Pow (Weight E) ℝ :=
  ⟨fun ρ m => ⟨fun x => ρ x ^ m, ρ.measurable.pow_const m,
    fun x => Real.rpow_pos_of_pos (ρ.pos x) m, fun K hK => by
      rcases K.eq_empty_or_nonempty with rfl | ⟨y, hy⟩
      · exact ⟨1, 1, one_pos, fun x hx => absurd hx (Set.notMem_empty x)⟩
      obtain ⟨a, b, ha, hab⟩ := ρ.locBdd K hK
      have hb : 0 < b := ha.trans_le ((hab y hy).1.trans (hab y hy).2)
      rcases le_total 0 m with hm | hm
      · refine ⟨a ^ m, b ^ m, Real.rpow_pos_of_pos ha m, fun x hx => ⟨?_, ?_⟩⟩
        · exact Real.rpow_le_rpow ha.le (hab x hx).1 hm
        · exact Real.rpow_le_rpow (ρ.pos x).le (hab x hx).2 hm
      · refine ⟨b ^ m, a ^ m, Real.rpow_pos_of_pos hb m, fun x hx => ⟨?_, ?_⟩⟩
        · exact Real.rpow_le_rpow_of_nonpos (ρ.pos x) (hab x hx).2 hm
        · exact Real.rpow_le_rpow_of_nonpos ha (hab x hx).1 hm⟩⟩

@[simp] theorem rpow_apply (ρ : Weight E) (m : ℝ) (x : E) : (ρ ^ m) x = ρ x ^ m := rfl

end Weight

/-! ### Weighted measures -/

section Measure

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] (μ : Measure E) (ρ : Weight E)

/-- The weighted measure `ρ dμ`. -/
def wμ : Measure E := μ.withDensity fun x => ENNReal.ofReal (ρ x)

theorem measurable_ofReal_weight : Measurable fun x => ENNReal.ofReal (ρ x) :=
  ENNReal.measurable_ofReal.comp ρ.measurable

@[simp] theorem wμ_one : wμ μ 1 = μ := by
  simp only [wμ, Weight.one_apply, ENNReal.ofReal_one]
  exact withDensity_one

theorem wμ_ac : wμ μ ρ ≪ μ := withDensity_absolutelyContinuous _ _

theorem ac_wμ : μ ≪ wμ μ ρ := by
  refine Measure.ae_le_iff_absolutelyContinuous.mp (fun s hs => ?_)
  have hs' : ∀ᵐ x ∂(wμ μ ρ), x ∈ s := hs
  have h := (ae_withDensity_iff (measurable_ofReal_weight ρ)).mp hs'
  filter_upwards [h] with x hx
  exact hx (by simpa [ENNReal.ofReal_eq_zero, not_le] using ρ.pos x)

theorem ae_wμ_iff {P : E → Prop} : (∀ᵐ x ∂(wμ μ ρ), P x) ↔ ∀ᵐ x ∂μ, P x :=
  ⟨fun h => ac_wμ μ ρ |>.ae_le h, fun h => wμ_ac μ ρ |>.ae_le h⟩

theorem ae_eq_wμ_iff {β : Type*} {f g : E → β} : f =ᵐ[wμ μ ρ] g ↔ f =ᵐ[μ] g :=
  ae_wμ_iff μ ρ

variable {μ ρ}

theorem wμ_lt_top [T2Space E] [OpensMeasurableSpace E] [IsFiniteMeasureOnCompacts μ]
    {K : Set E} (hK : IsCompact K) : wμ μ ρ K < ∞ := by
  obtain ⟨a, b, _, hab⟩ := ρ.locBdd K hK
  rw [wμ, withDensity_apply _ hK.measurableSet]
  calc ∫⁻ x in K, ENNReal.ofReal (ρ x) ∂μ ≤ ∫⁻ _ in K, ENNReal.ofReal b ∂μ :=
        setLIntegral_mono' hK.measurableSet fun x hx => ENNReal.ofReal_le_ofReal (hab x hx).2
    _ = ENNReal.ofReal b * μ K := setLIntegral_const _ _
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top

end Measure

/-! ### Compactly bounded multipliers -/

section Pairing

variable {E : Type*} [TopologicalSpace E] [T2Space E] [MeasurableSpace E] [OpensMeasurableSpace E]
  {μ : Measure E} [IsFiniteMeasureOnCompacts μ] {ρ : Weight E}

/-- A real multiplier that is a.e.-strongly measurable, bounded on a compact set `K`, and zero
`μ`-a.e. outside `K` (every admissible test function and its derivatives is one). -/
structure CompactlyBounded (μ : Measure E) (ψ : E → ℝ) : Prop where
  aesm : AEStronglyMeasurable ψ μ
  bdd : ∃ K : Set E, IsCompact K ∧ (∃ M : ℝ, ∀ x ∈ K, |ψ x| ≤ M) ∧
    ∀ᵐ x ∂μ, x ∉ K → ψ x = 0

/-- The conjugate exponent `(1 - p⁻¹)⁻¹`. -/
def conjExp (p : ℝ≥0∞) : ℝ≥0∞ := (1 - p⁻¹)⁻¹

theorem holderTriple_conjExp (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] :
    ENNReal.HolderTriple (conjExp p) p 1 :=
  ⟨by rw [conjExp, inv_inv, inv_one]; exact tsub_add_cancel_of_le (ENNReal.inv_le_one.2 hp.out)⟩

theorem fact_one_le_conjExp (p : ℝ≥0∞) [Fact (1 ≤ p)] : Fact (1 ≤ conjExp p) :=
  haveI := holderTriple_conjExp p
  ⟨ENNReal.HolderConjugate.one_le (conjExp p) p⟩

/-- `ψ/ρ` is in every `L^q(ρ dμ)`. -/
theorem CompactlyBounded.memLp_div {ψ : E → ℝ} (hψ : CompactlyBounded μ ψ) (q : ℝ≥0∞) :
    MemLp (fun x => ψ x / ρ x) q (wμ μ ρ) := by
  obtain ⟨K, hK, ⟨M, hM⟩, hz⟩ := hψ.bdd
  obtain ⟨a, b, ha, hab⟩ := ρ.locBdd K hK
  have hsm : AEStronglyMeasurable (fun x => ψ x / ρ x) (wμ μ ρ) :=
    (hψ.aesm.mono_ac (wμ_ac μ ρ)).mul ρ.measurable.inv.aestronglyMeasurable |>.congr
      (Eventually.of_forall fun x => (div_eq_mul_inv _ _).symm)
  have hind : (fun x => ψ x / ρ x) =ᵐ[wμ μ ρ] K.indicator fun x => ψ x / ρ x := by
    rw [ae_eq_wμ_iff]
    filter_upwards [hz] with x hx
    by_cases hxK : x ∈ K
    · rw [Set.indicator_of_mem hxK]
    · rw [Set.indicator_of_notMem hxK, hx hxK, zero_div]
  refine MemLp.ae_eq hind.symm ?_
  rw [memLp_indicator_iff_restrict hK.measurableSet]
  haveI : IsFiniteMeasure ((wμ μ ρ).restrict K) :=
    isFiniteMeasure_restrict.mpr (wμ_lt_top hK).ne
  refine MemLp.of_bound hsm.restrict (M / a) ?_
  refine ae_restrict_of_forall_mem hK.measurableSet fun x hx => ?_
  have hρ := ρ.pos x
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x hx)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hρ]
  calc |ψ x| / ρ x ≤ M / ρ x := div_le_div_of_nonneg_right (hM x hx) hρ.le
    _ ≤ M / a := div_le_div_of_nonneg_left hM0 ha (hab x hx).1

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem weight_smul_div_smul {ψ : E → ℝ} (f : E → F) (x : E) :
    (ρ x).toNNReal • ((ψ x / ρ x) • f x) = ψ x • f x := by
  rw [NNReal.smul_def, Real.coe_toNNReal _ (ρ.pos x).le, smul_smul,
    mul_div_cancel₀ _ (ρ.pos x).ne']

/-- **Unweighted pairing on weighted `L^p`**: `ψ • f ∈ L¹(μ)` for `f ∈ L^p(ρ dμ)`. -/
theorem integrable_smul_of_memLp {p : ℝ≥0∞} [Fact (1 ≤ p)] {ψ : E → ℝ}
    (hψ : CompactlyBounded μ ψ) {f : E → F} (hf : MemLp f p (wμ μ ρ)) :
    Integrable (fun x => ψ x • f x) μ := by
  haveI := holderTriple_conjExp p
  have h1 : MemLp ((fun x => ψ x / ρ x) • f) 1 (wμ μ ρ) := hf.smul (hψ.memLp_div (conjExp p))
  have h2 : Integrable (fun x => (ψ x / ρ x) • f x) (wμ μ ρ) := memLp_one_iff_integrable.mp h1
  have h3 := (integrable_withDensity_iff_integrable_smul
    (f := fun x => (ρ x).toNNReal) (μ := μ) (measurable_real_toNNReal.comp ρ.measurable)).mp h2
  simpa only [weight_smul_div_smul] using h3

/-- `L^p(ρ dμ) ⊂ L¹_loc(μ)` (on a locally compact space). -/
theorem locallyIntegrable_of_memLp [LocallyCompactSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {f : E → F} (hf : MemLp f p (wμ μ ρ)) : LocallyIntegrable f μ := by
  intro x
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds x
  refine ⟨K, hKn, ?_⟩
  have hψ : CompactlyBounded μ (K.indicator 1) := by
    refine ⟨(aestronglyMeasurable_const.indicator hK.measurableSet), K, hK, ⟨1, fun y _ => ?_⟩,
      Eventually.of_forall fun y hy => Set.indicator_of_notMem hy _⟩
    by_cases hy : y ∈ K <;> simp [hy]
  have := integrable_smul_of_memLp hψ hf
  have e : (fun y => K.indicator (1 : E → ℝ) y • f y) = K.indicator f := by
    funext y; by_cases hy : y ∈ K <;> simp [hy]
  rw [e, integrable_indicator_iff hK.measurableSet] at this
  exact this

/-- The weighted integral of `(ψ/ρ) • f` is the unweighted integral of `ψ • f`. -/
theorem integral_wμ_div_smul {ψ : E → ℝ} (f : E → F) :
    ∫ x, (ψ x / ρ x) • f x ∂(wμ μ ρ) = ∫ x, ψ x • f x ∂μ := by
  have := integral_withDensity_eq_integral_smul (μ := μ)
    (measurable_real_toNNReal.comp ρ.measurable) (fun x => (ψ x / ρ x) • f x)
  simp only [Function.comp_apply, weight_smul_div_smul] at this
  exact this

variable {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 F] [IsScalarTower ℝ 𝕜 F] [CompleteSpace F]

variable (μ ρ) in
/-- **The test pairing** `f ↦ ∫ ψ f dμ` as a continuous `𝕜`-linear functional on
`L^p(ρ dμ; F)` (the unweighted pairing of tex 13886, continuous by Hölder with
`ψ/ρ ∈ L^{p'}(ρ dμ)`). -/
def testPair (p : ℝ≥0∞) [Fact (1 ≤ p)] (ψ : E → ℝ) (hψ : CompactlyBounded μ ψ) :
    Lp F p (wμ μ ρ) →L[𝕜] F :=
  haveI := holderTriple_conjExp p
  haveI := fact_one_le_conjExp p
  (ContinuousLinearMap.lsmul 𝕜 𝕜 : 𝕜 →L[𝕜] F →L[𝕜] F).lpPairing (wμ μ ρ) (conjExp p) p
    (((hψ.memLp_div (conjExp p)).ofReal (K := 𝕜)).toLp _)

theorem testPair_apply (p : ℝ≥0∞) [Fact (1 ≤ p)] (ψ : E → ℝ) (hψ : CompactlyBounded μ ψ)
    (f : Lp F p (wμ μ ρ)) : testPair (𝕜 := 𝕜) μ ρ p ψ hψ f = ∫ x, ψ x • f x ∂μ := by
  haveI := holderTriple_conjExp p
  haveI := fact_one_le_conjExp p
  rw [testPair, ContinuousLinearMap.lpPairing_eq_integral, ← integral_wμ_div_smul]
  refine integral_congr_ae ?_
  filter_upwards [((hψ.memLp_div (conjExp p)).ofReal (K := 𝕜)).coeFn_toLp] with x hx
  rw [ContinuousLinearMap.lsmul_apply, hx, ← RCLike.real_smul_eq_coe_smul]

end Pairing

theorem CompactlyBounded.of_adm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [OpensMeasurableSpace E] {n : ℕ} {D : TestDomain E n} {φ : E → ℝ}
    (hφ : D.Adm φ) : CompactlyBounded D.μ φ := by
  obtain ⟨K, hK, hz⟩ := D.supp hφ
  have hc := D.continuous hφ
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  exact ⟨hc.aestronglyMeasurable, K, hK, ⟨M, fun x hx => by
    simpa [Real.norm_eq_abs] using hM x hx⟩, hz⟩


end UnforcedLeray.Sob
