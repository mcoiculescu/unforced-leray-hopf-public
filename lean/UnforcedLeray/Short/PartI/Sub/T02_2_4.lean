import UnforcedLeray.Short.PartI.Sub.T02_2
import UnforcedLeray.Short.PartI.Sub.T02_2_4.OdeTail

/-!
# Part I, task `PartI:T02/2/4`: `OscillationDecay` (conditional decomposition)

Source of record: `the November 2 reference manuscript`, line 447 ("The decaying
pressure gauge is used here"; the oscillating part `p - p̄` of the bounded periodic pressure tends
to `0` because `Δp → 0`).

The target is `OscillationDecay` (`Short/PartI/Sub/T02_2.lean`): a bounded `C²` function `u` on
the cylinder, `c`-periodic in `q`, with `Δu → 0` as `|η| → ∞`, satisfies `u - ū → 0` as
`|η| → ∞`, where `ū(η) = hmean c u η` is the `q`-average.

## Route (`L²` in `q`, then a maximum principle)

Put `w = u - ū`.  Then `w` is `C²`, periodic, bounded, has zero `q`-mean on every slice, and
`Δw = Δu - ū'' = Δu - \\overline{Δu} → 0` (`ū'' = \\overline{∂_η² u} = \\overline{Δu}`, since
`\\overline{∂_q² u} = 0` by periodicity).  This is `OscMeanReduction` and `ZeroMeanHyp`.

* `ZeroMeanSliceEnergyDecay`: `m(η) = ∫ w(q,η)² dq → 0`.  `m'' = 2∫ w_η² + 2∫ w_q² + 2∫ wΔw`
  (`SliceEnergyIdentity`), Wirtinger on zero-mean slices gives `∫ w_q² ≥ (2π/c)² m`
  (`SliceWirtinger`), so `m'' ≥ λ² m - G/λ²` with `λ = 2π/c`, `G(η) = ∫ (Δw)² → 0`; a bounded
  `m` with this inequality tends to `0` at `±∞` (one-dimensional comparison).
* `ZeroMeanPointwiseFromEnergy`: `w → 0` uniformly in `q`.  The identity for `m''`, integrated
  against a bump, shows that near every far `η₀` there are slices `a < η₀ < b` with
  `sup_q w(·,a)², sup_q w(·,b)²` small (`GoodSliceSup`, with the Sobolev bound
  `sup_q w² ≤ 2c⁻¹ m + c ∫ w_q²`); the maximum principle for `w² + μ(η-a)(η-b)` on the slab
  `[a,b]` (`SlabBound`) bounds `w(·,η₀)²`.

## What is proved here

* `oscillationDecay_of` derives `OscillationDecay` from `OscMeanReduction`,
  `ZeroMeanSliceEnergyDecay` and `ZeroMeanPointwiseFromEnergy`;
* `oscMeanReduction_of` derives `OscMeanReduction` from `OscMeanLap`;
* `zeroMeanSliceEnergyDecay_of` derives `ZeroMeanSliceEnergyDecay` from `SliceEnergyIdentity` and
  `SliceWirtinger` (the one-dimensional comparison is `OscDecay.decay_of_ode` in
  `Sub/T02_2_4/OdeTail.lean`, on top of the half-line maximum principle `halfLine_nonpos`);
* `zeroMeanPointwiseFromEnergy_of` derives `ZeroMeanPointwiseFromEnergy` from `GoodSliceSup` and
  `SlabBound`.

The five leaf statements are `OscMeanLap`, `SliceEnergyIdentity`, `SliceWirtinger`,
`GoodSliceSup` and `SlabBound`; `SliceIntegralCalculus` (differentiation of the `q`-integral under
the sign) is a shared helper leaf of `OscMeanLap` and `SliceEnergyIdentity` (it is not used in the
conditional theorems).

The unconditional statement is task `PartI:T02/2/4`
(`Short/PartI/Tasks/LerayPressureGauge/OscillationDecay.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Real

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)

/-- The standing hypotheses of the zero-mean core: `w` is `C²`, `c`-periodic in `q`, bounded,
has vanishing `q`-mean on every slice, and `Δw → 0` as `|η| → ∞`. -/
structure ZeroMeanHyp (c : ℝ) (w : Plane → ℝ) : Prop where
  smooth : ContDiff ℝ 2 w
  periodic : Cyl.IsPeriodic c w
  bounded : ∃ M : ℝ, ∀ z, |w z| ≤ M
  zero_mean : ∀ η : ℝ, ∫ q in Ioc (-c / 2) (c / 2), w (q, η) = 0
  lap_decay : Tendsto (Train.lapS w) (comap (fun z : Plane => |z.2|) atTop) (𝓝 0)

/-- **Reduction to zero slice mean** (source line 447): for `u` as in `OscillationDecay`, the
function `w = u - ū` satisfies `ZeroMeanHyp`.  `ū = hmean c u` is `C²` in `η` with
`ū'' = hmean c (∂_η² u)` (differentiation under the integral over the compact `q`-interval); the
slice mean of `∂_q² u` vanishes by periodicity (fundamental theorem of calculus on the period), so
`ū'' = hmean c (Δu)`, whence `Δw = Δu - hmean c (Δu) → 0` (`gg_hmean_tendsto`,
`Short/PartI/Sub/T02_2.lean`); boundedness `|w| ≤ 2M`, periodicity and `∫_{-c/2}^{c/2} w dq = 0`
are immediate. -/
def OscMeanReduction : Prop :=
  ∀ (c : ℝ) (u : Plane → ℝ), 0 < c → ContDiff ℝ 2 u → Cyl.IsPeriodic c u →
    (∃ M : ℝ, ∀ z, |u z| ≤ M) →
    Tendsto (Train.lapS u) (comap (fun z : Plane => |z.2|) atTop) (𝓝 0) →
    ZeroMeanHyp c (fun z => u z - hmean c u z.2)

/-- **Decay of the slice energy** (`L²`-in-`q` route, source line 447): under `ZeroMeanHyp`,
`m(η) = ∫_{-c/2}^{c/2} w(q,η)² dq → 0` as `|η| → ∞`. -/
def ZeroMeanSliceEnergyDecay : Prop :=
  ∀ (c : ℝ) (w : Plane → ℝ), 0 < c → ZeroMeanHyp c w →
    Tendsto (fun z : Plane => ∫ q in Ioc (-c / 2) (c / 2), w (q, z.2) ^ 2)
      (comap (fun z : Plane => |z.2|) atTop) (𝓝 0)

/-- **From slice energy to uniform decay** (source line 447): under `ZeroMeanHyp`, if the slice
energy tends to `0` then `w → 0` as `|η| → ∞` (uniformly in `q`). -/
def ZeroMeanPointwiseFromEnergy : Prop :=
  ∀ (c : ℝ) (w : Plane → ℝ), 0 < c → ZeroMeanHyp c w →
    Tendsto (fun z : Plane => ∫ q in Ioc (-c / 2) (c / 2), w (q, z.2) ^ 2)
      (comap (fun z : Plane => |z.2|) atTop) (𝓝 0) →
    Tendsto w (comap (fun z : Plane => |z.2|) atTop) (𝓝 0)

/-- **`OscillationDecay` from the reduction, the energy decay and the pointwise step.** -/
theorem oscillationDecay_of (h1 : OscMeanReduction) (h2 : ZeroMeanSliceEnergyDecay)
    (h3 : ZeroMeanPointwiseFromEnergy) : OscillationDecay := by
  unfold OscillationDecay
  intro c u hc hu hper hbd hlap
  have hZ : ZeroMeanHyp c (fun z => u z - hmean c u z.2) := h1 c u hc hu hper hbd hlap
  have hE := h2 c (fun z => u z - hmean c u z.2) hc hZ
  exact h3 c (fun z => u z - hmean c u z.2) hc hZ hE

/-! ### Second level: the slice energy decay -/

/-- **The slice energy identity** (differentiation under the integral over the compact period,
then partial integration in `q`): for `w` of class `C²` and `c`-periodic in `q`, the slice energy
`m(η) = ∫_{-c/2}^{c/2} w(q,η)² dq` is twice differentiable, `m' = m1`, `m1' = m2`, with
`m2 = 2∫ (∂_η w)² + 2∫ (∂_q w)² + 2∫ w Δw` (indeed
`m'' = 2∫ (∂_η w)² + 2∫ w ∂_η² w` and `∂_η² w = Δw - ∂_q² w`, `∫ w ∂_q² w = -∫ (∂_q w)²`
by periodicity). -/
def SliceEnergyIdentity : Prop :=
  ∀ (c : ℝ) (w : Plane → ℝ), 0 < c → ContDiff ℝ 2 w → Cyl.IsPeriodic c w →
    ∃ m1 m2 : ℝ → ℝ,
      (∀ η, HasDerivAt (fun η' => ∫ q in Ioc (-c / 2) (c / 2), w (q, η') ^ 2) (m1 η) η) ∧
      (∀ η, HasDerivAt m1 (m2 η) η) ∧
      ∀ η, m2 η = 2 * (∫ q in Ioc (-c / 2) (c / 2), Cyl.partialEta w (q, η) ^ 2)
        + 2 * (∫ q in Ioc (-c / 2) (c / 2), Cyl.partialQ w (q, η) ^ 2)
        + 2 * (∫ q in Ioc (-c / 2) (c / 2), w (q, η) * Train.lapS w (q, η))

/-- **Wirtinger's inequality on zero-mean slices** (`Cyl.wirtinger_slice`,
`Lib/Cylinder/ModesWirtinger.lean`, for real `C¹` periodic `g` with zero slice means):
`∫ g(q,η)² dq ≤ (c/2π)² ∫ (∂_q g(q,η))² dq`. -/
def SliceWirtinger : Prop :=
  ∀ (c : ℝ) (g : Plane → ℝ), 0 < c → ContDiff ℝ 1 g → Cyl.IsPeriodic c g →
    (∀ η : ℝ, ∫ q in Ioc (-c / 2) (c / 2), g (q, η) = 0) →
    ∀ η : ℝ, ∫ q in Ioc (-c / 2) (c / 2), g (q, η) ^ 2 ≤
      (c / (2 * π)) ^ 2 * ∫ q in Ioc (-c / 2) (c / 2), Cyl.partialQ g (q, η) ^ 2

/-- The filter `comap (fun z => |z.2|) atTop` in `ε`-`R` form (for functions on the plane). -/
theorem osc_tendsto_iff (f : Plane → ℝ) :
    Tendsto f (comap (fun z : Plane => |z.2|) atTop) (𝓝 0) ↔
      ∀ ε > 0, ∃ R : ℝ, ∀ z : Plane, R ≤ |z.2| → |f z| < ε := by
  rw [Metric.tendsto_nhds]
  constructor
  · intro h ε hε
    have h' := h ε hε
    rw [Filter.eventually_comap, Filter.eventually_atTop] at h'
    obtain ⟨R, hR⟩ := h'
    exact ⟨R, fun z hz => by simpa [Real.dist_eq] using hR (|z.2|) hz z rfl⟩
  · intro h ε hε
    obtain ⟨R, hR⟩ := h ε hε
    rw [Filter.eventually_comap, Filter.eventually_atTop]
    refine ⟨R, fun a ha z hz => ?_⟩
    subst hz
    simpa [Real.dist_eq] using hR z ha

/-- The Laplacian of a `C²` function is continuous. -/
theorem osc_lapS_continuous {w : Plane → ℝ} (hw : ContDiff ℝ 2 w) : Continuous (Train.lapS w) := by
  have h2 : ContDiff ℝ (1 + 1 : WithTop ℕ∞) w := by rw [one_add_one_eq_two]; exact hw
  have hq : ContDiff ℝ 1 (Cyl.partialQ w) := Cyl.contDiff_partialQ h2
  have he : ContDiff ℝ 1 (Cyl.partialEta w) := Cyl.contDiff_partialEta h2
  have h1 : ContDiff ℝ (0 + 1 : WithTop ℕ∞) (Cyl.partialQ w) := by rw [zero_add]; exact hq
  have h1' : ContDiff ℝ (0 + 1 : WithTop ℕ∞) (Cyl.partialEta w) := by rw [zero_add]; exact he
  have hqq : ContDiff ℝ 0 (Cyl.partialQ (Cyl.partialQ w)) := Cyl.contDiff_partialQ h1
  have hee : ContDiff ℝ 0 (Cyl.partialEta (Cyl.partialEta w)) := Cyl.contDiff_partialEta h1'
  exact hqq.continuous.add hee.continuous

/-- Slices of a continuous function are continuous. -/
theorem osc_slice_continuous {f : Plane → ℝ} (hf : Continuous f) (η : ℝ) :
    Continuous (fun q : ℝ => f (q, η)) :=
  hf.comp (continuous_id.prodMk continuous_const)

/-- **The slice energy decays** (`L²`-in-`q` route) from the energy identity and Wirtinger. -/
theorem zeroMeanSliceEnergyDecay_of (hE : SliceEnergyIdentity) (hW : SliceWirtinger) :
    ZeroMeanSliceEnergyDecay := by
  intro c w hc hZ
  obtain ⟨M, hM⟩ := hZ.bounded
  obtain ⟨m1, m2, hm, hm1, hid⟩ := hE c w hc hZ.smooth hZ.periodic
  have hwc : Continuous w := hZ.smooth.continuous
  have hfc : Continuous (Train.lapS w) := osc_lapS_continuous hZ.smooth
  set lam : ℝ := 2 * π / c with hlam_def
  have hlam : 0 < lam := by positivity
  let m : ℝ → ℝ := fun η => ∫ q in Ioc (-c / 2) (c / 2), w (q, η) ^ 2
  let G : ℝ → ℝ := fun η => ∫ q in Ioc (-c / 2) (c / 2), Train.lapS w (q, η) ^ 2
  have hvol : (volume : Measure ℝ).real (Ioc (-c / 2) (c / 2)) = c := by
    rw [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    ring
  have hmnn : ∀ η, 0 ≤ m η := fun η =>
    setIntegral_nonneg measurableSet_Ioc (fun q _ => sq_nonneg _)
  have hmb : ∀ η, m η ≤ M ^ 2 * c := by
    intro η
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (-c / 2) (c / 2))
      (f := fun q => w (q, η) ^ 2) (C := M ^ 2) (by simp) (fun q _ => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hM _) 2)
    rw [hvol, Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  have hineq : ∀ η, lam ^ 2 * m η - G η / lam ^ 2 ≤ m2 η := by
    intro η
    have hQ : 0 ≤ ∫ q in Ioc (-c / 2) (c / 2), Cyl.partialEta w (q, η) ^ 2 :=
      setIntegral_nonneg measurableSet_Ioc (fun q _ => sq_nonneg _)
    have hP : lam ^ 2 * m η ≤ ∫ q in Ioc (-c / 2) (c / 2), Cyl.partialQ w (q, η) ^ 2 := by
      have h := hW c w hc (hZ.smooth.of_le (by norm_num)) hZ.periodic hZ.zero_mean η
      have e : lam ^ 2 * (c / (2 * π)) ^ 2 = 1 := by rw [hlam_def]; field_simp
      calc lam ^ 2 * m η ≤ lam ^ 2 * ((c / (2 * π)) ^ 2 *
            ∫ q in Ioc (-c / 2) (c / 2), Cyl.partialQ w (q, η) ^ 2) :=
            mul_le_mul_of_nonneg_left h (sq_nonneg _)
        _ = _ := by rw [← mul_assoc, e, one_mul]
    have hw2 : Integrable (fun q : ℝ => w (q, η) ^ 2) (volume.restrict (Ioc (-c / 2) (c / 2))) :=
      ((osc_slice_continuous hwc η).pow 2).integrableOn_Ioc
    have hwf : Integrable (fun q : ℝ => w (q, η) * Train.lapS w (q, η))
        (volume.restrict (Ioc (-c / 2) (c / 2))) :=
      ((osc_slice_continuous hwc η).mul (osc_slice_continuous hfc η)).integrableOn_Ioc
    have hf2 : Integrable (fun q : ℝ => Train.lapS w (q, η) ^ 2)
        (volume.restrict (Ioc (-c / 2) (c / 2))) :=
      ((osc_slice_continuous hfc η).pow 2).integrableOn_Ioc
    have hnn : 0 ≤ ∫ q in Ioc (-c / 2) (c / 2),
        (lam ^ 2 * w (q, η) ^ 2 + 2 * (w (q, η) * Train.lapS w (q, η)) +
          Train.lapS w (q, η) ^ 2 / lam ^ 2) := by
      apply setIntegral_nonneg measurableSet_Ioc
      intro q _
      have : lam ^ 2 * w (q, η) ^ 2 + 2 * (w (q, η) * Train.lapS w (q, η)) +
          Train.lapS w (q, η) ^ 2 / lam ^ 2 =
          (lam * w (q, η) + Train.lapS w (q, η) / lam) ^ 2 := by
        field_simp
        ring
      rw [this]
      exact sq_nonneg _
    have h12 : Integrable (fun q : ℝ => lam ^ 2 * w (q, η) ^ 2 +
        2 * (w (q, η) * Train.lapS w (q, η))) (volume.restrict (Ioc (-c / 2) (c / 2))) :=
      (hw2.const_mul (lam ^ 2)).add (hwf.const_mul 2)
    have h3 : Integrable (fun q : ℝ => Train.lapS w (q, η) ^ 2 / lam ^ 2)
        (volume.restrict (Ioc (-c / 2) (c / 2))) := hf2.div_const _
    have h1 : Integrable (fun q : ℝ => lam ^ 2 * w (q, η) ^ 2)
        (volume.restrict (Ioc (-c / 2) (c / 2))) := hw2.const_mul (lam ^ 2)
    have h2 : Integrable (fun q : ℝ => 2 * (w (q, η) * Train.lapS w (q, η)))
        (volume.restrict (Ioc (-c / 2) (c / 2))) := hwf.const_mul 2
    rw [integral_add h12 h3, integral_add h1 h2, integral_const_mul,
      integral_const_mul, integral_div] at hnn
    have hm2 := hid η
    have hmη : m η = ∫ q in Ioc (-c / 2) (c / 2), w (q, η) ^ 2 := rfl
    have hGη : G η = ∫ q in Ioc (-c / 2) (c / 2), Train.lapS w (q, η) ^ 2 := rfl
    rw [hmη] at hP ⊢
    rw [hGη]
    linarith
  have hg : ∀ γ : ℝ, 0 < γ → ∃ R : ℝ, ∀ η, R ≤ |η| → G η ≤ γ := by
    intro γ hγ
    have hδ : 0 < Real.sqrt (γ / c) := Real.sqrt_pos.mpr (by positivity)
    obtain ⟨R, hR⟩ := (osc_tendsto_iff _).1 hZ.lap_decay (Real.sqrt (γ / c)) hδ
    refine ⟨R, fun η hη => ?_⟩
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (-c / 2) (c / 2))
      (f := fun q => Train.lapS w (q, η) ^ 2) (C := γ / c) (by simp) (fun q _ => by
        have h1 : |Train.lapS w (q, η)| < Real.sqrt (γ / c) := by
          have := hR (q, η) (by simpa using hη)
          simpa using this
        rw [Real.norm_eq_abs, abs_pow]
        have h2 : |Train.lapS w (q, η)| ^ 2 ≤ Real.sqrt (γ / c) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) h1.le 2
        rwa [Real.sq_sqrt (by positivity)] at h2)
    rw [hvol, Real.norm_eq_abs] at h
    have h3 : γ / c * c = γ := by field_simp
    rw [h3] at h
    exact (le_abs_self _).trans h
  have hdecay := OscDecay.decay_of_ode hlam hm hm1 hmb hineq hg
  refine (osc_tendsto_iff _).2 (fun ε hε => ?_)
  obtain ⟨R, hR⟩ := hdecay ε hε
  refine ⟨R, fun z hz => ?_⟩
  have h1 := hR z.2 hz
  have h2 := hmnn z.2
  show |m z.2| < ε
  rw [abs_of_nonneg h2]
  exact h1

/-! ### Second level: from the slice energy to uniform decay -/

/-- **Good slices** (energy identity integrated against a bump, plus the Sobolev bound on a
slice): under `ZeroMeanHyp`, if the slice energy `m(η) = ∫ w(q,η)² dq` tends to `0`, then for
every `ε > 0` there is `R` such that near every `η₀` with `|η₀| ≥ R` there are slices `a ≤ η₀ ≤ b`,
`|a - η₀|, |b - η₀| ≤ 2`, with `sup_q w(q,a)² ≤ ε` and `sup_q w(q,b)² ≤ ε`.

Proof sketch.  With `m'' = 2Q + 2P + 2F` (`SliceEnergyIdentity`; `P(η) = ∫ (∂_q w)²`,
`F = ∫ w Δw`), `2P ≤ m'' + 2|F|`; integrate against a `C²` bump `χ` (`χ = 1` on `[η₀-2, η₀+2]`,
supported in `[η₀-3, η₀+3]`, `∫|χ''|` independent of `η₀`): `2∫_{η₀-2}^{η₀+2} P ≤ ∫ χ'' m + 2∫ χ |F|`
(two partial integrations in `η`), which is small because `m → 0` and
`|F| ≤ √(m ∫ (Δw)²) → 0`.  So `P(a) ≤ ∫_{η₀-2}^{η₀-1} P` for some `a ∈ [η₀-2, η₀-1]` (continuity
of `P`) and likewise `b ∈ [η₀+1, η₀+2]`.  Then `sup_q w(·,a)² ≤ 2c⁻¹ m(a) + c P(a)` (`Cyl.sq_sup_q_le`,
`Lib/Cylinder/SupBound.lean`, applied to the `ℂ`-valued `w`). -/
def GoodSliceSup : Prop :=
  ∀ (c : ℝ) (w : Plane → ℝ), 0 < c → ZeroMeanHyp c w →
    Tendsto (fun z : Plane => ∫ q in Ioc (-c / 2) (c / 2), w (q, z.2) ^ 2)
      (comap (fun z : Plane => |z.2|) atTop) (𝓝 0) →
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ η0 : ℝ, R ≤ |η0| →
      ∃ a b : ℝ, η0 - 2 ≤ a ∧ a ≤ η0 ∧ η0 ≤ b ∧ b ≤ η0 + 2 ∧
        (∀ q : ℝ, w (q, a) ^ 2 ≤ ε) ∧ (∀ q : ℝ, w (q, b) ^ 2 ≤ ε)

/-- **Maximum principle on a slab for `w²`**: for `w` of class `C²` and `c`-periodic in `q`,
`a ≤ b`, if `|w Δw| < μ` on the slab `a ≤ η ≤ b` and `w² ≤ K` on both boundary lines, then
`w² ≤ K + μ (b - a)²/4` on the slab.  (`g = w² + μ (η - a)(η - b)` satisfies
`Δg = 2|∇w|² + 2 w Δw + 2μ > 0`, so its maximum over the compact period cell of the slab is not
attained at an interior point (at an interior maximum `∂_q² g ≤ 0` and `∂_η² g ≤ 0`, second
derivative test along the two coordinate lines); hence `g ≤ K` on the slab, and
`w² = g - μ (η - a)(η - b) ≤ K + μ (b - a)²/4`.) -/
def SlabBound : Prop :=
  ∀ (c : ℝ) (w : Plane → ℝ), 0 < c → ContDiff ℝ 2 w → Cyl.IsPeriodic c w →
    ∀ a b K μ : ℝ, a ≤ b →
      (∀ z : Plane, a ≤ z.2 → z.2 ≤ b → |w z * Train.lapS w z| < μ) →
      (∀ q : ℝ, w (q, a) ^ 2 ≤ K) → (∀ q : ℝ, w (q, b) ^ 2 ≤ K) →
      ∀ z : Plane, a ≤ z.2 → z.2 ≤ b → w z ^ 2 ≤ K + μ * (b - a) ^ 2 / 4

/-- **Uniform decay from the slice energy** (good slices, then the slab maximum principle). -/
theorem zeroMeanPointwiseFromEnergy_of (hG : GoodSliceSup) (hS : SlabBound) :
    ZeroMeanPointwiseFromEnergy := by
  intro c w hc hZ hE
  obtain ⟨M, hM⟩ := hZ.bounded
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  refine (osc_tendsto_iff _).2 (fun ε hε => ?_)
  have hε2 : 0 < ε ^ 2 := by positivity
  obtain ⟨R1, hR1⟩ := hG c w hc hZ hE (ε ^ 2 / 8) (by positivity)
  have hδ : 0 < ε ^ 2 / (32 * (M + 1)) := by positivity
  obtain ⟨R2, hR2⟩ := (osc_tendsto_iff _).1 hZ.lap_decay _ hδ
  refine ⟨max R1 (R2 + 2), fun z hz => ?_⟩
  have hz1 : R1 ≤ |z.2| := le_trans (le_max_left _ _) hz
  have hz2 : R2 + 2 ≤ |z.2| := le_trans (le_max_right _ _) hz
  obtain ⟨a, b, ha1, ha2, hb1, hb2, hKa, hKb⟩ := hR1 z.2 hz1
  have hslab : ∀ y : Plane, a ≤ y.2 → y.2 ≤ b → |w y * Train.lapS w y| < ε ^ 2 / 16 := by
    intro y hy1 hy2
    have hy : R2 ≤ |y.2| := by
      have h1 : |z.2| - 2 ≤ |y.2| := by
        have : |z.2| ≤ |y.2| + |z.2 - y.2| := by
          calc |z.2| = |y.2 + (z.2 - y.2)| := by ring_nf
            _ ≤ |y.2| + |z.2 - y.2| := abs_add_le _ _
        have h2 : |z.2 - y.2| ≤ 2 := by
          rw [abs_le]; constructor <;> linarith
        linarith
      linarith
    have hf := hR2 y hy
    rw [abs_mul]
    have hwy : |w y| ≤ M := hM y
    have h3 : |w y| * |Train.lapS w y| ≤ M * (ε ^ 2 / (32 * (M + 1))) :=
      mul_le_mul hwy hf.le (abs_nonneg _) hM0
    have h4 : M * (ε ^ 2 / (32 * (M + 1))) ≤ ε ^ 2 / 32 := by
      rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hb := hS c w hc hZ.smooth hZ.periodic a b (ε ^ 2 / 8) (ε ^ 2 / 16) (by linarith) hslab hKa hKb
    z (by linarith) (by linarith)
  have hba : (b - a) ^ 2 ≤ 16 := by nlinarith
  have hsq : w z ^ 2 < ε ^ 2 := by
    have : ε ^ 2 / 16 * (b - a) ^ 2 / 4 ≤ ε ^ 2 / 16 * 16 / 4 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact mul_le_mul_of_nonneg_left hba (by positivity)
    nlinarith
  exact abs_lt_of_sq_lt_sq hsq hε.le

/-! ### Second level: the reduction to zero slice mean -/

/-- **Calculus of the `q`-integral** (shared helper leaf of `OscMeanLap` and
`SliceEnergyIdentity`; differentiation under the integral over the compact `q`-interval,
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`, the bound coming from the continuity of the
derivative on `[-c/2, c/2] × [η-1, η+1]`): for `F` of class `C¹` on the plane,
`η ↦ ∫_{-c/2}^{c/2} F(q,η) dq` has derivative `∫_{-c/2}^{c/2} ∂_η F(q,η) dq`; and the `q`-integral
of a continuous function is continuous in `η`. -/
def SliceIntegralCalculus : Prop :=
  ∀ c : ℝ, 0 < c →
    (∀ F : Plane → ℝ, ContDiff ℝ 1 F → ∀ η : ℝ,
      HasDerivAt (fun η' => ∫ q in Ioc (-c / 2) (c / 2), F (q, η'))
        (∫ q in Ioc (-c / 2) (c / 2), Cyl.partialEta F (q, η)) η) ∧
    (∀ F : Plane → ℝ, Continuous F →
      Continuous (fun η : ℝ => ∫ q in Ioc (-c / 2) (c / 2), F (q, η)))

/-- **Smoothness and Laplacian of the fluctuation** (source line 447): for `u` of class `C²` and
`c`-periodic in `q`, the fluctuation `w = u - ū` is `C²` and
`Δw = Δu - hmean c (Δu)`.  (`ū = hmean c u` is `C²` in `η` with `ū'' = hmean c (∂_η² u)`,
differentiation under the integral over the compact `q`-interval; the slice mean of `∂_q² u`
vanishes by the fundamental theorem of calculus for the periodic function `∂_q u`; so
`ū'' = hmean c (Δu)`.  Existing Lean for `C^∞` data: `mm_hasDerivAt_avg`,
`mm_integral_partialQ_zero` in `Short/PartI/Tasks/TrainMeanEquations/MeanMomentumU.lean`;
`hmeanEtaDeriv` in `Short/PartII-a/Tasks/R02/MeanStress/HmeanEtaDeriv.lean`.) -/
def OscMeanLap : Prop :=
  ∀ (c : ℝ) (u : Plane → ℝ), 0 < c → ContDiff ℝ 2 u → Cyl.IsPeriodic c u →
    ContDiff ℝ 2 (fun z : Plane => u z - hmean c u z.2) ∧
      ∀ z : Plane, Train.lapS (fun z : Plane => u z - hmean c u z.2) z =
        Train.lapS u z - hmean c (Train.lapS u) z.2

/-- **The reduction to zero slice mean** from the smoothness and Laplacian of the fluctuation. -/
theorem oscMeanReduction_of (hL : OscMeanLap) : OscMeanReduction := by
  intro c u hc hu hper hbd hlap
  obtain ⟨M, hM⟩ := hbd
  obtain ⟨hsm, hlapEq⟩ := hL c u hc hu hper
  have huc : Continuous u := hu.continuous
  have hvol : (volume : Measure ℝ).real (Ioc (-c / 2) (c / 2)) = c := by
    rw [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    ring
  have hmean_le : ∀ η : ℝ, |hmean c u η| ≤ M := by
    intro η
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (-c / 2) (c / 2))
      (f := fun q => u (q, η)) (C := M) (by simp) (fun q _ => by
        rw [Real.norm_eq_abs]; exact hM _)
    rw [hvol, Real.norm_eq_abs] at h
    unfold hmean
    rw [smul_eq_mul, abs_mul, abs_inv, abs_of_pos hc]
    calc c⁻¹ * |∫ q in Ioc (-c / 2) (c / 2), u (q, η)| ≤ c⁻¹ * (M * c) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = M := by field_simp
  refine ⟨hsm, ?_, ⟨2 * M, fun z => ?_⟩, fun η => ?_, ?_⟩
  · intro z
    show u (z.1 + c, z.2) - hmean c u (z.1 + c, z.2).2 = u z - hmean c u z.2
    rw [hper z]
  · calc |u z - hmean c u z.2| ≤ |u z| + |hmean c u z.2| := abs_sub _ _
      _ ≤ M + M := add_le_add (hM z) (hmean_le z.2)
      _ = 2 * M := by ring
  · have hint : Integrable (fun q : ℝ => u (q, η)) (volume.restrict (Ioc (-c / 2) (c / 2))) :=
      (osc_slice_continuous huc η).integrableOn_Ioc
    show ∫ q in Ioc (-c / 2) (c / 2), (u (q, η) - hmean c u (q, η).2) = 0
    simp only
    rw [integral_sub hint (integrable_const _), setIntegral_const, hvol]
    unfold hmean
    rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul, sub_self]
  · have h2 : Tendsto (fun z : Plane => hmean c (Train.lapS u) z.2)
        (comap (fun z : Plane => |z.2|) atTop) (𝓝 0) := gg_hmean_tendsto hc hlap
    have h3 := hlap.sub h2
    rw [sub_zero] at h3
    have h4 : Train.lapS (fun z : Plane => u z - hmean c u z.2) =
        fun z => Train.lapS u z - hmean c (Train.lapS u) z.2 := funext hlapEq
    rw [h4]
    simpa using h3

end UnforcedLeray.Short.PartI
