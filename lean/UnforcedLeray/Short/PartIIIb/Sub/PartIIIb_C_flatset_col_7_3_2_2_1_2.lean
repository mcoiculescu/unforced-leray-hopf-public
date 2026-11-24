import UnforcedLeray.Units.B0224.Operators
import UnforcedLeray.Units.B0223.Lift

/-!
# Strong continuity at age `0` of the age-dependent cylinder heat `H_{θ_s}` on `H`

Source `the November 2 reference manuscript` lines 1650-1656.

For `g ∈ H` let `G_s = periodize g (s, ·)` be its fibre at age `s`.  By the fibre structure of
`heatH` (`coeFn_heatH`, `fiberHeat`), `‖H_{θ_t} g - g‖²_H = ∫_{s>0} s^{-3/2} N(θ_t(s), G_s) ds` with
`N(θ, u) = ∫_strip |e^{θΔ}u - u|²`.  The analytic inputs are the fibre statements `HeatFiberCont`
(planar heat is strongly continuous at time `0`) and `HeatFiberBound` (contraction), and the
age-level bookkeeping `HeatAgeFormula`, `HeatAgeMass`, `HeatAgeMeas`, `HeatFibreBasic`;
the age-level dominated convergence is proved here from them.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.HeatStrong

open UnforcedLeray.B0220 (HSpace measureH Profile periodize)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.B0224 (planeHeat strip heatH heatTime measurable_heatTime)

/-- `∫_strip |e^{θΔ}u - u|²` (the fibre error). -/
def stripN (c θ : ℝ) (u : ℝ × ℝ → MeridC) : ℝ≥0∞ :=
  ∫⁻ z in strip c, ‖planeHeat θ u z - u z‖ₑ ^ 2

/-- `∫_strip |u|²` (the fibre mass). -/
def stripM (c : ℝ) (u : ℝ × ℝ → MeridC) : ℝ≥0∞ :=
  ∫⁻ z in strip c, ‖u z‖ₑ ^ 2

/-- The `q`-periodised fibre of `g` at age `s`. -/
def fibre (c : ℝ) (g : HSpace c MeridC) (s : ℝ) : ℝ × ℝ → MeridC :=
  fun z => periodize c (g : Profile → MeridC) (s, z)

/-- Fibre strong continuity of the planar heat at time `0` (tex 1650-1656): for `u` measurable,
`c`-periodic with finite strip mass, `N(θ, u) → 0` as `θ → 0`. -/
def HeatFiberCont (c : ℝ) : Prop :=
  ∀ u : ℝ × ℝ → MeridC, StronglyMeasurable u → UnforcedLeray.Cyl.IsPeriodic c u →
    stripM c u < ∞ → Tendsto (fun θ : ℝ => stripN c θ u) (𝓝 0) (𝓝 0)

/-- Fibre contraction: `N(θ, u) ≤ 4 ∫_strip |u|²` for all `θ`. -/
def HeatFiberBound (c : ℝ) : Prop :=
  ∀ u : ℝ × ℝ → MeridC, StronglyMeasurable u → UnforcedLeray.Cyl.IsPeriodic c u →
    ∀ θ : ℝ, stripN c θ u ≤ 4 * stripM c u

/-- Fibres of `g ∈ H` are strongly measurable and `c`-periodic. -/
def HeatFibreBasic (c : ℝ) : Prop :=
  ∀ (g : HSpace c MeridC) (s : ℝ), StronglyMeasurable (fibre c g s) ∧
    UnforcedLeray.Cyl.IsPeriodic c (fibre c g s)

/-- Age formula for the error norm (via `coeFn_heatH`, `lintegral_measureH_eq`, Fubini). -/
def HeatAgeFormula (c : ℝ) : Prop :=
  ∀ (hc : 0 < c) (ν t : ℝ) (g : HSpace c MeridC),
    ∫⁻ p, ‖((heatH hc (measurable_heatTime ν t) g - g : HSpace c MeridC) : Profile → MeridC) p‖ₑ ^ 2
        ∂measureH c =
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) *
        stripN c (heatTime ν t s) (fibre c g s)

/-- Age formula for the mass. -/
def HeatAgeMass (c : ℝ) : Prop :=
  ∀ g : HSpace c MeridC,
    ∫⁻ p, ‖(g : Profile → MeridC) p‖ₑ ^ 2 ∂measureH c =
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) * stripM c (fibre c g s)

/-- Measurability in the age of the fibre error and mass. -/
def HeatAgeMeas (c : ℝ) : Prop :=
  ∀ (ν t : ℝ) (g : HSpace c MeridC),
    Measurable (fun s : ℝ => stripN c (heatTime ν t s) (fibre c g s)) ∧
    Measurable (fun s : ℝ => stripM c (fibre c g s))

theorem tendsto_heatH_heatTime_zero_of (c ν : ℝ) (hc : 0 < c)
    (h1 : HeatFiberCont c) (h2 : HeatFiberBound c) (h3 : HeatFibreBasic c)
    (h4 : HeatAgeFormula c) (h5 : HeatAgeMass c) (h6 : HeatAgeMeas c)
    (g : HSpace c MeridC) :
    Filter.Tendsto (fun s : ℝ => heatH hc (measurable_heatTime ν s) g)
      (nhdsWithin 0 (Set.Ici 0)) (nhds g) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  set μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hμ
  set M : ℝ → ℝ≥0∞ := fun s => stripM c (fibre c g s) with hM
  set B : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) * (4 * M s) with hB
  have hmass : ∫⁻ s, ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) * M s ∂μ < ∞ := by
    have h := h5 g
    show ∫⁻ s, ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) * stripM c (fibre c g s) ∂μ < ∞
    rw [hμ, ← h]
    exact UnforcedLeray.B0224.lintegral_sq_lt_top g
  have hwm : Measurable fun s : ℝ => ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)
  have hMm : Measurable M := (h6 ν 0 g).2
  have hBfin : ∫⁻ s, B s ∂μ ≠ ∞ := by
    have : ∫⁻ s, B s ∂μ = 4 * ∫⁻ s, ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) * M s ∂μ := by
      rw [← lintegral_const_mul' _ _ (by norm_num)]
      refine lintegral_congr fun s => ?_
      simp only [hB]; ring
    rw [this]
    exact (ENNReal.mul_lt_top (by norm_num) hmass).ne
  have hae : ∀ᵐ s ∂μ, M s < ∞ := by
    have hfin : ∀ᵐ s ∂μ, ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) * M s < ∞ :=
      ae_lt_top (hwm.mul hMm) hmass.ne
    filter_upwards [hfin, ae_restrict_mem measurableSet_Ioi] with s hs hs0
    have hpos : ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hs0 _)).ne'
    by_contra hx
    rw [not_lt, top_le_iff] at hx
    rw [hx, ENNReal.mul_top hpos] at hs
    exact lt_irrefl _ hs
  set F : ℝ → ℝ → ℝ≥0∞ := fun t s =>
    ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) * stripN c (heatTime ν t s) (fibre c g s) with hF
  have hlim : Tendsto (fun t : ℝ => ∫⁻ s, F t s ∂μ) (𝓝[≥] 0) (𝓝 (∫⁻ _s, (0 : ℝ≥0∞) ∂μ)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence B ?_ ?_ hBfin ?_
    · exact Eventually.of_forall fun t =>
        (hwm.mul (h6 ν t g).1 : Measurable (F t))
    · refine Eventually.of_forall fun t => ?_
      refine Eventually.of_forall fun s => ?_
      obtain ⟨hs1, hs2⟩ := h3 g s
      simp only [hF, hB, hM]
      exact mul_le_mul' le_rfl (h2 _ hs1 hs2 _)
    · filter_upwards [hae] with s hs
      obtain ⟨hs1, hs2⟩ := h3 g s
      have hc0 := h1 _ hs1 hs2 hs
      have hθ : Tendsto (fun t : ℝ => heatTime ν t s) (𝓝[≥] 0) (𝓝 0) := by
        have : Continuous fun t : ℝ => heatTime ν t s := by
          unfold heatTime; fun_prop
        have h0 : heatTime ν 0 s = 0 := by simp [heatTime]
        simpa [h0] using (this.tendsto 0).mono_left nhdsWithin_le_nhds
      have := (hc0.comp hθ)
      simp only [hF]
      have h' := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (s ^ (-(3 / 2 : ℝ)))) this
        (Or.inr ENNReal.ofReal_ne_top)
      simpa using h'
  simp only [lintegral_zero] at hlim
  have hfor : ∀ t, ∫⁻ s, F t s ∂μ =
      ∫⁻ p, ‖((heatH hc (measurable_heatTime ν t) g - g : HSpace c MeridC) :
        Profile → MeridC) p‖ₑ ^ 2 ∂measureH c := fun t => (h4 hc ν t g).symm
  have hnorm : ∀ t, ‖heatH hc (measurable_heatTime ν t) g - g‖ =
      ((∫⁻ s, F t s ∂μ) ^ (1 / 2 : ℝ)).toReal := by
    intro t
    rw [hfor t, Lp.norm_def, UnforcedLeray.B0224.eLpNorm_two_eq]
  simp_rw [hnorm]
  have hr : Tendsto (fun x : ℝ≥0∞ => x ^ (1 / 2 : ℝ)) (𝓝 0) (𝓝 0) := by
    have := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0
    simpa using this
  have := (ENNReal.tendsto_toReal (ENNReal.zero_ne_top)).comp (hr.comp hlim)
  simpa only [ENNReal.toReal_zero, Function.comp_def] using this

end UnforcedLeray.Short.PartIIIb.Concrete.HeatStrong
