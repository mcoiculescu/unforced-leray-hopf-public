import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.Defs

/-!
# The chart change of variables (source 2666-2668)

`chartChange_of` assembles `ChartChangeSE` (the planar change `(s, η) ↦ (ρ, t)`) and
`ChartChangeTQ` (the phase change over one period) with the age measure `ageμ` (`lintegral_ageμ`)
and Tonelli. The `τ`-integral is moved inside, `(s, η)` is changed to `(q, η)` by `ChartChangeTQ`,
and the constants `(R²/2)(2/R) = R` and `R c · c⁻¹ = R` combine.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Axi UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst

/-- The chart-side conversion: the integral over the age-weighted chart set equals the iterated
integral over `s`, then `η`, then `q` (source 2666-2668, `lintegral_ageμ`). -/
private theorem chart_rhs (R c lo : ℝ) (hR : 0 < R) (hc : 0 < c) (Θ : ℝ → ℝ → ℝ → ℝ≥0∞)
    (hΘ : Measurable (fun u : ℝ × ℝ × ℝ => Θ u.1 u.2.1 u.2.2)) :
    ∫⁻ x in {x : Chart | 0 < x.1 ∧ lo < R / Real.sqrt x.1},
        Θ (chartTau R x) (R / Real.sqrt x.1) (x.2.2 / Real.sqrt x.1) ∂(ageμ c (-5 / 2)) =
      ∫⁻ s in {s : ℝ | 0 < s ∧ lo < R / Real.sqrt s}, ∫⁻ η : ℝ, ∫⁻ q in Ico (-c / 2) (c / 2),
        ENNReal.ofReal (c⁻¹ * s ^ (-5 / 2 : ℝ)) *
          Θ (2 * q / R + Real.log s) (R / Real.sqrt s) (η / Real.sqrt s) := by
  have hS' : MeasurableSet {x : Chart | 0 < x.1 ∧ lo < R / Real.sqrt x.1} :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_const
        ((measurable_const.div Real.continuous_sqrt.measurable).comp measurable_fst))
  have hS : MeasurableSet {s : ℝ | 0 < s ∧ lo < R / Real.sqrt s} :=
    measurableSet_Ioi.inter
      (measurableSet_lt measurable_const (measurable_const.div Real.continuous_sqrt.measurable))
  have m1 : Measurable (fun x : Chart => chartTau R x) := by
    unfold chartTau
    exact ((measurable_const.mul (measurable_fst.comp measurable_snd)).div_const R).add
      (Real.measurable_log.comp measurable_fst)
  have m2 : Measurable (fun x : Chart => R / Real.sqrt x.1) :=
    measurable_const.div (Real.continuous_sqrt.measurable.comp measurable_fst)
  have m3 : Measurable (fun x : Chart => x.2.2 / Real.sqrt x.1) :=
    (measurable_snd.comp measurable_snd).div (Real.continuous_sqrt.measurable.comp measurable_fst)
  have hG : Measurable (fun x : Chart =>
      Θ (chartTau R x) (R / Real.sqrt x.1) (x.2.2 / Real.sqrt x.1)) :=
    hΘ.comp (m1.prodMk (m2.prodMk m3))
  have hw : Measurable (fun x : Chart => ENNReal.ofReal (c⁻¹ * x.1 ^ (-5 / 2 : ℝ))) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_fst.pow_const _))
  have hset : {x : Chart | 0 < x.1 ∧ lo < R / Real.sqrt x.1} ∩ (Ioi (0 : ℝ) ×ˢ qCell c)
      = {s : ℝ | 0 < s ∧ lo < R / Real.sqrt s} ×ˢ qCell c := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_setOf_eq, Set.mem_Ioi]
    tauto
  have hF : (fun p : Chart => ENNReal.ofReal (c⁻¹ * p.1 ^ (-5 / 2 : ℝ)) *
        {x : Chart | 0 < x.1 ∧ lo < R / Real.sqrt x.1}.indicator
          (fun x : Chart => Θ (chartTau R x) (R / Real.sqrt x.1) (x.2.2 / Real.sqrt x.1)) p)
      = {x : Chart | 0 < x.1 ∧ lo < R / Real.sqrt x.1}.indicator
          (fun p : Chart => ENNReal.ofReal (c⁻¹ * p.1 ^ (-5 / 2 : ℝ)) *
            Θ (chartTau R p) (R / Real.sqrt p.1) (p.2.2 / Real.sqrt p.1)) := by
    funext p
    by_cases hp : p ∈ {x : Chart | 0 < x.1 ∧ lo < R / Real.sqrt x.1}
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp]
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp, mul_zero]
  have hfm : Measurable (fun p : Chart => ENNReal.ofReal (c⁻¹ * p.1 ^ (-5 / 2 : ℝ)) *
      Θ (chartTau R p) (R / Real.sqrt p.1) (p.2.2 / Real.sqrt p.1)) := hw.mul hG
  -- the inner `(q, η)` product integral at fixed `s`
  have inner : ∀ s : ℝ, ∫⁻ y in qCell c, ENNReal.ofReal (c⁻¹ * s ^ (-5 / 2 : ℝ)) *
        Θ (2 * y.1 / R + Real.log s) (R / Real.sqrt s) (y.2 / Real.sqrt s)
          ∂(volume : Measure (ℝ × ℝ))
      = ∫⁻ q in Ico (-c / 2) (c / 2), ∫⁻ η : ℝ, ENNReal.ofReal (c⁻¹ * s ^ (-5 / 2 : ℝ)) *
          Θ (2 * q / R + Real.log s) (R / Real.sqrt s) (η / Real.sqrt s) := by
    intro s
    have ha : Measurable (fun y : ℝ × ℝ => 2 * y.1 / R + Real.log s) :=
      ((measurable_fst.const_mul 2).div_const R).add measurable_const
    have hb : Measurable (fun y : ℝ × ℝ => y.2 / Real.sqrt s) :=
      measurable_snd.div_const _
    have hk : Measurable (fun y : ℝ × ℝ => (R / Real.sqrt s, y.2 / Real.sqrt s)) :=
      measurable_const.prodMk hb
    have hm : Measurable (fun y : ℝ × ℝ => ENNReal.ofReal (c⁻¹ * s ^ (-5 / 2 : ℝ)) *
        Θ (2 * y.1 / R + Real.log s) (R / Real.sqrt s) (y.2 / Real.sqrt s)) :=
      measurable_const.mul (hΘ.comp (ha.prodMk hk))
    rw [qCell, Measure.volume_eq_prod ℝ ℝ, setLIntegral_prod _ hm.aemeasurable]
    simp only [Measure.restrict_univ]
  -- Fubini in `(q, η)` at fixed `s`
  have swapQE : ∀ s : ℝ, ∫⁻ q in Ico (-c / 2) (c / 2), ∫⁻ η : ℝ,
        ENNReal.ofReal (c⁻¹ * s ^ (-5 / 2 : ℝ)) *
          Θ (2 * q / R + Real.log s) (R / Real.sqrt s) (η / Real.sqrt s)
      = ∫⁻ η : ℝ, ∫⁻ q in Ico (-c / 2) (c / 2),
          ENNReal.ofReal (c⁻¹ * s ^ (-5 / 2 : ℝ)) *
            Θ (2 * q / R + Real.log s) (R / Real.sqrt s) (η / Real.sqrt s) := by
    intro s
    have ha : Measurable (fun z : ℝ × ℝ => 2 * z.1 / R + Real.log s) :=
      ((measurable_fst.const_mul 2).div_const R).add measurable_const
    have hb : Measurable (fun z : ℝ × ℝ => z.2 / Real.sqrt s) :=
      measurable_snd.div_const _
    have hk : Measurable (fun z : ℝ × ℝ => (R / Real.sqrt s, z.2 / Real.sqrt s)) :=
      measurable_const.prodMk hb
    have hm : Measurable (fun z : ℝ × ℝ => ENNReal.ofReal (c⁻¹ * s ^ (-5 / 2 : ℝ)) *
        Θ (2 * z.1 / R + Real.log s) (R / Real.sqrt s) (z.2 / Real.sqrt s)) :=
      measurable_const.mul (hΘ.comp (ha.prodMk hk))
    exact lintegral_lintegral_swap
      (f := fun q η : ℝ => ENNReal.ofReal (c⁻¹ * s ^ (-5 / 2 : ℝ)) *
          Θ (2 * q / R + Real.log s) (R / Real.sqrt s) (η / Real.sqrt s))
      hm.aemeasurable
  have hprod : ∫⁻ p in {s : ℝ | 0 < s ∧ lo < R / Real.sqrt s} ×ˢ qCell c,
        ENNReal.ofReal (c⁻¹ * p.1 ^ (-5 / 2 : ℝ)) *
          Θ (chartTau R p) (R / Real.sqrt p.1) (p.2.2 / Real.sqrt p.1)
      = ∫⁻ s in {s : ℝ | 0 < s ∧ lo < R / Real.sqrt s}, ∫⁻ η : ℝ, ∫⁻ q in Ico (-c / 2) (c / 2),
        ENNReal.ofReal (c⁻¹ * s ^ (-5 / 2 : ℝ)) *
          Θ (2 * q / R + Real.log s) (R / Real.sqrt s) (η / Real.sqrt s) := by
    rw [Measure.volume_eq_prod ℝ (ℝ × ℝ), setLIntegral_prod _ hfm.aemeasurable]
    refine setLIntegral_congr_fun hS (fun s _ => ?_)
    exact (inner s).trans (swapQE s)
  rw [← lintegral_indicator hS', lintegral_ageμ hc _ (hG.indicator hS'), hF,
    setLIntegral_indicator hS', hset, hprod]

/-- **The chart change of variables** (source 2666-2668), assembled from `ChartChangeSE` and
`ChartChangeTQ`: `ρ dρ dt = (R²/2) s^{-5/2} ds dη`, `dτ = (2/R) dq`, and `ageμ c (-5/2)` has
density `c⁻¹ s^{-5/2}` on `(0,∞) × qCell c`. -/
theorem chartChange_of (hSE : ChartChangeSE) (hTQ : ChartChangeTQ) : ChartChange := by
  intro R c lo hR hc hlo Θ hΘ hper
  have hc0 : c ≠ 0 := hc.ne'
  have hS : MeasurableSet {s : ℝ | 0 < s ∧ lo < R / Real.sqrt s} :=
    measurableSet_Ioi.inter
      (measurableSet_lt measurable_const (measurable_const.div Real.continuous_sqrt.measurable))
  rw [chart_rhs R c lo hR hc Θ hΘ]
  -- joint measurability of the `τ`-integrand, in `((τ, s), η)`
  have hH : Measurable (fun w : (ℝ × ℝ) × ℝ => ENNReal.ofReal (w.1.2 ^ (-5 / 2 : ℝ)) *
      Θ w.1.1 (R / Real.sqrt w.1.2) (w.2 / Real.sqrt w.1.2)) := by
    have hA : Measurable (fun w : (ℝ × ℝ) × ℝ => ENNReal.ofReal (w.1.2 ^ (-5 / 2 : ℝ))) :=
      ENNReal.measurable_ofReal.comp ((measurable_snd.comp measurable_fst).pow_const _)
    have ha : Measurable (fun w : (ℝ × ℝ) × ℝ => w.1.1) := measurable_fst.comp measurable_fst
    have hb : Measurable (fun w : (ℝ × ℝ) × ℝ => R / Real.sqrt w.1.2) :=
      measurable_const.div (Real.continuous_sqrt.measurable.comp (measurable_snd.comp measurable_fst))
    have hc' : Measurable (fun w : (ℝ × ℝ) × ℝ => w.2 / Real.sqrt w.1.2) :=
      measurable_snd.div (Real.continuous_sqrt.measurable.comp (measurable_snd.comp measurable_fst))
    have hB : Measurable (fun w : (ℝ × ℝ) × ℝ =>
        Θ w.1.1 (R / Real.sqrt w.1.2) (w.2 / Real.sqrt w.1.2)) :=
      hΘ.comp (ha.prodMk (hb.prodMk hc'))
    exact hA.mul hB
  -- the same at fixed `s`, in `(τ, η)`
  have hHs : ∀ s : ℝ, Measurable (fun z : ℝ × ℝ => ENNReal.ofReal (s ^ (-5 / 2 : ℝ)) *
      Θ z.1 (R / Real.sqrt s) (z.2 / Real.sqrt s)) := by
    intro s
    have hk : Measurable (fun z : ℝ × ℝ => (z.1, (R / Real.sqrt s, z.2 / Real.sqrt s))) :=
      measurable_fst.prodMk
        ((measurable_const : Measurable fun _ : ℝ × ℝ => R / Real.sqrt s).prodMk
          (measurable_snd.div_const _))
    exact (measurable_const.mul (hΘ.comp hk))
  -- the phase change at fixed `(s, η)`
  have hTQ' : ∀ s η : ℝ, ∫⁻ τ in Ico (0 : ℝ) (2 * c / R), Θ τ (R / Real.sqrt s) (η / Real.sqrt s)
      = ENNReal.ofReal (2 / R) * ∫⁻ q in Ico (-c / 2) (c / 2),
          Θ (2 * q / R + Real.log s) (R / Real.sqrt s) (η / Real.sqrt s) := by
    intro s η
    have hk : Measurable (fun τ : ℝ => (τ, (R / Real.sqrt s, η / Real.sqrt s))) :=
      measurable_id.prodMk (measurable_const : Measurable fun _ : ℝ => (R / Real.sqrt s, η / Real.sqrt s))
    have hΞm : Measurable (fun τ : ℝ => Θ τ (R / Real.sqrt s) (η / Real.sqrt s)) :=
      hΘ.comp hk
    exact hTQ R c hR hc _ hΞm (fun τ => hper τ _ _) (Real.log s)
  -- Tonelli in `(τ, s)`
  have hswap1 : ∫⁻ τ in Ico (0 : ℝ) (2 * c / R), ∫⁻ s in {s : ℝ | 0 < s ∧ lo < R / Real.sqrt s},
        ∫⁻ η : ℝ, ENNReal.ofReal (s ^ (-5 / 2 : ℝ)) * Θ τ (R / Real.sqrt s) (η / Real.sqrt s)
      = ∫⁻ s in {s : ℝ | 0 < s ∧ lo < R / Real.sqrt s},
        ∫⁻ τ in Ico (0 : ℝ) (2 * c / R), ∫⁻ η : ℝ,
          ENNReal.ofReal (s ^ (-5 / 2 : ℝ)) * Θ τ (R / Real.sqrt s) (η / Real.sqrt s) :=
    lintegral_lintegral_swap
      (f := fun τ s : ℝ => ∫⁻ η : ℝ, ENNReal.ofReal (s ^ (-5 / 2 : ℝ)) *
          Θ τ (R / Real.sqrt s) (η / Real.sqrt s))
      (hH.lintegral_prod_right').aemeasurable
  -- at fixed `s`: Tonelli in `(τ, η)`, then the phase change
  have L4 : ∀ s : ℝ, ∫⁻ τ in Ico (0 : ℝ) (2 * c / R), ∫⁻ η : ℝ,
        ENNReal.ofReal (s ^ (-5 / 2 : ℝ)) * Θ τ (R / Real.sqrt s) (η / Real.sqrt s)
      = ∫⁻ η : ℝ, ENNReal.ofReal (s ^ (-5 / 2 : ℝ)) * (ENNReal.ofReal (2 / R) *
          ∫⁻ q in Ico (-c / 2) (c / 2),
            Θ (2 * q / R + Real.log s) (R / Real.sqrt s) (η / Real.sqrt s)) := by
    intro s
    rw [lintegral_lintegral_swap
      (f := fun τ η : ℝ => ENNReal.ofReal (s ^ (-5 / 2 : ℝ)) *
          Θ τ (R / Real.sqrt s) (η / Real.sqrt s))
      (hHs s).aemeasurable]
    refine lintegral_congr (fun η => ?_)
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hTQ' s η]
  -- the constants: `(R²/2)(2/R) = R` and `R c · c⁻¹ = R`
  have key : ∀ s η : ℝ,
      ENNReal.ofReal (R ^ 2 / 2) * (ENNReal.ofReal (s ^ (-5 / 2 : ℝ)) *
        (ENNReal.ofReal (2 / R) * ∫⁻ q in Ico (-c / 2) (c / 2),
          Θ (2 * q / R + Real.log s) (R / Real.sqrt s) (η / Real.sqrt s)))
      = ENNReal.ofReal (R * c) * ∫⁻ q in Ico (-c / 2) (c / 2),
          ENNReal.ofReal (c⁻¹ * s ^ (-5 / 2 : ℝ)) *
            Θ (2 * q / R + Real.log s) (R / Real.sqrt s) (η / Real.sqrt s) := by
    intro s η
    have e1 : ENNReal.ofReal (R ^ 2 / 2) * ENNReal.ofReal (2 / R) = ENNReal.ofReal R := by
      rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ R ^ 2 / 2 by positivity)]
      congr 1
      field_simp
    have e2 : ENNReal.ofReal (R * c) * ENNReal.ofReal (c⁻¹ * s ^ (-5 / 2 : ℝ))
        = ENNReal.ofReal R * ENNReal.ofReal (s ^ (-5 / 2 : ℝ)) := by
      rw [← ENNReal.ofReal_mul (mul_pos hR hc).le, ← ENNReal.ofReal_mul hR.le]
      congr 1
      field_simp
    calc ENNReal.ofReal (R ^ 2 / 2) * (ENNReal.ofReal (s ^ (-5 / 2 : ℝ)) *
          (ENNReal.ofReal (2 / R) * ∫⁻ q in Ico (-c / 2) (c / 2),
            Θ (2 * q / R + Real.log s) (R / Real.sqrt s) (η / Real.sqrt s)))
        = (ENNReal.ofReal (R ^ 2 / 2) * ENNReal.ofReal (2 / R)) *
          (ENNReal.ofReal (s ^ (-5 / 2 : ℝ)) * ∫⁻ q in Ico (-c / 2) (c / 2),
            Θ (2 * q / R + Real.log s) (R / Real.sqrt s) (η / Real.sqrt s)) := by ring
      _ = ENNReal.ofReal R * (ENNReal.ofReal (s ^ (-5 / 2 : ℝ)) * ∫⁻ q in Ico (-c / 2) (c / 2),
            Θ (2 * q / R + Real.log s) (R / Real.sqrt s) (η / Real.sqrt s)) := by rw [e1]
      _ = (ENNReal.ofReal (R * c) * ENNReal.ofReal (c⁻¹ * s ^ (-5 / 2 : ℝ))) *
          ∫⁻ q in Ico (-c / 2) (c / 2),
            Θ (2 * q / R + Real.log s) (R / Real.sqrt s) (η / Real.sqrt s) := by rw [e2]; ring
      _ = ENNReal.ofReal (R * c) * ∫⁻ q in Ico (-c / 2) (c / 2),
          ENNReal.ofReal (c⁻¹ * s ^ (-5 / 2 : ℝ)) *
            Θ (2 * q / R + Real.log s) (R / Real.sqrt s) (η / Real.sqrt s) := by
        rw [lintegral_const_mul' (ENNReal.ofReal (c⁻¹ * s ^ (-5 / 2 : ℝ))) _
          ENNReal.ofReal_ne_top]
        ring
  -- the `τ`-integral of the left side, step by step
  have step1 : ∀ τ : ℝ, ∫⁻ ρ in Ioi lo, ∫⁻ t : ℝ, ENNReal.ofReal ρ * Θ τ ρ t
      = ENNReal.ofReal (R ^ 2 / 2) * ∫⁻ s in {s : ℝ | 0 < s ∧ lo < R / Real.sqrt s},
          ∫⁻ η : ℝ, ENNReal.ofReal (s ^ (-5 / 2 : ℝ)) * Θ τ (R / Real.sqrt s) (η / Real.sqrt s) := by
    intro τ
    have hk : Measurable (fun u : ℝ × ℝ => ((τ, u) : ℝ × (ℝ × ℝ))) :=
      (measurable_const : Measurable fun _ : ℝ × ℝ => τ).prodMk measurable_id
    have hm : Measurable (fun u : ℝ × ℝ => Θ τ u.1 u.2) := hΘ.comp hk
    exact hSE R lo hR hlo (fun ρ t => Θ τ ρ t) hm
  calc ∫⁻ τ in Ico (0 : ℝ) (2 * c / R), ∫⁻ ρ in Ioi lo, ∫⁻ t : ℝ, ENNReal.ofReal ρ * Θ τ ρ t
      = ∫⁻ τ in Ico (0 : ℝ) (2 * c / R), ENNReal.ofReal (R ^ 2 / 2) *
          ∫⁻ s in {s : ℝ | 0 < s ∧ lo < R / Real.sqrt s},
            ∫⁻ η : ℝ, ENNReal.ofReal (s ^ (-5 / 2 : ℝ)) * Θ τ (R / Real.sqrt s) (η / Real.sqrt s) :=
        lintegral_congr step1
    _ = ENNReal.ofReal (R ^ 2 / 2) * ∫⁻ τ in Ico (0 : ℝ) (2 * c / R),
          ∫⁻ s in {s : ℝ | 0 < s ∧ lo < R / Real.sqrt s},
            ∫⁻ η : ℝ, ENNReal.ofReal (s ^ (-5 / 2 : ℝ)) * Θ τ (R / Real.sqrt s) (η / Real.sqrt s) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (R ^ 2 / 2) * ∫⁻ s in {s : ℝ | 0 < s ∧ lo < R / Real.sqrt s},
          ∫⁻ τ in Ico (0 : ℝ) (2 * c / R), ∫⁻ η : ℝ,
            ENNReal.ofReal (s ^ (-5 / 2 : ℝ)) * Θ τ (R / Real.sqrt s) (η / Real.sqrt s) := by
        rw [hswap1]
    _ = ENNReal.ofReal (R ^ 2 / 2) * ∫⁻ s in {s : ℝ | 0 < s ∧ lo < R / Real.sqrt s},
          ∫⁻ η : ℝ, ENNReal.ofReal (s ^ (-5 / 2 : ℝ)) * (ENNReal.ofReal (2 / R) *
            ∫⁻ q in Ico (-c / 2) (c / 2),
              Θ (2 * q / R + Real.log s) (R / Real.sqrt s) (η / Real.sqrt s)) :=
        congrArg _ (setLIntegral_congr_fun hS (fun s _ => L4 s))
    _ = ∫⁻ s in {s : ℝ | 0 < s ∧ lo < R / Real.sqrt s}, ∫⁻ η : ℝ,
          ENNReal.ofReal (R ^ 2 / 2) * (ENNReal.ofReal (s ^ (-5 / 2 : ℝ)) * (ENNReal.ofReal (2 / R) *
            ∫⁻ q in Ico (-c / 2) (c / 2),
              Θ (2 * q / R + Real.log s) (R / Real.sqrt s) (η / Real.sqrt s))) := by
        rw [← lintegral_const_mul' (ENNReal.ofReal (R ^ 2 / 2)) _ ENNReal.ofReal_ne_top]
        exact lintegral_congr fun s => by
          rw [lintegral_const_mul' (ENNReal.ofReal (R ^ 2 / 2)) _ ENNReal.ofReal_ne_top]
    _ = ∫⁻ s in {s : ℝ | 0 < s ∧ lo < R / Real.sqrt s}, ∫⁻ η : ℝ,
          ENNReal.ofReal (R * c) * ∫⁻ q in Ico (-c / 2) (c / 2),
            ENNReal.ofReal (c⁻¹ * s ^ (-5 / 2 : ℝ)) *
              Θ (2 * q / R + Real.log s) (R / Real.sqrt s) (η / Real.sqrt s) :=
        setLIntegral_congr_fun hS (fun s _ => lintegral_congr (fun η => key s η))
    _ = ENNReal.ofReal (R * c) * ∫⁻ s in {s : ℝ | 0 < s ∧ lo < R / Real.sqrt s}, ∫⁻ η : ℝ,
          ∫⁻ q in Ico (-c / 2) (c / 2),
            ENNReal.ofReal (c⁻¹ * s ^ (-5 / 2 : ℝ)) *
              Θ (2 * q / R + Real.log s) (R / Real.sqrt s) (η / Real.sqrt s) :=
        (lintegral_congr (fun s => lintegral_const_mul' (ENNReal.ofReal (R * c)) _
            ENNReal.ofReal_ne_top)).trans
          (lintegral_const_mul' (ENNReal.ofReal (R * c)) _ ENNReal.ofReal_ne_top)

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
