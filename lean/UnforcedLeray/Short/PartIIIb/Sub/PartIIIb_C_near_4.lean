import UnforcedLeray.Short.PartIIIb.NearInst.Targets
import UnforcedLeray.Short.PartIIIa.Compose
import UnforcedLeray.Short.PartI.TrainClass
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_8

/-!
# Sub-lemmas for `PartIII-b:C/near/4` (`SplitMultBound`, source 2716, 2775-2777, 2706-2713)

Clauses 1 and 3 of `SplitMultBound` are the first clause of `IIIa.StressCoefficients`.  Clause 4
(`√s|v_b| ≤ ρ_b`) is `IIIa.repair_coeff_bound` and clause 2 for `r_b = p.corr z` follows from
the joint continuity of `p.corr z` (`IIIa.corr_continuous`).  The measurability of `chartCoeff p.R V`
for `V = U_raw + Σ α_i E_i` is reduced to the measurability of the chart coefficients of the two
fields `U_raw` and `E_i`, stated as the Props `RawChartMeasurable`, `InletChartMeasurable`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Short.IIIa

/-- **The chart coefficient of the raw lift is measurable** (source 2706, 2200-2201, 261-288):
for the BUC train of the level, `chartCoeff p.R p.raw = b_raw = (v₁, v₂ + εH)` on `s > 0`
(`IIIa.chartCoeff_raw`) and `0` for `s ≤ 0`; `b_raw` is built from `v`, `ψ` and the derivatives
`∂_η ψ`, `∂_s ψ`, which are jointly continuous on `s > 0` because the stream `ψ` of the train is
jointly smooth in `(s, q, η)` for `s > 0` (the field `IIb.BgRegime.train_stream_smooth`, source
line 397; the stream smoothness is a hypothesis of the lemma). -/
def RawChartMeasurable : Prop :=
  ∀ p : Params,
    ContDiffOn ℝ ∞ (fun x : ℝ × UnforcedLeray.Cyl.Plane => p.train.ψ x.1 x.2) (Ioi 0 ×ˢ univ) →
      Measurable (chartCoeff p.R p.raw)

/-- **The chart coefficients of the inlet columns are measurable** (source 2347-2358, 5288-5295):
`chartCoeff p.R (p.inlet i) = p.inletProfile i` on `s > 0` (`IIIa.chartCoeff_Nv`) and `0` for
`s ≤ 0`; `inletProfile i = ringStreamProfile R (χ(s)ψ_i)` is built from `fderiv` (measurable for
every function, `measurable_fderiv`) of the cut stream `χ(s) ψ_i`, with `ψ_i` the real/imaginary
part of the `c`-periodized planar stream `periodicStream p.mode p.c` (a convergent series of
continuous terms, decaying like `r⁻²`). -/
def InletChartMeasurable : Prop :=
  ∀ (p : Params) (i : Fin 2), Measurable (chartCoeff p.R (p.inlet i))

/-- The chart coefficient of a jointly continuous field is measurable. -/
theorem measurable_chartCoeff_of_continuous (R : ℝ) {F : ℝ → EuclideanSpace ℝ (Fin 3) →
    EuclideanSpace ℝ (Fin 3)} (hF : Continuous fun x : ℝ × EuclideanSpace ℝ (Fin 3) => F x.1 x.2) :
    Measurable (chartCoeff R F) := by
  have hy : Measurable fun pt : ℝ × (ℝ × ℝ) =>
      (!₂[R / Real.sqrt pt.1, 0, pt.2.2 / Real.sqrt pt.1] : EuclideanSpace ℝ (Fin 3)) := by
    refine (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp ?_
    refine measurable_pi_lambda _ (fun i => ?_)
    fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero]
      exact measurable_const.div (Real.continuous_sqrt.measurable.comp measurable_fst)
    · simp
    · simp only [Fin.reduceFinMk, Matrix.cons_val]
      exact (measurable_snd.comp measurable_snd).div (Real.continuous_sqrt.measurable.comp measurable_fst)
  have hτ : Measurable fun pt : ℝ × (ℝ × ℝ) => 2 * pt.2.1 / R + Real.log pt.1 := by
    fun_prop
  have hFm : Measurable fun pt : ℝ × (ℝ × ℝ) =>
      F (2 * pt.2.1 / R + Real.log pt.1)
        (!₂[R / Real.sqrt pt.1, 0, pt.2.2 / Real.sqrt pt.1] : EuclideanSpace ℝ (Fin 3)) :=
    hF.measurable.comp (hτ.prodMk hy)
  have hc : ∀ j : Fin 3, Measurable fun pt : ℝ × (ℝ × ℝ) =>
      F (2 * pt.2.1 / R + Real.log pt.1)
        (!₂[R / Real.sqrt pt.1, 0, pt.2.2 / Real.sqrt pt.1] : EuclideanSpace ℝ (Fin 3)) j :=
    fun j => (measurable_pi_apply j).comp ((PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp hFm)
  unfold chartCoeff
  refine Measurable.smul (Real.continuous_sqrt.measurable.comp measurable_fst).inv ?_
  refine (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).measurable.comp ?_
  refine measurable_pi_lambda _ (fun i => ?_)
  fin_cases i
  · exact hc 0
  · exact hc 2

/-- **`PartIII-b:C/near/4`, conditional form.** -/
theorem splitMultBound_of_sub (hSC : UnforcedLeray.Short.IIIa.StressCoefficients)
    (hI : InletChartMeasurable) (hR : RawChartMeasurable) : SplitMultBound := by
  intro dm dp hdm m0 C0 k0 hm0 hm0le hC0 mZ hmZ Sig lam q hSig hq
  obtain ⟨C, k, ν₀, hν₀, h⟩ := hSC dm dp hdm m0 C0 k0 hm0 hm0le mZ hmZ Sig lam q hSig hq
  refine ⟨C, k, min ν₀ (dm ^ 3 / 12), lt_min hν₀ (by positivity), ?_⟩
  intro p d hBG hν hSg hmode S_in V rb hsplit
  have hνa : p.ν ≤ ν₀ := hν.trans (min_le_left _ _)
  have hP1 := period_le_one_of_small hBG (hν.trans (min_le_right _ _))
  have hc1 := (h p d hBG hνa hSg hmode S_in V rb hsplit).1
  obtain ⟨z, -, hV, hrb, -⟩ := hsplit.state
  have hρ : 0 ≤ UnforcedLeray.Short.IIb.rhoB p m0 C0 k0 := by
    unfold UnforcedLeray.Short.IIb.rhoB
    have := p.ε_pos
    have := p.ν_pos
    positivity
  refine ⟨?_, ?_, hc1, ?_⟩
  · have hVeq : V = fun t y => p.raw t y + p.coord z 0 • p.inlet 0 t y +
        p.coord z 1 • p.inlet 1 t y := by
      funext t y
      rw [hV t y, Fin.sum_univ_two, add_assoc]
    have hfun : chartCoeff p.R V = fun pt => chartCoeff p.R p.raw pt +
        p.coord z 0 • chartCoeff p.R (p.inlet 0) pt +
        p.coord z 1 • chartCoeff p.R (p.inlet 1) pt := by
      funext pt
      rw [hVeq]
      exact chartCoeff_sum2 p.R _ _ _ _ _ pt
    rw [hfun]
    have h0 := hR p hBG.train_stream_smooth
    have h1 : Measurable fun pt => p.coord z 0 • chartCoeff p.R (p.inlet 0) pt :=
      Measurable.const_smul (hI p 0) (p.coord z 0)
    have h2 : Measurable fun pt => p.coord z 1 • chartCoeff p.R (p.inlet 1) pt :=
      Measurable.const_smul (hI p 1) (p.coord z 1)
    exact Measurable.add (Measurable.add h0 h1) h2
  · apply measurable_chartCoeff_of_continuous
    rw [hrb]
    exact corr_continuous p hP1 z
  · filter_upwards [ae_pos_ageμ p.c (-1 / 2)] with pt hpt
    exact repair_coeff_bound hP1 hρ hsplit pt hpt

end UnforcedLeray.Short.PartIIIb.NearInst
