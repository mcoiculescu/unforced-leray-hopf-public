import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.OldMeasureAC

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Transverse weight integral** (source 4934-4936): for `m_Z > 3/2` (indeed `> 1/2` suffices)
there is `C` with `∫ W⁻² davgμ_c(q,η) ≤ C √(1+u)` for all `u ≥ 0`, `c > 0`, where
`W² = (1 + η²/(1+u))^{m_Z}` (`transWeight`).  The `q`-factor of `avgμ c` is a probability
measure; scale `η = √(1+u) t` and use integrability of `(1+t²)^{-m_Z}`. -/
def SLTrans (mZ : ℝ) : Prop :=
  3 / 2 < mZ → ∃ C : ℝ, ∀ c : ℝ, 0 < c → ∀ u : ℝ, 0 ≤ u →
    ∫⁻ x : ℝ × ℝ, ENNReal.ofReal ((UnforcedLeray.Short.IIIa.transWeight mZ (u, x) ^ 2)⁻¹)
      ∂(Cyl.avgμ c) ≤ ENNReal.ofReal (C * Real.sqrt (1 + u))

/-- **Cauchy-Schwarz bound for `N₀`** (source 4924-4936): with `g⁻¹ = ginv`,
`u^{-3/2}|M| = (g⁻¹ W u^{-1/4}|M|)(g W⁻¹ u^{-5/4})`; the first factor has `L²(oldMeasure)` norm
at most `‖T‖` (the `gainZ1Measure` density `g⁻² W² u^{-1/2}` dominates on `u > 6/(5ν)`), the
second has square-integral `≤ e^{2γ/ν}·C` by `SLTrans` and `∫_{6/(5ν)}^∞ u^{-5/2}√(1+u) du ≤ 2`
(`ν ≤ 1`).  Stated in the lower-integral (`lintegral`) form. -/
def SLLint (mZ γ : ℝ) : Prop :=
  3 / 2 < mZ → 0 < γ → ∃ C : ℝ, ∀ (c ν ρb : ℝ), 0 < c → 0 < ν → ν ≤ 1 →
    ∀ T : StrG c mZ ρb γ ν,
      ∫⁻ p : Chart, ENNReal.ofReal (p.1 ^ (-(3 / 2 : ℝ)) * frob (thinRep T p))
        ∂(oldMeasure c ν) ≤ ENNReal.ofReal (C * Real.exp (γ / ν) * ‖T‖)

/-- Measurability of the thin representative on the old region. -/
theorem thinRep_aemeasurable {c mZ ρb γ ν : ℝ} (hν : 0 < ν) (T : StrG c mZ ρb γ ν) :
    AEStronglyMeasurable (thinRep T) (oldMeasure c ν) := by
  have h1 : AEStronglyMeasurable (fun p : Chart => ((WithLp.ofLp T).1 : Chart → Ten3) p)
      (gainZ1Measure c mZ γ ν) := (Lp.aestronglyMeasurable _)
  have h2 := h1.mono_ac (oldMeasureAC c mZ γ ν hν)
  have hc : Continuous (Ten3.toMatrix) := by
    unfold Ten3.toMatrix
    refine continuous_pi fun a => continuous_pi fun b => ?_
    exact (EuclideanSpace.proj (𝕜 := ℝ) (a, b)).continuous
  exact hc.comp_aestronglyMeasurable h2

theorem frob_continuous : Continuous frob := by
  unfold frob
  fun_prop

theorem ae_old_pos (c ν : ℝ) : ∀ᵐ p ∂(oldMeasure c ν), (6 / 5 / ν) < p.1 := by
  unfold oldMeasure
  exact (Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Ioi (6 / 5 / ν)))
    (ν := Cyl.avgμ c)).ae (ae_restrict_mem measurableSet_Ioi)

/-- `N₀` is finite and bounded, given the Cauchy-Schwarz lower-integral bound `SLLint`. -/
theorem sourceLN0_of {mZ γ : ℝ} (h : SLLint mZ γ) : SourceLN0 mZ γ := by
  intro hm hγ
  obtain ⟨C, hC⟩ := h hm hγ
  refine ⟨max C 0, 0, ?_⟩
  intro c ν ρb hc hν hν1 T
  have hbd := hC c ν ρb hc hν hν1 T
  have hbd' : ∫⁻ p : Chart, ENNReal.ofReal (p.1 ^ (-(3 / 2 : ℝ)) * frob (thinRep T p))
        ∂(oldMeasure c ν) ≤ ENNReal.ofReal (max C 0 * Real.exp (γ / ν) * ‖T‖) :=
    hbd.trans (ENNReal.ofReal_le_ofReal (by
      have : 0 ≤ Real.exp (γ / ν) * ‖T‖ := by positivity
      nlinarith [le_max_left C 0]))
  have hmeas : AEStronglyMeasurable (fun p : Chart => p.1 ^ (-(3 / 2 : ℝ)) * frob (thinRep T p))
      (oldMeasure c ν) := by
    have h1 : AEStronglyMeasurable (fun p : Chart => frob (thinRep T p)) (oldMeasure c ν) :=
      frob_continuous.comp_aestronglyMeasurable (thinRep_aemeasurable hν T)
    exact ((measurable_fst.pow_const _).aestronglyMeasurable).mul h1
  have hnn : 0 ≤ᵐ[oldMeasure c ν] fun p : Chart => p.1 ^ (-(3 / 2 : ℝ)) * frob (thinRep T p) := by
    filter_upwards [ae_old_pos c ν] with p hp
    have : 0 < p.1 := lt_trans (by positivity) hp
    have : 0 ≤ frob (thinRep T p) := Real.sqrt_nonneg _
    positivity
  have hint : Integrable (fun p : Chart => p.1 ^ (-(3 / 2 : ℝ)) * frob (thinRep T p))
      (oldMeasure c ν) := by
    refine ⟨hmeas, ?_⟩
    unfold HasFiniteIntegral
    calc ∫⁻ p, ‖p.1 ^ (-(3 / 2 : ℝ)) * frob (thinRep T p)‖ₑ ∂(oldMeasure c ν)
        = ∫⁻ p, ENNReal.ofReal (p.1 ^ (-(3 / 2 : ℝ)) * frob (thinRep T p)) ∂(oldMeasure c ν) := by
          refine lintegral_congr_ae ?_
          filter_upwards [hnn] with p hp
          rw [Real.enorm_eq_ofReal hp]
      _ < ∞ := lt_of_le_of_lt hbd' ENNReal.ofReal_lt_top
  refine ⟨⟨thinRep_aemeasurable hν T, hint⟩, ?_⟩
  have hEq : oldN0 c ν (thinRep T) =
      ∫ p, p.1 ^ (-(3 / 2 : ℝ)) * frob (thinRep T p) ∂(oldMeasure c ν) := by
    unfold oldN0
    haveI : SFinite (Cyl.avgμ c) := by
      unfold Cyl.avgμ
      infer_instance
    have hprod : oldMeasure c ν = (volume.restrict (Ioi (6 / 5 / ν))).prod (Cyl.avgμ c) := rfl
    rw [hprod, integral_prod _ (hprod ▸ hint)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only
    rw [integral_const_mul]
  rw [hEq, integral_eq_lintegral_of_nonneg_ae hnn hmeas]
  have hb : 0 ≤ max C 0 * Real.exp (γ / ν) * ‖T‖ := by positivity
  calc (∫⁻ p, ENNReal.ofReal (p.1 ^ (-(3 / 2 : ℝ)) * frob (thinRep T p)) ∂(oldMeasure c ν)).toReal
      ≤ (ENNReal.ofReal (max C 0 * Real.exp (γ / ν) * ‖T‖)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hbd'
    _ = max C 0 * Real.exp (γ / ν) * ‖T‖ := ENNReal.toReal_ofReal hb
    _ = max C 0 * (ν⁻¹ ^ 0) * Real.exp (γ / ν) * ‖T‖ := by simp

end UnforcedLeray.Short.PartIIIb.Concrete
