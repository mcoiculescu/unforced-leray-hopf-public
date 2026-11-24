import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F09_1
import UnforcedLeray.Units.B0421.Phase
import UnforcedLeray.Units.B0411
import UnforcedLeray.Units.B0419
import UnforcedLeray.Lib.Semigroups.Adjoint

/-!
# Part II-a, audit decomposition of `PartII-a:F09/1/3`

Source `the November 2 reference manuscript` lines 1359-1361, 1403-1413, 1426-1440.
`adjResolventEquation_of` reduces `AdjResolventEquation` to the adjoint generator identity on
phase tests `AdjTestGen`, which in turn follows from the Taylor expansion `AdjPhaseTaylor`
(the mirror of `PhaseAdjointTaylor`, forward free action on tests) by `AdjTestGenOfTaylor`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- `L₀` maps phase tests to phase tests (`L₀ = T₀ - νΔ - ½`, untransposed). -/
theorem isPhaseTest_L0' {P : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) (ν : ℝ) :
    IsPhaseTest P (L0 ν Φ) := by
  have e : L0 ν Φ = (dτ Φ - (1 / 2 : ℝ) • radialT Φ) - ν • lapT Φ - (1 / 2 : ℂ) • Φ := by
    funext p
    simp only [L0, T0, Pi.sub_apply, Pi.smul_apply]
    module
  rw [e]
  exact ((hΦ.dτ.sub (hΦ.radialT.const_smul _)).sub (hΦ.lapT.const_smul ν)).sub
    (hΦ.const_smul _)

/-- **The adjoint generator on phase tests (leaf, not proved here).** For every phase test `Φ`,
`ν > 0` and `x ∈ Y_2`, the right derivative at `0` of `t ↦ ⟪Φ, S(t)^* x⟫` equals `-⟪L₀Φ, x⟫`,
where `S(t)^* = adjT P ν t` is the Hilbert adjoint of the phase semigroup. -/
def AdjTestGen : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (ν : ℝ), 0 < ν → ∀ Φ : ℝ × Space → CVec3, IsPhaseTest P Φ →
    ∀ x : Yq P 2, Tendsto (fun t : ℝ => (t⁻¹ : ℝ) • (phasePair P 2 Φ (adjT P ν t x) -
      phasePair P 2 Φ x)) (𝓝[>] 0) (𝓝 (-(phasePair P 2 (L0 ν Φ) x)))

/-- **Reduction of `PartII-a:F09/1/3` to the leaf `AdjTestGen`.** The Laplace transform of the
adjoint semigroup solves the adjoint equation in distributions, by the same argument as
`F02.hasPhaseOp_laplace`. -/
theorem adjResolventEquation_of_gen (hG : AdjTestGen) : AdjResolventEquation := by
  intro P _ ν hν μ hμ Rm hRm f
  let S : UnforcedLeray.Infra.ExpSemigroup (Yq P 2) :=
    UnforcedLeray.B0421.phaseSemigroup (P := P) (q := 2) ENNReal.ofNat_ne_top hν.le 1 zero_le_one
      (fun r _ => by
        rw [one_mul]
        exact UnforcedLeray.B0421.norm_freeC_two_le ν r)
  have hωval : S.adjoint.ω = -(1 / 4 : ℝ) := by
    show -UnforcedLeray.B0418.gammaExp 2 = -(1 / 4 : ℝ)
    rw [UnforcedLeray.B0419.gammaExp_two]
  have hω : S.adjoint.ω < ((starRingEnd ℂ) μ).re := by
    rw [hωval, Complex.conj_re]
    linarith
  have hz : Rm f = S.adjoint.laplace ((starRingEnd ℂ) μ) f := by
    rw [hRm f, S.adjoint.laplace_apply hω]
    rfl
  rw [hz]
  intro Φ hΦ
  -- auxiliary functions of the Laplace reduction
  set I : ℝ → Yq P 2 := fun t => ∫ r in (0 : ℝ)..t, S.adjoint.lapInt ((starRingEnd ℂ) μ) f r
    with hI
  set g : ℝ → Yq P 2 := fun t =>
    Complex.exp (((starRingEnd ℂ) μ) * t) •
      (S.adjoint.laplace ((starRingEnd ℂ) μ) f - I t) with hg
  have hI' : HasDerivWithinAt I (S.adjoint.lapInt ((starRingEnd ℂ) μ) f 0) (Ici 0) 0 := by
    have hc := S.adjoint.continuousOn_lapInt ((starRingEnd ℂ) μ) f
    exact intervalIntegral.integral_hasDerivWithinAt_right (s := Ici 0) (t := Ioi 0)
      IntervalIntegrable.refl
      ((hc.mono Ioi_subset_Ici_self).stronglyMeasurableAtFilter_nhdsWithin measurableSet_Ioi 0)
      ((hc 0 Set.self_mem_Ici).mono Ioi_subset_Ici_self)
  have hlap0 : S.adjoint.lapInt ((starRingEnd ℂ) μ) f 0 = f := by
    have h0 : ContinuousLinearMap.adjoint (S.T 0) = 1 := by
      rw [S.T_zero, ContinuousLinearMap.adjoint_one]
    simp [UnforcedLeray.Infra.ExpSemigroup.lapInt_def, UnforcedLeray.Infra.ExpSemigroup.adjoint_T, h0]
  have hI0 : I 0 = 0 := by simp [hI]
  have hg' : HasDerivWithinAt g (((starRingEnd ℂ) μ) •
      S.adjoint.laplace ((starRingEnd ℂ) μ) f - f) (Ici 0) 0 := by
    have hexp := (UnforcedLeray.Infra.ExpSemigroup.hasDerivAt_cexp_mul
      ((starRingEnd ℂ) μ) 0).hasDerivWithinAt (s := Ici 0)
    have hsub := (hasDerivWithinAt_const (0 : ℝ) (Ici 0)
      (S.adjoint.laplace ((starRingEnd ℂ) μ) f)).sub hI'
    have hprod := hexp.smul hsub
    refine hprod.congr_deriv ?_
    rw [hlap0]
    simp [Pi.sub_apply, hI0]
    abel
  have hG' : HasDerivWithinAt (fun t => phasePair P 2 Φ (g t))
      (phasePair P 2 Φ (((starRingEnd ℂ) μ) • S.adjoint.laplace ((starRingEnd ℂ) μ) f - f))
      (Ici 0) 0 :=
    ((phasePair P 2 Φ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt 0 hg'
  have hA := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl (0 : ℝ))).1
    (hG'.mono Ioi_subset_Ici_self)
  have hg0 : g 0 = S.adjoint.laplace ((starRingEnd ℂ) μ) f := by simp [hg, hI0]
  have hA' : Tendsto (fun t : ℝ => (t⁻¹ : ℝ) • (phasePair P 2 Φ
      (S.adjoint.T t (S.adjoint.laplace ((starRingEnd ℂ) μ) f)) -
      phasePair P 2 Φ (S.adjoint.laplace ((starRingEnd ℂ) μ) f)))
      (𝓝[>] 0) (𝓝 (phasePair P 2 Φ (((starRingEnd ℂ) μ) •
        S.adjoint.laplace ((starRingEnd ℂ) μ) f - f))) := by
    refine hA.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
    rw [slope_def_module, sub_zero, hg0]
    congr 2
    rw [S.adjoint.T_laplace_apply hω ht0 f]
    rfl
  have hB : Tendsto (fun t : ℝ => (t⁻¹ : ℝ) • (phasePair P 2 Φ
      (S.adjoint.T t (S.adjoint.laplace ((starRingEnd ℂ) μ) f)) -
      phasePair P 2 Φ (S.adjoint.laplace ((starRingEnd ℂ) μ) f)))
      (𝓝[>] 0) (𝓝 (-(phasePair P 2 (L0 ν Φ) (S.adjoint.laplace ((starRingEnd ℂ) μ) f)))) :=
    hG P ν hν Φ hΦ _
  have heq := tendsto_nhds_unique hA' hB
  rw [map_sub, map_smul, smul_eq_mul] at heq
  show phasePair P 2 (((starRingEnd ℂ) μ) • Φ + L0 ν Φ)
      (S.adjoint.laplace ((starRingEnd ℂ) μ) f) = phasePair P 2 Φ f
  rw [phasePair_add (hΦ.const_smul _) (isPhaseTest_L0' hΦ ν), phasePair_const_smul hΦ ((starRingEnd ℂ) μ)]
  linear_combination heq


/-- **Taylor expansion of the adjoint phase semigroup on a phase test** (lines 1403-1413): for a
phase test `Φ`, `ν > 0` there is `C` such that for `0 < s ≤ 1` some `ψs ∈ Y_2` represents
`x ↦ ⟪Φ, S(s)^* x⟫` (i.e. `phasePair P 2 Φ (adjT P ν s x) = phasePairing P 2 ψs x`) and
`‖ψs - Φ + s L₀Φ‖_{Y_2} ≤ C s²` (`d/ds 𝒯(s)Φ|₀ = -L₀Φ`, `𝒯` commuting with complex conjugation). -/
def AdjPhaseTaylor : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (ν : ℝ), 0 < ν → ∀ Φ : ℝ × Space → CVec3, IsPhaseTest P Φ →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 < s → s ≤ 1 → ∃ ψs : Yq P (conjExp 2),
      (∀ x : Yq P 2, phasePair P 2 Φ (adjT P ν s x) = phasePairing P 2 ψs x) ∧
      ‖ψs - testElem P (conjExp 2) Φ + (s : ℂ) • testElem P (conjExp 2) (L0 ν Φ)‖ ≤ C * s ^ 2

/-- The passage from the Taylor expansion to the generator identity. -/
def AdjTestGenOfTaylor : Prop := AdjPhaseTaylor → AdjTestGen

/-- Reduction of `PartII-a:F09/1/3` to `AdjPhaseTaylor` and `AdjTestGenOfTaylor`. -/
theorem adjResolventEquation_of (h1 : AdjPhaseTaylor) (h2 : AdjTestGenOfTaylor) :
    AdjResolventEquation :=
  adjResolventEquation_of_gen (h2 h1)

end UnforcedLeray.Short.PartIIa
