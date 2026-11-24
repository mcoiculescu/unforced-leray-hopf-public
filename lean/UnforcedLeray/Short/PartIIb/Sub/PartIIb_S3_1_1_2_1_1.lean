import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S3_1_1_2_1

/-!
# Sub-module for `PartII-b:S3/1/1/2/1/1`: Raw and inlet coordinate-jet radial drift in `L⁴(ℝ³)`

Source of record: `the November 2 reference manuscript`
(SP), lines 438-467, 1305-1325, 2543-2559, 2594-2610.

Reduces `RawAndInletCoordJetRadialDriftL4` (`Sub/PartII-b_S3_1_1_2_1.lean`, lines 563-581) via
`RadialDriftL4Sub.eLpNorm_spatialRadialDrift_dirSpatialJet_le_of_inv_sq_decay` to the all-order
inverse-square spatial derivative decay bounds:
- `RawIteratedInvSqDecay` (`PartII-b:S3/1/1/2/1/1/1`):
  `‖iteratedFDeriv ℝ (k + 1) (p.raw τ) y‖ ≤ C * ((1 + ‖y‖) ^ 2)⁻¹`
- `InletIteratedInvSqDecay` (`PartII-b:S3/1/1/2/1/1/2`):
  `‖iteratedFDeriv ℝ (k + 1) (p.inlet i τ) y‖ ≤ C * ((1 + ‖y‖) ^ 2)⁻¹`

Also provides shared off-axis-to-global closure and ring-geometry helpers in
`namespace RawAndInletDriftL4Sub`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff BigOperators

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03 UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace
  UnforcedLeray.B0411 UnforcedLeray.B0412 UnforcedLeray.Blueprint

namespace RawAndInletDriftL4Sub

/-- Off-axis weighted derivative bound implies global inverse-square derivative decay for any
smooth field `V : Space → Space` agreeing off the axis `Axi.axis` with `G : Space → Space`. -/
theorem inv_sq_decay_of_offAxis {V G : Space → Space} {m : ℕ} {C : ℝ}
    (hV : ContDiff ℝ ∞ V)
    (hoff : ∀ y : Space, y ∉ Axi.axis → V y = G y)
    (hG : ∀ y : Space, y ∉ Axi.axis → (1 + ‖y‖) ^ 2 * ‖iteratedFDeriv ℝ m G y‖ ≤ C) :
    ∀ y : Space, ‖iteratedFDeriv ℝ m V y‖ ≤ C * ((1 + ‖y‖) ^ 2)⁻¹ := by
  have hopen : IsOpen {y : Space | y ∉ Axi.axis} := by
    have h1 : {y : Space | y ∉ Axi.axis} = {y : Space | Axi.ϱ y ≠ 0} := by
      ext y
      simp [Axi.mem_axis_iff]
    rw [h1]
    exact isOpen_ne_fun Axi.continuous_ϱ continuous_const
  have hcl : IsClosed {y : Space | (1 + ‖y‖) ^ 2 * ‖iteratedFDeriv ℝ m V y‖ ≤ C} := by
    refine isClosed_le ?_ continuous_const
    exact ((continuous_const.add continuous_norm).pow 2).mul
      (hV.continuous_iteratedFDeriv (m := m) (by exact_mod_cast le_top)).norm
  have hsub :
      {y : Space | y ∉ Axi.axis} ⊆
        {y : Space | (1 + ‖y‖) ^ 2 * ‖iteratedFDeriv ℝ m V y‖ ≤ C} := by
    intro y hy
    have hev : V =ᶠ[𝓝 y] G :=
      Filter.eventuallyEq_of_mem (hopen.mem_nhds hy) (fun z hz => hoff z hz)
    show (1 + ‖y‖) ^ 2 * ‖iteratedFDeriv ℝ m V y‖ ≤ C
    rw [(hev.iteratedFDeriv (𝕜 := ℝ) m).eq_of_nhds]
    exact hG y hy
  intro y
  have hy_cl : y ∈ closure {z : Space | z ∉ Axi.axis} :=
    UnforcedLeray.Cons.C03.dense_compl_axis y
  have hle : (1 + ‖y‖) ^ 2 * ‖iteratedFDeriv ℝ m V y‖ ≤ C :=
    (hcl.closure_subset_iff.2 hsub) hy_cl
  have hpos : 0 < (1 + ‖y‖) ^ 2 := by positivity
  rw [ ← le_div_iff₀' hpos, div_eq_mul_inv] at hle
  exact hle

/-- Off-axis ring geometry bound: for `0 < R`, `0 ≤ S`, `y ∉ Axi.axis`, and `Axi.age R y ≤ S`,
`(1 + ‖y‖) * √(Axi.age R y) ≤ (1 + S + R) * (1 + |Axi.trans R y|)`. -/
theorem one_add_norm_mul_sqrt_age_le {R S : ℝ} (hR : 0 < R) (hS : 0 ≤ S)
    {y : Space} (hy : y ∉ Axi.axis) (hage : Axi.age R y ≤ S) :
    (1 + ‖y‖) * √(Axi.age R y) ≤ (1 + S + R) * (1 + |Axi.trans R y|) := by
  have hρ : 0 < Axi.ϱ y := Axi.ϱ_pos hy
  have hsq : √(Axi.age R y) = R / Axi.ϱ y := Axi.sqrt_age hR hy
  set s' := √(Axi.age R y)
  have hs'0 : 0 ≤ s' := Real.sqrt_nonneg _
  have hs'sq : s' ^ 2 = Axi.age R y := Real.sq_sqrt (Axi.age_nonneg R y)
  have h1 : Axi.ϱ y * s' = R := by rw [hsq]; field_simp
  have htr : |Axi.trans R y| = R * |y 2| / Axi.ϱ y := by
    unfold Axi.trans
    rw [abs_div, abs_mul, abs_of_pos hR, abs_of_pos hρ]
  have h2 : |y 2| * s' = |Axi.trans R y| := by rw [htr, hsq]; field_simp
  have hn : ‖y‖ ≤ Axi.ϱ y + |y 2| := by
    have h := Axi.norm_sq_eq_ϱ_sq_add y
    by_contra hc
    nlinarith [norm_nonneg y, abs_nonneg (y 2), sq_abs (y 2), Axi.ϱ_nonneg y]
  have hn' : (1 + ‖y‖) * s' ≤ s' + R + |Axi.trans R y| := by
    have : (1 + ‖y‖) * s' ≤ (1 + Axi.ϱ y + |y 2|) * s' :=
      mul_le_mul_of_nonneg_right (by linarith) hs'0
    linarith
  have hs'_le : s' ≤ 1 + S := by
    have : s' ≤ 1 + s' ^ 2 := by nlinarith [sq_nonneg (s' - 1 / 2)]
    linarith
  have habs : 0 ≤ |Axi.trans R y| := abs_nonneg _
  nlinarith

/-- Squared off-axis ring geometry bound: for `0 < R`, `0 ≤ S`, `y ∉ Axi.axis`, and
`Axi.age R y ≤ S`, `(1 + ‖y‖) ^ 2 * Axi.age R y ≤ (1 + S + R) ^ 2 * (1 + |Axi.trans R y|) ^ 2`. -/
theorem one_add_norm_sq_mul_age_le {R S : ℝ} (hR : 0 < R) (hS : 0 ≤ S)
    {y : Space} (hy : y ∉ Axi.axis) (hage : Axi.age R y ≤ S) :
    (1 + ‖y‖) ^ 2 * Axi.age R y ≤ (1 + S + R) ^ 2 * (1 + |Axi.trans R y|) ^ 2 := by
  have h := one_add_norm_mul_sqrt_age_le hR hS hy hage
  have h0 : 0 ≤ (1 + ‖y‖) * √(Axi.age R y) := by positivity
  have hsq : ((1 + ‖y‖) * √(Axi.age R y)) ^ 2 ≤ ((1 + S + R) * (1 + |Axi.trans R y|)) ^ 2 :=
    pow_le_pow_left₀ h0 h 2
  rw [mul_pow, Real.sq_sqrt (Axi.age_nonneg R y), mul_pow] at hsq
  exact hsq

/-- Near-axis (`Axi.ϱ y ≤ R`) radial norm bound:
`1 + ‖y‖ ≤ 1 + R + |y 2|` and, off the axis, `1 + ‖y‖ ≤ (1 + R) * (1 + |Axi.trans R y|)`. -/
theorem one_add_norm_le_of_varrho_le {R : ℝ} (hR : 0 < R) {y : Space}
    (hy : y ∉ Axi.axis) (hϱ : Axi.ϱ y ≤ R) :
    1 + ‖y‖ ≤ 1 + R + |y 2| ∧ 1 + ‖y‖ ≤ (1 + R) * (1 + |Axi.trans R y|) := by
  have hρ : 0 < Axi.ϱ y := Axi.ϱ_pos hy
  have hn : ‖y‖ ≤ Axi.ϱ y + |y 2| := by
    have h := Axi.norm_sq_eq_ϱ_sq_add y
    by_contra hc
    nlinarith [norm_nonneg y, abs_nonneg (y 2), sq_abs (y 2), Axi.ϱ_nonneg y]
  have h1 : 1 + ‖y‖ ≤ 1 + R + |y 2| := by linarith
  have htr : |Axi.trans R y| = R * |y 2| / Axi.ϱ y := by
    unfold Axi.trans
    rw [abs_div, abs_mul, abs_of_pos hR, abs_of_pos hρ]
  have hy2 : |y 2| ≤ |Axi.trans R y| := by
    rw [htr, le_div_iff₀ hρ, mul_comm R]
    exact mul_le_mul_of_nonneg_left hϱ (abs_nonneg (y 2))
  refine ⟨h1, ?_⟩
  have habs : 0 ≤ |Axi.trans R y| := abs_nonneg _
  nlinarith

end RawAndInletDriftL4Sub

/-- **All-order inverse-square spatial derivative decay for `p.raw`**
(SP lines 2543-2551, 2594-2610): in the background regime for small `ν`, for every `k : ℕ` there is
`C ≥ 0` such that for all `τ : ℝ` and `y : Space`,
`‖iteratedFDeriv ℝ (k + 1) (p.raw τ) y‖ ≤ C * ((1 + ‖y‖) ^ 2)⁻¹`. -/
def RawIteratedInvSqDecay : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm →
    ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ContDiff ℝ ∞ (fun x : ℝ × Space => p.raw x.1 x.2) →
      (Blueprint.IsBoundedBackground p.raw ∧ ∀ τ, IsSolenoidal (p.raw τ)) →
      ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℝ) (y : Space),
        ‖iteratedFDeriv ℝ (k + 1) (p.raw τ) y‖ ≤ C * ((1 + ‖y‖) ^ 2)⁻¹

/-- **All-order inverse-square spatial derivative decay for `p.inlet i`**
(SP lines 2543-2551, 2594-2610): in the background regime for small `ν`, for every `k : ℕ` there is
`C ≥ 0` such that for all `i : Fin 2`, `τ : ℝ`, and `y : Space`,
`‖iteratedFDeriv ℝ (k + 1) (p.inlet i τ) y‖ ≤ C * ((1 + ‖y‖) ^ 2)⁻¹`. -/
def InletIteratedInvSqDecay : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm →
    ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      (∀ i : Fin 2, ContDiff ℝ ∞ (fun x : ℝ × Space => p.inlet i x.1 x.2)) →
      (∀ i : Fin 2, Blueprint.IsBoundedBackground (p.inlet i) ∧
        ∀ τ, IsSolenoidal (p.inlet i τ)) →
      ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : Fin 2) (τ : ℝ) (y : Space),
        ‖iteratedFDeriv ℝ (k + 1) (p.inlet i τ) y‖ ≤ C * ((1 + ‖y‖) ^ 2)⁻¹

/-- Conditional assembly of `RawAndInletCoordJetRadialDriftL4` (`PartII-b:S3/1/1/2/1/1`) from
`RawIteratedInvSqDecay` and `InletIteratedInvSqDecay` via
`RadialDriftL4Sub.eLpNorm_spatialRadialDrift_dirSpatialJet_le_of_inv_sq_decay`. -/
theorem rawAndInletCoordJetRadialDriftL4_of
    (hRawDecay : RawIteratedInvSqDecay)
    (hInletDecay : InletIteratedInvSqDecay) :
    RawAndInletCoordJetRadialDriftL4 := by
  intro Sig lam q hSig hlam dm dp hdm
  obtain ⟨ν₁, hν₁, hR⟩ := hRawDecay Sig lam q hSig hlam dm dp hdm
  obtain ⟨ν₂, hν₂, hI⟩ := hInletDecay Sig lam q hSig hlam dm dp hdm
  refine ⟨min ν₁ ν₂, lt_min hν₁ hν₂, ?_⟩
  intro p d hReg hν hAge hMode hRawCD hInCD hRaw hInlet k α
  obtain ⟨C_R, hCR0, hCR⟩ :=
    hR p d hReg (hν.trans (min_le_left _ _)) hAge hMode hRawCD hRaw k
  obtain ⟨C_I, hCI0, hCI⟩ :=
    hI p d hReg (hν.trans (min_le_right _ _)) hAge hMode hInCD hInlet k
  let C : ℝ := max C_R C_I
  have hC0 : 0 ≤ C := le_trans hCR0 (le_max_left C_R C_I)
  have hK0 : 0 ≤ RadialDriftL4Sub.decayK := RadialDriftL4Sub.decayK_nonneg
  refine ⟨C * RadialDriftL4Sub.decayK, mul_nonneg hC0 hK0, ?_⟩
  intro τ
  have hRawSlice : ContDiff ℝ ∞ (p.raw τ) :=
    PhaseDerivStepSub.contDiff_slice_of_joint (F := p.raw) hRawCD τ
  have hInSlice : ∀ i : Fin 2, ContDiff ℝ ∞ (p.inlet i τ) :=
    fun i => PhaseDerivStepSub.contDiff_slice_of_joint (F := p.inlet i) (hInCD i) τ
  refine ⟨?_, ?_⟩
  · refine RadialDriftL4Sub.eLpNorm_spatialRadialDrift_dirSpatialJet_le_of_inv_sq_decay
      hRawSlice α hC0 (fun y => ?_)
    refine (hCR τ y).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left C_R C_I) (by positivity)
  · intro i
    refine RadialDriftL4Sub.eLpNorm_spatialRadialDrift_dirSpatialJet_le_of_inv_sq_decay
      (hInSlice i) α hC0 (fun y => ?_)
    refine (hCI i τ y).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_right C_R C_I) (by positivity)

end UnforcedLeray.Short.IIb

end
