import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5.CellPairBound

/-!
# Decomposition of `FcvXiInt` (source 4614-4615, 2819-2836)

`ρ ↦ ρ^μ ℓ_ρ(ξ_B(ρ))` is integrable on `(0, s]`.  Source 4614-4615: `ξ_B = O(s^{5/2})` near `0`
and continuous on `(0,∞)` (`FlatXiRegular`); `ℓ_ρ(ω) = ∫_cell [ω(νΔφ + v·∇φ) - (K_cω·∇E)φ]`
(2819-2836) with the actual train `(v, E)` smooth, `φ` a compactly supported cylinder test.
Two analytic lemmas on `ℓ` suffice and are proved here from them (`fcvXiInt_of`):

* `FcvEllUnif` : `|ℓ_r ω| ≤ C_T ‖ω‖` for `0 < r ≤ T`, uniformly;
* `FcvEllCont` : `r ↦ ℓ_r(ω(r))` is continuous on `(0,∞)` when `ω` is.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- **Band `L¹` bound of the Biot-Savart velocity** (`kcLp` is a continuous linear image of `ω`,
`kcLp ∈ L²(cell)`, `‖ω‖` the `X_{m,c}` norm; source 2819-2836, 4610-4615).  Only the band
`cell ∩ {|η| ≤ R}` of finite measure is needed: the tested integrand of `ellFn` is supported in
the band `|η| ≤ R` of the cylinder test `φ` (`B0579.IsCylTest.band`), so the (false-by-Cauchy-
Schwarz, infinite-measure) whole-cell bound is not used. -/
def FcvKcL1 : Prop :=
  ∀ (c m : ℝ) [Fact (1 < m)] [Fact (0 < c)] (R : ℝ), ∃ C : ℝ, ∀ ω : Xmc c m, ∀ j : Fin 2,
    ∫ x in B0579.cell c ∩ {x : ℝ × ℝ | |x.2| ≤ R}, ‖kcC ω x j‖ ≤ C * ‖ω‖

/-- **`kcC` is a.e. additive** (`kcLp` linear, `kcMer_ae`). -/
def FcvKcSub : Prop :=
  ∀ (c m : ℝ) [Fact (1 < m)] [Fact (0 < c)] (ω₁ ω₂ : Xmc c m) (j : Fin 2),
    (fun x => kcC (ω₁ - ω₂) x j) =ᵐ[volume.restrict (B0579.cell c)]
      fun x => kcC ω₁ x j - kcC ω₂ x j

/-- **Uniform bounds of the tested coefficients** (train smooth, `IIIa.train_joint_cont`, `φ`
compactly supported in `η`, `[0,T]` compact): the coefficient of `ω` and of `K_cω` in
`flowIntegrand`, over `0 ≤ r ≤ T`, `y ∈ cell`. -/
def FcvEllCoef : Prop :=
  ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (φ : ℝ × ℝ → ℝ), B0579.IsCylTest c φ →
    ∀ T : ℝ, ∃ A B : ℝ, ∀ r ∈ Icc (0 : ℝ) T, ∀ y ∈ B0579.cell c,
      |ν * IIIa.lapP φ y + (tr.v r y 0 * B0579.pd 0 φ y + tr.v r y 1 * B0579.pd 1 φ y)| ≤ A ∧
      ∀ k : Fin 2, |B0579.pd k (UnforcedLeray.B0238.Ec tr r) y * φ y| ≤ B

/-- **`r ↦ ℓ_r(ω)` is continuous for fixed `ω`** on `(0,∞)` (dominated convergence over the cell
with the bounds of `FcvEllCoef`; joint continuity `IIIa.train_joint_cont`). -/
def FcvEllFixed : Prop :=
  ∀ (ν c m : ℝ) [Fact (1 < m)] [Fact (0 < c)] (tr : UnforcedLeray.B0140.TrainSol ν c)
    (φ : ℝ × ℝ → ℝ), B0579.IsCylTest c φ → ∀ ω : Xmc c m,
      ContinuousOn (fun r : ℝ => ellFn tr φ r ω) (Ioi 0)

/-- **Uniform bound `|ℓ_r ω| ≤ C_T ‖ω‖`, `0 < r ≤ T`**.  Proof (`Unif.lean`): let `R` be the
`B0579.IsCylTest.band` radius of `φ`; the integrand of `ellFn` vanishes off the band `|η| ≤ R`
(`φ`, `pd k φ`, `lapP φ` vanish there, and the `Ec` term is multiplied by `φ`), so split
`∫_cell` into `cell ∩ {|η| ≤ R}` and use `FcvEllCoef` (bounds `A`, `B`), `lintegral_norm_cell_le`
(`L¹` of `xFn`) and `FcvKcL1` with this `R`. -/
def FcvEllUnif : Prop :=
  ∀ (ν c m : ℝ) [Fact (1 < m)] [Fact (0 < c)] (tr : UnforcedLeray.B0140.TrainSol ν c)
    (φ : ℝ × ℝ → ℝ), B0579.IsCylTest c φ → ∀ T : ℝ, ∃ C : ℝ, ∀ r : ℝ, 0 < r → r ≤ T →
      ∀ ω : Xmc c m, ‖ellFn tr φ r ω‖ ≤ C * ‖ω‖

/-- **`r ↦ ℓ_r(ω(r))` is continuous** for `ω` continuous on `(0,∞)` into `X_{m,c}`
(`ℓ_r` is additive: `FcvKcSub`; split `ℓ_r ω_r - ℓ_{r₀} ω_{r₀} = ℓ_r(ω_r - ω_{r₀}) +
(ℓ_r - ℓ_{r₀}) ω_{r₀}`; `FcvEllUnif`, `FcvEllFixed`). -/
def FcvEllCont : Prop :=
  ∀ (ν c m : ℝ) [Fact (1 < m)] [Fact (0 < c)] (tr : UnforcedLeray.B0140.TrainSol ν c)
    (φ : ℝ × ℝ → ℝ), B0579.IsCylTest c φ → ∀ ω : ℝ → Xmc c m, ContinuousOn ω (Ioi 0) →
      ContinuousOn (fun r : ℝ => ellFn tr φ r (ω r)) (Ioi 0)

theorem fcvXiInt_of (hReg : FlatXiRegular) (hU : FcvEllUnif) (hC : FcvEllCont) : FcvXiInt := by
  intro κ ν c m hm hc tr D μ as χf A hν hμ hχ hA φ hφ s hs
  obtain ⟨hξc, C0, hC0⟩ := hReg κ ν c m tr D μ as χf A hν hμ hχ hA
  set ξ : ℝ → Xmc c m := xiD D (μ : ℂ) (Bmat ν μ χf A) with hξ
  obtain ⟨C, hCU⟩ := hU ν c m tr φ hφ s
  -- bound of `ξ` on `(0, s]`
  have hξb : ∃ M : ℝ, ∀ r ∈ Ioc (0 : ℝ) s, ‖ξ r‖ ≤ M := by
    have hK : IsCompact (Icc (1 : ℝ) (max s 1)) := isCompact_Icc
    obtain ⟨M1, hM1⟩ := hK.exists_bound_of_continuousOn
      (hξc.mono (fun r hr => lt_of_lt_of_le one_pos hr.1))
    refine ⟨max |C0| M1, fun r hr => ?_⟩
    by_cases h1 : r ≤ 1
    · refine (hC0 r ⟨hr.1, h1⟩).trans ?_
      have : r ^ (5 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hr.1.le h1 (by norm_num)
      calc C0 * r ^ (5 / 2 : ℝ) ≤ |C0| * r ^ (5 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hr.1.le _)
        _ ≤ |C0| * 1 := mul_le_mul_of_nonneg_left this (abs_nonneg _)
        _ ≤ max |C0| M1 := by rw [mul_one]; exact le_max_left _ _
    · exact (hM1 r ⟨(not_le.1 h1).le, hr.2.trans (le_max_left _ _)⟩).trans (le_max_right _ _)
  obtain ⟨M, hM⟩ := hξb
  have hcont : ContinuousOn (fun r : ℝ => ((r : ℂ) ^ (μ : ℂ)) * ellFn tr φ r (ξ r)) (Ioi 0) := by
    have hp : ContinuousOn (fun r : ℝ => ((r : ℂ) ^ (μ : ℂ))) (Ioi 0) := by
      refine ContinuousOn.cpow_const ?_ ?_
      · exact Complex.continuous_ofReal.continuousOn
      · intro t ht
        exact Or.inl (by simpa using ht)
    exact hp.mul (hC ν c m tr φ hφ ξ hξc)
  have hmeasR : AEStronglyMeasurable (fun r : ℝ => ((r : ℂ) ^ (μ : ℂ)) * ellFn tr φ r (ξ r))
      (volume.restrict (Ioc 0 s)) :=
    (hcont.mono (fun t ht => ht.1)).aestronglyMeasurable measurableSet_Ioc
  have hfin : (volume.restrict (Ioc 0 s)) univ ≠ ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact measure_Ioc_lt_top.ne
  have hbound : ∀ᵐ r : ℝ ∂(volume.restrict (Ioc 0 s)),
      ‖((r : ℂ) ^ (μ : ℂ)) * ellFn tr φ r (ξ r)‖ ≤ s ^ μ * (max C 0 * M) := by
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun r hr => ?_
    have h0 : 0 < r := hr.1
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos h0, Complex.ofReal_re]
    have h1 : r ^ μ ≤ s ^ μ := Real.rpow_le_rpow h0.le hr.2 hμ.le
    have h2 : ‖ellFn tr φ r (ξ r)‖ ≤ max C 0 * M := by
      refine (hCU r h0 hr.2 (ξ r)).trans ?_
      calc C * ‖ξ r‖ ≤ max C 0 * ‖ξ r‖ :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
        _ ≤ max C 0 * M := mul_le_mul_of_nonneg_left (hM r hr) (le_max_right _ _)
    exact mul_le_mul h1 h2 (norm_nonneg _) (Real.rpow_nonneg hs.le _)
  have hbound' : ∀ᵐ r : ℝ ∂((volume.restrict (Ioc 0 s)).restrict univ),
      ‖((r : ℂ) ^ (μ : ℂ)) * ellFn tr φ r (ξ r)‖ ≤ s ^ μ * (max C 0 * M) := by
    rw [Measure.restrict_univ]
    exact hbound
  exact integrableOn_univ.1 (Measure.integrableOn_of_bounded hfin hmeasR hbound')

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
