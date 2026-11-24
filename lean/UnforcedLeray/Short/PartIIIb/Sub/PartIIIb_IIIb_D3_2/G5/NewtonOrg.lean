import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G5.NewtonRem

/-!
# Organizer assembly for `NewtonTaylor` (`PartIII-b:IIIb-D3/2/G5/2/org`)

Splits `SigmaIntForm χo` into two leaf propositions:
* `SigmaIntSymm χo` (`PartIII-b:IIIb-D3/2/G5/2/1`): off-diagonal vanishing and `00 = 11` symmetry
  of `sigmaInt c ν χo M` via planar reflections and coordinate swap;
* `SigmaIntPolar χo` (`PartIII-b:IIIb-D3/2/G5/2/2`): polar evaluation of
  `sigmaInt c ν χo M 2 2 - sigmaInt c ν χo M 0 0` via `planePolar_bochner`;
together with the two remainder leaf propositions from `NewtonRem.lean`:
* `SigmaMFirstMoment χo` (`PartIII-b:IIIb-D3/2/G5/2/3`): radial first moment bound for `sigmaM`;
* `D3tDiffBound` (`PartIII-b:IIIb-D3/2/G5/2/4`): mean-value shift difference bound for `D3t`;
and proves `newtonTaylor_of` combining `newtonShort` (`0 < s < 4 / (5ν)`) and `newtonTail`
(`s ≥ 4 / (5ν)`) with `ν₀ = 1` and `k = 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G5

/-- Nonnegative Bochner version of `planePolar`: for `G ≥ 0` a.e. strongly measurable on `Ioi 0`
with `u ↦ u^{-3/2} G(u)` integrable on `Ioi 0`, `x' ↦ |x'|⁻¹ G(|x'|⁻²)` is integrable on `ℝ²`
with integral `π ∫_{u>0} u^{-3/2} G(u) du`. -/
theorem planePolar_bochner_nonneg (G : ℝ → ℝ) (hG0 : ∀ u, 0 ≤ G u)
    (hGm : AEStronglyMeasurable G (volume.restrict (Ioi (0 : ℝ))))
    (hGint : Integrable (fun u : ℝ => u ^ (-(3 / 2 : ℝ)) * G u) (volume.restrict (Ioi (0 : ℝ)))) :
    Integrable (fun x' : ℝ × ℝ =>
      (Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ * G ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹)) ∧
    (∫ x' : ℝ × ℝ, (Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ * G ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹)) =
      Real.pi * ∫ u in Ioi (0 : ℝ), u ^ (-(3 / 2 : ℝ)) * G u := by
  have hsqrt : Measurable (fun x' : ℝ × ℝ => Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2)) :=
    Real.continuous_sqrt.measurable.comp
      ((measurable_fst.pow_const 2).add (measurable_snd.pow_const 2))
  have hf_meas : AEStronglyMeasurable (fun x' : ℝ × ℝ =>
      (Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ * G ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹)) volume :=
    hsqrt.inv.aestronglyMeasurable.mul (pullback_aesm hGm)
  have hf0 : ∀ x' : ℝ × ℝ,
      0 ≤ (Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ * G ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹) :=
    fun x' => mul_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)) (hG0 _)
  have hu_nn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun u : ℝ => u ^ (-(3 / 2 : ℝ)) * G u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := hu
    exact mul_nonneg (Real.rpow_nonneg hu0.le _) (hG0 u)
  have hint_nn : 0 ≤ ∫ u in Ioi (0 : ℝ), u ^ (-(3 / 2 : ℝ)) * G u :=
    integral_nonneg_of_ae hu_nn
  have hL : ∫⁻ x' : ℝ × ℝ, ENNReal.ofReal
      ((Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ * G ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹)) =
      ENNReal.ofReal (Real.pi * ∫ u in Ioi (0 : ℝ), u ^ (-(3 / 2 : ℝ)) * G u) := by
    calc ∫⁻ x' : ℝ × ℝ, ENNReal.ofReal
          ((Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ * G ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹))
        = ENNReal.ofReal Real.pi *
            ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ (-(3 / 2 : ℝ)) * G u) :=
          planePolar G hG0 hGm.aemeasurable
      _ = ENNReal.ofReal Real.pi *
            ENNReal.ofReal (∫ u in Ioi (0 : ℝ), u ^ (-(3 / 2 : ℝ)) * G u) := by
          rw [ofReal_integral_eq_lintegral_ofReal hGint hu_nn]
      _ = ENNReal.ofReal (Real.pi * ∫ u in Ioi (0 : ℝ), u ^ (-(3 / 2 : ℝ)) * G u) :=
          (ENNReal.ofReal_mul Real.pi_pos.le).symm
  have hfin : (∫⁻ x' : ℝ × ℝ, ENNReal.ofReal
      ((Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ * G ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹))) < ∞ := by
    rw [hL]
    exact ENNReal.ofReal_lt_top
  have hint_f : Integrable (fun x' : ℝ × ℝ =>
      (Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ * G ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹)) :=
    ⟨hf_meas, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hf0)).2 hfin⟩
  refine ⟨hint_f, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf0) hf_meas, hL,
    ENNReal.toReal_ofReal (mul_nonneg Real.pi_pos.le hint_nn)]

/-- Signed Bochner version of `planePolar`: for any `H : ℝ → ℝ` a.e. strongly measurable on `Ioi 0`
with `u ↦ u^{-3/2} H(u)` integrable on `Ioi 0`, `x' ↦ |x'|⁻¹ H(|x'|⁻²)` is integrable on `ℝ²`
with integral `π ∫_{u>0} u^{-3/2} H(u) du`. -/
theorem planePolar_bochner (H : ℝ → ℝ)
    (hHm : AEStronglyMeasurable H (volume.restrict (Ioi (0 : ℝ))))
    (hint : Integrable (fun u : ℝ => u ^ (-(3 / 2 : ℝ)) * H u) (volume.restrict (Ioi (0 : ℝ)))) :
    Integrable (fun x' : ℝ × ℝ =>
      (Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ * H ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹)) ∧
    (∫ x' : ℝ × ℝ, (Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ * H ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹)) =
      Real.pi * ∫ u in Ioi (0 : ℝ), u ^ (-(3 / 2 : ℝ)) * H u := by
  let Hpos : ℝ → ℝ := fun u => max (H u) 0
  let Hneg : ℝ → ℝ := fun u => max (-H u) 0
  have hpos0 : ∀ u, 0 ≤ Hpos u := fun u => le_max_right _ _
  have hneg0 : ∀ u, 0 ≤ Hneg u := fun u => le_max_right _ _
  have hpos_m : AEStronglyMeasurable Hpos (volume.restrict (Ioi (0 : ℝ))) :=
    hHm.sup aestronglyMeasurable_const
  have hneg_m : AEStronglyMeasurable Hneg (volume.restrict (Ioi (0 : ℝ))) :=
    hHm.neg.sup aestronglyMeasurable_const
  have hp : Measurable (fun u : ℝ => u ^ (-(3 / 2 : ℝ))) := measurable_id.pow_const _
  have hpos_int : Integrable (fun u : ℝ => u ^ (-(3 / 2 : ℝ)) * Hpos u)
      (volume.restrict (Ioi (0 : ℝ))) := by
    refine Integrable.mono' hint.norm (hp.aestronglyMeasurable.mul hpos_m) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := hu
    have hr : 0 ≤ u ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hu0.le _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hr, abs_of_nonneg (hpos0 u),
      Real.norm_eq_abs, abs_mul, abs_of_nonneg hr]
    refine mul_le_mul_of_nonneg_left ?_ hr
    exact max_le (le_abs_self _) (abs_nonneg _)
  have hneg_int : Integrable (fun u : ℝ => u ^ (-(3 / 2 : ℝ)) * Hneg u)
      (volume.restrict (Ioi (0 : ℝ))) := by
    refine Integrable.mono' hint.norm (hp.aestronglyMeasurable.mul hneg_m) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := hu
    have hr : 0 ≤ u ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hu0.le _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hr, abs_of_nonneg (hneg0 u),
      Real.norm_eq_abs, abs_mul, abs_of_nonneg hr]
    refine mul_le_mul_of_nonneg_left ?_ hr
    exact max_le (neg_le_abs _) (abs_nonneg _)
  obtain ⟨hIpos, hEpos⟩ := planePolar_bochner_nonneg Hpos hpos0 hpos_m hpos_int
  obtain ⟨hIneg, hEneg⟩ := planePolar_bochner_nonneg Hneg hneg0 hneg_m hneg_int
  have hdecomp : ∀ u : ℝ, H u = Hpos u - Hneg u := by
    intro u
    simp only [Hpos, Hneg]
    rcases le_total 0 (H u) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith), sub_zero]
    · rw [max_eq_right h, max_eq_left (by linarith), zero_sub, neg_neg]
  have hf_eq : (fun x' : ℝ × ℝ =>
      (Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ * H ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹)) =
      fun x' : ℝ × ℝ =>
        (Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ * Hpos ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹) -
          (Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ * Hneg ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹) := by
    funext x'
    rw [hdecomp ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹), mul_sub]
  have hu_eq : (fun u : ℝ => u ^ (-(3 / 2 : ℝ)) * H u) =
      fun u : ℝ => u ^ (-(3 / 2 : ℝ)) * Hpos u - u ^ (-(3 / 2 : ℝ)) * Hneg u := by
    funext u
    rw [hdecomp u, mul_sub]
  refine ⟨by rw [hf_eq]; exact hIpos.sub hIneg, ?_⟩
  rw [hf_eq, integral_sub hIpos hIneg, hEpos, hEneg, hu_eq, integral_sub hpos_int hneg_int]
  ring

/-- Explicit entry formulas for `sigmaM c ν χo M y`: since the azimuthal (`1`) row and column of
`phaseMean` vanish and `rotQ` is block-diagonal between `{0, 1}` and `{2}`, each entry `(a, b)`
of `sigmaM` reduces to a single term. -/
theorem sigmaM_zero_zero (c ν : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (y : ℝ × ℝ) :
    sigmaM c ν χo M y 0 0 =
      (y.1 / Real.sqrt (y.1 ^ 2 + y.2 ^ 2)) ^ 2 *
        ((Real.sqrt (y.1 ^ 2 + y.2 ^ 2))⁻¹ * phaseMean c ν χo M (y.1 ^ 2 + y.2 ^ 2)⁻¹ 0 0) := by
  simp [sigmaM, Fin.sum_univ_three, rotQ, phaseMean]
  ring

theorem sigmaM_one_one (c ν : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (y : ℝ × ℝ) :
    sigmaM c ν χo M y 1 1 =
      (y.2 / Real.sqrt (y.1 ^ 2 + y.2 ^ 2)) ^ 2 *
        ((Real.sqrt (y.1 ^ 2 + y.2 ^ 2))⁻¹ * phaseMean c ν χo M (y.1 ^ 2 + y.2 ^ 2)⁻¹ 0 0) := by
  simp [sigmaM, Fin.sum_univ_three, rotQ, phaseMean]
  ring

theorem sigmaM_two_two (c ν : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (y : ℝ × ℝ) :
    sigmaM c ν χo M y 2 2 =
      (Real.sqrt (y.1 ^ 2 + y.2 ^ 2))⁻¹ * phaseMean c ν χo M (y.1 ^ 2 + y.2 ^ 2)⁻¹ 2 2 := by
  simp [sigmaM, Fin.sum_univ_three, rotQ, phaseMean]

theorem sigmaM_zero_two (c ν : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (y : ℝ × ℝ) :
    sigmaM c ν χo M y 0 2 =
      (y.1 / Real.sqrt (y.1 ^ 2 + y.2 ^ 2)) *
        ((Real.sqrt (y.1 ^ 2 + y.2 ^ 2))⁻¹ * phaseMean c ν χo M (y.1 ^ 2 + y.2 ^ 2)⁻¹ 0 2) := by
  simp [sigmaM, Fin.sum_univ_three, rotQ, phaseMean]

theorem sigmaM_two_zero (c ν : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (y : ℝ × ℝ) :
    sigmaM c ν χo M y 2 0 =
      (y.1 / Real.sqrt (y.1 ^ 2 + y.2 ^ 2)) *
        ((Real.sqrt (y.1 ^ 2 + y.2 ^ 2))⁻¹ * phaseMean c ν χo M (y.1 ^ 2 + y.2 ^ 2)⁻¹ 2 0) := by
  simp [sigmaM, Fin.sum_univ_three, rotQ, phaseMean]
  ring

theorem sigmaM_diag_combo (c ν : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) {y : ℝ × ℝ} (hy : y ≠ 0) :
    sigmaM c ν χo M y 2 2 - (sigmaM c ν χo M y 0 0 + sigmaM c ν χo M y 1 1) / 2 =
      (1 / 2 : ℝ) * ((Real.sqrt (y.1 ^ 2 + y.2 ^ 2))⁻¹ *
        (2 * phaseMean c ν χo M (y.1 ^ 2 + y.2 ^ 2)⁻¹ 2 2 -
          phaseMean c ν χo M (y.1 ^ 2 + y.2 ^ 2)⁻¹ 0 0)) := by
  have hs : 0 < y.1 ^ 2 + y.2 ^ 2 := by
    rcases (show (0 : ℝ) ≤ y.1 ^ 2 + y.2 ^ 2 by positivity).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hy
      have h1 : y.1 ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg y.2]) (sq_nonneg _)
      have h2 : y.2 ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg y.1]) (sq_nonneg _)
      exact Prod.ext (pow_eq_zero_iff two_ne_zero |>.1 h1) (pow_eq_zero_iff two_ne_zero |>.1 h2)
  have hsq : (y.1 / Real.sqrt (y.1 ^ 2 + y.2 ^ 2)) ^ 2 +
      (y.2 / Real.sqrt (y.1 ^ 2 + y.2 ^ 2)) ^ 2 = 1 := by
    rw [div_pow, div_pow, ← add_div, Real.sq_sqrt hs.le, div_self hs.ne']
  rw [sigmaM_zero_zero, sigmaM_one_one, sigmaM_two_two]
  linear_combination
    -((1 / 2 : ℝ) * ((Real.sqrt (y.1 ^ 2 + y.2 ^ 2))⁻¹ *
      phaseMean c ν χo M (y.1 ^ 2 + y.2 ^ 2)⁻¹ 0 0)) * hsq

/-- Leaf 1 (`PartIII-b:IIIb-D3/2/G5/2/1`): off-diagonal entries of `sigmaInt c ν χo M` vanish and
`sigmaInt c ν χo M 0 0 = sigmaInt c ν χo M 1 1` by planar reflection and coordinate-swap
symmetries. -/
def SigmaIntSymm (χo : ℝ → ℝ) : Prop :=
  ∀ (c ν : ℝ), 0 < c → 0 < ν → IsOutwardCutoff χo →
    ∀ M : Chart → Mat3, OldThinFinite c ν M →
      (∀ a b : Fin 3, a ≠ b → sigmaInt c ν χo M a b = 0) ∧
      sigmaInt c ν χo M 0 0 = sigmaInt c ν χo M 1 1

/-- Leaf 2 (`PartIII-b:IIIb-D3/2/G5/2/2`): polar-coordinate evaluation of
`sigmaInt c ν χo M 2 2 - sigmaInt c ν χo M 0 0` when `sigmaInt c ν χo M 0 0 = sigmaInt c ν χo M 1 1`. -/
def SigmaIntPolar (χo : ℝ → ℝ) : Prop :=
  ∀ (c ν : ℝ), 0 < c → 0 < ν → IsOutwardCutoff χo →
    ∀ M : Chart → Mat3, OldThinFinite c ν M →
      sigmaInt c ν χo M 0 0 = sigmaInt c ν χo M 1 1 →
      sigmaInt c ν χo M 2 2 - sigmaInt c ν χo M 0 0 =
        (Real.pi / 2) * ∫ u in Ioi (0 : ℝ),
          χo (ν * u) * u ^ (-(3 / 2 : ℝ)) *
            ConcreteYF.cellInt c (fun p => 2 * M (u, p) 2 2 - M (u, p) 0 0)

theorem sigmaIntForm_of {χo : ℝ → ℝ} (hSymm : SigmaIntSymm χo) (hPol : SigmaIntPolar χo) :
    SigmaIntForm χo := by
  intro c ν hc hν hχ M hM
  obtain ⟨hoff, h01⟩ := hSymm c ν hc hν hχ M hM
  exact ⟨hoff, h01, hPol c ν hc hν hχ M hM h01⟩

/-- Main assembly theorem: `NewtonTaylor as K χo χy` follows from the 4 leaf propositions
`SigmaIntSymm χo`, `SigmaIntPolar χo`, `SigmaMFirstMoment χo`, and `D3tDiffBound`. -/
theorem newtonTaylor_of (as : ℝ) (K : Set ℝ) (χo χy : ℝ → ℝ)
    (hSymm : SigmaIntSymm χo) (hPol : SigmaIntPolar χo)
    (hMom : SigmaMFirstMoment χo) (hD : D3tDiffBound) :
    NewtonTaylor as K χo χy := by
  intro has _hK _hKsub
  have hS : SigmaIntForm χo := sigmaIntForm_of hSymm hPol
  have hRem : NewtonVRemBound χo := newtonVRemBound_of hMom hD
  obtain ⟨C1, hC1_0, hShort⟩ := newtonShort as χo χy has hS hRem
  obtain ⟨C2, hC2_0, hTail⟩ := newtonTail as χo χy has
  refine ⟨C1 + C2, 1, 0, add_nonneg hC1_0 hC2_0, one_pos, ?_⟩
  intro c ν ε μ h _hν1 _hμK M hM s hs0
  have hε3_0 : 0 ≤ ε ^ 3 := pow_nonneg h.eps_pos.le 3
  have hN1_0 : 0 ≤ oldN1w c ν χo M := oldN1w_nonneg h.nu_pos h.chiO M
  have hN0_0 : 0 ≤ oldN0w c ν χo M := rj6_oldN0w_nonneg c ν h.nu_pos h.chiO M
  have hexp_0 : 0 ≤ Real.exp (-(4 * as / 5) / ν) := Real.exp_nonneg _
  rw [pow_zero, one_mul]
  by_cases hs : s < 4 / (5 * ν)
  · have hb := hShort c ν ε μ h M hM s hs0 hs
    calc affTerm as 6 (Lpt c ν ε μ χo χy M - ellMuGen c ν ε μ χo M • aMuFun μ) s
        ≤ C1 * ε ^ 3 * oldN1w c ν χo M := hb
      _ ≤ (C1 + C2) * ε ^ 3 *
            (oldN1w c ν χo M + Real.exp (-(4 * as / 5) / ν) * oldN0w c ν χo M) := by
          nlinarith [mul_nonneg hε3_0 hN1_0, mul_nonneg hexp_0 hN0_0,
            mul_nonneg (add_nonneg hC1_0 hC2_0) (mul_nonneg hε3_0 (mul_nonneg hexp_0 hN0_0))]
  · have hs_ge : 4 / (5 * ν) ≤ s := le_of_not_gt hs
    have hb := hTail c ν ε μ h M hM s hs_ge
    calc affTerm as 6 (Lpt c ν ε μ χo χy M - ellMuGen c ν ε μ χo M • aMuFun μ) s
        ≤ C2 * ε ^ 3 * Real.exp (-(4 * as / 5) / ν) * oldN0w c ν χo M := hb
      _ ≤ (C1 + C2) * ε ^ 3 *
            (oldN1w c ν χo M + Real.exp (-(4 * as / 5) / ν) * oldN0w c ν χo M) := by
          nlinarith [mul_nonneg hε3_0 hN1_0, mul_nonneg hexp_0 hN0_0,
            mul_nonneg hC1_0 (mul_nonneg hε3_0 (mul_nonneg hexp_0 hN0_0)),
            mul_nonneg (add_nonneg hC1_0 hC2_0) (mul_nonneg hε3_0 hN1_0)]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G5
