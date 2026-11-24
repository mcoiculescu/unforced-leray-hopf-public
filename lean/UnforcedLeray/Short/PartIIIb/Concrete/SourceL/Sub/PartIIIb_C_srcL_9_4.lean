import UnforcedLeray.Short.PartIIIb.Concrete.SourceL

/-!
# Decomposition of `sigmaM_l1` (source 4766-4775, 4924-4927)

Source: `the November 2 reference manuscript`.

`Σ_M(x') = Q (ρ⁻¹ E(u)) Qᵀ`, `u = ρ⁻²`, `E = phaseMean`.  Support is proved here.  The
`L¹` bound reduces to `SigmaMeas`, `SigmaPointwise`, `PlanePolar`, `PhaseBInt`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `B(u) = χ_o(νu) ∫_cell |M(u,·)| d(avgμ c)` (source 4766-4770, 4924-4927). -/
def phaseB (c ν : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (u : ℝ) : ℝ :=
  χo (ν * u) * ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c)

/-- `Σ_M` is a.e. strongly measurable on the plane (source 4771-4775; `E(u)` is a.e. measurable in
`u` by Fubini on `oldMeasure`, and `x' ↦ |x'|⁻²` pushes Lebesgue measure to a measure
absolutely continuous w.r.t. Lebesgue). -/
def SigmaMeas : Prop :=
  ∀ (c ν : ℝ) (χo : ℝ → ℝ), 0 < c → 0 < ν → IsOutwardCutoff χo →
    ∀ M : Chart → Mat3, OldThinFinite c ν M →
      AEStronglyMeasurable (fun x' : ℝ × ℝ => sigmaM c ν χo M x') volume

/-- Pointwise bound (source 4771-4775): `|Σ_M(x')| ≤ ρ⁻¹ |E(ρ⁻²)| ≤ ρ⁻¹ B(ρ⁻²)`
(Frobenius norm is invariant under conjugation by the orthogonal `rotQ` for `x' ≠ 0`; Frobenius of
an integral ≤ integral of Frobenius; `0 ≤ χ_o`).  It holds for almost every `x'`: the inner
integral `∫ |M(u,·)|` is a Bochner integral and `OldThinFinite` makes `|M(u,·)|` integrable only
for a.e. `u`, which pulls back to a.e. `x'` under `x' ↦ |x'|⁻²` (the exceptional `x'` form a null
set; the statement without "a.e." is false, e.g. for a tensor with one non-integrable slice). -/
def SigmaPointwise : Prop :=
  ∀ (c ν : ℝ) (χo : ℝ → ℝ), 0 < c → 0 < ν → IsOutwardCutoff χo →
    ∀ (M : Chart → Mat3), OldThinFinite c ν M →
    ∀ᵐ x' : ℝ × ℝ ∂volume, frob (sigmaM c ν χo M x') ≤
      (Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ * phaseB c ν χo M (x'.1 ^ 2 + x'.2 ^ 2)⁻¹

/-- Polar coordinates in the plane with `u = ρ⁻²`, `ρ = u^{-1/2}`, `dρ = ½ u^{-3/2} du`:
`∫_{ℝ²} ρ⁻¹ H(ρ⁻²) dx' = π ∫_0^∞ u^{-3/2} H(u) du` for `H ≥ 0` a.e. measurable. -/
def PlanePolar : Prop :=
  ∀ H : ℝ → ℝ, (∀ u, 0 ≤ H u) → AEMeasurable H (volume.restrict (Ioi (0 : ℝ))) →
    ∫⁻ x' : ℝ × ℝ, ENNReal.ofReal ((Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ *
        H ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹)) =
      ENNReal.ofReal Real.pi * ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ (-(3 / 2 : ℝ)) * H u)

/-- `B` is a.e. measurable on `(0,∞)` and `∫ u^{-3/2} B ≤ N₀` (source 4924-4927): `B = 0` for
`νu ≤ 6/5` (`χ_o` vanishes), `B ≤ ∫_cell |M|` (`χ_o ≤ 1`), Fubini on `oldMeasure`. -/
def PhaseBInt : Prop :=
  ∀ (c ν : ℝ) (χo : ℝ → ℝ), 0 < c → 0 < ν → IsOutwardCutoff χo →
    ∀ M : Chart → Mat3, OldThinFinite c ν M →
      AEMeasurable (phaseB c ν χo M) (volume.restrict (Ioi (0 : ℝ))) ∧
      ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ (-(3 / 2 : ℝ)) * phaseB c ν χo M u) ≤
        ENNReal.ofReal (oldN0 c ν M)

theorem phaseB_nonneg (c ν : ℝ) {χo : ℝ → ℝ} (hχ : IsOutwardCutoff χo) (M : Chart → Mat3) (u : ℝ) :
    0 ≤ phaseB c ν χo M u :=
  mul_nonneg (hχ.range _).1 (integral_nonneg fun x => Real.sqrt_nonneg _)

theorem sigmaM_support {c ν : ℝ} {χo : ℝ → ℝ} (hν : 0 < ν) (hχ : IsOutwardCutoff χo)
    (M : Chart → Mat3) (x' : ℝ × ℝ) (hx : ν * (5 / 6) < x'.1 ^ 2 + x'.2 ^ 2) :
    sigmaM c ν χo M x' = 0 := by
  have hpos : 0 < x'.1 ^ 2 + x'.2 ^ 2 := by nlinarith
  have hu : ν * (x'.1 ^ 2 + x'.2 ^ 2)⁻¹ ≤ 6 / 5 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hpos]; nlinarith
  have h0 : phaseMean c ν χo M (x'.1 ^ 2 + x'.2 ^ 2)⁻¹ = 0 := by
    funext i j
    simp [phaseMean, hχ.zero _ hu]
  funext a b
  simp [sigmaM, h0]

theorem frob_nonneg' (A : Mat3) : 0 ≤ frob A := Real.sqrt_nonneg _

theorem norm_le_frob (A : Mat3) : ‖A‖ ≤ frob A := by
  refine (pi_norm_le_iff_of_nonneg (frob_nonneg' A)).2 fun i => ?_
  refine (pi_norm_le_iff_of_nonneg (frob_nonneg' A)).2 fun j => ?_
  rw [Real.norm_eq_abs]
  unfold frob
  apply Real.abs_le_sqrt
  calc A i j ^ 2 ≤ ∑ j, A i j ^ 2 :=
        Finset.single_le_sum (f := fun j => A i j ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i, ∑ j, A i j ^ 2 :=
        Finset.single_le_sum (f := fun i => ∑ j, A i j ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)

theorem continuous_frob : Continuous frob := by
  unfold frob; fun_prop

theorem sigmaM_lintegral_le (hP : SigmaPointwise) (hPol : PlanePolar) (hB : PhaseBInt)
    {c ν : ℝ} {χo : ℝ → ℝ} (hc : 0 < c) (hν : 0 < ν) (hχ : IsOutwardCutoff χo)
    {M : Chart → Mat3} (hM : OldThinFinite c ν M) :
    ∫⁻ x' : ℝ × ℝ, ENNReal.ofReal (frob (sigmaM c ν χo M x')) ≤
      ENNReal.ofReal (Real.pi * oldN0 c ν M) := by
  obtain ⟨hmeas, hint⟩ := hB c ν χo hc hν hχ M hM
  calc ∫⁻ x' : ℝ × ℝ, ENNReal.ofReal (frob (sigmaM c ν χo M x'))
      ≤ ∫⁻ x' : ℝ × ℝ, ENNReal.ofReal ((Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ *
          phaseB c ν χo M ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹)) :=
        lintegral_mono_ae ((hP c ν χo hc hν hχ M hM).mono fun x' h => ENNReal.ofReal_le_ofReal h)
    _ = ENNReal.ofReal Real.pi * ∫⁻ u in Ioi (0 : ℝ),
          ENNReal.ofReal (u ^ (-(3 / 2 : ℝ)) * phaseB c ν χo M u) :=
        hPol _ (phaseB_nonneg c ν hχ M) hmeas
    _ ≤ ENNReal.ofReal Real.pi * ENNReal.ofReal (oldN0 c ν M) := by gcongr
    _ = ENNReal.ofReal (Real.pi * oldN0 c ν M) :=
        (ENNReal.ofReal_mul Real.pi_pos.le).symm

/-- The target, from the four sub-statements. -/
theorem sigmaM_l1_of (hS : SigmaMeas) (hP : SigmaPointwise) (hPol : PlanePolar) (hB : PhaseBInt)
    (c ν : ℝ) (χo : ℝ → ℝ) (hc : 0 < c) (hν : 0 < ν) (hχ : IsOutwardCutoff χo)
    (M : Chart → Mat3) (hM : OldThinFinite c ν M) :
    (∀ x' : ℝ × ℝ, ν * (5 / 6) < x'.1 ^ 2 + x'.2 ^ 2 → sigmaM c ν χo M x' = 0) ∧
    Integrable (fun x' : ℝ × ℝ => sigmaM c ν χo M x') ∧
    ∫ x' : ℝ × ℝ, frob (sigmaM c ν χo M x') ≤ Real.pi * oldN0 c ν M := by
  have hmeas := hS c ν χo hc hν hχ M hM
  have hL := sigmaM_lintegral_le hP hPol hB hc hν hχ hM
  have hN0 := oldN0_nonneg c ν hν M
  have hfin : (∫⁻ x' : ℝ × ℝ, ENNReal.ofReal (frob (sigmaM c ν χo M x'))) < ∞ :=
    lt_of_le_of_lt hL ENNReal.ofReal_lt_top
  have hg : Integrable (fun x' : ℝ × ℝ => frob (sigmaM c ν χo M x')) :=
    ⟨continuous_frob.comp_aestronglyMeasurable hmeas,
      (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun _ => frob_nonneg' _)).2 hfin⟩
  refine ⟨fun x' hx => sigmaM_support hν hχ M x' hx, ?_, ?_⟩
  · exact hg.mono' hmeas (Filter.Eventually.of_forall fun x' => norm_le_frob _)
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => frob_nonneg' _)
      hg.aestronglyMeasurable]
    calc (∫⁻ x' : ℝ × ℝ, ENNReal.ofReal (frob (sigmaM c ν χo M x'))).toReal
        ≤ (ENNReal.ofReal (Real.pi * oldN0 c ν M)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hL
      _ = Real.pi * oldN0 c ν M := ENNReal.toReal_ofReal (mul_nonneg Real.pi_pos.le hN0)

end UnforcedLeray.Short.PartIIIb.Concrete
