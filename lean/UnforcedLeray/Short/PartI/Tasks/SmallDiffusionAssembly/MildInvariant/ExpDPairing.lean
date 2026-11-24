import UnforcedLeray.Short.PartI.Sub.PartI_C05_4
import UnforcedLeray.Cons.L2.CanonicalBranch.CanonicalAmplitudeGenerator
import UnforcedLeray.Short.PartI.Tasks.SmallDiffusionAssembly.MildInvariant.ExpDPairing.Scalar

/-!
# Target `PartI:C05/4/2`: the measurable-clock pairing identity

Source of record: `the November 2 reference manuscript`, lines 1056-1058.
The clock `B(τ) = ∫_r^τ β` is only measurable. The vector Duhamel identity
`e^{B(t)D} qd = qd + ∫ β(τ) e^{B(τ)D} (D qd) dτ` is proved coordinatewise in the oscillator basis,
where it is the scalar identity of `ExpDPairing/Scalar.lean`. The pairing then follows by
selfadjointness of `e^{aD}` for `a ≥ 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology intervalIntegral

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-- Interchange of a first-slot interval integral with the inner product against `z`. -/
theorem inner_intervalIntegral_left {f : ℝ → B0010.XG} {r t : ℝ} (hrt : r ≤ t)
    (hf : IntervalIntegrable f volume r t) (z : B0010.XG) :
    inner ℂ (∫ τ in r..t, f τ) z = ∫ τ in r..t, inner ℂ (f τ) z := by
  have h1 : inner ℂ (∫ τ in r..t, f τ) z =
      (starRingEnd ℂ) (inner ℂ z (∫ τ in r..t, f τ)) := (inner_conj_symm _ _).symm
  have h2 : ∫ τ in r..t, inner ℂ z (f τ) = inner ℂ z (∫ τ in r..t, f τ) := by
    have := (innerSL ℂ z).intervalIntegral_comp_comm hf
    simpa only [innerSL_apply_apply] using this
  rw [h1, ← h2, intervalIntegral.integral_of_le hrt, intervalIntegral.integral_of_le hrt,
    ← integral_conj]
  refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun x => ?_)
  exact inner_conj_symm _ _

/-- Interval integrability of the Duhamel integrand `τ ↦ β(τ) e^{B(τ)D} (D qd)`. -/
theorem integrable_clock_vec (qd : B0010.XG) (hqd : qd ∈ B0094.D.domain) (β : ℝ → ℝ)
    (hβm : Measurable β) (hβ01 : ∀ τ, 0 ≤ β τ ∧ β τ ≤ 1) (r t : ℝ) :
    IntervalIntegrable (fun τ => (β τ : ℂ) •
      B0123.expD (∫ u in r..τ, β u) (B0094.D ⟨qd, hqd⟩)) volume r t := by
  have hBc : Continuous fun τ => ∫ u in r..τ, β u :=
    intervalIntegral.continuous_primitive (fun a b => ExpDPairingHelp.beta_intervalIntegrable
      hβm hβ01 a b) r
  have hv : Continuous fun τ => B0123.expD (∫ u in r..τ, β u) (B0094.D ⟨qd, hqd⟩) :=
    (Cons.G3b.continuous_expD_apply (B0094.D ⟨qd, hqd⟩)).comp hBc
  obtain ⟨C, hC⟩ := (isCompact_uIcc (a := r) (b := t)).exists_bound_of_continuousOn
    hv.continuousOn
  have hmeas : AEStronglyMeasurable (fun τ => (β τ : ℂ) •
      B0123.expD (∫ u in r..τ, β u) (B0094.D ⟨qd, hqd⟩)) volume :=
    ((Complex.measurable_ofReal.comp hβm).aestronglyMeasurable).smul hv.aestronglyMeasurable
  refine (intervalIntegrable_const (c := C)).mono_fun' hmeas.restrict ?_
  refine (ae_restrict_iff' measurableSet_uIoc).mpr (Eventually.of_forall fun x hx => ?_)
  have hb : ‖β x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [(hβ01 x).1], (hβ01 x).2⟩
  calc ‖(β x : ℂ) • B0123.expD (∫ u in r..x, β u) (B0094.D ⟨qd, hqd⟩)‖
      = ‖β x‖ * ‖B0123.expD (∫ u in r..x, β u) (B0094.D ⟨qd, hqd⟩)‖ := by
        rw [norm_smul, Complex.norm_real]
    _ ≤ 1 * C := mul_le_mul hb (hC x (Set.uIoc_subset_uIcc hx)) (norm_nonneg _) zero_le_one
    _ = C := one_mul C

/-- The scalar clock identity for `ℓ = e^{B(t)}` in multiplier form. -/
theorem expMult_clock (n : ℕ) {r t : ℝ} (hrt : r ≤ t) (β : ℝ → ℝ) (hβm : Measurable β)
    (hβ01 : ∀ τ, 0 ≤ β τ ∧ β τ ≤ 1) :
    B0123.expMult (∫ u in r..t, β u) n =
      1 + ∫ τ in r..t, (β τ : ℂ) * (B0123.expMult (∫ u in r..τ, β u) n * (-(n : ℂ))) := by
  have hreal := ExpDPairingHelp.scalar_exp_clock n hrt β hβm hβ01
  have hBnn : ∀ τ ∈ uIcc r t, 0 ≤ ∫ u in r..τ, β u := by
    intro τ hτ
    rw [uIcc_of_le hrt] at hτ
    exact intervalIntegral.integral_nonneg hτ.1 (fun u _ => (hβ01 u).1)
  have hpt : ∀ τ ∈ uIcc r t, B0123.expMult (∫ u in r..τ, β u) n =
      ((Real.exp (-(n : ℝ) * ∫ u in r..τ, β u) : ℝ) : ℂ) := by
    intro τ hτ
    rw [B0123.expMult, max_eq_left (hBnn τ hτ)]
    congr 2
    ring
  have hint2 : (∫ τ in r..t, (β τ : ℂ) * (B0123.expMult (∫ u in r..τ, β u) n * (-(n : ℂ)))) =
      ((∫ τ in r..t, Real.exp (-(n : ℝ) * ∫ u in r..τ, β u) * (-(n : ℝ) * β τ) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro τ hτ
    dsimp only
    rw [hpt τ hτ]
    push_cast
    ring
  rw [hint2, hpt t (by rw [uIcc_of_le hrt]; exact ⟨hrt, le_rfl⟩)]
  have hr : Real.exp (-(n : ℝ) * ∫ u in r..t, β u) =
      1 + ∫ τ in r..t, Real.exp (-(n : ℝ) * ∫ u in r..τ, β u) * (-(n : ℝ) * β τ) := by
    linarith [hreal]
  rw [hr]
  push_cast
  rfl

/-- The vector Duhamel identity with a measurable clock, tested in the oscillator basis. -/
theorem duhamel_vec (qd : B0010.XG) (hqd : qd ∈ B0094.D.domain) (β : ℝ → ℝ)
    (hβm : Measurable β) (hβ01 : ∀ τ, 0 ≤ β τ ∧ β τ ≤ 1) {r t : ℝ} (hrt : r ≤ t) :
    B0123.expD (∫ u in r..t, β u) qd = qd + ∫ τ in r..t, (β τ : ℂ) •
      B0123.expD (∫ u in r..τ, β u) (B0094.D ⟨qd, hqd⟩) := by
  apply B0094.ext_inner_basis
  intro n
  have hint := integrable_clock_vec qd hqd β hβm hβ01 r t
  have hI : inner ℂ (B0094.oscBasis n) (∫ τ in r..t, (β τ : ℂ) •
      B0123.expD (∫ u in r..τ, β u) (B0094.D ⟨qd, hqd⟩)) =
      ∫ τ in r..t, inner ℂ (B0094.oscBasis n) ((β τ : ℂ) •
        B0123.expD (∫ u in r..τ, β u) (B0094.D ⟨qd, hqd⟩)) := by
    have := (innerSL ℂ (B0094.oscBasis n)).intervalIntegral_comp_comm hint
    simpa only [innerSL_apply_apply] using this.symm
  have hcoord : ∀ τ ∈ uIcc r t, inner ℂ (B0094.oscBasis n) ((β τ : ℂ) •
      B0123.expD (∫ u in r..τ, β u) (B0094.D ⟨qd, hqd⟩)) =
      (β τ : ℂ) * (B0123.expMult (∫ u in r..τ, β u) n * (-(n : ℂ))) *
        inner ℂ (B0094.oscBasis n) qd := by
    intro τ _
    rw [inner_smul_right, B0123.inner_expD, B0123.inner_D ⟨qd, hqd⟩ n]
    dsimp only
    ring
  rw [inner_add_right, hI, intervalIntegral.integral_congr hcoord,
    intervalIntegral.integral_mul_const, B0123.inner_expD, expMult_clock n hrt β hβm hβ01]
  ring

/-- **Target `PartI:C05/4/2`**: the measurable-clock pairing identity. -/
theorem expDPairingMeasurable : ExpDPairingMeasurable := by
  unfold ExpDPairingMeasurable
  intro qd hqd β hβm hβ01 r t hrt z
  have ha : 0 ≤ ∫ u in r..t, β u := intervalIntegral.integral_nonneg hrt (fun u _ => (hβ01 u).1)
  have hg := integrable_clock_vec qd hqd β hβm hβ01 r t
  calc inner ℂ qd (B0123.expD (∫ u in r..t, β u) z)
      = inner ℂ (B0123.expD (∫ u in r..t, β u) qd) z := by
        rw [← ContinuousLinearMap.adjoint_inner_left, Cons.G3b.expD_adjoint_eq_self ha]
    _ = inner ℂ (qd + ∫ τ in r..t, (β τ : ℂ) •
          B0123.expD (∫ u in r..τ, β u) (B0094.D ⟨qd, hqd⟩)) z := by
        rw [duhamel_vec qd hqd β hβm hβ01 hrt]
    _ = inner ℂ qd z + ∫ τ in r..t, inner ℂ ((β τ : ℂ) •
          B0123.expD (∫ u in r..τ, β u) (B0094.D ⟨qd, hqd⟩)) z := by
        rw [inner_add_left, inner_intervalIntegral_left hrt hg z]
    _ = inner ℂ qd z + ∫ τ in r..t, (β τ : ℂ) *
          inner ℂ (B0094.D ⟨qd, hqd⟩) (B0123.expD (∫ u in r..τ, β u) z) := by
        congr 1
        apply intervalIntegral.integral_congr
        intro τ hτ
        dsimp only
        have hb : 0 ≤ ∫ u in r..τ, β u := by
          rw [uIcc_of_le hrt] at hτ
          exact intervalIntegral.integral_nonneg hτ.1 (fun u _ => (hβ01 u).1)
        have hadj := ContinuousLinearMap.adjoint_inner_left
          (B0123.expD (∫ u in r..τ, β u)) z (B0094.D ⟨qd, hqd⟩)
        rw [Cons.G3b.expD_adjoint_eq_self hb] at hadj
        simp only [inner_smul_left, Complex.conj_ofReal]
        rw [hadj]

end UnforcedLeray.Short.PartI
