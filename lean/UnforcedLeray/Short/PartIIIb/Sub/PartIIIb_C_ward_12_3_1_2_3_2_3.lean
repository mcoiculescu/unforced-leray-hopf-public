import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_3_2

/-!
# `PartIII-b:C/ward/12/3/1/2/3/2/3`: decomposition of `MollDerivIdentity` (source 1415-1424, 2531)

`mollDerivIdentity_of` reduces `MollDerivIdentity` (a.e. `τ`, all `n`, all `y`) to the pointwise
version `MollDerivAtPoint` (for each fixed `n` and `y`, a.e. `τ`) and `MollSliceFacts`
(smoothness of the slice mollification): take the countable dense set of points `y`, intersect
the countably many a.e. sets, and extend to all `y` by continuity of both sides.

Source of record `the November 2 reference manuscript`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology
open UnforcedLeray.Cons.C03.Concrete (rep)

/-- **Pointwise version of `MollDerivIdentity`** (source 1415-1424): for fixed `n` and `y`, the
identity holds for a.e. `τ`.  Proof idea: test `HasPhaseOp (-dy j) w g` against
`Φ(τ, z) = a(τ) ρ_n(y - z) e_c` with `a` smooth `P`-periodic, differentiate under the integral
(`HasCompactSupport.hasFDerivAt_convolution_left`), and apply the fundamental lemma in `τ`. -/
def MollDerivAtPoint : Prop :=
  ∀ ρ : ℕ → UnforcedLeray.Space → ℝ, MollSeq ρ → ∀ (P : ℝ) [Fact (0 < P)]
    (w g : Yq P UnforcedLeray.B0412.q0E) (j : Fin 3),
    HasPhaseOp (fun Φ => -dy j Φ) w g →
    ∀ (n : ℕ) (y : UnforcedLeray.Space), ∀ᵐ τ ∂(volume : Measure ℝ),
      fderiv ℝ (Moll (ρ n) (rep w τ)) y (EuclideanSpace.single j 1) = Moll (ρ n) (rep g τ) y

theorem mollDerivIdentity_of (h2 : MollSliceFacts) (h : MollDerivAtPoint) :
    MollDerivIdentity := by
  intro ρ hρ P _ w g j hop
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense UnforcedLeray.Space
  have hae : ∀ᵐ τ ∂(volume : Measure ℝ), ∀ n : ℕ, ∀ y ∈ D,
      fderiv ℝ (Moll (ρ n) (rep w τ)) y (EuclideanSpace.single j 1) = Moll (ρ n) (rep g τ) y := by
    rw [ae_all_iff]
    intro n
    rw [ae_ball_iff hDc]
    intro y _
    exact h ρ hρ P w g j hop n y
  filter_upwards [hae] with τ hτ n y
  have hw := (h2 ρ hρ n (rep w τ) (memLp_rep_slice w τ)).1
  have hg := (h2 ρ hρ n (rep g τ) (memLp_rep_slice g τ)).1
  have hc1 : Continuous (fun z => fderiv ℝ (Moll (ρ n) (rep w τ)) z (EuclideanSpace.single j 1)) :=
    ((hw.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hc2 : Continuous (Moll (ρ n) (rep g τ)) := hg.continuous
  have := Continuous.ext_on hDd hc1 hc2 (fun z hz => hτ n z hz)
  exact congrFun this y


/-! ## Splitting `MollDerivAtPoint` -/

/-- The `c`-th component of the slice defect `∂_j(ρ * rep w τ)(y) - (ρ * rep g τ)(y)`. -/
def mollSliceDiff (K : UnforcedLeray.Space → ℝ) {P : ℝ} [Fact (0 < P)]
    (w g : Yq P UnforcedLeray.B0412.q0E) (j : Fin 3) (y : UnforcedLeray.Space) (c : Fin 3)
    (t : ℝ) : ℂ :=
  (fderiv ℝ (Moll K (rep w t)) y (EuclideanSpace.single j 1) - Moll K (rep g t) y) c

/-- **Lemma 1** (differentiation under the integral; Mathlib
`HasCompactSupport.hasFDerivAt_convolution_left` after `moll_eq_convolution_lsmul`). -/
def MollFderivApply : Prop :=
  ∀ (K : UnforcedLeray.Space → ℝ), ContDiff ℝ 1 K → HasCompactSupport K →
    ∀ (f : UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3), LocallyIntegrable f volume →
    ∀ x v : UnforcedLeray.Space,
      fderiv ℝ (Moll K f) x v = ∫ z, fderiv ℝ K (x - z) v • f z

/-- **Lemma 2** (fundamental lemma of calculus of variations for periodic functions): a
`P`-periodic locally integrable `ℂ`-valued function orthogonal to all smooth `P`-periodic real
functions on one period vanishes a.e. (Take `a = Σ_k b(· + kP)` with `b ∈ C_c^∞(ℝ)` and use
`ae_eq_zero_of_integral_contDiff_smul_eq_zero`.) -/
def PeriodicFundamental : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (F : ℝ → ℂ), Function.Periodic F P → LocallyIntegrable F volume →
    (∀ a : ℝ → ℝ, ContDiff ℝ ∞ a → Function.Periodic a P → ∫ t in Ioc (0 : ℝ) P, a t • F t = 0) →
    ∀ᵐ t ∂(volume : Measure ℝ), F t = 0

/-- **Lemma 3** (local integrability in the phase variable of the slice defect, from
`‖ρ_n * rep w τ (y)‖ ≤ ‖ρ_n‖_{q'}‖rep w τ‖_q` and `τ ↦ ‖rep w τ‖_q` in `L^q(0,P)`, periodic). -/
def MollSliceLocInt : Prop :=
  ∀ ρ : ℕ → UnforcedLeray.Space → ℝ, MollSeq ρ → ∀ (P : ℝ) [Fact (0 < P)]
    (w g : Yq P UnforcedLeray.B0412.q0E) (j : Fin 3) (n : ℕ) (y : UnforcedLeray.Space) (c : Fin 3),
    LocallyIntegrable (mollSliceDiff (ρ n) w g j y c) volume

/-- **Lemma 4** (test-function instance, source 1415-1424): testing `HasPhaseOp (-dy j) w g` with
`Φ(τ, z) = a(τ) ρ_n(y - z) e_c` (an `IsPhaseTest`), using `phasePair_eq_periodIntegral` and
Lemma 1. -/
def MollSliceTest : Prop :=
  ∀ ρ : ℕ → UnforcedLeray.Space → ℝ, MollSeq ρ → ∀ (P : ℝ) [Fact (0 < P)]
    (w g : Yq P UnforcedLeray.B0412.q0E) (j : Fin 3),
    HasPhaseOp (fun Φ => -dy j Φ) w g →
    ∀ (n : ℕ) (y : UnforcedLeray.Space) (c : Fin 3) (a : ℝ → ℝ), ContDiff ℝ ∞ a →
      Function.Periodic a P →
      ∫ t in Ioc (0 : ℝ) P, a t • mollSliceDiff (ρ n) w g j y c t = 0

theorem mollDerivAtPoint_of (h2 : PeriodicFundamental) (h3 : MollSliceLocInt)
    (h4 : MollSliceTest) : MollDerivAtPoint := by
  intro ρ hρ P _ w g j hop n y
  have hper : ∀ c : Fin 3, Function.Periodic (mollSliceDiff (ρ n) w g j y c) P := by
    intro c t
    have hw : rep w (t + P) = rep w t := funext fun z =>
      UnforcedLeray.Cons.C03.Concrete.rep_add_period w t z
    have hg : rep g (t + P) = rep g t := funext fun z =>
      UnforcedLeray.Cons.C03.Concrete.rep_add_period g t z
    simp only [mollSliceDiff, hw, hg]
  have hc : ∀ c : Fin 3, ∀ᵐ t ∂(volume : Measure ℝ), mollSliceDiff (ρ n) w g j y c t = 0 :=
    fun c => h2 P _ (hper c) (h3 ρ hρ P w g j n y c) (fun a ha hap => h4 ρ hρ P w g j hop n y c a ha hap)
  have hall : ∀ᵐ t ∂(volume : Measure ℝ), ∀ c : Fin 3, mollSliceDiff (ρ n) w g j y c t = 0 :=
    ae_all_iff.2 hc
  filter_upwards [hall] with t ht
  ext c
  have := ht c
  simp only [mollSliceDiff, PiLp.sub_apply] at this
  exact sub_eq_zero.1 this

end UnforcedLeray.Short.PartIIIb.Concrete
