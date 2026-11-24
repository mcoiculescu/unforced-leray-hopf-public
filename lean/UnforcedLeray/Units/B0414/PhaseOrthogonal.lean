import UnforcedLeray.Units.B0414.Orthogonal
import UnforcedLeray.Lib.LerayC.PhaseSol

/-!
# B0414 helper: at `q = 2` the phase Leray projection is an orthogonal projection on `Y_2`

Blueprint unit B0414 (`paper/main.tex` lines 7336–7344: `P_σ` is bounded on `L^q`, "hence on
`Y_q`", and "it is an orthogonal projection at `q = 2`"). The phase operator is the drafted
`RieszLp.lerayY P q` (`Lib/LerayC/Phase.lean`, INF01 T17): `lerayC q` applied slice by slice on
`Y_q = L^q(ℝ/Pℤ; L^q(ℝ³; ℂ³))` (decision D2, `PhaseSpace.Yq`).

* `solenoidalY P`: the closed `ℂ`-subspace of `Y_2` of fields whose phase slices are a.e.
  distributionally solenoidal (`mem_solenoidalY_iff`, `isClosed_solenoidalY`);
* `lerayY_two`: `lerayY P 2 = (solenoidalY P).starProjection`, the orthogonal projection;
  consequences `norm_lerayY_two_le` (`C_2 = 1`, tex 7444), `inner_lerayY_two_left_eq_right`
  (symmetry), `lerayY_two_eq_self_iff`;
* `isPhaseSolenoidal_of_mem_solenoidalY`: slice-wise solenoidal fields are solenoidal in the
  phase-space distribution sense `PhaseSpace.IsPhaseSolenoidal` (via the drafted
  `RieszLp.lerayY_isPhaseSolenoidal`, `Lib/LerayC/PhaseSol.lean`).

The converse (`IsPhaseSolenoidal f` implies a.e. slice-wise solenoidality) is not proved here.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology InnerProductSpace

namespace UnforcedLeray.B0414

open UnforcedLeray.RieszLp
open UnforcedLeray.PhaseSpace (CVec3 Yq)

variable {P : ℝ} [Fact (0 < P)]

/-- **B0414 (ii) on `Y_2`, the range.** The fields of `Y_2` whose phase slices are a.e.
distributionally solenoidal (`IsSolenoidalC`). -/
def solenoidalY (P : ℝ) [Fact (0 < P)] : Submodule ℂ (Yq P 2) where
  carrier := {f | ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)), f τ ∈ solenoidalC}
  add_mem' {f g} hf hg := by
    filter_upwards [hf, hg, Lp.coeFn_add f g] with τ h1 h2 h3
    rw [h3, Pi.add_apply]
    exact add_mem h1 h2
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero (Lp CVec3 2 (volume : Measure Space)) 2
      (AddCircle.haarAddCircle (T := P))] with τ h
    rw [h, Pi.zero_apply]
    exact zero_mem _
  smul_mem' c f hf := by
    filter_upwards [hf, Lp.coeFn_smul c f] with τ h1 h2
    rw [h2, Pi.smul_apply]
    exact Submodule.smul_mem _ c h1

theorem mem_solenoidalY_iff_slices (f : Yq P 2) :
    f ∈ solenoidalY P ↔ ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)), f τ ∈ solenoidalC := Iff.rfl

/-- Membership in `solenoidalY` is a.e. slice-wise distributional solenoidality. -/
theorem mem_solenoidalY_iff (f : Yq P 2) :
    f ∈ solenoidalY P ↔
      ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)), IsSolenoidalC (f τ : Space → CVec3) := by
  rw [mem_solenoidalY_iff_slices]
  simp_rw [mem_solenoidalC_iff]

/-- The residual operator `I - Q` on `L²(ℝ³; ℂ³)`, `Q` the orthogonal projection onto
`solenoidalC`. -/
abbrev residualC : Lp CVec3 2 (volume : Measure Space) →L[ℂ] Lp CVec3 2 (volume : Measure Space) :=
  ContinuousLinearMap.id ℂ _ - solenoidalC.starProjection

theorem mem_solenoidalY_iff_ker (f : Yq P 2) :
    f ∈ solenoidalY P ↔ residualC.compLpL 2 (AddCircle.haarAddCircle (T := P)) f = 0 := by
  rw [Lp.eq_zero_iff_ae_eq_zero]
  have h := residualC.coeFn_compLpL (μ := AddCircle.haarAddCircle (T := P)) (p := 2) f
  constructor
  · intro hf
    filter_upwards [hf, h] with τ h1 h2
    rw [h2, Pi.zero_apply, _root_.sub_apply, ContinuousLinearMap.id_apply,
      Submodule.starProjection_eq_self_iff.mpr h1, sub_self]
  · intro hT
    filter_upwards [hT, h] with τ h1 h2
    rw [h2, Pi.zero_apply, _root_.sub_apply, ContinuousLinearMap.id_apply,
      sub_eq_zero] at h1
    exact Submodule.starProjection_eq_self_iff.mp h1.symm

theorem isClosed_solenoidalY : IsClosed (solenoidalY P : Set (Yq P 2)) := by
  have e : (solenoidalY P : Set (Yq P 2)) =
      {f | residualC.compLpL 2 (AddCircle.haarAddCircle (T := P)) f = 0} := by
    ext f
    exact mem_solenoidalY_iff_ker f
  rw [e]
  exact isClosed_eq (residualC.compLpL 2 AddCircle.haarAddCircle).continuous continuous_const

instance solenoidalY_completeSpace : CompleteSpace (solenoidalY P) :=
  isClosed_solenoidalY.completeSpace_coe

theorem lerayY_two_mem (f : Yq P 2) :
    lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top f ∈ solenoidalY P := by
  filter_upwards [coeFn_lerayY ENNReal.one_lt_two ENNReal.ofNat_ne_top f] with τ h
  rw [h]
  exact lerayC_two_mem _

theorem inner_residualY_eq_zero (f : Yq P 2) {g : Yq P 2} (hg : g ∈ solenoidalY P) :
    ⟪f - lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top f, g⟫_ℂ = 0 := by
  rw [L2.inner_def]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hg, coeFn_lerayY ENNReal.one_lt_two ENNReal.ofNat_ne_top f,
    Lp.coeFn_sub f (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top f)] with τ h1 h2 h3
  rw [h3, Pi.sub_apply, h2, Pi.zero_apply]
  exact inner_residual_eq_zero _ h1

/-- **B0414 (ii) on `Y_2`.** At `q = 2` the phase Leray projection is the orthogonal projection
of `Y_2` onto the fields with a.e. solenoidal phase slices (tex 7340–7342). -/
theorem lerayY_two :
    lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top = (solenoidalY P).starProjection := by
  ext1 f
  symm
  exact Submodule.eq_starProjection_of_mem_of_inner_eq_zero (lerayY_two_mem f)
    fun g hg => inner_residualY_eq_zero f hg

/-- `C_2 = 1`: `‖P_σ‖_{Y_2 → Y_2} ≤ 1` (tex 7444, eq:free-stress-10 with `C_2 = 1`). -/
theorem norm_lerayY_two_le : ‖lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top‖ ≤ 1 := by
  rw [lerayY_two]
  exact (solenoidalY P).starProjection_norm_le

/-- At `q = 2`, `P_σ` is symmetric on `Y_2`. -/
theorem inner_lerayY_two_left_eq_right (f g : Yq P 2) :
    ⟪lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top f, g⟫_ℂ =
      ⟪f, lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top g⟫_ℂ := by
  rw [lerayY_two]
  exact (solenoidalY P).inner_starProjection_left_eq_right f g

theorem lerayY_two_eq_self_iff (f : Yq P 2) :
    lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top f = f ↔ f ∈ solenoidalY P := by
  rw [lerayY_two, Submodule.starProjection_eq_self_iff]

/-- Fields of `Y_2` with a.e. solenoidal slices are solenoidal in the phase-space distribution
sense of `PhaseSpace.IsPhaseSolenoidal` (tex 7333–7334). -/
theorem isPhaseSolenoidal_of_mem_solenoidalY {f : Yq P 2} (hf : f ∈ solenoidalY P) :
    PhaseSpace.IsPhaseSolenoidal f := by
  have h := lerayY_isPhaseSolenoidal (P := P) ENNReal.one_lt_two ENNReal.ofNat_ne_top f
  rwa [(lerayY_two_eq_self_iff f).mpr hf] at h

end UnforcedLeray.B0414
