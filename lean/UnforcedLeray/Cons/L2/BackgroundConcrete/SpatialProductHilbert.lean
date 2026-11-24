import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductWeakDeriv
import UnforcedLeray.Units.B0448.Fundamental
import UnforcedLeray.Lib.SobolevC.CylTransfer
import UnforcedLeray.Lib.SobolevB.Mollify
import UnforcedLeray.Units.B0424.Tests
import UnforcedLeray.Units.B0005.Bridge.Weak
import UnforcedLeray.Lib.PhaseTrace.Periodize
import UnforcedLeray.Lib.Semigroups.Multiplication

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal Topology

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint
open UnforcedLeray.PhaseSpace
open UnforcedLeray.Sob
open UnforcedLeray.B0448
open UnforcedLeray.B0424
open UnforcedLeray.B0005
open UnforcedLeray.PhaseTrace

/-- Multiplication by a smooth coefficient constant along `v` preserves a weak derivative. -/
theorem hasWeakDeriv_smul_of_fderiv_eq_zero {n : ℕ} {dir : Fin n → SpaceTime}
    {v : SpaceTime} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {a : SpaceTime → ℝ} (ha : ContDiff ℝ ∞ a)
    (hda : ∀ x, fderiv ℝ a x v = 0) {f g : SpaceTime → F}
    (h : HasWeakDeriv (wholeSpaceOf SpaceTime volume dir) [v] f g) :
    HasWeakDeriv (wholeSpaceOf SpaceTime volume dir) [v]
      (fun x => a x • f x) (fun x => a x • g x) := by
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · rcases hφ with ⟨hs, hc⟩
    have hψ : (wholeSpaceOf SpaceTime volume dir).Adm
        (fun x => φ x * a x) := ⟨hs.mul ha, hc.mul_right⟩
    have hi := h.int_left _ hψ
    have heq : (fun x => fderiv ℝ φ x v • (a x • f x)) =
        (fun x => fderiv ℝ (fun y => φ y * a y) x v • f x) := by
      funext x
      have hφx : DifferentiableAt ℝ φ x := hs.differentiable (by simp) x
      have hax : DifferentiableAt ℝ a x := ha.differentiable (by simp) x
      have hmul := fderiv_mul hφx hax
      have hv := congrArg (fun L : SpaceTime →L[ℝ] ℝ => L v) hmul
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul] at hv
      rw [hda x] at hv
      have hv' : fderiv ℝ (φ * a) x v =
          a x * fderiv ℝ φ x v := by simpa only [mul_zero, zero_add] using hv
      have hfun : (φ * a) = (fun y => φ y * a y) := rfl
      rw [← hfun, hv']
      simp [smul_smul, mul_assoc, mul_left_comm, mul_comm]
    have hi' := hi.congr (Eventually.of_forall (fun x => (congrFun heq x).symm))
    simpa only [iterDirDeriv_singleton] using hi'
  · rcases hφ with ⟨hs, hc⟩
    have hψ : (wholeSpaceOf SpaceTime volume dir).Adm
        (fun x => φ x * a x) := ⟨hs.mul ha, hc.mul_right⟩
    have hi := h.int_right _ hψ
    have heq : (fun x => φ x • (a x • g x)) =
        (fun x => (φ x * a x) • g x) := by
      funext x
      simp [smul_smul]
    rw [heq]
    exact hi
  · rcases hφ with ⟨hs, hc⟩
    have hψ : (wholeSpaceOf SpaceTime volume dir).Adm
        (fun x => φ x * a x) := ⟨hs.mul ha, hc.mul_right⟩
    have hid := h.identity _ hψ
    have heqL : (fun x => fderiv ℝ φ x v • (a x • f x)) =
        (fun x => fderiv ℝ (fun y => φ y * a y) x v • f x) := by
      funext x
      have hφx : DifferentiableAt ℝ φ x := hs.differentiable (by simp) x
      have hax : DifferentiableAt ℝ a x := ha.differentiable (by simp) x
      have hmul := fderiv_mul hφx hax
      have hv := congrArg (fun L : SpaceTime →L[ℝ] ℝ => L v) hmul
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul] at hv
      rw [hda x] at hv
      have hv' : fderiv ℝ (φ * a) x v =
          a x * fderiv ℝ φ x v := by simpa only [mul_zero, zero_add] using hv
      have hfun : (φ * a) = (fun y => φ y * a y) := rfl
      rw [← hfun, hv']
      simp [smul_smul, mul_assoc, mul_left_comm, mul_comm]
    have heqR : (fun x => φ x • (a x • g x)) =
        (fun x => (φ x * a x) • g x) := by
      funext x
      simp [smul_smul]
    calc
      ∫ x, fderiv ℝ φ x v • (a x • f x) =
          ∫ x, fderiv ℝ (fun y => φ y * a y) x v • f x := by
            exact integral_congr_ae (Eventually.of_forall (fun x => congrFun heqL x))
      _ = (-1 : ℝ) ^ (1 : ℕ) • ∫ x, (φ x * a x) • g x := hid
      _ = (-1 : ℝ) ^ (1 : ℕ) • ∫ x, φ x • (a x • g x) := by
            rw [integral_congr_ae (Eventually.of_forall (fun x => (congrFun heqR x).symm))]

/-- A phase-only scalar coefficient on ordinary spacetime. -/
def phaseCutoffSpaceTime (χ : ℝ → ℝ) (z : SpaceTime) : ℝ := χ z.1

theorem contDiff_phaseCutoffSpaceTime {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (phaseCutoffSpaceTime χ) :=
  hχ.comp (ContinuousLinearMap.fst ℝ ℝ Space).contDiff

theorem fderiv_phaseCutoffSpaceTime_spatial {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {v : SpaceTime} (hv : v.1 = 0) (z : SpaceTime) :
    fderiv ℝ (phaseCutoffSpaceTime χ) z v = 0 := by
  have hproj : HasFDerivAt (fun x : SpaceTime => x.1)
      (ContinuousLinearMap.fst ℝ ℝ Space) z :=
    (ContinuousLinearMap.fst ℝ ℝ Space).hasFDerivAt
  have hχF : HasFDerivAt χ (fderiv ℝ χ z.1) z.1 :=
    (hχ.differentiable (by simp) z.1).hasFDerivAt
  have hcomp := hχF.comp z hproj
  change fderiv ℝ (χ ∘ Prod.fst) z v = 0
  rw [hcomp.fderiv]
  change fderiv ℝ χ z.1 v.1 = 0
  rw [hv]
  simp

theorem hasWeakDeriv_phaseCutoffSpaceTime {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {n : ℕ} {dir : Fin n → SpaceTime} {v : SpaceTime} (hv : v.1 = 0)
    {f g : SpaceTime → ℂ}
    (h : HasWeakDeriv (wholeSpaceOf SpaceTime volume dir) [v] f g) :
    HasWeakDeriv (wholeSpaceOf SpaceTime volume dir) [v]
      (fun z => phaseCutoffSpaceTime χ z • f z)
      (fun z => phaseCutoffSpaceTime χ z • g z) :=
  hasWeakDeriv_smul_of_fderiv_eq_zero (contDiff_phaseCutoffSpaceTime hχ)
    (fun z => fderiv_phaseCutoffSpaceTime_spatial hχ hv z) h

/-- A phase cutoff makes the compact spatial support of a phase test compact in spacetime. -/
theorem hasCompactSupport_phaseCutoff_scalarTestBackground {P : ℝ}
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {U : ℝ → SpatialField} {χ : ℝ → ℝ} (hχc : HasCompactSupport χ) :
    HasCompactSupport (fun z : SpaceTime => phaseCutoffSpaceTime χ z •
      scalarTestBackground Φ U z) := by
  obtain ⟨R, hR⟩ := hΦ.bounded_support
  obtain ⟨M, hM0, hM⟩ := exists_bound_real hχc
  refine HasCompactSupport.intro (K := Icc (-M) M ×ˢ Metric.closedBall (0 : Space) R)
    (isCompact_Icc.prod (isCompact_closedBall _ _)) fun z hz => ?_
  simp only [mem_prod, mem_Icc, Metric.mem_closedBall, dist_zero_right,
    not_and_or, not_le] at hz
  rcases hz with hτ | hy
  · have hχzero : χ z.1 = 0 := by
      apply hM
      rcases hτ with hτ | hτ
      · rw [abs_of_neg (by linarith [hM0])]
        linarith
      · exact hτ.trans_le (le_abs_self _)
    simp [phaseCutoffSpaceTime, hχzero]
  · have hΦzero : Φ (z.1, z.2) = 0 := hR z.1 z.2 hy
    simp [phaseCutoffSpaceTime, scalarTestBackground, hΦzero]

/-- The actual compact-test/background product retains its weak spatial derivative after cutoff. -/
theorem hasWeakSpatialDerivative_cutoff_scalarTestBackground {P : ℝ}
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {U : ℝ → SpatialField} (hU : IsBoundedBackground U)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (j : Fin 3) :
    HasWeakDeriv
      (wholeSpaceOf SpaceTime volume scalarTestSpaceTimeDir)
      [scalarTestSpaceTimeDir j]
      (fun z : SpaceTime => phaseCutoffSpaceTime χ z • scalarTestBackground Φ U z)
      (fun z : SpaceTime => phaseCutoffSpaceTime χ z •
        fderiv ℝ (fun x : Space => scalarTestBackground Φ U (z.1, x)) z.2
          (EuclideanSpace.single j (1 : ℝ))) := by
  have hbase := hasWeakSpatialDerivative_scalarTestBackground hΦ hU j
  exact hasWeakDeriv_smul_of_fderiv_eq_zero
    (contDiff_phaseCutoffSpaceTime hχ)
    (fun z => fderiv_phaseCutoffSpaceTime_spatial hχ rfl z) hbase

#print axioms hasWeakDeriv_smul_of_fderiv_eq_zero
#print axioms hasWeakDeriv_phaseCutoffSpaceTime
#print axioms hasCompactSupport_phaseCutoff_scalarTestBackground
#print axioms hasWeakSpatialDerivative_cutoff_scalarTestBackground

/-- The Euclidean Hilbert realization of spacetime. -/
def spacetimeHilbertEquiv : SpaceTime ≃L[ℝ] ST :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ Space).symm

/-- Transfer a whole-spacetime weak derivative to the Hilbert carrier used by mollification. -/
theorem hasWeakDeriv_spacetimeHilbertEquiv {n : ℕ} {dir : Fin n → SpaceTime}
    {vs : List SpaceTime} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {f g : SpaceTime → F}
    (h : HasWeakDeriv (wholeSpaceOf SpaceTime volume dir) vs f g) :
    HasWeakDeriv
      (wholeSpaceOf ST volume (fun i => spacetimeHilbertEquiv (dir i)))
      (vs.map spacetimeHilbertEquiv)
      (f ∘ spacetimeHilbertEquiv.symm) (g ∘ spacetimeHilbertEquiv.symm) := by
  let E := spacetimeHilbertEquiv
  have hmp : MeasurePreserving (fun x : ST => E.symm x) volume volume := by
    change MeasurePreserving (fun x : ST => WithLp.ofLp x) volume volume
    exact measurePreserving_ofLp
  have hemb : MeasurableEmbedding (fun x : ST => E.symm x) :=
    E.symm.toHomeomorph.measurableEmbedding
  have hadm : ∀ φ : ST → ℝ,
      (wholeSpaceOf ST volume (fun i => E (dir i))).Adm φ →
        (wholeSpaceOf SpaceTime volume dir).Adm (φ ∘ E) := by
    intro φ hφ
    exact ⟨hφ.1.comp E.contDiff, hφ.2.comp_homeomorph E.toHomeomorph⟩
  have hit : ∀ φ : ST → ℝ,
      (wholeSpaceOf ST volume (fun i => E (dir i))).Adm φ →
        ∀ ws : List SpaceTime,
          iterDirDeriv ws (φ ∘ E) =
            iterDirDeriv (ws.map E) φ ∘ E := by
    intro φ hφ ws
    exact iterDirDeriv_comp_clm E.toContinuousLinearMap hφ.1 ws
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · have h1 := h.int_left _ (hadm φ hφ)
    rw [hit φ hφ] at h1
    have h2 := (hmp.integrable_comp_emb hemb).mpr h1
    have heq : (fun x : ST =>
        (iterDirDeriv (vs.map E) φ ∘ E) (E.symm x) • f (E.symm x)) =
        (fun x : ST => iterDirDeriv (vs.map E) φ x • f (E.symm x)) := by
      funext x
      simp only [Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
    change Integrable (fun x : ST =>
      (iterDirDeriv (vs.map E) φ ∘ E) (E.symm x) • f (E.symm x)) volume at h2
    rw [heq] at h2
    change Integrable (fun x : ST =>
      iterDirDeriv (vs.map E) φ x • f (E.symm x)) volume
    exact h2
  · have h1 := h.int_right _ (hadm φ hφ)
    have h2 := (hmp.integrable_comp_emb hemb).mpr h1
    have heq : (fun x : ST => (φ ∘ E) (E.symm x) • g (E.symm x)) =
        (fun x : ST => φ x • g (E.symm x)) := by
      funext x
      simp only [Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
    change Integrable (fun x : ST => (φ ∘ E) (E.symm x) • g (E.symm x)) volume at h2
    rw [heq] at h2
    change Integrable (fun x : ST => φ x • g (E.symm x)) volume
    exact h2
  · have h1 := h.identity _ (hadm φ hφ)
    rw [hit φ hφ] at h1
    simp only [wholeSpaceOf_μ] at h1
    simp only [wholeSpaceOf_μ, List.length_map]
    have e1 := hmp.integral_comp hemb
      (fun z : SpaceTime => iterDirDeriv (vs.map E) φ (E z) • f z)
    have e2 := hmp.integral_comp hemb
      (fun z : SpaceTime => φ (E z) • g z)
    have e1' : ∫ x : ST, iterDirDeriv (vs.map E) φ x • f (E.symm x) =
        ∫ z : SpaceTime, iterDirDeriv (vs.map E) φ (E z) • f z := by
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using e1
    have e2' : ∫ x : ST, φ x • g (E.symm x) =
        ∫ z : SpaceTime, φ (E z) • g z := by
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using e2
    change (∫ x : ST, iterDirDeriv (vs.map E) φ x • f (E.symm x)) =
      (-1 : ℝ) ^ vs.length • (∫ x : ST, φ x • g (E.symm x))
    calc
      _ = ∫ z : SpaceTime, iterDirDeriv (vs.map E) φ (E z) • f z := e1'
      _ = (-1 : ℝ) ^ vs.length • ∫ z : SpaceTime, φ (E z) • g z := h1
      _ = _ := by rw [e2'.symm]

/-- Smooth phase cutoffs which vanish at the two seams of `(0,P)`. -/
def phaseInteriorCutoff (P : ℝ) (n : ℕ) (τ : ℝ) : ℝ :=
  Real.smoothTransition (((n : ℝ) + 1) * τ - 1) *
    Real.smoothTransition (((n : ℝ) + 1) * (P - τ) - 1)

theorem contDiff_phaseInteriorCutoff (P : ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (phaseInteriorCutoff P n) := by
  unfold phaseInteriorCutoff
  have hleft : ContDiff ℝ (⊤ : ℕ∞) (fun τ : ℝ => ((n : ℝ) + 1) * τ - 1) := by fun_prop
  have hright : ContDiff ℝ (⊤ : ℕ∞) (fun τ : ℝ => ((n : ℝ) + 1) * (P - τ) - 1) := by fun_prop
  exact ((Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).comp hleft).mul
    ((Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).comp hright)

/-- Pulling an `L^p` spacetime function to the volume-preserving Hilbert carrier preserves `L^p`. -/
theorem memLp_spacetimeHilbertPullback {p : ℝ≥0∞} {f : SpaceTime → ℂ}
    (hf : MemLp f p volume) :
    MemLp (f ∘ spacetimeHilbertEquiv.symm) p volume :=
  hf.comp_measurePreserving measurePreserving_ofLp

/-- Shrinking Euclidean bumps on the four-dimensional Hilbert spacetime. -/
def spacetimeShrinkBump (j : ℕ) : ContDiffBump (0 : ST) :=
  ⟨((j : ℝ) + 2)⁻¹, ((j : ℝ) + 1)⁻¹, by positivity,
    (inv_lt_inv₀ (by positivity) (by positivity)).mpr (by linarith)⟩

theorem tendsto_spacetimeShrinkBump_rOut :
    Tendsto (fun j : ℕ => (spacetimeShrinkBump j).rOut) atTop (𝓝 0) := by
  simpa [spacetimeShrinkBump, one_div] using
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)

/-- The actual mollifications converge in any finite `L^p` space on Hilbert spacetime. -/
theorem tendsto_spacetimeMollification {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : ST → F} (hf : MemLp f p volume) :
    Tendsto (fun j : ℕ => eLpNorm (moll (spacetimeShrinkBump j) volume f - f) p volume)
      atTop (𝓝 0) := by
  have h := tendsto_eLpNorm_moll_sub (E := ST) (μ := volume) hp hf
    tendsto_spacetimeShrinkBump_rOut
  simpa only [eLpNorm_sub_comm] using h

/-- A compactly supported input remains compactly supported after spacetime mollification. -/
theorem hasCompactSupport_spacetimeMollification {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : ST → F} (hf : HasCompactSupport f) (j : ℕ) :
    HasCompactSupport (moll (spacetimeShrinkBump j) volume f) := by
  apply hasCompactSupport_cv
    ((spacetimeShrinkBump j).hasCompactSupport_normed (μ := volume)) hf
  filter_upwards with x hx
  exact image_eq_zero_of_notMem_tsupport hx

/-- Mollifying an `L^p`, `p ≥ 1`, spacetime field gives a smooth field. -/
theorem contDiff_spacetimeMollification {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : ST → F} (hf : MemLp f p volume) (j : ℕ) :
    ContDiff ℝ ∞ (moll (spacetimeShrinkBump j) volume f) := by
  exact contDiff_moll (spacetimeShrinkBump j)
    (hf.locallyIntegrable Fact.out)

/-- Smooth convolution represents each transported weak spatial derivative. -/
theorem iterDD_spacetimeMollification_derivative {n : ℕ} {dir : Fin n → SpaceTime}
    {vs : List SpaceTime} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {f g : SpaceTime → F}
    (h : HasWeakDeriv (wholeSpaceOf SpaceTime volume dir) vs f g)
    (hloc : LocallyIntegrable (f ∘ spacetimeHilbertEquiv.symm) volume)
    (j : ℕ) :
    iterDD (vs.map spacetimeHilbertEquiv)
      (moll (spacetimeShrinkBump j) volume (f ∘ spacetimeHilbertEquiv.symm)) =
    moll (spacetimeShrinkBump j) volume (g ∘ spacetimeHilbertEquiv.symm) := by
  exact iterDD_cv_of_hasWeakDeriv
    (hasWeakDeriv_spacetimeHilbertEquiv h)
    ((spacetimeShrinkBump j).contDiff_normed (μ := volume))
    ((spacetimeShrinkBump j).hasCompactSupport_normed (μ := volume)) hloc


theorem hasCompactSupport_phaseInteriorCutoff {P : ℝ} (hP : 0 < P) (n : ℕ) :
    HasCompactSupport (phaseInteriorCutoff P n) := by
  refine HasCompactSupport.intro (K := Icc 0 P) isCompact_Icc fun τ hτ => ?_
  simp only [mem_Icc, not_and_or, not_le] at hτ
  rcases hτ with hleft | hright
  · unfold phaseInteriorCutoff
    have hN : 0 < (n : ℝ) + 1 := by positivity
    have hprod : ((n : ℝ) + 1) * τ ≤ 0 := by
      have h := mul_le_mul_of_nonneg_left hleft.le hN.le
      simpa only [mul_zero] using h
    have hz : Real.smoothTransition (((n : ℝ) + 1) * τ - 1) = 0 :=
      Real.smoothTransition.zero_of_nonpos (by linarith)
    rw [hz]
    simp
  · unfold phaseInteriorCutoff
    have hz : Real.smoothTransition (((n : ℝ) + 1) * (P - τ) - 1) = 0 := by
      apply Real.smoothTransition.zero_of_nonpos
      have hN : 0 < (n : ℝ) + 1 := by positivity
      have hneg : P - τ < 0 := by linarith
      have hprod := mul_neg_of_pos_of_neg hN hneg
      linarith
    rw [hz]
    simp

theorem phaseInteriorCutoff_nonneg {P : ℝ} (n : ℕ) (τ : ℝ) :
    0 ≤ phaseInteriorCutoff P n τ := by
  unfold phaseInteriorCutoff
  exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem phaseInteriorCutoff_le_one {P : ℝ} (n : ℕ) (τ : ℝ) :
    phaseInteriorCutoff P n τ ≤ 1 := by
  unfold phaseInteriorCutoff
  have hleft := Real.smoothTransition.nonneg (((n : ℝ) + 1) * τ - 1)
  have hleft' := Real.smoothTransition.le_one (((n : ℝ) + 1) * τ - 1)
  have hright := Real.smoothTransition.nonneg (((n : ℝ) + 1) * (P - τ) - 1)
  have hright' := Real.smoothTransition.le_one (((n : ℝ) + 1) * (P - τ) - 1)
  calc
    _ ≤ Real.smoothTransition (((n : ℝ) + 1) * τ - 1) * 1 :=
      mul_le_mul_of_nonneg_left hright' hleft
    _ ≤ 1 := by simpa using hleft'

theorem phaseInteriorCutoff_eq_zero_left {P : ℝ} (n : ℕ) {τ : ℝ}
    (hτ : τ ≤ 1 / ((n : ℝ) + 1)) : phaseInteriorCutoff P n τ = 0 := by
  unfold phaseInteriorCutoff
  have hN : 0 < (n : ℝ) + 1 := by positivity
  have hmul : τ * ((n : ℝ) + 1) ≤ 1 := (le_div_iff₀ hN).1 hτ
  have hz : Real.smoothTransition (((n : ℝ) + 1) * τ - 1) = 0 := by
    apply Real.smoothTransition.zero_of_nonpos
    nlinarith [hmul]
  rw [hz]
  simp

theorem phaseInteriorCutoff_eq_zero_right {P : ℝ} (n : ℕ) {τ : ℝ}
    (hτ : P - 1 / ((n : ℝ) + 1) ≤ τ) : phaseInteriorCutoff P n τ = 0 := by
  unfold phaseInteriorCutoff
  have hN : 0 < (n : ℝ) + 1 := by positivity
  have hsmall : P - τ ≤ 1 / ((n : ℝ) + 1) := by linarith
  have hmul : (P - τ) * ((n : ℝ) + 1) ≤ 1 := (le_div_iff₀ hN).1 hsmall
  have hz : Real.smoothTransition (((n : ℝ) + 1) * (P - τ) - 1) = 0 := by
    apply Real.smoothTransition.zero_of_nonpos
    nlinarith [hmul]
  rw [hz]
  simp

theorem eventually_phaseInteriorCutoff_eq_one {P : ℝ} (hP : 0 < P) {τ : ℝ}
    (hτ0 : 0 < τ) (hτP : τ < P) :
    ∀ᶠ n : ℕ in atTop, phaseInteriorCutoff P n τ = 1 := by
  have hmin : 0 < min τ (P - τ) := lt_min hτ0 (by linarith)
  have ht : Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
  have hev : ∀ᶠ n : ℕ in atTop, 2 / ((n : ℝ) + 1) < min τ (P - τ) :=
    ht.eventually (Iio_mem_nhds hmin)
  filter_upwards [hev] with n hn
  have hN : 0 < (n : ℝ) + 1 := by positivity
  have hτn : 2 / ((n : ℝ) + 1) < τ := hn.trans_le (min_le_left _ _)
  have hτp : 2 / ((n : ℝ) + 1) < P - τ := hn.trans_le (min_le_right _ _)
  have hm1 : ((n : ℝ) + 1) * τ > 2 := by
    have h := (div_lt_iff₀ hN).1 hτn
    nlinarith
  have hm2 : ((n : ℝ) + 1) * (P - τ) > 2 := by
    have h := (div_lt_iff₀ hN).1 hτp
    nlinarith
  have hleft : Real.smoothTransition (((n : ℝ) + 1) * τ - 1) = 1 :=
    Real.smoothTransition.one_of_one_le (by linarith)
  have hright : Real.smoothTransition (((n : ℝ) + 1) * (P - τ) - 1) = 1 :=
    Real.smoothTransition.one_of_one_le (by linarith)
  unfold phaseInteriorCutoff
  rw [hleft, hright]
  norm_num

theorem hasCompactSupport_phaseInteriorCutoff_inner {P : ℝ} (hP : 0 < P)
    {n : ℕ} (hn : 2 / ((n : ℝ) + 1) ≤ P) :
    HasCompactSupport (phaseInteriorCutoff P n) := by
  let δ : ℝ := 1 / ((n : ℝ) + 1)
  have hδ : δ ≤ P - δ := by
    dsimp [δ]
    have hN : 0 < (n : ℝ) + 1 := by positivity
    have hmul := (div_le_iff₀ hN).1 hn
    have hn' : 2 / ((n : ℝ) + 1) ≤ P := (div_le_iff₀ hN).2 hmul
    have hsum : 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) =
        2 / ((n : ℝ) + 1) := by ring
    rw [← hsum] at hn'
    linarith
  refine HasCompactSupport.intro (K := Icc δ (P - δ))
    isCompact_Icc fun τ hτ => ?_
  simp only [mem_Icc, not_and_or, not_le] at hτ
  rcases hτ with hleft | hright
  · exact phaseInteriorCutoff_eq_zero_left (P := P) n (by simpa [δ] using hleft.le)
  · exact phaseInteriorCutoff_eq_zero_right (P := P) n (by simpa [δ] using hright.le)

/-- The open phase cell, with all spatial points included. -/
def phaseCell (P : ℝ) : Set SpaceTime := Set.Ioc 0 P ×ˢ Set.univ

/-- Removing the phase seams converges in finite `L^p` on all spacetime after zero extension. -/
theorem tendsto_phaseInteriorCutoff_on_cell {P : ℝ} (hP : 0 < P)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) {f : SpaceTime → ℂ}
    (hf : MemLp f p (volume.restrict (phaseCell P))) :
    Tendsto (fun n : ℕ => eLpNorm
      ((fun z : SpaceTime => phaseInteriorCutoff P n z.1 • f z) -
        (phaseCell P).indicator f) p volume) atTop (𝓝 0) := by
  have hcell : MeasurableSet (phaseCell P) :=
    measurableSet_Ioc.prod MeasurableSet.univ
  have hfc : MemLp ((phaseCell P).indicator f) p volume := by
    rw [memLp_indicator_iff_restrict hcell]
    exact hf
  have hτ : ∀ᵐ τ : ℝ ∂(volume : Measure ℝ), τ ≠ P := by
    simpa [ae_iff, measure_singleton]
  have hτz : ∀ᵐ z : SpaceTime ∂(volume : Measure SpaceTime), z.1 ≠ P := by
    have h : ∀ᵐ z : ℝ × Space ∂((volume : Measure ℝ).prod (volume : Measure Space)),
        z.1 ≠ P := Measure.quasiMeasurePreserving_fst.ae hτ
    simpa [Measure.volume_eq_prod] using h
  let g : ℕ → SpaceTime → ℂ := fun n =>
    (phaseCell P).indicator (fun z => Complex.ofReal (phaseInteriorCutoff P n z.1 - 1))
  have hg : ∀ n, AEStronglyMeasurable (g n) volume := by
    intro n
    have hcont : Continuous (fun z : SpaceTime =>
        Complex.ofReal (phaseInteriorCutoff P n z.1 - 1)) :=
      Complex.continuous_ofReal.comp
        (((contDiff_phaseInteriorCutoff P n).continuous.comp continuous_fst).sub continuous_const)
    exact hcont.aestronglyMeasurable.indicator hcell
  have hB : ∀ n, ∀ᵐ z ∂volume, ‖g n z‖ ≤ 1 := by
    intro n
    filter_upwards with z
    by_cases hz : z ∈ phaseCell P
    · have h0 := phaseInteriorCutoff_nonneg (P := P) n z.1
      have h1 := phaseInteriorCutoff_le_one (P := P) n z.1
      change ‖(phaseCell P).indicator
        (fun z => Complex.ofReal (phaseInteriorCutoff P n z.1 - 1)) z‖ ≤ 1
      rw [Set.indicator_of_mem hz]
      change ‖Complex.ofReal (phaseInteriorCutoff P n z.1 - 1)‖ ≤ 1
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (show phaseInteriorCutoff P n z.1 - 1 ≤ 0 by linarith)]
      linarith
    · simp [g, hz]
  have hlim : ∀ᵐ z ∂volume, Tendsto (fun n => g n z) atTop (𝓝 0) := by
    filter_upwards [hτz] with z hτP
    by_cases hz : z ∈ phaseCell P
    · have hτlt : z.1 < P := lt_of_le_of_ne hz.1.2 hτP
      have hev := eventually_phaseInteriorCutoff_eq_one hP hz.1.1 hτlt
      have hzero : ∀ᶠ n : ℕ in atTop, g n z = 0 :=
        hev.mono fun n hn => by simp [g, hz, hn]
      exact tendsto_const_nhds.congr' (hzero.mono fun n hn => hn.symm)
    · simp [g, hz]
  have hconv := UnforcedLeray.Infra.Mult.tendsto_eLpNorm_smul_of_dominated
    (μ := volume) (p := p) hp (Filter.Eventually.of_forall hg)
    (Filter.Eventually.of_forall hB) hlim hfc
  have heq : ∀ n, (fun z : SpaceTime =>
      phaseInteriorCutoff P n z.1 • f z - (phaseCell P).indicator f z) =
      (fun z => g n z • (phaseCell P).indicator f z) := by
    intro n
    funext z
    by_cases hz : z ∈ phaseCell P
    · simp only [Set.indicator_of_mem hz, g]
      rw [Complex.real_smul]
      push_cast
      ring
    · have hχ : phaseInteriorCutoff P n z.1 = 0 := by
        by_cases ht : 0 < z.1
        · have htp : P ≤ z.1 := by
            by_contra hnot
            exact hz ⟨⟨ht, (lt_of_not_ge hnot).le⟩, Set.mem_univ _⟩
          exact phaseInteriorCutoff_eq_zero_right (P := P) n (by
            have hN : 0 < (n : ℝ) + 1 := by positivity
            have hδ : 0 < 1 / ((n : ℝ) + 1) := one_div_pos.mpr hN
            linarith)
        · exact phaseInteriorCutoff_eq_zero_left (P := P) n (by
            have hN : 0 < (n : ℝ) + 1 := by positivity
            have hδ : 0 < 1 / ((n : ℝ) + 1) := one_div_pos.mpr hN
            linarith)
      simp [g, hz, hχ]
  refine Tendsto.congr (fun n => ?_) hconv
  change eLpNorm (fun z => g n z • (phaseCell P).indicator f z) p volume =
    eLpNorm (fun z => phaseInteriorCutoff P n z.1 • f z -
      (phaseCell P).indicator f z) p volume
  exact (congrArg (fun F : SpaceTime → ℂ => eLpNorm F p volume) (heq n)).symm

/-- Multiplying by one interior phase cutoff lifts cell `L^p` integrability to spacetime. -/
theorem memLp_phaseInteriorCutoff_of_cell_memLp {P : ℝ}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {f : SpaceTime → ℂ}
    (hf : MemLp f p (volume.restrict (phaseCell P))) (n : ℕ) :
    MemLp (fun z : SpaceTime => phaseInteriorCutoff P n z.1 • f z) p volume := by
  have hcell : MeasurableSet (phaseCell P) := measurableSet_Ioc.prod MeasurableSet.univ
  have hfc : MemLp ((phaseCell P).indicator f) p volume := by
    rw [memLp_indicator_iff_restrict hcell]
    exact hf
  let m : SpaceTime → ℂ := fun z => Complex.ofReal (phaseInteriorCutoff P n z.1)
  have hm : AEStronglyMeasurable m volume := by
    exact (Complex.continuous_ofReal.comp
      ((contDiff_phaseInteriorCutoff P n).continuous.comp continuous_fst)).aestronglyMeasurable
  have hbound : ∀ᵐ z ∂volume, ‖m z‖ ≤ 1 := by
    filter_upwards with z
    change ‖Complex.ofReal (phaseInteriorCutoff P n z.1)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (phaseInteriorCutoff_nonneg (P := P) n z.1)]
    exact phaseInteriorCutoff_le_one (P := P) n z.1
  have hmul := UnforcedLeray.Infra.Mult.memLp_smul_of_bdd hm hbound hfc
  have heq : (fun z : SpaceTime => m z • (phaseCell P).indicator f z) =
      (fun z => phaseInteriorCutoff P n z.1 • f z) := by
    funext z
    by_cases hz : z ∈ phaseCell P
    · simp [m, hz]
    · have hχ : phaseInteriorCutoff P n z.1 = 0 := by
        by_cases ht : 0 < z.1
        · have htp : P ≤ z.1 := by
            by_contra hnot
            exact hz ⟨⟨ht, (lt_of_not_ge hnot).le⟩, Set.mem_univ _⟩
          exact phaseInteriorCutoff_eq_zero_right (P := P) n (by
            have hN : 0 < (n : ℝ) + 1 := by positivity
            have hδ : 0 < 1 / ((n : ℝ) + 1) := one_div_pos.mpr hN
            linarith)
        · exact phaseInteriorCutoff_eq_zero_left (P := P) n (by
            have hN : 0 < (n : ℝ) + 1 := by positivity
            have hδ : 0 < 1 / ((n : ℝ) + 1) := one_div_pos.mpr hN
            linarith)
      simp [hz, hχ, m]
  rw [← heq]
  exact hmul

/-- Smooth compact scalar functions periodize to genuine scalar phase tests. -/
theorem isPhaseTest_perT_of_compactSupport {P : ℝ} (hP : 0 < P)
    {f : SpaceTime → ℂ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    IsPhaseTest P (perT P f) := by
  obtain ⟨R, _hR, hT, hspace⟩ := exists_window_of_hasCompactSupport hfc
  have hzero : IsPhaseTest 0 f := ⟨hf, fun τ y => by simp, ⟨R, hspace⟩⟩
  exact isPhaseTest_perT hP hT hzero

/-- Periodizing a smooth compact Hilbert-spacetime mollification gives a genuine phase test. -/
theorem isPhaseTest_perT_spacetimeMollification {P : ℝ} (hP : 0 < P)
    {f : ST → ℂ} (hf : HasCompactSupport f)
    (hloc : LocallyIntegrable f volume) (j : ℕ) :
    IsPhaseTest P (perT P ((moll (spacetimeShrinkBump j) volume f) ∘
      spacetimeHilbertEquiv)) := by
  apply isPhaseTest_perT_of_compactSupport hP
  · exact (contDiff_moll (spacetimeShrinkBump j) hloc).comp
      spacetimeHilbertEquiv.contDiff
  · exact (hasCompactSupport_spacetimeMollification hf j).comp_homeomorph
      spacetimeHilbertEquiv.toHomeomorph

/-- The phase-cutoff product's weak derivative transferred to the Euclidean Hilbert carrier. -/
theorem hasWeakSpatialDerivative_cutoff_scalarTestBackground_hilbert {P : ℝ}
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {U : ℝ → SpatialField} (hU : IsBoundedBackground U)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (j : Fin 3) :
    HasWeakDeriv
      (wholeSpaceOf ST volume (fun i => spacetimeHilbertEquiv (scalarTestSpaceTimeDir i)))
      [spacetimeHilbertEquiv (scalarTestSpaceTimeDir j)]
      ((fun z => phaseCutoffSpaceTime χ z • scalarTestBackground Φ U z) ∘
        spacetimeHilbertEquiv.symm)
      ((fun z => phaseCutoffSpaceTime χ z •
        fderiv ℝ (fun x : Space => scalarTestBackground Φ U (z.1, x)) z.2
          (EuclideanSpace.single j (1 : ℝ))) ∘ spacetimeHilbertEquiv.symm) := by
  exact hasWeakDeriv_spacetimeHilbertEquiv
    (hasWeakSpatialDerivative_cutoff_scalarTestBackground hΦ hU hχ j)

theorem iterDD_cutoff_scalarTestBackground_mollification {P : ℝ}
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {U : ℝ → SpatialField} (hU : IsBoundedBackground U)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (j : Fin 3)
    (hloc : LocallyIntegrable
      ((fun z => phaseCutoffSpaceTime χ z • scalarTestBackground Φ U z) ∘
        spacetimeHilbertEquiv.symm) volume) (n : ℕ) :
    iterDD [spacetimeHilbertEquiv (scalarTestSpaceTimeDir j)]
      (moll (spacetimeShrinkBump n) volume
        ((fun z => phaseCutoffSpaceTime χ z • scalarTestBackground Φ U z) ∘
          spacetimeHilbertEquiv.symm)) =
    moll (spacetimeShrinkBump n) volume
      ((fun z => phaseCutoffSpaceTime χ z •
        fderiv ℝ (fun x : Space => scalarTestBackground Φ U (z.1, x)) z.2
          (EuclideanSpace.single j (1 : ℝ))) ∘ spacetimeHilbertEquiv.symm) := by
  simpa using iterDD_spacetimeMollification_derivative
    (hasWeakSpatialDerivative_cutoff_scalarTestBackground hΦ hU hχ j) hloc n

/-- Cell `L^p` bounds supply local integrability and the exact actual mollified derivative. -/
theorem iterDD_cutoff_scalarTestBackground_mollification_of_cellLp {P : ℝ}
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {U : ℝ → SpatialField} (hU : IsBoundedBackground U)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (j : Fin 3) (n : ℕ)
    (hf : MemLp (fun z : SpaceTime =>
      phaseCutoffSpaceTime χ z • scalarTestBackground Φ U z) p volume) :
    iterDD [spacetimeHilbertEquiv (scalarTestSpaceTimeDir j)]
      (moll (spacetimeShrinkBump n) volume
        ((fun z => phaseCutoffSpaceTime χ z • scalarTestBackground Φ U z) ∘
          spacetimeHilbertEquiv.symm)) =
    moll (spacetimeShrinkBump n) volume
      ((fun z => phaseCutoffSpaceTime χ z •
        fderiv ℝ (fun x : Space => scalarTestBackground Φ U (z.1, x)) z.2
          (EuclideanSpace.single j (1 : ℝ))) ∘ spacetimeHilbertEquiv.symm) := by
  have hloc : LocallyIntegrable
      ((fun z => phaseCutoffSpaceTime χ z • scalarTestBackground Φ U z) ∘
        spacetimeHilbertEquiv.symm) volume :=
    (memLp_spacetimeHilbertPullback hf).locallyIntegrable Fact.out
  exact iterDD_cutoff_scalarTestBackground_mollification hΦ hU hχ j hloc n


/-- Compact support is preserved when the phase-cutoff field is moved to the Hilbert carrier. -/
theorem hasCompactSupport_hilbert_phaseCutoff_scalarTestBackground {P : ℝ}
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {U : ℝ → SpatialField} {χ : ℝ → ℝ} (hχc : HasCompactSupport χ) :
    HasCompactSupport
      ((fun z => phaseCutoffSpaceTime χ z • scalarTestBackground Φ U z) ∘
        spacetimeHilbertEquiv.symm) :=
  (hasCompactSupport_phaseCutoff_scalarTestBackground hΦ hχc).comp_homeomorph
    spacetimeHilbertEquiv.symm.toHomeomorph


#print axioms hasWeakDeriv_spacetimeHilbertEquiv
#print axioms tendsto_spacetimeMollification
#print axioms iterDD_spacetimeMollification_derivative
#print axioms hasWeakSpatialDerivative_cutoff_scalarTestBackground_hilbert
#print axioms iterDD_cutoff_scalarTestBackground_mollification
#print axioms iterDD_cutoff_scalarTestBackground_mollification_of_cellLp
#print axioms memLp_spacetimeHilbertPullback
#print axioms phaseInteriorCutoff_nonneg
#print axioms phaseInteriorCutoff_le_one
#print axioms hasCompactSupport_phaseInteriorCutoff_inner
#print axioms eventually_phaseInteriorCutoff_eq_one
#print axioms isPhaseTest_perT_of_compactSupport
#print axioms isPhaseTest_perT_spacetimeMollification
#print axioms tendsto_phaseInteriorCutoff_on_cell
#print axioms memLp_phaseInteriorCutoff_of_cell_memLp

end UnforcedLeray.Cons.C03.Concrete
