import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_2_1
import UnforcedLeray.Lib.SobolevB.Bilin
import UnforcedLeray.Lib.SobolevC.CylTransfer

/-!
# `PlaneProductSmul`: local weak product rule on `ℝ²`

Source: `the November 2 reference manuscript`, lines 261-288 (weak Leibniz rule for
the advection term).  Proof: transfer to `Eucl 2` along `toPlane`, multiply by a cutoff equal to
`1` near the support of the test, apply `Sob.HasWeakDeriv.bilin` (`p = q = 2`, `r = 1`) to the
cut-off factors, and transfer back.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)

namespace PlaneProd

/-- Local `L²` on `Eucl 2`: `L²` on every closed ball. -/
def LocL2 {E : Type*} [NormedAddCommGroup E] (u : Sob.Eucl 2 → E) : Prop :=
  ∀ R : ℝ, MemLp u 2 (volume.restrict (closedBall (0 : Sob.Eucl 2) R))

theorem locallyIntegrable_of_locL2 {E : Type*} [NormedAddCommGroup E] {u : Sob.Eucl 2 → E}
    (hu : LocL2 u) : LocallyIntegrable u volume := by
  rw [locallyIntegrable_iff]
  intro k hk
  obtain ⟨S, hS⟩ := hk.isBounded.subset_closedBall (0 : Sob.Eucl 2)
  haveI : IsFiniteMeasure (volume.restrict (closedBall (0 : Sob.Eucl 2) S)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall _ _).measure_lt_top.ne
  have h : IntegrableOn u (closedBall (0 : Sob.Eucl 2) S) volume := (hu S).integrable (by norm_num)
  exact h.mono_set hS

theorem locL2_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Sob.Eucl 2 → ℝ}
    {g : Sob.Eucl 2 → E} (hf : LocL2 f) (hg : LocL2 g) :
    LocallyIntegrable (fun x => f x • g x) volume := by
  rw [locallyIntegrable_iff]
  intro k hk
  obtain ⟨S, hS⟩ := hk.isBounded.subset_closedBall (0 : Sob.Eucl 2)
  haveI : ENNReal.HolderTriple 2 2 1 := inferInstance
  haveI : IsFiniteMeasure (volume.restrict (closedBall (0 : Sob.Eucl 2) S)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall _ _).measure_lt_top.ne
  have h : MemLp (fun x => f x • g x) 1 (volume.restrict (closedBall (0 : Sob.Eucl 2) S)) :=
    (hg S).smul (hf S)
  have h' : IntegrableOn (fun x => f x • g x) (closedBall (0 : Sob.Eucl 2) S) volume :=
    memLp_one_iff_integrable.1 h
  exact h'.mono_set hS

theorem memLp_smul_cs {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a : Sob.Eucl 2 → ℝ}
    (ha : Continuous a) (hac : HasCompactSupport a) {u : Sob.Eucl 2 → E} (hu : LocL2 u) :
    MemLp (fun x => a x • u x) 2 volume := by
  obtain ⟨S, hS⟩ := hac.isCompact.isBounded.subset_closedBall (0 : Sob.Eucl 2)
  have hK : MeasurableSet (closedBall (0 : Sob.Eucl 2) S) := measurableSet_closedBall
  haveI : ENNReal.HolderTriple ⊤ 2 2 := inferInstance
  have h1 : MemLp (fun x => a x • u x) 2 (volume.restrict (closedBall (0 : Sob.Eucl 2) S)) :=
    (hu S).smul (ha.memLp_top_of_hasCompactSupport hac (μ := _))
  have h2 : (fun x => a x • u x) =
      (closedBall (0 : Sob.Eucl 2) S).indicator (fun x => a x • u x) := by
    funext x
    by_cases hx : x ∈ closedBall (0 : Sob.Eucl 2) S
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx]
      have : a x = 0 := by
        by_contra hne
        exact hx (hS (subset_tsupport a hne))
      simp [this]
  rw [h2]
  exact (memLp_indicator_iff_restrict hK).2 h1

/-- Product rule on `Eucl 2`, for locally `L²` factors. -/
theorem product_eucl {v : Sob.Eucl 2} {f f' : Sob.Eucl 2 → ℝ} {g g' : Sob.Eucl 2 → Cyl.Vec2}
    (hf : LocL2 f) (hf' : LocL2 f') (hg : LocL2 g) (hg' : LocL2 g')
    (hwf : Sob.HasWeakDeriv (Sob.wholeSpace 2) [v] f f')
    (hwg : Sob.HasWeakDeriv (Sob.wholeSpace 2) [v] g g') :
    Sob.HasWeakDeriv (Sob.wholeSpace 2) [v] (fun x => f x • g x)
      (fun x => f' x • g x + f x • g' x) := by
  have lf := locallyIntegrable_of_locL2 hf
  have lf' := locallyIntegrable_of_locL2 hf'
  have lg := locallyIntegrable_of_locL2 hg
  have lg' := locallyIntegrable_of_locL2 hg'
  refine Sob.HasWeakDeriv.of_locallyIntegrable (locL2_smul hf hg)
    ((locL2_smul hf' hg).add (locL2_smul hf hg')) fun φ hφs hφc => ?_
  obtain ⟨r, hr⟩ := hφc.isCompact.isBounded.subset_ball (0 : Sob.Eucl 2)
  set R : ℝ := max r 1 with hRdef
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hsub : tsupport φ ⊆ ball (0 : Sob.Eucl 2) R :=
    hr.trans (ball_subset_ball (le_max_left _ _))
  let θ : ContDiffBump (0 : Sob.Eucl 2) := ⟨R, 2 * R, hR, by linarith⟩
  have hθs : ContDiff ℝ ∞ θ := θ.contDiff
  have hθc : HasCompactSupport θ := θ.hasCompactSupport
  have hθ1 : ∀ x ∈ closedBall (0 : Sob.Eucl 2) R, θ x = 1 := fun x hx =>
    θ.one_of_mem_closedBall hx
  have hθd : ∀ x ∈ ball (0 : Sob.Eucl 2) R, fderiv ℝ θ x v = 0 := by
    intro x hx
    have hev : (θ : Sob.Eucl 2 → ℝ) =ᶠ[𝓝 x] fun _ => (1 : ℝ) :=
      Filter.mem_of_superset (isOpen_ball.mem_nhds hx) fun y hy =>
        hθ1 y (ball_subset_closedBall hy)
    rw [hev.fderiv_eq]
    simp
  have hdθ : Continuous fun x => fderiv ℝ θ x v := (Sob.contDiff_dirDeriv hθs v).continuous
  have hdθc : HasCompactSupport fun x => fderiv ℝ θ x v := hθc.fderiv_apply ℝ v
  -- cut-off factors
  have hF := Sob.HasWeakDeriv.smul_left hθs lf lf' hwf
  have hG := Sob.HasWeakDeriv.smul_left hθs lg lg' hwg
  haveI : ENNReal.HolderTriple 2 2 1 := inferInstance
  have m1 : MemLp (fun x => θ x • f x) 2 volume := memLp_smul_cs hθs.continuous hθc hf
  have m2 : MemLp (fun x => fderiv ℝ θ x v • f x + θ x • f' x) 2 volume :=
    (memLp_smul_cs hdθ hdθc hf).add (memLp_smul_cs hθs.continuous hθc hf')
  have m3 : MemLp (fun x => θ x • g x) 2 volume := memLp_smul_cs hθs.continuous hθc hg
  have m4 : MemLp (fun x => fderiv ℝ θ x v • g x + θ x • g' x) 2 volume :=
    (memLp_smul_cs hdθ hdθc hg).add (memLp_smul_cs hθs.continuous hθc hg')
  have hb := Sob.HasWeakDeriv.bilin (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Cyl.Vec2 →L[ℝ] Cyl.Vec2)
    (p := 2) (q := 2) (r := 1) (by norm_num) m1 m2 m3 m4 hF hG
  have hid := hb.identity φ ⟨hφs, hφc⟩
  simp only [Sob.iterDirDeriv_singleton, Sob.wholeSpace_μ, List.length_singleton, pow_one,
    neg_smul, one_smul, ContinuousLinearMap.lsmul_apply] at hid ⊢
  have e1 : (fun x => fderiv ℝ φ x v • (θ x • f x) • (θ x • g x)) =
      fun x => fderiv ℝ φ x v • f x • g x := by
    funext x
    by_cases hx : x ∈ tsupport φ
    · have := hθ1 x (ball_subset_closedBall (hsub hx))
      simp [this]
    · have h0 : fderiv ℝ φ x = 0 := (notMem_tsupport_iff_eventuallyEq.mp hx).fderiv_eq.trans
        (by simp)
      simp [h0]
  have e2 : (fun x => φ x • ((fderiv ℝ θ x v • f x + θ x • f' x) • (θ x • g x) +
        (θ x • f x) • (fderiv ℝ θ x v • g x + θ x • g' x))) =
      fun x => φ x • (f' x • g x + f x • g' x) := by
    funext x
    by_cases hx : x ∈ tsupport φ
    · have h1 := hθ1 x (ball_subset_closedBall (hsub hx))
      have h2 := hθd x (hsub hx)
      simp [h1, h2]
    · have h0 : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [h0]
  rw [e1, e2] at hid
  exact hid

end PlaneProd

open Sob in
/-- Converse of `Sob.hasWeakDeriv_comp_toPlane`. -/
theorem hasWeakDeriv_of_comp_toPlane {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {vs : List (ℝ × ℝ)} {f g : ℝ × ℝ → F}
    (h : HasWeakDeriv (wholeSpace 2) (vs.map toPlane.symm) (f ∘ toPlane) (g ∘ toPlane)) :
    HasWeakDeriv (wholeSpaceOf (ℝ × ℝ) volume cylDir) vs f g := by
  have hmp := measurePreserving_toPlane
  have hemb := measurableEmbedding_toPlane
  have hadm : ∀ φ : ℝ × ℝ → ℝ, (wholeSpaceOf (ℝ × ℝ) volume cylDir).Adm φ →
      (wholeSpace 2).Adm (φ ∘ toPlane) := fun φ hφ =>
    ⟨hφ.1.comp toPlane.contDiff, hφ.2.comp_homeomorph toPlane.toHomeomorph⟩
  have hit : ∀ φ : ℝ × ℝ → ℝ, (wholeSpaceOf (ℝ × ℝ) volume cylDir).Adm φ →
      iterDirDeriv (vs.map toPlane.symm) (φ ∘ toPlane) = iterDirDeriv vs φ ∘ toPlane := by
    intro φ hφ
    have h1 := iterDirDeriv_comp_clm (toPlane : Eucl 2 →L[ℝ] ℝ × ℝ) hφ.1 (vs.map toPlane.symm)
    have h2 : (vs.map toPlane.symm).map (toPlane : Eucl 2 →L[ℝ] ℝ × ℝ) = vs := by
      simp [List.map_map, Function.comp_def]
    rw [h2] at h1
    exact h1
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · have h1 := h.int_left _ (hadm φ hφ)
    rw [hit φ hφ] at h1
    exact (hmp.integrable_comp_emb hemb).mp h1
  · have h1 := h.int_right _ (hadm φ hφ)
    exact (hmp.integrable_comp_emb hemb).mp h1
  · have h1 := h.identity _ (hadm φ hφ)
    rw [hit φ hφ] at h1
    try simp only [wholeSpaceOf_μ]
    simp only [wholeSpace_μ, List.length_map, Function.comp_apply] at h1
    have e1 := hmp.integral_comp hemb (fun z => iterDirDeriv vs φ z • f z)
    have e2 := hmp.integral_comp hemb (fun z => φ z • g z)
    try simp only [Function.comp_apply] at e1 e2
    rw [← e1, ← e2]
    exact h1

theorem planeProductSmul : PlaneProductSmul := by
  intro j f f' g g' hf hf' hg hg' hwf hwg
  have hloc : ∀ {E : Type} [NormedAddCommGroup E] (u : ℝ × ℝ → E),
      (∀ A M : ℝ, MemLp u 2 (volume.restrict (Icc (-A) A ×ˢ Icc (-M) M))) →
      PlaneProd.LocL2 (u ∘ Sob.toPlane) := by
    intro E _ u hu R
    have h1 : MemLp (u ∘ Sob.toPlane) 2 (volume.restrict (Sob.boxE R R)) :=
      (hu R R).comp_measurePreserving
        (Sob.measurePreserving_toPlane.restrict_preimage_emb Sob.measurableEmbedding_toPlane _)
    refine h1.mono_measure (Measure.restrict_mono ?_ le_rfl)
    intro y hy
    rw [Sob.mem_boxE]
    have hn : ‖y‖ ≤ R := by simpa using hy
    exact ⟨(by simpa using (PiLp.norm_apply_le y 0).trans hn), by
      simpa using (PiLp.norm_apply_le y 1).trans hn⟩
  have wf := Sob.hasWeakDeriv_comp_toPlane hwf
  have wg := Sob.hasWeakDeriv_comp_toPlane hwg
  have wf' : Sob.HasWeakDeriv (Sob.wholeSpace 2) [Sob.e j] (f ∘ Sob.toPlane) (f' ∘ Sob.toPlane) := by
    simpa [Sob.toPlane_symm_cylDir] using wf
  have wg' : Sob.HasWeakDeriv (Sob.wholeSpace 2) [Sob.e j] (g ∘ Sob.toPlane) (g' ∘ Sob.toPlane) := by
    simpa [Sob.toPlane_symm_cylDir] using wg
  have key := PlaneProd.product_eucl (hloc f hf) (hloc f' hf') (hloc g hg) (hloc g' hg') wf' wg'
  refine hasWeakDeriv_of_comp_toPlane ?_
  simpa [Sob.toPlane_symm_cylDir, Function.comp_def] using key

end UnforcedLeray.Short.PartI
