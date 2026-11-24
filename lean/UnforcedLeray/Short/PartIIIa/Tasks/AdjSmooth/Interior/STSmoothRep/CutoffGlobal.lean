import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.STSmooth.Defs
import UnforcedLeray.Lib.Sobolev.SmoothCoeff

/-!
# `PartIII-a:T21/2/7/2/1/1/8/1`: cutoffs of `H^∞_loc(U)` are in `H^∞(ℝ × ℝ²)` (`stCutoffGlobal`)

Source: SP 3060-3061 (`the November 2 reference manuscript`).

Route avoiding the coefficient bookkeeping of the word Leibniz rule: the class `InSpan` of finite
sums of terms `ζ • g u` (`ζ ∈ C_c^∞(U)`, `g u` the `L²_loc(U)` derivatives of `F`) is closed under
one weak derivative on the whole space, `∂_j (ζ g) = (∂_j ζ) g + ζ ∂_j g`, for tests `φ` of the whole
space (the product `φ ζ` is a test of `U`).  Induction on the word.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.IIIa

open UnforcedLeray.Sob

/-- Cutoffs: `C^∞`, compact support inside `U`. -/
def IsCut (U : Set STSpace) (ζ : STSpace → ℝ) : Prop :=
  ContDiff ℝ ∞ ζ ∧ HasCompactSupport ζ ∧ tsupport ζ ⊆ U

/-- `L²_loc(U)`. -/
def LocL2 (U : Set STSpace) (h : STSpace → ℂ) : Prop :=
  ∀ K : Set STSpace, IsCompact K → K ⊆ U → MemLp h 2 (volume.restrict K)

theorem IsCut.fderiv {U : Set STSpace} {ζ : STSpace → ℝ} (h : IsCut U ζ) (v : STSpace) :
    IsCut U (fun x => fderiv ℝ ζ x v) :=
  ⟨contDiff_dirDeriv h.1 v, h.2.1.fderiv_apply ℝ v,
    (tsupport_fderiv_apply_subset ℝ v).trans h.2.2⟩

theorem memLp_cut {U : Set STSpace} {ζ : STSpace → ℝ} {h : STSpace → ℂ} (hh : LocL2 U h)
    (hζ : IsCut U ζ) : MemLp (fun p => ζ p • h p) 2 volume := by
  have hK : IsCompact (tsupport ζ) := hζ.2.1
  have e : (fun p => ζ p • h p) = (tsupport ζ).indicator (fun p => ζ p • h p) := by
    funext p
    by_cases hp : p ∈ tsupport ζ
    · simp [hp]
    · simp [hp, image_eq_zero_of_notMem_tsupport hp]
  rw [e, memLp_indicator_iff_restrict (isClosed_tsupport _).measurableSet]
  have hm := hh _ hK hζ.2.2
  obtain ⟨C, hC⟩ := hζ.1.continuous.bounded_above_of_compact_support hζ.2.1
  refine MemLp.of_le_mul (c := C) hm
    (hζ.1.continuous.aestronglyMeasurable.smul hm.1) (Eventually.of_forall fun p => ?_)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (hC p) (norm_nonneg _)

theorem integrable_cut {U : Set STSpace} {ψ : STSpace → ℝ} {h : STSpace → ℂ} (hh : LocL2 U h)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U) :
    Integrable (fun p => ψ p • h p) volume := by
  have e : (fun p => ψ p • h p) = (tsupport ψ).indicator (fun p => ψ p • h p) := by
    funext p
    by_cases hp : p ∈ tsupport ψ
    · simp [hp]
    · simp [hp, image_eq_zero_of_notMem_tsupport hp]
  rw [e, integrable_indicator_iff (isClosed_tsupport _).measurableSet]
  have hm := hh _ hc hs
  haveI : IsFiniteMeasure (volume.restrict (tsupport ψ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hc.measure_lt_top⟩
  have hi : IntegrableOn h (tsupport ψ) volume := hm.integrable one_le_two
  exact hi.continuousOn_smul hψ.continuousOn hc

/-- Finite sums of cutoff terms `ζ • g u`. -/
inductive InSpan (U : Set STSpace) (g : List (Fin 3) → STSpace → ℂ) : (STSpace → ℂ) → Prop
  | single {ζ : STSpace → ℝ} (hζ : IsCut U ζ) (u : List (Fin 3)) :
      InSpan U g (fun p => ζ p • g u p)
  | add {f f' : STSpace → ℂ} : InSpan U g f → InSpan U g f' → InSpan U g (f + f')
  | zero : InSpan U g 0

theorem InSpan.memLp {U : Set STSpace} {g : List (Fin 3) → STSpace → ℂ}
    (hg : ∀ u, LocL2 U (g u)) {f : STSpace → ℂ} (hf : InSpan U g f) : MemLp f 2 volume := by
  induction hf with
  | single hζ u => exact memLp_cut (hg u) hζ
  | add _ _ h1 h2 => exact h1.add h2
  | zero => exact MemLp.zero

/-- The first-order cutoff step: `∂_v (ζ g) = (∂_v ζ) g + ζ g'` on the whole space. -/
theorem cutoff_step {U : Set STSpace} (hU : IsOpen U) {g g' : STSpace → ℂ} {j : Fin 3}
    (hg : LocL2 U g) (hg' : LocL2 U g')
    (h : HasWeakDeriv (stDomain U hU) [stDir j] g g') {ζ : STSpace → ℝ} (hζ : IsCut U ζ) :
    HasWeakDeriv (wholeSpaceOf STSpace volume stDir) [stDir j] (fun p => ζ p • g p)
      (fun p => fderiv ℝ ζ p (stDir j) • g p + ζ p • g' p) := by
  set v := stDir j with hv
  have hdζ : IsCut U (fun x => fderiv ℝ ζ x v) := hζ.fderiv v
  -- integrability of the pieces
  have iA : ∀ ψ : STSpace → ℝ, Continuous ψ → tsupport ψ ⊆ tsupport ζ →
      Integrable (fun p => ψ p • g p) volume := fun ψ hc hs =>
    integrable_cut hg hc (hζ.2.1.of_isClosed_subset (isClosed_tsupport _) hs) (hs.trans hζ.2.2)
  have iB : ∀ ψ : STSpace → ℝ, Continuous ψ → tsupport ψ ⊆ tsupport ζ →
      Integrable (fun p => ψ p • g' p) volume := fun ψ hc hs =>
    integrable_cut hg' hc (hζ.2.1.of_isClosed_subset (isClosed_tsupport _) hs) (hs.trans hζ.2.2)
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · have := iA (fun x => fderiv ℝ φ x v * ζ x)
      (((hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const).mul hζ.1.continuous)
      ((tsupport_mul_subset_right))
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp [mul_assoc]
  · have h1 := iA (fun x => φ x * fderiv ℝ ζ x v) (hφ.1.continuous.mul hdζ.1.continuous)
      (tsupport_mul_subset_right.trans (tsupport_fderiv_apply_subset ℝ v))
    have h2 := iB (fun x => φ x * ζ x) (hφ.1.continuous.mul hζ.1.continuous)
      tsupport_mul_subset_right
    refine (h1.add h2).congr (Eventually.of_forall fun x => ?_)
    simp [mul_assoc]
  · -- the identity
    have hψ : (stDomain U hU).Adm (fun x => φ x * ζ x) :=
      ⟨hφ.1.mul hζ.1, hζ.2.1.mul_left, tsupport_mul_subset_right.trans hζ.2.2⟩
    have hid := h.identity _ hψ
    have hd : ∀ x, fderiv ℝ (fun y => φ y * ζ y) x v =
        fderiv ℝ φ x v * ζ x + φ x * fderiv ℝ ζ x v := by
      intro x
      have h1 : DifferentiableAt ℝ φ x := (hφ.1.differentiable (by simp)) x
      have h2 : DifferentiableAt ℝ ζ x := (hζ.1.differentiable (by simp)) x
      have : fderiv ℝ (fun y => φ y * ζ y) x = φ x • fderiv ℝ ζ x + ζ x • fderiv ℝ φ x :=
        fderiv_mul h1 h2
      rw [this]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    have hsub : tsupport ζ ⊆ U := hζ.2.2
    -- pass from `μ.restrict U` to `μ`
    have r1 : ∫ x, iterDirDeriv [v] (fun y => φ y * ζ y) x • g x =
        -∫ x, (φ x * ζ x) • g' x := by
      have h1 := hid
      simp only [List.length_singleton, pow_one, neg_smul, one_smul] at h1
      have a1 : ∫ x, iterDirDeriv [v] (fun y => φ y * ζ y) x • g x ∂(stDomain U hU).μ =
          ∫ x, iterDirDeriv [v] (fun y => φ y * ζ y) x • g x := by
        show ∫ x, _ ∂(volume.restrict U) = _
        refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
        have hx' : x ∉ tsupport ζ := fun hh => hx (hsub hh)
        have : x ∉ tsupport (fun y => fderiv ℝ (fun y => φ y * ζ y) y v) :=
          fun hh => hx' ((tsupport_fderiv_apply_subset ℝ v).trans tsupport_mul_subset_right hh)
        simp [iterDirDeriv_singleton, image_eq_zero_of_notMem_tsupport this]
      have a2 : ∫ x, (φ x * ζ x) • g' x ∂(stDomain U hU).μ = ∫ x, (φ x * ζ x) • g' x := by
        show ∫ x, _ ∂(volume.restrict U) = _
        refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
        have hx' : x ∉ tsupport ζ := fun hh => hx (hsub hh)
        have : x ∉ tsupport (fun y => φ y * ζ y) := fun hh => hx' (tsupport_mul_subset_right hh)
        simp [image_eq_zero_of_notMem_tsupport this]
      rw [a1, a2] at h1; exact h1
    simp only [iterDirDeriv_singleton, List.length_singleton, pow_one, neg_smul, one_smul,
      wholeSpaceOf_μ]
    simp only [iterDirDeriv_singleton] at r1
    have i1 : Integrable (fun x => fderiv ℝ (fun y => φ y * ζ y) x v • g x) volume :=
      iA (fun x => fderiv ℝ (fun y => φ y * ζ y) x v)
        (((hψ.1.continuous_fderiv (by simp)).clm_apply continuous_const))
        ((tsupport_fderiv_apply_subset ℝ v).trans tsupport_mul_subset_right)
    have i2 : Integrable (fun x => (φ x * fderiv ℝ ζ x v) • g x) volume :=
      iA _ (hφ.1.continuous.mul hdζ.1.continuous)
        (tsupport_mul_subset_right.trans (tsupport_fderiv_apply_subset ℝ v))
    have i4 : Integrable (fun x => (φ x * ζ x) • g' x) volume :=
      iB _ (hφ.1.continuous.mul hζ.1.continuous) tsupport_mul_subset_right
    calc ∫ x, fderiv ℝ φ x v • (ζ x • g x)
        = ∫ x, (fderiv ℝ (fun y => φ y * ζ y) x v • g x - (φ x * fderiv ℝ ζ x v) • g x) := by
          congr 1 with x
          rw [hd, smul_smul, add_smul, add_sub_cancel_right]
      _ = -(∫ x, (φ x * ζ x) • g' x) - ∫ x, (φ x * fderiv ℝ ζ x v) • g x := by
          rw [integral_sub i1 i2, r1]
      _ = -∫ x, φ x • (fderiv ℝ ζ x v • g x + ζ x • g' x) := by
          have e3 : ∫ x, φ x • (fderiv ℝ ζ x v • g x + ζ x • g' x) =
              (∫ x, (φ x * fderiv ℝ ζ x v) • g x) + ∫ x, (φ x * ζ x) • g' x := by
            rw [← integral_add i2 i4]
            congr 1 with x
            rw [smul_add, smul_smul, smul_smul]
          rw [e3]
          abel

/-- **`stCutoffGlobal`**: cutoffs of `H^∞_loc(U)` are in `H^∞(ℝ × ℝ²)`. -/
theorem stCutoffGlobal : STCutoffGlobal := by
  intro U hU F hF ζ hζ hc hs
  have hcut : IsCut U ζ := ⟨hζ, hc, hs⟩
  choose g hgloc hgw using hF.2
  classical
  let g' : List (Fin 3) → STSpace → ℂ := fun u => if u = [] then F else g u
  have hg'loc : ∀ u, LocL2 U (g' u) := by
    intro u
    by_cases hu : u = []
    · simp only [g', hu, if_true]; exact hF.1
    · simp only [g', hu, if_false]; exact hgloc u
  have hg'w : ∀ u, HasWeakDeriv (stDomain U hU) (u.map stDir) F (g' u) := by
    intro u
    by_cases hu : u = []
    · subst hu
      simp only [g', if_true, List.map_nil]
      refine HasWeakDeriv.nil fun φ hφ => ?_
      exact (integrable_cut hF.1 hφ.1.continuous hφ.2.1 hφ.2.2).integrableOn
    · simp only [g', hu, if_false]; exact hgw u
  have hstep : ∀ f, InSpan U g' f → ∀ j : Fin 3, ∃ f', InSpan U g' f' ∧
      HasWeakDeriv (wholeSpaceOf STSpace volume stDir) [stDir j] f f' := by
    intro f hf j
    induction hf with
    | @single ζ' hζ' u =>
      refine ⟨_, (InSpan.single (hζ'.fderiv (stDir j)) u).add (InSpan.single hζ' (u ++ [j])),
        ?_⟩
      have h1 := hg'w u
      have h2 : HasWeakDeriv (stDomain U hU) (u.map stDir ++ [stDir j]) F (g' (u ++ [j])) := by
        simpa using hg'w (u ++ [j])
      exact cutoff_step hU (hg'loc u) (hg'loc _) (h1.of_append h2) hζ'
    | add _ _ ih1 ih2 =>
      obtain ⟨f1, s1, w1⟩ := ih1
      obtain ⟨f2, s2, w2⟩ := ih2
      exact ⟨f1 + f2, s1.add s2, w1.add w2⟩
    | zero => exact ⟨0, InSpan.zero, HasWeakDeriv.zero⟩
  have hmain : ∀ l : List (Fin 3), ∃ f, InSpan U g' f ∧
      HasWeakDeriv (wholeSpaceOf STSpace volume stDir) (l.map stDir) (fun p => ζ p • F p) f := by
    intro l
    induction l with
    | nil =>
      refine ⟨fun p => ζ p • g' [] p, InSpan.single hcut [], ?_⟩
      have e : (fun p => ζ p • g' [] p) = fun p => ζ p • F p := by
        funext p; simp [g']
      rw [e]
      refine HasWeakDeriv.nil fun φ hφ => ?_
      have := integrable_cut hF.1 (hφ.1.continuous.mul hζ.continuous) (hc.mul_left)
        (tsupport_mul_subset_right.trans hs)
      refine this.congr (Eventually.of_forall fun x => ?_)
      simp [mul_assoc]
    | cons j l ih =>
      obtain ⟨f, sf, wf⟩ := ih
      obtain ⟨f', sf', wf'⟩ := hstep f sf j
      exact ⟨f', sf', by simpa using wf.cons wf'⟩
  refine ⟨memLp_cut hF.1 hcut, fun l => ?_⟩
  obtain ⟨f, sf, wf⟩ := hmain l
  exact ⟨f, sf.memLp hg'loc, wf⟩

end UnforcedLeray.Short.IIIa
