import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org.LinearVersion
import UnforcedLeray.Short.PartIIb.Tasks.HardyL1
import UnforcedLeray.Short.PartIIb.Tasks.GlobalEnergy.Continuation.BodySourceGlue
import UnforcedLeray.Lib.BochnerTime.Slices
import Mathlib.MeasureTheory.Covering.OneDim

/-!
# `DuhamelRegularity.WeakAndSlices`: Local weak calculus, `L¹` forcing bounds, Borel `H¹_σ`
slice upgrades, and right-Lebesgue age differentiation

Helper module for `PartII-b:F8/1/org/3` (`MeridionalDuhamelRegularity`, SP 2301–2305).
All declarations are inside `UnforcedLeray.Short.IIb.F8Duh` (R6).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.F8Duh

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-! ## 1. Interval-restricted weak derivatives and smooth time-cutoff gluing -/

/-- Test function on `(a, b) × ℝ²` (`s > 0`). -/
def IsIooTest (a b : ℝ) (φ : Coord → ℝ) : Prop :=
  IsCoordTest φ ∧ tsupport φ ⊆ Ioo a b ×ˢ univ

/-- Scalar distributional derivative `g = v·∇u + d u` on `(a, b) × ℝ²`. -/
def HasWeakFOOnIoo (a b : ℝ) (v : Coord → Fin 3 → ℝ) (d : Coord → ℝ)
    (u g : Coord → ℂ) : Prop :=
  (∀ φ, IsIooTest a b φ →
    Integrable (fun x => u x * (coordTranspose v d φ x : ℂ)) ∧
      Integrable (fun x => g x * (φ x : ℂ))) ∧
  ∀ φ, IsIooTest a b φ →
    ∫ x, g x * (φ x : ℂ) = ∫ x, u x * (coordTranspose v d φ x : ℂ)

/-- Vector distributional derivative on `(a, b) × ℝ²`. -/
def HasWeakVecOnIoo (a b : ℝ) (v : Coord → Fin 3 → ℝ) (d : Coord → ℝ)
    (u g : CProf) : Prop :=
  ∀ i : Fin 2, HasWeakFOOnIoo a b v d (fun x => u x i) (fun x => g x i)

lemma isIooTest_mono {a b a' b' : ℝ} (ha : a ≤ a') (hb : b' ≤ b) {φ : Coord → ℝ}
    (hφ : IsIooTest a' b' φ) : IsIooTest a b φ :=
  ⟨hφ.1, hφ.2.trans (prod_mono (Ioo_subset_Ioo ha hb) Subset.rfl)⟩

lemma hasWeakFOOnIoo_of_global (a b : ℝ) {v : Coord → Fin 3 → ℝ} {d : Coord → ℝ}
    {u g : Coord → ℂ} (h : HasWeakFO v d u g) : HasWeakFOOnIoo a b v d u g :=
  ⟨fun φ hφ => h.1 φ hφ.1, fun φ hφ => h.2 φ hφ.1⟩

lemma hasWeakVecOnIoo_of_global (a b : ℝ) {v : Coord → Fin 3 → ℝ} {d : Coord → ℝ}
    {u g : CProf} (h : HasWeakVec v d u g) : HasWeakVecOnIoo a b v d u g :=
  fun i => hasWeakFOOnIoo_of_global a b (h i)

lemma hasWeakFOOnIoo_mono {a b a' b' : ℝ} (ha : a ≤ a') (hb : b' ≤ b)
    {v : Coord → Fin 3 → ℝ} {d : Coord → ℝ} {u g : Coord → ℂ}
    (h : HasWeakFOOnIoo a b v d u g) : HasWeakFOOnIoo a' b' v d u g :=
  ⟨fun φ hφ => h.1 φ (isIooTest_mono ha hb hφ), fun φ hφ => h.2 φ (isIooTest_mono ha hb hφ)⟩

lemma hasWeakVecOnIoo_mono {a b a' b' : ℝ} (ha : a ≤ a') (hb : b' ≤ b)
    {v : Coord → Fin 3 → ℝ} {d : Coord → ℝ} {u g : CProf}
    (h : HasWeakVecOnIoo a b v d u g) : HasWeakVecOnIoo a' b' v d u g :=
  fun i => hasWeakFOOnIoo_mono ha hb (h i)

lemma vanish_outside_Ioo {a b : ℝ} {φ : Coord → ℝ} (hφ : IsIooTest a b φ)
    {x : Coord} (hx : x.1 ∉ Ioo a b) : φ =ᶠ[𝓝 x] 0 := by
  have hx' : x ∉ tsupport φ := fun hm => hx (hφ.2 hm).1
  exact notMem_tsupport_iff_eventuallyEq.1 hx'

lemma coordTranspose_eq_zero_outside_Ioo {a b : ℝ} (v : Coord → Fin 3 → ℝ) (d : Coord → ℝ)
    {φ : Coord → ℝ} (hφ : IsIooTest a b φ) {x : Coord} (hx : x.1 ∉ Ioo a b) :
    coordTranspose v d φ x = 0 := by
  have hv := vanish_outside_Ioo hφ hx
  have hj : ∀ j : Fin 3, cpd j (fun y => v y j * φ y) x = 0 := by
    intro j
    have : (fun y => v y j * φ y) =ᶠ[𝓝 x] 0 := hv.mono fun y hy => by simp [hy]
    simp [cpd, this.fderiv_eq]
  simp [coordTranspose, hj, hv.eq_of_nhds]

lemma ae_mul_eq_on_Ioo {a b : ℝ} {u u' h : Coord → ℂ}
    (hu : u =ᵐ[volume.restrict (Ioo a b ×ˢ univ)] u')
    (hh : ∀ x : Coord, x.1 ∉ Ioo a b → h x = 0) :
    (fun x => u x * h x) =ᵐ[volume] (fun x => u' x * h x) := by
  have hM : MeasurableSet (Ioo a b ×ˢ (univ : Set B0579.Plane)) :=
    measurableSet_Ioo.prod MeasurableSet.univ
  rw [Filter.EventuallyEq, ae_restrict_iff' hM] at hu
  filter_upwards [hu] with x hx
  by_cases hm : x.1 ∈ Ioo a b
  · rw [hx ⟨hm, trivial⟩]
  · simp [hh x hm]

lemma hasWeakFOOnIoo_congr {a b : ℝ} (v : Coord → Fin 3 → ℝ) (d : Coord → ℝ)
    {u u' g g' : Coord → ℂ}
    (hu : u =ᵐ[volume.restrict (Ioo a b ×ˢ univ)] u')
    (hg : g =ᵐ[volume.restrict (Ioo a b ×ˢ univ)] g')
    (h : HasWeakFOOnIoo a b v d u g) : HasWeakFOOnIoo a b v d u' g' := by
  obtain ⟨hI, hE⟩ := h
  have e1 : ∀ φ, IsIooTest a b φ →
      (fun x => u x * (coordTranspose v d φ x : ℂ)) =ᵐ[volume]
        (fun x => u' x * (coordTranspose v d φ x : ℂ)) :=
    fun φ hφ => ae_mul_eq_on_Ioo hu (fun x hx => by simp [coordTranspose_eq_zero_outside_Ioo v d hφ hx])
  have e2 : ∀ φ, IsIooTest a b φ →
      (fun x => g x * (φ x : ℂ)) =ᵐ[volume] (fun x => g' x * (φ x : ℂ)) :=
    fun φ hφ => ae_mul_eq_on_Ioo hg (fun x hx => by simp [(vanish_outside_Ioo hφ hx).eq_of_nhds])
  refine ⟨fun φ hφ => ⟨(integrable_congr (e1 φ hφ)).1 (hI φ hφ).1,
    (integrable_congr (e2 φ hφ)).1 (hI φ hφ).2⟩, fun φ hφ => ?_⟩
  rw [← integral_congr_ae (e2 φ hφ), hE φ hφ, integral_congr_ae (e1 φ hφ)]

lemma hasWeakVecOnIoo_congr {a b : ℝ} (v : Coord → Fin 3 → ℝ) (d : Coord → ℝ)
    {u u' g g' : CProf}
    (hu : u =ᵐ[volume.restrict (Ioo a b ×ˢ univ)] u')
    (hg : g =ᵐ[volume.restrict (Ioo a b ×ˢ univ)] g')
    (h : HasWeakVecOnIoo a b v d u g) : HasWeakVecOnIoo a b v d u' g' :=
  fun i => hasWeakFOOnIoo_congr v d (hu.mono fun _ hx => congrArg (fun v => v i) hx)
    (hg.mono fun _ hx => congrArg (fun v => v i) hx) (h i)

lemma hasWeakVecOnIoo_sub {a b : ℝ} (v : Coord → Fin 3 → ℝ) (d : Coord → ℝ)
    {u₁ g₁ u₂ g₂ : CProf}
    (h₁ : HasWeakVecOnIoo a b v d u₁ g₁) (h₂ : HasWeakVecOnIoo a b v d u₂ g₂) :
    HasWeakVecOnIoo a b v d (u₁ - u₂) (g₁ - g₂) := by
  intro i
  refine ⟨fun φ hφ => ⟨?_, ?_⟩, fun φ hφ => ?_⟩
  · exact (((h₁ i).1 φ hφ).1.sub (((h₂ i).1 φ hφ).1)).congr
      (Eventually.of_forall fun x => by simp [sub_mul])
  · exact (((h₁ i).1 φ hφ).2.sub (((h₂ i).1 φ hφ).2)).congr
      (Eventually.of_forall fun x => by simp [sub_mul])
  · have eL : (fun x => (g₁ x i - g₂ x i) * (φ x : ℂ)) =
        fun x => g₁ x i * (φ x : ℂ) - g₂ x i * (φ x : ℂ) := by funext x; ring
    have eR : (fun x => (u₁ x i - u₂ x i) * (coordTranspose v d φ x : ℂ)) =
        fun x => u₁ x i * (coordTranspose v d φ x : ℂ) -
          u₂ x i * (coordTranspose v d φ x : ℂ) := by funext x; ring
    change ∫ x, (g₁ x i - g₂ x i) * (φ x : ℂ) =
      ∫ x, (u₁ x i - u₂ x i) * (coordTranspose v d φ x : ℂ)
    rw [eL, eR, integral_sub (((h₁ i).1 φ hφ).2) (((h₂ i).1 φ hφ).2),
      integral_sub (((h₁ i).1 φ hφ).1) (((h₂ i).1 φ hφ).1),
      (h₁ i).2 φ hφ, (h₂ i).2 φ hφ]

/-- Uniqueness of distributional derivatives on `(a, b) × ℝ²` for `0 ≤ a < b`. -/
lemma weak_unique_on_Ioo {a b : ℝ} (ha : 0 ≤ a) (v : Coord → Fin 3 → ℝ) (d : Coord → ℝ)
    {u g₁ g₂ : Coord → ℂ}
    (h₁ : HasWeakFOOnIoo a b v d u g₁) (h₂ : HasWeakFOOnIoo a b v d u g₂) :
    g₁ =ᵐ[volume.restrict (Ioo a b ×ˢ univ)] g₂ := by
  set U : Set Coord := Ioo a b ×ˢ univ
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_univ
  have hU_pos : U ⊆ Ioi (0 : ℝ) ×ˢ univ :=
    prod_mono (fun s hs => lt_of_le_of_lt ha hs.1) Subset.rfl
  have hint : ∀ φ, IsIooTest a b φ → Integrable (fun x => (g₁ x - g₂ x) * (φ x : ℂ)) := by
    intro φ hφ
    exact (((h₁.1 φ hφ).2).sub ((h₂.1 φ hφ).2)).congr
      (Eventually.of_forall fun x => by simp [sub_mul])
  have loc : LocallyIntegrableOn (fun x => g₁ x - g₂ x) U volume := by
    intro x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hx
    let f : ContDiffBump x := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
    have hts : tsupport (f : Coord → ℝ) ⊆ U := by
      rw [f.tsupport_eq]
      intro y hy
      apply hball
      rw [Metric.mem_ball]
      have hy' := Metric.mem_closedBall.1 hy
      show dist y x < ε
      simp only [f] at hy'
      linarith
    have hφ : IsIooTest a b f := ⟨⟨f.contDiff, f.hasCompactSupport, hts.trans hU_pos⟩, hts⟩
    refine ⟨Metric.closedBall x (ε / 4),
      mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds x (by positivity)), ?_⟩
    refine ((hint f hφ).integrableOn (s := Metric.closedBall x (ε / 4))).congr_fun
      (fun y hy => ?_) Metric.isClosed_closedBall.measurableSet
    simp [f.one_of_mem_closedBall hy]
  have key := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero loc (μ := volume) ?_
  · rw [Filter.EventuallyEq, ae_restrict_iff' (measurableSet_Ioo.prod MeasurableSet.univ)]
    filter_upwards [key] with x hx hxU
    exact sub_eq_zero.1 (hx hxU)
  · intro φ hφs hφc hsub
    have hφ : IsIooTest a b φ := ⟨⟨hφs, hφc, hsub.trans hU_pos⟩, hsub⟩
    have heq := (h₁.2 φ hφ).trans (h₂.2 φ hφ).symm
    have e : ∫ x, φ x • (g₁ x - g₂ x) = ∫ x, ((g₁ x - g₂ x) * (φ x : ℂ)) :=
      integral_congr_ae (Eventually.of_forall fun x => by simp [mul_comm, Complex.real_smul])
    rw [e]
    simp only [sub_mul]
    rw [integral_sub (h₁.1 φ hφ).2 (h₂.1 φ hφ).2, heq, sub_self]

lemma weak_zero_on_Ioo {a b : ℝ} (ha : 0 ≤ a) (v : Coord → Fin 3 → ℝ) (d : Coord → ℝ)
    {u g : CProf} (hu : u =ᵐ[volume.restrict (Ioo a b ×ˢ univ)] 0)
    (h : HasWeakVecOnIoo a b v d u g) :
    g =ᵐ[volume.restrict (Ioo a b ×ˢ univ)] 0 := by
  have h0 : HasWeakVecOnIoo a b v d 0 0 := fun _ =>
    ⟨fun _ _ => ⟨by simp, by simp⟩, fun _ _ => by simp⟩
  have h' : HasWeakVecOnIoo a b v d 0 g :=
    hasWeakVecOnIoo_congr v d hu (EventuallyEq.refl _ _) h
  have hi : ∀ i : Fin 2,
      (fun x => g x i) =ᵐ[volume.restrict (Ioo a b ×ˢ univ)] (fun _ => (0 : ℂ)) :=
    fun i => weak_unique_on_Ioo ha v d (h' i) (h0 i)
  filter_upwards [hi 0, hi 1] with x h0x h1x
  ext j; fin_cases j
  · exact h0x
  · exact h1x

/-- Spatial transpose commutes with any smooth function of `s = x.1` alone (`w 0 = 0`). -/
lemma coordTranspose_mul_fst {w : Fin 3 → ℝ} (hw0 : w 0 = 0) {θ : ℝ → ℝ}
    (hθ : Differentiable ℝ θ) {φ : Coord → ℝ} (hφ : Differentiable ℝ φ) (x : Coord) :
    coordTranspose (fun _ => w) dZero (fun y => θ y.1 * φ y) x =
      θ x.1 * coordTranspose (fun _ => w) dZero φ x := by
  have hθc : Differentiable ℝ (fun y : Coord => θ y.1) := hθ.comp differentiable_fst
  have hmul : Differentiable ℝ (fun y : Coord => θ y.1 * φ y) := hθc.mul hφ
  rw [F8L.coordTranspose_const w hmul, F8L.coordTranspose_const w hφ]
  have h1 : HasFDerivAt (fun y : Coord => θ y.1)
      ((fderiv ℝ θ x.1).comp (ContinuousLinearMap.fst ℝ ℝ B0579.Plane)) x :=
    (hθ x.1).hasFDerivAt.comp x hasFDerivAt_fst
  have h2 : HasFDerivAt (fun y : Coord => θ y.1 * φ y) _ x := h1.mul (hφ x).hasFDerivAt
  have hc1 : cpd 1 (fun y : Coord => θ y.1 * φ y) x = θ x.1 * cpd 1 φ x := by
    simp [cpd, cdir, h2.fderiv]
  have hc2 : cpd 2 (fun y : Coord => θ y.1 * φ y) x = θ x.1 * cpd 2 φ x := by
    simp [cpd, cdir, h2.fderiv]
  simp [Fin.sum_univ_three, hw0, hc1, hc2]
  ring

/-- Gluing two overlapping age windows `(a₁, b₁)` and `(a₂, b₂)` (`a₂ < b₁`) for a
purely spatial first-order operator (`w 0 = 0`). -/
lemma hasWeakFOOnIoo_glue {a₁ b₁ a₂ b₂ : ℝ} (h_ov : a₂ < b₁)
    {w : Fin 3 → ℝ} (hw0 : w 0 = 0) {u g : Coord → ℂ}
    (h₁ : HasWeakFOOnIoo a₁ b₁ (fun _ => w) dZero u g)
    (h₂ : HasWeakFOOnIoo a₂ b₂ (fun _ => w) dZero u g) :
    HasWeakFOOnIoo a₁ b₂ (fun _ => w) dZero u g := by
  let m : ℝ := (a₂ + b₁) / 2
  let δ : ℝ := (b₁ - a₂) / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let θ₁ : ℝ → ℝ := fun s => Real.smoothTransition ((m + δ - s) / (2 * δ))
  let θ₂ : ℝ → ℝ := fun s => 1 - θ₁ s
  have hθ₁_sm : ContDiff ℝ ∞ θ₁ :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const (2 * δ))
  have hθ₂_sm : ContDiff ℝ ∞ θ₂ := contDiff_const.sub hθ₁_sm
  have hθ₁_nn : ∀ s, 0 ≤ θ₁ s := fun s => Real.smoothTransition.nonneg _
  have hθ₁_le : ∀ s, θ₁ s ≤ 1 := fun s => Real.smoothTransition.le_one _
  have hθ₂_nn : ∀ s, 0 ≤ θ₂ s := fun s => sub_nonneg.2 (hθ₁_le s)
  have hθ₁_zero : ∀ s, m + δ ≤ s → θ₁ s = 0 := by
    intro s hs
    apply Real.smoothTransition.zero_of_nonpos
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  have hθ₂_zero : ∀ s, s ≤ m - δ → θ₂ s = 0 := by
    intro s hs
    have h1 : θ₁ s = 1 := by
      apply Real.smoothTransition.one_of_one_le
      rw [le_div_iff₀ (by positivity)]
      linarith
    simp [θ₂, h1]
  have hts₁ : tsupport (fun x : Coord => θ₁ x.1) ⊆ {x : Coord | x.1 ≤ m + δ} := by
    refine closure_minimal (fun x hx => ?_) (isClosed_le continuous_fst continuous_const)
    by_contra hlt
    exact hx (hθ₁_zero x.1 (le_of_lt (not_le.1 hlt)))
  have hts₂ : tsupport (fun x : Coord => θ₂ x.1) ⊆ {x : Coord | m - δ ≤ x.1} := by
    refine closure_minimal (fun x hx => ?_) (isClosed_le continuous_const continuous_fst)
    by_contra hlt
    exact hx (hθ₂_zero x.1 (le_of_lt (not_le.1 hlt)))
  have split_test : ∀ φ, IsIooTest a₁ b₂ φ →
      IsIooTest a₁ b₁ (fun x => θ₁ x.1 * φ x) ∧ IsIooTest a₂ b₂ (fun x => θ₂ x.1 * φ x) := by
    intro φ hφ
    have hsm₁ : ContDiff ℝ ∞ (fun x : Coord => θ₁ x.1) := hθ₁_sm.comp contDiff_fst
    have hsm₂ : ContDiff ℝ ∞ (fun x : Coord => θ₂ x.1) := hθ₂_sm.comp contDiff_fst
    have hc₁ : IsCoordTest (fun x => θ₁ x.1 * φ x) :=
      ⟨hsm₁.mul hφ.1.smooth, hφ.1.compact.mul_left, tsupport_mul_subset_right.trans hφ.1.supp⟩
    have hc₂ : IsCoordTest (fun x => θ₂ x.1 * φ x) :=
      ⟨hsm₂.mul hφ.1.smooth, hφ.1.compact.mul_left, tsupport_mul_subset_right.trans hφ.1.supp⟩
    refine ⟨⟨hc₁, ?_⟩, ⟨hc₂, ?_⟩⟩
    · intro x hx
      have hx₁ := hts₁ (tsupport_mul_subset_left hx)
      have hx₂ := hφ.2 (tsupport_mul_subset_right hx)
      exact ⟨⟨hx₂.1.1, lt_of_le_of_lt hx₁ (by dsimp [m, δ]; linarith)⟩, trivial⟩
    · intro x hx
      have hx₁ := hts₂ (tsupport_mul_subset_left hx)
      have hx₂ := hφ.2 (tsupport_mul_subset_right hx)
      exact ⟨⟨lt_of_lt_of_le (by dsimp [m, δ]; linarith) hx₁, hx₂.1.2⟩, trivial⟩
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_⟩
  · obtain ⟨ht₁, ht₂⟩ := split_test φ hφ
    have hdφ : Differentiable ℝ φ := hφ.1.smooth.differentiable (by simp)
    have hsumU : ∀ x, u x * (coordTranspose (fun _ => w) dZero φ x : ℂ) =
        u x * (coordTranspose (fun _ => w) dZero (fun y => θ₁ y.1 * φ y) x : ℂ) +
          u x * (coordTranspose (fun _ => w) dZero (fun y => θ₂ y.1 * φ y) x : ℂ) := by
      intro x
      rw [coordTranspose_mul_fst hw0 (hθ₁_sm.differentiable (by simp)) hdφ,
        coordTranspose_mul_fst hw0 (hθ₂_sm.differentiable (by simp)) hdφ]
      dsimp [θ₂]
      push_cast
      ring
    have hsumG : ∀ x, g x * (φ x : ℂ) =
        g x * (((θ₁ x.1 * φ x : ℝ) : ℂ)) + g x * (((θ₂ x.1 * φ x : ℝ) : ℂ)) := by
      intro x; dsimp [θ₂]; push_cast; ring
    exact ⟨(((h₁.1 _ ht₁).1).add ((h₂.1 _ ht₂).1)).congr (Eventually.of_forall fun x => (hsumU x).symm),
      (((h₁.1 _ ht₁).2).add ((h₂.1 _ ht₂).2)).congr (Eventually.of_forall fun x => (hsumG x).symm)⟩
  · obtain ⟨ht₁, ht₂⟩ := split_test φ hφ
    have hdφ : Differentiable ℝ φ := hφ.1.smooth.differentiable (by simp)
    have hsumU : (fun x => u x * (coordTranspose (fun _ => w) dZero φ x : ℂ)) =
        fun x => u x * (coordTranspose (fun _ => w) dZero (fun y => θ₁ y.1 * φ y) x : ℂ) +
          u x * (coordTranspose (fun _ => w) dZero (fun y => θ₂ y.1 * φ y) x : ℂ) := by
      funext x
      rw [coordTranspose_mul_fst hw0 (hθ₁_sm.differentiable (by simp)) hdφ,
        coordTranspose_mul_fst hw0 (hθ₂_sm.differentiable (by simp)) hdφ]
      dsimp [θ₂]; push_cast; ring
    have hsumG : (fun x => g x * (φ x : ℂ)) =
        fun x => g x * (((θ₁ x.1 * φ x : ℝ) : ℂ)) + g x * (((θ₂ x.1 * φ x : ℝ) : ℂ)) := by
      funext x; dsimp [θ₂]; push_cast; ring
    rw [hsumG, integral_add (h₁.1 _ ht₁).2 (h₂.1 _ ht₂).2,
      h₁.2 _ ht₁, h₂.2 _ ht₂, ← integral_add (h₁.1 _ ht₁).1 (h₂.1 _ ht₂).1, ← hsumU]

lemma hasWeakVecOnIoo_glue {a₁ b₁ a₂ b₂ : ℝ} (h_ov : a₂ < b₁)
    {w : Fin 3 → ℝ} (hw0 : w 0 = 0) {u g : CProf}
    (h₁ : HasWeakVecOnIoo a₁ b₁ (fun _ => w) dZero u g)
    (h₂ : HasWeakVecOnIoo a₂ b₂ (fun _ => w) dZero u g) :
    HasWeakVecOnIoo a₁ b₂ (fun _ => w) dZero u g :=
  fun i => hasWeakFOOnIoo_glue h_ov hw0 (h₁ i) (h₂ i)

/-- Exhaustion of `(0, ∞)` by open intervals lifts `HasWeakVecOnIoo` to global `HasWeakVec`. -/
lemma hasWeakVec_of_exhaust_Ioo {v : Coord → Fin 3 → ℝ} {d : Coord → ℝ} {u g : CProf}
    (hex : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ ≤ s₂ →
      ∃ a b : ℝ, a < s₁ ∧ s₂ < b ∧ HasWeakVecOnIoo a b v d u g) :
    HasWeakVec v d u g := by
  intro i
  have hcomp : ∀ φ : Coord → ℝ, IsCoordTest φ → ∃ a b : ℝ, IsIooTest a b φ ∧
      HasWeakVecOnIoo a b v d u g := by
    intro φ hφ
    by_cases hne : (tsupport φ).Nonempty
    · have hK : IsCompact (Prod.fst '' tsupport φ) := hφ.compact.image continuous_fst
      have hne' : (Prod.fst '' tsupport φ).Nonempty := hne.image Prod.fst
      obtain ⟨s₁, hs₁_mem, hs₁_min⟩ := hK.exists_isMinOn hne' continuousOn_id
      obtain ⟨s₂, hs₂_mem, hs₂_max⟩ := hK.exists_isMaxOn hne' continuousOn_id
      rcases hs₁_mem with ⟨x₁, hx₁, rfl⟩
      have hs₁_pos : 0 < x₁.1 := (hφ.supp hx₁).1
      have hs₁₂ : x₁.1 ≤ s₂ := hs₂_max ⟨x₁, hx₁, rfl⟩
      obtain ⟨a, b, ha, hb, hw⟩ := hex x₁.1 s₂ hs₁_pos hs₁₂
      refine ⟨a, b, ⟨hφ, fun y hy => ⟨⟨lt_of_lt_of_le ha (hs₁_min ⟨y, hy, rfl⟩),
        lt_of_le_of_lt (hs₂_max ⟨y, hy, rfl⟩) hb⟩, trivial⟩⟩, hw⟩
    · rw [not_nonempty_iff_eq_empty] at hne
      obtain ⟨a, b, ha, hb, hw⟩ := hex 1 2 one_pos (by norm_num)
      refine ⟨a, b, ⟨hφ, by rw [hne]; exact empty_subset _⟩, hw⟩
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_⟩
  · obtain ⟨a, b, hI, hw⟩ := hcomp φ hφ
    exact (hw i).1 φ hI
  · obtain ⟨a, b, hI, hw⟩ := hcomp φ hφ
    exact (hw i).2 φ hI

/-! ## 2. `L¹` integrability of the forcing slice norm on bounded age intervals -/

lemma G_lintegral_Ioc_lt_top {T₀ T₁ : ℝ} (hT₁ : 0 < T₁) (hT₁₀ : T₁ ≤ T₀)
    {G : ℝ → ℝ≥0∞} (hG : Measurable G)
    (hsLp : sLpNorm (13 / 8) T₀ G < ⊤)
    (htail : tailLpNorm (-9 / 8) T₁ G < ⊤) :
    ∀ B : ℝ, 0 < B → ∫⁻ s in Ioc 0 B, G s < ⊤ := by
  have hT₀ : 0 < T₀ := lt_of_lt_of_le hT₁ hT₁₀
  have hL1_T₀ : ∫⁻ s in Ioc 0 T₀, G s < ⊤ := by
    have hh := hardyL1_proof T₀ hT₀ G hG
    unfold sLpNorm at hsLp
    exact lt_of_le_of_lt hh (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hsLp)
  have htail_int : ∫⁻ s in Ioi T₁, G s ^ bgp * ENNReal.ofReal (s ^ (-9 / 8 : ℝ)) < ⊤ := by
    unfold tailLpNorm at htail
    have hfin : ∫⁻ s in Ioi T₁, G s ^ bgp ∂sMeas (-9 / 8) < ⊤ := by
      by_contra htop
      rw [not_lt, top_le_iff] at htop
      rw [htop, ENNReal.top_rpow_of_pos (by norm_num)] at htail
      exact lt_irrefl _ htail
    rwa [sMeas_Ioi (-9 / 8) T₁ hT₁.le (fun s => G s ^ bgp) (by fun_prop)] at hfin
  intro B hB
  by_cases hBT₀ : B ≤ T₀
  · exact lt_of_le_of_lt (lintegral_mono_set (Ioc_subset_Ioc_right hBT₀)) hL1_T₀
  · replace hBT₀ : T₀ < B := lt_of_not_ge hBT₀
    have hT₁B : T₁ < B := lt_of_le_of_lt hT₁₀ hBT₀
    have hsub : Ioc 0 B ⊆ Ioc 0 T₀ ∪ Ioc T₁ B := by
      intro s hs
      by_cases hsT₀ : s ≤ T₀
      · exact Or.inl ⟨hs.1, hsT₀⟩
      · exact Or.inr ⟨lt_of_le_of_lt hT₁₀ (not_le.1 hsT₀), hs.2⟩
    refine lt_of_le_of_lt ((lintegral_mono_set hsub).trans (lintegral_union_le _ _ _)) ?_
    refine ENNReal.add_lt_top.2 ⟨hL1_T₀, ?_⟩
    have hpoint : ∀ s ∈ Ioc T₁ B,
        G s ≤ 1 + ENNReal.ofReal (B ^ (9 / 8 : ℝ)) *
          (G s ^ bgp * ENNReal.ofReal (s ^ (-9 / 8 : ℝ))) := by
      intro s hs
      have hs0 : 0 < s := lt_trans hT₁ hs.1
      have hG_pow : G s ≤ 1 + G s ^ bgp := by
        rcases le_or_gt (G s) 1 with hle | hgt
        · exact hle.trans le_self_add
        · have h1 : G s ≤ G s ^ bgp := by
            simpa using ENNReal.rpow_le_rpow_of_exponent_le hgt.le (show (1 : ℝ) ≤ bgp by norm_num [bgp])
          exact h1.trans le_add_self
      have hB_id : ENNReal.ofReal (B ^ (9 / 8 : ℝ)) * ENNReal.ofReal (B ^ (-9 / 8 : ℝ)) = 1 := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hB.le _), ← Real.rpow_add hB]
        norm_num
      have hs_ge : B ^ (-9 / 8 : ℝ) ≤ s ^ (-9 / 8 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos hs0 hs.2 (by norm_num)
      calc G s ≤ 1 + G s ^ bgp := hG_pow
        _ = 1 + ENNReal.ofReal (B ^ (9 / 8 : ℝ)) *
              (G s ^ bgp * ENNReal.ofReal (B ^ (-9 / 8 : ℝ))) := by
            rw [← mul_assoc, mul_comm (ENNReal.ofReal _), mul_assoc, hB_id, mul_one]
        _ ≤ 1 + ENNReal.ofReal (B ^ (9 / 8 : ℝ)) *
              (G s ^ bgp * ENNReal.ofReal (s ^ (-9 / 8 : ℝ))) := by
            gcongr
    have hmono : ∫⁻ s in Ioc T₁ B, G s ≤
        ∫⁻ s in Ioc T₁ B, (1 + ENNReal.ofReal (B ^ (9 / 8 : ℝ)) *
          (G s ^ bgp * ENNReal.ofReal (s ^ (-9 / 8 : ℝ)))) :=
      setLIntegral_mono (by fun_prop) hpoint
    refine lt_of_le_of_lt hmono ?_
    rw [lintegral_add_left measurable_const, setLIntegral_const, one_mul, lintegral_const_mul _ (by fun_prop)]
    have hvol : volume (Ioc T₁ B) < ⊤ := by simp [Real.volume_Ioc]
    have hsub_tail : ∫⁻ s in Ioc T₁ B, G s ^ bgp * ENNReal.ofReal (s ^ (-9 / 8 : ℝ)) < ⊤ :=
      lt_of_le_of_lt (lintegral_mono_set (fun s hs => hs.1)) htail_int
    exact ENNReal.add_lt_top.2 ⟨hvol, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hsub_tail⟩

lemma G_ae_lt_top {T₀ T₁ : ℝ} (hT₁ : 0 < T₁) (hT₁₀ : T₁ ≤ T₀)
    {G : ℝ → ℝ≥0∞} (hG : Measurable G)
    (hsLp : sLpNorm (13 / 8) T₀ G < ⊤)
    (htail : tailLpNorm (-9 / 8) T₁ G < ⊤) :
    ∀ᵐ s ∂volume, 0 < s → G s < ⊤ := by
  have hN : ∀ n : ℕ, ∀ᵐ s ∂volume, s ∈ Ioc 0 ((n : ℝ) + 1) → G s < ⊤ := by
    intro n
    have hfin := G_lintegral_Ioc_lt_top hT₁ hT₁₀ hG hsLp htail ((n : ℝ) + 1) (by positivity)
    have hae := ae_lt_top hG hfin.ne
    rwa [ae_restrict_iff' measurableSet_Ioc] at hae
  filter_upwards [ae_all_iff.2 hN] with s hs hs0
  obtain ⟨n, hn⟩ := exists_nat_gt s
  exact hs n ⟨hs0, by linarith⟩

/-! ## 3. Local integrability from `HasWeakFO vQ0`, Borel `QPeriodic` upgrade, and `IsCylH1Datum` -/

lemma locInt_of_hasWeakFO_q {f fq : Coord → ℂ} (hw : HasWeakFO vQ0 dZero f fq) :
    LocallyIntegrableOn f {x : Coord | 0 < x.1} volume ∧
      LocallyIntegrableOn fq {x : Coord | 0 < x.1} volume := by
  have hU : IsOpen {x : Coord | 0 < x.1} := isOpen_lt continuous_const continuous_fst
  constructor
  · intro x₀ hx₀
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
    let χ : ContDiffBump x₀ := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
    have hχ : IsCoordTest χ := by
      refine ⟨χ.contDiff, χ.hasCompactSupport, ?_⟩
      rw [χ.tsupport_eq]
      intro y hy
      have hy' := Metric.mem_closedBall.1 hy
      have hyb : y ∈ Metric.ball x₀ ε := by
        rw [Metric.mem_ball]; simp only [χ] at hy'; linarith
      simpa using hball hyb
    let φ : Coord → ℝ := fun z => -(z.2.1 - x₀.2.1) * χ z
    have hφ_sm : ContDiff ℝ ∞ φ :=
      (((contDiff_fst.comp contDiff_snd).sub contDiff_const).neg).mul χ.contDiff
    have hφ : IsCoordTest φ :=
      ⟨hφ_sm, χ.hasCompactSupport.mul_left, tsupport_mul_subset_right.trans hχ.supp⟩
    refine ⟨Metric.closedBall x₀ (ε / 8),
      mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds x₀ (by positivity)), ?_⟩
    refine ((hw.1 φ hφ).1.integrableOn (s := Metric.closedBall x₀ (ε / 8))).congr_fun
      (fun y hy => ?_) Metric.isClosed_closedBall.measurableSet
    have hχ_ev : (χ : Coord → ℝ) =ᶠ[𝓝 y] fun _ => (1 : ℝ) := by
      have hy_in : y ∈ Metric.ball x₀ (ε / 4) := by
        rw [Metric.mem_ball]
        exact lt_of_le_of_lt (Metric.mem_closedBall.1 hy) (by linarith)
      filter_upwards [Metric.isOpen_ball.mem_nhds hy_in] with z hz
      exact χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hz)
    have hφ_ev : φ =ᶠ[𝓝 y] fun z : Coord => -(z.2.1 - x₀.2.1) :=
      hχ_ev.mono fun z hz => by simp [φ, hz]
    have hfd : fderiv ℝ φ y =
        -((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) := by
      rw [hφ_ev.fderiv_eq]
      exact (((hasFDerivAt_fst.comp y hasFDerivAt_snd).sub_const x₀.2.1).neg).fderiv
    have hct : coordTranspose vQ0 dZero φ y = 1 := by
      unfold vQ0
      rw [F8L.coordTranspose_const ![0, 1, 0] (hφ_sm.differentiable (by simp)) y]
      simp [Fin.sum_univ_three, cpd, cdir, hfd]
    simp [hct]
  · intro x₀ hx₀
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
    let χ : ContDiffBump x₀ := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
    have hχ : IsCoordTest χ := by
      refine ⟨χ.contDiff, χ.hasCompactSupport, ?_⟩
      rw [χ.tsupport_eq]
      intro y hy
      have hy' := Metric.mem_closedBall.1 hy
      have hyb : y ∈ Metric.ball x₀ ε := by
        rw [Metric.mem_ball]; simp only [χ] at hy'; linarith
      simpa using hball hyb
    refine ⟨Metric.closedBall x₀ (ε / 4),
      mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds x₀ (by positivity)), ?_⟩
    refine ((hw.1 χ hχ).2.integrableOn (s := Metric.closedBall x₀ (ε / 4))).congr_fun
      (fun y hy => ?_) Metric.isClosed_closedBall.measurableSet
    simp [χ.one_of_mem_closedBall hy]

lemma exists_sm_qper_pos {c : ℝ} {u : CProf} (hper : QPeriodic c u)
    (hloc : ∀ i : Fin 2, LocallyIntegrableOn (fun x => u x i) {x : Coord | 0 < x.1} volume) :
    ∃ u₁ : CProf, StronglyMeasurable u₁ ∧ QPeriodic c u₁ ∧
      u₁ =ᵐ[volume.restrict {x : Coord | 0 < x.1}] u := by
  set Upos : Set Coord := {x : Coord | 0 < x.1}
  have hmeas_U : MeasurableSet Upos := measurableSet_lt measurable_const measurable_fst
  have haesm_comp : ∀ i : Fin 2, AEStronglyMeasurable (Upos.indicator (fun x => u x i)) volume :=
    fun i => (aestronglyMeasurable_indicator_iff hmeas_U).2 (hloc i).aestronglyMeasurable
  set u₀ : CProf := fun x => if 0 < x.1 then u x else 0
  have hu₀_eq : u₀ = wbdVec (fun i => Upos.indicator (fun x => u x i)) := by
    funext x; ext i
    by_cases hp : 0 < x.1 <;> simp [u₀, Upos, wbdVec, hp]
  have hu₀_aesm : AEStronglyMeasurable u₀ volume := by
    rw [hu₀_eq]; exact wbdVec_aesm haesm_comp
  have hu₀_per : QPeriodic c u₀ := by
    refine QPerHalf.of_ae_imp ?_
    filter_upwards [QPerHalf.ae_imp hper] with x hx hp
    simp [u₀, hp, hx hp]
  obtain ⟨u₁, hu₁_sm, hu₁_per, hu₁_ae⟩ := exists_sm_rep_vol hu₀_per hu₀_aesm
  refine ⟨u₁, hu₁_sm, hu₁_per, ?_⟩
  rw [Filter.EventuallyEq, ae_restrict_iff' hmeas_U]
  filter_upwards [hu₁_ae] with x hx hp
  have hp' : 0 < x.1 := hp
  simpa only [u₀, hp', ↓reduceIte] using hx

/-- Upgrade a `QPeriodic`, weakly solenoidal `(u, uq, uη)` triple to a `StronglyMeasurable`,
`QPeriodic` triple agreeing `volume`-a.e. on `s > 0`, preserving `sliceH1Norm` a.e., and yielding
`F8U.IsCylH1Datum` on a.e. slice `s > 0` where `sliceH1Norm < ⊤`. -/
lemma upgrade_weakH1_solenoidal {c : ℝ} (hc : 0 < c) {u uq uη : CProf}
    (hu_per : QPeriodic c u)
    (huq : HasWeakVec vQ0 dZero u uq)
    (huη : HasWeakVec vEta dZero u uη)
    (hsol : ∀ φ, IsCoordTest φ →
      Integrable (fun x => u x 0 * (cpd 1 φ x : ℂ) + u x 1 * (cpd 2 φ x : ℂ)) ∧
        ∫ x, (u x 0 * (cpd 1 φ x : ℂ) + u x 1 * (cpd 2 φ x : ℂ)) = 0) :
    ∃ u₁ uq₁ uη₁ : CProf,
      StronglyMeasurable u₁ ∧ StronglyMeasurable uq₁ ∧ StronglyMeasurable uη₁ ∧
      QPeriodic c u₁ ∧ QPeriodic c uq₁ ∧ QPeriodic c uη₁ ∧
      HasWeakVec vQ0 dZero u₁ uq₁ ∧ HasWeakVec vEta dZero u₁ uη₁ ∧
      (∀ φ, IsCoordTest φ →
        Integrable (fun x => u₁ x 0 * (cpd 1 φ x : ℂ) + u₁ x 1 * (cpd 2 φ x : ℂ)) ∧
          ∫ x, (u₁ x 0 * (cpd 1 φ x : ℂ) + u₁ x 1 * (cpd 2 φ x : ℂ)) = 0) ∧
      u₁ =ᵐ[volume.restrict {x : Coord | 0 < x.1}] u ∧
      uq₁ =ᵐ[volume.restrict {x : Coord | 0 < x.1}] uq ∧
      uη₁ =ᵐ[volume.restrict {x : Coord | 0 < x.1}] uη ∧
      (∀ᵐ s ∂volume, 0 < s → sliceH1Norm c u₁ uq₁ uη₁ s = sliceH1Norm c u uq uη s) ∧
      (∀ᵐ s ∂volume, 0 < s → sliceH1Norm c u₁ uq₁ uη₁ s < ⊤ →
        F8U.IsCylH1Datum c (F8U.slice u₁ s) (F8U.slice uq₁ s) (F8U.slice uη₁ s)) := by
  have huq_per : QPeriodic c uq := F8L.qperiodic_deriv ![0, 1, 0] hu_per huq
  have huη_per : QPeriodic c uη := F8L.qperiodic_deriv ![0, 0, 1] hu_per huη
  have hloc_u : ∀ i : Fin 2, LocallyIntegrableOn (fun x => u x i) {x : Coord | 0 < x.1} volume :=
    fun i => (locInt_of_hasWeakFO_q (huq i)).1
  have hloc_uq : ∀ i : Fin 2, LocallyIntegrableOn (fun x => uq x i) {x : Coord | 0 < x.1} volume :=
    fun i => (locInt_of_hasWeakFO_q (huq i)).2
  have hloc_uη : ∀ i : Fin 2, LocallyIntegrableOn (fun x => uη x i) {x : Coord | 0 < x.1} volume := by
    intro i x₀ hx₀
    have hU : IsOpen {x : Coord | 0 < x.1} := isOpen_lt continuous_const continuous_fst
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
    let χ : ContDiffBump x₀ := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
    have hχ : IsCoordTest χ := by
      refine ⟨χ.contDiff, χ.hasCompactSupport, ?_⟩
      rw [χ.tsupport_eq]
      intro y hy
      have hy' := Metric.mem_closedBall.1 hy
      have hyb : y ∈ Metric.ball x₀ ε := by
        rw [Metric.mem_ball]; simp only [χ] at hy'; linarith
      simpa using hball hyb
    refine ⟨Metric.closedBall x₀ (ε / 4),
      mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds x₀ (by positivity)), ?_⟩
    refine (((huη i).1 χ hχ).2.integrableOn (s := Metric.closedBall x₀ (ε / 4))).congr_fun
      (fun y hy => ?_) Metric.isClosed_closedBall.measurableSet
    simp [χ.one_of_mem_closedBall hy]
  obtain ⟨u₁, hu₁_sm, hu₁_per, hu₁_ae⟩ := exists_sm_qper_pos hu_per hloc_u
  obtain ⟨uq₁, huq₁_sm, huq₁_per, huq₁_ae⟩ := exists_sm_qper_pos huq_per hloc_uq
  obtain ⟨uη₁, huη₁_sm, huη₁_per, huη₁_ae⟩ := exists_sm_qper_pos huη_per hloc_uη
  have huq₁ : HasWeakVec vQ0 dZero u₁ uq₁ := fun i =>
    F8L.hasWeakFO_congr vQ0 dZero
      (hu₁_ae.symm.mono fun _ hx => congrArg (fun v => v i) hx)
      (huq₁_ae.symm.mono fun _ hx => congrArg (fun v => v i) hx) (huq i)
  have huη₁ : HasWeakVec vEta dZero u₁ uη₁ := fun i =>
    F8L.hasWeakFO_congr vEta dZero
      (hu₁_ae.symm.mono fun _ hx => congrArg (fun v => v i) hx)
      (huη₁_ae.symm.mono fun _ hx => congrArg (fun v => v i) hx) (huη i)
  have hsol₁ := F8L.transfer_solenoidal hu₁_ae.symm hsol
  have hsl_eq : ∀ᵐ s ∂volume, 0 < s → sliceH1Norm c u₁ uq₁ uη₁ s = sliceH1Norm c u uq uη s := by
    filter_upwards [F8L.slice_ae hu₁_ae, F8L.slice_ae huq₁_ae, F8L.slice_ae huη₁_ae] with s h1 h2 h3 hs0
    unfold sliceH1Norm
    rw [eLpNorm_congr_ae (ae_restrict_of_ae (h1 hs0)),
      eLpNorm_congr_ae (ae_restrict_of_ae (h2 hs0)),
      eLpNorm_congr_ae (ae_restrict_of_ae (h3 hs0))]
  have hdiv_ae : ∀ᵐ x : Coord, 0 < x.1 → uq₁ x 0 + uη₁ x 1 = 0 := by
    have hU : IsOpen {x : Coord | 0 < x.1} := isOpen_lt continuous_const continuous_fst
    have hloc_div : LocallyIntegrableOn (fun x => uq₁ x 0 + uη₁ x 1) {x : Coord | 0 < x.1} volume := by
      have l0 := (locInt_of_hasWeakFO_q (huq₁ 0)).2
      have l1 : LocallyIntegrableOn (fun x => uη₁ x 1) {x : Coord | 0 < x.1} volume := by
        intro x₀ hx₀
        obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
        let χ : ContDiffBump x₀ := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
        have hχ : IsCoordTest χ := by
          refine ⟨χ.contDiff, χ.hasCompactSupport, ?_⟩
          rw [χ.tsupport_eq]
          intro y hy
          have hy' := Metric.mem_closedBall.1 hy
          have hyb : y ∈ Metric.ball x₀ ε := by
            rw [Metric.mem_ball]; simp only [χ] at hy'; linarith
          simpa using hball hyb
        refine ⟨Metric.closedBall x₀ (ε / 4),
          mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds x₀ (by positivity)), ?_⟩
        refine (((huη₁ 1).1 χ hχ).2.integrableOn (s := Metric.closedBall x₀ (ε / 4))).congr_fun
          (fun y hy => ?_) Metric.isClosed_closedBall.measurableSet
        simp [χ.one_of_mem_closedBall hy]
      exact l0.add l1
    have key := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc_div (μ := volume) ?_
    · filter_upwards [key] with x hx hp
      exact hx hp
    · intro φ hφs hφc hsub
      have hφ : IsCoordTest φ := ⟨hφs, hφc, fun y hy => by simpa using hsub hy⟩
      have hdφ : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
      have hIq := ((huq₁ 0).1 φ hφ).2
      have hIη := ((huη₁ 1).1 φ hφ).2
      have e : ∫ x, φ x • (uq₁ x 0 + uη₁ x 1) =
          (∫ x, uq₁ x 0 * (φ x : ℂ)) + ∫ x, uη₁ x 1 * (φ x : ℂ) := by
        rw [← integral_add hIq hIη]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp [Complex.real_smul]; ring
      rw [e, (huq₁ 0).2 φ hφ, (huη₁ 1).2 φ hφ]
      have hctQ : (fun x => u₁ x 0 * (coordTranspose vQ0 dZero φ x : ℂ)) =
          fun x => -(u₁ x 0 * (cpd 1 φ x : ℂ)) := by
        funext x
        unfold vQ0
        rw [F8L.coordTranspose_const ![0, 1, 0] hdφ x]
        simp [Fin.sum_univ_three]
      have hctE : (fun x => u₁ x 1 * (coordTranspose vEta dZero φ x : ℂ)) =
          fun x => -(u₁ x 1 * (cpd 2 φ x : ℂ)) := by
        funext x
        unfold vEta
        rw [F8L.coordTranspose_const ![0, 0, 1] hdφ x]
        simp [Fin.sum_univ_three]
      have hIq' : Integrable (fun x => u₁ x 0 * (cpd 1 φ x : ℂ)) := by
        have := ((huq₁ 0).1 φ hφ).1; rw [hctQ] at this
        exact this.neg.congr (Eventually.of_forall fun x => neg_neg _)
      have hIη' : Integrable (fun x => u₁ x 1 * (cpd 2 φ x : ℂ)) := by
        have := ((huη₁ 1).1 φ hφ).1; rw [hctE] at this
        exact this.neg.congr (Eventually.of_forall fun x => neg_neg _)
      rw [hctQ, hctE, integral_neg, integral_neg, ← neg_add, ← integral_add hIq' hIη',
        (hsol₁ φ hφ).2, neg_zero]
  have hjw0 := FlatBvSliceGoodAeNeeded.jointWeakToSlice_proof c hc 0 u₁ uq₁
    hu₁_sm huq₁_sm hu₁_per huq₁_per (by simpa using huq₁)
  have hjw1 := FlatBvSliceGoodAeNeeded.jointWeakToSlice_proof c hc 1 u₁ uη₁
    hu₁_sm huη₁_sm hu₁_per huη₁_per (by simpa using huη₁)
  have hdiv_sl : ∀ᵐ s ∂(volume : Measure ℝ), ∀ᵐ y ∂(volume : Measure B0579.Plane),
      0 < (s, y).1 → uq₁ (s, y) 0 + uη₁ (s, y) 1 = 0 :=
    Measure.ae_ae_of_ae_prod hdiv_ae
  have hdat : ∀ᵐ s ∂volume, 0 < s → sliceH1Norm c u₁ uq₁ uη₁ s < ⊤ →
      F8U.IsCylH1Datum c (F8U.slice u₁ s) (F8U.slice uq₁ s) (F8U.slice uη₁ s) := by
    filter_upwards [hjw0, hjw1, hdiv_sl] with s hw0 hw1 hds hs0 hfin
    unfold sliceH1Norm at hfin
    have hmu : MemLp (F8U.slice u₁ s) 2 (volume.restrict (B0579.cell c)) :=
      ⟨(F8L.sliceMeas hu₁_sm s).aestronglyMeasurable,
        lt_of_le_of_lt (le_self_add.trans le_self_add) hfin⟩
    have hmuq : MemLp (F8U.slice uq₁ s) 2 (volume.restrict (B0579.cell c)) :=
      ⟨(F8L.sliceMeas huq₁_sm s).aestronglyMeasurable,
        lt_of_le_of_lt (le_add_self.trans le_self_add) hfin⟩
    have hmuη : MemLp (F8U.slice uη₁ s) 2 (volume.restrict (B0579.cell c)) :=
      ⟨(F8L.sliceMeas huη₁_sm s).aestronglyMeasurable,
        lt_of_le_of_lt le_add_self hfin⟩
    have hcd0 := hw0 hs0 hmu hmuq
    have hcd1 := hw1 hs0 hmu hmuη
    refine ⟨hcd0, hcd1, fun ψ hψ => ?_, ⟨hmu, hmuq, hmuη⟩⟩
    dsimp only [F8U.slice]
    refine ⟨((hcd0 0).1 ψ hψ).1.add ((hcd1 1).1 ψ hψ).1, ?_⟩
    rw [integral_add ((hcd0 0).1 ψ hψ).1 ((hcd1 1).1 ψ hψ).1,
      (hcd0 0).2 ψ hψ, (hcd1 1).2 ψ hψ, ← neg_add,
      ← integral_add ((hcd0 0).1 ψ hψ).2 ((hcd1 1).1 ψ hψ).2]
    have hzero : ∫ y in B0579.cell c,
        (uq₁ (s, y) 0 * (ψ y : ℂ) + uη₁ (s, y) 1 * (ψ y : ℂ)) = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [ae_restrict_of_ae hds] with y hy
      calc uq₁ (s, y) 0 * (ψ y : ℂ) + uη₁ (s, y) 1 * (ψ y : ℂ)
          = (uq₁ (s, y) 0 + uη₁ (s, y) 1) * (ψ y : ℂ) := by ring
        _ = 0 := by rw [hy hs0, zero_mul]
    rw [hzero, neg_zero]
  exact ⟨u₁, uq₁, uη₁, hu₁_sm, huq₁_sm, huη₁_sm, hu₁_per, huq₁_per, huη₁_per,
    huq₁, huη₁, hsol₁, hu₁_ae, huq₁_ae, huη₁_ae, hsl_eq, hdat⟩

/-! ## 4. Right-Lebesgue `L²(cell)` differentiation at a.e. age `σ > 0` -/

lemma ae_rightLebesgue_sliceL2 {c M : ℝ} (hM : 0 ≤ M) {z₁ : CProf}
    (hz₁_sm : StronglyMeasurable z₁)
    (hbnd : ∀ᵐ s ∂volume, 0 < s → F8U.cellL2 c (F8U.slice z₁ s) ≤ ENNReal.ofReal M) :
    ∀ᵐ σ ∂volume, 0 < σ →
      Tendsto (fun h : ℝ => h⁻¹ *
        ∫ t in Ioc σ (σ + h), (F8U.cellL2 c (fun y => z₁ (t, y) - z₁ (σ, y))).toReal ^ 2)
        (𝓝[>] 0) (𝓝 0) := by
  let μc : Measure B0579.Plane := volume.restrict (B0579.cell c)
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let path₀ : ℝ → Lp CMerid 2 μc := UnforcedLeray.BochnerTime.toPathLq 2 μc z₁
  have hpath₀_sm : StronglyMeasurable path₀ :=
    UnforcedLeray.BochnerTime.stronglyMeasurable_toPathLq hz₁_sm
  let S_good : Set ℝ := {s : ℝ | F8U.cellL2 c (F8U.slice z₁ s) ≤ ENNReal.ofReal M}
  have hN_meas : Measurable (fun s : ℝ => ∫⁻ y, ‖z₁ (s, y)‖ₑ ^ (2 : ℝ) ∂μc) :=
    (hz₁_sm.enorm.pow_const _).lintegral_prod_right'
  have hcell_eq : ∀ s : ℝ, F8U.cellL2 c (F8U.slice z₁ s) =
      (∫⁻ y, ‖z₁ (s, y)‖ₑ ^ (2 : ℝ) ∂μc) ^ (1 / (2 : ℝ)) := by
    intro s
    unfold F8U.cellL2 F8U.slice
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    rfl
  have hS_meas : MeasurableSet S_good := by
    have : S_good = {s : ℝ | (∫⁻ y, ‖z₁ (s, y)‖ₑ ^ (2 : ℝ) ∂μc) ^ (1 / (2 : ℝ)) ≤ ENNReal.ofReal M} := by
      ext s; simp [S_good, hcell_eq]
    rw [this]
    exact measurableSet_le (hN_meas.pow_const _) measurable_const
  let f : ℝ → Lp CMerid 2 μc := S_good.piecewise path₀ 0
  have hf_sm : StronglyMeasurable f := hpath₀_sm.piecewise hS_meas stronglyMeasurable_const
  have hf_norm : ∀ s : ℝ, ‖f s‖ ≤ M := by
    intro s
    by_cases hs : s ∈ S_good
    · have hmem : MemLp (F8U.slice z₁ s) 2 μc :=
        ⟨(F8L.sliceMeas hz₁_sm s).aestronglyMeasurable,
          lt_of_le_of_lt hs ENNReal.ofReal_lt_top⟩
      have hfeq : f s = hmem.toLp (F8U.slice z₁ s) := by
        simp only [f, piecewise_eq_of_mem _ _ _ hs, path₀]
        exact UnforcedLeray.BochnerTime.toPathLq_of_memLp hmem
      rw [hfeq, Lp.norm_toLp]
      exact ENNReal.toReal_le_of_le_ofReal hM hs
    · change ‖S_good.piecewise path₀ 0 s‖ ≤ M
      rw [piecewise_eq_of_notMem _ _ _ hs, Pi.zero_apply, norm_zero]
      exact hM
  have hf_loc : LocallyIntegrable f volume :=
    (memLp_top_of_bound hf_sm.aestronglyMeasurable M (Eventually.of_forall hf_norm)).locallyIntegrable
      le_top
  have hvit :=
    (IsUnifLocDoublingMeasure.vitaliFamily (volume : Measure ℝ) 1).ae_tendsto_average_norm_sub hf_loc
  have hae_S : ∀ᵐ s ∂(volume : Measure ℝ), 0 < s → s ∈ S_good := hbnd
  filter_upwards [hvit, hae_S] with σ hσ_vit hσ_S hσ_pos
  have hσ_mem : σ ∈ S_good := hσ_S hσ_pos
  have hmem_σ : MemLp (F8U.slice z₁ σ) 2 μc :=
    ⟨(F8L.sliceMeas hz₁_sm σ).aestronglyMeasurable,
      lt_of_le_of_lt hσ_mem ENNReal.ofReal_lt_top⟩
  have hf_σ : f σ = hmem_σ.toLp (F8U.slice z₁ σ) := by
    simp only [f, piecewise_eq_of_mem _ _ _ hσ_mem, path₀]
    exact UnforcedLeray.BochnerTime.toPathLq_of_memLp hmem_σ
  have hshift : Tendsto (fun h : ℝ => σ + h) (𝓝[>] 0) (𝓝[>] σ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc0 : Continuous (fun h : ℝ => σ + h) := continuous_const.add continuous_id
      have ht0 := hc0.tendsto 0
      rw [add_zero] at ht0
      exact ht0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with h hh
      simp only [mem_Ioi] at hh ⊢
      linarith
  have havg : Tendsto (fun h : ℝ => ⨍ t in Icc σ (σ + h), ‖f t - f σ‖) (𝓝[>] 0) (𝓝 0) :=
    hσ_vit.comp ((Real.tendsto_Icc_vitaliFamily_right σ).comp hshift)
  have hlin : Tendsto (fun h : ℝ => (2 * M) * (⨍ t in Icc σ (σ + h), ‖f t - f σ‖))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using havg.const_mul (2 * M)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlin ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with h hh
    have hh0 : 0 < h := hh
    exact mul_nonneg (inv_nonneg.2 hh0.le)
      (integral_nonneg fun _ => sq_nonneg _)
  · filter_upwards [self_mem_nhdsWithin] with h hh
    have hh0 : 0 < h := hh
    have hvol : volume.real (Icc σ (σ + h)) = h := by
      simp [Measure.real, Real.volume_Icc, hh0.le]
    have havg_eq : (2 * M) * (⨍ t in Icc σ (σ + h), ‖f t - f σ‖) =
        h⁻¹ * ∫ t in Ioc σ (σ + h), (2 * M) * ‖f t - f σ‖ := by
      rw [setAverage_eq, hvol, integral_Icc_eq_integral_Ioc, smul_eq_mul]
      calc (2 * M) * (h⁻¹ * ∫ t in Ioc σ (σ + h), ‖f t - f σ‖)
          = h⁻¹ * ((2 * M) * ∫ t in Ioc σ (σ + h), ‖f t - f σ‖) := by ring
        _ = h⁻¹ * ∫ t in Ioc σ (σ + h), (2 * M) * ‖f t - f σ‖ := by rw [integral_const_mul]
    rw [havg_eq]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hh0.le)
    have hint_f : IntegrableOn (fun t => (2 * M) * ‖f t - f σ‖) (Ioc σ (σ + h)) volume :=
      (((hf_loc.integrableOn_isCompact isCompact_Icc).mono_set Ioc_subset_Icc_self).sub
        (integrableOn_const (by simp [Real.volume_Ioc]))).norm.const_mul (2 * M)
    have hae_Ioc : (fun t => (F8U.cellL2 c (fun y => z₁ (t, y) - z₁ (σ, y))).toReal ^ 2)
        =ᵐ[volume.restrict (Ioc σ (σ + h))] (fun t => ‖f t - f σ‖ ^ 2) := by
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
      filter_upwards [hae_S] with t ht ht_mem
      have ht_pos : 0 < t := lt_trans hσ_pos ht_mem.1
      have ht_S : t ∈ S_good := ht ht_pos
      have hmem_t : MemLp (F8U.slice z₁ t) 2 μc :=
        ⟨(F8L.sliceMeas hz₁_sm t).aestronglyMeasurable,
          lt_of_le_of_lt ht_S ENNReal.ofReal_lt_top⟩
      have hf_t : f t = hmem_t.toLp (F8U.slice z₁ t) := by
        simp only [f, piecewise_eq_of_mem _ _ _ ht_S, path₀]
        exact UnforcedLeray.BochnerTime.toPathLq_of_memLp hmem_t
      change (F8U.cellL2 c (fun y => z₁ (t, y) - z₁ (σ, y))).toReal ^ 2 = ‖f t - f σ‖ ^ 2
      rw [hf_t, hf_σ, ← MemLp.toLp_sub hmem_t hmem_σ, Lp.norm_toLp]
      rfl
    have hint_sq : IntegrableOn
        (fun t => (F8U.cellL2 c (fun y => z₁ (t, y) - z₁ (σ, y))).toReal ^ 2)
        (Ioc σ (σ + h)) volume := by
      have hint_norm_sq : IntegrableOn (fun t => ‖f t - f σ‖ ^ 2) (Ioc σ (σ + h)) volume := by
        refine Integrable.mono' hint_f
          (((hf_sm.sub stronglyMeasurable_const).norm.pow 2).aestronglyMeasurable) ?_
        filter_upwards with t
        rw [Real.norm_of_nonneg (sq_nonneg _), sq]
        have hle2 : ‖f t - f σ‖ ≤ 2 * M :=
          (norm_sub_le _ _).trans (by linarith [hf_norm t, hf_norm σ])
        exact mul_le_mul_of_nonneg_right hle2 (norm_nonneg _)
      exact hint_norm_sq.congr_fun_ae hae_Ioc.symm
    refine integral_mono_ae hint_sq hint_f ?_
    filter_upwards [hae_Ioc] with t ht
    change (F8U.cellL2 c (fun y => z₁ (t, y) - z₁ (σ, y))).toReal ^ 2 ≤ (2 * M) * ‖f t - f σ‖
    rw [ht, sq]
    have hle2 : ‖f t - f σ‖ ≤ 2 * M :=
      (norm_sub_le _ _).trans (by linarith [hf_norm t, hf_norm σ])
    exact mul_le_mul_of_nonneg_right hle2 (norm_nonneg _)

end UnforcedLeray.Short.IIb.F8Duh
