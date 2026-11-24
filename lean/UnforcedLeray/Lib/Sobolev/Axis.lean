import UnforcedLeray.Lib.Sobolev.Jacobian
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The removable axis (INF11 target S1, `HasWeakDeriv.of_bdd_off_axis`)

Scoping note `INF11-INF14-Sobolev.md` §5.1 (S1) and §2 (blueprint unit B0200, tex 3028–3051:
`W^{1,p}(ℝ³)` membership of a field that is smooth off the axis, bounded, with integrable
derivatives; "weak derivatives across the axis, a codimension-2 null set"); scoping README §4
(INF13 BP6: "Axis removability … Cutoff error ≲ δ^{1-2/p}‖f‖").

**Statement.** Let `f : ℝ³ → F` be `C¹` off the axis `{x₀ = x₁ = 0}`, bounded on compact sets,
and let `x ↦ Df(x) v` be locally integrable. Then `Df(·) v` is the weak derivative of `f` in
the direction `v` on the whole space.

**Proof.** Cut the axis out with `χ_m(x) = η((m+1)² (x₀² + x₁²))`, `η = 0` on `(-∞, 1]` and
`= 1` on `[2, ∞)`. For a test `φ`, the classical integration by parts holds for `φ χ_m`, which
is supported off the axis. As `m → ∞`, the two terms with `χ_m` converge by dominated
convergence (the axis is null), and the commutator term is bounded by
`sup|φ| · sup_K ‖f‖ · |∇χ_m| · vol{|x₀|, |x₁| ≤ 2/(m+1), |x₂| ≤ R} ≲ (m+1) · (m+1)⁻²`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Sob

/-- The complement of the axis `{x₀ = x₁ = 0}` of `ℝ³`. -/
def offAxis : Set Space := {x | x 0 ≠ 0 ∨ x 1 ≠ 0}

theorem isOpen_offAxis : IsOpen offAxis :=
  (isOpen_ne_fun (contDiff_coord (n := 3) 0).continuous continuous_const).union
    (isOpen_ne_fun (contDiff_coord (n := 3) 1).continuous continuous_const)

/-- The axis is Lebesgue-null. -/
theorem ae_offAxis : ∀ᵐ x ∂(volume : Measure Space), x ∈ offAxis := by
  let L : Space →ₗ[ℝ] ℝ := (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).toLinearMap
  have hne : LinearMap.ker L ≠ ⊤ := by
    intro h
    have : e (0 : Fin 3) ∈ LinearMap.ker L := h ▸ Submodule.mem_top
    rw [LinearMap.mem_ker] at this
    simp [L, e] at this
  have h0 := Measure.addHaar_submodule volume (LinearMap.ker L) hne
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) h0
  simp only [offAxis, mem_setOf_eq, not_or, not_not] at hx
  show x ∈ LinearMap.ker L
  rw [LinearMap.mem_ker]
  simp [L, hx.1]

/-! ### The cutoff -/

/-- `η = 0` on `(-∞, 1]`, `η = 1` on `[2, ∞)`. -/
def axisEta (t : ℝ) : ℝ := Real.smoothTransition (t - 1)

theorem contDiff_axisEta : ContDiff ℝ ∞ axisEta :=
  (Real.smoothTransition.contDiff (n := ⊤)).comp (contDiff_id.sub contDiff_const)

theorem axisEta_eq_zero {t : ℝ} (ht : t ≤ 1) : axisEta t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem axisEta_eq_one {t : ℝ} (ht : 2 ≤ t) : axisEta t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem axisEta_nonneg (t : ℝ) : 0 ≤ axisEta t := Real.smoothTransition.nonneg _

theorem axisEta_le_one (t : ℝ) : axisEta t ≤ 1 := Real.smoothTransition.le_one _

theorem deriv_axisEta_eq_zero {t : ℝ} (ht : t < 1 ∨ 2 < t) : deriv axisEta t = 0 := by
  rcases ht with ht | ht
  · have : axisEta =ᶠ[𝓝 t] fun _ => (0 : ℝ) :=
      Filter.eventually_of_mem (Iio_mem_nhds ht) fun s hs => axisEta_eq_zero (le_of_lt hs)
    rw [this.deriv_eq, deriv_const]
  · have : axisEta =ᶠ[𝓝 t] fun _ => (1 : ℝ) :=
      Filter.eventually_of_mem (Ioi_mem_nhds ht) fun s hs => axisEta_eq_one (le_of_lt hs)
    rw [this.deriv_eq, deriv_const]

theorem exists_bound_deriv_axisEta : ∃ B, 0 ≤ B ∧ ∀ t, |deriv axisEta t| ≤ B := by
  have hc : Continuous (deriv axisEta) := contDiff_axisEta.continuous_deriv (by simp)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (1 : ℝ) 2)
    hc.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht : t ∈ Icc (1 : ℝ) 2
  · exact (by simpa [Real.norm_eq_abs] using hB t ht : |deriv axisEta t| ≤ B).trans
      (le_max_left _ _)
  · rw [deriv_axisEta_eq_zero (by
      simp only [mem_Icc, not_and_or, not_le] at ht; exact ht), abs_zero]
    exact le_max_right _ _

/-- `q x = x₀² + x₁²`. -/
def axisQ (x : Space) : ℝ := x 0 * x 0 + x 1 * x 1

theorem hasFDerivAt_axisQ (x : Space) :
    HasFDerivAt axisQ (x 0 • (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ) +
      x 0 • (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ) +
      (x 1 • (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ) +
      x 1 • (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ))) x := by
  have h0 := (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt (x := x)
  have h1 := (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt (x := x)
  exact (h0.mul h0).add (h1.mul h1)

theorem contDiff_axisQ : ContDiff ℝ ∞ axisQ :=
  ((contDiff_coord 0).mul (contDiff_coord 0)).add ((contDiff_coord 1).mul (contDiff_coord 1))

theorem fderiv_axisQ_apply (x v : Space) :
    fderiv ℝ axisQ x v = 2 * x 0 * v 0 + 2 * x 1 * v 1 := by
  rw [(hasFDerivAt_axisQ x).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  simp
  ring

/-- The cutoff `χ_m(x) = η((m+1)² q(x))`. -/
def axisCut (m : ℕ) (x : Space) : ℝ := axisEta (((m : ℝ) + 1) ^ 2 * axisQ x)

theorem contDiff_axisCut (m : ℕ) : ContDiff ℝ ∞ (axisCut m) :=
  contDiff_axisEta.comp (contDiff_const.mul contDiff_axisQ)

theorem fderiv_axisCut_apply (m : ℕ) (x v : Space) :
    fderiv ℝ (axisCut m) x v = deriv axisEta (((m : ℝ) + 1) ^ 2 * axisQ x) *
      (((m : ℝ) + 1) ^ 2 * (2 * x 0 * v 0 + 2 * x 1 * v 1)) := by
  have hq := ((hasFDerivAt_axisQ x).const_mul (((m : ℝ) + 1) ^ 2))
  have hη : HasDerivAt axisEta (deriv axisEta (((m : ℝ) + 1) ^ 2 * axisQ x))
      (((m : ℝ) + 1) ^ 2 * axisQ x) :=
    ((contDiff_axisEta.differentiable (by simp)) _).hasDerivAt
  have := hη.comp_hasFDerivAt x hq
  rw [show axisCut m = axisEta ∘ fun y => ((m : ℝ) + 1) ^ 2 * axisQ y from rfl, this.fderiv]
  rw [← fderiv_axisQ_apply x v, (hasFDerivAt_axisQ x).fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem axisCut_nonneg (m : ℕ) (x : Space) : 0 ≤ axisCut m x := axisEta_nonneg _

theorem axisCut_le_one (m : ℕ) (x : Space) : axisCut m x ≤ 1 := axisEta_le_one _

theorem axisQ_nonneg (x : Space) : 0 ≤ axisQ x := by
  unfold axisQ; nlinarith [mul_self_nonneg (x 0), mul_self_nonneg (x 1)]

theorem tsupport_axisCut_subset (m : ℕ) : tsupport (axisCut m) ⊆ offAxis := by
  have hcl : IsClosed {x : Space | 1 ≤ ((m : ℝ) + 1) ^ 2 * axisQ x} :=
    isClosed_le continuous_const (continuous_const.mul contDiff_axisQ.continuous)
  refine (closure_minimal (fun x hx => ?_) hcl).trans fun x hx => ?_
  · by_contra h
    exact hx (axisEta_eq_zero (le_of_lt (not_le.mp h)))
  · by_contra h
    simp only [offAxis, mem_setOf_eq, not_or, not_not] at h
    have : axisQ x = 0 := by simp [axisQ, h.1, h.2]
    have hx' : 1 ≤ ((m : ℝ) + 1) ^ 2 * axisQ x := hx
    rw [this, mul_zero] at hx'
    linarith

/-- Off the axis, `χ_m = 1` eventually. -/
theorem eventually_axisCut_eq_one {x : Space} (hx : x ∈ offAxis) :
    ∀ᶠ m : ℕ in atTop, axisCut m x = 1 := by
  have hq : 0 < axisQ x := by
    rcases hx with h | h
    · unfold axisQ; nlinarith [mul_self_pos.mpr h, mul_self_nonneg (x 1)]
    · unfold axisQ; nlinarith [mul_self_pos.mpr h, mul_self_nonneg (x 0)]
  refine eventually_atTop.2 ⟨⌈2 / axisQ x⌉₊, fun m hm => axisEta_eq_one ?_⟩
  have h1 : 2 / axisQ x ≤ m := (Nat.le_ceil _).trans (by exact_mod_cast hm)
  have h2 : 2 ≤ (m : ℝ) * axisQ x := by
    rwa [div_le_iff₀ hq] at h1
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  nlinarith

/-- Where `∇χ_m ≠ 0`, the point is within `2/(m+1)` of the axis and `|∂_v χ_m| ≲ m + 1`. -/
theorem axisCut_deriv_bound {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ t, |deriv axisEta t| ≤ B) (m : ℕ)
    (x v : Space) (hx : fderiv ℝ (axisCut m) x v ≠ 0) :
    |x 0| ≤ 2 / ((m : ℝ) + 1) ∧ |x 1| ≤ 2 / ((m : ℝ) + 1) ∧
      |fderiv ℝ (axisCut m) x v| ≤ 4 * B * (|v 0| + |v 1|) * ((m : ℝ) + 1) := by
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  rw [fderiv_axisCut_apply] at hx ⊢
  have hd : deriv axisEta (((m : ℝ) + 1) ^ 2 * axisQ x) ≠ 0 := left_ne_zero_of_mul hx
  have hrange : ((m : ℝ) + 1) ^ 2 * axisQ x ≤ 2 := by
    by_contra h
    exact hd (deriv_axisEta_eq_zero (Or.inr (not_le.mp h)))
  have hsq : ∀ i : Fin 3, i = 0 ∨ i = 1 → ((m + 1 : ℝ) * |x i|) ^ 2 ≤ 2 := by
    rintro i (rfl | rfl)
    · rw [mul_pow, sq_abs]; unfold axisQ at hrange
      nlinarith [mul_self_nonneg (x 1), sq_nonneg ((m : ℝ) + 1)]
    · rw [mul_pow, sq_abs]; unfold axisQ at hrange
      nlinarith [mul_self_nonneg (x 0), sq_nonneg ((m : ℝ) + 1)]
  have hlin : ∀ i : Fin 3, i = 0 ∨ i = 1 → (m + 1 : ℝ) * |x i| ≤ 2 := by
    intro i hi
    have := hsq i hi
    nlinarith [abs_nonneg (x i), mul_nonneg hm.le (abs_nonneg (x i))]
  have hx0 : |x 0| ≤ 2 / ((m : ℝ) + 1) := by
    rw [le_div_iff₀ hm]; linarith [hlin 0 (Or.inl rfl)]
  have hx1 : |x 1| ≤ 2 / ((m : ℝ) + 1) := by
    rw [le_div_iff₀ hm]; linarith [hlin 1 (Or.inr rfl)]
  refine ⟨hx0, hx1, ?_⟩
  rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < ((m : ℝ) + 1) ^ 2)]
  have hlin' : |2 * x 0 * v 0 + 2 * x 1 * v 1| * ((m : ℝ) + 1) ≤ 4 * (|v 0| + |v 1|) := by
    have e1 : |2 * x 0 * v 0 + 2 * x 1 * v 1| ≤ 2 * |x 0| * |v 0| + 2 * |x 1| * |v 1| := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_two]
    have h0 := hlin 0 (Or.inl rfl)
    have h1 := hlin 1 (Or.inr rfl)
    nlinarith [abs_nonneg (v 0), abs_nonneg (v 1), mul_nonneg (abs_nonneg (x 0)) hm.le]
  calc |deriv axisEta (((m : ℝ) + 1) ^ 2 * axisQ x)| *
        (((m : ℝ) + 1) ^ 2 * |2 * x 0 * v 0 + 2 * x 1 * v 1|)
      ≤ B * (((m : ℝ) + 1) * (|2 * x 0 * v 0 + 2 * x 1 * v 1| * ((m : ℝ) + 1))) := by
        refine mul_le_mul (hB _) (le_of_eq (by ring)) (by positivity) hB0
    _ ≤ B * (((m : ℝ) + 1) * (4 * (|v 0| + |v 1|))) := by
        gcongr
    _ = 4 * B * (|v 0| + |v 1|) * ((m : ℝ) + 1) := by ring

/-- The box `|x₀|, |x₁| ≤ a`, `|x₂| ≤ R` as a preimage of an interval of `Fin 3 → ℝ`. -/
def axisBox (a R : ℝ) : Set Space :=
  (WithLp.ofLp : Space → (Fin 3 → ℝ)) ⁻¹' Icc (-![a, a, R]) ![a, a, R]

theorem measurableSet_axisBox (a R : ℝ) : MeasurableSet (axisBox a R) :=
  measurableSet_Icc.preimage (WithLp.measurable_ofLp 2 _)

theorem volume_axisBox {a R : ℝ} (ha : 0 ≤ a) (hR : 0 ≤ R) :
    (volume : Measure Space).real (axisBox a R) = (2 * a) * (2 * a) * (2 * R) := by
  have h := (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
    (measurableSet_Icc (a := -![a, a, R]) (b := ![a, a, R])).nullMeasurableSet
  rw [measureReal_def, axisBox, h, Real.volume_Icc_pi, Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Pi.neg_apply,
    Matrix.head_cons, Matrix.tail_cons]
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith),
    ENNReal.toReal_ofReal (by linarith)]
  ring

theorem volume_axisBox_ne_top (a R : ℝ) : (volume : Measure Space) (axisBox a R) ≠ ⊤ := by
  rw [axisBox, (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
    (measurableSet_Icc (a := -![a, a, R]) (b := ![a, a, R])).nullMeasurableSet,
    Real.volume_Icc_pi]
  exact ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top

theorem mem_axisBox {a R : ℝ} {x : Space} (h0 : |x 0| ≤ a) (h1 : |x 1| ≤ a) (h2 : |x 2| ≤ R) :
    x ∈ axisBox a R := by
  rw [axisBox, mem_preimage, mem_Icc]
  constructor
  · intro i; fin_cases i <;> simp <;> linarith [neg_abs_le (x 0), neg_abs_le (x 1),
      neg_abs_le (x 2)]
  · intro i; fin_cases i <;> simp <;> linarith [le_abs_self (x 0), le_abs_self (x 1),
      le_abs_self (x 2)]

/-! ### The removable axis -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **Removable axis** (S1, B0200): a field that is `C¹` off the axis `{x₀ = x₁ = 0}` of `ℝ³`,
bounded on compact sets, with locally integrable classical derivative `Df(·) v`, has
`Df(·) v` as its weak derivative in the direction `v` on the whole space. -/
theorem HasWeakDeriv.of_bdd_off_axis {f : Space → F} (v : Space)
    (hf : ContDiffOn ℝ 1 f offAxis)
    (hb : ∀ K : Set Space, IsCompact K → ∃ M, ∀ x ∈ K, ‖f x‖ ≤ M)
    (hg : LocallyIntegrable (fun x => fderiv ℝ f x v) volume) :
    HasWeakDeriv (wholeSpace 3) [v] f (fun x => fderiv ℝ f x v) := by
  have hU := isOpen_offAxis
  have hdiff : ∀ x ∈ offAxis, DifferentiableAt ℝ f x := fun x hx =>
    (hf.differentiableOn one_ne_zero x hx).differentiableAt (hU.mem_nhds hx)
  have hmeas : AEStronglyMeasurable f volume := by
    have h1 : AEStronglyMeasurable f (volume.restrict offAxis) :=
      hf.continuousOn.aestronglyMeasurable hU.measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem ae_offAxis] at h1
  have hfl : LocallyIntegrable f volume := by
    rw [locallyIntegrable_iff]
    intro K hK
    obtain ⟨M, hM⟩ := hb K hK
    exact IntegrableOn.of_bound hK.measure_lt_top hmeas.restrict M
      ((ae_restrict_iff' hK.measurableSet).mpr (Eventually.of_forall fun x hx => hM x hx))
  refine HasWeakDeriv.of_locallyIntegrable hfl hg fun φ hφ hφc => ?_
  simp only [iterDirDeriv_singleton, List.length_singleton, pow_one, neg_smul, one_smul]
  have hφA : (wholeSpace 3).Adm φ := ⟨hφ, hφc⟩
  have hcut := contDiff_axisCut
  -- the three families
  set A : ℕ → F := fun m => ∫ x, (fderiv ℝ φ x v * axisCut m x) • f x with hA_def
  set Bm : ℕ → F := fun m => ∫ x, (φ x * fderiv ℝ (axisCut m) x v) • f x with hB_def
  set C : ℕ → F := fun m => ∫ x, (φ x * axisCut m x) • fderiv ℝ f x v with hC_def
  -- integration by parts away from the axis
  have hid : ∀ m, C m = -(A m + Bm m) := by
    intro m
    have hψA : (wholeSpace 3).Adm (fun x => φ x * axisCut m x) :=
      ⟨hφ.mul (hcut m), hφc.mul_right⟩
    have hsupp : tsupport (fun x => φ x * axisCut m x) ⊆ offAxis :=
      (tsupport_mul_subset_right (f := φ) (g := axisCut m)).trans (tsupport_axisCut_subset m)
    have hibp := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
      (μ := volume) (f := fun x => φ x * axisCut m x) (g := f) (v := v)
      (integrable_smul_of_adm ((wholeSpace 3).deriv_mem hψA v) hfl)
      (integrable_smul_of_adm hψA hg) (integrable_smul_of_adm hψA hfl)
      (fun x _ => ((hφ.mul (hcut m)).differentiable (by simp)) x)
      (fun x hx => hdiff x (hsupp hx))
    have hprod : ∀ x, fderiv ℝ (fun y => φ y * axisCut m y) x v =
        fderiv ℝ φ x v * axisCut m x + φ x * fderiv ℝ (axisCut m) x v := by
      intro x
      have : fderiv ℝ (fun y => φ y * axisCut m y) x =
          φ x • fderiv ℝ (axisCut m) x + axisCut m x • fderiv ℝ φ x :=
        fderiv_mul ((hφ.differentiable (by simp)) x) (((hcut m).differentiable (by simp)) x)
      rw [this]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    have i1 : Integrable (fun x => (fderiv ℝ φ x v * axisCut m x) • f x) volume :=
      integrable_smul_of_adm (φ := fun x => fderiv ℝ φ x v * axisCut m x)
        ⟨(contDiff_dirDeriv hφ v).mul (hcut m), (hφc.fderiv_apply ℝ v).mul_right⟩ hfl
    have i2 : Integrable (fun x => (φ x * fderiv ℝ (axisCut m) x v) • f x) volume :=
      integrable_smul_of_adm (φ := fun x => φ x * fderiv ℝ (axisCut m) x v)
        ⟨hφ.mul (contDiff_dirDeriv (hcut m) v), hφc.mul_right⟩ hfl
    simp only [hC_def, hA_def, hB_def]
    rw [hibp, ← integral_add i1 i2]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hprod, add_smul]
  -- the two dominated limits
  have hlimA : Tendsto A atTop (𝓝 (∫ x, fderiv ℝ φ x v • f x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖fderiv ℝ φ x v • f x‖)
      (fun m => (((contDiff_dirDeriv hφ v).mul (hcut m)).continuous.aestronglyMeasurable).smul
        hmeas)
      (integrable_smul_of_adm ((wholeSpace 3).deriv_mem hφA v) hfl).norm
      (fun m => Eventually.of_forall fun x => ?_) ?_
    · rw [norm_smul, norm_smul, norm_mul]
      gcongr
      rw [Real.norm_of_nonneg (axisCut_nonneg m x)]
      exact mul_le_of_le_one_right (norm_nonneg _) (axisCut_le_one m x)
    · filter_upwards [ae_offAxis] with x hx
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_axisCut_eq_one hx] with m hm
      rw [hm, mul_one]
  have hlimC : Tendsto C atTop (𝓝 (∫ x, φ x • fderiv ℝ f x v)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖φ x • fderiv ℝ f x v‖)
      (fun m => ((hφ.mul (hcut m)).continuous.aestronglyMeasurable).smul
        hg.aestronglyMeasurable)
      (integrable_smul_of_adm hφA hg).norm (fun m => Eventually.of_forall fun x => ?_) ?_
    · rw [norm_smul, norm_smul, norm_mul]
      gcongr
      rw [Real.norm_of_nonneg (axisCut_nonneg m x)]
      exact mul_le_of_le_one_right (norm_nonneg _) (axisCut_le_one m x)
    · filter_upwards [ae_offAxis] with x hx
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_axisCut_eq_one hx] with m hm
      rw [hm, mul_one]
  -- the commutator term tends to zero
  have hlimB : Tendsto Bm atTop (𝓝 0) := by
    obtain ⟨R₀, hR₀⟩ := (isBounded_iff_subset_closedBall (0 : Space)).mp
      hφc.isCompact.isBounded
    set R := max R₀ 0 with hR
    have hR0 : 0 ≤ R := le_max_right _ _
    obtain ⟨Mφ, hMφ⟩ := hφ.continuous.bounded_above_of_compact_support hφc
    obtain ⟨Mf, hMf⟩ := hb _ hφc.isCompact
    obtain ⟨B, hB0, hB⟩ := exists_bound_deriv_axisEta
    set L := 4 * B * (|v 0| + |v 1|) with hL
    have hL0 : 0 ≤ L := by positivity
    set K := max Mφ 0 * L * max Mf 0 with hK
    have hK0 : 0 ≤ K := by positivity
    have hbound : ∀ m : ℕ, ‖Bm m‖ ≤ K * ((m : ℝ) + 1) *
        ((2 * (2 / ((m : ℝ) + 1))) * (2 * (2 / ((m : ℝ) + 1))) * (2 * R)) := by
      intro m
      have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      have ha : 0 ≤ 2 / ((m : ℝ) + 1) := by positivity
      have hpt : ∀ x, ‖(φ x * fderiv ℝ (axisCut m) x v) • f x‖ ≤
          (axisBox (2 / ((m : ℝ) + 1)) R).indicator (fun _ => K * ((m : ℝ) + 1)) x := by
        intro x
        by_cases hφx : φ x = 0
        · simp only [hφx, zero_mul, zero_smul, norm_zero]
          exact indicator_nonneg (fun _ _ => by positivity) _
        by_cases hdx : fderiv ℝ (axisCut m) x v = 0
        · simp only [hdx, mul_zero, zero_smul, norm_zero]
          exact indicator_nonneg (fun _ _ => by positivity) _
        have hxs : x ∈ tsupport φ := subset_tsupport _ (Function.mem_support.mpr hφx)
        obtain ⟨h0, h1, hd⟩ := axisCut_deriv_bound hB0 hB m x v hdx
        have h2 : |x 2| ≤ R := by
          have hx := hR₀ hxs
          rw [mem_closedBall, dist_zero_right] at hx
          have := PiLp.norm_apply_le x 2
          rw [Real.norm_eq_abs] at this
          linarith [le_max_left R₀ 0]
        rw [indicator_of_mem (mem_axisBox h0 h1 h2), norm_smul, norm_mul, Real.norm_eq_abs,
          Real.norm_eq_abs]
        have e1' : |φ x| ≤ Mφ := by simpa [Real.norm_eq_abs] using hMφ x
        have e1 : |φ x| ≤ max Mφ 0 := e1'.trans (le_max_left _ _)
        have e2 : ‖f x‖ ≤ max Mf 0 := (hMf x hxs).trans (le_max_left _ _)
        calc |φ x| * |fderiv ℝ (axisCut m) x v| * ‖f x‖
            ≤ max Mφ 0 * (L * ((m : ℝ) + 1)) * max Mf 0 := by
              gcongr <;> first
                | exact le_max_right _ _
                | simpa [hL, mul_assoc] using hd
                | assumption
          _ = K * ((m : ℝ) + 1) := by rw [hK]; ring
      have hint : Integrable ((axisBox (2 / ((m : ℝ) + 1)) R).indicator
          (fun _ => K * ((m : ℝ) + 1))) volume := by
        exact (integrable_indicator_iff (measurableSet_axisBox _ _)).mpr
          (integrableOn_const (volume_axisBox_ne_top _ _))
      calc ‖Bm m‖ ≤ ∫ x, (axisBox (2 / ((m : ℝ) + 1)) R).indicator
            (fun _ => K * ((m : ℝ) + 1)) x :=
            norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)
        _ = K * ((m : ℝ) + 1) * ((2 * (2 / ((m : ℝ) + 1))) * (2 * (2 / ((m : ℝ) + 1))) *
            (2 * R)) := by
            rw [integral_indicator_const _ (measurableSet_axisBox _ _), volume_axisBox ha hR0,
              smul_eq_mul]
            ring
    refine squeeze_zero_norm hbound ?_
    have h1 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (32 * K * R)
    rw [mul_zero] at h1
    refine h1.congr fun m => ?_
    have hm : (m : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  -- conclusion
  have hlim2 : Tendsto C atTop (𝓝 (-((∫ x, fderiv ℝ φ x v • f x) + 0))) := by
    have : C = fun m => -(A m + Bm m) := funext hid
    rw [this]
    exact (hlimA.add hlimB).neg
  have huniq := tendsto_nhds_unique hlimC hlim2
  rw [add_zero] at huniq
  rw [huniq, neg_neg]

end UnforcedLeray.Sob
