import UnforcedLeray.Lib.CylinderB.Liouville
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# CY12: the cylinder Leray projector `P₀` (bypass BP4)


(§5 Layer 2). Bypass BP4: `P₀` is the `L²(cell)` orthogonal projection onto the weakly
divergence-free periodic fields, identified by orthogonality, not by Fourier multipliers.

Manuscript: `paper/main.tex` lines 8004–8015 (B0486: `P₀` the ordinary 2D Leray projection on
`(b_r, b_z)` over `(ℝ/ℓℤ) × ℝ`), 4749–4770 (B0288: orthogonal on `L²`), 11826–11843 and
12688–12706 (B0811, B0852: `P₀` on `c`-periodic meridional fields, including the zero horizontal
mode in the decaying transverse gauge), 11955–11968 (B0819: `L²` contraction), 11970–11989
(B0820: `curl P₀ = curl`).

## Main declarations
* `L2v c = L²(cell; ℝ²)`; `gradT φ = (∂_q φ, ∂_η φ)`, `rotT φ = (∂_η φ, −∂_q φ)` and their
  classes `gradL`, `rotL` for periodic tests;
* `divFree c`: the fields `u` with `∫_cell u · ∇φ = 0` for every periodic test `φ` (a closed
  subspace), `P0 c = (divFree c).starProjection`;
* `P0_eq_of_orthogonal`, `gradL_mem_orthogonal`, `norm_P0_le`, `P0_idem`, `inner_P0_comm`
  (B0288, B0819);
* `rotL_mem_divFree`, `curl_P0`: `∫ P₀f · ∇^⊥φ = ∫ f · ∇^⊥φ` for every test, i.e.
  `curl P₀ f = curl f` weakly (B0820);
* `qAvg_P0`: the `q`-average of `P₀ f` is `(f̄₁, 0)` (B0852, decaying gauge).

Not built: the commutation with translations and weak derivatives (`P0_comm_translate`,
`P0_comm_weakPartial`, `norm_P0_H1_le`), the mode formula `qMode_P0`, and the periodization
identity `P0_periodize` (B0812, B0817).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Complex
open scoped ENNReal ContDiff Topology InnerProductSpace

namespace UnforcedLeray.Cyl

variable {c : ℝ}

/-- `L²(cell; ℝ²)` with the Euclidean norm on `ℝ²`. -/
abbrev L2v (c : ℝ) := Lp Vec2 2 (cellμ c)

/-- The vector `(a, b) ∈ ℝ²`. -/
abbrev vec (a b : ℝ) : Vec2 := WithLp.toLp 2 ![a, b]

@[simp] theorem vec_zero (a b : ℝ) : vec a b 0 = a := rfl
@[simp] theorem vec_one (a b : ℝ) : vec a b 1 = b := rfl

theorem inner_vec (x : Vec2) (a b : ℝ) : ⟪x, vec a b⟫_ℝ = x 0 * a + x 1 * b := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp [mul_comm]

/-- The gradient `(∂_q φ, ∂_η φ)`. -/
def gradT (φ : Plane → ℝ) (z : Plane) : Vec2 := vec (partialQ φ z) (partialEta φ z)

/-- The rotated gradient `∇^⊥ φ = (∂_η φ, −∂_q φ)`. -/
def rotT (φ : Plane → ℝ) (z : Plane) : Vec2 := vec (partialEta φ z) (-partialQ φ z)

/-- A continuous field vanishing for large `|η|` lies in every `Lᵖ(cell)`. -/
theorem memLp_of_vanishes {E : Type*} [NormedAddCommGroup E] {F : Plane → E} (hF : Continuous F)
    {R : ℝ} (hv : VanishesOutside R F) (p : ℝ≥0∞) : MemLp F p (cellμ c) := by
  set K : Set Plane := Icc (-c / 2) (c / 2) ×ˢ Icc (-R) R
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hind : F =ᵐ[cellμ c] K.indicator F := by
    refine ae_restrict_of_forall_mem (measurableSet_cell c) fun z hz => ?_
    by_cases hzK : z ∈ K
    · rw [Set.indicator_of_mem hzK]
    · rw [Set.indicator_of_notMem hzK]
      apply hv
      rw [mem_cell] at hz
      by_contra hle
      push Not at hle
      exact hzK ⟨⟨hz.1, hz.2.le⟩, abs_le.1 hle⟩
  refine MemLp.ae_eq hind.symm ?_
  rw [memLp_indicator_iff_restrict hK.measurableSet]
  have hfin : (cellμ c).restrict K univ < ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_lt (Measure.restrict_le_self K) hK.measure_lt_top
  have : IsFiniteMeasure ((cellμ c).restrict K) := ⟨hfin⟩
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
  exact MemLp.of_bound hF.aestronglyMeasurable.restrict M
    (ae_restrict_of_forall_mem hK.measurableSet hM)

theorem continuous_gradT {φ : Plane → ℝ} (hφ : Sob.IsCylTest c φ) : Continuous (gradT φ) := by
  have h1 := (isCylTest_partialQ hφ).continuous
  have h2 := (isCylTest_partialEta hφ).continuous
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => by
    fin_cases i
    · exact h1
    · exact h2)

theorem continuous_rotT {φ : Plane → ℝ} (hφ : Sob.IsCylTest c φ) : Continuous (rotT φ) := by
  have h1 := (isCylTest_partialQ hφ).continuous
  have h2 := (isCylTest_partialEta hφ).continuous
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => by
    fin_cases i
    · exact h2
    · exact h1.neg)

theorem vanishes_gradT {φ : Plane → ℝ} (hφ : Sob.IsCylTest c φ) :
    ∃ R, VanishesOutside R (gradT φ) := by
  obtain ⟨R, hR⟩ := hφ.vanishes
  refine ⟨R, fun z hz => ?_⟩
  simp only [gradT, hR.partialQ z hz, hR.partialEta z hz]
  ext i; fin_cases i <;> rfl

theorem vanishes_rotT {φ : Plane → ℝ} (hφ : Sob.IsCylTest c φ) :
    ∃ R, VanishesOutside R (rotT φ) := by
  obtain ⟨R, hR⟩ := hφ.vanishes
  refine ⟨R, fun z hz => ?_⟩
  simp only [rotT, hR.partialQ z hz, hR.partialEta z hz, neg_zero]
  ext i; fin_cases i <;> rfl

theorem memLp_gradT {φ : Plane → ℝ} (hφ : Sob.IsCylTest c φ) : MemLp (gradT φ) 2 (cellμ c) := by
  obtain ⟨R, hR⟩ := vanishes_gradT hφ
  exact memLp_of_vanishes (continuous_gradT hφ) hR 2

theorem memLp_rotT {φ : Plane → ℝ} (hφ : Sob.IsCylTest c φ) : MemLp (rotT φ) 2 (cellμ c) := by
  obtain ⟨R, hR⟩ := vanishes_rotT hφ
  exact memLp_of_vanishes (continuous_rotT hφ) hR 2

/-- The class of `∇φ` in `L²(cell; ℝ²)`. -/
def gradL {φ : Plane → ℝ} (hφ : Sob.IsCylTest c φ) : L2v c := (memLp_gradT hφ).toLp _

/-- The class of `∇^⊥φ` in `L²(cell; ℝ²)`. -/
def rotL {φ : Plane → ℝ} (hφ : Sob.IsCylTest c φ) : L2v c := (memLp_rotT hφ).toLp _

/-- **The weakly divergence-free periodic fields** (BP4):
`{u ∈ L²(cell; ℝ²) : ∫_cell u · ∇φ = 0 for every periodic test φ}`. -/
def divFree (c : ℝ) : Submodule ℝ (L2v c) :=
  ⨅ φ : {φ : Plane → ℝ // Sob.IsCylTest c φ},
    LinearMap.ker ((innerSL ℝ (gradL φ.2) : L2v c →L[ℝ] ℝ) : L2v c →ₗ[ℝ] ℝ)

theorem mem_divFree {u : L2v c} :
    u ∈ divFree c ↔ ∀ (φ : Plane → ℝ) (hφ : Sob.IsCylTest c φ), ⟪gradL hφ, u⟫_ℝ = 0 := by
  simp only [divFree, Submodule.mem_iInf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    innerSL_apply_apply, Subtype.forall]

theorem isClosed_divFree (c : ℝ) : IsClosed (divFree c : Set (L2v c)) := by
  have : (divFree c : Set (L2v c)) =
      ⋂ p : {φ : Plane → ℝ // Sob.IsCylTest c φ}, {u | ⟪gradL p.2, u⟫_ℝ = 0} := by
    ext u
    simp only [SetLike.mem_coe, mem_divFree, mem_iInter, mem_setOf_eq, Subtype.forall]
  rw [this]
  exact isClosed_iInter fun p => isClosed_eq (continuous_const.inner continuous_id)
    continuous_const

instance completeSpace_divFree (c : ℝ) : CompleteSpace (divFree c) :=
  (isClosed_divFree c).completeSpace_coe

instance hasOrthogonalProjection_divFree (c : ℝ) : (divFree c).HasOrthogonalProjection :=
  Submodule.HasOrthogonalProjection.ofCompleteSpace _

/-- **The cylinder Leray projector** `P₀` (BP4; B0486, B0288): the orthogonal projection of
`L²(cell; ℝ²)` onto the weakly divergence-free periodic fields. -/
def P0 (c : ℝ) : L2v c →L[ℝ] L2v c := (divFree c).starProjection

/-- `P₀` is characterized by orthogonality (BP4, template `projection_eq_of_orthogonal`). -/
theorem P0_eq_of_orthogonal {f g : L2v c} (hg : g ∈ divFree c) (h : f - g ∈ (divFree c)ᗮ) :
    P0 c f = g :=
  Submodule.eq_starProjection_of_mem_of_inner_eq_zero hg fun w hw => by
    rw [real_inner_comm]; exact h w hw

theorem P0_mem (f : L2v c) : P0 c f ∈ divFree c := Submodule.starProjection_apply_mem _ f

theorem sub_P0_mem_orthogonal (f : L2v c) : f - P0 c f ∈ (divFree c)ᗮ :=
  Submodule.sub_starProjection_mem_orthogonal f

/-- Gradients of tests are orthogonal to the divergence-free fields. -/
theorem gradL_mem_orthogonal {φ : Plane → ℝ} (hφ : Sob.IsCylTest c φ) :
    gradL hφ ∈ (divFree c)ᗮ := fun u hu => by
  rw [real_inner_comm]; exact mem_divFree.1 hu φ hφ

/-- `‖P₀‖ ≤ 1` (B0819: the `L²` contraction). -/
theorem norm_P0_le : ‖P0 c‖ ≤ 1 := Submodule.starProjection_norm_le _

theorem P0_eq_self {g : L2v c} (hg : g ∈ divFree c) : P0 c g = g :=
  (Submodule.starProjection_eq_self_iff).2 hg

theorem P0_idem (f : L2v c) : P0 c (P0 c f) = P0 c f := P0_eq_self (P0_mem f)

/-- `P₀` is self-adjoint (B0291: the projector disappears in pairings with divergence-free
fields). -/
theorem inner_P0_comm (f g : L2v c) : ⟪P0 c f, g⟫_ℝ = ⟪f, P0 c g⟫_ℝ :=
  Submodule.inner_starProjection_left_eq_right _ f g

/-! ### `P₀` preserves the weak curl -/

theorem inner_toLp_left {F : Plane → Vec2} (hF : MemLp F 2 (cellμ c)) (g : L2v c) :
    ⟪hF.toLp F, g⟫_ℝ = ∫ z in cell c, ⟪F z, (g : Plane → Vec2) z⟫_ℝ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hF.coeFn_toLp] with z h1
  rw [h1]

theorem inner_toLp_eq {F G : Plane → Vec2} (hF : MemLp F 2 (cellμ c)) (hG : MemLp G 2 (cellμ c)) :
    ⟪hF.toLp F, hG.toLp G⟫_ℝ = ∫ z in cell c, ⟪F z, G z⟫_ℝ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hF.coeFn_toLp, hG.coeFn_toLp] with z h1 h2
  rw [h1, h2]

/-- `∇^⊥φ` is divergence free: `∫ ∇ψ · ∇^⊥φ = 0` (periodic integration by parts and symmetry of
second derivatives). -/
theorem rotL_mem_divFree (hc : 0 < c) {φ : Plane → ℝ} (hφ : Sob.IsCylTest c φ) :
    rotL hφ ∈ divFree c := by
  rw [mem_divFree]
  intro ψ hψ
  rw [gradL, rotL, inner_toLp_eq]
  have hd := hψ.differentiable
  have hdφ := hφ.differentiable
  have hφη := isCylTest_partialEta hφ
  have hφq := isCylTest_partialQ hφ
  have e : (fun z => ⟪gradT ψ z, rotT φ z⟫_ℝ) = fun z =>
      fderiv ℝ ψ z ((1 : ℝ), (0 : ℝ)) * partialEta φ z -
        fderiv ℝ ψ z ((0 : ℝ), (1 : ℝ)) * partialQ φ z := by
    funext z
    simp only [gradT, rotT, inner_vec, partialQ_eq_fderiv hd, partialEta_eq_fderiv hd,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, PiLp.toLp_apply]
    ring
  rw [e, integral_sub ((hψ.dirDeriv _).integrableOn_mul hφη.continuous)
    ((hψ.dirDeriv _).integrableOn_mul hφq.continuous),
    integral_fderiv_mul_test hc hψ hφη, integral_fderiv_mul_test hc hψ hφq]
  have hsymm : (fun z => fderiv ℝ (partialEta φ) z ((1 : ℝ), (0 : ℝ))) =
      fun z => fderiv ℝ (partialQ φ) z ((0 : ℝ), (1 : ℝ)) := by
    rw [← dir01_eq hdφ, ← dir10_eq hdφ]
    have := Sob.iterDirDeriv_perm (List.Perm.swap ((0 : ℝ), (1 : ℝ)) ((1 : ℝ), (0 : ℝ)) [])
      hφ.smooth
    exact this
  have h2 : ∀ z, fderiv ℝ (partialEta φ) z ((1 : ℝ), (0 : ℝ)) =
      fderiv ℝ (partialQ φ) z ((0 : ℝ), (1 : ℝ)) := fun z => congrFun hsymm z
  simp_rw [h2]
  ring

/-- **`curl P₀ = curl`** (B0820, tex 11970–11989): for every periodic test `φ`,
`∫_cell P₀f · ∇^⊥φ = ∫_cell f · ∇^⊥φ`. -/
theorem curl_P0 (hc : 0 < c) (f : L2v c) {φ : Plane → ℝ} (hφ : Sob.IsCylTest c φ) :
    ∫ z in cell c, ⟪(P0 c f) z, rotT φ z⟫_ℝ = ∫ z in cell c, ⟪f z, rotT φ z⟫_ℝ := by
  have h1 : ∀ g : L2v c, ⟪g, rotL hφ⟫_ℝ = ∫ z in cell c, ⟪g z, rotT φ z⟫_ℝ := by
    intro g
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [(memLp_rotT hφ).coeFn_toLp] with z hz
    rw [rotL, hz]
  rw [← h1, ← h1, inner_P0_comm, P0_eq_self (rotL_mem_divFree hc hφ)]

/-! ### The horizontal mean of `P₀ f` (B0852) -/

theorem memLp_component (f : L2v c) (i : Fin 2) : MemLp (fun z => f z i) 2 (cellμ c) :=
  MemLp.of_le (Lp.memLp f)
    ((EuclideanSpace.proj i : Vec2 →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable f))
    (Eventually.of_forall fun z => by
      simpa using PiLp.norm_apply_le (f z) i)

theorem freq_zero (c : ℝ) : freq c 0 = 0 := by simp [freq]

theorem sinTest_zero (ψ : ℝ → ℝ) (z : Plane) : sinTest 0 ψ z = 0 := by simp [sinTest]

theorem pairC_zero (g : Plane → ℝ) (ψ : ℝ → ℝ) :
    pairC c 0 g ψ = ((∫ z in cell c, cosTest 0 ψ z * g z : ℝ) : ℂ) := by
  simp [pairC, freq_zero, sinTest_zero]

/-- The `q`-mean of the second component of a divergence-free field vanishes. -/
theorem qMode_zero_snd_eq_zero (hc : 0 < c) {u : L2v c} (hu : u ∈ divFree c) :
    modeR c hc 0 (fun z => u z 1) =ᵐ[volume] 0 := by
  have hm := memLp_component u 1
  refine OneD.eq_zero_of_deriv (memLp_modeR hc 0 hm) fun θ hθ => ?_
  have hd : Differentiable ℝ θ := hθ.smooth.differentiable (by simp)
  have hφ := isCylTest_cosTest hc 0 hθ
  have h0 := mem_divFree.1 hu _ hφ
  rw [gradL, inner_toLp_left] at h0
  have hfun : (fun z => ⟪gradT (cosTest (freq c 0) θ) z, (u : Plane → Vec2) z⟫_ℝ) =
      fun z => cosTest (freq c 0) (deriv θ) z * u z 1 := by
    funext z
    rw [real_inner_comm, gradT, inner_vec, partialQ_cosTest, partialEta_cosTest _ hd, freq_zero]
    ring
  rw [hfun] at h0
  have hp : pairC c 0 (fun z => u z 1) (deriv θ) = 0 := by
    rw [pairC_zero, ← freq_zero c, h0]; simp
  rw [pairC_eq' hc 0 hm hθ.deriv] at hp
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  exact (mul_eq_zero.1 hp).resolve_left hc0

/-- The field `(θ(η), 0)`, constant in `q`. -/
def etaField (θ : ℝ → ℝ) (z : Plane) : Vec2 := vec (cosTest 0 θ z) 0

theorem memLp_etaField {θ : ℝ → ℝ} (hθ : OneD.Test θ) : MemLp (etaField θ) 2 (cellμ c) := by
  obtain ⟨M, -, hM⟩ := hθ.exists_bound
  refine memLp_of_vanishes ?_ (R := M) (fun z hz => ?_) 2
  · refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
    fin_cases i
    · exact (Real.continuous_cos.comp (continuous_const.mul continuous_fst)).mul
        (hθ.continuous.comp continuous_snd)
    · exact continuous_const
  · simp only [etaField, cosTest, hM _ hz.le, mul_zero]
    ext i; fin_cases i <;> rfl

theorem etaField_mem_divFree (hc : 0 < c) {θ : ℝ → ℝ} (hθ : OneD.Test θ) :
    (memLp_etaField (c := c) hθ).toLp _ ∈ divFree c := by
  rw [mem_divFree]
  intro ψ hψ
  rw [gradL, inner_toLp_eq]
  have hφ := isCylTest_cosTest hc 0 hθ
  rw [freq_zero] at hφ
  have e : (fun z => ⟪gradT ψ z, etaField θ z⟫_ℝ) =
      fun z => fderiv ℝ ψ z ((1 : ℝ), (0 : ℝ)) * cosTest 0 θ z := by
    funext z
    rw [etaField, inner_vec, gradT, partialQ_eq_fderiv hψ.differentiable]
    simp
  have h0 : ∀ z, fderiv ℝ (cosTest 0 θ) z ((1 : ℝ), (0 : ℝ)) = 0 := fun z => by
    rw [← partialQ_eq_fderiv hφ.differentiable, partialQ_cosTest]; simp
  rw [e, integral_fderiv_mul_test hc hψ hφ]
  simp [h0]

/-- **The horizontal mean of `P₀ f`** (B0852, tex 12688–12706; BP4 "on the mean mode,
divergence-free means `∂_η g₂ = 0`, so `P₀(f̄₁, f̄₂) = (f̄₁, 0)`"): the `q`-average of the
second component of `P₀ f` vanishes, and that of the first component is `f̄₁`. -/
theorem qAvg_P0 (hc : 0 < c) (f : L2v c) :
    qAvg c (fun z => ((P0 c f) z 1 : ℂ)) =ᵐ[volume] 0 ∧
      qAvg c (fun z => ((P0 c f) z 0 : ℂ)) =ᵐ[volume] qAvg c (fun z => (f z 0 : ℂ)) := by
  have hq : ∀ g : Plane → ℂ, qMode c hc 0 g = qAvg c g := fun g => funext fun η => qMode_zero hc g η
  refine ⟨?_, ?_⟩
  · rw [← hq]; exact qMode_zero_snd_eq_zero hc (P0_mem f)
  · rw [← hq, ← hq]
    have hm1 := memLp_component f 0
    have hm2 := memLp_component (P0 c f) 0
    have hv : MemLp (fun η => modeR c hc 0 (fun z => (P0 c f) z 0) η -
        modeR c hc 0 (fun z => f z 0) η) 2 volume :=
      (memLp_modeR hc 0 hm2).sub (memLp_modeR hc 0 hm1)
    have key := ae_eq_zero_of_integral_contDiff_smul_eq_zero (hv.locallyIntegrable (by norm_num))
      fun θ hθs hθc => by
        have hθ : OneD.Test θ := ⟨hθs, hθc⟩
        have horth := sub_P0_mem_orthogonal f _ (etaField_mem_divFree hc hθ)
        rw [inner_toLp_left (memLp_etaField hθ)] at horth
        have e1 : (fun z => ⟪etaField θ z, ((f - P0 c f : L2v c) : Plane → Vec2) z⟫_ℝ) =ᵐ[volume.restrict (cell c)]
            fun z => cosTest 0 θ z * f z 0 - cosTest 0 θ z * (P0 c f) z 0 := by
          filter_upwards [Lp.coeFn_sub f (P0 c f)] with z hz
          rw [hz, real_inner_comm, etaField, inner_vec]
          simp only [Pi.sub_apply, PiLp.sub_apply]
          ring
        rw [integral_congr_ae e1] at horth
        have hφ := isCylTest_cosTest hc 0 hθ
        rw [freq_zero] at hφ
        rw [integral_sub (integrableOn_test_mul hφ hm1) (integrableOn_test_mul hφ hm2),
          sub_eq_zero] at horth
        have hp : pairC c 0 (fun z => (P0 c f) z 0) θ = 1 * pairC c 0 (fun z => f z 0) θ := by
          rw [pairC_zero, pairC_zero, horth, one_mul]
        have hmm := integral_mode_eq_of_pairC hc 0 hm2 hm1 hθ hp
        rw [one_mul] at hmm
        have e2 : (fun η => θ η • (modeR c hc 0 (fun z => (P0 c f) z 0) η -
            modeR c hc 0 (fun z => f z 0) η)) = fun η =>
            θ η • modeR c hc 0 (fun z => (P0 c f) z 0) η - θ η • modeR c hc 0 (fun z => f z 0) η := by
          funext η; rw [smul_sub]
        rw [e2, integral_sub (integrable_modeR hc 0 hm2 hθ) (integrable_modeR hc 0 hm1 hθ), hmm,
          sub_self]
    filter_upwards [key] with η hη
    exact sub_eq_zero.1 hη

end UnforcedLeray.Cyl
