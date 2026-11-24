import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
# B0579 `prepared:p1.1`: weighted spaces and the unweighted negative dual

Blueprint unit **B0579**, label `prepared:p1.1`, `paper/main.tex` lines 9370–9387
(Section `sec:prepared`, P1; definition unit).

**Statement in words.** On the centered meridional `c`-cell of the cylinder
`C_c = (ℝ/cℤ) × ℝ`, with `⟨(q,η)⟩ = (1 + q² + η²)^{1/2}` on the centered cell
`[-c/2, c/2) × ℝ`, put `X_m = L²(⟨(q,η)⟩^{2m} dq dη)` (line 9373) and
`H^1_{±m} = {f : ⟨(q,η)⟩^{±m} (f, ∇f) ∈ L²}` (lines 9374–9375, `∇` distributional on the
cylinder). With the unweighted distributional pairing `⟨f, φ⟩ = ∫ f φ`, define
`H^{-1}_m = (H^1_{-m})^*` (lines 9378–9382). This is the negative-order scale attached to
positively weighted sources (lines 9384–9385): a source `f ∈ X_m` (and a derivative `∂_j G`,
`G ∈ X_m`) defines an element of `H^{-1}_m`. Equivalently one may use the `X_m` pivot
convention, provided the distribution and the pairing are both conjugated by the weight
(lines 9385–9387).

**Lean conventions.**
* `Plane = ℝ × ℝ`, `x = (q, η)`. A field on the cylinder is a function on the plane; all
  integrals are unnormalized Lebesgue integrals over one cell, `cell c = [-c/2, c/2) × ℝ`
  (the manuscript's cell convention, `paper/main.tex:2110-2111`). On the cell
  `⟨x⟩ = bracket x = √(1 + q² + η²)` and `⟨x⟩^{2m} = jb x ^ m`; the periodic continuation of
  the weight is never evaluated off the cell.
* `X c m = Lp ℝ 2 (cellMeasure c m)`, where `cellMeasure c m` is Lebesgue measure on the cell
  with density `(1 + q² + η²)^m`, for any real `m` (`H^1_{+m} = H1 c m`, `H^1_{-m} = H1 c (-m)`).
  Its norm is `‖⟨x⟩^m f‖_{L²(cell)}` (`norm_X`, `memLp_cellMeasure_iff`).
* Cylinder test functions (`IsCylTest c φ`): smooth on the plane, `c`-periodic in `q`, zero for
  `|η|` large. `HasWeakCellDeriv c j f g` means `∫_cell f ∂_j φ = -∫_cell g φ` for all of them
  (`j = 0`: `∂_q`, `j = 1`: `∂_η`). For the elements used the integrals converge absolutely
  (`integrableOn_mul_neg`), so no Bochner junk value enters.
* `H1 c m` is the closed subspace of `PiLp 2 (X c m)³` of triples `(f, ∂_q f, ∂_η f)` satisfying
  the weak-derivative identities: a real Hilbert space (`H1.completeSpace`) with the norm
  `‖⟨x⟩^m (f, ∂_q f, ∂_η f)‖_{L²(cell)}` (`H1.norm_sq_eq_weighted`). `memH1_iff`: it realizes
  exactly the function set `MemH1 c m` of line 9374.
* `Hneg c m := H1 c (-m) →L[ℝ] ℝ`, which is `StrongDual ℝ (H1 c (-m))` by `rfl`.

**Main results.**
* Unweighted pairing: `abs_integral_mul_le` (`|∫_cell f φ| ≤ ‖f‖_{X_m} ‖φ‖_{X_{-m}}`),
  `integrableOn_mul_neg`, `inner_mulW_neg`.
* Positively weighted sources: `sourceCLM : X_m →L H^{-1}_m`, `sourceCLM_apply`
  (`φ ↦ ∫_cell f φ`), `norm_sourceCLM_le`; divergence form: `derivSourceCLM`,
  `derivSourceCLM_apply`, `norm_derivSourceCLM_le`.
* Distributional meaning: `integral_mul_pd` (integration by parts on the cylinder, no seam
  term), `testH1` (test functions lie in every `H^1_m`), `toDistribution_sourceCLM`,
  `toDistribution_derivSourceCLM`, `exists_test_one`.
* Pivot convention: `inner_X_eq`, `inner_eq_unweighted_conj`, `inner_eq_unweighted_conj_left`,
  `unweighted_eq_inner_conj` (conjugation identities at the `L²` level); `weightEquiv`
  (`F ↦ ⟨x⟩^{m - m'} F` is an isomorphism `H^1_m ≃ H^1_{m'}`, from the product rule
  `HasWeakCellDeriv.weight_mul` for the Lipschitz periodic weight, proved with the smooth
  periodic approximations `bApprox` and dominated convergence); `pivot_equivalence`,
  `norm_sourceCLM_le_pivot`, `norm_pivot_le_sourceCLM`.

**Hypotheses made explicit.** `0 < c` (the manuscript has `c = ν^{-ρ} > 0`) is assumed only for
the weight isomorphism and the pivot equivalence; the definitions and the other facts hold for
every real `c`. Uniqueness of weak derivatives on the cylinder (injectivity of `H1.value`) is not
asserted by the unit and is not proved here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff Topology

namespace UnforcedLeray.B0579

/-- Meridional coordinates `x = (q, η)`. -/
abbrev Plane : Type := ℝ × ℝ

/-- The centered meridional `c`-cell `[-c/2, c/2) × ℝ` (`paper/main.tex:9370`). -/
def cell (c : ℝ) : Set Plane := Ico (-(c / 2)) (c / 2) ×ˢ univ

theorem measurableSet_cell (c : ℝ) : MeasurableSet (cell c) :=
  measurableSet_Ico.prod MeasurableSet.univ

/-- `⟨x⟩² = 1 + q² + η²`. -/
def jb (x : Plane) : ℝ := 1 + x.1 ^ 2 + x.2 ^ 2

theorem jb_pos (x : Plane) : 0 < jb x := by unfold jb; positivity

theorem continuous_jb : Continuous jb := by unfold jb; fun_prop

theorem continuous_jb_rpow (k : ℝ) : Continuous fun x => jb x ^ k :=
  continuous_jb.rpow_const fun x => Or.inl (jb_pos x).ne'

/-- The weight `⟨(q, η)⟩ = (1 + q² + η²)^{1/2}` on the centered cell (`paper/main.tex:9373`). -/
def bracket (x : Plane) : ℝ := Real.sqrt (jb x)

theorem bracket_rpow (s : ℝ) (x : Plane) : bracket x ^ s = jb x ^ (s / 2) := by
  rw [bracket, Real.sqrt_eq_rpow, ← Real.rpow_mul (jb_pos x).le]
  congr 1
  ring

theorem jb_rpow_mul (x : Plane) (a b : ℝ) : jb x ^ a * jb x ^ b = jb x ^ (a + b) :=
  (Real.rpow_add (jb_pos x) a b).symm

/-- The density `⟨x⟩^{2m} = (1 + q² + η²)^m`. -/
def density (m : ℝ) (x : Plane) : ℝ≥0 := Real.toNNReal (jb x ^ m)

theorem coe_density (m : ℝ) (x : Plane) : (density m x : ℝ) = jb x ^ m :=
  Real.coe_toNNReal _ (Real.rpow_nonneg (jb_pos x).le m)

theorem density_pos (m : ℝ) (x : Plane) : 0 < (density m x : ℝ) := by
  rw [coe_density]
  exact Real.rpow_pos_of_pos (jb_pos x) m

theorem continuous_density (m : ℝ) : Continuous (density m) :=
  continuous_real_toNNReal.comp (continuous_jb_rpow m)

theorem measurable_density (m : ℝ) : Measurable (density m) :=
  (continuous_density m).measurable

/-- Lebesgue measure on the centered cell with density `⟨x⟩^{2m}`. -/
def cellMeasure (c m : ℝ) : Measure Plane :=
  (volume.restrict (cell c)).withDensity (fun x => (density m x : ℝ≥0∞))

theorem cellMeasure_ac (c m : ℝ) : cellMeasure c m ≪ volume.restrict (cell c) :=
  withDensity_absolutelyContinuous _ _

theorem ac_cellMeasure (c m : ℝ) : volume.restrict (cell c) ≪ cellMeasure c m :=
  withDensity_absolutelyContinuous'
    (measurable_density m).coe_nnreal_ennreal.aemeasurable
    (Eventually.of_forall fun x => by simpa using (density_pos m x).ne')

theorem cellMeasure_ac_cellMeasure (c m m' : ℝ) : cellMeasure c m ≪ cellMeasure c m' :=
  (cellMeasure_ac c m).trans (ac_cellMeasure c m')

/-- **`X_m = L²(⟨(q,η)⟩^{2m} dq dη)`** on the centered cell (`paper/main.tex:9373`). -/
abbrev X (c m : ℝ) : Type := Lp ℝ 2 (cellMeasure c m)

theorem eLpNorm_cellMeasure (c m : ℝ) (f : Plane → ℝ) :
    eLpNorm f 2 (cellMeasure c m) =
      eLpNorm (fun x => jb x ^ (m / 2) * f x) 2 (volume.restrict (cell c)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), cellMeasure,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _
      (measurable_density m).coe_nnreal_ennreal
      (Eventually.of_forall fun _ => ENNReal.coe_lt_top)]
  congr 1
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply, enorm_mul, ENNReal.toReal_ofNat, ENNReal.rpow_two]
  have h0 : 0 ≤ jb x ^ (m / 2) := Real.rpow_nonneg (jb_pos x).le _
  rw [mul_pow, Real.enorm_eq_ofReal h0, ← ENNReal.ofReal_pow h0, ← Real.rpow_natCast,
    ← Real.rpow_mul (jb_pos x).le]
  have : m / 2 * ((2 : ℕ) : ℝ) = m := by push_cast; ring
  rw [this]
  rfl

/-! ### Weight multipliers between the `X_m` -/

/-- Multiplication by `jb^k = ⟨x⟩^{2k}`. -/
def mulFun (k : ℝ) (f : Plane → ℝ) (x : Plane) : ℝ := jb x ^ k * f x

theorem eLpNorm_mulFun (c m m' : ℝ) (f : Plane → ℝ) :
    eLpNorm (mulFun ((m - m') / 2) f) 2 (cellMeasure c m') = eLpNorm f 2 (cellMeasure c m) := by
  rw [eLpNorm_cellMeasure, eLpNorm_cellMeasure]
  congr 1
  funext x
  simp only [mulFun]
  rw [← mul_assoc, jb_rpow_mul]
  congr 2
  ring

theorem memLp_mulFun {c m : ℝ} (m' : ℝ) {f : Plane → ℝ} (hf : MemLp f 2 (cellMeasure c m)) :
    MemLp (mulFun ((m - m') / 2) f) 2 (cellMeasure c m') := by
  refine ⟨?_, ?_⟩
  · exact (continuous_jb_rpow _).aestronglyMeasurable.mul
      (hf.1.mono_ac (cellMeasure_ac_cellMeasure c m' m))
  · rw [eLpNorm_mulFun]
    exact hf.2

theorem coeFn_ae_cell {c m m' : ℝ} {f g : Plane → ℝ} (h : f =ᵐ[cellMeasure c m] g) :
    f =ᵐ[cellMeasure c m'] g :=
  (cellMeasure_ac_cellMeasure c m' m).ae_le h

/-- The multiplier `f ↦ ⟨x⟩^{m - m'} f`, an isometry `X_m → X_{m'}`. -/
def mulW (c m m' : ℝ) : X c m →ₗᵢ[ℝ] X c m' where
  toFun f := (memLp_mulFun m' (Lp.memLp f)).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_mulFun m' (Lp.memLp (f + g))),
      Lp.coeFn_add ((memLp_mulFun m' (Lp.memLp f)).toLp _)
        ((memLp_mulFun m' (Lp.memLp g)).toLp _),
      MemLp.coeFn_toLp (memLp_mulFun m' (Lp.memLp f)),
      MemLp.coeFn_toLp (memLp_mulFun m' (Lp.memLp g)),
      coeFn_ae_cell (m' := m') (Lp.coeFn_add f g)] with x h1 h2 h3 h4 h5
    rw [h1, h2, Pi.add_apply, h3, h4]
    simp only [mulFun, h5, Pi.add_apply]
    ring
  map_smul' a f := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_mulFun m' (Lp.memLp (a • f))),
      Lp.coeFn_smul a ((memLp_mulFun m' (Lp.memLp f)).toLp _),
      MemLp.coeFn_toLp (memLp_mulFun m' (Lp.memLp f)),
      coeFn_ae_cell (m' := m') (Lp.coeFn_smul a f)] with x h1 h2 h3 h4
    rw [h1, RingHom.id_apply, h2, Pi.smul_apply, h3]
    simp only [mulFun, h4, Pi.smul_apply, smul_eq_mul]
    ring
  norm_map' f := by
    change ‖(memLp_mulFun m' (Lp.memLp f)).toLp _‖ = ‖f‖
    rw [Lp.norm_toLp, eLpNorm_mulFun, Lp.norm_def]

theorem coeFn_mulW (c m m' : ℝ) (f : X c m) :
    (mulW c m m' f : Plane → ℝ) =ᵐ[cellMeasure c m'] fun x => jb x ^ ((m - m') / 2) * f x :=
  MemLp.coeFn_toLp (memLp_mulFun m' (Lp.memLp f))

theorem mulW_mulW (c m m' m'' : ℝ) (f : X c m) :
    mulW c m' m'' (mulW c m m' f) = mulW c m m'' f := by
  apply Lp.ext
  filter_upwards [coeFn_mulW c m' m'' (mulW c m m' f), coeFn_mulW c m m'' f,
    coeFn_ae_cell (m' := m'') (coeFn_mulW c m m' f)] with x h1 h2 h3
  rw [h1, h2, h3, ← mul_assoc, jb_rpow_mul]
  congr 2
  ring

theorem mulW_self (c m : ℝ) (f : X c m) : mulW c m m f = f := by
  apply Lp.ext
  filter_upwards [coeFn_mulW c m m f] with x h1
  rw [h1, sub_self, zero_div, Real.rpow_zero, one_mul]

/-- The weight conjugation `X_m ≃ X_{m'}`, `f ↦ ⟨x⟩^{m - m'} f`. -/
def mulWEquiv (c m m' : ℝ) : X c m ≃ₗᵢ[ℝ] X c m' :=
  LinearIsometryEquiv.ofSurjective (mulW c m m') fun g =>
    ⟨mulW c m' m g, by rw [mulW_mulW, mulW_self]⟩

@[simp] theorem mulWEquiv_apply (c m m' : ℝ) (f : X c m) : mulWEquiv c m m' f = mulW c m m' f :=
  rfl

/-! ### The unweighted pairing of `X_m` with `X_{-m}` -/

theorem integral_cellMeasure (c m : ℝ) (g : Plane → ℝ) :
    ∫ x, g x ∂cellMeasure c m = ∫ x in cell c, density m x • g x :=
  integral_withDensity_eq_integral_smul (measurable_density m) g

theorem integrable_cellMeasure_iff (c m : ℝ) {g : Plane → ℝ} :
    Integrable g (cellMeasure c m) ↔ IntegrableOn (fun x => density m x • g x) (cell c) :=
  integrable_withDensity_iff_integrable_smul (measurable_density m)

/-- The unweighted pairing of `f ∈ X_m` with `φ ∈ X_{-m}` is the `X_m` inner product with the
conjugated element `⟨x⟩^{-2m} φ` (and the integral converges absolutely, `integrableOn_mul_neg`). -/
theorem inner_mulW_neg (c m : ℝ) (f : X c m) (φ : X c (-m)) :
    inner ℝ (mulW c (-m) m φ) f = ∫ x in cell c, f x * φ x := by
  rw [L2.inner_def]
  have h1 : (fun x => inner ℝ ((mulW c (-m) m φ : Plane → ℝ) x) (f x)) =ᵐ[cellMeasure c m]
      fun x => jb x ^ ((-m - m) / 2) * φ x * f x := by
    filter_upwards [coeFn_mulW c (-m) m φ] with x hx
    rw [hx, Real.inner_apply]
  rw [integral_congr_ae h1, integral_cellMeasure]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [NNReal.smul_def, smul_eq_mul, coe_density]
  have : jb x ^ m * (jb x ^ ((-m - m) / 2) * φ x * f x) =
      (jb x ^ m * jb x ^ ((-m - m) / 2)) * (f x * φ x) := by ring
  rw [this, jb_rpow_mul]
  have h2 : m + (-m - m) / 2 = 0 := by ring
  rw [h2, Real.rpow_zero, one_mul]

theorem integrableOn_mul_neg (c m : ℝ) (f : X c m) (φ : X c (-m)) :
    IntegrableOn (fun x => f x * φ x) (cell c) := by
  have h0 := L2.integrable_inner (𝕜 := ℝ) (mulW c (-m) m φ) f
  have h1 : (fun x => inner ℝ ((mulW c (-m) m φ : Plane → ℝ) x) (f x)) =ᵐ[cellMeasure c m]
      fun x => jb x ^ ((-m - m) / 2) * φ x * f x := by
    filter_upwards [coeFn_mulW c (-m) m φ] with x hx
    rw [hx, Real.inner_apply]
  have h2 := h0.congr h1
  rw [integrable_cellMeasure_iff] at h2
  refine h2.congr (Eventually.of_forall fun x => ?_)
  simp only
  rw [NNReal.smul_def, smul_eq_mul, coe_density]
  have : jb x ^ m * (jb x ^ ((-m - m) / 2) * φ x * f x) =
      (jb x ^ m * jb x ^ ((-m - m) / 2)) * (f x * φ x) := by ring
  rw [this, jb_rpow_mul]
  have h2 : m + (-m - m) / 2 = 0 := by ring
  rw [h2, Real.rpow_zero, one_mul]

/-- The unweighted pairing (`paper/main.tex:9378`) is bounded on `X_m × X_{-m}`:
`|∫_cell f φ| ≤ ‖f‖_{X_m} ‖φ‖_{X_{-m}}`. -/
theorem abs_integral_mul_le (c m : ℝ) (f : X c m) (φ : X c (-m)) :
    |∫ x in cell c, f x * φ x| ≤ ‖f‖ * ‖φ‖ := by
  rw [← inner_mulW_neg, ← Real.norm_eq_abs]
  calc ‖inner ℝ (mulW c (-m) m φ) f‖ ≤ ‖mulW c (-m) m φ‖ * ‖f‖ := norm_inner_le_norm _ _
    _ = ‖f‖ * ‖φ‖ := by rw [LinearIsometry.norm_map, mul_comm]

/-! ### Test functions on the cylinder `(ℝ / cℤ) × ℝ` -/

/-- The coordinate directions: `dir 0 = e_q`, `dir 1 = e_η`. -/
def dir : Fin 2 → Plane := ![(1, 0), (0, 1)]

/-- The classical partial derivative `∂_q` (`j = 0`) or `∂_η` (`j = 1`). -/
def pd (j : Fin 2) (φ : Plane → ℝ) (x : Plane) : ℝ := fderiv ℝ φ x (dir j)

/-- A test function on the cylinder `C_c = (ℝ/cℤ) × ℝ`, represented on the plane: smooth,
`c`-periodic in `q`, and vanishing for `|η|` large (compact support on the cylinder). -/
structure IsCylTest (c : ℝ) (φ : Plane → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ φ
  periodic : ∀ x : Plane, φ (x.1 + c, x.2) = φ x
  band : ∃ R : ℝ, ∀ x : Plane, R < |x.2| → φ x = 0

theorem IsCylTest.continuous {c : ℝ} {φ : Plane → ℝ} (hφ : IsCylTest c φ) : Continuous φ :=
  hφ.smooth.continuous

theorem IsCylTest.differentiable {c : ℝ} {φ : Plane → ℝ} (hφ : IsCylTest c φ) :
    Differentiable ℝ φ :=
  hφ.smooth.differentiable (by simp)

theorem IsCylTest.pd {c : ℝ} {φ : Plane → ℝ} (hφ : IsCylTest c φ) (j : Fin 2) :
    IsCylTest c (pd j φ) where
  smooth := ((contDiff_infty_iff_fderiv.1 hφ.smooth).2).clm_apply contDiff_const
  periodic x := by
    have hfun : (fun y : Plane => φ (y + ((c, 0) : Plane))) = φ := by
      funext y
      have hy : y + ((c, 0) : Plane) = (y.1 + c, y.2) := by ext <;> simp
      rw [hy]
      exact hφ.periodic y
    have h := fderiv_comp_add_right (𝕜 := ℝ) (f := φ) (x := x) ((c, 0) : Plane)
    rw [hfun] at h
    have hx : x + ((c, 0) : Plane) = (x.1 + c, x.2) := by ext <;> simp
    rw [hx] at h
    simp only [B0579.pd]
    rw [← h]
  band := by
    obtain ⟨R, hR⟩ := hφ.band
    refine ⟨R, fun x hx => ?_⟩
    have hU : IsOpen {y : Plane | R < |y.2|} := isOpen_lt continuous_const continuous_snd.abs
    have hev : φ =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
      Filter.eventually_of_mem (hU.mem_nhds hx) fun y hy => hR y hy
    simp only [B0579.pd]
    rw [hev.fderiv_eq]
    simp

theorem IsCylTest.mul {c : ℝ} {φ χ : Plane → ℝ} (hφ : IsCylTest c φ) (hχ : IsCylTest c χ) :
    IsCylTest c (fun x => φ x * χ x) where
  smooth := hφ.smooth.mul hχ.smooth
  periodic x := by simp only [hφ.periodic x, hχ.periodic x]
  band := by
    obtain ⟨R, hR⟩ := hφ.band
    exact ⟨R, fun x hx => by simp [hR x hx]⟩

/-- The compact box `[-c/2, c/2] × [-R, R]`. -/
def box (c R : ℝ) : Set Plane := Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R

theorem isCompact_box (c R : ℝ) : IsCompact (box c R) := isCompact_Icc.prod isCompact_Icc

theorem mem_box_of_mem_cell {c R : ℝ} {x : Plane} (hx : x ∈ cell c) (hR : |x.2| ≤ R) :
    x ∈ box c R := by
  refine ⟨Ico_subset_Icc_self hx.1, ?_⟩
  exact ⟨by linarith [neg_abs_le x.2], le_trans (le_abs_self _) hR⟩

/-- A continuous function vanishing on the cell outside a compact set is square integrable
on the cell. -/
theorem memLp_cell_of_continuous {c : ℝ} {g : Plane → ℝ} (hg : Continuous g) {K : Set Plane}
    (hK : IsCompact K) (hv : ∀ x ∈ cell c, x ∉ K → g x = 0) :
    MemLp g 2 (volume.restrict (cell c)) := by
  have hKm : MeasurableSet K := hK.measurableSet
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  have h1 : MemLp g 2 (volume.restrict K) := by
    have : IsFiniteMeasure (volume.restrict K) :=
      isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
    exact MemLp.of_bound hg.aestronglyMeasurable C
      ((ae_restrict_iff' hKm).2 (Eventually.of_forall hC))
  have h2 : MemLp (K.indicator g) 2 volume := (memLp_indicator_iff_restrict hKm).2 h1
  refine (h2.restrict (cell c)).ae_eq ?_
  refine (ae_restrict_iff' (measurableSet_cell c)).2 (Eventually.of_forall fun x hx => ?_)
  by_cases hxK : x ∈ K
  · simp [indicator_of_mem hxK]
  · rw [indicator_of_notMem hxK, hv x hx hxK]

theorem IsCylTest.vanish {c : ℝ} {φ : Plane → ℝ} (hφ : IsCylTest c φ) :
    ∃ R : ℝ, ∀ x ∈ cell c, x ∉ box c R → φ x = 0 := by
  obtain ⟨R, hR⟩ := hφ.band
  refine ⟨R, fun x hx hxK => hR x ?_⟩
  by_contra h
  exact hxK (mem_box_of_mem_cell hx (not_lt.1 h))

/-- Test functions lie in every `X_m`. -/
theorem IsCylTest.memLp {c : ℝ} {φ : Plane → ℝ} (hφ : IsCylTest c φ) (m : ℝ) :
    MemLp φ 2 (cellMeasure c m) := by
  obtain ⟨R, hR⟩ := hφ.vanish
  have h := memLp_cell_of_continuous (c := c) (g := fun x => jb x ^ (m / 2) * φ x)
    ((continuous_jb_rpow (m / 2)).mul hφ.continuous)
    (isCompact_box c R) (fun x hx hxK => by simp [hR x hx hxK])
  exact ⟨hφ.continuous.aestronglyMeasurable, by rw [eLpNorm_cellMeasure]; exact h.2⟩

/-- A test function as an element of `X_m`. -/
def testLp (c m : ℝ) {φ : Plane → ℝ} (hφ : IsCylTest c φ) : X c m := (hφ.memLp m).toLp φ

theorem coeFn_testLp (c m : ℝ) {φ : Plane → ℝ} (hφ : IsCylTest c φ) :
    (testLp c m hφ : Plane → ℝ) =ᵐ[volume.restrict (cell c)] φ :=
  (ac_cellMeasure c m).ae_le (MemLp.coeFn_toLp (hφ.memLp m))

/-- The element of `X_m` representing the unweighted pairing `f ↦ ∫_cell f φ`. -/
def testVec (c m : ℝ) {φ : Plane → ℝ} (hφ : IsCylTest c φ) : X c m :=
  mulW c (-m) m (testLp c (-m) hφ)

theorem inner_testVec (c m : ℝ) {φ : Plane → ℝ} (hφ : IsCylTest c φ) (f : X c m) :
    inner ℝ (testVec c m hφ) f = ∫ x in cell c, f x * φ x := by
  rw [testVec, inner_mulW_neg]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_testLp c (-m) hφ] with x hx
  rw [hx]

/-! ### The weighted Sobolev graphs `H^1_{m}` -/

/-- Weak (distributional) derivative on the cylinder: `g = ∂_j f` when
`∫_cell f ∂_j φ = -∫_cell g φ` for every cylinder test function `φ`. -/
def HasWeakCellDeriv (c : ℝ) (j : Fin 2) (f g : Plane → ℝ) : Prop :=
  ∀ φ : Plane → ℝ, IsCylTest c φ → ∫ x in cell c, f x * pd j φ x = -∫ x in cell c, g x * φ x

/-- Slot `0` holds `f`, slots `1, 2` hold `∂_q f`, `∂_η f`. -/
abbrev Ambient (c m : ℝ) : Type := PiLp 2 (fun _ : Fin 3 => X c m)

/-- The continuous functional `F ↦ ∫_cell F₀ ∂_j φ + ∫_cell F_{j+1} φ`. -/
def weakFunctional (c m : ℝ) (j : Fin 2) {φ : Plane → ℝ} (hφ : IsCylTest c φ) :
    Ambient c m →L[ℝ] ℝ :=
  (innerSL ℝ (testVec c m (hφ.pd j))).comp (PiLp.proj 2 (fun _ : Fin 3 => X c m) 0) +
    (innerSL ℝ (testVec c m hφ)).comp (PiLp.proj 2 (fun _ : Fin 3 => X c m) j.succ)

theorem weakFunctional_apply (c m : ℝ) (j : Fin 2) {φ : Plane → ℝ} (hφ : IsCylTest c φ)
    (F : Ambient c m) :
    weakFunctional c m j hφ F =
      (∫ x in cell c, (F.ofLp 0 : Plane → ℝ) x * pd j φ x) +
        ∫ x in cell c, (F.ofLp j.succ : Plane → ℝ) x * φ x := by
  simp only [weakFunctional, add_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, PiLp.proj_apply]
  rw [inner_testVec, inner_testVec]

/-- `H^1_m` inside the ambient tuple space. -/
def H1Sub (c m : ℝ) : Submodule ℝ (Ambient c m) :=
  ⨅ (j : Fin 2) (φ : {φ : Plane → ℝ // IsCylTest c φ}),
    LinearMap.ker (weakFunctional c m j φ.2 : Ambient c m →ₗ[ℝ] ℝ)

theorem mem_H1Sub_iff {c m : ℝ} (F : Ambient c m) :
    F ∈ H1Sub c m ↔ ∀ j : Fin 2,
      HasWeakCellDeriv c j (F.ofLp 0 : Plane → ℝ) (F.ofLp j.succ : Plane → ℝ) := by
  simp only [H1Sub, Submodule.mem_iInf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    weakFunctional_apply, HasWeakCellDeriv]
  constructor
  · intro h j φ hφ
    have := h j ⟨φ, hφ⟩
    linarith
  · intro h j φ
    have := h j φ.1 φ.2
    linarith

theorem isClosed_H1Sub (c m : ℝ) : IsClosed (H1Sub c m : Set (Ambient c m)) := by
  rw [H1Sub, Submodule.coe_iInf]
  refine isClosed_iInter fun j => ?_
  rw [Submodule.coe_iInf]
  exact isClosed_iInter fun φ => (weakFunctional c m j φ.2).isClosed_ker

/-- **`H^1_{±m}`** (`paper/main.tex:9374-9375`): functions with `⟨x⟩^{m} (f, ∇f) ∈ L²` on the
cell (`m` of either sign), stored with their weak gradient `(∂_q f, ∂_η f)`. -/
abbrev H1 (c m : ℝ) : Type := ↥(H1Sub c m)

instance H1.completeSpace (c m : ℝ) : CompleteSpace (H1 c m) :=
  (isClosed_H1Sub c m).completeSpace_coe

example (c m : ℝ) : InnerProductSpace ℝ (H1 c m) := inferInstance

namespace H1

variable {c m : ℝ}

/-- The function `f`. -/
def value (F : H1 c m) : X c m := (F : Ambient c m).ofLp 0

/-- The weak derivative `∂_j f`. -/
def der (F : H1 c m) (j : Fin 2) : X c m := (F : Ambient c m).ofLp j.succ

variable (c m) in
def valueCLM : H1 c m →L[ℝ] X c m :=
  (PiLp.proj 2 (fun _ : Fin 3 => X c m) 0).comp (H1Sub c m).subtypeL

variable (c m) in
def derCLM (j : Fin 2) : H1 c m →L[ℝ] X c m :=
  (PiLp.proj 2 (fun _ : Fin 3 => X c m) j.succ).comp (H1Sub c m).subtypeL

@[simp] theorem valueCLM_apply (F : H1 c m) : valueCLM c m F = F.value := rfl

@[simp] theorem derCLM_apply (j : Fin 2) (F : H1 c m) : derCLM c m j F = F.der j := rfl

theorem hasWeakCellDeriv (F : H1 c m) (j : Fin 2) :
    HasWeakCellDeriv c j (F.value : Plane → ℝ) (F.der j : Plane → ℝ) :=
  (mem_H1Sub_iff (F : Ambient c m)).1 F.2 j

theorem norm_sq (F : H1 c m) : ‖F‖ ^ 2 = ‖F.value‖ ^ 2 + ‖F.der 0‖ ^ 2 + ‖F.der 1‖ ^ 2 := by
  rw [Submodule.coe_norm, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  rfl

theorem norm_value_le (F : H1 c m) : ‖F.value‖ ≤ ‖F‖ :=
  PiLp.norm_apply_le (F : Ambient c m) 0

theorem norm_der_le (F : H1 c m) (j : Fin 2) : ‖F.der j‖ ≤ ‖F‖ :=
  PiLp.norm_apply_le (F : Ambient c m) j.succ

end H1

/-! ### Function-level description of `X_m` and `H^1_m` -/

theorem continuous_bracket_rpow (m : ℝ) : Continuous fun x => bracket x ^ m := by
  simp only [bracket_rpow]
  exact continuous_jb_rpow _

theorem bracket_rpow_pos (m : ℝ) (x : Plane) : 0 < bracket x ^ m := by
  rw [bracket_rpow]
  exact Real.rpow_pos_of_pos (jb_pos x) _

theorem aestronglyMeasurable_bracket_iff (c m : ℝ) {f : Plane → ℝ} :
    AEStronglyMeasurable f (cellMeasure c m) ↔
      AEStronglyMeasurable (fun x => bracket x ^ m * f x) (volume.restrict (cell c)) := by
  constructor
  · intro hf
    exact (continuous_bracket_rpow m).aestronglyMeasurable.mul (hf.mono_ac (ac_cellMeasure c m))
  · intro hf
    have h2 : AEStronglyMeasurable (fun x => (bracket x ^ m)⁻¹ * (bracket x ^ m * f x))
        (volume.restrict (cell c)) :=
      ((continuous_bracket_rpow m).inv₀ fun x =>
        (bracket_rpow_pos m x).ne').aestronglyMeasurable.mul hf
    have he : (fun x => (bracket x ^ m)⁻¹ * (bracket x ^ m * f x)) = f := by
      funext x
      rw [← mul_assoc, inv_mul_cancel₀ (bracket_rpow_pos m x).ne', one_mul]
    rw [he] at h2
    exact h2.mono_ac (cellMeasure_ac c m)

/-- `f ∈ X_m` iff `⟨x⟩^m f ∈ L²` of the centered cell (`paper/main.tex:9373`). -/
theorem memLp_cellMeasure_iff (c m : ℝ) {f : Plane → ℝ} :
    MemLp f 2 (cellMeasure c m) ↔
      MemLp (fun x => bracket x ^ m * f x) 2 (volume.restrict (cell c)) := by
  unfold MemLp
  rw [aestronglyMeasurable_bracket_iff, eLpNorm_cellMeasure]
  simp only [bracket_rpow]

/-- The norm of `X_m` is `‖⟨x⟩^m f‖_{L²(cell)}`. -/
theorem norm_X (c m : ℝ) (f : X c m) :
    ‖f‖ = (eLpNorm (fun x => bracket x ^ m * f x) 2 (volume.restrict (cell c))).toReal := by
  rw [Lp.norm_def, eLpNorm_cellMeasure]
  simp only [bracket_rpow]

theorem HasWeakCellDeriv.congr {c : ℝ} {j : Fin 2} {f g f' g' : Plane → ℝ}
    (h : HasWeakCellDeriv c j f g) (hf : f =ᵐ[volume.restrict (cell c)] f')
    (hg : g =ᵐ[volume.restrict (cell c)] g') : HasWeakCellDeriv c j f' g' := by
  intro φ hφ
  have h1 : ∫ x in cell c, f' x * pd j φ x = ∫ x in cell c, f x * pd j φ x :=
    integral_congr_ae (hf.mono fun x hx => by simp only [hx])
  have h2 : ∫ x in cell c, g' x * φ x = ∫ x in cell c, g x * φ x :=
    integral_congr_ae (hg.mono fun x hx => by simp only [hx])
  rw [h1, h2]
  exact h φ hφ

/-- The set `H^1_m = {f : ⟨x⟩^m (f, ∇f) ∈ L²}` of `paper/main.tex:9374-9375`, at the level of
functions on the cell, with the distributional gradient on the cylinder. -/
def MemH1 (c m : ℝ) (f : Plane → ℝ) : Prop :=
  MemLp (fun x => bracket x ^ m * f x) 2 (volume.restrict (cell c)) ∧
    ∃ g : Fin 2 → Plane → ℝ, ∀ j : Fin 2,
      MemLp (fun x => bracket x ^ m * g j x) 2 (volume.restrict (cell c)) ∧
        HasWeakCellDeriv c j f (g j)

/-- The canonical tuple `(f, ∂_q f, ∂_η f)`. -/
def tuple (c m : ℝ) (f : X c m) (g : Fin 2 → X c m) : Ambient c m :=
  WithLp.toLp 2 (Fin.cons f g)

/-- The Hilbert space `H1 c m` realizes exactly the function set `MemH1 c m`. -/
theorem memH1_iff (c m : ℝ) (f : Plane → ℝ) :
    MemH1 c m f ↔ ∃ F : H1 c m, (F.value : Plane → ℝ) =ᵐ[volume.restrict (cell c)] f := by
  constructor
  · rintro ⟨hf, g, hg⟩
    have hf' := (memLp_cellMeasure_iff c m).2 hf
    have hg' : ∀ j, MemLp (g j) 2 (cellMeasure c m) := fun j => (memLp_cellMeasure_iff c m).2 (hg j).1
    let T := tuple c m (hf'.toLp f) (fun j => (hg' j).toLp (g j))
    have e0 : ((hf'.toLp f : X c m) : Plane → ℝ) =ᵐ[volume.restrict (cell c)] f :=
      (ac_cellMeasure c m).ae_le (MemLp.coeFn_toLp hf')
    have ej : ∀ j, (((hg' j).toLp (g j) : X c m) : Plane → ℝ) =ᵐ[volume.restrict (cell c)] g j :=
      fun j => (ac_cellMeasure c m).ae_le (MemLp.coeFn_toLp (hg' j))
    have hT : T ∈ H1Sub c m := by
      rw [mem_H1Sub_iff]
      intro j
      exact (hg j).2.congr e0.symm (ej j).symm
    exact ⟨⟨T, hT⟩, (ac_cellMeasure c m).ae_le (MemLp.coeFn_toLp hf')⟩
  · rintro ⟨F, hF⟩
    refine ⟨?_, fun j => (F.der j : Plane → ℝ), fun j => ⟨?_, ?_⟩⟩
    · refine ((memLp_cellMeasure_iff c m).1 (Lp.memLp F.value)).ae_eq ?_
      exact hF.mono fun x hx => by simp only [hx]
    · exact (memLp_cellMeasure_iff c m).1 (Lp.memLp (F.der j))
    · exact (F.hasWeakCellDeriv j).congr hF (ae_eq_refl _)

namespace H1

variable {c m : ℝ}

/-- The norm of `H^1_m` is `‖⟨x⟩^m (f, ∂_q f, ∂_η f)‖_{L²(cell)}`. -/
theorem norm_sq_eq_weighted (F : H1 c m) :
    ‖F‖ ^ 2 =
      (eLpNorm (fun x => bracket x ^ m * F.value x) 2 (volume.restrict (cell c))).toReal ^ 2 +
      (eLpNorm (fun x => bracket x ^ m * F.der 0 x) 2 (volume.restrict (cell c))).toReal ^ 2 +
      (eLpNorm (fun x => bracket x ^ m * F.der 1 x) 2 (volume.restrict (cell c))).toReal ^ 2 := by
  rw [norm_sq, norm_X, norm_X, norm_X]

end H1

/-! ### The negative space `H^{-1}_m = (H^1_{-m})^*` with the unweighted pairing -/

/-- **`H^{-1}_m := (H^1_{-m})^*`**, the continuous dual (`prepared:p1.1`, `paper/main.tex:9380`);
sources act on it through the unweighted pairing (`sourceCLM`, line 9378). -/
abbrev Hneg (c m : ℝ) : Type := H1 c (-m) →L[ℝ] ℝ

/-- `Hneg c m` is literally Mathlib's strong dual of `H^1_{-m}`. -/
example (c m : ℝ) : Hneg c m = StrongDual ℝ (H1 c (-m)) := rfl

/-- The value of `φ ∈ H^1_{-m}`, conjugated into `X_m`: `⟨x⟩^{-2m} φ`. -/
def conjValue (c m : ℝ) : H1 c (-m) →L[ℝ] X c m :=
  (mulW c (-m) m).toContinuousLinearMap.comp (H1.valueCLM c (-m))

theorem norm_conjValue_le (c m : ℝ) (φ : H1 c (-m)) : ‖conjValue c m φ‖ ≤ ‖φ‖ := by
  simp only [conjValue, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    H1.valueCLM_apply, LinearIsometry.norm_map]
  exact H1.norm_value_le φ

/-- The conjugated derivative `⟨x⟩^{-2m} ∂_j φ` of `φ ∈ H^1_{-m}`, in `X_m`. -/
def conjDer (c m : ℝ) (j : Fin 2) : H1 c (-m) →L[ℝ] X c m :=
  (mulW c (-m) m).toContinuousLinearMap.comp (H1.derCLM c (-m) j)

theorem norm_conjDer_le (c m : ℝ) (j : Fin 2) (φ : H1 c (-m)) : ‖conjDer c m j φ‖ ≤ ‖φ‖ := by
  simp only [conjDer, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    H1.derCLM_apply, LinearIsometry.norm_map]
  exact H1.norm_der_le φ j

/-- The functional `φ ↦ ⟪f, A φ⟫_{X_m}` on a normed space `V` of test elements, for a bounded
`A : V → X_m`; linear in `f`. -/
def pairLM (c m : ℝ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : V →L[ℝ] X c m) : X c m →ₗ[ℝ] (V →L[ℝ] ℝ) where
  toFun f := (innerSL ℝ f).comp A
  map_add' f g := by
    ext φ
    simp
  map_smul' a f := by
    ext φ
    simp

theorem pairLM_apply (c m : ℝ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : V →L[ℝ] X c m) (f : X c m) (φ : V) :
    pairLM c m A f φ = inner ℝ f (A φ) := rfl

theorem pairLM_bound (c m : ℝ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : V →L[ℝ] X c m) (hA : ∀ φ, ‖A φ‖ ≤ ‖φ‖) (f : X c m) : ‖pairLM c m A f‖ ≤ 1 * ‖f‖ := by
  rw [one_mul]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f) fun φ => ?_
  rw [pairLM_apply]
  calc ‖inner ℝ f (A φ)‖ ≤ ‖f‖ * ‖A φ‖ := norm_inner_le_norm _ _
    _ ≤ ‖f‖ * ‖φ‖ := by gcongr; exact hA φ

/-- The bounded linear map `f ↦ (φ ↦ ⟪f, A φ⟫_{X_m})`, for `A` of norm at most one. -/
def pairCLM (c m : ℝ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : V →L[ℝ] X c m) (hA : ∀ φ, ‖A φ‖ ≤ ‖φ‖) : X c m →L[ℝ] (V →L[ℝ] ℝ) :=
  LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ) (E := X c m) (F := V →L[ℝ] ℝ) (σ := RingHom.id ℝ)
    (pairLM c m A) 1 (pairLM_bound c m A hA)

theorem pairCLM_apply (c m : ℝ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : V →L[ℝ] X c m) (hA : ∀ φ, ‖A φ‖ ≤ ‖φ‖)
    (f : X c m) (φ : V) : pairCLM c m A hA f φ = inner ℝ f (A φ) := rfl

theorem norm_pairCLM_le (c m : ℝ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : V →L[ℝ] X c m) (hA : ∀ φ, ‖A φ‖ ≤ ‖φ‖) (f : X c m) : ‖pairCLM c m A hA f‖ ≤ ‖f‖ := by
  have h := pairLM_bound c m A hA f
  rw [one_mul] at h
  exact h

/-- **Positively weighted sources** (`paper/main.tex:9378`, `9384-9385`). The unweighted
distributional pairing `⟨f, φ⟩ = ∫_cell f φ` maps `X_m` continuously into `H^{-1}_m`. -/
def sourceCLM (c m : ℝ) : X c m →L[ℝ] Hneg c m := pairCLM c m (conjValue c m) (norm_conjValue_le c m)

/-- The source functional is the unweighted pairing `φ ↦ ∫_cell f φ`. -/
theorem sourceCLM_apply (c m : ℝ) (f : X c m) (φ : H1 c (-m)) :
    sourceCLM c m f φ = ∫ x in cell c, f x * φ.value x := by
  rw [sourceCLM, pairCLM_apply, real_inner_comm]
  exact inner_mulW_neg c m f φ.value

theorem integrableOn_source (c m : ℝ) (f : X c m) (φ : H1 c (-m)) :
    IntegrableOn (fun x => f x * φ.value x) (cell c) :=
  integrableOn_mul_neg c m f φ.value

/-- `‖f‖_{H^{-1}_m} ≤ ‖f‖_{X_m}` (`paper/main.tex:9384-9385`). -/
theorem norm_sourceCLM_le (c m : ℝ) (f : X c m) : ‖sourceCLM c m f‖ ≤ ‖f‖ :=
  norm_pairCLM_le c m _ (norm_conjValue_le c m) f

/-- Divergence-form sources: for `G ∈ X_m`, the distribution `∂_j G`,
`⟨∂_j G, φ⟩ = -∫_cell G ∂_j φ`, lies in `H^{-1}_m` with norm at most `‖G‖_{X_m}`. -/
def derivSourceCLM (c m : ℝ) (j : Fin 2) : X c m →L[ℝ] Hneg c m :=
  -pairCLM c m (conjDer c m j) (norm_conjDer_le c m j)

theorem derivSourceCLM_apply (c m : ℝ) (j : Fin 2) (G : X c m) (φ : H1 c (-m)) :
    derivSourceCLM c m j G φ = -∫ x in cell c, G x * φ.der j x := by
  rw [derivSourceCLM, neg_apply, neg_apply, pairCLM_apply, real_inner_comm]
  congr 1
  exact inner_mulW_neg c m G (φ.der j)

theorem norm_derivSourceCLM_le (c m : ℝ) (j : Fin 2) (G : X c m) :
    ‖derivSourceCLM c m j G‖ ≤ ‖G‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg G) fun φ => ?_
  rw [derivSourceCLM, neg_apply, neg_apply, norm_neg, pairCLM_apply]
  calc ‖inner ℝ G (conjDer c m j φ)‖ ≤ ‖G‖ * ‖conjDer c m j φ‖ := norm_inner_le_norm _ _
    _ ≤ ‖G‖ * ‖φ‖ := by gcongr; exact norm_conjDer_le c m j φ

/-! ### Integration by parts on the cylinder: test functions lie in every `H^1_m` -/

theorem integrableOn_cell_of_continuous {c : ℝ} {g : Plane → ℝ} (hg : Continuous g)
    {K : Set Plane} (hK : IsCompact K) (hv : ∀ x ∈ cell c, x ∉ K → g x = 0) :
    IntegrableOn g (cell c) :=
  (hg.continuousOn.integrableOn_compact hK).of_forall_sdiff_eq_zero (measurableSet_cell c)
    (fun x hx => hv x hx.1 hx.2)

theorem IsCylTest.integrableOn {c : ℝ} {φ : Plane → ℝ} (hφ : IsCylTest c φ) :
    IntegrableOn φ (cell c) := by
  obtain ⟨R, hR⟩ := hφ.vanish
  exact integrableOn_cell_of_continuous hφ.continuous (isCompact_box c R) hR

theorem hasDerivAt_fst {φ : Plane → ℝ} (hφ : Differentiable ℝ φ) (q η : ℝ) :
    HasDerivAt (fun t => φ (t, η)) (pd 0 φ (q, η)) q := by
  have h1 : HasDerivAt (fun t : ℝ => ((t, η) : Plane)) ((1, 0) : Plane) q :=
    (hasDerivAt_id' q).prodMk (hasDerivAt_const q η)
  have h2 := (hφ (q, η)).hasFDerivAt.comp_hasDerivAt q h1
  simpa [pd, dir, Function.comp_def] using h2

theorem hasDerivAt_snd {φ : Plane → ℝ} (hφ : Differentiable ℝ φ) (q η : ℝ) :
    HasDerivAt (fun t => φ (q, t)) (pd 1 φ (q, η)) η := by
  have h1 : HasDerivAt (fun t : ℝ => ((q, t) : Plane)) ((0, 1) : Plane) η :=
    (hasDerivAt_const η q).prodMk (hasDerivAt_id' η)
  have h2 := (hφ (q, η)).hasFDerivAt.comp_hasDerivAt η h1
  simpa [pd, dir, Function.comp_def] using h2

theorem IsCylTest.hasCompactSupport_slice {c : ℝ} {φ : Plane → ℝ} (hφ : IsCylTest c φ)
    (q : ℝ) : HasCompactSupport fun t => φ (q, t) := by
  obtain ⟨R, hR⟩ := hφ.band
  refine HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) fun t ht => hR _ ?_
  simp only [mem_Icc, not_and_or, not_le] at ht
  rcases ht with ht | ht
  · exact lt_of_lt_of_le (by linarith) (neg_le_abs t)
  · exact lt_of_lt_of_le ht (le_abs_self t)

/-- `∫_cell ∂_q ψ = 0`: the two seam values cancel by periodicity. -/
theorem integral_pd_zero {c : ℝ} {ψ : Plane → ℝ} (hψ : IsCylTest c ψ) :
    ∫ x in cell c, pd 0 ψ x = 0 := by
  have hint := (hψ.pd 0).integrableOn
  unfold IntegrableOn at hint
  rw [cell, Measure.volume_eq_prod, ← Measure.prod_restrict] at hint ⊢
  rw [integral_prod_symm _ hint]
  refine (integral_congr_ae (Eventually.of_forall fun η => ?_)).trans (integral_zero _ _)
  by_cases hc : -(c / 2) ≤ c / 2
  · rw [integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hc,
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun q _ => hasDerivAt_fst hψ.differentiable q η)
        (((hψ.pd 0).continuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _)]
    have h := hψ.periodic (-(c / 2), η)
    rw [show -(c / 2) + c = c / 2 by ring] at h
    rw [h, sub_self]
  · rw [Ico_eq_empty fun h => hc h.le, Measure.restrict_empty, integral_zero_measure]

/-- `∫_cell ∂_η ψ = 0`: compact support in `η`. -/
theorem integral_pd_one {c : ℝ} {ψ : Plane → ℝ} (hψ : IsCylTest c ψ) :
    ∫ x in cell c, pd 1 ψ x = 0 := by
  have hint := (hψ.pd 1).integrableOn
  rw [cell, Measure.volume_eq_prod] at hint ⊢
  rw [setIntegral_prod _ hint]
  refine (integral_congr_ae (Eventually.of_forall fun q => ?_)).trans (integral_zero _ _)
  simp only [Measure.restrict_univ]
  exact integral_eq_zero_of_hasDerivAt_of_integrable
    (fun η => hasDerivAt_snd hψ.differentiable q η)
    (((hψ.pd 1).continuous.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      ((hψ.pd 1).hasCompactSupport_slice q))
    ((hψ.continuous.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (hψ.hasCompactSupport_slice q))

theorem integral_pd_eq_zero {c : ℝ} {ψ : Plane → ℝ} (hψ : IsCylTest c ψ) (j : Fin 2) :
    ∫ x in cell c, pd j ψ x = 0 := by
  fin_cases j
  · exact integral_pd_zero hψ
  · exact integral_pd_one hψ

theorem pd_mul {φ χ : Plane → ℝ} (hφ : Differentiable ℝ φ) (hχ : Differentiable ℝ χ)
    (j : Fin 2) (x : Plane) : pd j (fun y => φ y * χ y) x = pd j φ x * χ x + φ x * pd j χ x := by
  simp only [pd]
  rw [fderiv_fun_mul (hφ x) (hχ x)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- Integration by parts on the cylinder, without boundary terms. -/
theorem integral_mul_pd {c : ℝ} {φ χ : Plane → ℝ} (hφ : IsCylTest c φ) (hχ : IsCylTest c χ)
    (j : Fin 2) : ∫ x in cell c, φ x * pd j χ x = -∫ x in cell c, pd j φ x * χ x := by
  have h0 := integral_pd_eq_zero (hφ.mul hχ) j
  have heq : pd j (fun y => φ y * χ y) = fun x => pd j φ x * χ x + φ x * pd j χ x :=
    funext (pd_mul hφ.differentiable hχ.differentiable j)
  rw [heq, integral_add ((hφ.pd j).mul hχ).integrableOn (hφ.mul (hχ.pd j)).integrableOn] at h0
  linarith

/-- Classical derivatives of test functions are their weak cylinder derivatives. -/
theorem IsCylTest.hasWeakCellDeriv {c : ℝ} {φ : Plane → ℝ} (hφ : IsCylTest c φ) (j : Fin 2) :
    HasWeakCellDeriv c j φ (B0579.pd j φ) :=
  fun _ hχ => integral_mul_pd hφ hχ j

/-- A test function as an element of `H^1_m` (for every weight exponent `m`). -/
def testH1 (c m : ℝ) {φ : Plane → ℝ} (hφ : IsCylTest c φ) : H1 c m :=
  ⟨tuple c m (testLp c m hφ) (fun j => testLp c m (hφ.pd j)), by
    rw [mem_H1Sub_iff]
    intro j
    exact (hφ.hasWeakCellDeriv j).congr (coeFn_testLp c m hφ).symm
      (coeFn_testLp c m (hφ.pd j)).symm⟩

@[simp] theorem testH1_value (c m : ℝ) {φ : Plane → ℝ} (hφ : IsCylTest c φ) :
    (testH1 c m hφ).value = testLp c m hφ := rfl

@[simp] theorem testH1_der (c m : ℝ) {φ : Plane → ℝ} (hφ : IsCylTest c φ) (j : Fin 2) :
    (testH1 c m hφ).der j = testLp c m (hφ.pd j) := rfl

/-- The restriction of `ℓ ∈ H^{-1}_m` to cylinder test functions: the distribution it defines. -/
def toDistribution (c m : ℝ) (ℓ : Hneg c m) (φ : {φ : Plane → ℝ // IsCylTest c φ}) : ℝ :=
  ℓ (testH1 c (-m) φ.2)

/-- On test functions the source functional of `f ∈ X_m` is the unweighted distributional
pairing `⟨f, φ⟩ = ∫_cell f φ` (`paper/main.tex:9378`). -/
theorem toDistribution_sourceCLM (c m : ℝ) (f : X c m) (φ : {φ : Plane → ℝ // IsCylTest c φ}) :
    toDistribution c m (sourceCLM c m f) φ = ∫ x in cell c, f x * φ.1 x := by
  rw [toDistribution, sourceCLM_apply, testH1_value]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_testLp c (-m) φ.2] with x hx
  rw [hx]

/-- On test functions `derivSourceCLM j G` is the distributional derivative `∂_j G`. -/
theorem toDistribution_derivSourceCLM (c m : ℝ) (j : Fin 2) (G : X c m)
    (φ : {φ : Plane → ℝ // IsCylTest c φ}) :
    toDistribution c m (derivSourceCLM c m j G) φ = -∫ x in cell c, G x * pd j φ.1 x := by
  rw [toDistribution, derivSourceCLM_apply, testH1_der]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [coeFn_testLp c (-m) (φ.2.pd j)] with x hx
  rw [hx]

/-- Non-degeneracy of the test class: a test function with `φ(0, 0) = 1` (a bump in `η`,
constant in `q`). -/
theorem exists_test_one (c : ℝ) : ∃ φ : Plane → ℝ, IsCylTest c φ ∧ φ (0, 0) = 1 := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  refine ⟨fun x => b x.2, ⟨b.contDiff.comp contDiff_snd, fun x => rfl, ⟨2, fun x hx => ?_⟩⟩, ?_⟩
  · exact b.zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact hx.le)
  · exact b.one_of_mem_closedBall (by simp [b])

/-! ### The `X_m`-pivot convention (`paper/main.tex:9384-9387`) -/

/-- The `X_m` inner product is the weighted integral `⟪f, ψ⟫_{X_m} = ∫_cell f ψ ⟨x⟩^{2m}`. -/
theorem inner_X_eq (c m : ℝ) (f ψ : X c m) :
    inner ℝ f ψ = ∫ x in cell c, f x * ψ x * bracket x ^ (2 * m) := by
  rw [L2.inner_def, integral_cellMeasure]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [NNReal.smul_def, smul_eq_mul, coe_density, Real.inner_apply, bracket_rpow,
    show 2 * m / 2 = m by ring]
  ring

/-- Conjugated pairing, test side: the pivot pairing `⟪f, ψ⟫_{X_m}` is the unweighted pairing of
`f` with the conjugated element `⟨x⟩^{2m} ψ ∈ X_{-m}`. -/
theorem inner_eq_unweighted_conj (c m : ℝ) (f ψ : X c m) :
    inner ℝ f ψ = ∫ x in cell c, f x * mulW c m (-m) ψ x := by
  rw [← inner_mulW_neg, mulW_mulW, mulW_self, real_inner_comm]

/-- Conjugated pairing, distribution side: `⟪f, ψ⟫_{X_m} = ∫_cell (⟨x⟩^{2m} f) ψ`, the unweighted
pairing of the conjugated distribution `⟨x⟩^{2m} f ∈ X_{-m}` with `ψ ∈ X_m`. -/
theorem inner_eq_unweighted_conj_left (c m : ℝ) (f ψ : X c m) :
    inner ℝ f ψ = ∫ x in cell c, mulW c m (-m) f x * ψ x := by
  rw [real_inner_comm, inner_eq_unweighted_conj]
  exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)

/-- Conversely the unweighted pairing of `f ∈ X_m` with `φ ∈ X_{-m}` is the pivot pairing of `f`
with `⟨x⟩^{-2m} φ ∈ X_m`. -/
theorem unweighted_eq_inner_conj (c m : ℝ) (f : X c m) (φ : X c (-m)) :
    ∫ x in cell c, f x * φ x = inner ℝ f (mulW c (-m) m φ) := by
  rw [real_inner_comm, inner_mulW_neg]

/-- The negative space of the `X_m`-pivot convention (`paper/main.tex:9385`): the dual of `H^1_m`,
with `X_m ∋ f ↦ ⟪f, ·⟫_{X_m}` (`pivotSourceCLM`). -/
abbrev HnegPivot (c m : ℝ) : Type := H1 c m →L[ℝ] ℝ

/-- The pivot representation `ψ ↦ ⟪f, ψ⟫_{X_m}` of `f ∈ X_m`. -/
def pivotSourceCLM (c m : ℝ) : X c m →L[ℝ] HnegPivot c m :=
  pairCLM c m (H1.valueCLM c m) H1.norm_value_le

theorem pivotSourceCLM_apply (c m : ℝ) (f : X c m) (ψ : H1 c m) :
    pivotSourceCLM c m f ψ = inner ℝ f ψ.value := rfl

/-- A bounded map `H^1_{-m} → H^1_m` acting on values as the weight conjugation
`φ ↦ ⟨x⟩^{-2m} φ`. -/
def IsWeightMultiplier (c m : ℝ) (M : H1 c (-m) →L[ℝ] H1 c m) : Prop :=
  ∀ φ : H1 c (-m), (M φ).value = mulW c (-m) m φ.value

/-- Through a weight multiplier, the pivot representation of `f` is its unweighted
representation: `⟪f, ⟨x⟩^{-2m} φ⟫_{X_m} = ∫_cell f φ`. -/
theorem pivotSourceCLM_comp (c m : ℝ) {M : H1 c (-m) →L[ℝ] H1 c m}
    (hM : IsWeightMultiplier c m M) (f : X c m) :
    (pivotSourceCLM c m f).comp M = sourceCLM c m f := by
  ext φ
  rw [ContinuousLinearMap.comp_apply, pivotSourceCLM_apply, hM, sourceCLM_apply,
    unweighted_eq_inner_conj]

/-- The transpose of an isomorphism `M : H^1_{-m} ≃ H^1_m` identifies the two negative spaces. -/
def pivotEquiv {c m : ℝ} (M : H1 c (-m) ≃L[ℝ] H1 c m) : HnegPivot c m ≃L[ℝ] Hneg c m :=
  M.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)

theorem pivotEquiv_apply {c m : ℝ} (M : H1 c (-m) ≃L[ℝ] H1 c m) (ℓ : HnegPivot c m)
    (φ : H1 c (-m)) : pivotEquiv M ℓ φ = ℓ (M φ) := by
  simp [pivotEquiv]

/-- **The `X_m`-pivot convention is equivalent once both the distribution and the pairing are
conjugated by the weight** (`paper/main.tex:9384-9387`): if the weight conjugation
`φ ↦ ⟨x⟩^{-2m} φ` is an isomorphism `M : H^1_{-m} ≃ H^1_m`, its transpose carries the pivot
representation of each `f ∈ X_m` to its unweighted representation in `H^{-1}_m`. -/
theorem pivotEquiv_pivotSourceCLM {c m : ℝ} (M : H1 c (-m) ≃L[ℝ] H1 c m)
    (hM : IsWeightMultiplier c m (M : H1 c (-m) →L[ℝ] H1 c m)) (f : X c m) :
    pivotEquiv M (pivotSourceCLM c m f) = sourceCLM c m f := by
  ext φ
  rw [pivotEquiv_apply, ← pivotSourceCLM_comp c m hM f]
  rfl

open Real

/-! ### A smooth periodic approximation of `q̃²` -/

/-- `(c/π)² arcsin(t sin(πq/c))²`; for `t → 1⁻` it tends to `q̃²`, the square of the centered
representative of `q mod c`. -/
def sApprox (c t q : ℝ) : ℝ := (c / π) ^ 2 * arcsin (t * sin (π * q / c)) ^ 2

/-- Its derivative. -/
def sDeriv (c t q : ℝ) : ℝ :=
  (c / π) ^ 2 * (2 * arcsin (t * sin (π * q / c)) *
    (1 / √(1 - (t * sin (π * q / c)) ^ 2) * (t * (cos (π * q / c) * (π / c)))))

theorem abs_t_sin_lt {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (y : ℝ) : |t * sin y| < 1 := by
  rw [abs_mul, abs_of_nonneg ht0]
  calc t * |sin y| ≤ t * 1 := by gcongr; exact abs_sin_le_one y
    _ < 1 := by linarith

theorem hasDerivAt_sApprox (c : ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (q : ℝ) :
    HasDerivAt (sApprox c t) (sDeriv c t q) q := by
  have hu := abs_t_sin_lt ht0 ht1 (π * q / c)
  have h1 : HasDerivAt (fun q : ℝ => π * q / c) (π / c) q := by
    simpa using ((hasDerivAt_id q).const_mul π).div_const c
  have h2 : HasDerivAt (fun q : ℝ => t * sin (π * q / c)) (t * (cos (π * q / c) * (π / c))) q :=
    ((hasDerivAt_sin _).comp q h1).const_mul t
  have h3 : HasDerivAt (fun q : ℝ => arcsin (t * sin (π * q / c)))
      (1 / √(1 - (t * sin (π * q / c)) ^ 2) * (t * (cos (π * q / c) * (π / c)))) q :=
    (hasDerivAt_arcsin (by intro h; rw [h] at hu; norm_num at hu)
      (by intro h; rw [h] at hu; norm_num at hu)).comp q h2
  have h4 := (h3.pow 2).const_mul ((c / π) ^ 2)
  have e : sDeriv c t q = (c / π) ^ 2 * (((2 : ℕ) : ℝ) * arcsin (t * sin (π * q / c)) ^ (2 - 1) *
      (1 / √(1 - (t * sin (π * q / c)) ^ 2) * (t * (cos (π * q / c) * (π / c))))) := by
    unfold sDeriv
    norm_num
  rw [e]
  exact h4

theorem contDiff_sApprox (c : ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ContDiff ℝ ∞ (sApprox c t) := by
  have hin : ContDiff ℝ ∞ fun q : ℝ => t * sin (π * q / c) := by fun_prop
  have harc : ContDiff ℝ ∞ fun q : ℝ => arcsin (t * sin (π * q / c)) := by
    rw [contDiff_iff_contDiffAt]
    intro q
    have hu := abs_t_sin_lt ht0 ht1 (π * q / c)
    exact (contDiffAt_arcsin (by intro h; rw [h] at hu; norm_num at hu)
      (by intro h; rw [h] at hu; norm_num at hu)).comp q hin.contDiffAt
  unfold sApprox
  exact contDiff_const.mul (harc.pow 2)

theorem sApprox_periodic {c : ℝ} (hc : c ≠ 0) (t q : ℝ) : sApprox c t (q + c) = sApprox c t q := by
  have : π * (q + c) / c = π * q / c + π := by field_simp
  simp only [sApprox, this, sin_add_pi, mul_neg, arcsin_neg, neg_sq]

theorem sApprox_nonneg (c t q : ℝ) : 0 ≤ sApprox c t q := by
  unfold sApprox
  positivity

theorem sApprox_le (c t q : ℝ) : sApprox c t q ≤ c ^ 2 / 4 := by
  unfold sApprox
  have h1 := arcsin_le_pi_div_two (t * sin (π * q / c))
  have h2 := neg_pi_div_two_le_arcsin (t * sin (π * q / c))
  have hsq : arcsin (t * sin (π * q / c)) ^ 2 ≤ (π / 2) ^ 2 := by
    exact sq_le_sq' h2 h1
  calc (c / π) ^ 2 * arcsin (t * sin (π * q / c)) ^ 2 ≤ (c / π) ^ 2 * (π / 2) ^ 2 := by
        gcongr
    _ = c ^ 2 / 4 := by field_simp; ring

theorem abs_sDeriv_le {c : ℝ} (hc : 0 < c) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (q : ℝ) :
    |sDeriv c t q| ≤ c := by
  set y := π * q / c
  have hu := abs_t_sin_lt ht0 ht1 y
  have hpos : 0 < 1 - (t * sin y) ^ 2 := by
    have : (t * sin y) ^ 2 < 1 := by
      rw [← sq_abs]; nlinarith [abs_nonneg (t * sin y)]
    linarith
  have hsqrt : 0 < √(1 - (t * sin y) ^ 2) := Real.sqrt_pos.2 hpos
  have hratio : |t * cos y| ≤ √(1 - (t * sin y) ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    have := sin_sq_add_cos_sq y
    have ht2 : t ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg (sin y), sq_nonneg (cos y)]
  have harc : |arcsin (t * sin y)| ≤ π / 2 :=
    abs_le.2 ⟨neg_pi_div_two_le_arcsin _, arcsin_le_pi_div_two _⟩
  have hpi : 0 < π := pi_pos
  unfold sDeriv
  rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (c / π) ^ 2),
    abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos (by positivity : 0 < 1 / √(1 - (t * sin y) ^ 2))]
  have hq : |t * (cos y * (π / c))| = |t * cos y| * (π / c) := by
    rw [← mul_assoc, abs_mul, abs_of_pos (by positivity : 0 < π / c)]
  rw [hq]
  have hr : 1 / √(1 - (t * sin y) ^ 2) * (|t * cos y| * (π / c)) ≤ π / c := by
    rw [← mul_assoc]
    have : 1 / √(1 - (t * sin y) ^ 2) * |t * cos y| ≤ 1 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_one hsqrt]
      exact hratio
    calc 1 / √(1 - (t * sin y) ^ 2) * |t * cos y| * (π / c) ≤ 1 * (π / c) := by gcongr
      _ = π / c := one_mul _
  calc (c / π) ^ 2 * (2 * |arcsin (t * sin y)| *
        (1 / √(1 - (t * sin y) ^ 2) * (|t * cos y| * (π / c))))
      ≤ (c / π) ^ 2 * (2 * (π / 2) * (π / c)) := by gcongr
    _ = c := by field_simp

/-- `y = πq/c` lies in `(-π/2, π/2)` when `|q| < c/2`. -/
theorem mem_Ioo_of_abs_lt {c : ℝ} (hc : 0 < c) {q : ℝ} (hq : |q| < c / 2) :
    π * q / c ∈ Ioo (-(π / 2)) (π / 2) := by
  have hpi : 0 < π := pi_pos
  rw [abs_lt] at hq
  constructor
  · rw [lt_div_iff₀ hc]; nlinarith
  · rw [div_lt_iff₀ hc]; nlinarith

theorem tendsto_sApprox {c : ℝ} (hc : 0 < c) {q : ℝ} (hq : |q| < c / 2) :
    Tendsto (fun t => sApprox c t q) (𝓝 1) (𝓝 (q ^ 2)) := by
  have hcont : Continuous fun t => sApprox c t q := by unfold sApprox; fun_prop
  have h1 := hcont.tendsto 1
  have hy := mem_Ioo_of_abs_lt hc hq
  have hval : sApprox c 1 q = q ^ 2 := by
    rw [sApprox, one_mul, arcsin_sin hy.1.le hy.2.le]
    field_simp
  rwa [hval] at h1

theorem tendsto_sDeriv {c : ℝ} (hc : 0 < c) {q : ℝ} (hq : |q| < c / 2) :
    Tendsto (fun t => sDeriv c t q) (𝓝 1) (𝓝 (2 * q)) := by
  set y := π * q / c with hy_def
  have hy := mem_Ioo_of_abs_lt hc hq
  have hcos : 0 < cos y := cos_pos_of_mem_Ioo hy
  have hsq : 1 - (1 * sin y) ^ 2 = cos y ^ 2 := by
    rw [one_mul]; nlinarith [sin_sq_add_cos_sq y]
  have hden : √(1 - (1 * sin y) ^ 2) ≠ 0 := by
    rw [hsq, Real.sqrt_sq hcos.le]; exact hcos.ne'
  have hc1 : ContinuousAt (fun t : ℝ => √(1 - (t * sin y) ^ 2)) 1 := by fun_prop
  have hc2 : ContinuousAt (fun t : ℝ => 1 / √(1 - (t * sin y) ^ 2)) 1 :=
    continuousAt_const.div hc1 hden
  have hc3 : ContinuousAt (fun t => sDeriv c t q) 1 := by
    unfold sDeriv
    refine continuousAt_const.mul (ContinuousAt.mul (by fun_prop) (hc2.mul (by fun_prop)))
  have h1 := hc3.tendsto
  have hval : sDeriv c 1 q = 2 * q := by
    have hcos' : cos (π * q / c) ≠ 0 := by rw [← hy_def]; exact hcos.ne'
    rw [sDeriv, ← hy_def, hsq, Real.sqrt_sq hcos.le, one_mul, arcsin_sin hy.1.le hy.2.le, hy_def]
    field_simp
  rwa [hval] at h1

/-- The parameters `t_n = 1 - 1/(n+2) ∈ [0, 1)`, `t_n → 1`. -/
def tSeq (n : ℕ) : ℝ := 1 - 1 / ((n : ℝ) + 2)

theorem tSeq_nonneg (n : ℕ) : 0 ≤ tSeq n := by
  unfold tSeq
  have : 1 / ((n : ℝ) + 2) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  linarith

theorem tSeq_lt_one (n : ℕ) : tSeq n < 1 := by
  unfold tSeq
  have : 0 < 1 / ((n : ℝ) + 2) := by positivity
  linarith

theorem tendsto_tSeq : Tendsto tSeq atTop (𝓝 1) := by
  have h0 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
  have h : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    refine h0.congr fun n => ?_
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    ring
  have h2 := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub h
  rw [sub_zero] at h2
  exact h2

/-! ### Smooth periodic weights `b_t = (1 + s_t(q) + η²)^k` and their limit `jb^k` -/

/-- The smooth `c`-periodic weight `(1 + s_t(q) + η²)^k`. -/
def bApprox (c t k : ℝ) (x : Plane) : ℝ := (1 + sApprox c t x.1 + x.2 ^ 2) ^ k

theorem bBase_pos (c t : ℝ) (x : Plane) : 0 < 1 + sApprox c t x.1 + x.2 ^ 2 := by
  have := sApprox_nonneg c t x.1
  positivity

theorem contDiff_bApprox (c : ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (k : ℝ) :
    ContDiff ℝ ∞ (bApprox c t k) := by
  have h : ContDiff ℝ ∞ (fun x : Plane => 1 + sApprox c t x.1 + x.2 ^ 2) :=
    (contDiff_const.add ((contDiff_sApprox c ht0 ht1).comp contDiff_fst)).add (contDiff_snd.pow 2)
  exact h.rpow_const_of_ne fun x => (bBase_pos c t x).ne'

theorem bApprox_periodic {c : ℝ} (hc : c ≠ 0) (t k : ℝ) (x : Plane) :
    bApprox c t k (x.1 + c, x.2) = bApprox c t k x := by
  simp only [bApprox, sApprox_periodic hc]

theorem pd_zero_bApprox (c : ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (k : ℝ) (x : Plane) :
    pd 0 (bApprox c t k) x =
      sDeriv c t x.1 * k * (1 + sApprox c t x.1 + x.2 ^ 2) ^ (k - 1) := by
  obtain ⟨q, η⟩ := x
  have h1 := hasDerivAt_fst ((contDiff_bApprox c ht0 ht1 k).differentiable (by simp)) q η
  have h2 : HasDerivAt (fun s => bApprox c t k (s, η))
      (sDeriv c t q * k * (1 + sApprox c t q + η ^ 2) ^ (k - 1)) q :=
    (((hasDerivAt_sApprox c ht0 ht1 q).const_add 1).add_const (η ^ 2)).rpow_const
      (Or.inl (bBase_pos c t (q, η)).ne')
  exact h1.unique h2

theorem pd_one_bApprox (c : ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (k : ℝ) (x : Plane) :
    pd 1 (bApprox c t k) x =
      2 * x.2 * k * (1 + sApprox c t x.1 + x.2 ^ 2) ^ (k - 1) := by
  obtain ⟨q, η⟩ := x
  have h1 := hasDerivAt_snd ((contDiff_bApprox c ht0 ht1 k).differentiable (by simp)) q η
  have h2 : HasDerivAt (fun s => bApprox c t k (q, s))
      (((2 : ℕ) : ℝ) * η ^ (2 - 1) * k * (1 + sApprox c t q + η ^ 2) ^ (k - 1)) η :=
    ((hasDerivAt_pow 2 η).const_add (1 + sApprox c t q)).rpow_const
      (Or.inl (bBase_pos c t (q, η)).ne')
  rw [h1.unique h2]
  norm_num

theorem contDiff_jb : ContDiff ℝ ∞ jb := by
  unfold jb
  fun_prop

theorem contDiff_jb_rpow (k : ℝ) : ContDiff ℝ ∞ fun x => jb x ^ k :=
  contDiff_jb.rpow_const_of_ne fun x => (jb_pos x).ne'

theorem pd_zero_jb_rpow (k : ℝ) (x : Plane) :
    pd 0 (fun x => jb x ^ k) x = 2 * x.1 * k * jb x ^ (k - 1) := by
  obtain ⟨q, η⟩ := x
  have h1 := hasDerivAt_fst ((contDiff_jb_rpow k).differentiable (by simp)) q η
  have h2 : HasDerivAt (fun s => jb (s, η) ^ k)
      (((2 : ℕ) : ℝ) * q ^ (2 - 1) * k * jb (q, η) ^ (k - 1)) q :=
    (((hasDerivAt_pow 2 q).const_add 1).add_const (η ^ 2)).rpow_const (Or.inl (jb_pos (q, η)).ne')
  rw [h1.unique h2]
  norm_num

theorem pd_one_jb_rpow (k : ℝ) (x : Plane) :
    pd 1 (fun x => jb x ^ k) x = 2 * x.2 * k * jb x ^ (k - 1) := by
  obtain ⟨q, η⟩ := x
  have h1 := hasDerivAt_snd ((contDiff_jb_rpow k).differentiable (by simp)) q η
  have h2 : HasDerivAt (fun s => jb (q, s) ^ k)
      (((2 : ℕ) : ℝ) * η ^ (2 - 1) * k * jb (q, η) ^ (k - 1)) η :=
    ((hasDerivAt_pow 2 η).const_add (1 + q ^ 2)).rpow_const (Or.inl (jb_pos (q, η)).ne')
  rw [h1.unique h2]
  norm_num

theorem rpow_le_rpow_abs {b M k : ℝ} (hb : 1 ≤ b) (hbM : b ≤ M) : b ^ k ≤ M ^ |k| := by
  rcases le_or_gt 0 k with hk | hk
  · rw [abs_of_nonneg hk]
    exact Real.rpow_le_rpow (by linarith) hbM hk
  · calc b ^ k ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hb hk.le
      _ ≤ M ^ |k| := Real.one_le_rpow (hb.trans hbM) (abs_nonneg k)

theorem bBase_mem {c t R : ℝ} {x : Plane} (hx : |x.2| ≤ R) :
    1 ≤ 1 + sApprox c t x.1 + x.2 ^ 2 ∧ 1 + sApprox c t x.1 + x.2 ^ 2 ≤ 1 + c ^ 2 / 4 + R ^ 2 := by
  have h1 := sApprox_nonneg c t x.1
  have h2 := sApprox_le c t x.1
  have h3 : x.2 ^ 2 ≤ R ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hx 2
  constructor <;> nlinarith [sq_nonneg x.2]

/-- Uniform bounds for the approximating weights on a band `|η| ≤ R`. -/
theorem bApprox_bounds {c : ℝ} (hc : 0 < c) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (k R : ℝ)
    (x : Plane) (hx : |x.2| ≤ R) :
    |bApprox c t k x| ≤ (1 + c ^ 2 / 4 + R ^ 2) ^ |k| ∧
    |pd 0 (bApprox c t k) x| ≤ c * |k| * (1 + c ^ 2 / 4 + R ^ 2) ^ |k - 1| ∧
    |pd 1 (bApprox c t k) x| ≤ 2 * R * |k| * (1 + c ^ 2 / 4 + R ^ 2) ^ |k - 1| := by
  obtain ⟨hb1, hbM⟩ := bBase_mem (c := c) (t := t) hx
  have hbpos : 0 < 1 + sApprox c t x.1 + x.2 ^ 2 := by linarith
  have hp1 : |(1 + sApprox c t x.1 + x.2 ^ 2) ^ (k - 1)| ≤ (1 + c ^ 2 / 4 + R ^ 2) ^ |k - 1| := by
    rw [abs_of_pos (Real.rpow_pos_of_pos hbpos _)]
    exact rpow_le_rpow_abs hb1 hbM
  refine ⟨?_, ?_, ?_⟩
  · rw [bApprox, abs_of_pos (Real.rpow_pos_of_pos hbpos _)]
    exact rpow_le_rpow_abs hb1 hbM
  · rw [pd_zero_bApprox c ht0 ht1, abs_mul, abs_mul]
    have := abs_sDeriv_le hc ht0 ht1 x.1
    gcongr
  · rw [pd_one_bApprox c ht0 ht1, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hR : 0 ≤ R := (abs_nonneg _).trans hx
    gcongr

theorem tendsto_bApprox {c : ℝ} (hc : 0 < c) (k : ℝ) {x : Plane} (hx : |x.1| < c / 2) :
    Tendsto (fun n => bApprox c (tSeq n) k x) atTop (𝓝 (jb x ^ k)) ∧
    Tendsto (fun n => pd 0 (bApprox c (tSeq n) k) x) atTop (𝓝 (pd 0 (fun x => jb x ^ k) x)) ∧
    Tendsto (fun n => pd 1 (bApprox c (tSeq n) k) x) atTop
      (𝓝 (pd 1 (fun x => jb x ^ k) x)) := by
  have hs := (tendsto_sApprox hc hx).comp tendsto_tSeq
  have hd := (tendsto_sDeriv hc hx).comp tendsto_tSeq
  have hbase : Tendsto (fun n => 1 + sApprox c (tSeq n) x.1 + x.2 ^ 2) atTop (𝓝 (jb x)) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).add hs).add (tendsto_const_nhds (x := x.2 ^ 2))
    simpa [jb, Function.comp_def] using this
  have hpow : ∀ p : ℝ, Tendsto (fun n => (1 + sApprox c (tSeq n) x.1 + x.2 ^ 2) ^ p) atTop
      (𝓝 (jb x ^ p)) := fun p => hbase.rpow_const (Or.inl (jb_pos x).ne')
  refine ⟨hpow k, ?_, ?_⟩
  · rw [pd_zero_jb_rpow]
    have e : (fun n => pd 0 (bApprox c (tSeq n) k) x) = fun n =>
        sDeriv c (tSeq n) x.1 * k * (1 + sApprox c (tSeq n) x.1 + x.2 ^ 2) ^ (k - 1) :=
      funext fun n => pd_zero_bApprox c (tSeq_nonneg n) (tSeq_lt_one n) k x
    rw [e]
    exact (hd.mul tendsto_const_nhds).mul (hpow (k - 1))
  · rw [pd_one_jb_rpow]
    have e : (fun n => pd 1 (bApprox c (tSeq n) k) x) = fun n =>
        2 * x.2 * k * (1 + sApprox c (tSeq n) x.1 + x.2 ^ 2) ^ (k - 1) :=
      funext fun n => pd_one_bApprox c (tSeq_nonneg n) (tSeq_lt_one n) k x
    rw [e]
    exact tendsto_const_nhds.mul (hpow (k - 1))

/-! ### Product rule for weak derivatives with a weight approximable by smooth periodic ones -/

theorem contDiff_pd {φ : Plane → ℝ} (hφ : ContDiff ℝ ∞ φ) (j : Fin 2) : ContDiff ℝ ∞ (pd j φ) :=
  ((contDiff_infty_iff_fderiv.1 hφ).2).clm_apply contDiff_const

theorem IsCylTest.exists_band_pd {c : ℝ} {χ : Plane → ℝ} (hχ : IsCylTest c χ) (j : Fin 2) :
    ∃ R : ℝ, ∀ x : Plane, R < |x.2| → χ x = 0 ∧ B0579.pd j χ x = 0 := by
  obtain ⟨R1, h1⟩ := hχ.band
  obtain ⟨R2, h2⟩ := (hχ.pd j).band
  exact ⟨max R1 R2, fun x hx =>
    ⟨h1 x (lt_of_le_of_lt (le_max_left _ _) hx), h2 x (lt_of_le_of_lt (le_max_right _ _) hx)⟩⟩

theorem exists_bound_cell_band (c R : ℝ) {h : Plane → ℝ} (hh : Continuous h) :
    ∃ K : ℝ, ∀ x ∈ cell c, |x.2| ≤ R → |h x| ≤ K := by
  obtain ⟨K, hK⟩ := (isCompact_box c R).exists_bound_of_continuousOn hh.continuousOn
  exact ⟨K, fun x hx hxR => by simpa using hK x (mem_box_of_mem_cell hx hxR)⟩

/-- The band `|η| ≤ R`. -/
def band (R : ℝ) : Set Plane := {x : Plane | |x.2| ≤ R}

theorem measurableSet_band (R : ℝ) : MeasurableSet (band R) :=
  measurableSet_le (continuous_abs.comp continuous_snd).measurable measurable_const

theorem integrable_band_indicator {c R : ℝ} {f : Plane → ℝ}
    (hf : IntegrableOn f (band R ∩ cell c)) :
    Integrable ((band R).indicator fun x => |f x|) (volume.restrict (cell c)) := by
  rw [integrable_indicator_iff (measurableSet_band R), IntegrableOn,
    Measure.restrict_restrict (measurableSet_band R)]
  exact hf.abs

/-- A locally integrable `f` times a continuous function vanishing for `|η| > R` is integrable. -/
theorem integrableOn_mul_band {c R : ℝ} {f h : Plane → ℝ}
    (hfm : AEStronglyMeasurable f (volume.restrict (cell c)))
    (hf : IntegrableOn f (band R ∩ cell c)) (hh : Continuous h)
    (hv : ∀ x : Plane, R < |x.2| → h x = 0) :
    IntegrableOn (fun x => f x * h x) (cell c) := by
  obtain ⟨K, hK⟩ := exists_bound_cell_band c R hh
  refine Integrable.mono' ((integrable_band_indicator hf).const_mul K)
    (hfm.mul hh.aestronglyMeasurable) ?_
  refine (ae_restrict_iff' (measurableSet_cell c)).2 (Eventually.of_forall fun x hx => ?_)
  by_cases hxR : |x.2| ≤ R
  · have hk := hK x hx hxR
    rw [indicator_of_mem (show x ∈ band R from hxR), Real.norm_eq_abs, abs_mul, mul_comm K]
    exact mul_le_mul_of_nonneg_left hk (abs_nonneg _)
  · rw [hv x (not_le.1 hxR), mul_zero, norm_zero, indicator_of_notMem (show x ∉ band R from hxR),
      mul_zero]

theorem abs_mul_add_le {a b c' d C K1 K2 : ℝ} (ha : |a| ≤ C) (hb : |b| ≤ K1) (hc : |c'| ≤ C)
    (hd : |d| ≤ K2) : |a * b + c' * d| ≤ C * K1 + C * K2 := by
  have hC : 0 ≤ C := (abs_nonneg _).trans ha
  calc |a * b + c' * d| ≤ |a * b| + |c' * d| := abs_add_le _ _
    _ = |a| * |b| + |c'| * |d| := by rw [abs_mul, abs_mul]
    _ ≤ C * K1 + C * K2 :=
      add_le_add (mul_le_mul ha hb (abs_nonneg _) hC) (mul_le_mul hc hd (abs_nonneg _) hC)

/-- **Product rule.** If `(f, g)` is a weak-derivative pair on the cylinder and the weight `B`
(with candidate derivative `β`) is the a.e. limit on the cell of smooth `c`-periodic weights `b n`
whose values and `j`-derivatives converge a.e. and are bounded uniformly on bands, then
`∂_j (B f) = B g + β f` weakly. -/
theorem HasWeakCellDeriv.weight_mul {c : ℝ} {j : Fin 2} {f g : Plane → ℝ}
    (h : HasWeakCellDeriv c j f g)
    (hfm : AEStronglyMeasurable f (volume.restrict (cell c)))
    (hgm : AEStronglyMeasurable g (volume.restrict (cell c)))
    (hfloc : ∀ R : ℝ, IntegrableOn f (band R ∩ cell c))
    (hgloc : ∀ R : ℝ, IntegrableOn g (band R ∩ cell c))
    {b : ℕ → Plane → ℝ} (hb : ∀ n, ContDiff ℝ ∞ (b n))
    (hbper : ∀ n (x : Plane), b n (x.1 + c, x.2) = b n x)
    (hbd : ∀ R : ℝ, ∃ C : ℝ, ∀ n, ∀ x ∈ cell c, |x.2| ≤ R → |b n x| ≤ C ∧ |pd j (b n) x| ≤ C)
    {B β : Plane → ℝ} (hB : Continuous B) (hβ : Continuous β)
    (hlim : ∀ᵐ x ∂(volume.restrict (cell c)), Tendsto (fun n => b n x) atTop (𝓝 (B x)) ∧
      Tendsto (fun n => pd j (b n) x) atTop (𝓝 (β x))) :
    HasWeakCellDeriv c j (fun x => B x * f x) (fun x => B x * g x + β x * f x) := by
  intro χ hχ
  obtain ⟨R, hR⟩ := hχ.exists_band_pd j
  obtain ⟨C, hC⟩ := hbd R
  obtain ⟨K1, hK1⟩ := exists_bound_cell_band c R hχ.continuous
  obtain ⟨K2, hK2⟩ := exists_bound_cell_band c R (hχ.pd j).continuous
  have hθ : ∀ n, IsCylTest c (fun x => b n x * χ x) := fun n =>
    ⟨(hb n).mul hχ.smooth, fun x => by simp only [hbper n x, hχ.periodic x],
      ⟨R, fun x hx => by simp [(hR x hx).1]⟩⟩
  have hid : ∀ n, ∫ x in cell c, f x * (pd j (b n) x * χ x + b n x * pd j χ x) =
      -∫ x in cell c, g x * (b n x * χ x) := by
    intro n
    rw [← h _ (hθ n)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [pd_mul ((hb n).differentiable (by simp)) hχ.differentiable j x]
  have hF : Tendsto (fun n => ∫ x in cell c, f x * (pd j (b n) x * χ x + b n x * pd j χ x))
      atTop (𝓝 (∫ x in cell c, f x * (β x * χ x + B x * pd j χ x))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => (C * K1 + C * K2) * (band R).indicator (fun x => |f x|) x) (fun n => ?_)
      ((integrable_band_indicator (hfloc R)).const_mul _) (fun n => ?_) ?_
    · exact hfm.mul ((((contDiff_pd (hb n) j).continuous.mul hχ.continuous).add
        ((hb n).continuous.mul (hχ.pd j).continuous)).aestronglyMeasurable)
    · refine (ae_restrict_iff' (measurableSet_cell c)).2 (Eventually.of_forall fun x hx => ?_)
      by_cases hxR : |x.2| ≤ R
      · rw [indicator_of_mem (show x ∈ band R from hxR), Real.norm_eq_abs, abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (abs_mul_add_le (hC n x hx hxR).2 (hK1 x hx hxR)
          (hC n x hx hxR).1 (hK2 x hx hxR)) (abs_nonneg _)
      · have h0 := hR x (not_le.1 hxR)
        rw [h0.1, h0.2, indicator_of_notMem (show x ∉ band R from hxR)]
        simp
    · filter_upwards [hlim] with x hx
      exact tendsto_const_nhds.mul ((hx.2.mul tendsto_const_nhds).add
        (hx.1.mul tendsto_const_nhds))
  have hG : Tendsto (fun n => ∫ x in cell c, g x * (b n x * χ x))
      atTop (𝓝 (∫ x in cell c, g x * (B x * χ x))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => (C * K1) * (band R).indicator (fun x => |g x|) x) (fun n => ?_)
      ((integrable_band_indicator (hgloc R)).const_mul _) (fun n => ?_) ?_
    · exact hgm.mul (((hb n).continuous.mul hχ.continuous).aestronglyMeasurable)
    · refine (ae_restrict_iff' (measurableSet_cell c)).2 (Eventually.of_forall fun x hx => ?_)
      by_cases hxR : |x.2| ≤ R
      · rw [indicator_of_mem (show x ∈ band R from hxR), Real.norm_eq_abs, abs_mul, mul_comm,
          abs_mul]
        have hCn := (hC n x hx hxR).1
        have hC0 : 0 ≤ C := (abs_nonneg _).trans hCn
        exact mul_le_mul_of_nonneg_right (mul_le_mul hCn (hK1 x hx hxR) (abs_nonneg _) hC0)
          (abs_nonneg _)
      · have h0 := hR x (not_le.1 hxR)
        rw [h0.1, indicator_of_notMem (show x ∉ band R from hxR)]
        simp
    · filter_upwards [hlim] with x hx
      exact tendsto_const_nhds.mul (hx.1.mul tendsto_const_nhds)
  have hF' : Tendsto (fun n => -∫ x in cell c, g x * (b n x * χ x)) atTop
      (𝓝 (∫ x in cell c, f x * (β x * χ x + B x * pd j χ x))) := by
    rw [show (fun n => -∫ x in cell c, g x * (b n x * χ x)) = fun n =>
      ∫ x in cell c, f x * (pd j (b n) x * χ x + b n x * pd j χ x) from funext fun n => (hid n).symm]
    exact hF
  have hlimeq := tendsto_nhds_unique hF' hG.neg
  -- integrability of the pieces
  have i1 : IntegrableOn (fun x => f x * (β x * χ x)) (cell c) :=
    integrableOn_mul_band hfm (hfloc R) (hβ.mul hχ.continuous) fun x hx => by simp [(hR x hx).1]
  have i2 : IntegrableOn (fun x => f x * (B x * pd j χ x)) (cell c) :=
    integrableOn_mul_band hfm (hfloc R) (hB.mul (hχ.pd j).continuous) fun x hx => by
      simp [(hR x hx).2]
  have i3 : IntegrableOn (fun x => g x * (B x * χ x)) (cell c) :=
    integrableOn_mul_band hgm (hgloc R) (hB.mul hχ.continuous) fun x hx => by simp [(hR x hx).1]
  have hsplit : ∫ x in cell c, f x * (β x * χ x + B x * pd j χ x) =
      (∫ x in cell c, f x * (β x * χ x)) + ∫ x in cell c, f x * (B x * pd j χ x) := by
    rw [← integral_add i1 i2]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
  have hL : ∫ x in cell c, B x * f x * pd j χ x = ∫ x in cell c, f x * (B x * pd j χ x) :=
    integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
  have hRhs : ∫ x in cell c, (B x * g x + β x * f x) * χ x =
      (∫ x in cell c, g x * (B x * χ x)) + ∫ x in cell c, f x * (β x * χ x) := by
    rw [← integral_add i3 i1]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
  rw [hL, hRhs]
  rw [hsplit] at hlimeq
  linarith

/-! ### The product rule for the weight `⟨x⟩^{2k} = jb^k` of the centered cell -/

/-- Almost every point of the cell lies off the seam `q = -c/2`. -/
theorem ae_cell_abs_fst_lt (c : ℝ) : ∀ᵐ x ∂(volume.restrict (cell c)), |x.1| < c / 2 := by
  have h0 : ∀ᵐ x ∂(volume : Measure Plane), x.1 ≠ -(c / 2) := by
    rw [ae_iff]
    have : {x : Plane | ¬x.1 ≠ -(c / 2)} = {-(c / 2)} ×ˢ univ := by
      ext x
      simp
    rw [this, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]
  filter_upwards [ae_restrict_mem (measurableSet_cell c), ae_restrict_of_ae h0] with x hx hne
  rw [abs_lt]
  exact ⟨lt_of_le_of_ne hx.1.1 (Ne.symm hne), hx.1.2⟩

theorem HasWeakCellDeriv.jb_rpow_mul {c : ℝ} (hc : 0 < c) (k : ℝ) {j : Fin 2} {f g : Plane → ℝ}
    (h : HasWeakCellDeriv c j f g)
    (hfm : AEStronglyMeasurable f (volume.restrict (cell c)))
    (hgm : AEStronglyMeasurable g (volume.restrict (cell c)))
    (hfloc : ∀ R : ℝ, IntegrableOn f (band R ∩ cell c))
    (hgloc : ∀ R : ℝ, IntegrableOn g (band R ∩ cell c)) :
    HasWeakCellDeriv c j (fun x => jb x ^ k * f x)
      (fun x => jb x ^ k * g x + pd j (fun x => jb x ^ k) x * f x) := by
  refine h.weight_mul hfm hgm hfloc hgloc (b := fun n => bApprox c (tSeq n) k)
    (fun n => contDiff_bApprox c (tSeq_nonneg n) (tSeq_lt_one n) k)
    (fun n x => bApprox_periodic hc.ne' _ k x) ?_ (continuous_jb_rpow k)
    (contDiff_pd (contDiff_jb_rpow k) j).continuous ?_
  · intro R
    refine ⟨(1 + c ^ 2 / 4 + R ^ 2) ^ |k| + (c + 2 * R) * |k| * (1 + c ^ 2 / 4 + R ^ 2) ^ |k - 1|,
      fun n x _ hxR => ?_⟩
    have hR : 0 ≤ R := (abs_nonneg _).trans hxR
    obtain ⟨h1, h2, h3⟩ := bApprox_bounds hc (tSeq_nonneg n) (tSeq_lt_one n) k R x hxR
    have hP : 0 ≤ |k| * (1 + c ^ 2 / 4 + R ^ 2) ^ |k - 1| := by positivity
    have hQ : 0 ≤ (1 + c ^ 2 / 4 + R ^ 2) ^ |k| := by positivity
    refine ⟨by nlinarith, ?_⟩
    fin_cases j
    · simp only [Fin.zero_eta] at h2 ⊢
      nlinarith
    · simp only [Fin.mk_one] at h3 ⊢
      nlinarith
  · filter_upwards [ae_cell_abs_fst_lt c] with x hx
    have := tendsto_bApprox hc k hx
    fin_cases j
    · exact ⟨this.1, this.2.1⟩
    · exact ⟨this.1, this.2.2⟩

/-! ### Local integrability of elements of `X_m` -/

theorem memLp_indicator_band (c m R : ℝ) :
    MemLp ((band R).indicator fun _ => (1 : ℝ)) 2 (cellMeasure c m) := by
  obtain ⟨K, hK⟩ := (isCompact_box c R).exists_bound_of_continuousOn
    (continuous_jb_rpow (m / 2)).continuousOn
  have hg : MemLp ((box c R).indicator fun _ => |K|) 2 (volume.restrict (cell c)) :=
    memLp_indicator_const 2 (isCompact_box c R).measurableSet _
      (Or.inr (by
        rw [Measure.restrict_apply (isCompact_box c R).measurableSet]
        exact (measure_mono inter_subset_left).trans_lt (isCompact_box c R).measure_lt_top |>.ne))
  have hf : MemLp (fun x => jb x ^ (m / 2) * (band R).indicator (fun _ => (1 : ℝ)) x) 2
      (volume.restrict (cell c)) := by
    refine hg.of_le ((continuous_jb_rpow _).aestronglyMeasurable.mul
      (aestronglyMeasurable_const.indicator (measurableSet_band R))) ?_
    refine (ae_restrict_iff' (measurableSet_cell c)).2 (Eventually.of_forall fun x hx => ?_)
    by_cases hxR : x ∈ band R
    · have hxb : x ∈ box c R := mem_box_of_mem_cell hx hxR
      rw [indicator_of_mem hxR, indicator_of_mem hxb, mul_one, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_abs]
      exact (hK x hxb).trans (le_abs_self K)
    · rw [indicator_of_notMem hxR, mul_zero, norm_zero]
      exact norm_nonneg _
  exact ⟨aestronglyMeasurable_const.indicator (measurableSet_band R),
    by rw [eLpNorm_cellMeasure]; exact hf.2⟩

/-- Elements of `X_m` are integrable on every band of the cell. -/
theorem integrableOn_band_X {c m : ℝ} (f : X c m) (R : ℝ) :
    IntegrableOn (f : Plane → ℝ) (band R ∩ cell c) := by
  have h := integrableOn_mul_neg c m f ((memLp_indicator_band c (-m) R).toLp _)
  have h2 : IntegrableOn (fun x => f x * (band R).indicator (fun _ => (1 : ℝ)) x) (cell c) := by
    refine h.congr_fun_ae ?_
    filter_upwards [(ac_cellMeasure c (-m)).ae_le (MemLp.coeFn_toLp (memLp_indicator_band c (-m) R))]
      with x hx
    rw [hx]
  have h3 : IntegrableOn ((band R).indicator (f : Plane → ℝ)) (cell c) := by
    refine h2.congr_fun (fun x _ => ?_) (measurableSet_cell c)
    by_cases hx : x ∈ band R <;> simp [hx]
  rw [IntegrableOn, integrable_indicator_iff (measurableSet_band R), IntegrableOn,
    Measure.restrict_restrict (measurableSet_band R)] at h3
  exact h3

theorem aestronglyMeasurable_X {c m : ℝ} (f : X c m) :
    AEStronglyMeasurable (f : Plane → ℝ) (volume.restrict (cell c)) :=
  (Lp.aestronglyMeasurable f).mono_ac (ac_cellMeasure c m)

/-- The product rule for `F ∈ H^1_m` and the weight `jb^k = ⟨x⟩^{2k}`. -/
theorem H1.hasWeakCellDeriv_jb_rpow {c m : ℝ} (hc : 0 < c) (k : ℝ) (F : H1 c m) (j : Fin 2) :
    HasWeakCellDeriv c j (fun x => jb x ^ k * F.value x)
      (fun x => jb x ^ k * F.der j x + pd j (fun x => jb x ^ k) x * F.value x) :=
  (F.hasWeakCellDeriv j).jb_rpow_mul hc k (aestronglyMeasurable_X _) (aestronglyMeasurable_X _)
    (integrableOn_band_X _) (integrableOn_band_X _)

/-! ### Bounded multipliers on `X_m` -/

/-- The logarithmic derivative `∂_j(jb^k) / jb^k = 2k x_j / jb` of the weight. -/
def wratio (k : ℝ) (j : Fin 2) (x : Plane) : ℝ := pd j (fun x => jb x ^ k) x / jb x ^ k

theorem pd_jb_rpow_eq (k : ℝ) (j : Fin 2) (x : Plane) :
    pd j (fun x => jb x ^ k) x = jb x ^ k * wratio k j x := by
  rw [wratio, mul_div_cancel₀ _ (Real.rpow_pos_of_pos (jb_pos x) k).ne']

theorem wratio_zero (k : ℝ) (x : Plane) : wratio k 0 x = 2 * x.1 * k / jb x := by
  rw [wratio, pd_zero_jb_rpow, Real.rpow_sub_one (jb_pos x).ne']
  have h1 : 0 < jb x ^ k := Real.rpow_pos_of_pos (jb_pos x) k
  have h2 : 0 < jb x := jb_pos x
  field_simp

theorem wratio_one (k : ℝ) (x : Plane) : wratio k 1 x = 2 * x.2 * k / jb x := by
  rw [wratio, pd_one_jb_rpow, Real.rpow_sub_one (jb_pos x).ne']
  have h1 : 0 < jb x ^ k := Real.rpow_pos_of_pos (jb_pos x) k
  have h2 : 0 < jb x := jb_pos x
  field_simp

theorem wratio_neg (k : ℝ) (j : Fin 2) (x : Plane) : wratio (-k) j x = -wratio k j x := by
  fin_cases j
  · simp only [Fin.zero_eta, wratio_zero]
    ring
  · simp only [Fin.mk_one, wratio_one]
    ring

theorem continuous_wratio (k : ℝ) (j : Fin 2) : Continuous (wratio k j) :=
  (contDiff_pd (contDiff_jb_rpow k) j).continuous.div (continuous_jb_rpow k)
    fun x => (Real.rpow_pos_of_pos (jb_pos x) k).ne'

theorem two_abs_le_jb (x : Plane) : 2 * |x.1| ≤ jb x ∧ 2 * |x.2| ≤ jb x := by
  unfold jb
  constructor
  · nlinarith [sq_nonneg (|x.1| - 1), sq_abs x.1, sq_nonneg x.2]
  · nlinarith [sq_nonneg (|x.2| - 1), sq_abs x.2, sq_nonneg x.1]

theorem abs_wratio_le (k : ℝ) (j : Fin 2) (x : Plane) : |wratio k j x| ≤ |k| := by
  have hj := jb_pos x
  have hb := two_abs_le_jb x
  fin_cases j
  · simp only [Fin.zero_eta, wratio_zero]
    rw [abs_div, abs_of_pos hj, div_le_iff₀ hj, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    nlinarith [abs_nonneg k, abs_nonneg x.1]
  · simp only [Fin.mk_one, wratio_one]
    rw [abs_div, abs_of_pos hj, div_le_iff₀ hj, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    nlinarith [abs_nonneg k, abs_nonneg x.2]

theorem memLp_mulR {c m : ℝ} {r : Plane → ℝ} (hr : Continuous r) {C : ℝ} (hC : ∀ x, |r x| ≤ C)
    (f : X c m) : MemLp (fun x => r x * f x) 2 (cellMeasure c m) := by
  refine ((Lp.memLp f).const_mul C).of_le
    (hr.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)) (Eventually.of_forall fun x => ?_)
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC x)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hC0]
  exact mul_le_mul_of_nonneg_right (hC x) (abs_nonneg _)

/-- Multiplication by a bounded continuous function, `X_m → X_m`. -/
def mulRLM (c m : ℝ) {r : Plane → ℝ} (hr : Continuous r) {C : ℝ} (hC : ∀ x, |r x| ≤ C) :
    X c m →ₗ[ℝ] X c m where
  toFun f := (memLp_mulR hr hC f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_mulR hr hC (f + g)),
      Lp.coeFn_add ((memLp_mulR hr hC f).toLp _) ((memLp_mulR hr hC g).toLp _),
      MemLp.coeFn_toLp (memLp_mulR hr hC f), MemLp.coeFn_toLp (memLp_mulR hr hC g),
      Lp.coeFn_add f g] with x h1 h2 h3 h4 h5
    rw [h1, h2, Pi.add_apply, h3, h4, h5, Pi.add_apply]
    ring
  map_smul' a f := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_mulR hr hC (a • f)),
      Lp.coeFn_smul a ((memLp_mulR hr hC f).toLp _),
      MemLp.coeFn_toLp (memLp_mulR hr hC f), Lp.coeFn_smul a f] with x h1 h2 h3 h4
    rw [h1, RingHom.id_apply, h2, Pi.smul_apply, h3, h4, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    ring

theorem norm_mulRLM_le (c m : ℝ) {r : Plane → ℝ} (hr : Continuous r) {C : ℝ}
    (hC : ∀ x, |r x| ≤ C) (f : X c m) : ‖mulRLM c m hr hC f‖ ≤ C * ‖f‖ := by
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_mulR hr hC f)] with x hx
  change ‖((memLp_mulR hr hC f).toLp _ : Plane → ℝ) x‖ ≤ _
  rw [hx, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hC x) (abs_nonneg _)

/-- The bounded multiplier as a continuous linear map. -/
def mulR (c m : ℝ) {r : Plane → ℝ} (hr : Continuous r) {C : ℝ} (hC : ∀ x, |r x| ≤ C) :
    X c m →L[ℝ] X c m :=
  LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ) (E := X c m) (F := X c m) (σ := RingHom.id ℝ)
    (mulRLM c m hr hC) C (norm_mulRLM_le c m hr hC)

theorem coeFn_mulR (c m : ℝ) {r : Plane → ℝ} (hr : Continuous r) {C : ℝ}
    (hC : ∀ x, |r x| ≤ C) (f : X c m) :
    (mulR c m hr hC f : Plane → ℝ) =ᵐ[cellMeasure c m] fun x => r x * f x :=
  MemLp.coeFn_toLp (memLp_mulR hr hC f)

theorem norm_mulR_le (c m : ℝ) {r : Plane → ℝ} (hr : Continuous r) {C : ℝ}
    (hC : ∀ x, |r x| ≤ C) (f : X c m) : ‖mulR c m hr hC f‖ ≤ C * ‖f‖ :=
  norm_mulRLM_le c m hr hC f

/-- Multiplication by the logarithmic derivative `wratio k j`. -/
def ratioCLM (c m k : ℝ) (j : Fin 2) : X c m →L[ℝ] X c m :=
  mulR c m (continuous_wratio k j) (abs_wratio_le k j)

/-! ### The weight multiplier `H^1_m → H^1_{m'}`, `F ↦ ⟨x⟩^{m - m'} F` -/

namespace H1

variable {c m : ℝ}

theorem ext_comp {F G : H1 c m} (hv : F.value = G.value) (hd : ∀ j, F.der j = G.der j) :
    F = G := by
  apply Subtype.ext
  apply (WithLp.ext_iff (p := 2)).2
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hv
  · exact hd j

@[simp] theorem value_add (F G : H1 c m) : (F + G).value = F.value + G.value := rfl

@[simp] theorem der_add (F G : H1 c m) (j : Fin 2) : (F + G).der j = F.der j + G.der j := rfl

@[simp] theorem value_smul (a : ℝ) (F : H1 c m) : (a • F).value = a • F.value := rfl

@[simp] theorem der_smul (a : ℝ) (F : H1 c m) (j : Fin 2) : (a • F).der j = a • F.der j := rfl

end H1

/-- Value part of the multiplier: `⟨x⟩^{m - m'} f`. -/
def h1MulValue (c m m' : ℝ) : H1 c m →L[ℝ] X c m' :=
  (mulW c m m').toContinuousLinearMap.comp (H1.valueCLM c m)

/-- Derivative part: `⟨x⟩^{m - m'} (∂_j f + (∂_j jb^k / jb^k) f) = jb^k ∂_j f + ∂_j(jb^k) f`,
`k = (m - m')/2`. -/
def h1MulDer (c m m' : ℝ) (j : Fin 2) : H1 c m →L[ℝ] X c m' :=
  (mulW c m m').toContinuousLinearMap.comp
    (H1.derCLM c m j + (ratioCLM c m ((m - m') / 2) j).comp (H1.valueCLM c m))

theorem h1MulValue_apply (c m m' : ℝ) (F : H1 c m) : h1MulValue c m m' F = mulW c m m' F.value :=
  rfl

theorem h1MulDer_apply (c m m' : ℝ) (j : Fin 2) (F : H1 c m) :
    h1MulDer c m m' j F = mulW c m m' (F.der j + ratioCLM c m ((m - m') / 2) j F.value) := rfl

theorem coeFn_h1MulDer (c m m' : ℝ) (j : Fin 2) (F : H1 c m) :
    (h1MulDer c m m' j F : Plane → ℝ) =ᵐ[cellMeasure c m'] fun x =>
      jb x ^ ((m - m') / 2) * F.der j x + pd j (fun x => jb x ^ ((m - m') / 2)) x * F.value x := by
  rw [h1MulDer_apply]
  filter_upwards [coeFn_mulW c m m' (F.der j + ratioCLM c m ((m - m') / 2) j F.value),
    coeFn_ae_cell (m' := m') (Lp.coeFn_add (F.der j) (ratioCLM c m ((m - m') / 2) j F.value)),
    coeFn_ae_cell (m' := m') (coeFn_mulR c m (continuous_wratio ((m - m') / 2) j)
      (abs_wratio_le ((m - m') / 2) j) F.value)] with x h1 h2 h3
  rw [h1, h2, Pi.add_apply]
  change jb x ^ ((m - m') / 2) * (F.der j x + (mulR c m _ _ F.value : Plane → ℝ) x) = _
  rw [h3, pd_jb_rpow_eq]
  ring

theorem mem_H1Sub_h1Mul {c : ℝ} (hc : 0 < c) (m m' : ℝ) (F : H1 c m) :
    tuple c m' (h1MulValue c m m' F) (fun j => h1MulDer c m m' j F) ∈ H1Sub c m' := by
  rw [mem_H1Sub_iff]
  intro j
  refine (F.hasWeakCellDeriv_jb_rpow hc ((m - m') / 2) j).congr ?_ ?_
  · have e : ((h1MulValue c m m' F : X c m') : Plane → ℝ) =ᵐ[volume.restrict (cell c)]
        fun x => jb x ^ ((m - m') / 2) * F.value x :=
      (ac_cellMeasure c m').ae_le (coeFn_mulW c m m' F.value)
    exact e.symm
  · have e : ((h1MulDer c m m' j F : X c m') : Plane → ℝ) =ᵐ[volume.restrict (cell c)]
        fun x => jb x ^ ((m - m') / 2) * F.der j x +
          pd j (fun x => jb x ^ ((m - m') / 2)) x * F.value x :=
      (ac_cellMeasure c m').ae_le (coeFn_h1MulDer c m m' j F)
    exact e.symm

/-- The weight multiplier `F ↦ ⟨x⟩^{m - m'} F` as a function `H^1_m → H^1_{m'}`. -/
def h1MulFun {c : ℝ} (hc : 0 < c) (m m' : ℝ) (F : H1 c m) : H1 c m' :=
  ⟨tuple c m' (h1MulValue c m m' F) (fun j => h1MulDer c m m' j F), mem_H1Sub_h1Mul hc m m' F⟩

@[simp] theorem h1MulFun_value {c : ℝ} (hc : 0 < c) (m m' : ℝ) (F : H1 c m) :
    (h1MulFun hc m m' F).value = mulW c m m' F.value := rfl

@[simp] theorem h1MulFun_der {c : ℝ} (hc : 0 < c) (m m' : ℝ) (F : H1 c m) (j : Fin 2) :
    (h1MulFun hc m m' F).der j = h1MulDer c m m' j F := rfl

def h1MulLM {c : ℝ} (hc : 0 < c) (m m' : ℝ) : H1 c m →ₗ[ℝ] H1 c m' where
  toFun := h1MulFun hc m m'
  map_add' F G := by
    apply H1.ext_comp
    · simp [map_add]
    · intro j
      simp only [h1MulFun_der, H1.der_add, map_add]
  map_smul' a F := by
    apply H1.ext_comp
    · simp [map_smul]
    · intro j
      simp only [h1MulFun_der, H1.der_smul, map_smul, RingHom.id_apply]

theorem norm_h1MulFun_le {c : ℝ} (hc : 0 < c) (m m' : ℝ) (F : H1 c m) :
    ‖h1MulFun hc m m' F‖ ≤ (2 * (1 + |(m - m') / 2|)) * ‖F‖ := by
  set k := (m - m') / 2
  have hv : ‖(h1MulFun hc m m' F).value‖ ≤ ‖F‖ := by
    rw [h1MulFun_value, LinearIsometry.norm_map]
    exact H1.norm_value_le F
  have hd : ∀ j, ‖(h1MulFun hc m m' F).der j‖ ≤ (1 + |k|) * ‖F‖ := by
    intro j
    rw [h1MulFun_der, h1MulDer_apply, LinearIsometry.norm_map]
    calc ‖F.der j + ratioCLM c m k j F.value‖ ≤ ‖F.der j‖ + ‖ratioCLM c m k j F.value‖ :=
          norm_add_le _ _
      _ ≤ ‖F‖ + |k| * ‖F‖ := by
          gcongr
          · exact H1.norm_der_le F j
          · exact (norm_mulR_le c m _ _ F.value).trans
              (mul_le_mul_of_nonneg_left (H1.norm_value_le F) (abs_nonneg k))
      _ = (1 + |k|) * ‖F‖ := by ring
  have hsq := H1.norm_sq (h1MulFun hc m m' F)
  have h0 := hd 0
  have h1 := hd 1
  have hF := norm_nonneg F
  have hk := abs_nonneg k
  have hn0 := norm_nonneg (h1MulFun hc m m' F).value
  have hn1 := norm_nonneg ((h1MulFun hc m m' F).der 0)
  have hn2 := norm_nonneg ((h1MulFun hc m m' F).der 1)
  have hbound : ‖h1MulFun hc m m' F‖ ^ 2 ≤ ((2 * (1 + |k|)) * ‖F‖) ^ 2 := by
    rw [hsq]
    have e0 : ‖(h1MulFun hc m m' F).value‖ ^ 2 ≤ ‖F‖ ^ 2 := pow_le_pow_left₀ hn0 hv 2
    have e1 : ‖(h1MulFun hc m m' F).der 0‖ ^ 2 ≤ ((1 + |k|) * ‖F‖) ^ 2 := pow_le_pow_left₀ hn1 h0 2
    have e2 : ‖(h1MulFun hc m m' F).der 1‖ ^ 2 ≤ ((1 + |k|) * ‖F‖) ^ 2 := pow_le_pow_left₀ hn2 h1 2
    nlinarith [mul_nonneg hk hF, sq_nonneg ‖F‖, mul_nonneg (mul_nonneg hk hF) hF]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 hbound

/-- The weight multiplier `F ↦ ⟨x⟩^{m - m'} F`, bounded `H^1_m → H^1_{m'}`. -/
def h1Mul {c : ℝ} (hc : 0 < c) (m m' : ℝ) : H1 c m →L[ℝ] H1 c m' :=
  LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ) (E := H1 c m) (F := H1 c m') (σ := RingHom.id ℝ)
    (h1MulLM hc m m') _ (norm_h1MulFun_le hc m m')

@[simp] theorem h1Mul_value {c : ℝ} (hc : 0 < c) (m m' : ℝ) (F : H1 c m) :
    (h1Mul hc m m' F).value = mulW c m m' F.value := rfl

@[simp] theorem h1Mul_der {c : ℝ} (hc : 0 < c) (m m' : ℝ) (F : H1 c m) (j : Fin 2) :
    (h1Mul hc m m' F).der j = h1MulDer c m m' j F := rfl

theorem coeFn_ratioCLM (c m k : ℝ) (j : Fin 2) (f : X c m) :
    (ratioCLM c m k j f : Plane → ℝ) =ᵐ[cellMeasure c m] fun x => wratio k j x * f x :=
  coeFn_mulR c m (continuous_wratio k j) (abs_wratio_le k j) f

theorem mulW_ratio_cancel (c m m' : ℝ) (j : Fin 2) (f : X c m) :
    mulW c m' m (ratioCLM c m' ((m' - m) / 2) j (mulW c m m' f)) =
      -ratioCLM c m ((m - m') / 2) j f := by
  apply Lp.ext
  filter_upwards [coeFn_mulW c m' m (ratioCLM c m' ((m' - m) / 2) j (mulW c m m' f)),
    coeFn_ae_cell (m' := m) (coeFn_ratioCLM c m' ((m' - m) / 2) j (mulW c m m' f)),
    coeFn_ae_cell (m' := m) (coeFn_mulW c m m' f),
    Lp.coeFn_neg (ratioCLM c m ((m - m') / 2) j f),
    coeFn_ratioCLM c m ((m - m') / 2) j f] with x h1 h2 h3 h4 h5
  rw [h1, h2, h3, h4, Pi.neg_apply, h5, show (m' - m) / 2 = -((m - m') / 2) by ring, wratio_neg]
  have e : jb x ^ ((m' - m) / 2) * jb x ^ ((m - m') / 2) = 1 := by
    rw [jb_rpow_mul, show (m' - m) / 2 + (m - m') / 2 = 0 by ring, Real.rpow_zero]
  rw [show (m' - m) / 2 = -((m - m') / 2) by ring] at e
  have : jb x ^ (-((m - m') / 2)) * (-wratio ((m - m') / 2) j x * (jb x ^ ((m - m') / 2) * f x)) =
      -(jb x ^ (-((m - m') / 2)) * jb x ^ ((m - m') / 2)) * (wratio ((m - m') / 2) j x * f x) := by
    ring
  rw [this, e]
  ring

theorem h1Mul_h1Mul {c : ℝ} (hc : 0 < c) (m m' : ℝ) (F : H1 c m) :
    h1Mul hc m' m (h1Mul hc m m' F) = F := by
  apply H1.ext_comp
  · simp only [h1Mul_value, mulW_mulW, mulW_self]
  · intro j
    rw [h1Mul_der, h1MulDer_apply, h1Mul_der, h1Mul_value, h1MulDer_apply, map_add, mulW_mulW,
      mulW_self, mulW_ratio_cancel]
    abel

/-- The weight conjugation `F ↦ ⟨x⟩^{m - m'} F` is an isomorphism `H^1_m ≃ H^1_{m'}`
(the conjugation by the weight of `paper/main.tex:9386-9387`; needs `0 < c`). -/
def weightEquiv {c : ℝ} (hc : 0 < c) (m m' : ℝ) : H1 c m ≃L[ℝ] H1 c m' :=
  ContinuousLinearEquiv.equivOfInverse (h1Mul hc m m') (h1Mul hc m' m) (h1Mul_h1Mul hc m m')
    (h1Mul_h1Mul hc m' m)

theorem weightEquiv_apply {c : ℝ} (hc : 0 < c) (m m' : ℝ) (F : H1 c m) :
    weightEquiv hc m m' F = h1Mul hc m m' F := rfl

theorem weightEquiv_value {c : ℝ} (hc : 0 < c) (m m' : ℝ) (F : H1 c m) :
    (weightEquiv hc m m' F).value = mulW c m m' F.value := rfl

theorem isWeightMultiplier_weightEquiv {c : ℝ} (hc : 0 < c) (m : ℝ) :
    IsWeightMultiplier c m (weightEquiv hc (-m) m : H1 c (-m) →L[ℝ] H1 c m) := fun _ => rfl

theorem norm_h1Mul_apply_le {c : ℝ} (hc : 0 < c) (m m' : ℝ) (F : H1 c m) :
    ‖h1Mul hc m m' F‖ ≤ (2 * (1 + |(m - m') / 2|)) * ‖F‖ :=
  norm_h1MulFun_le hc m m' F


/-! ### Headline: the `X_m`-pivot convention is equivalent (`paper/main.tex:9384-9387`) -/

/-- **`prepared:p1.1`, pivot convention** (`paper/main.tex:9384-9387`). On the centered cell of
circumference `c > 0`, the weight conjugation `φ ↦ ⟨x⟩^{-2m} φ` is an isomorphism
`H^1_{-m} ≃ H^1_m` (`weightEquiv`), and its transpose is an isomorphism `E` from the
`X_m`-pivot negative space `(H^1_m)^*` onto `H^{-1}_m = (H^1_{-m})^*` that carries the pivot
representation `ψ ↦ ⟪f, ψ⟫_{X_m}` of each source `f ∈ X_m` to its unweighted representation
`φ ↦ ∫_cell f φ`. -/
theorem pivot_equivalence {c : ℝ} (hc : 0 < c) (m : ℝ) :
    ∃ E : HnegPivot c m ≃L[ℝ] Hneg c m,
      (∀ (ℓ : HnegPivot c m) (φ : H1 c (-m)), E ℓ φ = ℓ (weightEquiv hc (-m) m φ)) ∧
      (∀ φ : H1 c (-m), (weightEquiv hc (-m) m φ).value = mulW c (-m) m φ.value) ∧
      ∀ f : X c m, E (pivotSourceCLM c m f) = sourceCLM c m f :=
  ⟨pivotEquiv (weightEquiv hc (-m) m), fun ℓ φ => pivotEquiv_apply _ ℓ φ, fun _ => rfl,
    pivotEquiv_pivotSourceCLM _ (isWeightMultiplier_weightEquiv hc m)⟩

/-- The two conventions give equivalent negative norms of a source `f ∈ X_m`:
`‖f‖_{H^{-1}_m} ≤ 2(1 + |m|) ‖f‖_{(H^1_m)^*, pivot}`. -/
theorem norm_sourceCLM_le_pivot {c : ℝ} (hc : 0 < c) (m : ℝ) (f : X c m) :
    ‖sourceCLM c m f‖ ≤ (2 * (1 + |m|)) * ‖pivotSourceCLM c m f‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun φ => ?_
  rw [← pivotSourceCLM_comp c m (isWeightMultiplier_weightEquiv hc m) f,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, weightEquiv_apply]
  have hM := norm_h1Mul_apply_le hc (-m) m φ
  rw [show (-m - m) / 2 = -m by ring, abs_neg] at hM
  calc ‖pivotSourceCLM c m f (h1Mul hc (-m) m φ)‖
      ≤ ‖pivotSourceCLM c m f‖ * ‖h1Mul hc (-m) m φ‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖pivotSourceCLM c m f‖ * ((2 * (1 + |m|)) * ‖φ‖) := by gcongr
    _ = 2 * (1 + |m|) * ‖pivotSourceCLM c m f‖ * ‖φ‖ := by ring

/-- Converse: `‖f‖_{(H^1_m)^*, pivot} ≤ 2(1 + |m|) ‖f‖_{H^{-1}_m}`. -/
theorem norm_pivot_le_sourceCLM {c : ℝ} (hc : 0 < c) (m : ℝ) (f : X c m) :
    ‖pivotSourceCLM c m f‖ ≤ (2 * (1 + |m|)) * ‖sourceCLM c m f‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun ψ => ?_
  have e : pivotSourceCLM c m f ψ = sourceCLM c m f (h1Mul hc m (-m) ψ) := by
    rw [← pivotSourceCLM_comp c m (isWeightMultiplier_weightEquiv hc m) f,
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, weightEquiv_apply,
      h1Mul_h1Mul hc m (-m) ψ]
  have hM := norm_h1Mul_apply_le hc m (-m) ψ
  rw [show (m - -m) / 2 = m by ring] at hM
  rw [e]
  calc ‖sourceCLM c m f (h1Mul hc m (-m) ψ)‖
      ≤ ‖sourceCLM c m f‖ * ‖h1Mul hc m (-m) ψ‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖sourceCLM c m f‖ * ((2 * (1 + |m|)) * ‖ψ‖) := by gcongr
    _ = 2 * (1 + |m|) * ‖sourceCLM c m f‖ * ‖ψ‖ := by ring

end UnforcedLeray.B0579
