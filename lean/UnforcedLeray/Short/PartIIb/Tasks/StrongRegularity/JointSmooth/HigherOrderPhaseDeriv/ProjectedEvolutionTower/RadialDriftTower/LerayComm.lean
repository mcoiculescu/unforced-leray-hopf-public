import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S3_1_2_2_2
import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth.HigherOrderPhaseDeriv.SmoothLeraySlice.DerivZero
import UnforcedLeray.Lib.LerayC.Dilate
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# `PartII-b:S3/1/2/2/2/1` (`SmoothLerayRadialDriftComm`, `LerayComm.lean`, SP 2519-2523, 2552)

Source of record: `the November 2 reference manuscript`
(SP), lines 2519-2523 and 2552:
"The projected equation is $A_0 U + \mathbb{P}(U \cdot \nabla U) = 0$ with zero residual. ...
These estimates are uniform in phase; the bounded Cartesian Leray map preserves them in $W^{k,p}$."

Proves `smoothLerayRadialDriftComm_proof : UnforcedLeray.Short.IIb.SmoothLerayRadialDriftComm`:
for any slice family `G : ℝ → SpatialField` with `G` and `fun τ => spatialRadialDrift (G τ)` in
`IsUniformSmoothL4SliceFamily` and any `τ : ℝ`,
`spatialRadialDrift (smoothLeraySlice G τ) = smoothLeraySlice (fun τ' => spatialRadialDrift (G τ')) τ`.

Proof strategy:
For fixed `τ : ℝ`, consider the bounded positive dilation path `b s = 1 + (1 / 2) * Real.sin s`
(`1 / 2 ≤ b s ≤ 3 / 2`, `b 0 = 1`, `HasDerivAt b (1 / 2) 0`) and the dilated slice families
`F s y = G τ (b s • y)` and `F' s y = (b' s / b s) • spatialRadialDrift (G τ) (b s • y)`.
1. By `UnforcedLeray.RieszLp.lerayLp_dilate_apply`, `IsSmoothLerayRep` commutes with positive spatial
   dilations `y ↦ a • y` (`a > 0`), so `smoothLeraySlice F s y = smoothLeraySlice G τ (b s • y)` for
   all `s : ℝ`.
2. Using `PhaseDerivStepSub.dirSpatialJet_spatialRadialDrift`, `F` and `F'` lie in
   `IsUniformSmoothL4SliceFamily` and satisfy `HasPhaseJetDeriv F F'`.
3. Applying `smoothLeraySliceDerivZero_proof` at `s = 0` and comparing with the chain-rule derivative
   of `s ↦ smoothLeraySlice G τ (b s • y)` at `s = 0` yields
   `(1 / 2 : ℝ) • spatialRadialDrift (smoothLeraySlice G τ) y = (1 / 2 : ℝ) • smoothLeraySlice (fun τ' => spatialRadialDrift (G τ')) τ y`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff BigOperators

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace

local instance fact_one_le_four_lrc : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

namespace SmoothLerayRadialDriftCommAux

/-- Spatial scaling `y ↦ a • y` as a continuous linear map on `Space`. -/
def scaleLinear (a : ℝ) : Space →L[ℝ] Space :=
  a • ContinuousLinearMap.id ℝ Space

@[simp]
theorem scaleLinear_apply (a : ℝ) (y : Space) :
    scaleLinear a y = a • y := rfl

theorem contDiff_infty_comp_scale {f : SpatialField} (hf : ContDiff ℝ ∞ f) (a : ℝ) :
    ContDiff ℝ ∞ (fun y : Space => f (a • y)) :=
  hf.comp_continuousLinearMap (g := scaleLinear a)

theorem contDiff_infty_smul_comp_scale {f : SpatialField} (hf : ContDiff ℝ ∞ f) (c a : ℝ) :
    ContDiff ℝ ∞ (fun y : Space => c • f (a • y)) :=
  (contDiff_infty_comp_scale hf a).const_smul c

/-- `k`-th Fréchet derivative of `y ↦ f (a • y)`. -/
theorem iteratedFDeriv_comp_scale {f : SpatialField} (hf : ContDiff ℝ ∞ f) (a : ℝ)
    (k : ℕ) (y : Space) :
    iteratedFDeriv ℝ k (fun z : Space => f (a • z)) y =
      a ^ k • iteratedFDeriv ℝ k f (a • y) := by
  have hcomp : (fun z : Space => f (a • z)) = f ∘ scaleLinear a := rfl
  rw [hcomp, (scaleLinear a).iteratedFDeriv_comp_right hf y (by exact_mod_cast le_top)]
  ext m
  simp [scaleLinear, ContinuousMultilinearMap.map_smul_univ]

/-- `k`-th Fréchet derivative of `y ↦ c • f (a • y)`. -/
theorem iteratedFDeriv_smul_comp_scale {f : SpatialField} (hf : ContDiff ℝ ∞ f) (c a : ℝ)
    (k : ℕ) (y : Space) :
    iteratedFDeriv ℝ k (fun z : Space => c • f (a • z)) y =
      (c * a ^ k) • iteratedFDeriv ℝ k f (a • y) := by
  have hcd : ContDiffAt ℝ k (fun z : Space => f (a • z)) y :=
    ((contDiff_infty_comp_scale hf a).of_le (by exact_mod_cast le_top)).contDiffAt
  change iteratedFDeriv ℝ k (c • fun z : Space => f (a • z)) y = _
  rw [iteratedFDeriv_const_smul_apply hcd, iteratedFDeriv_comp_scale hf a k y, smul_smul]

/-- Directional spatial jet of `y ↦ f (a • y)`. -/
theorem dirSpatialJet_comp_scale {f : SpatialField} (hf : ContDiff ℝ ∞ f) (a : ℝ) :
    ∀ ws : List Space,
      dirSpatialJet (fun z : Space => f (a • z)) ws =
        fun y : Space => a ^ ws.length • dirSpatialJet f ws (a • y)
  | [] => by
      funext y
      simp
  | w :: ws => by
      funext y
      have ih := dirSpatialJet_comp_scale hf a ws
      have hws : DifferentiableAt ℝ (dirSpatialJet f ws) (a • y) :=
        JointSmoothSub.differentiable_dirSpatialJet hf ws (a • y)
      have hcomp : HasFDerivAt (fun z : Space => a ^ ws.length • dirSpatialJet f ws (a • z))
          (a ^ ws.length • (fderiv ℝ (dirSpatialJet f ws) (a • y)).comp (scaleLinear a)) y :=
        (hws.hasFDerivAt.comp y (scaleLinear a).hasFDerivAt).const_smul (a ^ ws.length)
      change fderiv ℝ (dirSpatialJet (fun z : Space => f (a • z)) ws) y w = _
      rw [ih, hcomp.fderiv]
      simp [scaleLinear, List.length_cons, pow_succ, mul_smul]

/-- Directional spatial jet of `y ↦ c • f (a • y)`. -/
theorem dirSpatialJet_smul_comp_scale {f : SpatialField} (hf : ContDiff ℝ ∞ f) (c a : ℝ)
    (ws : List Space) :
    dirSpatialJet (fun z : Space => c • f (a • z)) ws =
      fun y : Space => (c * a ^ ws.length) • dirSpatialJet f ws (a • y) := by
  change dirSpatialJet (c • fun z : Space => f (a • z)) ws = _
  rw [HigherPhaseSub.dirSpatialJet_smul c (contDiff_infty_comp_scale hf a) ws,
    dirSpatialJet_comp_scale hf a ws]
  funext y
  simp [mul_smul]

/-- Exact `L⁴(ℝ³)` transport of a dilation for any normed target space `E`. -/
theorem eLpNorm_comp_dilation_any {E : Type*} [NormedAddCommGroup E]
    {a : ℝ} (ha : a ≠ 0) (u : Space → E) :
    eLpNorm (fun x : Space => u (a • x)) 4 volume =
      (ENNReal.ofReal |(a ^ 3)⁻¹|) ^ (1 / (4 : ℝ≥0∞)).toReal * eLpNorm u 4 volume := by
  have hp : (4 : ℝ≥0∞) ≠ ⊤ := by norm_num
  change eLpNorm (u ∘ fun x : Space => a • x) 4 volume = _
  rw [← (UnforcedLeray.SpatialScaling.dilation_measurableEmbedding ha).eLpNorm_map_measure,
    UnforcedLeray.SpatialScaling.map_dilation ha, eLpNorm_smul_measure_of_ne_top hp]
  rfl

/-- Positive spatial dilation `y ↦ a • y` (`a > 0`) preserves `IsSmoothLerayRep`. -/
theorem isSmoothLerayRep_comp_scale {f g : SpatialField}
    (hrep : IsSmoothLerayRep f g) {a : ℝ} (ha : 0 < a) :
    IsSmoothLerayRep (fun y : Space => f (a • y)) (fun y : Space => g (a • y)) := by
  obtain ⟨hf, hg_smooth, hg_ae⟩ := hrep
  have hne : a ≠ 0 := ha.ne'
  have hp1 : (1 : ℝ≥0∞) < 4 := by norm_num
  have hp : (4 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hf_a : MemLp (fun y : Space => f (a • y)) 4 volume :=
    UnforcedLeray.SpatialScaling.memLp_comp_dilation hf hne
  refine ⟨hf_a, contDiff_infty_comp_scale hg_smooth a, ?_⟩
  have htoLp : hf_a.toLp (fun y : Space => f (a • y)) =
      UnforcedLeray.RieszLp.dilateLp 4 hp hne (hf.toLp f) := by
    rw [UnforcedLeray.RieszLp.dilateLp_apply]
    exact MemLp.toLp_congr hf_a _
      (UnforcedLeray.SpatialScaling.ae_eq_comp_dilation hf.coeFn_toLp.symm hne)
  rw [htoLp, UnforcedLeray.RieszLp.lerayLp_dilate_apply hp1 hp ha]
  have hae1 : (fun y : Space => g (a • y)) =ᵐ[volume]
      fun y : Space =>
        (UnforcedLeray.RieszLp.lerayLp 4 hp1 hp (hf.toLp f) : SpatialField) (a • y) :=
    UnforcedLeray.SpatialScaling.ae_eq_comp_dilation hg_ae hne
  have hae2 := UnforcedLeray.RieszLp.coeFn_dilateLp hp hne
    (UnforcedLeray.RieszLp.lerayLp 4 hp1 hp (hf.toLp f))
  exact hae1.trans hae2.symm

/-- For `a > 0` and `IsSmoothLerayRep f (smoothLerayProj f)`, `smoothLerayProj` commutes with
`y ↦ a • y`. -/
theorem smoothLerayProj_comp_scale {f : SpatialField}
    (hrep : IsSmoothLerayRep f (smoothLerayProj f)) {a : ℝ} (ha : 0 < a) :
    smoothLerayProj (fun y : Space => f (a • y)) =
      fun y : Space => smoothLerayProj f (a • y) :=
  HigherPhaseSub.smoothLerayProj_eq_of_isSmoothLerayRep (isSmoothLerayRep_comp_scale hrep ha)

/-- Concrete bounded positive dilation path `b s = 1 + (1 / 2) * Real.sin s`. -/
def dilPath (s : ℝ) : ℝ :=
  1 + (1 / 2 : ℝ) * Real.sin s

/-- Derivative `b' s = (1 / 2) * Real.cos s` of `dilPath`. -/
def dilPathDeriv (s : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.cos s

/-- Logarithmic derivative `c s = b' s / b s` of `dilPath`. -/
def dilLogDeriv (s : ℝ) : ℝ :=
  dilPathDeriv s / dilPath s

@[simp]
theorem dilPath_zero : dilPath 0 = 1 := by
  simp [dilPath]

@[simp]
theorem dilPathDeriv_zero : dilPathDeriv 0 = 1 / 2 := by
  simp [dilPathDeriv]

@[simp]
theorem dilLogDeriv_zero : dilLogDeriv 0 = 1 / 2 := by
  simp [dilLogDeriv]

theorem hasDerivAt_dilPath (s : ℝ) :
    HasDerivAt dilPath (dilPathDeriv s) s := by
  unfold dilPath dilPathDeriv
  simpa using (Real.hasDerivAt_sin s).const_mul (1 / 2 : ℝ) |>.const_add 1

theorem half_le_dilPath (s : ℝ) : (1 / 2 : ℝ) ≤ dilPath s := by
  have h := (abs_le.1 (Real.abs_sin_le_one s)).1
  unfold dilPath
  linarith

theorem dilPath_le_three_halves (s : ℝ) : dilPath s ≤ 3 / 2 := by
  have h := (abs_le.1 (Real.abs_sin_le_one s)).2
  unfold dilPath
  linarith

theorem dilPath_pos (s : ℝ) : 0 < dilPath s :=
  by linarith [half_le_dilPath s]

theorem dilPath_ne_zero (s : ℝ) : dilPath s ≠ 0 :=
  (dilPath_pos s).ne'

theorem abs_dilPath_le_two (s : ℝ) : |dilPath s| ≤ 2 := by
  rw [abs_of_pos (dilPath_pos s)]
  linarith [dilPath_le_three_halves s]

theorem abs_dilPathDeriv_le_one (s : ℝ) : |dilPathDeriv s| ≤ 1 := by
  unfold dilPathDeriv
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have h := Real.abs_cos_le_one s
  linarith

theorem abs_dilLogDeriv_le_two (s : ℝ) : |dilLogDeriv s| ≤ 2 := by
  unfold dilLogDeriv
  rw [abs_div, abs_of_pos (dilPath_pos s)]
  have h1 := abs_dilPathDeriv_le_one s
  have h2 := half_le_dilPath s
  have h3 : dilPathDeriv s ≤ |dilPathDeriv s| := le_abs_self _
  calc |dilPathDeriv s| / dilPath s
      ≤ 1 / (1 / 2 : ℝ) := div_le_div₀ (by norm_num) h1 (by norm_num) h2
    _ = 2 := by norm_num

theorem abs_inv_cube_dilPath_le_eight (s : ℝ) :
    |((dilPath s) ^ 3)⁻¹| ≤ 8 := by
  have hhalf : (1 / 2 : ℝ) ≤ dilPath s := half_le_dilPath s
  have hpos : (0 : ℝ) < (dilPath s) ^ 3 := pow_pos (dilPath_pos s) 3
  have hcube : (1 / 8 : ℝ) ≤ (dilPath s) ^ 3 := by
    calc (1 / 8 : ℝ) = (1 / 2 : ℝ) ^ 3 := by norm_num
      _ ≤ (dilPath s) ^ 3 := pow_le_pow_left₀ (by norm_num) hhalf 3
  rw [abs_inv, abs_of_pos hpos]
  calc ((dilPath s) ^ 3)⁻¹
      ≤ (1 / 8 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hcube
    _ = 8 := by norm_num

/-- For any slice `f = G τ` of `G ∈ IsUniformSmoothL4SliceFamily` and any scalar multiplier
`c : ℝ → ℝ` bounded by `C_c ≥ 0`, the dilated family `fun s y => c s • f (dilPath s • y)` lies in
`IsUniformSmoothL4SliceFamily`. -/
theorem sliceFamily_smul_comp_dilPath {G : ℝ → SpatialField}
    (hG : IsUniformSmoothL4SliceFamily G) (τ : ℝ)
    (c : ℝ → ℝ) {C_c : ℝ} (hCc0 : 0 ≤ C_c) (hc : ∀ s : ℝ, |c s| ≤ C_c) :
    IsUniformSmoothL4SliceFamily (fun s y => c s • G τ (dilPath s • y)) := by
  set f : SpatialField := G τ
  have hf : ContDiff ℝ ∞ f := HigherPhaseSub.sliceFamily_contDiff_infty hG τ
  refine ⟨?_, ?_, ?_⟩
  · intro k s
    exact (contDiff_infty_smul_comp_scale hf (c s) (dilPath s)).of_le (by exact_mod_cast le_top)
  · intro k
    obtain ⟨M, hM⟩ := hG.iteratedFDeriv_bounded k
    set M' : ℝ := max M 0
    have hM'0 : 0 ≤ M' := le_max_right M 0
    refine ⟨C_c * (2 : ℝ) ^ k * M', fun s y => ?_⟩
    rw [iteratedFDeriv_smul_comp_scale hf (c s) (dilPath s) k y, norm_smul, Real.norm_eq_abs,
      abs_mul, abs_pow]
    have ha : |dilPath s| ^ k ≤ (2 : ℝ) ^ k :=
      pow_le_pow_left₀ (abs_nonneg _) (abs_dilPath_le_two s) k
    have hcoeff : |c s| * |dilPath s| ^ k ≤ C_c * (2 : ℝ) ^ k :=
      mul_le_mul (hc s) ha (pow_nonneg (abs_nonneg _) k) hCc0
    have hf_le : ‖iteratedFDeriv ℝ k f (dilPath s • y)‖ ≤ M' :=
      (hM τ (dilPath s • y)).trans (le_max_left M 0)
    exact mul_le_mul hcoeff hf_le (norm_nonneg _) (by positivity)
  · intro k
    obtain ⟨M, hM⟩ := hG.l4_bounded k
    set M' : ℝ := max M 0
    have hM'0 : 0 ≤ M' := le_max_right M 0
    set J : ℝ := (8 : ℝ) ^ (1 / (4 : ℝ≥0∞)).toReal
    have hJ0 : 0 ≤ J := Real.rpow_nonneg (by norm_num) _
    refine ⟨C_c * (2 : ℝ) ^ k * J * M', fun s => ?_⟩
    have hfun : (fun y : Space =>
        iteratedFDeriv ℝ k (fun z : Space => c s • f (dilPath s • z)) y) =
        (c s * (dilPath s) ^ k) • fun y : Space => iteratedFDeriv ℝ k f (dilPath s • y) := by
      funext y
      exact iteratedFDeriv_smul_comp_scale hf (c s) (dilPath s) k y
    rw [hfun, eLpNorm_const_smul,
      eLpNorm_comp_dilation_any (dilPath_ne_zero s) (fun y => iteratedFDeriv ℝ k f y)]
    have hcoeff_real : |c s * (dilPath s) ^ k| ≤ C_c * (2 : ℝ) ^ k := by
      rw [abs_mul, abs_pow]
      exact mul_le_mul (hc s)
        (pow_le_pow_left₀ (abs_nonneg _) (abs_dilPath_le_two s) k)
        (pow_nonneg (abs_nonneg _) k) hCc0
    have hcoeff : ‖c s * (dilPath s) ^ k‖ₑ ≤ ENNReal.ofReal (C_c * (2 : ℝ) ^ k) := by
      rw [Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal hcoeff_real
    have hjac : (ENNReal.ofReal |((dilPath s) ^ 3)⁻¹|) ^ (1 / (4 : ℝ≥0∞)).toReal ≤
        ENNReal.ofReal J := by
      rw [← ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by positivity)]
      exact ENNReal.rpow_le_rpow
        (ENNReal.ofReal_le_ofReal (abs_inv_cube_dilPath_le_eight s))
        (by positivity)
    have hf_l4 : eLpNorm (fun y : Space => iteratedFDeriv ℝ k f y) 4 volume ≤
        ENNReal.ofReal M' :=
      (hM τ).trans (ENNReal.ofReal_le_ofReal (le_max_left M 0))
    calc ‖c s * (dilPath s) ^ k‖ₑ *
          ((ENNReal.ofReal |((dilPath s) ^ 3)⁻¹|) ^ (1 / (4 : ℝ≥0∞)).toReal *
            eLpNorm (fun y : Space => iteratedFDeriv ℝ k f y) 4 volume)
        ≤ ENNReal.ofReal (C_c * (2 : ℝ) ^ k) * (ENNReal.ofReal J * ENNReal.ofReal M') :=
          mul_le_mul' hcoeff (mul_le_mul' hjac hf_l4)
      _ = ENNReal.ofReal (C_c * (2 : ℝ) ^ k * J * M') := by
          rw [← ENNReal.ofReal_mul hJ0, ← ENNReal.ofReal_mul (by positivity)]
          ring_nf

/-- Chain-rule derivative along `dilPath`: for any smooth `h : SpatialField`, `s : ℝ`, and `y : Space`,
`s' ↦ h (dilPath s' • y)` has derivative `dilLogDeriv s • spatialRadialDrift h (dilPath s • y)` at `s`. -/
theorem hasDerivAt_comp_dilPath {h : SpatialField} (hh : ContDiff ℝ ∞ h) (s : ℝ) (y : Space) :
    HasDerivAt (fun s' : ℝ => h (dilPath s' • y))
      (dilLogDeriv s • spatialRadialDrift h (dilPath s • y)) s := by
  have hd_path : HasDerivAt (fun s' : ℝ => dilPath s' • y) (dilPathDeriv s • y) s :=
    (hasDerivAt_dilPath s).smul_const y
  have hd_h : HasFDerivAt h (fderiv ℝ h (dilPath s • y)) (dilPath s • y) :=
    ((hh.differentiable (by simp)) (dilPath s • y)).hasFDerivAt
  have hcomp : HasDerivAt (fun s' : ℝ => h (dilPath s' • y))
      (fderiv ℝ h (dilPath s • y) (dilPathDeriv s • y)) s :=
    hd_h.comp_hasDerivAt s hd_path
  have hvec : dilPathDeriv s • y = dilLogDeriv s • (dilPath s • y) := by
    rw [smul_smul, dilLogDeriv, div_mul_cancel₀ _ (dilPath_ne_zero s)]
  have hval : fderiv ℝ h (dilPath s • y) (dilPathDeriv s • y) =
      dilLogDeriv s • spatialRadialDrift h (dilPath s • y) := by
    rw [hvec, map_smul]
    rfl
  rwa [hval] at hcomp

/-- Scalar power derivative identity along `dilPath`:
`(n : ℝ) * (dilPath s) ^ (n - 1) * dilPathDeriv s = (dilLogDeriv s * (dilPath s) ^ n) * (n : ℝ)`. -/
theorem dilPath_pow_deriv_eq (s : ℝ) :
    ∀ n : ℕ,
      (n : ℝ) * (dilPath s) ^ (n - 1) * dilPathDeriv s =
        (dilLogDeriv s * (dilPath s) ^ n) * (n : ℝ)
  | 0 => by simp
  | n + 1 => by
      have hne : dilPath s ≠ 0 := dilPath_ne_zero s
      simp only [Nat.add_sub_cancel, pow_succ, dilLogDeriv]
      field_simp [hne]

/-- `HasPhaseJetDeriv` for the dilated slice family `s ↦ (y ↦ f (dilPath s • y))` with phase
derivative `s ↦ (y ↦ dilLogDeriv s • spatialRadialDrift f (dilPath s • y))`. -/
theorem hasPhaseJetDeriv_comp_dilPath {f : SpatialField} (hf : ContDiff ℝ ∞ f) :
    HasPhaseJetDeriv
      (fun s y => f (dilPath s • y))
      (fun s y => dilLogDeriv s • spatialRadialDrift f (dilPath s • y)) := by
  intro ws s y
  have hfun : (fun s' : ℝ => dirSpatialJet (fun z : Space => f (dilPath s' • z)) ws y) =
      fun s' : ℝ => (dilPath s') ^ ws.length • dirSpatialJet f ws (dilPath s' • y) := by
    funext s'
    exact congrFun (dirSpatialJet_comp_scale hf (dilPath s') ws) y
  rw [hfun]
  have hjet_cd : ContDiff ℝ ∞ (dirSpatialJet f ws) :=
    JointSmoothSub.contDiff_infty_dirSpatialJet hf ws
  have hd_pow : HasDerivAt (fun s' : ℝ => (dilPath s') ^ ws.length)
      ((ws.length : ℝ) * (dilPath s) ^ (ws.length - 1) * dilPathDeriv s) s :=
    (hasDerivAt_dilPath s).pow ws.length
  have hd_eval : HasDerivAt (fun s' : ℝ => dirSpatialJet f ws (dilPath s' • y))
      (dilLogDeriv s • spatialRadialDrift (dirSpatialJet f ws) (dilPath s • y)) s :=
    hasDerivAt_comp_dilPath hjet_cd s y
  have hd_prod := hd_pow.smul hd_eval
  have hrhs : dirSpatialJet
      (fun z : Space => dilLogDeriv s • spatialRadialDrift f (dilPath s • z)) ws y =
      (dilPath s) ^ ws.length •
        (dilLogDeriv s • spatialRadialDrift (dirSpatialJet f ws) (dilPath s • y)) +
      ((ws.length : ℝ) * (dilPath s) ^ (ws.length - 1) * dilPathDeriv s) •
        dirSpatialJet f ws (dilPath s • y) := by
    have h1 := congrFun
      (dirSpatialJet_smul_comp_scale
        (HigherPhaseSub.contDiff_infty_spatialRadialDrift hf)
        (dilLogDeriv s) (dilPath s) ws) y
    have h2 := congrFun (PhaseDerivStepSub.dirSpatialJet_spatialRadialDrift hf ws) (dilPath s • y)
    rw [h1, h2, Pi.add_apply, Pi.smul_apply, smul_add, smul_smul,
      dilPath_pow_deriv_eq s ws.length, mul_comm (dilLogDeriv s) (dilPath s ^ ws.length),
      mul_smul]
  rw [hrhs]
  exact hd_prod

end SmoothLerayRadialDriftCommAux

/-- **Leaf 1 (`PartII-b:S3/1/2/2/2/1`, `SmoothLerayRadialDriftComm`)**
(`the November 2 reference manuscript`,
lines 2519-2523 and 2552): `smoothLeraySlice` commutes with `spatialRadialDrift` on every slice
family `G` with `G` and `fun τ => spatialRadialDrift (G τ)` in `IsUniformSmoothL4SliceFamily`. -/
theorem smoothLerayRadialDriftComm_proof : UnforcedLeray.Short.IIb.SmoothLerayRadialDriftComm := by
  intro G hG hradG τ
  open SmoothLerayRadialDriftCommAux in
  funext y
  set F : ℝ → SpatialField := fun s z => G τ (dilPath s • z)
  set F' : ℝ → SpatialField := fun s z => dilLogDeriv s • spatialRadialDrift (G τ) (dilPath s • z)
  have hf_cd : ContDiff ℝ ∞ (G τ) := HigherPhaseSub.sliceFamily_contDiff_infty hG τ
  have hF_fam : IsUniformSmoothL4SliceFamily F := by
    have h := sliceFamily_smul_comp_dilPath hG τ (fun _ => (1 : ℝ))
      (C_c := 1) (by norm_num) (fun _ => by norm_num)
    simpa [F, one_smul] using h
  have hF'_fam : IsUniformSmoothL4SliceFamily F' :=
    sliceFamily_smul_comp_dilPath hradG τ dilLogDeriv
      (C_c := 2) (by norm_num) abs_dilLogDeriv_le_two
  have hdF : HasPhaseJetDeriv F F' := hasPhaseJetDeriv_comp_dilPath hf_cd
  have hderiv_leray : HasDerivAt (fun s : ℝ => smoothLeraySlice F s y)
      (smoothLeraySlice F' 0 y) 0 :=
    smoothLeraySliceDerivZero_proof smoothLerayRepExists_proof F F' hF_fam hF'_fam hdF 0 y
  have hrep_Gτ : IsSmoothLerayRep (G τ) (smoothLeraySlice G τ) :=
    (SmoothLeraySliceSub.smoothLeraySlice_rep_and_memLp smoothLerayRepExists_proof hG τ).1
  have hrep_radGτ : IsSmoothLerayRep (spatialRadialDrift (G τ))
      (smoothLeraySlice (fun τ' => spatialRadialDrift (G τ')) τ) :=
    (SmoothLeraySliceSub.smoothLeraySlice_rep_and_memLp smoothLerayRepExists_proof hradG τ).1
  have hslice_F : (fun s : ℝ => smoothLeraySlice F s y) =
      fun s : ℝ => smoothLeraySlice G τ (dilPath s • y) := by
    funext s
    exact congrFun (smoothLerayProj_comp_scale hrep_Gτ (dilPath_pos s)) y
  have hderiv_chain : HasDerivAt (fun s : ℝ => smoothLeraySlice G τ (dilPath s • y))
      ((1 / 2 : ℝ) • spatialRadialDrift (smoothLeraySlice G τ) y) 0 := by
    have hd := hasDerivAt_comp_dilPath hrep_Gτ.2.1 0 y
    simpa [dilLogDeriv_zero, dilPath_zero, one_smul] using hd
  rw [hslice_F] at hderiv_leray
  have hF'_zero : F' 0 = (1 / 2 : ℝ) • spatialRadialDrift (G τ) := by
    funext z
    simp [F', dilLogDeriv_zero, dilPath_zero, one_smul]
  have hslice_F'_zero : smoothLeraySlice F' 0 y =
      (1 / 2 : ℝ) • smoothLeraySlice (fun τ' => spatialRadialDrift (G τ')) τ y := by
    change smoothLerayProj (F' 0) y = _
    rw [hF'_zero, SmoothLeraySliceSub.smoothLerayProj_smul (1 / 2 : ℝ) hrep_radGτ]
    rfl
  rw [hslice_F'_zero] at hderiv_leray
  have heq_half :
      (1 / 2 : ℝ) • spatialRadialDrift (smoothLeraySlice G τ) y =
        (1 / 2 : ℝ) • smoothLeraySlice (fun τ' => spatialRadialDrift (G τ')) τ y :=
    hderiv_chain.unique hderiv_leray
  have hmul := congrArg ((2 : ℝ) • ·) heq_half
  simpa [smul_smul] using hmul

end UnforcedLeray.Short.IIb

end
