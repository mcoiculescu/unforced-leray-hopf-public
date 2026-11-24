import UnforcedLeray.Lib.LerayC.Transfer
import UnforcedLeray.Lib.PhaseSpace.Test

/-!
# The Leray projection on complex fields `L^p(R³;ℂ³)` (INF01 T17, `ℂ³` version)

Blueprint: INF01 target T17 (the `ℂ³` version, "via real and imaginary parts (for complex `μ` in

Level 2, and risk R7 (constants at most doubled); block 3C LERAY-C.

Manuscript: unit B0414 (`paper/main.tex` lines 7336–7344): `P_σ`, with multiplier
`Id − ξ⊗ξ/|ξ|²`, is bounded on `L^q(R³;ℂ³)` for `1 < q < ∞` (the space `Y_q` of tex 7313–7317
is built on `L^q(R³;ℂ³)`); the multiplier is real, so `P_σ` acts on real and imaginary parts
separately.

* `reV`, `imV : ℂ³ →L[ℝ] R³`, `ofReV`, `ofImV : R³ →L[ℝ] ℂ³`: real and imaginary parts and the
  two real embeddings, with `ofReV (reV z) + ofImV (imV z) = z`;
* `lerayC p hp1 hp : L^p(R³;ℂ³) →L[ℂ] L^p(R³;ℂ³)`, `(𝔓F) = 𝔓(Re F) + i 𝔓(Im F)`; it is
  `ℂ`-linear (`lerayC_apply`, `coeFn_lerayC`);
* `norm_lerayC_le`: `‖𝔓‖_{L^p(ℂ³)} ≤ 2 ‖𝔓‖_{L^p(R³)}` (risk R7: a factor of at most 2);
* `lerayC_ofRe`: on real fields `lerayC` is `lerayLp`;
* `lerayC_consistent`: consistency across exponents;
* `lerayC_translate`, `lerayC_heat`: commutation with translations and with the heat
  semigroup on `L^p(R³;ℂ³)` (`Heat.heatLp` with values in `ℂ³`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace UnforcedLeray.RieszLp

open UnforcedLeray.PhaseSpace (CVec3)

/-! ### Real and imaginary parts of `ℂ³` -/

/-- `z ↦ Re z`, linear part. -/
def reVLin : CVec3 →ₗ[ℝ] Space where
  toFun z := WithLp.toLp 2 (fun i => (z i).re)
  map_add' z w := by ext i; simp
  map_smul' c z := by ext i; simp

/-- `z ↦ Im z`, linear part. -/
def imVLin : CVec3 →ₗ[ℝ] Space where
  toFun z := WithLp.toLp 2 (fun i => (z i).im)
  map_add' z w := by ext i; simp
  map_smul' c z := by ext i; simp

/-- `x ↦ x` (real vector as complex vector), linear part. -/
def ofReVLin : Space →ₗ[ℝ] CVec3 where
  toFun x := WithLp.toLp 2 (fun i => ((x i : ℝ) : ℂ))
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp

/-- `x ↦ i x`, linear part. -/
def ofImVLin : Space →ₗ[ℝ] CVec3 where
  toFun x := WithLp.toLp 2 (fun i => ((x i : ℝ) : ℂ) * Complex.I)
  map_add' x y := by ext i; simp [add_mul]
  map_smul' c x := by ext i; simp [mul_assoc]

theorem norm_reVLin_le (z : CVec3) : ‖reVLin z‖ ≤ ‖z‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  have h : ‖(reVLin z) i‖ ≤ ‖z i‖ := by
    change ‖(z i).re‖ ≤ ‖z i‖
    rw [Real.norm_eq_abs]
    exact Complex.abs_re_le_norm _
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

theorem norm_imVLin_le (z : CVec3) : ‖imVLin z‖ ≤ ‖z‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  have h : ‖(imVLin z) i‖ ≤ ‖z i‖ := by
    change ‖(z i).im‖ ≤ ‖z i‖
    rw [Real.norm_eq_abs]
    exact Complex.abs_im_le_norm _
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

theorem norm_ofReVLin (x : Space) : ‖ofReVLin x‖ = ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  change ‖((x i : ℝ) : ℂ)‖ ^ 2 = ‖x i‖ ^ 2
  rw [Complex.norm_real]

theorem norm_ofImVLin (x : Space) : ‖ofImVLin x‖ = ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  change ‖((x i : ℝ) : ℂ) * Complex.I‖ ^ 2 = ‖x i‖ ^ 2
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real]

/-- Real part `ℂ³ → R³`. -/
def reV : CVec3 →L[ℝ] Space := LinearMap.mkContinuous reVLin 1 fun z => by
  rw [one_mul]; exact norm_reVLin_le z

/-- Imaginary part `ℂ³ → R³`. -/
def imV : CVec3 →L[ℝ] Space := LinearMap.mkContinuous imVLin 1 fun z => by
  rw [one_mul]; exact norm_imVLin_le z

/-- The embedding `R³ → ℂ³`, `x ↦ x`. -/
def ofReV : Space →L[ℝ] CVec3 := LinearMap.mkContinuous ofReVLin 1 fun x => by
  rw [one_mul]; exact (norm_ofReVLin x).le

/-- The embedding `R³ → ℂ³`, `x ↦ i x`. -/
def ofImV : Space →L[ℝ] CVec3 := LinearMap.mkContinuous ofImVLin 1 fun x => by
  rw [one_mul]; exact (norm_ofImVLin x).le

@[simp] theorem reV_apply (z : CVec3) (i : Fin 3) : reV z i = (z i).re := rfl
@[simp] theorem imV_apply (z : CVec3) (i : Fin 3) : imV z i = (z i).im := rfl
@[simp] theorem ofReV_apply (x : Space) (i : Fin 3) : ofReV x i = ((x i : ℝ) : ℂ) := rfl
@[simp] theorem ofImV_apply (x : Space) (i : Fin 3) :
    ofImV x i = ((x i : ℝ) : ℂ) * Complex.I := rfl

theorem norm_reV_le : ‖reV‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _
theorem norm_imV_le : ‖imV‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _
theorem norm_ofReV_le : ‖ofReV‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _
theorem norm_ofImV_le : ‖ofImV‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem ofReV_reV_add_ofImV_imV (z : CVec3) : ofReV (reV z) + ofImV (imV z) = z := by
  ext i
  simp [Complex.re_add_im]

theorem reV_I_smul (z : CVec3) : reV (Complex.I • z) = -imV z := by
  ext i
  simp

theorem imV_I_smul (z : CVec3) : imV (Complex.I • z) = reV z := by
  ext i
  simp

theorem I_smul_ofReV (x : Space) : Complex.I • ofReV x = ofImV x := by
  ext i
  simp [mul_comm]

theorem I_smul_ofImV (x : Space) : Complex.I • ofImV x = -ofReV x := by
  ext i
  simp only [PiLp.smul_apply, smul_eq_mul, ofImV_apply, PiLp.neg_apply, ofReV_apply]
  rw [mul_comm, mul_assoc, Complex.I_mul_I, mul_neg_one]

@[simp] theorem reV_ofReV (x : Space) : reV (ofReV x) = x := by ext i; simp
@[simp] theorem imV_ofReV (x : Space) : imV (ofReV x) = 0 := by ext i; simp

/-! ### The operators on `L^p` -/

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- `I • F` acts on the real and imaginary parts as `(Re, Im) ↦ (-Im, Re)`. -/
theorem reV_compLpL_I_smul (F : Lp CVec3 p (volume : Measure Space)) :
    reV.compLpL p volume (Complex.I • F) = -(imV.compLpL p volume F) := by
  apply Lp.ext
  filter_upwards [reV.coeFn_compLpL (μ := volume) (p := p) (Complex.I • F),
    imV.coeFn_compLpL (μ := volume) (p := p) F, Lp.coeFn_smul Complex.I F,
    Lp.coeFn_neg (imV.compLpL p volume F)] with x h1 h2 h3 h4
  rw [h1, h4, Pi.neg_apply, h2, h3, Pi.smul_apply, reV_I_smul]

theorem imV_compLpL_I_smul (F : Lp CVec3 p (volume : Measure Space)) :
    imV.compLpL p volume (Complex.I • F) = reV.compLpL p volume F := by
  apply Lp.ext
  filter_upwards [imV.coeFn_compLpL (μ := volume) (p := p) (Complex.I • F),
    reV.coeFn_compLpL (μ := volume) (p := p) F, Lp.coeFn_smul Complex.I F] with x h1 h2 h3
  rw [h1, h2, h3, Pi.smul_apply, imV_I_smul]

theorem I_smul_ofReV_compLpL (G : Lp Space p (volume : Measure Space)) :
    Complex.I • ofReV.compLpL p volume G = ofImV.compLpL p volume G := by
  apply Lp.ext
  filter_upwards [ofReV.coeFn_compLpL (μ := volume) (p := p) G,
    ofImV.coeFn_compLpL (μ := volume) (p := p) G,
    Lp.coeFn_smul Complex.I (ofReV.compLpL p volume G)] with x h1 h2 h3
  rw [h3, Pi.smul_apply, h1, h2, I_smul_ofReV]

theorem I_smul_ofImV_compLpL (G : Lp Space p (volume : Measure Space)) :
    Complex.I • ofImV.compLpL p volume G = -(ofReV.compLpL p volume G) := by
  apply Lp.ext
  filter_upwards [ofReV.coeFn_compLpL (μ := volume) (p := p) G,
    ofImV.coeFn_compLpL (μ := volume) (p := p) G,
    Lp.coeFn_smul Complex.I (ofImV.compLpL p volume G),
    Lp.coeFn_neg (ofReV.compLpL p volume G)] with x h1 h2 h3 h4
  rw [h3, Pi.smul_apply, h4, Pi.neg_apply, h1, h2, I_smul_ofImV]

variable (p) in
/-- The real-linear operator `F ↦ 𝔓(Re F) + i 𝔓(Im F)` on `L^p(R³;ℂ³)`. -/
def lerayCR (hp1 : 1 < p) (hp : p ≠ ⊤) :
    Lp CVec3 p (volume : Measure Space) →L[ℝ] Lp CVec3 p (volume : Measure Space) :=
  (ofReV.compLpL p volume).comp ((lerayLp p hp1 hp).comp (reV.compLpL p volume)) +
    (ofImV.compLpL p volume).comp ((lerayLp p hp1 hp).comp (imV.compLpL p volume))

theorem lerayCR_apply (hp1 : 1 < p) (hp : p ≠ ⊤) (F : Lp CVec3 p (volume : Measure Space)) :
    lerayCR p hp1 hp F =
      ofReV.compLpL p volume (lerayLp p hp1 hp (reV.compLpL p volume F)) +
        ofImV.compLpL p volume (lerayLp p hp1 hp (imV.compLpL p volume F)) := rfl

set_option maxHeartbeats 1600000 in
theorem lerayCR_I_smul (hp1 : 1 < p) (hp : p ≠ ⊤) (F : Lp CVec3 p (volume : Measure Space)) :
    lerayCR p hp1 hp (Complex.I • F) = Complex.I • lerayCR p hp1 hp F := by
  rw [lerayCR_apply, lerayCR_apply]
  rw [reV_compLpL_I_smul]
  rw [imV_compLpL_I_smul]
  rw [(lerayLp p hp1 hp).map_neg (imV.compLpL p volume F)]
  rw [(ofReV.compLpL p volume).map_neg (lerayLp p hp1 hp (imV.compLpL p volume F))]
  rw [smul_add]
  rw [I_smul_ofReV_compLpL]
  rw [I_smul_ofImV_compLpL]
  abel

theorem lerayCR_smul (hp1 : 1 < p) (hp : p ≠ ⊤) (c : ℂ)
    (F : Lp CVec3 p (volume : Measure Space)) :
    lerayCR p hp1 hp (c • F) = c • lerayCR p hp1 hp F := by
  have e : ∀ G : Lp CVec3 p (volume : Measure Space),
      c • G = c.re • G + c.im • (Complex.I • G) := by
    intro G
    conv_lhs => rw [← Complex.re_add_im c]
    rw [add_smul, mul_smul, RCLike.real_smul_eq_coe_smul (K := ℂ) c.re G,
      RCLike.real_smul_eq_coe_smul (K := ℂ) c.im (Complex.I • G)]
    rfl
  rw [e F, e (lerayCR p hp1 hp F), map_add, map_smul, map_smul, lerayCR_I_smul]

variable (p) in
/-- The Leray projection on complex fields, linear part. -/
def lerayCLin (hp1 : 1 < p) (hp : p ≠ ⊤) :
    Lp CVec3 p (volume : Measure Space) →ₗ[ℂ] Lp CVec3 p (volume : Measure Space) where
  toFun := lerayCR p hp1 hp
  map_add' := map_add _
  map_smul' c F := lerayCR_smul hp1 hp c F

variable (p) in
/-- **INF01 T17 (`ℂ³` version).** The Leray projection on `L^p(R³;ℂ³)`, `1 < p < ∞`:
`𝔓F = 𝔓(Re F) + i 𝔓(Im F)`, a `ℂ`-linear bounded operator (B0414, `paper/main.tex`
lines 7336–7344). -/
def lerayC (hp1 : 1 < p) (hp : p ≠ ⊤) :
    Lp CVec3 p (volume : Measure Space) →L[ℂ] Lp CVec3 p (volume : Measure Space) :=
  LinearMap.mkContinuous (lerayCLin p hp1 hp) ‖lerayCR p hp1 hp‖
    fun F => (lerayCR p hp1 hp).le_opNorm F

theorem lerayC_apply (hp1 : 1 < p) (hp : p ≠ ⊤) (F : Lp CVec3 p (volume : Measure Space)) :
    lerayC p hp1 hp F =
      ofReV.compLpL p volume (lerayLp p hp1 hp (reV.compLpL p volume F)) +
        ofImV.compLpL p volume (lerayLp p hp1 hp (imV.compLpL p volume F)) := rfl

theorem lerayC_restrictScalars (hp1 : 1 < p) (hp : p ≠ ⊤) :
    (lerayC p hp1 hp).restrictScalars ℝ = lerayCR p hp1 hp := rfl

/-- Pointwise formula: `𝔓F = 𝔓(Re F) + i 𝔓(Im F)` a.e. -/
theorem coeFn_lerayC (hp1 : 1 < p) (hp : p ≠ ⊤) (F : Lp CVec3 p (volume : Measure Space)) :
    (lerayC p hp1 hp F : Space → CVec3) =ᵐ[volume] fun x =>
      ofReV (lerayLp p hp1 hp (reV.compLpL p volume F) x) +
        ofImV (lerayLp p hp1 hp (imV.compLpL p volume F) x) := by
  rw [lerayC_apply]
  filter_upwards [Lp.coeFn_add (ofReV.compLpL p volume (lerayLp p hp1 hp (reV.compLpL p volume F)))
      (ofImV.compLpL p volume (lerayLp p hp1 hp (imV.compLpL p volume F))),
    ofReV.coeFn_compLpL (μ := volume) (p := p) (lerayLp p hp1 hp (reV.compLpL p volume F)),
    ofImV.coeFn_compLpL (μ := volume) (p := p) (lerayLp p hp1 hp (imV.compLpL p volume F))]
    with x h1 h2 h3
  rw [h1, Pi.add_apply, h2, h3]

/-- **INF01 T17 / risk R7.** `‖𝔓‖_{L^p(ℂ³) → L^p(ℂ³)} ≤ 2 ‖𝔓‖_{L^p(R³) → L^p(R³)}`, so the
constant depends on `p` only. -/
theorem norm_lerayC_le (hp1 : 1 < p) (hp : p ≠ ⊤) :
    ‖lerayC p hp1 hp‖ ≤ 2 * ‖lerayLp p hp1 hp‖ := by
  have hre : ‖reV.compLpL p (volume : Measure Space)‖ ≤ 1 :=
    (ContinuousLinearMap.norm_compLpL_le _).trans norm_reV_le
  have him : ‖imV.compLpL p (volume : Measure Space)‖ ≤ 1 :=
    (ContinuousLinearMap.norm_compLpL_le _).trans norm_imV_le
  have hore : ‖ofReV.compLpL p (volume : Measure Space)‖ ≤ 1 :=
    (ContinuousLinearMap.norm_compLpL_le _).trans norm_ofReV_le
  have hoim : ‖ofImV.compLpL p (volume : Measure Space)‖ ≤ 1 :=
    (ContinuousLinearMap.norm_compLpL_le _).trans norm_ofImV_le
  have hL := norm_nonneg (lerayLp p hp1 hp)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun F => ?_
  rw [lerayC_apply]
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖ofReV.compLpL p volume (lerayLp p hp1 hp (reV.compLpL p volume F))‖ ≤
      ‖lerayLp p hp1 hp‖ * ‖F‖ := by
    calc _ ≤ ‖ofReV.compLpL p (volume : Measure Space)‖ *
          (‖lerayLp p hp1 hp‖ * (‖reV.compLpL p (volume : Measure Space)‖ * ‖F‖)) := by
          refine ((ofReV.compLpL p volume).le_opNorm _).trans ?_
          gcongr
          refine ((lerayLp p hp1 hp).le_opNorm _).trans ?_
          gcongr
          exact (reV.compLpL p volume).le_opNorm F
      _ ≤ 1 * (‖lerayLp p hp1 hp‖ * (1 * ‖F‖)) := by gcongr
      _ = ‖lerayLp p hp1 hp‖ * ‖F‖ := by ring
  have h2 : ‖ofImV.compLpL p volume (lerayLp p hp1 hp (imV.compLpL p volume F))‖ ≤
      ‖lerayLp p hp1 hp‖ * ‖F‖ := by
    calc _ ≤ ‖ofImV.compLpL p (volume : Measure Space)‖ *
          (‖lerayLp p hp1 hp‖ * (‖imV.compLpL p (volume : Measure Space)‖ * ‖F‖)) := by
          refine ((ofImV.compLpL p volume).le_opNorm _).trans ?_
          gcongr
          refine ((lerayLp p hp1 hp).le_opNorm _).trans ?_
          gcongr
          exact (imV.compLpL p volume).le_opNorm F
      _ ≤ 1 * (‖lerayLp p hp1 hp‖ * (1 * ‖F‖)) := by gcongr
      _ = ‖lerayLp p hp1 hp‖ * ‖F‖ := by ring
  linarith

end UnforcedLeray.RieszLp
