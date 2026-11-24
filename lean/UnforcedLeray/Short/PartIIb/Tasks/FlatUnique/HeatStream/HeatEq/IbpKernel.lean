import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.HeatStream.HeatEq.TauDeriv
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.HeatStream.NiceClosure
import UnforcedLeray.Units.B0296.Kernel

/-!
# Part II-b, helper for leaf `PartII-b:T11/3/4` (`HeatConvEq`): Gaussian integration by parts

Source of record: `the November 2 reference manuscript`, line 1924 and lines
1923-1927.

For the planar Gaussian `K = heatKernel2 θ` (`θ > 0`), the age derivative satisfies
`∂_θ K = (∂_q² K) + (∂_η² K)` with `∂_q² K = (q²/(4θ²) - 1/(2θ)) K` and the same in `η`. Two
Gaussian integrations by parts per coordinate (Mathlib's
`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`) transfer `∂_q²` and `∂_η²` from `K` to the
nice stream `ζ`. The explicit derivatives are computed from `B0296.dHeatKernel`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-! ### The one-dimensional kernel and its first derivative -/

theorem hce_g_diff {θ : ℝ} (hθ : θ ≠ 0) :
    Differentiable ℝ (UnforcedLeray.B0191.heatKernel 1 θ) :=
  fun x => (UnforcedLeray.B0296.hasDerivAt_heatKernel hθ x).differentiableAt

theorem hce_dH_hasDerivAt {θ : ℝ} (hθ : θ ≠ 0) (x : ℝ) :
    HasDerivAt (UnforcedLeray.B0296.dHeatKernel θ)
      (-(1 / (2 * θ)) * UnforcedLeray.B0191.heatKernel 1 θ x +
        -(x / (2 * θ)) * UnforcedLeray.B0296.dHeatKernel θ x) x :=
  ((hasDerivAt_id' x).div_const (2 * θ)).neg.mul
    (UnforcedLeray.B0296.hasDerivAt_heatKernel hθ x)

theorem hce_dH_diff {θ : ℝ} (hθ : θ ≠ 0) :
    Differentiable ℝ (UnforcedLeray.B0296.dHeatKernel θ) :=
  fun x => (hce_dH_hasDerivAt hθ x).differentiableAt

/-- `∂_q K` as a function on the plane: `dHeatKernel(q) g(η)`. -/
def hceD1 (θ : ℝ) (v : ℝ × ℝ) : ℝ :=
  UnforcedLeray.B0296.dHeatKernel θ v.1 * UnforcedLeray.B0191.heatKernel 1 θ v.2

/-- `∂_η K` as a function on the plane: `g(q) dHeatKernel(η)`. -/
def hceD2 (θ : ℝ) (v : ℝ × ℝ) : ℝ :=
  UnforcedLeray.B0191.heatKernel 1 θ v.1 * UnforcedLeray.B0296.dHeatKernel θ v.2

theorem hce_K_diff {θ : ℝ} (hθ : θ ≠ 0) :
    Differentiable ℝ (UnforcedLeray.B0284.heatKernel2 θ) := by
  have hg := hce_g_diff hθ
  exact (hg.comp differentiable_fst).mul (hg.comp differentiable_snd)

theorem hceD1_diff {θ : ℝ} (hθ : θ ≠ 0) : Differentiable ℝ (hceD1 θ) :=
  ((hce_dH_diff hθ).comp differentiable_fst).mul ((hce_g_diff hθ).comp differentiable_snd)

theorem hceD2_diff {θ : ℝ} (hθ : θ ≠ 0) : Differentiable ℝ (hceD2 θ) :=
  ((hce_g_diff hθ).comp differentiable_fst).mul ((hce_dH_diff hθ).comp differentiable_snd)

theorem hceD1_eq {θ : ℝ} (v : ℝ × ℝ) :
    hceD1 θ v = (-(1 / (2 * θ)) * v.1 + 0 * v.1 ^ 2 + 0) *
      UnforcedLeray.B0284.heatKernel2 θ v := by
  unfold hceD1 UnforcedLeray.B0284.heatKernel2 UnforcedLeray.B0296.dHeatKernel
  ring

theorem hceD2_eq {θ : ℝ} (v : ℝ × ℝ) :
    hceD2 θ v = (-(1 / (2 * θ)) * v.2 + 0 * v.2 ^ 2 + 0) *
      UnforcedLeray.B0284.heatKernel2 θ v := by
  unfold hceD2 UnforcedLeray.B0284.heatKernel2 UnforcedLeray.B0296.dHeatKernel
  ring

/-- The `q`-slice of `∂_q K`: its derivative is `(q²/(4θ²) - 1/(2θ)) K`. -/
theorem hceD1_hasDerivAt {θ : ℝ} (hθ : θ ≠ 0) (x y : ℝ) :
    HasDerivAt (fun t : ℝ => hceD1 θ (t, y))
      ((x ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) * UnforcedLeray.B0284.heatKernel2 θ (x, y)) x := by
  have h := (hce_dH_hasDerivAt hθ x).mul_const (UnforcedLeray.B0191.heatKernel 1 θ y)
  show HasDerivAt (fun t : ℝ => UnforcedLeray.B0296.dHeatKernel θ t *
    UnforcedLeray.B0191.heatKernel 1 θ y) _ x
  refine h.congr_deriv ?_
  simp only [UnforcedLeray.B0284.heatKernel2, UnforcedLeray.B0296.dHeatKernel]
  ring

/-- The `η`-slice of `∂_η K`: its derivative is `(η²/(4θ²) - 1/(2θ)) K`. -/
theorem hceD2_hasDerivAt {θ : ℝ} (hθ : θ ≠ 0) (x y : ℝ) :
    HasDerivAt (fun t : ℝ => hceD2 θ (x, t))
      ((y ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) * UnforcedLeray.B0284.heatKernel2 θ (x, y)) y := by
  have h := (hce_dH_hasDerivAt hθ y).const_mul (UnforcedLeray.B0191.heatKernel 1 θ x)
  show HasDerivAt (fun t : ℝ => UnforcedLeray.B0191.heatKernel 1 θ x *
    UnforcedLeray.B0296.dHeatKernel θ t) _ y
  refine h.congr_deriv ?_
  simp only [UnforcedLeray.B0284.heatKernel2, UnforcedLeray.B0296.dHeatKernel]
  ring

/-! ### Slices and first derivatives -/

theorem hce_slice_fst {f : ℝ × ℝ → ℝ} (hf : Differentiable ℝ f) (a b : ℝ) :
    HasDerivAt (fun t : ℝ => f (t, b)) (fderiv ℝ f (a, b) ((1 : ℝ), (0 : ℝ))) a := by
  have h1 : HasDerivAt (fun t : ℝ => ((t, b) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) a :=
    (hasDerivAt_id' a).prodMk (hasDerivAt_const a b)
  exact (hf (a, b)).hasFDerivAt.comp_hasDerivAt a h1

theorem hce_slice_snd {f : ℝ × ℝ → ℝ} (hf : Differentiable ℝ f) (a b : ℝ) :
    HasDerivAt (fun t : ℝ => f (a, t)) (fderiv ℝ f (a, b) ((0 : ℝ), (1 : ℝ))) b := by
  have h1 : HasDerivAt (fun t : ℝ => ((a, t) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) b :=
    (hasDerivAt_const b a).prodMk (hasDerivAt_id' b)
  exact (hf (a, b)).hasFDerivAt.comp_hasDerivAt b h1

theorem hce_fderiv_K_fst {θ : ℝ} (hθ : θ ≠ 0) (w : ℝ × ℝ) :
    fderiv ℝ (UnforcedLeray.B0284.heatKernel2 θ) w ((1 : ℝ), (0 : ℝ)) = hceD1 θ w := by
  obtain ⟨a, b⟩ := w
  have h1 := hce_slice_fst (hce_K_diff hθ) a b
  have h2 := UnforcedLeray.B0296.hasDerivAt_heatKernel2_fst hθ (a, b)
  exact h1.unique h2

theorem hce_fderiv_K_snd {θ : ℝ} (hθ : θ ≠ 0) (w : ℝ × ℝ) :
    fderiv ℝ (UnforcedLeray.B0284.heatKernel2 θ) w ((0 : ℝ), (1 : ℝ)) = hceD2 θ w := by
  obtain ⟨a, b⟩ := w
  have h1 := hce_slice_snd (hce_K_diff hθ) a b
  have h2 := UnforcedLeray.B0296.hasDerivAt_heatKernel2_snd hθ (a, b)
  exact h1.unique h2

theorem hce_fderiv_D1_fst {θ : ℝ} (hθ : θ ≠ 0) (w : ℝ × ℝ) :
    fderiv ℝ (hceD1 θ) w ((1 : ℝ), (0 : ℝ)) =
      (w.1 ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) * UnforcedLeray.B0284.heatKernel2 θ w := by
  obtain ⟨a, b⟩ := w
  have h1 := hce_slice_fst (hceD1_diff hθ) a b
  have h2 := hceD1_hasDerivAt hθ a b
  exact h1.unique h2

theorem hce_fderiv_D2_snd {θ : ℝ} (hθ : θ ≠ 0) (w : ℝ × ℝ) :
    fderiv ℝ (hceD2 θ) w ((0 : ℝ), (1 : ℝ)) =
      (w.2 ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) * UnforcedLeray.B0284.heatKernel2 θ w := by
  obtain ⟨a, b⟩ := w
  have h1 := hce_slice_snd (hceD2_diff hθ) a b
  have h2 := hceD2_hasDerivAt hθ a b
  exact h1.unique h2

theorem hce_fderiv_sub {f : ℝ × ℝ → ℝ} (hf : Differentiable ℝ f) (z e w : ℝ × ℝ) :
    fderiv ℝ (fun y : ℝ × ℝ => f (z - y)) w e = -(fderiv ℝ f (z - w) e) := by
  have hm : HasFDerivAt (fun y : ℝ × ℝ => z - y) (-ContinuousLinearMap.id ℝ (ℝ × ℝ)) w :=
    (hasFDerivAt_id w).const_sub z
  have hcomp := (hf (z - w)).hasFDerivAt.comp w hm
  change fderiv ℝ (f ∘ (fun y : ℝ × ℝ => z - y)) w e = _
  rw [hcomp.fderiv]
  simp

/-! ### Bounds and integrability -/

theorem hce_quad_bound (a b d t s : ℝ) :
    |a * t + b * t ^ 2 + d| ≤ (|a| + |b| + |d|) * (1 + t ^ 2 + s ^ 2) := by
  have h1 : |t| ≤ 1 + t ^ 2 + s ^ 2 := by
    nlinarith [sq_abs t, abs_nonneg t, sq_nonneg (|t| - 1 / 2), sq_nonneg s]
  have h2 : t ^ 2 ≤ 1 + t ^ 2 + s ^ 2 := by nlinarith [sq_nonneg s]
  have h3 : (1 : ℝ) ≤ 1 + t ^ 2 + s ^ 2 := by nlinarith [sq_nonneg t, sq_nonneg s]
  have hA : |a * t + b * t ^ 2 + d| ≤ |a * t| + |b * t ^ 2| + |d| := by
    have := abs_add_le (a * t + b * t ^ 2) d
    have := abs_add_le (a * t) (b * t ^ 2)
    linarith
  rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg t)] at hA
  have e1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg a)
  have e2 := mul_le_mul_of_nonneg_left h2 (abs_nonneg b)
  have e3 := le_mul_of_one_le_right (abs_nonneg d) h3
  have key : (|a| + |b| + |d|) * (1 + t ^ 2 + s ^ 2) =
      |a| * (1 + t ^ 2 + s ^ 2) + |b| * (1 + t ^ 2 + s ^ 2) + |d| * (1 + t ^ 2 + s ^ 2) := by
    ring
  linarith

theorem hce_abs_zeta_le {c : ℝ} (hc : 0 < c) {ζ : ℝ × ℝ → ℝ} (hζ : NiceStream c ζ) :
    ∃ B : ℝ, ∀ y : ℝ × ℝ, |ζ y| ≤ B := by
  obtain ⟨B, -, hB⟩ := hcs_nice_iteratedFDeriv_bound hc hζ 0
  exact ⟨B, fun y => by simpa [Real.norm_eq_abs] using hB y⟩

theorem hce_abs_fderiv_le {c : ℝ} (hc : 0 < c) {ζ : ℝ × ℝ → ℝ} (hζ : NiceStream c ζ)
    (v : ℝ × ℝ) : ∃ M : ℝ, ∀ y : ℝ × ℝ, |fderiv ℝ ζ y v| ≤ M := by
  obtain ⟨M, -, hM⟩ := hcs_nice_iteratedFDeriv_bound hc hζ 1
  refine ⟨M * ‖v‖, fun y => ?_⟩
  have h2 : ‖fderiv ℝ ζ y‖ ≤ M := by simpa using hM y
  have h3 : ‖fderiv ℝ ζ y v‖ ≤ ‖fderiv ℝ ζ y‖ * ‖v‖ := (fderiv ℝ ζ y).le_opNorm v
  rw [← Real.norm_eq_abs]
  exact h3.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg v))

theorem hce_int_of_bound {θ C B : ℝ} (hθ : 0 < θ) {p c : ℝ × ℝ → ℝ} (hpc : Continuous p)
    (hcc : Continuous c) (hp : ∀ w : ℝ × ℝ, |p w| ≤ C * (1 + w.1 ^ 2 + w.2 ^ 2))
    (hc : ∀ w : ℝ × ℝ, |c w| ≤ B) (hC : 0 ≤ C) :
    Integrable (fun w : ℝ × ℝ => p w * UnforcedLeray.B0284.heatKernel2 θ w * c w) := by
  have hK : Continuous (UnforcedLeray.B0284.heatKernel2 θ) := (hce_K_diff hθ.ne').continuous
  have hK0 : ∀ w : ℝ × ℝ, 0 ≤ UnforcedLeray.B0284.heatKernel2 θ w :=
    fun w => UnforcedLeray.B0284.heatKernel2_nonneg hθ w
  have hbd := (UnforcedLeray.HeatCylinder.integrable_one_add_sq_mul_heatKernel2 hθ).const_mul
    (C * B)
  refine hbd.mono' ((hpc.mul hK).mul hcc).aestronglyMeasurable (ae_of_all _ fun w => ?_)
  show ‖p w * UnforcedLeray.B0284.heatKernel2 θ w * c w‖ ≤
    C * B * ((1 + w.1 ^ 2 + w.2 ^ 2) * UnforcedLeray.B0284.heatKernel2 θ w)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hK0 w)]
  have hw : 0 ≤ C * (1 + w.1 ^ 2 + w.2 ^ 2) * UnforcedLeray.B0284.heatKernel2 θ w :=
    mul_nonneg (mul_nonneg hC (by positivity)) (hK0 w)
  calc |p w| * UnforcedLeray.B0284.heatKernel2 θ w * |c w|
      ≤ (C * (1 + w.1 ^ 2 + w.2 ^ 2)) * UnforcedLeray.B0284.heatKernel2 θ w * B :=
        mul_le_mul (mul_le_mul_of_nonneg_right (hp w) (hK0 w)) (hc w) (abs_nonneg _) hw
    _ = C * B * ((1 + w.1 ^ 2 + w.2 ^ 2) * UnforcedLeray.B0284.heatKernel2 θ w) := by ring

theorem hce_int_K {θ B : ℝ} (hθ : 0 < θ) {c : ℝ × ℝ → ℝ} (hcc : Continuous c)
    (hc : ∀ w : ℝ × ℝ, |c w| ≤ B) :
    Integrable (fun w : ℝ × ℝ => UnforcedLeray.B0284.heatKernel2 θ w * c w) :=
  (UnforcedLeray.B0284.integrable_heatKernel2 hθ).mul_bdd hcc.aestronglyMeasurable
    (ae_of_all _ fun w => by rw [Real.norm_eq_abs]; exact hc w)

theorem hce_int_D1 {θ B : ℝ} (hθ : 0 < θ) {c : ℝ × ℝ → ℝ} (hcc : Continuous c)
    (hc : ∀ w : ℝ × ℝ, |c w| ≤ B) :
    Integrable (fun w : ℝ × ℝ => hceD1 θ w * c w) := by
  have hp : ∀ w : ℝ × ℝ, |-(1 / (2 * θ)) * w.1 + 0 * w.1 ^ 2 + 0| ≤
      (|-(1 / (2 * θ))| + |0| + |0|) * (1 + w.1 ^ 2 + w.2 ^ 2) :=
    fun w => hce_quad_bound (-(1 / (2 * θ))) 0 0 w.1 w.2
  refine (hce_int_of_bound (C := |-(1 / (2 * θ))| + |0| + |0|)
    (p := fun w : ℝ × ℝ => -(1 / (2 * θ)) * w.1 + 0 * w.1 ^ 2 + 0) (c := c) (B := B) hθ
    (by fun_prop) hcc hp hc (by positivity)).congr (ae_of_all _ fun w => ?_)
  dsimp only
  rw [hceD1_eq]

theorem hce_int_D2 {θ B : ℝ} (hθ : 0 < θ) {c : ℝ × ℝ → ℝ} (hcc : Continuous c)
    (hc : ∀ w : ℝ × ℝ, |c w| ≤ B) :
    Integrable (fun w : ℝ × ℝ => hceD2 θ w * c w) := by
  have hp : ∀ w : ℝ × ℝ, |-(1 / (2 * θ)) * w.2 + 0 * w.2 ^ 2 + 0| ≤
      (|-(1 / (2 * θ))| + |0| + |0|) * (1 + w.1 ^ 2 + w.2 ^ 2) := by
    intro w
    have h := hce_quad_bound (-(1 / (2 * θ))) 0 0 w.2 w.1
    have e : (|-(1 / (2 * θ))| + |0| + |0|) * (1 + w.2 ^ 2 + w.1 ^ 2) =
        (|-(1 / (2 * θ))| + |0| + |0|) * (1 + w.1 ^ 2 + w.2 ^ 2) := by ring
    exact h.trans_eq e
  refine (hce_int_of_bound (C := |-(1 / (2 * θ))| + |0| + |0|)
    (p := fun w : ℝ × ℝ => -(1 / (2 * θ)) * w.2 + 0 * w.2 ^ 2 + 0) (c := c) (B := B) hθ
    (by fun_prop) hcc hp hc (by positivity)).congr (ae_of_all _ fun w => ?_)
  dsimp only
  rw [hceD2_eq]

theorem hce_int_A1 {θ c : ℝ} (hθ : 0 < θ) (hc : 0 < c) {ζ : ℝ × ℝ → ℝ} (hζ : NiceStream c ζ)
    (z : ℝ × ℝ) :
    Integrable (fun w : ℝ × ℝ => (w.1 ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) *
      UnforcedLeray.B0284.heatKernel2 θ w * ζ (z - w)) := by
  obtain ⟨B, hB⟩ := hce_abs_zeta_le hc hζ
  have hp : ∀ w : ℝ × ℝ, |0 * w.1 + (1 / (4 * θ ^ 2)) * w.1 ^ 2 + -(1 / (2 * θ))| ≤
      (|0| + |1 / (4 * θ ^ 2)| + |-(1 / (2 * θ))|) * (1 + w.1 ^ 2 + w.2 ^ 2) :=
    fun w => hce_quad_bound 0 (1 / (4 * θ ^ 2)) (-(1 / (2 * θ))) w.1 w.2
  have hcc : Continuous (fun w : ℝ × ℝ => ζ (z - w)) :=
    hζ.smooth.continuous.comp (continuous_const.sub continuous_id)
  refine (hce_int_of_bound (C := |0| + |1 / (4 * θ ^ 2)| + |-(1 / (2 * θ))|)
    (p := fun w : ℝ × ℝ => 0 * w.1 + (1 / (4 * θ ^ 2)) * w.1 ^ 2 + -(1 / (2 * θ)))
    (c := fun w => ζ (z - w)) (B := B) hθ (by fun_prop) hcc hp (fun w => hB (z - w))
    (by positivity)).congr (ae_of_all _ fun w => by ring)

theorem hce_int_A2 {θ c : ℝ} (hθ : 0 < θ) (hc : 0 < c) {ζ : ℝ × ℝ → ℝ} (hζ : NiceStream c ζ)
    (z : ℝ × ℝ) :
    Integrable (fun w : ℝ × ℝ => (w.2 ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) *
      UnforcedLeray.B0284.heatKernel2 θ w * ζ (z - w)) := by
  obtain ⟨B, hB⟩ := hce_abs_zeta_le hc hζ
  have hp : ∀ w : ℝ × ℝ, |0 * w.2 + (1 / (4 * θ ^ 2)) * w.2 ^ 2 + -(1 / (2 * θ))| ≤
      (|0| + |1 / (4 * θ ^ 2)| + |-(1 / (2 * θ))|) * (1 + w.1 ^ 2 + w.2 ^ 2) := by
    intro w
    have h := hce_quad_bound 0 (1 / (4 * θ ^ 2)) (-(1 / (2 * θ))) w.2 w.1
    have e : (|0| + |1 / (4 * θ ^ 2)| + |-(1 / (2 * θ))|) * (1 + w.2 ^ 2 + w.1 ^ 2) =
        (|0| + |1 / (4 * θ ^ 2)| + |-(1 / (2 * θ))|) * (1 + w.1 ^ 2 + w.2 ^ 2) := by ring
    exact h.trans_eq e
  have hcc : Continuous (fun w : ℝ × ℝ => ζ (z - w)) :=
    hζ.smooth.continuous.comp (continuous_const.sub continuous_id)
  refine (hce_int_of_bound (C := |0| + |1 / (4 * θ ^ 2)| + |-(1 / (2 * θ))|)
    (p := fun w : ℝ × ℝ => 0 * w.2 + (1 / (4 * θ ^ 2)) * w.2 ^ 2 + -(1 / (2 * θ)))
    (c := fun w => ζ (z - w)) (B := B) hθ (by fun_prop) hcc hp (fun w => hB (z - w))
    (by positivity)).congr (ae_of_all _ fun w => by ring)

/-! ### Integration by parts in `q` and in `η` -/

theorem hce_ibp_fst {θ c : ℝ} (hθ : 0 < θ) (hc : 0 < c) {ζ : ℝ × ℝ → ℝ} (hζ : NiceStream c ζ)
    (z : ℝ × ℝ) :
    ∫ w : ℝ × ℝ, (w.1 ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) *
        UnforcedLeray.B0284.heatKernel2 θ w * ζ (z - w) =
      ∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ w * qDer (qDer ζ) (z - w) := by
  have hθ0 : θ ≠ 0 := hθ.ne'
  have hζd : Differentiable ℝ ζ := hζ.smooth.differentiable (by simp)
  have hζc : Continuous ζ := hζ.smooth.continuous
  have hQN : NiceStream c (qDer ζ) := (niceStreamClosure c ζ ζ 0 hζ hζ).1
  have hQd : Differentiable ℝ (qDer ζ) := hQN.smooth.differentiable (by simp)
  have hQc : Continuous (qDer ζ) := hQN.smooth.continuous
  have hQQc : Continuous (qDer (qDer ζ)) :=
    (niceStreamClosure c (qDer ζ) (qDer ζ) 0 hQN hQN).1.smooth.continuous
  have hsub : Differentiable ℝ (fun w : ℝ × ℝ => z - w) :=
    (differentiable_const z).sub differentiable_id
  have hsubc : Continuous (fun w : ℝ × ℝ => z - w) := continuous_const.sub continuous_id
  obtain ⟨B, hB⟩ := hce_abs_zeta_le hc hζ
  obtain ⟨M, hM⟩ := hce_abs_fderiv_le hc hζ ((1 : ℝ), (0 : ℝ))
  obtain ⟨N, hN⟩ := hce_abs_fderiv_le hc hQN ((1 : ℝ), (0 : ℝ))
  have hG1d : Differentiable ℝ (fun w : ℝ × ℝ => ζ (z - w)) := hζd.comp hsub
  have hQzd : Differentiable ℝ (fun w : ℝ × ℝ => qDer ζ (z - w)) := hQd.comp hsub
  have hG1c : Continuous (fun w : ℝ × ℝ => ζ (z - w)) := hζc.comp hsubc
  have hQzc : Continuous (fun w : ℝ × ℝ => qDer ζ (z - w)) := hQc.comp hsubc
  have hQQzc : Continuous (fun w : ℝ × ℝ => qDer (qDer ζ) (z - w)) := hQQc.comp hsubc
  have hGder : ∀ x : ℝ × ℝ,
      fderiv ℝ (fun w : ℝ × ℝ => ζ (z - w)) x ((1 : ℝ), (0 : ℝ)) = -(qDer ζ (z - x)) :=
    fun x => hce_fderiv_sub hζd z _ x
  have hQder : ∀ x : ℝ × ℝ,
      fderiv ℝ (fun w : ℝ × ℝ => qDer ζ (z - w)) x ((1 : ℝ), (0 : ℝ)) =
        -(qDer (qDer ζ) (z - x)) :=
    fun x => hce_fderiv_sub hQd z _ x
  -- first integration by parts: `f = ∂_q K` against `g = ζ(z - ·)`
  have hI1a : Integrable (fun x : ℝ × ℝ =>
      fderiv ℝ (hceD1 θ) x ((1 : ℝ), (0 : ℝ)) * ζ (z - x)) :=
    (hce_int_A1 hθ hc hζ z).congr (ae_of_all _ fun x => by
      dsimp only
      rw [hce_fderiv_D1_fst hθ0])
  have hI1b : Integrable (fun x : ℝ × ℝ =>
      hceD1 θ x * fderiv ℝ (fun w : ℝ × ℝ => ζ (z - w)) x ((1 : ℝ), (0 : ℝ))) :=
    (hce_int_D1 hθ (c := fun w : ℝ × ℝ => -(qDer ζ (z - w))) hQzc.neg
      (fun w => by rw [abs_neg]; exact hM (z - w))).congr (ae_of_all _ fun x => by
        dsimp only
        rw [hGder x])
  have hI1c : Integrable (fun x : ℝ × ℝ => hceD1 θ x * ζ (z - x)) :=
    hce_int_D1 hθ hG1c (fun w => hB (z - w))
  have ibp1 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := hceD1 θ) (g := fun w : ℝ × ℝ => ζ (z - w)) (v := ((1 : ℝ), (0 : ℝ)))
    hI1a hI1b hI1c (fun x _ => (hceD1_diff hθ0) x) (fun x _ => hG1d x)
  have eL1 : ∫ x : ℝ × ℝ, hceD1 θ x * fderiv ℝ (fun w : ℝ × ℝ => ζ (z - w)) x
      ((1 : ℝ), (0 : ℝ)) = -∫ x : ℝ × ℝ, hceD1 θ x * qDer ζ (z - x) := by
    rw [← integral_neg]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    dsimp only
    rw [hGder x]
    ring
  have eR1 : ∫ x : ℝ × ℝ, fderiv ℝ (hceD1 θ) x ((1 : ℝ), (0 : ℝ)) * ζ (z - x) =
      ∫ x : ℝ × ℝ, (x.1 ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) *
        UnforcedLeray.B0284.heatKernel2 θ x * ζ (z - x) := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    dsimp only
    rw [hce_fderiv_D1_fst hθ0]
  have key1 : ∫ x : ℝ × ℝ, hceD1 θ x * qDer ζ (z - x) =
      ∫ x : ℝ × ℝ, (x.1 ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) *
        UnforcedLeray.B0284.heatKernel2 θ x * ζ (z - x) := by
    rw [eL1, eR1] at ibp1
    linarith
  -- second integration by parts: `f = K` against `g = ∂_q ζ(z - ·)`
  have hI2a : Integrable (fun x : ℝ × ℝ =>
      fderiv ℝ (UnforcedLeray.B0284.heatKernel2 θ) x ((1 : ℝ), (0 : ℝ)) * qDer ζ (z - x)) :=
    (hce_int_D1 hθ hQzc (fun w => hM (z - w))).congr (ae_of_all _ fun x => by
      dsimp only
      rw [hce_fderiv_K_fst hθ0])
  have hI2b : Integrable (fun x : ℝ × ℝ =>
      UnforcedLeray.B0284.heatKernel2 θ x *
        fderiv ℝ (fun w : ℝ × ℝ => qDer ζ (z - w)) x ((1 : ℝ), (0 : ℝ))) :=
    (hce_int_K hθ (c := fun w : ℝ × ℝ => -(qDer (qDer ζ) (z - w))) hQQzc.neg
      (fun w => by rw [abs_neg]; exact hN (z - w))).congr (ae_of_all _ fun x => by
        dsimp only
        rw [hQder x])
  have hI2c : Integrable (fun x : ℝ × ℝ =>
      UnforcedLeray.B0284.heatKernel2 θ x * qDer ζ (z - x)) :=
    hce_int_K hθ hQzc (fun w => hM (z - w))
  have ibp2 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := UnforcedLeray.B0284.heatKernel2 θ) (g := fun w : ℝ × ℝ => qDer ζ (z - w))
    (v := ((1 : ℝ), (0 : ℝ))) hI2a hI2b hI2c
    (fun x _ => (hce_K_diff hθ0) x) (fun x _ => hQzd x)
  have eL2 : ∫ x : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ x *
      fderiv ℝ (fun w : ℝ × ℝ => qDer ζ (z - w)) x ((1 : ℝ), (0 : ℝ)) =
      -∫ x : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ x * qDer (qDer ζ) (z - x) := by
    rw [← integral_neg]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    dsimp only
    rw [hQder x]
    ring
  have eR2 : ∫ x : ℝ × ℝ, fderiv ℝ (UnforcedLeray.B0284.heatKernel2 θ) x
      ((1 : ℝ), (0 : ℝ)) * qDer ζ (z - x) =
      ∫ x : ℝ × ℝ, hceD1 θ x * qDer ζ (z - x) := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    dsimp only
    rw [hce_fderiv_K_fst hθ0]
  have key2 : ∫ x : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ x * qDer (qDer ζ) (z - x) =
      ∫ x : ℝ × ℝ, hceD1 θ x * qDer ζ (z - x) := by
    rw [eL2, eR2] at ibp2
    linarith
  linarith

end UnforcedLeray.Short.IIb
