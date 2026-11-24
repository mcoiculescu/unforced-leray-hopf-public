import UnforcedLeray.Lib.Parabolic.Hormander

/-!
# Space-time test functions and their derivatives (INF02 T6, preliminaries)


target T6 ("causal Duhamel on `C_c^∞`"). The manuscript's distributional formulation of
eq:free-stress-11 (`paper/main.tex` lines 7447–7477, blueprint unit B0423) tests against smooth
compactly supported functions on `ℝ × ℝ^d`; this file fixes that class and the derivative
operators used for it.

* `IsSTTest f`: `f : ℝ × ℝ^d → ℝ` is `C^∞` with compact support; closed under sums, scalar
  multiples and directional derivatives (`IsSTTest.dirD`).
* `dirD v f X = Df(X) v`; `sD i = ∂_{x_i}` (direction `(0, eᵢ)`), `tD = ∂_t` (direction
  `(1, 0)`), `sD2 i j = ∂_{x_i}∂_{x_j}`, `sLap = Σᵢ ∂_{x_i}²`.
* Slices: `x ↦ f(t, x)` is `C^∞` with compact support (`IsSTTest.slice_contDiff`,
  `IsSTTest.slice_hasCompactSupport`), and its derivative is the spatial derivative of `f`
  (`fderiv_slice`).
* `IsSTTest.timeBound`: the time support of a test lies in some `[-R, R]`.
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.Parabolic

open MeasureTheory Real Set
open scoped ENNReal NNReal ContDiff

open UnforcedLeray.Gaussian (Euc gaussKernel)

variable {d : ℕ}

/-- Smooth compactly supported test functions on `ℝ × ℝ^d`. -/
def IsSTTest (f : PS d → ℝ) : Prop := ContDiff ℝ ∞ f ∧ HasCompactSupport f

/-- Directional derivative `X ↦ Df(X) v`. -/
def dirD (v : PS d) (f : PS d → ℝ) (X : PS d) : ℝ := fderiv ℝ f X v

/-- The spatial direction `(0, eᵢ)`. -/
abbrev sdir (i : Fin d) : PS d := (0, ev i)

/-- The time direction `(1, 0)`. -/
abbrev tdir : PS d := (1, 0)

/-- `∂_{x_i}`. -/
abbrev sD (i : Fin d) (f : PS d → ℝ) : PS d → ℝ := dirD (sdir i) f

/-- `∂_t`. -/
abbrev tD (f : PS d → ℝ) : PS d → ℝ := dirD tdir f

/-- `∂_{x_i}∂_{x_j}`. -/
abbrev sD2 (i j : Fin d) (f : PS d → ℝ) : PS d → ℝ := sD i (sD j f)

/-- The spatial Laplacian `Σᵢ ∂_{x_i}²`. -/
def sLap (f : PS d → ℝ) (X : PS d) : ℝ := ∑ i, sD2 i i f X

namespace IsSTTest

variable {f g : PS d → ℝ}

theorem continuous (hf : IsSTTest f) : Continuous f := hf.1.continuous

theorem integrable (hf : IsSTTest f) : Integrable f volume :=
  hf.continuous.integrable_of_hasCompactSupport hf.2

theorem memLp (hf : IsSTTest f) (p : ℝ≥0∞) : MemLp f p volume :=
  hf.continuous.memLp_of_hasCompactSupport hf.2

theorem differentiable (hf : IsSTTest f) : Differentiable ℝ f :=
  hf.1.differentiable (by simp)

theorem dirD (hf : IsSTTest f) (v : PS d) : IsSTTest (dirD v f) :=
  ⟨(hf.1.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const, hf.2.fderiv_apply ℝ v⟩

theorem sD2 (hf : IsSTTest f) (i j : Fin d) : IsSTTest (sD2 i j f) := (hf.dirD _).dirD _

theorem add (hf : IsSTTest f) (hg : IsSTTest g) : IsSTTest (f + g) :=
  ⟨hf.1.add hg.1, hf.2.add hg.2⟩

theorem smul (hf : IsSTTest f) (c : ℝ) : IsSTTest (c • f) :=
  ⟨hf.1.const_smul c, hf.2.smul_left⟩

theorem zero : IsSTTest (0 : PS d → ℝ) := ⟨contDiff_const, HasCompactSupport.zero⟩

theorem bounded (hf : IsSTTest f) : ∃ M : ℝ, 0 ≤ M ∧ ∀ X, |f X| ≤ M := by
  obtain ⟨M, hM⟩ := hf.continuous.bounded_above_of_compact_support hf.2
  exact ⟨max M 0, le_max_right _ _, fun X => (Real.norm_eq_abs _ ▸ hM X).trans (le_max_left _ _)⟩

/-- The support of a test lies in a time slab `|t| ≤ R`. -/
theorem timeBound (hf : IsSTTest f) : ∃ R : ℝ, 0 < R ∧ ∀ X : PS d, f X ≠ 0 → |X.1| ≤ R := by
  obtain ⟨R, hR⟩ := hf.2.isCompact.isBounded.subset_closedBall 0
  refine ⟨max R 1, by positivity, fun X hX => ?_⟩
  have hmem := hR (subset_tsupport f hX)
  rw [Metric.mem_closedBall, dist_zero_right] at hmem
  have : |X.1| ≤ ‖X‖ := by
    rw [← Real.norm_eq_abs]; exact norm_fst_le X
  linarith [le_max_left R 1]

/-- The spatial support of a test lies in a ball `|x| ≤ R`. -/
theorem spaceBound (hf : IsSTTest f) : ∃ R : ℝ, 0 < R ∧ ∀ X : PS d, f X ≠ 0 → ‖X.2‖ ≤ R := by
  obtain ⟨R, hR⟩ := hf.2.isCompact.isBounded.subset_closedBall 0
  refine ⟨max R 1, by positivity, fun X hX => ?_⟩
  have hmem := hR (subset_tsupport f hX)
  rw [Metric.mem_closedBall, dist_zero_right] at hmem
  have : ‖X.2‖ ≤ ‖X‖ := norm_snd_le X
  linarith [le_max_left R 1]

theorem slice_contDiff (hf : IsSTTest f) (t : ℝ) : ContDiff ℝ ∞ (fun x : Euc d => f (t, x)) :=
  hf.1.comp (contDiff_const.prodMk contDiff_id)

theorem slice_hasCompactSupport (hf : IsSTTest f) (t : ℝ) :
    HasCompactSupport (fun x : Euc d => f (t, x)) := by
  obtain ⟨R, -, hR⟩ := hf.spaceBound
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) R) fun x hx => ?_
  by_contra h
  exact hx (by simpa using hR (t, x) h)

end IsSTTest

/-- The derivative of a slice is the spatial derivative. -/
theorem fderiv_slice {f : PS d → ℝ} (hf : Differentiable ℝ f) (t : ℝ) (x v : Euc d) :
    fderiv ℝ (fun y : Euc d => f (t, y)) x v = dirD (0, v) f (t, x) := by
  have h1 : HasFDerivAt (fun y : Euc d => ((t, y) : PS d)) (ContinuousLinearMap.inr ℝ ℝ (Euc d)) x :=
    (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
  have h2 : HasFDerivAt (fun y : Euc d => f (t, y))
      ((fderiv ℝ f (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ (Euc d))) x :=
    (hf (t, x)).hasFDerivAt.comp x h1
  rw [h2.fderiv]
  rfl

theorem sD_slice {f : PS d → ℝ} (hf : Differentiable ℝ f) (i : Fin d) (t : ℝ) (x : Euc d) :
    sD i f (t, x) = fderiv ℝ (fun y : Euc d => f (t, y)) x (ev i) :=
  (fderiv_slice hf t x (ev i)).symm

/-- The second spatial derivative of a test is the second derivative of its slice. -/
theorem sD2_slice {f : PS d → ℝ} (hf : IsSTTest f) (i j : Fin d) (t : ℝ) (x : Euc d) :
    sD2 i j f (t, x) = fderiv ℝ (fun y : Euc d => fderiv ℝ (fun y' : Euc d => f (t, y')) y (ev j))
      x (ev i) := by
  have hj : (fun y : Euc d => fderiv ℝ (fun y' : Euc d => f (t, y')) y (ev j)) =
      fun y => sD j f (t, y) := by
    funext y; exact (sD_slice hf.differentiable j t y).symm
  rw [hj]
  exact sD_slice (hf.dirD _).differentiable i t x

end UnforcedLeray.Parabolic
