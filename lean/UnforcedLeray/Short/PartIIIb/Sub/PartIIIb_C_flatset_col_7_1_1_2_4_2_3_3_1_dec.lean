import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_3_of
import UnforcedLeray.Lib.TrainB.P0SmoothH3
import Mathlib.Analysis.Calculus.ContDiff.WithLp

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (P0C P0re P0im toL2v reVec imVec cplxOf vnorm2)

/-- **Sub1: all-order regularity of `P₀` of a smooth periodic field** (source 1650-1656, 1676,
1684-1689: `P₀` is an order-zero Fourier multiplier in `(q, η)` commuting with `∂_q, ∂_η`).
For `u` smooth, `c`-periodic, vanishing for `|η|` large, and every `k`, the class `P₀ u ∈ L²(cell)`
is the value component of an element of the unweighted `H^k(cell; ℝ²)`.  Route: generalise
`TrainB.exists_projectedSmoothVecH3` (`Lib/TrainB/P0SmoothH3.lean`, only `k = 3`) to arbitrary `k`,
i.e. a `k`-indexed `vecH3CellDerivCLM` / `projectedSmoothWord`, using `IIIa.p0CommWeakC`
(iterated weak-derivative commutation of `P₀`). -/
def P0SmoothRegK : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ u : UnforcedLeray.Cyl.Plane → UnforcedLeray.Cyl.Vec2,
    UnforcedLeray.Sob.IsCylSmooth c u → ∀ k : ℕ,
    ∃ y : UnforcedLeray.Cyl.H ℝ UnforcedLeray.Cyl.Vec2 c 0 k,
      ((UnforcedLeray.Sob.W.value _ _ _ _ _ _ y : UnforcedLeray.Cyl.Plane → UnforcedLeray.Cyl.Vec2)) =ᵐ[UnforcedLeray.Cyl.cellμ c]
      (UnforcedLeray.Cyl.P0 c (toL2v c u) : UnforcedLeray.Cyl.Plane → UnforcedLeray.Cyl.Vec2)

/-- **Sub2: cylinder Sobolev embedding** (`H^k(cell) ⊂ C^m` in dimension 2, `k = m + 2` suffices;
the cell `[-c/2, c/2) × ℝ` is a periodic strip, so apply the Euclidean Sobolev/Morrey embedding on
unit squares, with uniform constants by `q`-periodicity and translation in `η`; source 1684-1689 uses
only that `P₀ φ ∈ H^k` for all `k` gives a `C^∞` function).  For every `m` there are `k` and `C`
such that every `y ∈ H^k(cell; ℝ²)` (unweighted, `m = 0`) has a `C^m`, `c`-periodic representative
`z` of its value component with `sup ‖z‖ ≤ C ‖y‖`. -/
def CylEmbedK : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ m : ℕ, ∃ (k : ℕ) (C : ℝ), ∀ y : UnforcedLeray.Cyl.H ℝ UnforcedLeray.Cyl.Vec2 c 0 k,
    ∃ z : UnforcedLeray.Cyl.Plane → UnforcedLeray.Cyl.Vec2, ContDiff ℝ m z ∧
      (∀ x : ℝ × ℝ, z (x.1 + c, x.2) = z x) ∧ (∀ x, ‖z x‖ ≤ C * ‖y‖) ∧
      z =ᵐ[UnforcedLeray.Cyl.cellμ c]
        ((UnforcedLeray.Sob.W.value _ _ _ _ _ _ y : UnforcedLeray.Cyl.Plane → UnforcedLeray.Cyl.Vec2))

/-- **Sub3: uniqueness of continuous periodic representatives.**  Two continuous `c`-periodic (in
`q`) fields that agree a.e. on the cell agree everywhere (every point is a limit of Lebesgue-points
of the set of agreement: the set `{z₁ = z₂}` is closed, `q`-periodic, and of full measure in the cell,
hence dense in the plane; or the ball-averaging argument of `contRepMeasurable`). -/
def PeriodicContUnique : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ z₁ z₂ : UnforcedLeray.Cyl.Plane → UnforcedLeray.Cyl.Vec2,
    Continuous z₁ → Continuous z₂ → (∀ x : ℝ × ℝ, z₁ (x.1 + c, x.2) = z₁ x) →
    (∀ x : ℝ × ℝ, z₂ (x.1 + c, x.2) = z₂ x) →
    z₁ =ᵐ[UnforcedLeray.Cyl.cellμ c] z₂ → z₁ = z₂

theorem p0SliceSmooth_of (h1 : P0SmoothRegK) (h2 : CylEmbedK) (h3 : PeriodicContUnique) :
    P0SliceSmooth := by
  intro c hc φ hφs hφp ⟨L, hL⟩
  set u : UnforcedLeray.Cyl.Plane → UnforcedLeray.Cyl.Vec2 :=
    fun y => UnforcedLeray.Cyl.vec (φ y 0) (φ y 1) with hu_def
  have hu : UnforcedLeray.Sob.IsCylSmooth c u := by
    refine ⟨?_, ?_, ?_⟩
    · refine (contDiff_piLp 2).mpr fun i => ?_
      fin_cases i
      · exact hφs 0
      · exact hφs 1
    · intro z
      have := hφp z.1 z.2
      simp only [hu_def, Prod.mk_add_mk, add_zero]
      rw [show (z.1 + c, z.2) = z + (c, 0) by ext <;> simp] at this
      simp [this]
    · refine ⟨L, fun z hz => ?_⟩
      have h0 : φ z = 0 := by
        by_contra hne
        exact absurd (hL z hne) (not_le.mpr hz)
      simp [hu_def, h0]
  set g : UnforcedLeray.Cyl.Plane → UnforcedLeray.Cyl.Vec2 :=
    ((UnforcedLeray.Cyl.P0 c (toL2v c u) : UnforcedLeray.Cyl.L2v c) :
      UnforcedLeray.Cyl.Plane → UnforcedLeray.Cyl.Vec2) with hg_def
  have key : ∀ m : ℕ, ∃ (C : ℝ) (z : UnforcedLeray.Cyl.Plane → UnforcedLeray.Cyl.Vec2),
      ContDiff ℝ m z ∧ (∀ x : ℝ × ℝ, z (x.1 + c, x.2) = z x) ∧ (∃ C' : ℝ, ∀ x, ‖z x‖ ≤ C') ∧
      z =ᵐ[UnforcedLeray.Cyl.cellμ c] g := by
    intro m
    obtain ⟨k, C, hk⟩ := h2 c hc m
    obtain ⟨y, hy⟩ := h1 c hc u hu k
    obtain ⟨z, hz1, hz2, hz3, hz4⟩ := hk y
    exact ⟨C, z, hz1, hz2, ⟨C * ‖y‖, hz3⟩, hz4.trans hy⟩
  obtain ⟨_, z0, hz0d, hz0p, hz0b, hz0a⟩ := key 0
  have hz0c : Continuous z0 := hz0d.continuous
  have hz0inf : ContDiff ℝ ∞ z0 := by
    rw [contDiff_infty]
    intro m
    obtain ⟨_, zm, hzmd, hzmp, _, hzma⟩ := key m
    have : zm = z0 := h3 c hc zm z0 hzmd.continuous hz0c hzmp hz0p (hzma.trans hz0a.symm)
    rw [← this]; exact hzmd
  obtain ⟨C0, hC0⟩ := hz0b
  refine ⟨fun y i => ((z0 y i : ℝ) : ℂ), fun i => ?_, fun q η => ?_, ⟨C0, fun y => ?_⟩, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp ((contDiff_piLp 2).mp hz0inf i)
  · funext i
    simp only
    rw [hz0p (q, η)]
  · have : vnorm2 (fun i => ((z0 y i : ℝ) : ℂ)) = ‖z0 y‖ := by
      simp [vnorm2, EuclideanSpace.norm_eq]
    rw [this]; exact hC0 y
  · have hre : reVec (fun y i => ((φ y i : ℝ) : ℂ)) = u := by
      funext x; simp [reVec, hu_def]
    have him : imVec (fun y i => ((φ y i : ℝ) : ℂ)) = imVec (fun _ _ => (0 : ℂ)) := by
      funext x; ext i; fin_cases i <;> simp [imVec, UnforcedLeray.Cyl.vec]
    have hP0im : P0im c (fun y i => ((φ y i : ℝ) : ℂ)) = 0 := by
      simp only [P0im, him, toL2v_imVec_zero, map_zero]
    have hP0re : P0re c (fun y i => ((φ y i : ℝ) : ℂ)) = UnforcedLeray.Cyl.P0 c (toL2v c u) := by
      simp only [P0re, hre]
    have hzero : ((0 : UnforcedLeray.Cyl.L2v c) : UnforcedLeray.Cyl.Plane →
        UnforcedLeray.Cyl.Vec2) =ᵐ[UnforcedLeray.Cyl.cellμ c] 0 := Lp.coeFn_zero _ _ _
    filter_upwards [hz0a, hzero] with x hx hx0
    funext i
    simp only [P0C, cplxOf, hP0im, hP0re]
    have e1 : (UnforcedLeray.Cyl.P0 c (toL2v c u) : UnforcedLeray.Cyl.L2v c) x i = z0 x i := by
      have := congrArg (fun v => v i) hx
      simpa [hg_def] using this.symm
    have e2 : ((0 : UnforcedLeray.Cyl.L2v c) : UnforcedLeray.Cyl.Plane →
        UnforcedLeray.Cyl.Vec2) x i = 0 := by
      have := congrArg (fun v => v i) hx0
      simpa using this
    rw [e1, e2]
    simp

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
