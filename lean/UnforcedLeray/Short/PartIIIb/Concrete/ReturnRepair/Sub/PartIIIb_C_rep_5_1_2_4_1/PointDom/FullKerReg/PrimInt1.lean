import UnforcedLeray.Statement
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The outward primitive of a `C²` function: integrand and its derivative bounds

`primF A w q u = (q₀ + u) A(q + u e₀ - w)`, `primInt A w q = ∫_{u>0} primF A w q u du`; for
`q = (r, 0, y₃)` this is `∫_{ρ>r} ρ A((ρ,0,y₃) - w) dρ` (the primitive of source 4178-4179).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray

/-- The first basis vector. -/
def primE0 : Space := EuclideanSpace.single 0 1

/-- The integrand: `(q₀ + u) A(q + u e₀ - w)`. -/
def primF (A : Space → ℝ) (w q : Space) (u : ℝ) : ℝ := (q 0 + u) * A (q + (u • primE0 - w))

/-- The primitive `∫_{u>0} (q₀+u) A(q + u e₀ - w) du`. -/
def primInt (A : Space → ℝ) (w q : Space) : ℝ := ∫ u in Ioi (0 : ℝ), primF A w q u

theorem primE0_apply0 : (primE0 : Space) 0 = 1 := by simp [primE0]
theorem primE0_apply1 : (primE0 : Space) 1 = 0 := by simp [primE0]
theorem primE0_apply2 : (primE0 : Space) 2 = 0 := by simp [primE0]

theorem prim_shift_sq (q w : Space) (u : ℝ) :
    ‖q + (u • primE0 - w)‖ ^ 2 = (q 0 + u - w 0) ^ 2 + (q 1 - w 1) ^ 2 + (q 2 - w 2) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp [primE0_apply0, primE0_apply1, primE0_apply2, Real.norm_eq_abs, sq_abs]
  ring

/-- The lower bound `‖x‖² ≥ v² + b²` with `v = q₀ + u - ρ₀`, `w₀ ≤ ρ₀ ≤ q₀ + u`. -/
theorem prim_shift_lower (q w : Space) (u ρ₀ : ℝ) (hw : w 0 ≤ ρ₀) (hq : ρ₀ ≤ q 0 + u) :
    (q 0 + u - ρ₀) ^ 2 + (q 2 - w 2) ^ 2 ≤ ‖q + (u • primE0 - w)‖ ^ 2 := by
  rw [prim_shift_sq]
  have h1 : q 0 + u - ρ₀ ≤ q 0 + u - w 0 := by linarith
  have h2 : (q 0 + u - ρ₀) ^ 2 ≤ (q 0 + u - w 0) ^ 2 :=
    pow_le_pow_left₀ (by linarith) h1 2
  nlinarith [sq_nonneg (q 1 - w 1)]

theorem primF_contDiff {A : Space → ℝ} (hA : ContDiff ℝ 2 A) (w : Space) :
    ContDiff ℝ 2 (fun p : Space × ℝ => primF A w p.1 p.2) := by
  unfold primF
  have hc : ContDiff ℝ 2 (fun p : Space × ℝ => p.1 0) :=
    ((EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).contDiff).comp contDiff_fst
  refine (hc.add contDiff_snd).mul (hA.comp ?_)
  exact contDiff_fst.add ((contDiff_snd.smul contDiff_const).sub contDiff_const)

theorem primF_contDiff_q {A : Space → ℝ} (hA : ContDiff ℝ 2 A) (w : Space) (u : ℝ) :
    ContDiff ℝ 2 (fun q : Space => primF A w q u) :=
  (primF_contDiff hA w).comp (contDiff_id.prodMk contDiff_const)

/-- Derivative bounds of the integrand in terms of those of `A` at `x = q + u e₀ - w`. -/
theorem primF_iter_bound {A : Space → ℝ} (hA : ContDiff ℝ 2 A) (w q : Space) (u : ℝ) :
    ‖iteratedFDeriv ℝ 0 (fun q' => primF A w q' u) q‖ ≤
        |q 0 + u| * |A (q + (u • primE0 - w))| ∧
    ‖iteratedFDeriv ℝ 1 (fun q' => primF A w q' u) q‖ ≤
        |A (q + (u • primE0 - w))| +
          |q 0 + u| * ‖iteratedFDeriv ℝ 1 A (q + (u • primE0 - w))‖ ∧
    ‖iteratedFDeriv ℝ 2 (fun q' => primF A w q' u) q‖ ≤
        2 * ‖iteratedFDeriv ℝ 1 A (q + (u • primE0 - w))‖ +
          |q 0 + u| * ‖iteratedFDeriv ℝ 2 A (q + (u • primE0 - w))‖ := by
  set c : Space := u • primE0 - w with hc
  have hf : ContDiff ℝ 2 (fun q' : Space => q' 0 + u) :=
    (((EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).contDiff).add contDiff_const)
  have hg : ContDiff ℝ 2 (fun q' : Space => A (q' + c)) := hA.comp (contDiff_id.add contDiff_const)
  have hgd : ∀ n : ℕ, ‖iteratedFDeriv ℝ n (fun q' : Space => A (q' + c)) q‖ =
      ‖iteratedFDeriv ℝ n A (q + c)‖ := fun n => by rw [iteratedFDeriv_comp_add_right]
  have hfd : ∀ q' : Space, fderiv ℝ (fun q'' : Space => q'' 0 + u) q' =
      (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ) := by
    intro q'
    have := ((EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt (x := q')).add_const u
    exact this.fderiv
  have hf0 : ‖iteratedFDeriv ℝ 0 (fun q' : Space => q' 0 + u) q‖ = |q 0 + u| := by
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
  have hproj : ‖(EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
      simpa using PiLp.norm_apply_le x 0)
  have hf1 : ‖iteratedFDeriv ℝ 1 (fun q' : Space => q' 0 + u) q‖ ≤ 1 := by
    rw [norm_iteratedFDeriv_one, hfd]
    exact hproj
  have hf2 : ‖iteratedFDeriv ℝ 2 (fun q' : Space => q' 0 + u) q‖ = 0 := by
    have := (norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := fun q' : Space => q' 0 + u) (x := q) (n := 1))
    rw [← this]
    have e : fderiv ℝ (fun q'' : Space => q'' 0 + u) = fun _ => (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ) :=
      funext hfd
    rw [e, iteratedFDeriv_const_of_ne (by norm_num)]
    simp
  have hn1 := hgd 1
  have hn2 := hgd 2
  have hn0 : ‖iteratedFDeriv ℝ 0 (fun q' : Space => A (q' + c)) q‖ = |A (q + c)| := by
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
  refine ⟨?_, ?_, ?_⟩
  · have := norm_iteratedFDeriv_mul_le hf hg q (n := 0) (N := 2) (by norm_num)
    rw [Finset.sum_range_one] at this
    show ‖iteratedFDeriv ℝ 0 (fun q' => (q' 0 + u) * A (q' + c)) q‖ ≤ _
    refine this.trans (le_of_eq ?_)
    rw [show (0:ℕ) - 0 = 0 from rfl, hf0, hn0]
    simp
  · have := norm_iteratedFDeriv_mul_le hf hg q (n := 1) (N := 2) (by norm_num)
    rw [Finset.sum_range_succ, Finset.sum_range_one] at this
    show ‖iteratedFDeriv ℝ 1 (fun q' => (q' 0 + u) * A (q' + c)) q‖ ≤ _
    refine this.trans ?_
    rw [show (1:ℕ) - 0 = 1 from rfl, show (1:ℕ) - 1 = 0 from rfl, hf0, hn1, hn0]
    have c0 : ((Nat.choose 1 0 : ℕ) : ℝ) = 1 := by norm_num
    have c1 : ((Nat.choose 1 1 : ℕ) : ℝ) = 1 := by norm_num
    rw [c0, c1]
    have := mul_le_mul_of_nonneg_right hf1 (abs_nonneg (A (q + c)))
    nlinarith [norm_nonneg (iteratedFDeriv ℝ 1 A (q + c)), abs_nonneg (q 0 + u)]
  · have := norm_iteratedFDeriv_mul_le hf hg q (n := 2) (N := 2) (by norm_num)
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one] at this
    show ‖iteratedFDeriv ℝ 2 (fun q' => (q' 0 + u) * A (q' + c)) q‖ ≤ _
    refine this.trans ?_
    rw [show (2:ℕ) - 0 = 2 from rfl, show (2:ℕ) - 1 = 1 from rfl, show (2:ℕ) - 2 = 0 from rfl,
      hf0, hn2, hn1, hn0, hf2]
    have c0 : ((Nat.choose 2 0 : ℕ) : ℝ) = 1 := by norm_num
    have c1 : ((Nat.choose 2 1 : ℕ) : ℝ) = 2 := by norm_num
    have c2 : ((Nat.choose 2 2 : ℕ) : ℝ) = 1 := by norm_num
    rw [c0, c1, c2]
    have h3 := mul_le_mul_of_nonneg_right hf1 (norm_nonneg (iteratedFDeriv ℝ 1 A (q + c)))
    nlinarith [norm_nonneg (iteratedFDeriv ℝ 1 A (q + c)), abs_nonneg (q 0 + u)]

end UnforcedLeray.Short.PartIIIb.Concrete

end
