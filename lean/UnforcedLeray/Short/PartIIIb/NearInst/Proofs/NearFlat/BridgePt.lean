import UnforcedLeray.Short.PartIIIb.NearInst.Chart
import UnforcedLeray.Short.PartIIIa.ComposeCorollary
import UnforcedLeray.Short.PartIIIb.NearInst.Proofs.NearFlat.BridgeReal

/-!
# Pointwise planar dictionary for `nearD0Surj_of` (source 3560-3581, 2664-2701, 3866-3880)

Source of record: `the November 2 reference manuscript` (73 pages).

The flat maps act on the meridional block of a three-component cylindrical tensor
(source 3569-3571); the near multiplier is `M₀u = (v⊗u + u⊗v, 0)` (source 3566-3567, 3876-3877).
Pointwise facts relating the `3×3` chart tensors of `Z` (`Ten3`, Frobenius norm) to the planar
complex tensors of the flat equation (`merBlockC`, `tnorm2`):

* `nsSym_add`, `nsSym_sub`, `merBlockC_symm` : `nsSym` is additive and its planar block symmetric;
* `nsSym_ten3Of_symOuter` : the planar block of `a⊗h + h⊗a` is `a_i h_j + h_i a_j`;
* `tnorm2_merBlockC_le` : the planar block has Frobenius norm at most that of the tensor;
* `tnorm2_flatMult_velC` : `|v⊗h + h⊗v|` is the same in planar and in `3×3` form;
* `reTenC_flatMult`, `tnorm2_flatMult_reVecC_le` : `Re(M₀b) = M₀(Re b)` for the real train `v`;
* `transWeight_ge_one` : `W ≥ 1` for `m_Z ≥ 0` (source 3573-3575, "the first-component weight is
  at least one");
* `vnorm2_velC`, `tnorm2_smul`, `vnorm2_smul` : norms of real vectors and of scalar multiples.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Short.IIIa

/-! ## `nsSym` and the planar block -/

theorem nsSym_add (T T' : Ten3) (a b : Fin 3) :
    nsSym (T + T') a b = nsSym T a b + nsSym T' a b := by
  fin_cases a <;> fin_cases b <;> simp [nsSym, symRZ] <;> ring

theorem nsSym_sub (T T' : Ten3) (a b : Fin 3) :
    nsSym (T - T') a b = nsSym T a b - nsSym T' a b := by
  fin_cases a <;> fin_cases b <;> simp [nsSym, symRZ] <;> ring

theorem merBlockC_symm (T : Chart → Ten3) (p : Chart) (i j : Fin 2) :
    merBlockC T p i j = merBlockC T p j i := by
  fin_cases i <;> fin_cases j <;> simp [merBlockC, nsSym, merIdx]

/-- The planar block of `a⊗h + h⊗a` is `a_i h_j + h_i a_j`. -/
theorem nsSym_ten3Of_symOuter (a h : Merid) (i j : Fin 2) :
    nsSym (ten3Of (symOuter a h)) (merIdx i) (merIdx j) = a i * h j + h i * a j := by
  fin_cases i <;> fin_cases j <;>
    simp [nsSym, ten3Of, symOuter, embedMerid, merIdx, symRZ] <;> ring

/-- The entries of `nsSym T` are continuous in `T`. -/
theorem continuous_nsSym_apply (a b : Fin 3) : Continuous fun T : Ten3 => nsSym T a b := by
  have h : ∀ x : Fin 3 × Fin 3, Continuous fun T : Ten3 => T x := fun x =>
    PiLp.continuous_apply 2 (fun _ => ℝ) x
  fin_cases a <;> fin_cases b <;> simp [nsSym, symRZ] <;>
    first
    | exact continuous_const
    | exact h _
    | exact ((h _).add (h _)).div_const _

theorem measurable_merBlockC {T : Chart → Ten3} (hT : Measurable T) (i j : Fin 2) :
    Measurable fun p => merBlockC T p i j :=
  ((continuous_nsSym_apply (merIdx i) (merIdx j)).measurable.comp hT).complex_ofReal

/-- The planar block has Frobenius norm at most the Frobenius norm of the `3×3` tensor
(`2((T_rz+T_zr)/2)² ≤ T_rz² + T_zr²`). -/
theorem tnorm2_merBlockC_le (T : Chart → Ten3) (p : Chart) : tnorm2 (merBlockC T p) ≤ ‖T p‖ := by
  rw [← Real.sqrt_sq (norm_nonneg (T p))]
  unfold tnorm2
  apply Real.sqrt_le_sqrt
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
  simp only [merBlockC, Complex.norm_real, Real.norm_eq_abs, sq_abs, Fin.sum_univ_two,
    Fin.sum_univ_three]
  simp [nsSym, merIdx, symRZ]
  nlinarith [sq_nonneg (T p (0, 2) - T p (2, 0)), sq_nonneg (T p (0, 1)), sq_nonneg (T p (1, 0)),
    sq_nonneg (T p (1, 1)), sq_nonneg (T p (1, 2)), sq_nonneg (T p (2, 1))]

/-! ## The flat multiplier -/

theorem trainMer_apply {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (p : Chart) (i : Fin 2) :
    trainMer tr p i = trainVel tr p.1 p.2 i := by
  simp [trainMer]

/-- `|v⊗h + h⊗v|` in planar complex form equals the Frobenius norm of the `3×3` tensor
`ten3Of (symOuter v h)` (the hoop row and column vanish). -/
theorem tnorm2_flatMult_velC {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    (h : Chart → Merid) (p : Chart) :
    tnorm2 (flatMult tr (velC h) p) = ‖ten3Of (symOuter (trainMer tr p) (h p))‖ := by
  rw [← Real.sqrt_sq (norm_nonneg (ten3Of (symOuter (trainMer tr p) (h p))))]
  unfold tnorm2
  congr 1
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
  have e : ∀ i j : Fin 2, flatMult tr (velC h) p i j =
      (((trainMer tr p i * h p j + h p i * trainMer tr p j : ℝ)) : ℂ) := by
    intro i j
    simp only [flatMult, velC, trainMer_apply]
    push_cast
    ring
  simp only [e, Complex.norm_real, Real.norm_eq_abs, sq_abs, Fin.sum_univ_two, Fin.sum_univ_three]
  simp [ten3Of, symOuter, embedMerid]

/-- `Re(v⊗b + b⊗v) = v⊗Re b + Re b⊗v` for the real train `v`. -/
theorem reTenC_flatMult {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) : reTenC (flatMult tr b) = flatMult tr (reVecC b) := by
  funext p i j
  simp only [reTenC, reVecC, flatMult, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, mul_zero]
  push_cast
  ring

theorem tnorm2_flatMult_reVecC_le {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (p : ℝ × (ℝ × ℝ)) :
    tnorm2 (flatMult tr (reVecC b) p) ≤ tnorm2 (flatMult tr b p) := by
  rw [← reTenC_flatMult]
  exact tnorm2_reTenC_le _ p

/-! ## Weights and scalar multiples -/

/-- `W = ⟨η/√(1+s)⟩^{m_Z} ≥ 1` for `m_Z ≥ 0` (source 3573-3575). -/
theorem transWeight_ge_one {mZ : ℝ} (hmZ : 0 ≤ mZ) (p : ℝ × (ℝ × ℝ)) : 1 ≤ transWeight mZ p := by
  unfold transWeight
  exact Real.one_le_rpow (by nlinarith [sq_nonneg (p.2.2 / Real.sqrt (1 + p.1))]) (by positivity)

theorem vnorm2_velC (h : Chart → Merid) (p : Chart) : vnorm2 (velC h p) = ‖h p‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold vnorm2 velC
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.norm_real]

theorem tnorm2_smul (r : ℝ) (T : Fin 2 → Fin 2 → ℂ) : tnorm2 (r • T) = |r| * tnorm2 T := by
  unfold tnorm2
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg r)]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, Complex.real_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, sq_abs]

theorem vnorm2_smul (r : ℝ) (a : Fin 2 → ℂ) : vnorm2 (r • a) = |r| * vnorm2 a := by
  unfold vnorm2
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg r)]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, Complex.real_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, sq_abs]

end UnforcedLeray.Short.PartIIIb.NearInst
