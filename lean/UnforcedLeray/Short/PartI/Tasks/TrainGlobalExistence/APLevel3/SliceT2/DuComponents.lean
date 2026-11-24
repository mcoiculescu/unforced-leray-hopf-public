import UnforcedLeray.Short.PartI.Sub.PartI_T04_10_2_2_2

/-!
# Part I, `PartI:T04/10/2/2/2/1`: `SliceDuComponents`

Source of record: `the November 2 reference manuscript`, lines 285-288.
The four entries of `Du` are `f_a z = (D u z e_k)_i` with `a ↔ (k, i)`, `k ∈ {1,2}`, `i ∈ {0,1}`.
Constants: `C₀ = 1` (operator norm bounded by the sum of the entries) and
`C₁ = ∑_a ‖Λ_a‖` (the jets of `f_a` are jets of `Du` composed with the CLM `Λ_a`).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

/-- Direction `e_k` attached to the component index `a : Fin 4`. -/
def sdcDir : Fin 4 → Plane := ![(1, 0), (1, 0), (0, 1), (0, 1)]

/-- Coordinate index `i` attached to the component index `a : Fin 4`. -/
def sdcIdx : Fin 4 → Fin 2 := ![0, 1, 0, 1]

/-- The CLM `L ↦ (L e_k)_i` on `Plane →L[ℝ] Vec`. -/
def sdcLam (a : Fin 4) : (Plane →L[ℝ] Vec) →L[ℝ] ℝ :=
  (EuclideanSpace.proj (sdcIdx a)).comp ((ContinuousLinearMap.apply ℝ Vec) (sdcDir a))

lemma sdcLam_apply (a : Fin 4) (L : Plane →L[ℝ] Vec) :
    sdcLam a L = L (sdcDir a) (sdcIdx a) := rfl

/-- Euclidean norm on `Vec` is bounded by the sum of the absolute coordinates. -/
lemma sdc_vec_norm_le (v : Vec) : ‖v‖ ≤ |v 0| + |v 1| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs]
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [abs_nonneg (v 0), abs_nonneg (v 1), sq_abs (v 0), sq_abs (v 1), mul_nonneg (abs_nonneg (v 0)) (abs_nonneg (v 1))]

/-- The four coordinates of `L x`. -/
lemma sdc_coord (L : Plane →L[ℝ] Vec) (x : Plane) (i : Fin 2) :
    L x i = x.1 * L (1, 0) i + x.2 * L (0, 1) i := by
  have hx : x = x.1 • ((1 : ℝ), (0 : ℝ)) + x.2 • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  conv_lhs => rw [hx]
  rw [map_add, map_smul, map_smul]
  simp [smul_eq_mul]

/-- Operator norm on `Plane →L[ℝ] Vec` bounded by the sum of the four component functionals. -/
lemma sdc_opNorm_le (L : Plane →L[ℝ] Vec) : ‖L‖ ≤ ∑ a, |sdcLam a L| := by
  rw [Fin.sum_univ_four]
  have e0 : sdcLam 0 L = L (1, 0) 0 := rfl
  have e1 : sdcLam 1 L = L (1, 0) 1 := rfl
  have e2 : sdcLam 2 L = L (0, 1) 0 := rfl
  have e3 : sdcLam 3 L = L (0, 1) 1 := rfl
  rw [e0, e1, e2, e3]
  set A0 := L (1, 0) 0
  set A1 := L (1, 0) 1
  set A2 := L (0, 1) 0
  set A3 := L (0, 1) 1
  have hsum : 0 ≤ |A0| + |A1| + |A2| + |A3| := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ hsum ?_
  intro x
  have hx1 : |x.1| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using norm_fst_le x
  have hx2 : |x.2| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using norm_snd_le x
  have hn : 0 ≤ ‖x‖ := norm_nonneg x
  have c0 : |L x 0| ≤ ‖x‖ * (|A0| + |A2|) := by
    rw [sdc_coord L x 0]
    calc |x.1 * A0 + x.2 * A2| ≤ |x.1 * A0| + |x.2 * A2| := abs_add_le _ _
      _ = |x.1| * |A0| + |x.2| * |A2| := by rw [abs_mul, abs_mul]
      _ ≤ ‖x‖ * |A0| + ‖x‖ * |A2| := by gcongr
      _ = ‖x‖ * (|A0| + |A2|) := by ring
  have c1 : |L x 1| ≤ ‖x‖ * (|A1| + |A3|) := by
    rw [sdc_coord L x 1]
    calc |x.1 * A1 + x.2 * A3| ≤ |x.1 * A1| + |x.2 * A3| := abs_add_le _ _
      _ = |x.1| * |A1| + |x.2| * |A3| := by rw [abs_mul, abs_mul]
      _ ≤ ‖x‖ * |A1| + ‖x‖ * |A3| := by gcongr
      _ = ‖x‖ * (|A1| + |A3|) := by ring
  have hv := sdc_vec_norm_le (L x)
  have : (|A0| + |A1| + |A2| + |A3|) * ‖x‖ = ‖x‖ * (|A0| + |A2|) + ‖x‖ * (|A1| + |A3|) := by ring
  linarith

theorem sliceDuComponents : SliceDuComponents := by
  -- constants
  have hC1 : (0 : ℝ) ≤ ∑ a, ‖sdcLam a‖ := Finset.sum_nonneg fun a _ => by positivity
  refine ⟨1, ∑ a, ‖sdcLam a‖, zero_le_one, hC1, ?_⟩
  intro c u hc hu
  obtain ⟨hC, hper, -, -, -⟩ := hu
  -- smoothness of the derivative
  have hD : ContDiff ℝ ∞ (fderiv ℝ u) := (contDiff_infty_iff_fderiv.1 hC).2
  -- periodicity of the derivative
  have hfderivPer : ∀ z : Plane, fderiv ℝ u (z.1 + c, z.2) = fderiv ℝ u z := by
    intro z
    have hfun : (fun w : Plane => u (w + ((c : ℝ), (0 : ℝ)))) = u := by
      funext w
      rw [← hper w]
      congr 1
      ext <;> simp
    have key := fderiv_comp_add_right (𝕜 := ℝ) (f := u) (((c : ℝ), (0 : ℝ))) (x := z)
    rw [hfun] at key
    have hz : (z.1 + c, z.2) = z + ((c : ℝ), (0 : ℝ)) := by ext <;> simp
    rw [hz]
    exact key.symm
  refine ⟨fun a z => sdcLam a (fderiv ℝ u z), ?_, ?_, ?_, ?_⟩
  · intro a
    exact (sdcLam a).contDiff.comp hD
  · intro a z
    show sdcLam a (fderiv ℝ u (z.1 + c, z.2)) = sdcLam a (fderiv ℝ u z)
    rw [hfderivPer z]
  · intro z
    rw [norm_iteratedFDeriv_one, one_mul]
    exact sdc_opNorm_le _
  · intro a j z
    have hdiff : ContDiffAt ℝ ∞ (fderiv ℝ u) z := hD.contDiffAt
    have h1 := (sdcLam a).norm_iteratedFDeriv_comp_left (f := fderiv ℝ u) (x := z) hdiff
      (n := j) (by exact_mod_cast le_top)
    rw [norm_iteratedFDeriv_fderiv] at h1
    have hle : ‖sdcLam a‖ ≤ ∑ b, ‖sdcLam b‖ :=
      Finset.single_le_sum (f := fun b => ‖sdcLam b‖) (fun b _ => by positivity) (Finset.mem_univ a)
    calc ‖iteratedFDeriv ℝ j (fun z => sdcLam a (fderiv ℝ u z)) z‖
        ≤ ‖sdcLam a‖ * ‖iteratedFDeriv ℝ (j + 1) u z‖ := h1
      _ ≤ (∑ b, ‖sdcLam b‖) * ‖iteratedFDeriv ℝ (j + 1) u z‖ :=
          mul_le_mul_of_nonneg_right hle (norm_nonneg _)

end UnforcedLeray.Short.PartI
