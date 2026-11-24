import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.NewtonV.Geom
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_9_4

/-!
# Vector-valued shift bound and the contraction operator (helper of `Ambient/NewtonV.lean`)

Source 4776-4782, 4870-4900.  `D3t z = (∂_i∂_j∂_k N(z))_{ijk}` as a `T3`-valued map; `Lmat S`
is the continuous linear contraction `T ↦ (∑_{jk} T_{ijk} S_{jk})_i`, `‖Lmat S‖ ≤ 9 |S|_F`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace NewtonVGeom

abbrev T3 := Fin 3 × Fin 3 × Fin 3 → ℝ

/-- The triple of third derivatives of `N`, as a `T3`-valued map. -/
def D3t (z : Vec3) : T3 := fun p => newtonD3 z p.1 p.2.1 p.2.2

/-- The contraction with a matrix, as a continuous linear map. -/
def Lmat (S : Mat3) : T3 →L[ℝ] Vec3 :=
  ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
    S j k • ((ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℝ) i).comp
      (ContinuousLinearMap.proj ((i, j, k) : Fin 3 × Fin 3 × Fin 3)))

theorem Lmat_apply (S : Mat3) (T : T3) (i : Fin 3) :
    Lmat S T i = ∑ j, ∑ k, S j k * T (i, j, k) := by
  simp [Lmat, Finset.sum_apply, Pi.single_apply]

theorem Lmat_zero : Lmat 0 = 0 := by
  ext T i
  simp [Lmat_apply]

theorem continuous_Lmat : Continuous Lmat := by
  unfold Lmat
  fun_prop

theorem abs_le_frob (S : Mat3) (j k : Fin 3) : |S j k| ≤ frob S := by
  have h := norm_le_frob S
  have h1 : ‖S j k‖ ≤ ‖S‖ := (norm_le_pi_norm (S j) k).trans (norm_le_pi_norm S j)
  rw [Real.norm_eq_abs] at h1
  linarith

theorem norm_Lmat (S : Mat3) : ‖Lmat S‖ ≤ 9 * frob S := by
  have hf := frob_nonneg' S
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun T => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [Real.norm_eq_abs, Lmat_apply]
  calc |∑ j, ∑ k, S j k * T (i, j, k)|
      ≤ ∑ j, |∑ k, S j k * T (i, j, k)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin 3, ∑ k : Fin 3, |S j k * T (i, j, k)| :=
        Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin 3, ∑ k : Fin 3, frob S * ‖T‖ := by
        refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul]
        have h1 := abs_le_frob S j k
        have h2 : |T (i, j, k)| ≤ ‖T‖ := by
          rw [← Real.norm_eq_abs]; exact norm_le_pi_norm T (i, j, k)
        exact mul_le_mul h1 h2 (abs_nonneg _) hf
    _ = 9 * frob S * ‖T‖ := by simp; ring

/-- A multilinear map into a finite product has norm bounded by the bounds of its components. -/
theorem norm_cmm_le_of_comp {n : ℕ} {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] (g : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) (ι → ℝ)) {B : ℝ}
    (hB : 0 ≤ B)
    (h : ∀ i, ‖(ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).compContinuousMultilinearMap g‖ ≤ B) :
    ‖g‖ ≤ B := by
  refine g.opNorm_le_bound hB fun m => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  have h1 := ((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).compContinuousMultilinearMap g).le_opNorm m
  have h2 := mul_le_mul_of_nonneg_right (h i) (Finset.prod_nonneg (s := Finset.univ) fun j _ => norm_nonneg (m j))
  simpa using h1.trans h2

theorem D3t_contDiffAt {z : Vec3} (hz : z ≠ 0) : ContDiffAt ℝ NewtonD3.ii D3t z :=
  contDiffAt_pi.2 fun p =>
    (NewtonD3.newtonD3_contDiffOn p.1 p.2.1 p.2.2).contDiffAt
      (NewtonD3.isOpen_punct.mem_nhds (by simpa [NewtonD3.punct] using hz))

theorem shift_ne_zero {ν t : ℝ} {w : Vec3} {x' : ℝ × ℝ} (hν : 0 < ν) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hw : ν * (11 / 12) < eucSq w) (hx : x'.1 ^ 2 + x'.2 ^ 2 ≤ 5 * ν / 6) :
    w - t • embPlane x' ≠ 0 := by
  intro h
  have ha : 0 < 1 - Real.sqrt (10 / 11) := by linarith [sqrt_one_tenth_elevenths_lt]
  have hX : 0 < Real.sqrt (eucSq w) := Real.sqrt_pos.2 (by linarith)
  have hlow := shift_lower ht0 ht1 hw hx
  have h0 : eucSq (0 : Vec3) = 0 := by simp [eucSq]
  rw [h, h0, Real.sqrt_zero] at hlow
  linarith [mul_pos ha hX]

/-- Operator-norm shift bound for the vector of third derivatives. -/
theorem D3t_shift_bound (m : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (ν t : ℝ) (w : Vec3) (x' : ℝ × ℝ),
    0 < ν → 0 ≤ t → t ≤ 1 → ν * (11 / 12) < eucSq w → x'.1 ^ 2 + x'.2 ^ 2 ≤ 5 * ν / 6 →
    ‖iteratedFDeriv ℝ m (fun x => D3t (x - t • embPlane x')) w‖ ≤
      K * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m) := by
  obtain ⟨K, hK⟩ := newtonD3_shift_bound m
  refine ⟨|K|, abs_nonneg K, ?_⟩
  intro ν t w x' hν ht0 ht1 hw hx
  have hz := shift_ne_zero hν ht0 ht1 hw hx
  have hwpos : 0 < eucSq w := by linarith
  have hp : 0 ≤ (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m) :=
    Real.rpow_nonneg (Real.sqrt_nonneg _) _
  refine norm_cmm_le_of_comp _ (mul_nonneg (abs_nonneg K) hp) fun p => ?_
  have hcd : ContDiffAt ℝ NewtonD3.ii (fun x => D3t (x - t • embPlane x')) w :=
    (D3t_contDiffAt hz).comp w (contDiffAt_id.sub contDiffAt_const)
  have hc := ContinuousLinearMap.iteratedFDeriv_comp_left
    (ContinuousLinearMap.proj p : T3 →L[ℝ] ℝ) hcd (i := m) (by unfold NewtonD3.ii; exact_mod_cast (le_top : (m : ℕ∞) ≤ (⊤ : ℕ∞)))
  have hfun : ((ContinuousLinearMap.proj p : T3 →L[ℝ] ℝ) ∘ fun x => D3t (x - t • embPlane x')) =
      fun x => newtonD3 (x - t • embPlane x') p.1 p.2.1 p.2.2 := rfl
  rw [hfun] at hc
  rw [← hc]
  exact (hK ν t w x' p.1 p.2.1 p.2.2 hν ht0 ht1 hw hx).trans
    (mul_le_mul_of_nonneg_right (le_abs_self K) hp)

end NewtonVGeom

end UnforcedLeray.Short.PartIIIb.Concrete
