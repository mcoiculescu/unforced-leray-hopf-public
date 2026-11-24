import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T12_1_4_1

/-!

Source: `the November 2 reference manuscript` lines 1933-1935.
Each translate `G(· + j c e_q)` is weakly divergence free against planar tests, since
`φ(· - j c e_q)` is again a planar test; the average is a finite combination, so it is too.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Function
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- Translation `z ↦ (z.1 + a, z.2)` preserves Lebesgue measure on the plane. -/
theorem ppl_div_mp_shift (a : ℝ) :
    MeasurePreserving (fun z : ℝ × ℝ => (z.1 + a, z.2)) volume volume := by
  rw [Measure.volume_eq_prod]
  exact (measurePreserving_add_right (volume : Measure ℝ) a).prod (MeasurePreserving.id volume)

/-- A coordinate of an `L²` field, composed with a `q`-translation, is `L²`. -/
theorem ppl_div_coord_memLp {G : ℝ × ℝ → CMerid} (hG : MemLp G 2 volume) (a : ℝ) (i : Fin 2) :
    MemLp (fun z : ℝ × ℝ => G (z.1 + a, z.2) i) 2 volume := by
  have h1 : MemLp (fun z : ℝ × ℝ => G (z.1 + a, z.2)) 2 volume :=
    hG.comp_measurePreserving (ppl_div_mp_shift a)
  exact h1.continuousLinearMap_comp (EuclideanSpace.proj i : CMerid →L[ℂ] ℂ)

/-- A planar test derivative in a fixed direction is `L²` (continuous, compactly supported). -/
theorem ppl_div_deriv_memLp {φ : ℝ × ℝ → ℝ} (hφ : PlaneTest φ) (e : ℝ × ℝ) :
    MemLp (fun z : ℝ × ℝ => (fderiv ℝ φ z e : ℂ)) 2 volume := by
  apply Continuous.memLp_of_hasCompactSupport
  · exact Complex.continuous_ofReal.comp ((hφ.smooth.continuous_fderiv (by simp)).clm_apply
      continuous_const)
  · exact (hφ.compact.fderiv_apply ℝ e).comp_left Complex.ofReal_zero

/-- **Task `PartII-b:T12/1/4/1/3`** (`PPLAvgDivFree`). -/
theorem ppl_avg_div_free : UnforcedLeray.Short.IIb.PPLAvgDivFree := by
  intro c N G hG hdiv φ hφ
  -- each translate vanishes against every planar test
  have hcomp : ∀ j : ℤ, ∫ z, (G (z.1 + (j : ℝ) * c, z.2) 0 * (fderiv ℝ φ z (1, 0) : ℂ) +
      G (z.1 + (j : ℝ) * c, z.2) 1 * (fderiv ℝ φ z (0, 1) : ℂ)) = 0 := by
    intro j
    set a : ℝ := (j : ℝ) * c with ha
    set u : ℝ × ℝ := (-a, 0) with hu
    have hψ : PlaneTest (fun w : ℝ × ℝ => φ (w + u)) := by
      constructor
      · exact hφ.smooth.comp (contDiff_id.add contDiff_const)
      · exact hφ.compact.comp_homeomorph (Homeomorph.addRight u)
    have h0 := hdiv (fun w : ℝ × ℝ => φ (w + u)) hψ
    have hd : ∀ z : ℝ × ℝ, fderiv ℝ (fun w : ℝ × ℝ => φ (w + u)) z = fderiv ℝ φ (z + u) :=
      fun z => fderiv_comp_add_right u
    simp only [hd] at h0
    have e2 : ∀ z : ℝ × ℝ, z + (a, (0 : ℝ)) = (z.1 + a, z.2) := fun z => by ext <;> simp
    have e1 : ∀ z : ℝ × ℝ, (z.1 + a, z.2) + u = z := fun z => by
      ext <;> simp [hu]
    have key : ∫ z, (G (z.1 + a, z.2) 0 * (fderiv ℝ φ z (1, 0) : ℂ) +
        G (z.1 + a, z.2) 1 * (fderiv ℝ φ z (0, 1) : ℂ)) =
        ∫ z, (G z 0 * (fderiv ℝ φ (z + u) (1, 0) : ℂ) + G z 1 * (fderiv ℝ φ (z + u) (0, 1) : ℂ)) := by
      rw [← integral_add_right_eq_self (fun z : ℝ × ℝ =>
        (G z 0 * (fderiv ℝ φ (z + u) (1, 0) : ℂ) + G z 1 * (fderiv ℝ φ (z + u) (0, 1) : ℂ))) (a, (0 : ℝ))]
      congr 1
      funext z
      simp only [e2, e1]
    rw [key]
    exact h0
  -- integrability of each translate of the average integrand
  have hint : ∀ j : ℤ, Integrable (fun z : ℝ × ℝ => G (z.1 + (j : ℝ) * c, z.2) 0 * (fderiv ℝ φ z (1, 0) : ℂ) +
      G (z.1 + (j : ℝ) * c, z.2) 1 * (fderiv ℝ φ z (0, 1) : ℂ)) := by
    intro j
    have h1 := (ppl_div_coord_memLp hG ((j : ℝ) * c) 0).integrable_mul (ppl_div_deriv_memLp hφ (1, 0))
    have h2 := (ppl_div_coord_memLp hG ((j : ℝ) * c) 1).integrable_mul (ppl_div_deriv_memLp hφ (0, 1))
    exact h1.add h2
  -- the average integrand is `N⁻¹` times the sum of the translate integrands
  have hpt : ∀ z : ℝ × ℝ, ppAvg c N G z 0 * (fderiv ℝ φ z (1, 0) : ℂ) +
      ppAvg c N G z 1 * (fderiv ℝ φ z (0, 1) : ℂ) =
      (N : ℂ)⁻¹ * ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        (G (z.1 + (j : ℝ) * c, z.2) 0 * (fderiv ℝ φ z (1, 0) : ℂ) +
          G (z.1 + (j : ℝ) * c, z.2) 1 * (fderiv ℝ φ z (0, 1) : ℂ)) := by
    intro z
    have hs : ∀ i : Fin 2, (∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), G (z.1 + (j : ℝ) * c, z.2)) i =
        ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), G (z.1 + (j : ℝ) * c, z.2) i := by
      intro i
      first
        | exact map_sum (EuclideanSpace.proj i) _ _
        | simp [WithLp.ofLp_sum, Finset.sum_apply]
    have hA : ∀ i : Fin 2, ppAvg c N G z i =
        (N : ℂ)⁻¹ * ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), G (z.1 + (j : ℝ) * c, z.2) i := by
      intro i
      unfold ppAvg
      rw [PiLp.smul_apply, smul_eq_mul, hs i]
    rw [hA 0, hA 1]
    have e2 : ∀ k x y d1 d2 : ℂ, k * x * d1 + k * y * d2 = k * (x * d1 + y * d2) :=
      fun k x y d1 d2 => by ring
    rw [e2, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  have hfun : (fun z : ℝ × ℝ => ppAvg c N G z 0 * (fderiv ℝ φ z (1, 0) : ℂ) +
      ppAvg c N G z 1 * (fderiv ℝ φ z (0, 1) : ℂ)) =
      fun z => (N : ℂ)⁻¹ * ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        (G (z.1 + (j : ℝ) * c, z.2) 0 * (fderiv ℝ φ z (1, 0) : ℂ) +
          G (z.1 + (j : ℝ) * c, z.2) 1 * (fderiv ℝ φ z (0, 1) : ℂ)) := funext hpt
  rw [hfun, integral_const_mul, integral_finsetSum _ (fun j _ => hint j),
    Finset.sum_eq_zero (fun j _ => hcomp j), mul_zero]

#print axioms UnforcedLeray.Short.IIb.ppl_avg_div_free
