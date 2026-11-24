import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_5_3_2

/-!
# `PartIII-a:T21/2/2/3/5/3/2` leaf `E1ScaleR`: change of variables in the field-derivative term

Source of record: `the November 2 reference manuscript` (SP) lines 2860-2864,
3036-3037. With `x = √a y`: `physW(r, √a y) = p_d⁻¹(y)`, `∂_kφ(r, √a y) = √a ∂_kΦ(y)`,
`psiK = -(a√a) ∂_k∂_rφ(√a ·)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.AdjE1

open UnforcedLeray.Short.IIIa

theorem e1ScaleR (m : ℝ) : E1ScaleR m := by
  unfold E1ScaleR
  intro ν tr t s φ ζ hζ k
  obtain ⟨hr, ha⟩ := adjFlowAt_age hζ
  obtain ⟨hν, _, _, ⟨G, _, hF⟩, _⟩ := hζ
  have hc : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hφ : ContDiff ℝ ∞ (φ (revAge ν s ζ)) := hF.smooth _ (Ioo_subset_Ico_self hr)
  have hs : 0 < Real.sqrt (clockA ν (revAge ν s ζ)) := Real.sqrt_pos.mpr ha
  have hs' : Real.sqrt (clockA ν (revAge ν s ζ)) ≠ 0 := hs.ne'
  have ha' : clockA ν (revAge ν s ζ) ≠ 0 := ha.ne'
  have key : ∀ y : ℝ × ℝ,
      physW ν (ν ^ (-2 : ℝ)) m (revAge ν s ζ)
          (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1, Real.sqrt (clockA ν (revAge ν s ζ)) * y.2) *
        ((starRingEnd ℂ) (pdCx k (φ (revAge ν s ζ))
            (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1, Real.sqrt (clockA ν (revAge ν s ζ)) * y.2)) *
          pdCx k (adjDt t s φ (revAge ν s ζ))
            (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1, Real.sqrt (clockA ν (revAge ν s ζ)) * y.2)).re
      = -((clockA ν (revAge ν s ζ))⁻¹) *
          (periodicWeight (-m) (mvLen ν (ν ^ (-2 : ℝ)) s ζ) y *
            ((starRingEnd ℂ) (pdCx k (mvPhi ν φ s ζ) y) * psiK ν t s φ ζ k y).re) := by
    intro y
    have hx : ((Real.sqrt (clockA ν (revAge ν s ζ)) * y.1,
        Real.sqrt (clockA ν (revAge ν s ζ)) * y.2) : ℝ × ℝ) =
        Real.sqrt (clockA ν (revAge ν s ζ)) • y := by
      ext <;> simp [smul_eq_mul]
    have hdiv : ((Real.sqrt (clockA ν (revAge ν s ζ)) • y).1 / Real.sqrt (clockA ν (revAge ν s ζ)),
        (Real.sqrt (clockA ν (revAge ν s ζ)) • y).2 / Real.sqrt (clockA ν (revAge ν s ζ))) = y := by
      ext <;> simp [smul_eq_mul, hs']
    have e1 : physW ν (ν ^ (-2 : ℝ)) m (revAge ν s ζ)
        (Real.sqrt (clockA ν (revAge ν s ζ)) • y) =
        periodicWeight (-m) (mvLen ν (ν ^ (-2 : ℝ)) s ζ) y := by
      unfold physW mvLen cellLen
      rw [hdiv]
    have e2 : pdCx k (φ (revAge ν s ζ)) (Real.sqrt (clockA ν (revAge ν s ζ)) • y) =
        ((Real.sqrt (clockA ν (revAge ν s ζ)) : ℝ) : ℂ) * pdCx k (mvPhi ν φ s ζ) y := by
      have h : pdCx k (mvPhi ν φ s ζ) y =
          (((clockA ν (revAge ν s ζ))⁻¹ : ℝ) : ℂ) * ((Real.sqrt (clockA ν (revAge ν s ζ)) : ℝ) : ℂ) *
            pdCx k (φ (revAge ν s ζ)) (Real.sqrt (clockA ν (revAge ν s ζ)) • y) :=
        pdCx_movingPhi ν φ (revAge ν s ζ) hφ k y
      have hk := sqrt_mul_sqrt_inv_mul _ ha
      linear_combination (-((Real.sqrt (clockA ν (revAge ν s ζ)) : ℝ) : ℂ)) * h +
        (-(pdCx k (φ (revAge ν s ζ)) (Real.sqrt (clockA ν (revAge ν s ζ)) • y))) * hk
    have e3 : psiK ν t s φ ζ k y =
        -(((clockA ν (revAge ν s ζ) * Real.sqrt (clockA ν (revAge ν s ζ)) : ℝ)) : ℂ) *
          pdCx k (adjDt t s φ (revAge ν s ζ)) (Real.sqrt (clockA ν (revAge ν s ζ)) • y) := rfl
    rw [hx, e1, e2, e3, map_mul, Complex.conj_ofReal]
    have A : ((((Real.sqrt (clockA ν (revAge ν s ζ)) : ℝ)) : ℂ) *
        (starRingEnd ℂ) (pdCx k (mvPhi ν φ s ζ) y)) *
        pdCx k (adjDt t s φ (revAge ν s ζ)) (Real.sqrt (clockA ν (revAge ν s ζ)) • y) =
        ((Real.sqrt (clockA ν (revAge ν s ζ)) : ℝ) : ℂ) *
          ((starRingEnd ℂ) (pdCx k (mvPhi ν φ s ζ) y) *
            pdCx k (adjDt t s φ (revAge ν s ζ)) (Real.sqrt (clockA ν (revAge ν s ζ)) • y)) := by
      ring
    have B : (starRingEnd ℂ) (pdCx k (mvPhi ν φ s ζ) y) *
        (-(((clockA ν (revAge ν s ζ) * Real.sqrt (clockA ν (revAge ν s ζ)) : ℝ)) : ℂ) *
          pdCx k (adjDt t s φ (revAge ν s ζ)) (Real.sqrt (clockA ν (revAge ν s ζ)) • y)) =
        (((-(clockA ν (revAge ν s ζ) * Real.sqrt (clockA ν (revAge ν s ζ))) : ℝ)) : ℂ) *
          ((starRingEnd ℂ) (pdCx k (mvPhi ν φ s ζ) y) *
            pdCx k (adjDt t s φ (revAge ν s ζ)) (Real.sqrt (clockA ν (revAge ν s ζ)) • y)) := by
      push_cast
      ring
    rw [A, B, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    have hinv : (clockA ν (revAge ν s ζ))⁻¹ * clockA ν (revAge ν s ζ) = 1 := inv_mul_cancel₀ ha'
    linear_combination (-(periodicWeight (-m) (mvLen ν (ν ^ (-2 : ℝ)) s ζ) y *
        Real.sqrt (clockA ν (revAge ν s ζ)) *
        ((starRingEnd ℂ) (pdCx k (mvPhi ν φ s ζ) y) *
          pdCx k (adjDt t s φ (revAge ν s ζ)) (Real.sqrt (clockA ν (revAge ν s ζ)) • y)).re)) * hinv
  have hcs : ∫ y in B0579.cell (mvLen ν (ν ^ (-2 : ℝ)) s ζ),
      physW ν (ν ^ (-2 : ℝ)) m (revAge ν s ζ)
          (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1, Real.sqrt (clockA ν (revAge ν s ζ)) * y.2) *
        ((starRingEnd ℂ) (pdCx k (φ (revAge ν s ζ))
            (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1, Real.sqrt (clockA ν (revAge ν s ζ)) * y.2)) *
          pdCx k (adjDt t s φ (revAge ν s ζ))
            (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1, Real.sqrt (clockA ν (revAge ν s ζ)) * y.2)).re
      = (clockA ν (revAge ν s ζ))⁻¹ * ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
          physW ν (ν ^ (-2 : ℝ)) m (revAge ν s ζ) x *
            ((starRingEnd ℂ) (pdCx k (φ (revAge ν s ζ)) x) *
              pdCx k (adjDt t s φ (revAge ν s ζ)) x).re :=
    UnforcedLeray.Short.IIIa.integral_cell_scale (ν ^ (-2 : ℝ)) (clockA ν (revAge ν s ζ)) ha
      (fun x => physW ν (ν ^ (-2 : ℝ)) m (revAge ν s ζ) x *
        ((starRingEnd ℂ) (pdCx k (φ (revAge ν s ζ)) x) *
          pdCx k (adjDt t s φ (revAge ν s ζ)) x).re)
  have h2 : ∫ y in B0579.cell (mvLen ν (ν ^ (-2 : ℝ)) s ζ),
      physW ν (ν ^ (-2 : ℝ)) m (revAge ν s ζ)
          (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1, Real.sqrt (clockA ν (revAge ν s ζ)) * y.2) *
        ((starRingEnd ℂ) (pdCx k (φ (revAge ν s ζ))
            (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1, Real.sqrt (clockA ν (revAge ν s ζ)) * y.2)) *
          pdCx k (adjDt t s φ (revAge ν s ζ))
            (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1, Real.sqrt (clockA ν (revAge ν s ζ)) * y.2)).re
      = ∫ y in B0579.cell (mvLen ν (ν ^ (-2 : ℝ)) s ζ),
          -((clockA ν (revAge ν s ζ))⁻¹) *
            (periodicWeight (-m) (mvLen ν (ν ^ (-2 : ℝ)) s ζ) y *
              ((starRingEnd ℂ) (pdCx k (mvPhi ν φ s ζ) y) * psiK ν t s φ ζ k y).re) := by
    congr 1
    funext y
    exact key y
  rw [integral_const_mul] at h2
  rw [h2] at hcs
  set I := ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
          physW ν (ν ^ (-2 : ℝ)) m (revAge ν s ζ) x *
            ((starRingEnd ℂ) (pdCx k (φ (revAge ν s ζ)) x) *
              pdCx k (adjDt t s φ (revAge ν s ζ)) x).re with hI
  set J := ∫ y in B0579.cell (mvLen ν (ν ^ (-2 : ℝ)) s ζ),
          periodicWeight (-m) (mvLen ν (ν ^ (-2 : ℝ)) s ζ) y *
            ((starRingEnd ℂ) (pdCx k (mvPhi ν φ s ζ) y) * psiK ν t s φ ζ k y).re with hJ
  have h3 : (clockA ν (revAge ν s ζ))⁻¹ * (I + J) = 0 := by
    linear_combination (-1 : ℝ) * hcs
  have h4 : I + J = 0 := (mul_eq_zero.mp h3).resolve_left (inv_ne_zero ha')
  linear_combination (-2 : ℝ) * h4

end UnforcedLeray.Short.IIIa.AdjE1
