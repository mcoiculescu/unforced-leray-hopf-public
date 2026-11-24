import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16

/-!
# `PartIII-a:T16/1` : `SepWDominated` from the differentiated-under-the-integral bound

Source `the November 2 reference manuscript` lines 3604-3623 (`sep:kernel`,
`sep:resolvent`, radial gap).  The only analytic step not proved here is the differentiation of
`sepW` under the `(λ,z)` integral (`SepWDiffUnder`); the radial gap and the replacement of the
raw majorant by the gap-truncated `sepKd` on the support are proved.  Both Props carry the
finiteness of the order-`0` majorant at the receiver (see `SepWDominated`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- **Differentiation under the `(λ,z)` integral** (SP 3611-3623): `|D^j W_μ(y,τ)|` is bounded by
`C0 ∫_0^1 λ^{2Re μ+2} ∫ |y-λz|^{-4-j} |T(z,τ+2log λ)| dz dλ` for receivers `|y'| ≥ r_i` at which
the order-`0` majorant (`sepDom` at order `0`) is finite (the kernel bound
`|D^{n+1}K_t(x)| ≤ C|x|^{-4-n}` of `SepKernelBounds`, uniform in `t>0`, applied at `x = y' - λz`,
which stays in `|x| ≥ (r_i - r_o)/2 > 0` on the support for `|y' - y| < (r_i - r_o)/2`; there the
order-`n` weight is at most `2^{4+n}(r_i - r_o)^{-n}` times the order-`0` weight at `y`, so the
finite order-`0` majorant dominates every derivative and differentiation under the integral is
justified; tensor contractions cost an absolute constant absorbed in `C0`).  Without the
finiteness the bound fails to be meaningful: see `SepWDominated`. -/
def SepWDiffUnder : Prop :=
  SepKernelBounds → ∀ j : ℕ, ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ ν : ℝ, 0 < ν → ∀ μ : ℂ, -(1 / 4) < μ.re →
    ∀ rOut rIn P : ℝ, 0 ≤ rOut → rOut < rIn → 0 < P →
      ∀ T, IsSepSource P rOut T → ∀ (τ : ℝ) (y : Space), rIn ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) →
        sepDom (2 * μ.re + 2) 0 (rIn - rOut) (srcNorm T) τ y < ⊤ →
        wDerivNorm ν μ T j τ y ≤
          ENNReal.ofReal C0 * ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (2 * μ.re + 2)) *
            ∫⁻ z : Space, ENNReal.ofReal (‖y - l • z‖ ^ (-4 - (j : ℝ))) *
              srcNorm T (τ + 2 * Real.log l) z

theorem rho_add_le (u v : Space) :
    Real.sqrt ((u 0 + v 0) ^ 2 + (u 1 + v 1) ^ 2) ≤
      Real.sqrt (u 0 ^ 2 + u 1 ^ 2) + Real.sqrt (v 0 ^ 2 + v 1 ^ 2) := by
  have hu := Real.sqrt_nonneg (u 0 ^ 2 + u 1 ^ 2)
  have hv := Real.sqrt_nonneg (v 0 ^ 2 + v 1 ^ 2)
  have hu2 := Real.sq_sqrt (show 0 ≤ u 0 ^ 2 + u 1 ^ 2 by positivity)
  have hv2 := Real.sq_sqrt (show 0 ≤ v 0 ^ 2 + v 1 ^ 2 by positivity)
  have hcs : u 0 * v 0 + u 1 * v 1 ≤
      Real.sqrt (u 0 ^ 2 + u 1 ^ 2) * Real.sqrt (v 0 ^ 2 + v 1 ^ 2) := by
    rw [← Real.sqrt_mul (by positivity)]
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg (u 0 * v 1 - u 1 * v 0)]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  nlinarith

theorem rho_le_norm (x : Space) : Real.sqrt (x 0 ^ 2 + x 1 ^ 2) ≤ ‖x‖ := by
  have h : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_three]
  apply Real.sqrt_le_iff.mpr
  refine ⟨norm_nonneg _, ?_⟩
  nlinarith [sq_nonneg (x 2)]

/-- The radial gap: `|y - λz| ≥ r_i - r_o`. -/
theorem radial_gap (y z : Space) (l rOut rIn : ℝ) (hl : l ∈ Ioo (0 : ℝ) 1)
    (hz : Real.sqrt (z 0 ^ 2 + z 1 ^ 2) ≤ rOut) (hy : rIn ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) :
    rIn - rOut ≤ ‖y - l • z‖ := by
  have h1 := rho_add_le (y - l • z) (l • z)
  have h2 : Real.sqrt ((l • z) 0 ^ 2 + (l • z) 1 ^ 2) = l * Real.sqrt (z 0 ^ 2 + z 1 ^ 2) := by
    have : (l • z) 0 ^ 2 + (l • z) 1 ^ 2 = l ^ 2 * (z 0 ^ 2 + z 1 ^ 2) := by
      simp only [PiLp.smul_apply, smul_eq_mul]; ring
    rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hl.1.le]
  have h3 : (y - l • z) 0 + (l • z) 0 = y 0 := by simp
  have h4 : (y - l • z) 1 + (l • z) 1 = y 1 := by simp
  rw [h3, h4, h2] at h1
  have h5 := rho_le_norm (y - l • z)
  have h6 : l * Real.sqrt (z 0 ^ 2 + z 1 ^ 2) ≤ rOut := by
    have := Real.sqrt_nonneg (z 0 ^ 2 + z 1 ^ 2)
    nlinarith [hl.2, hl.1]
  linarith

theorem sepWDominated_of (h : SepWDiffUnder) : SepWDominated := by
  intro hK j
  obtain ⟨C0, hC0, hB⟩ := h hK j
  refine ⟨C0, hC0, ?_⟩
  intro ν hν μ hμ rOut rIn P hrO hrr hP T hT τ y hy hfin
  refine (hB ν hν μ hμ rOut rIn P hrO hrr hP T hT τ y hy hfin).trans ?_
  unfold sepDom
  refine mul_le_mul' le_rfl (setLIntegral_mono' measurableSet_Ioo fun l hl => ?_)
  refine mul_le_mul' le_rfl (lintegral_mono fun z => ?_)
  by_cases hz : Real.sqrt (z 0 ^ 2 + z 1 ^ 2) ≤ rOut
  · have hg := radial_gap y z l rOut rIn hl hz hy
    unfold sepKd
    rw [if_pos hg]
  · push_neg at hz
    have hT0 := hT.support (τ + 2 * Real.log l) z hz
    have : srcNorm T (τ + 2 * Real.log l) z = 0 := by
      unfold srcNorm tensorNorm; rw [hT0]; simp
    rw [this]; simp

end UnforcedLeray.Short.IIIa
end
