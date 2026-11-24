import UnforcedLeray.Short.PartIIIa.Sub.T21_c2_2_5_2
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.DiffusionBound.Common
import UnforcedLeray.Lib.Cylinder.IBP

/-!
# Leaf `PartIII-a:T21/c2/2/5/2/1` (`diffGreenCut`): the cut-off Green inequality on the cell.

Source: `the November 2 reference manuscript` lines 2950-2954. Template:
`PartII-b` `dbCutId` (`Tasks/CylEnergy/DiffusionBound/CutId.lean`) with `jb^m` replaced by `p`.
With `F₁ = χ²(p ∂_q G - G ∂_q p)` and `F₂ = χ²(p ∂_η G - G ∂_η p)`, the `q`-flux integrates to
`-2 ∫ χ² G ∂_q p(c/2,·) ≤ 0` (`p` even, `∂_q p` odd in `q`, `G` `c`-periodic), and the `η`-flux
integrates to zero.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Short.IIb
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace GreenCutAux

open DbCommon

/-- The `q`-flux `χ(η)² (p ∂_q G - G ∂_q p)`. -/
def gF1 (χ : ℝ → ℝ) (p G : B0579.Plane → ℝ) (x : B0579.Plane) : ℝ :=
  χ x.2 ^ 2 * (p x * B0579.pd 0 G x - G x * B0579.pd 0 p x)

/-- Its `q`-derivative. -/
def gF1' (χ : ℝ → ℝ) (p G : B0579.Plane → ℝ) (x : B0579.Plane) : ℝ :=
  χ x.2 ^ 2 * (B0579.pd 0 p x * B0579.pd 0 G x + p x * B0579.pd 0 (B0579.pd 0 G) x -
    (B0579.pd 0 G x * B0579.pd 0 p x + G x * B0579.pd 0 (B0579.pd 0 p) x))

/-- The `η`-flux `χ(η)² (p ∂_η G - G ∂_η p)`. -/
def gF2 (χ : ℝ → ℝ) (p G : B0579.Plane → ℝ) (x : B0579.Plane) : ℝ :=
  χ x.2 ^ 2 * (p x * B0579.pd 1 G x - G x * B0579.pd 1 p x)

/-- Its `η`-derivative. -/
def gF2' (χ : ℝ → ℝ) (p G : B0579.Plane → ℝ) (x : B0579.Plane) : ℝ :=
  (deriv χ x.2 * χ x.2 + χ x.2 * deriv χ x.2) *
      (p x * B0579.pd 1 G x - G x * B0579.pd 1 p x) +
    χ x.2 ^ 2 * (B0579.pd 1 p x * B0579.pd 1 G x + p x * B0579.pd 1 (B0579.pd 1 G) x -
      (B0579.pd 1 G x * B0579.pd 1 p x + G x * B0579.pd 1 (B0579.pd 1 p) x))

theorem hasDerivAt_gF1 {χ : ℝ → ℝ} {p G : B0579.Plane → ℝ} (hp : ContDiff ℝ 2 p)
    (hG : ContDiff ℝ 2 G) (q η : ℝ) :
    HasDerivAt (fun t => gF1 χ p G (t, η)) (gF1' χ p G (q, η)) q := by
  have hpd : Differentiable ℝ p := hp.differentiable (by norm_num)
  have hGd : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hpd0 : Differentiable ℝ (B0579.pd 0 p) :=
    (pd_contDiff_one hp 0).differentiable (by norm_num)
  have hGd0 : Differentiable ℝ (B0579.pd 0 G) :=
    (pd_contDiff_one hG 0).differentiable (by norm_num)
  have hA := hasDerivAt_slice_q hpd q η
  have hB := hasDerivAt_slice_q hGd q η
  have hC := hasDerivAt_slice_q hGd0 q η
  have hD := hasDerivAt_slice_q hpd0 q η
  have h4 := ((hA.mul hC).sub (hB.mul hD)).const_mul (χ η ^ 2)
  have hfun : (fun t => gF1 χ p G (t, η)) =
      fun y => χ η ^ 2 * (p (y, η) * B0579.pd 0 G (y, η) - G (y, η) * B0579.pd 0 p (y, η)) :=
    rfl
  rw [hfun]
  refine h4.congr_deriv ?_
  simp only [gF1']
  try ring

theorem hasDerivAt_gF2 {χ : ℝ → ℝ} {p G : B0579.Plane → ℝ} (hχ : Differentiable ℝ χ)
    (hp : ContDiff ℝ 2 p) (hG : ContDiff ℝ 2 G) (q η : ℝ) :
    HasDerivAt (fun t => gF2 χ p G (q, t)) (gF2' χ p G (q, η)) η := by
  have hpd : Differentiable ℝ p := hp.differentiable (by norm_num)
  have hGd : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hpd1 : Differentiable ℝ (B0579.pd 1 p) :=
    (pd_contDiff_one hp 1).differentiable (by norm_num)
  have hGd1 : Differentiable ℝ (B0579.pd 1 G) :=
    (pd_contDiff_one hG 1).differentiable (by norm_num)
  have hχa : HasDerivAt χ (deriv χ η) η := (hχ η).hasDerivAt
  have hsq0 := hχa.mul hχa
  have hsq : HasDerivAt (fun t => χ t ^ 2) (deriv χ η * χ η + χ η * deriv χ η) η := by
    have e : (fun t => χ t ^ 2) = fun y => χ y * χ y := funext fun t => sq (χ t)
    rw [e]
    exact hsq0
  have hA := hasDerivAt_slice_eta hpd q η
  have hB := hasDerivAt_slice_eta hGd q η
  have hC := hasDerivAt_slice_eta hGd1 q η
  have hD := hasDerivAt_slice_eta hpd1 q η
  have h4 := hsq.mul ((hA.mul hC).sub (hB.mul hD))
  have hfun : (fun t => gF2 χ p G (q, t)) =
      fun y => χ y ^ 2 * (p (q, y) * B0579.pd 1 G (q, y) - G (q, y) * B0579.pd 1 p (q, y)) :=
    rfl
  rw [hfun]
  refine h4.congr_deriv ?_
  simp only [gF2', Pi.mul_apply, Pi.sub_apply]
  try ring

end GreenCutAux

open GreenCutAux DbCommon in
/-- **Leaf `diffGreenCut`** (SP 2950-2954): the cut-off Green inequality for `DiffGreenCut`. -/
theorem diffGreenCut : DiffGreenCut := by
  intro c m p hc hp G hG hper hG0 χ hχ hχc
  obtain ⟨R, hR⟩ := exists_support_radius hχc
  have hχd : Differentiable ℝ χ := hχ.differentiable (by simp)
  have hχ0 : Continuous χ := hχ.continuous
  have hχ'0 : Continuous (deriv χ) := hχ.continuous_deriv (by exact_mod_cast le_top)
  have hpD : Differentiable ℝ p := hp.smooth.differentiable (by norm_num)
  have hpc : Continuous p := hp.smooth.continuous
  have hGc : Continuous G := hG.continuous
  have hp0 : Continuous (B0579.pd 0 p) := continuous_pd_of_c2 hp.smooth 0
  have hp1 : Continuous (B0579.pd 1 p) := continuous_pd_of_c2 hp.smooth 1
  have hG0c : Continuous (B0579.pd 0 G) := continuous_pd_of_c2 hG 0
  have hG1c : Continuous (B0579.pd 1 G) := continuous_pd_of_c2 hG 1
  have hpp00 : Continuous (B0579.pd 0 (B0579.pd 0 p)) := continuous_pd_pd hp.smooth 0 0
  have hpp11 : Continuous (B0579.pd 1 (B0579.pd 1 p)) := continuous_pd_pd hp.smooth 1 1
  have hGG00 : Continuous (B0579.pd 0 (B0579.pd 0 G)) := continuous_pd_pd hG 0 0
  have hGG11 : Continuous (B0579.pd 1 (B0579.pd 1 G)) := continuous_pd_pd hG 1 1
  have hLp : Continuous (lapP p) := continuous_lapP hp.smooth
  have hLG : Continuous (lapP G) := continuous_lapP hG
  -- derivatives in the slices
  have hd1 : ∀ q η, HasDerivAt (fun q' => gF1 χ p G (q', η)) (gF1' χ p G (q, η)) q :=
    fun q η => hasDerivAt_gF1 hp.smooth hG q η
  have hd2 : ∀ q η, HasDerivAt (fun η' => gF2 χ p G (q, η')) (gF2' χ p G (q, η)) η :=
    fun q η => hasDerivAt_gF2 hχd hp.smooth hG q η
  -- continuity and compact `η`-support of every integrand
  have c1' : Continuous (gF1' χ p G) := by
    unfold gF1'; fun_prop
  have c2 : Continuous (gF2 χ p G) := by
    unfold gF2; fun_prop
  have c2' : Continuous (gF2' χ p G) := by
    unfold gF2'; fun_prop
  have i1' : IntegrableOn (gF1' χ p G) (B0579.cell c) :=
    integrableOn_cell_of_eta (R := R) c1' (fun x hx => by simp [gF1', hR x.2 hx])
  have i2 : IntegrableOn (gF2 χ p G) (B0579.cell c) :=
    integrableOn_cell_of_eta (R := R) c2 (fun x hx => by simp [gF2, hR x.2 hx])
  have i2' : IntegrableOn (gF2' χ p G) (B0579.cell c) :=
    integrableOn_cell_of_eta (R := R) c2' (fun x hx => by simp [gF2', hR x.2 hx])
  -- the cell of the library IBP lemmas is the same set, written with `-c / 2`
  have hcell : B0579.cell c = UnforcedLeray.Cyl.cell c := by
    unfold B0579.cell UnforcedLeray.Cyl.cell
    rw [neg_div]
  have i1C : IntegrableOn (gF1' χ p G) (UnforcedLeray.Cyl.cell c) := by
    rw [← hcell]; exact i1'
  have i2C : IntegrableOn (gF2 χ p G) (UnforcedLeray.Cyl.cell c) := by
    rw [← hcell]; exact i2
  have i2'C : IntegrableOn (gF2' χ p G) (UnforcedLeray.Cyl.cell c) := by
    rw [← hcell]; exact i2'
  -- the boundary term of the `q`-flux is nonpositive
  have hbd : ∀ η : ℝ, gF1 χ p G (c / 2, η) - gF1 χ p G (-c / 2, η) ≤ 0 := by
    intro η
    have hGs : G (-c / 2, η) = G (c / 2, η) := by
      have h : G (-c / 2 + c, η) = G (-c / 2, η) := hper (-c / 2, η)
      rw [show -c / 2 + c = c / 2 by ring] at h
      exact h.symm
    have hPGs : B0579.pd 0 G (-c / 2, η) = B0579.pd 0 G (c / 2, η) := by
      have h : B0579.pd 0 G (-c / 2 + c, η) = B0579.pd 0 G (-c / 2, η) :=
        pd0_periodic hG hper (-c / 2) η
      rw [show -c / 2 + c = c / 2 by ring] at h
      exact h.symm
    have hpe : p (-c / 2, η) = p (c / 2, η) := hp.even η
    have hpo : B0579.pd 0 p (-c / 2, η) = -B0579.pd 0 p (c / 2, η) := hp.oddq η
    have hnn : 0 ≤ χ η ^ 2 * (G (c / 2, η) * B0579.pd 0 p (c / 2, η)) :=
      mul_nonneg (sq_nonneg _) (mul_nonneg (hG0 _) (hp.seam_nonneg η))
    unfold gF1
    simp only []
    rw [hpe, hpo, hGs, hPGs]
    nlinarith [hnn]
  -- the `q`-flux integrates to a nonpositive quantity
  have hI1 : ∫ x in B0579.cell c, gF1' χ p G x ≤ 0 := by
    rw [hcell, UnforcedLeray.Cyl.integral_cell_deriv_q (F := gF1 χ p G) (F' := gF1' χ p G) hc
      hd1 i1C]
    exact integral_nonpos hbd
  -- the `η`-flux integrates to zero
  have h2 : ∫ x in B0579.cell c, gF2' χ p G x = 0 := by
    rw [hcell]
    exact UnforcedLeray.Cyl.integral_cell_deriv_eta (F := gF2 χ p G) (F' := gF2' χ p G) hd2
      i2C i2'C
  -- integrability of the two target integrands
  have hA : IntegrableOn (fun x : B0579.Plane => χ x.2 ^ 2 *
      (p x * lapP G x - G x * lapP p x)) (B0579.cell c) :=
    integrableOn_cell_of_eta (R := R) (by fun_prop) (fun x hx => by simp [hR x.2 hx])
  have hB : IntegrableOn (fun x : B0579.Plane => 2 * χ x.2 * deriv χ x.2 *
      (p x * B0579.pd 1 G x - G x * B0579.pd 1 p x)) (B0579.cell c) :=
    integrableOn_cell_of_eta (R := R) (by fun_prop) (fun x hx => by simp [hR x.2 hx])
  -- pointwise: the sum of the two derivatives is the two target integrands
  have hpt : ∀ x : B0579.Plane, gF1' χ p G x + gF2' χ p G x =
      χ x.2 ^ 2 * (p x * lapP G x - G x * lapP p x) +
      2 * χ x.2 * deriv χ x.2 * (p x * B0579.pd 1 G x - G x * B0579.pd 1 p x) := by
    intro x
    unfold gF1' gF2'
    simp only [lapP]
    ring
  have hsum : ∫ x in B0579.cell c, (gF1' χ p G x + gF2' χ p G x) =
      (∫ x in B0579.cell c, gF1' χ p G x) + ∫ x in B0579.cell c, gF2' χ p G x :=
    integral_add i1' i2'
  rw [h2, add_zero] at hsum
  simp only [hpt] at hsum
  rw [integral_add hA hB] at hsum
  linarith [hI1, hsum]

end UnforcedLeray.Short.IIIa
