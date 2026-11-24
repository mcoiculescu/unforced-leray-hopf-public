import UnforcedLeray.Short.PartIIb.Sub.T22_4
import UnforcedLeray.Short.PartIIb.Sub.T22.CylDecayBridge
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.DiffusionBound.Common
import UnforcedLeray.Lib.Cylinder.IBP

/-!
# Leaf `PartII-b:T22/4/3` (`dbCutId`): the cut-off identity on the cell.

Source: `the November 2 reference manuscript` lines 2092-2104. With `w = jb^m`,
the fields `F₁ = χ(η)² g w ∂_q g` and `F₂ = χ(η)² g w ∂_η g` have divergence
`χ² (w|∇g|² + g ∇w·∇g + g w Δg) + 2 χ χ' g w ∂_η g`. The `q`-flux integrates to zero on the cell
(seam values agree by `c`-periodicity of `g`, `∂_q g` and evenness of `jb` in `q`), and the
`η`-flux integrates to zero (compact support of `χ`). Everything is continuous with `χ`-support
compact in `η`, so no decay is needed here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

namespace DbCutIdAux

open DbCommon

/-- The `q`-flux `χ(η)² g w ∂_q g`. -/
def cutF1 (χ : ℝ → ℝ) (g : B0579.Plane → ℝ) (m : ℝ) (x : B0579.Plane) : ℝ :=
  χ x.2 ^ 2 * (g x * B0579.jb x ^ m * B0579.pd 0 g x)

/-- Its `q`-derivative. -/
def cutF1' (χ : ℝ → ℝ) (g : B0579.Plane → ℝ) (m : ℝ) (x : B0579.Plane) : ℝ :=
  χ x.2 ^ 2 * (B0579.pd 0 g x * B0579.jb x ^ m * B0579.pd 0 g x +
    g x * B0579.pd 0 (fun y => B0579.jb y ^ m) x * B0579.pd 0 g x +
    g x * B0579.jb x ^ m * B0579.pd 0 (B0579.pd 0 g) x)

/-- The `η`-flux `χ(η)² g w ∂_η g`. -/
def cutF2 (χ : ℝ → ℝ) (g : B0579.Plane → ℝ) (m : ℝ) (x : B0579.Plane) : ℝ :=
  χ x.2 ^ 2 * (g x * B0579.jb x ^ m * B0579.pd 1 g x)

/-- Its `η`-derivative. -/
def cutF2' (χ : ℝ → ℝ) (g : B0579.Plane → ℝ) (m : ℝ) (x : B0579.Plane) : ℝ :=
  2 * χ x.2 * deriv χ x.2 * (g x * B0579.jb x ^ m * B0579.pd 1 g x) +
    χ x.2 ^ 2 * (B0579.pd 1 g x * B0579.jb x ^ m * B0579.pd 1 g x +
      g x * B0579.pd 1 (fun y => B0579.jb y ^ m) x * B0579.pd 1 g x +
      g x * B0579.jb x ^ m * B0579.pd 1 (B0579.pd 1 g) x)

theorem jb_rpow_differentiable (m : ℝ) : Differentiable ℝ (fun y : B0579.Plane => B0579.jb y ^ m) :=
  (B0579.contDiff_jb_rpow m).differentiable (by simp)

theorem hasDerivAt_cutF1 {χ : ℝ → ℝ} {g : B0579.Plane → ℝ} {m : ℝ} (hC : ContDiff ℝ 2 g)
    (q η : ℝ) :
    HasDerivAt (fun t => cutF1 χ g m (t, η)) (cutF1' χ g m (q, η)) q := by
  have hgd : Differentiable ℝ g := hC.differentiable (by norm_num)
  have hPd : Differentiable ℝ (B0579.pd 0 g) := (pd_contDiff_one hC 0).differentiable (by norm_num)
  have h1 := hasDerivAt_slice_q hgd q η
  have h2 := hasDerivAt_slice_q (jb_rpow_differentiable m) q η
  have h3 := hasDerivAt_slice_q hPd q η
  have h4 := ((h1.mul h2).mul h3).const_mul (χ η ^ 2)
  have hfun : (fun t => cutF1 χ g m (t, η)) =
      fun y => χ η ^ 2 * ((g (y, η) * B0579.jb (y, η) ^ m) * B0579.pd 0 g (y, η)) := rfl
  rw [hfun]
  refine h4.congr_deriv ?_
  unfold cutF1'
  dsimp only [Pi.mul_apply, Pi.add_apply]
  ring

theorem hasDerivAt_cutF2 {χ : ℝ → ℝ} {g : B0579.Plane → ℝ} {m : ℝ} (hχ : Differentiable ℝ χ)
    (hC : ContDiff ℝ 2 g) (q η : ℝ) :
    HasDerivAt (fun t => cutF2 χ g m (q, t)) (cutF2' χ g m (q, η)) η := by
  have hgd : Differentiable ℝ g := hC.differentiable (by norm_num)
  have hQd : Differentiable ℝ (B0579.pd 1 g) := (pd_contDiff_one hC 1).differentiable (by norm_num)
  have hχa : HasDerivAt χ (deriv χ η) η := (hχ η).hasDerivAt
  have hsq0 := hχa.mul hχa
  have hsq : HasDerivAt (fun t => χ t ^ 2) (deriv χ η * χ η + χ η * deriv χ η) η := by
    have e : (fun t => χ t ^ 2) = fun y => χ y * χ y := funext fun t => sq (χ t)
    rw [e]
    exact hsq0
  have h1 := hasDerivAt_slice_eta hgd q η
  have h2 := hasDerivAt_slice_eta (jb_rpow_differentiable m) q η
  have h3 := hasDerivAt_slice_eta hQd q η
  have h4 := hsq.mul (((h1.mul h2).mul h3))
  have hfun : (fun t => cutF2 χ g m (q, t)) =
      fun y => χ y ^ 2 * ((g (q, y) * B0579.jb (q, y) ^ m) * B0579.pd 1 g (q, y)) := rfl
  rw [hfun]
  refine h4.congr_deriv ?_
  unfold cutF2'
  dsimp only [Pi.mul_apply, Pi.add_apply]
  ring

/-- Periodicity of the seam values `g(c/2, η) = g(-c/2, η)`, `∂_q g` likewise, `jb` even. -/
theorem seam_eq {c : ℝ} {g : B0579.Plane → ℝ} (hg : CylSmoothDecay c g) (η : ℝ) :
    g (c / 2, η) = g (-c / 2, η) ∧ B0579.pd 0 g (c / 2, η) = B0579.pd 0 g (-c / 2, η) ∧
      B0579.jb (c / 2, η) = B0579.jb (-c / 2, η) := by
  refine ⟨?_, ?_, ?_⟩
  · have h : g (-c / 2 + c, η) = g (-c / 2, η) := hg.periodic (-c / 2, η)
    rw [show -c / 2 + c = c / 2 by ring] at h
    exact h
  · have h := pd0_periodic hg.smooth hg.periodic (-c / 2) η
    rw [show -c / 2 + c = c / 2 by ring] at h
    exact h
  · simp only [B0579.jb]
    ring

theorem cutF1_boundary_zero {c : ℝ} {g : B0579.Plane → ℝ} (hg : CylSmoothDecay c g) (m : ℝ)
    (χ : ℝ → ℝ) (η : ℝ) :
    cutF1 χ g m (c / 2, η) - cutF1 χ g m (-c / 2, η) = 0 := by
  obtain ⟨h1, h2, h3⟩ := seam_eq hg η
  unfold cutF1
  dsimp only
  rw [h1, h2, h3]
  ring

end DbCutIdAux

open DbCutIdAux DbCommon in
set_option maxHeartbeats 1000000 in
theorem dbCutId : UnforcedLeray.Short.IIb.DbCutId := by
  intro m hm c hc g hg χ hχ hχc
  have hC2 : ContDiff ℝ 2 g := hg.smooth
  obtain ⟨R, hR⟩ := exists_support_radius hχc
  have hχ0 : Continuous χ := hχ.continuous
  have hχd : Differentiable ℝ χ := hχ.differentiable (by simp)
  have hχ'0 : Continuous (deriv χ) := hχ.continuous_deriv (by exact_mod_cast le_top)
  have hgc : Continuous g := hC2.continuous
  have hPg : Continuous (B0579.pd 0 g) := continuous_pd_of_c2 hC2 0
  have hQg : Continuous (B0579.pd 1 g) := continuous_pd_of_c2 hC2 1
  have hPP : Continuous (B0579.pd 0 (B0579.pd 0 g)) := continuous_pd_pd hC2 0 0
  have hQQ : Continuous (B0579.pd 1 (B0579.pd 1 g)) := continuous_pd_pd hC2 1 1
  have hlap : Continuous (lapP g) := continuous_lapP hC2
  have hjb : Continuous (fun y : B0579.Plane => B0579.jb y ^ m) := B0579.continuous_jb_rpow m
  have hjbC : Continuous B0579.jb := by unfold B0579.jb; fun_prop
  have hwP : Continuous (B0579.pd 0 (fun y => B0579.jb y ^ m)) := continuous_pd0_jb m
  have hwQ : Continuous (B0579.pd 1 (fun y => B0579.jb y ^ m)) := continuous_pd1_jb m
  have hdens : Continuous (fun x : B0579.Plane => (B0579.density m x : ℝ)) := continuous_dens m
  -- derivatives in the slices
  have hd1 : ∀ q η, HasDerivAt (fun q' => cutF1 χ g m (q', η)) (cutF1' χ g m (q, η)) q :=
    fun q η => hasDerivAt_cutF1 hC2 q η
  have hd2 : ∀ q η, HasDerivAt (fun η' => cutF2 χ g m (q, η')) (cutF2' χ g m (q, η)) η :=
    fun q η => hasDerivAt_cutF2 hχd hC2 q η
  -- continuity and compact `η`-support of every integrand
  have c1' : Continuous (cutF1' χ g m) := by
    unfold cutF1'; fun_prop
  have c2 : Continuous (cutF2 χ g m) := by
    unfold cutF2; fun_prop
  have c2' : Continuous (cutF2' χ g m) := by
    unfold cutF2'; fun_prop
  have c1 : Continuous (cutF1 χ g m) := by
    unfold cutF1; fun_prop
  have i1' : IntegrableOn (cutF1' χ g m) (B0579.cell c) :=
    integrableOn_cell_of_eta (R := R) c1' (fun x hx => by simp [cutF1', hR x.2 hx])
  have i2 : IntegrableOn (cutF2 χ g m) (B0579.cell c) :=
    integrableOn_cell_of_eta (R := R) c2 (fun x hx => by simp [cutF2, hR x.2 hx])
  have i2' : IntegrableOn (cutF2' χ g m) (B0579.cell c) :=
    integrableOn_cell_of_eta (R := R) c2' (fun x hx => by simp [cutF2', hR x.2 hx])
  -- the cell of the library IBP lemmas is the same set, written with `-c / 2`
  have hcell : B0579.cell c = UnforcedLeray.Cyl.cell c := by
    unfold B0579.cell UnforcedLeray.Cyl.cell
    rw [neg_div]
  have i1C : IntegrableOn (cutF1' χ g m) (UnforcedLeray.Cyl.cell c) := by
    rw [← hcell]; exact i1'
  have i2C : IntegrableOn (cutF2 χ g m) (UnforcedLeray.Cyl.cell c) := by
    rw [← hcell]; exact i2
  have i2'C : IntegrableOn (cutF2' χ g m) (UnforcedLeray.Cyl.cell c) := by
    rw [← hcell]; exact i2'
  -- the `q`-flux integrates to zero
  have h1 : ∫ x in B0579.cell c, cutF1' χ g m x = 0 := by
    rw [hcell, UnforcedLeray.Cyl.integral_cell_deriv_q (F := cutF1 χ g m) (F' := cutF1' χ g m) hc
      hd1 i1C]
    simp only [cutF1_boundary_zero hg m χ, integral_zero]
  -- the `η`-flux integrates to zero
  have h2 : ∫ x in B0579.cell c, cutF2' χ g m x = 0 := by
    rw [hcell]
    exact UnforcedLeray.Cyl.integral_cell_deriv_eta (F := cutF2 χ g m) (F' := cutF2' χ g m) hd2
      i2C i2'C
  -- the four target integrands
  have hA : IntegrableOn (fun x : B0579.Plane => χ x.2 ^ 2 *
      ((B0579.density m x : ℝ) * (B0579.pd 0 g x ^ 2 + B0579.pd 1 g x ^ 2)))
      (B0579.cell c) :=
    integrableOn_cell_of_eta (R := R) (by fun_prop) (fun x hx => by simp [hR x.2 hx])
  have hB : IntegrableOn (fun x : B0579.Plane => χ x.2 ^ 2 *
      (g x * (B0579.pd 0 (fun y => B0579.jb y ^ m) x * B0579.pd 0 g x +
        B0579.pd 1 (fun y => B0579.jb y ^ m) x * B0579.pd 1 g x)))
      (B0579.cell c) :=
    integrableOn_cell_of_eta (R := R) (by fun_prop) (fun x hx => by simp [hR x.2 hx])
  have hC : IntegrableOn (fun x : B0579.Plane => χ x.2 ^ 2 *
      (g x * lapP g x * (B0579.density m x : ℝ))) (B0579.cell c) :=
    integrableOn_cell_of_eta (R := R) (by fun_prop) (fun x hx => by simp [hR x.2 hx])
  have hD : IntegrableOn (fun x : B0579.Plane => 2 * χ x.2 * deriv χ x.2 *
      (g x * (B0579.density m x : ℝ) * B0579.pd 1 g x)) (B0579.cell c) :=
    integrableOn_cell_of_eta (R := R) (by fun_prop) (fun x hx => by simp [hR x.2 hx])
  -- pointwise: the sum of the two derivatives is the four target integrands
  have hpt : ∀ x : B0579.Plane, cutF1' χ g m x + cutF2' χ g m x =
      χ x.2 ^ 2 * ((B0579.density m x : ℝ) * (B0579.pd 0 g x ^ 2 + B0579.pd 1 g x ^ 2)) +
      χ x.2 ^ 2 * (g x * (B0579.pd 0 (fun y => B0579.jb y ^ m) x * B0579.pd 0 g x +
        B0579.pd 1 (fun y => B0579.jb y ^ m) x * B0579.pd 1 g x)) +
      χ x.2 ^ 2 * (g x * lapP g x * (B0579.density m x : ℝ)) +
      2 * χ x.2 * deriv χ x.2 * (g x * (B0579.density m x : ℝ) * B0579.pd 1 g x) := by
    intro x
    unfold cutF1' cutF2'
    simp only [lapP, B0579.coe_density]
    ring
  have hsum : ∫ x in B0579.cell c, (cutF1' χ g m x + cutF2' χ g m x) = 0 := by
    rw [integral_add i1' i2', h1, h2, add_zero]
  simp only [hpt] at hsum
  rw [integral_add, integral_add, integral_add] at hsum
  all_goals first
    | linarith
    | exact ((hA.add hB).add hC)
    | exact (hA.add hB)
    | exact hA
    | exact hB
    | exact hC
    | exact hD

end UnforcedLeray.Short.IIb
