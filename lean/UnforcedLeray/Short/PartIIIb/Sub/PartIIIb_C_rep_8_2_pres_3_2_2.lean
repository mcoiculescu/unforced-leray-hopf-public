import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_2.AxiU

/-!
# `presChgPhys` (`PartIII-b:C/rep/8/2/pres/3/2/2`)

Source of record: `the November 2 reference manuscript`:
1205-1225 and 1217 (`p_lift = s p_cyl` is smooth off the axis, `P`-periodic since `p_cyl` is
`c`-periodic in `q` and `Axi.phase` shifts by `R P/2 = c`), 2031 and 2522-2523 (`U` is axisymmetric
without swirl), 4139-4141 (`D₀U + U·∇U + ∇p = 0`, `U`, `p` smooth and `P`-periodic), 4144-4145.

* measurability: the density is continuous on the open off-axis set and `axisZero` is a piecewise
  function across the closed axis;
* periodicity: `IsExactProfile.periodicP` and the periodicity of `liftP`;
* axisymmetry: `∇p` is equivariant (`grad_gEqv`, from `IsExactProfile.equation` and the
  equivariance of `U`, `pf2b_axiU`), `∇p_lift` is equivariant since `p_lift ∘ g = p_lift`; so
  `∇p - ∇p_lift` is axisymmetric without swirl and its norm is invariant under `merPt`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

theorem pf2b_varrho_apply (g : Space ≃ₗᵢ[ℝ] Space) (hg : FixesAxis g) (y : Space) :
    ϱ (g y) = ϱ y := by
  have := ϱ_symm_apply g hg (g y)
  rw [g.symm_apply_apply] at this
  exact this.symm

theorem pf2b_apply_two (g : Space ≃ₗᵢ[ℝ] Space) (hg : FixesAxis g) (y : Space) :
    (g y) 2 = y 2 := by
  have := symm_apply_two g hg (g y)
  rw [g.symm_apply_apply] at this
  exact this.symm

/-- `p_lift ∘ g = p_lift` for every isometry `g` fixing `e₃` (source 1217). -/
theorem pf2b_liftP_invariant (L : ReturnLevel) (τ : ℝ) (g : Space ≃ₗᵢ[ℝ] Space)
    (hg : FixesAxis g) (y : Space) : liftP L τ (g y) = liftP L τ y := by
  have h1 := pf2b_varrho_apply g hg y
  have h2 := pf2b_apply_two g hg y
  simp only [liftP, Axi.chart, Axi.age, Axi.phase, Axi.trans, h1, h2]

/-- `p_lift` is `P`-periodic (source 1217: `Axi.phase` shifts by `R P/2 = c`, `p_cyl` is
`c`-periodic in `q`). -/
theorem pf2b_liftP_periodic (L : ReturnLevel) (τ : ℝ) (y : Space) :
    liftP L (τ + 2 * L.ε * cOf L.ν) y = liftP L τ y := by
  have hε : L.ε ≠ 0 := L.ε_pos.ne'
  have hph : Axi.phase L.ε⁻¹ (τ + 2 * L.ε * cOf L.ν) y = Axi.phase L.ε⁻¹ τ y + cOf L.ν := by
    simp only [Axi.phase]
    field_simp
    ring
  have hage : (Axi.chart L.ε⁻¹ (τ + 2 * L.ε * cOf L.ν) y) =
      ((Axi.chart L.ε⁻¹ τ y).1, ((Axi.chart L.ε⁻¹ τ y).2.1 + cOf L.ν,
        (Axi.chart L.ε⁻¹ τ y).2.2)) := by
    simp only [Axi.chart, hph]
  have hnn : 0 ≤ (Axi.chart L.ε⁻¹ τ y).1 := by
    simp only [Axi.chart, Axi.age]; positivity
  have hper := L.train.isTrain.periodic_p _ hnn ((Axi.chart L.ε⁻¹ τ y).2)
  unfold liftP
  rw [hage]
  exact congrArg _ hper

/-- `⟪∇q(y), v⟫ = Dq(y) v`. -/
theorem pf2b_inner_physGrad (q : Space → ℝ) (y v : Space) :
    inner ℝ (physGrad q y) v = fderiv ℝ q y v := by
  conv_rhs => rw [pf_eq_sum_coord v]
  conv_lhs => rw [pf_eq_sum_coord v]
  simp only [map_sum, map_smul, inner_sum, inner_smul_right, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [physGrad, coordinateVector, EuclideanSpace.inner_single_right]

/-- The gradient of a `g`-invariant scalar is `g`-equivariant. -/
theorem pf2b_physGrad_equiv {q : Space → ℝ} (g : Space ≃ₗᵢ[ℝ] Space)
    (hq : ∀ y, q (g y) = q y) (y : Space) : physGrad q (g y) = g (physGrad q y) := by
  have h1 : fderiv ℝ q y = (fderiv ℝ q (g y)).comp (g.toContinuousLinearEquiv : Space →L[ℝ] Space) := by
    have e : q = q ∘ g.toContinuousLinearEquiv := funext fun x => (hq x).symm
    conv_lhs => rw [e]
    exact ContinuousLinearEquiv.comp_right_fderiv (iso := g.toContinuousLinearEquiv) 
  have hD : ∀ v, fderiv ℝ q y v = fderiv ℝ q (g y) (g v) := fun v => by
    rw [h1]; rfl
  refine ext_inner_right ℝ fun v => ?_
  rw [pf2b_inner_physGrad]
  calc fderiv ℝ q (g y) v = fderiv ℝ q (g y) (g (g.symm v)) := by rw [g.apply_symm_apply]
    _ = fderiv ℝ q y (g.symm v) := (hD _).symm
    _ = inner ℝ (physGrad q y) (g.symm v) := (pf2b_inner_physGrad _ _ _).symm
    _ = inner ℝ (g (physGrad q y)) (g (g.symm v)) := (g.inner_map_map _ _).symm
    _ = inner ℝ (g (physGrad q y)) v := by rw [g.apply_symm_apply]

/-- `∇p - ∇p_lift` is continuous off the axis, hence its norm density is measurable. -/
theorem pf2b_presChg_contOn (L : ReturnLevel)
    (hP : ContDiff ℝ ∞ (fun x : ℝ × Space => L.pres x.1 x.2)) :
    ContinuousOn (fun x : ℝ × Space => presChgDens (L.pres x.1) (liftP L x.1) x.2) offAxisSet := by
  have h1 := physGrad_continuousOn (F := fun x => L.pres x.1 x.2)
    (hP.contDiffOn.mono (subset_univ _))
  have h2 := physGrad_continuousOn (F := fun x => liftP L x.1 x.2) (liftP_contDiffOn L L.ε_pos)
  exact (h1.sub h2).norm

theorem presChgPhys (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    D.PresChgPhys := by
  filter_upwards [hst.actual, pf2b_axiU D hst] with n hn hU
  refine ⟨?_, ?_, ?_⟩
  · exact pf4_axisZero_measurable
      (f := fun τ y => presChgDens ((D.level n).pres τ) (liftP (D.level n) τ) y)
      (pf2b_presChg_contOn (D.level n) hn.profile.smoothP)
  · intro τ y
    have hp : (D.level n).pres (τ + 2 * (D.level n).ε * cOf (D.level n).ν) = (D.level n).pres τ :=
      funext fun y' => hn.profile.periodicP τ y'
    have hl : liftP (D.level n) (τ + 2 * (D.level n).ε * cOf (D.level n).ν) =
        liftP (D.level n) τ := funext fun y' => pf2b_liftP_periodic (D.level n) τ y'
    rw [hp, hl]
  · intro τ y
    have hW : AxiNoSwirlPt (fun y' => physGrad ((D.level n).pres τ) y' -
        physGrad (liftP (D.level n) τ) y') := by
      refine axi_of_gEqv fun g hg y' => ?_
      have h1 := grad_gEqv fderivEqv_proved lapEqv_proved hn.profile g
        (fun t => axi_gEqv (hU t) hg) τ y'
      have h2 := pf2b_physGrad_equiv (q := liftP (D.level n) τ) g
        (pf2b_liftP_invariant (D.level n) τ g hg) y'
      show physGrad (D.pres n τ) (g y') - physGrad (liftP (D.level n) τ) (g y') =
        g (physGrad (D.pres n τ) y' - physGrad (liftP (D.level n) τ) y')
      rw [h1, h2, map_sub]
    exact (axiDens_azimuth hW y).1

end UnforcedLeray.Short.PartIIIb.Concrete
