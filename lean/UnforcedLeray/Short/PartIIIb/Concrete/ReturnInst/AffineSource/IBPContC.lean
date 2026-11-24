import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.RADefs

/-!
# `IBPContC` (source 4268-4270, 5001-5008): continuity at finite smoothness

The `C^∞` version `ibpCont_proved` (`Sub/IIIb-D2_3_2/Sub/IIIb-D2_3_2_8_6.lean`) is repeated with
the smoothness budget of `IBPContC`: `D_μ` needs `C²` (one time and two space derivatives), while
`div(a⊗b + b⊗a)` and `∇q` need `C¹` only.  The slice identity is the one of
`B0005.fderiv_slice_space`, stated for a general codomain.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Slice identity for a differentiable joint map with values in any normed space. -/
theorem ibpcC_slice {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Ψ : ℝ × Space → F} (hΨ : Differentiable ℝ Ψ) (τ : ℝ) (y v : Space) :
    fderiv ℝ (fun y' => Ψ (τ, y')) y v = fderiv ℝ Ψ (τ, y) (0, v) := by
  rw [UnforcedLeray.B0005.fderiv_slice_space (hΨ (τ, y)), ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply]

/-- The time derivative of a jointly differentiable map along a slice. -/
theorem ibpcC_time {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Ψ : ℝ × Space → F} (hΨ : Differentiable ℝ Ψ) (τ : ℝ) (y : Space) :
    deriv (fun t => Ψ (t, y)) τ = fderiv ℝ Ψ (τ, y) (1, 0) := by
  have h1 : HasDerivAt (fun t : ℝ => ((t, y) : ℝ × Space)) ((1 : ℝ), (0 : Space)) τ :=
    (hasDerivAt_id' τ).prodMk (hasDerivAt_const τ y)
  exact ((hΨ (τ, y)).hasFDerivAt.comp_hasDerivAt τ h1).deriv

/-- `D_μ` of a `C²` joint field, written through the joint derivatives (source 4140-4141). -/
theorem ibpcC_dmu_eq {ν μ : ℝ} {Ψ : ℝ × Space → Space} (hΨ : ContDiff ℝ 2 Ψ) (τ : ℝ) (y : Space) :
    physDmu ν μ (fun τ y => Ψ (τ, y)) τ y =
      fderiv ℝ Ψ (τ, y) (1, 0) - (1 / 2 : ℝ) • fderiv ℝ Ψ (τ, y) (0, y) -
        ν • ∑ j : Fin 3, fderiv ℝ (fun z => fderiv ℝ Ψ z (0, coordinateVector j))
          (τ, y) (0, coordinateVector j) + (μ - 1 / 2) • Ψ (τ, y) := by
  have hd : Differentiable ℝ Ψ := hΨ.differentiable (by norm_num)
  have hg : ∀ j : Fin 3, Differentiable ℝ (fun z => fderiv ℝ Ψ z (0, coordinateVector j)) := by
    intro j
    have hC : ContDiff ℝ 1 (fderiv ℝ Ψ) := hΨ.fderiv_right (m := 1) (by norm_num)
    exact (hC.clm_apply contDiff_const).differentiable (by norm_num)
  have hC : ∀ j : Fin 3, fderiv ℝ (fun y' => fderiv ℝ (fun y'' => Ψ (τ, y'')) y' (coordinateVector j))
      y (coordinateVector j) =
        fderiv ℝ (fun z => fderiv ℝ Ψ z (0, coordinateVector j)) (τ, y) (0, coordinateVector j) := by
    intro j
    simp only [ibpcC_slice hd]
    exact ibpcC_slice (hg j) τ y _
  simp only [physDmu, physLap, physPd2, physPd]
  rw [ibpcC_time hd τ y, ibpcC_slice hd τ y y]
  simp only [hC]

theorem ibpcC_dmu_cont {ν μ : ℝ} {Ψ : ℝ × Space → Space} (hΨ : ContDiff ℝ 2 Ψ) :
    Continuous (fun x : ℝ × Space => physDmu ν μ (fun τ y => Ψ (τ, y)) x.1 x.2) := by
  have c1 : Continuous fun x : ℝ × Space => fderiv ℝ Ψ x (1, 0) :=
    (hΨ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have c2 : Continuous fun x : ℝ × Space => fderiv ℝ Ψ x (0, x.2) :=
    (hΨ.continuous_fderiv (by norm_num)).clm_apply (continuous_const.prodMk continuous_snd)
  have hC : ContDiff ℝ 1 (fderiv ℝ Ψ) := hΨ.fderiv_right (m := 1) (by norm_num)
  have c3 : Continuous fun x : ℝ × Space =>
      ∑ j : Fin 3, fderiv ℝ (fun z => fderiv ℝ Ψ z (0, coordinateVector j)) x
        (0, coordinateVector j) :=
    continuous_finsetSum _ fun j _ =>
      ((hC.clm_apply contDiff_const).continuous_fderiv (by norm_num)).clm_apply continuous_const
  have c4 : Continuous fun x : ℝ × Space => Ψ x := hΨ.continuous
  exact Continuous.congr (((c1.sub (c2.const_smul (1 / 2 : ℝ))).sub (c3.const_smul ν)).add
    (c4.const_smul (μ - 1 / 2))) (fun x => (ibpcC_dmu_eq hΨ x.1 x.2).symm)

theorem ibpcC_coord {V : ℝ × Space → Space} (hV : ContDiff ℝ 1 V) (k : Fin 3) :
    ContDiff ℝ 1 (fun x => V x k) :=
  ((EuclideanSpace.proj k : Space →L[ℝ] ℝ).contDiff.comp hV)

theorem ibpcC_divPsi {U W : ℝ → Space → Space}
    (hU : ContDiff ℝ 1 (fun x : ℝ × Space => U x.1 x.2))
    (hW : ContDiff ℝ 1 (fun x : ℝ × Space => W x.1 x.2)) (i j : Fin 3) :
    ContDiff ℝ 1 (fun x : ℝ × Space => U x.1 x.2 j * W x.1 x.2 i + W x.1 x.2 j * U x.1 x.2 i) :=
  ((ibpcC_coord hU j).mul (ibpcC_coord hW i)).add ((ibpcC_coord hW j).mul (ibpcC_coord hU i))

theorem ibpcC_div_joint {U W : ℝ → Space → Space}
    (hU : ContDiff ℝ 1 (fun x : ℝ × Space => U x.1 x.2))
    (hW : ContDiff ℝ 1 (fun x : ℝ × Space => W x.1 x.2)) (τ : ℝ) (y : Space) :
    physDivSym (U τ) (W τ) y = WithLp.toLp 2 fun i => ∑ j : Fin 3,
      fderiv ℝ (fun x : ℝ × Space => U x.1 x.2 j * W x.1 x.2 i + W x.1 x.2 j * U x.1 x.2 i)
        (τ, y) (0, coordinateVector j) := by
  unfold physDivSym
  congr 1
  funext i
  refine Finset.sum_congr rfl fun j _ => ?_
  exact ibpcC_slice ((ibpcC_divPsi hU hW i j).differentiable (by norm_num)) τ y (coordinateVector j)

theorem ibpcC_div (U W : ℝ → Space → Space)
    (hU : ContDiff ℝ 1 (fun x : ℝ × Space => U x.1 x.2))
    (hW : ContDiff ℝ 1 (fun x : ℝ × Space => W x.1 x.2)) :
    Continuous (realCf (fun τ y => physDivSym (U τ) (W τ) y)) := by
  have hG : Continuous (fun x : ℝ × Space => physDivSym (U x.1) (W x.1) x.2) := by
    have heq : (fun x : ℝ × Space => physDivSym (U x.1) (W x.1) x.2) =
        fun x => WithLp.toLp 2 (fun i => ∑ j : Fin 3,
          fderiv ℝ (fun z : ℝ × Space => U z.1 z.2 j * W z.1 z.2 i + W z.1 z.2 j * U z.1 z.2 i)
            x (0, coordinateVector j)) := by
      funext x
      exact ibpcC_div_joint hU hW x.1 x.2
    rw [heq]
    exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => continuous_finsetSum _ fun j _ =>
      ((ibpcC_divPsi hU hW i j).continuous_fderiv (by norm_num)).clm_apply continuous_const)
  exact contDiff_realC_8.continuous.comp hG

theorem ibpcC_grad_joint {q : ℝ → Space → ℝ}
    (hq : ContDiff ℝ 1 (fun x : ℝ × Space => q x.1 x.2)) (τ : ℝ) (y : Space) :
    physGrad (q τ) y = WithLp.toLp 2 fun j =>
      fderiv ℝ (fun x : ℝ × Space => q x.1 x.2) (τ, y) (0, coordinateVector j) := by
  unfold physGrad
  congr 1
  funext j
  exact ibpcC_slice (hq.differentiable (by norm_num)) τ y (coordinateVector j)

theorem ibpcC_grad (q : ℝ → Space → ℝ)
    (hq : ContDiff ℝ 1 (fun x : ℝ × Space => q x.1 x.2)) :
    Continuous (realCf (fun τ y => physGrad (q τ) y)) := by
  have hG : Continuous (fun x : ℝ × Space => physGrad (q x.1) x.2) := by
    have heq : (fun x : ℝ × Space => physGrad (q x.1) x.2) =
        fun x => WithLp.toLp 2 (fun j =>
          fderiv ℝ (fun z : ℝ × Space => q z.1 z.2) x (0, coordinateVector j)) := by
      funext x
      exact ibpcC_grad_joint hq x.1 x.2
    rw [heq]
    exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j =>
      (hq.continuous_fderiv (by norm_num)).clm_apply continuous_const)
  exact contDiff_realC_8.continuous.comp hG

theorem ibpcC_dmu (ν μ : ℝ) (u : ℝ → Space → Space)
    (hu : ContDiff ℝ 2 (fun x : ℝ × Space => u x.1 x.2)) :
    Continuous (realCf (physDmu ν μ u)) := by
  have h : Continuous (fun x : ℝ × Space => physDmu ν μ u x.1 x.2) := ibpcC_dmu_cont (Ψ := fun x : ℝ × Space => u x.1 x.2) hu
  exact contDiff_realC_8.continuous.comp h

theorem ibpContC : IBPContC := by
  refine ⟨?_, ?_, ?_⟩
  · exact fun ν μ u hu => ibpcC_dmu ν μ u hu
  · exact fun U W hU hW => ibpcC_div U W hU hW
  · exact fun q hq => ibpcC_grad q hq

end UnforcedLeray.Short.PartIIIb.Concrete
