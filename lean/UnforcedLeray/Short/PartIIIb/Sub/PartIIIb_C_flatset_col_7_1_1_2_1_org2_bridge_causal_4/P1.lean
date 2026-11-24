import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1_org2_bridge_causal_4
import UnforcedLeray.Units.B0224.PlaneHeat
import UnforcedLeray.Lib.HeatR3.ConvOp
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Measure

/-!
# Leaf `PlaneHeatVecAe` (source `shorter-proof-2026-11-02.tex` 1650-1656)

For `σ < s` the heat time `θ = ν (s - σ)` is positive. The slice of `Gh` is a.e. the vector
of the components of `G`; the planar heat is an integral over the translations `planeι y`, and
`y ↦ x - planeι y` is measure preserving, so the a.e. identity transfers pointwise in `x`. The
vector integral is then taken componentwise (`eval_integral_piLp`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff Interval
open UnforcedLeray.Gaussian (Euc gaussKernel)

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem planeHeatVecAe : UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.PlaneHeatVecAe := by
  intro c ν G hG hν Gh σ s hlt h x
  have hGc : ∀ i : Fin 2, Continuous fun p : UnforcedLeray.Short.PartIIIb.Concrete.Chart => G p i :=
    fun i => (hG.1 i).continuous
  have hbd : ∀ i : Fin 2, ∃ M : ℝ, ∀ p : UnforcedLeray.Short.PartIIIb.Concrete.Chart,
      ‖G p i‖ ≤ M := by
    intro i
    obtain ⟨C, hC⟩ := hG.2.2.2 i 0
    exact ⟨C, fun p => by simpa [norm_iteratedFDeriv_zero] using hC p⟩
  have huv : ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)),
      UnforcedLeray.B0220.periodize c (⇑Gh) (σ, z) =
        (WithLp.toLp 2 (fun i : Fin 2 => ((G (σ, z) i : ℝ) : ℂ)) : UnforcedLeray.B0223.MeridC) := by
    filter_upwards [ae_all_iff.2 h] with z hz
    ext i
    simpa using hz i
  have hmp : MeasurePreserving (fun y : Euc 2 => UnforcedLeray.B0224.planeι y) volume volume :=
    (MeasureTheory.volume_preserving_finTwoArrow ℝ).comp
      (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (ι := Fin 2))
  have hsh : MeasurePreserving (fun y : Euc 2 => x - UnforcedLeray.B0224.planeι y) volume volume :=
    (volume.measurePreserving_sub_left x).comp hmp
  have hae : ∀ᵐ y ∂(volume : Measure (Euc 2)),
      UnforcedLeray.B0220.periodize c (⇑Gh) (σ, x - UnforcedLeray.B0224.planeι y) =
        (WithLp.toLp 2 (fun i : Fin 2 => ((G (σ, x - UnforcedLeray.B0224.planeι y) i : ℝ) : ℂ)) :
          UnforcedLeray.B0223.MeridC) :=
    hsh.quasiMeasurePreserving.ae huv
  set θ : ℝ := ν * (s - σ) with hθdef
  have hθ : 0 < θ := mul_pos hν (sub_pos.2 hlt)
  have hint : ∀ i : Fin 2, Integrable (fun y : Euc 2 =>
      (gaussKernel 2 θ y • (WithLp.toLp 2 (fun j : Fin 2 =>
        ((G (σ, x - UnforcedLeray.B0224.planeι y) j : ℝ) : ℂ)) :
          UnforcedLeray.B0223.MeridC)) i) volume := by
    intro i
    obtain ⟨M, hM⟩ := hbd i
    have hfun : (fun y : Euc 2 => (gaussKernel 2 θ y • (WithLp.toLp 2 (fun j : Fin 2 =>
        ((G (σ, x - UnforcedLeray.B0224.planeι y) j : ℝ) : ℂ)) :
          UnforcedLeray.B0223.MeridC)) i) =
        fun y : Euc 2 => ((gaussKernel 2 θ y * G (σ, x - UnforcedLeray.B0224.planeι y) i : ℝ) : ℂ) := by
      funext y
      simp [Complex.real_smul]
    rw [hfun]
    refine Integrable.mono' ((UnforcedLeray.Gaussian.integrable_gaussKernel hθ).mul_const M) ?_ ?_
    · apply Continuous.aestronglyMeasurable
      apply Complex.continuous_ofReal.comp
      apply Continuous.mul
      · exact UnforcedLeray.Gaussian.continuous_gaussKernel θ
      · exact (hGc i).comp (continuous_const.prodMk
          (continuous_const.sub UnforcedLeray.B0224.continuous_planeι))
    · refine Eventually.of_forall fun y => ?_
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (UnforcedLeray.Gaussian.gaussKernel_nonneg hθ y)]
      exact mul_le_mul_of_nonneg_left
        (by simpa [Real.norm_eq_abs] using hM (σ, x - UnforcedLeray.B0224.planeι y))
        (UnforcedLeray.Gaussian.gaussKernel_nonneg hθ y)
  have e1 : UnforcedLeray.B0224.planeHeat θ
      (fun z => UnforcedLeray.B0220.periodize c (⇑Gh) (σ, z)) x =
      ∫ y : Euc 2, gaussKernel 2 θ y • (WithLp.toLp 2 (fun j : Fin 2 =>
        ((G (σ, x - UnforcedLeray.B0224.planeι y) j : ℝ) : ℂ)) : UnforcedLeray.B0223.MeridC) := by
    rw [UnforcedLeray.B0224.planeHeat_of_pos hθ]
    refine integral_congr_ae ?_
    filter_upwards [hae] with y hy
    simp only [hy]
  have e2 : ∀ i : Fin 2, UnforcedLeray.B0224.planeHeat θ (fun z => ((G (σ, z) i : ℝ) : ℂ)) x =
      ∫ y : Euc 2, gaussKernel 2 θ y • ((G (σ, x - UnforcedLeray.B0224.planeι y) i : ℝ) : ℂ) := by
    intro i
    simp only [UnforcedLeray.B0224.planeHeat_of_pos hθ]
  rw [e1]
  ext i
  rw [eval_integral_piLp (f := fun y : Euc 2 => gaussKernel 2 θ y • (WithLp.toLp 2
      (fun j : Fin 2 => ((G (σ, x - UnforcedLeray.B0224.planeι y) j : ℝ) : ℂ)) :
        UnforcedLeray.B0223.MeridC)) hint i]
  rw [WithLp.ofLp_toLp, e2 i]
  congr 1

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
