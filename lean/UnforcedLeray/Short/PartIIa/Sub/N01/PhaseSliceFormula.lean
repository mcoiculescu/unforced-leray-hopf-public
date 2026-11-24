import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_2
import UnforcedLeray.Units.B0223
import UnforcedLeray.Units.B0421.FreeC
import UnforcedLeray.Lib.HeatR3.Space
import UnforcedLeray.Analysis.Heat.Flow
import UnforcedLeray.Short.PartIIa.Tasks.F01BodyResolvent.HeatPositivity

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp
open UnforcedLeray.B0223 (ιx)

/-- Free side: the free semigroup at positive time on an `L²` class, as a heat average. -/
theorem psf_free_formula (ν t : ℝ) (hν : 0 < ν) (ht : 0 < t)
    (v : Lp CVec3 2 (volume : Measure Space)) :
    (B0421.freeC (p := 2) ENNReal.ofNat_ne_top ν t v : Space → CVec3) =ᵐ[volume]
      fun y => Real.exp (t / 2) • UnforcedLeray.Heat.average (ν * (Real.exp t - 1))
        (v : Space → CVec3) (Real.exp (t / 2) • y) := by
  have hθ : 0 < ν * (Real.exp t - 1) := mul_pos hν (by linarith [Real.add_one_lt_exp ht.ne'])
  have hfe : ∀ (f : Space → Space) (y : Space),
      AncientLocalization.freeEvolution ν t f y =
        Real.exp (t / 2) • UnforcedLeray.Heat.average (ν * (Real.exp t - 1)) f
          (Real.exp (t / 2) • y) := by
    intro f y
    simp only [AncientLocalization.freeEvolution, AncientLocalization.similarityDilation,
      SpatialScaling.spatialScale]
    rw [UnforcedLeray.Heat.flow_pos f hθ]
  have hre : (reV.compLpL 2 (volume : Measure Space) v : Space → Space) =ᵐ[volume]
      fun z => reV (v z) := by
    filter_upwards [reV.coeFn_compLpL (μ := (volume : Measure Space)) (p := 2) v] with z hz
    exact hz
  have him : (imV.compLpL 2 (volume : Measure Space) v : Space → Space) =ᵐ[volume]
      fun z => imV (v z) := by
    filter_upwards [imV.coeFn_compLpL (μ := (volume : Measure Space)) (p := 2) v] with z hz
    exact hz
  have hA := UnforcedLeray.Heat.average_congr_ae (t := ν * (Real.exp t - 1)) hre
  have hB := UnforcedLeray.Heat.average_congr_ae (t := ν * (Real.exp t - 1)) him
  filter_upwards [B0421.coeFn_freeC (p := 2) ENNReal.ofNat_ne_top ν t v] with y hy
  rw [hy, hfe, hfe, hA, hB, map_smul, map_smul, ← smul_add]
  congr 1
  exact UnforcedLeray.Short.PartIIa.ofReV_average_add_ofImV_average ENNReal.ofNat_ne_top hθ
    (v : Space → CVec3) (Lp.memLp v) (Real.exp (t / 2) • y)

/-- The right-hand side of the formula `S_ε(t)` (tex lines 3350–3352), as a function on `PSpace`. -/
def psfPhi (ν ε t : ℝ) {P : ℝ} [Fact (0 < P)] (F : B0223.PSpace P → B0223.SpaceC)
    (z : B0223.PSpace P) : B0223.SpaceC :=
  Real.exp (t / 2) • Heat.heatConv (ιx P) (ν * ε ^ 2 * (Real.exp t - 1))
    (fun w => F (w.1, w.2 - (t : AddCircle P))) (Real.exp (t / 2) • z.1, z.2)

/-- Slice identity: the shifted heat integral on `ℝ³ × ℝ/Pℤ` is the spatial heat integral on the slice. -/
theorem psf_slice' (θ s : ℝ) {P : ℝ} [Fact (0 < P)] (F : B0223.PSpace P → B0223.SpaceC) (x : Space)
    (τ : AddCircle P) :
    Heat.heatConv (ιx P) θ (fun w => F (w.1, w.2 - (s : AddCircle P))) (x, τ) =
      Heat.heatConv (AddMonoidHom.id Space) θ (fun w => F (w, τ - (s : AddCircle P))) x := by
  have hι : ∀ w : Space, (x, τ) - (ιx P) w = (x - w, τ) := fun w => by
    rw [B0223.ιx_apply, Prod.mk_sub_mk, sub_zero]
  simp only [Heat.heatConv, AddMonoidHom.id_apply, hι]

set_option maxHeartbeats 1600000 in
theorem phaseSliceFormula : UnforcedLeray.Short.PartIIa.N01.PhaseSliceFormula := by
  intro ν ε P _ hν hε U hU t ht F
  have hP : 0 < P := Fact.out
  have hθ' : 0 < ν * (Real.exp t - 1) := mul_pos hν (by linarith [Real.add_one_lt_exp ht.ne'])
  have hθ : 0 < ν * ε ^ 2 * (Real.exp t - 1) :=
    mul_pos (mul_pos hν (by positivity)) (by linarith [Real.add_one_lt_exp ht.ne'])
  have hκ : (Real.sqrt P * ε ^ (3 / 2 : ℝ) : ℝ) ≠ 0 :=
    mul_ne_zero (Real.sqrt_pos.2 hP).ne' (Real.rpow_pos_of_pos hε _).ne'
  have hκC : ((Real.sqrt P * ε ^ (3 / 2 : ℝ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hκ
  -- the S-formula, in the product measure
  have hS1 : ∀ᵐ z ∂((volume : Measure Space).prod (volume : Measure (AddCircle P))),
      ((B0223.outerS (E := B0223.SpaceC) (P := P) hν ε).T t F : B0223.PSpace P → B0223.SpaceC) z =
        psfPhi ν ε t (F : B0223.PSpace P → B0223.SpaceC) z := by
    rw [← B0223.volume_pspace]
    exact B0223.S_formula hν hε ht F
  have hS2 : ∀ᵐ z ∂((volume : Measure (AddCircle P)).prod (volume : Measure Space)),
      ((B0223.outerS (E := B0223.SpaceC) (P := P) hν ε).T t F : B0223.PSpace P → B0223.SpaceC)
          (z.2, z.1) = psfPhi ν ε t (F : B0223.PSpace P → B0223.SpaceC) (z.2, z.1) :=
    (Measure.measurePreserving_swap (μ := (volume : Measure (AddCircle P)))
      (ν := (volume : Measure Space))).quasiMeasurePreserving.ae hS1
  have hS3 : ∀ᵐ τ ∂(volume : Measure (AddCircle P)), ∀ᵐ y ∂(volume : Measure Space),
      ((B0223.outerS (E := B0223.SpaceC) (P := P) hν ε).T t F : B0223.PSpace P → B0223.SpaceC)
          (y, τ) = psfPhi ν ε t (F : B0223.PSpace P → B0223.SpaceC) (y, τ) :=
    Measure.ae_ae_of_ae_prod hS2
  have hPne : ENNReal.ofReal P ≠ 0 := (ENNReal.ofReal_pos.2 hP).ne'
  have hS4 : ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)), ∀ᵐ y ∂(volume : Measure Space),
      ((B0223.outerS (E := B0223.SpaceC) (P := P) hν ε).T t F : B0223.PSpace P → B0223.SpaceC)
          (y, τ) = psfPhi ν ε t (F : B0223.PSpace P → B0223.SpaceC) (y, τ) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle] at hS3
    exact (Measure.ae_ennreal_smul_measure_iff hPne).1 hS3
  have hA := hU ((B0223.outerS (E := B0223.SpaceC) (P := P) hν ε).T t F)
  have hB : ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)),
      ∀ᵐ y ∂(volume : Measure Space),
        ((U F (τ - (t : AddCircle P)) : Lp B0223.SpaceC 2 (volume : Measure Space)) :
            Space → B0223.SpaceC) y =
          ((Real.sqrt P * ε ^ (3 / 2 : ℝ) : ℝ) : ℂ) • (F : B0223.PSpace P → B0223.SpaceC) (ε • y, τ - (t : AddCircle P)) := by
    have hF := hU F
    have hq := (measurePreserving_sub_right (AddCircle.haarAddCircle (T := P))
      (t : AddCircle P)).quasiMeasurePreserving
    exact hq.ae (p := fun τ' : AddCircle P => ∀ᵐ y ∂(volume : Measure Space),
      ((U F τ' : Lp B0223.SpaceC 2 (volume : Measure Space)) : Space → B0223.SpaceC) y =
        ((Real.sqrt P * ε ^ (3 / 2 : ℝ) : ℝ) : ℂ) •
          (F : B0223.PSpace P → B0223.SpaceC) (ε • y, τ')) hF
  filter_upwards [hA, hB, hS4] with τ hAτ hBτ hSτ
  refine Lp.ext ?_
  have hεne : ε ≠ 0 := hε.ne'
  have hW : ∀ᵐ w ∂(volume : Measure Space),
      (F : B0223.PSpace P → B0223.SpaceC) (w, τ - (t : AddCircle P)) =
        ((Real.sqrt P * ε ^ (3 / 2 : ℝ) : ℝ) : ℂ)⁻¹ •
          ((U F (τ - (t : AddCircle P)) : Lp B0223.SpaceC 2 (volume : Measure Space)) :
            Space → B0223.SpaceC) (ε⁻¹ • w) := by
    filter_upwards [(Measure.quasiMeasurePreserving_smul (μ := (volume : Measure Space))
      (inv_ne_zero hεne)).ae hBτ] with w hw
    beta_reduce at hw
    rw [smul_inv_smul₀ hεne] at hw
    rw [hw, smul_smul, inv_mul_cancel₀ hκC, one_smul]
  have e1 := UnforcedLeray.Heat.average_congr_ae (t := ν * ε ^ 2 * (Real.exp t - 1))
    (f := fun w : Space => (F : B0223.PSpace P → B0223.SpaceC) (w, τ - (t : AddCircle P)))
    (g := fun w : Space => ((Real.sqrt P * ε ^ (3 / 2 : ℝ) : ℝ) : ℂ)⁻¹ •
          ((U F (τ - (t : AddCircle P)) : Lp B0223.SpaceC 2 (volume : Measure Space)) :
            Space → B0223.SpaceC) (ε⁻¹ • w)) hW
  have e2 : UnforcedLeray.Heat.average (ν * ε ^ 2 * (Real.exp t - 1))
      (fun w : Space => ((Real.sqrt P * ε ^ (3 / 2 : ℝ) : ℝ) : ℂ)⁻¹ •
          ((U F (τ - (t : AddCircle P)) : Lp B0223.SpaceC 2 (volume : Measure Space)) :
            Space → B0223.SpaceC) (ε⁻¹ • w)) =
      fun x => ((Real.sqrt P * ε ^ (3 / 2 : ℝ) : ℝ) : ℂ)⁻¹ •
          UnforcedLeray.Heat.average (ν * ε ^ 2 * (Real.exp t - 1))
            (fun w : Space => ((U F (τ - (t : AddCircle P)) : Lp B0223.SpaceC 2
              (volume : Measure Space)) : Space → B0223.SpaceC) (ε⁻¹ • w)) x := by
    funext x
    simp only [UnforcedLeray.Heat.average]
    rw [← integral_smul]
    congr 1
    funext y'
    rw [smul_comm]
  have e3 := UnforcedLeray.Heat.average_dilate (lam := ε⁻¹) (θ := ν * ε ^ 2 * (Real.exp t - 1))
    (inv_pos.2 hε) hθ
    ((U F (τ - (t : AddCircle P)) : Lp B0223.SpaceC 2 (volume : Measure Space)) :
      Space → B0223.SpaceC)
  have hθeq : (ε⁻¹) ^ 2 * (ν * ε ^ 2 * (Real.exp t - 1)) = ν * (Real.exp t - 1) := by
    field_simp
  have hPhi : ∀ y : Space, psfPhi ν ε t F (ε • y, τ) =
      Real.exp (t / 2) • (((Real.sqrt P * ε ^ (3 / 2 : ℝ) : ℝ) : ℂ)⁻¹ •
        UnforcedLeray.Heat.average (ν * (Real.exp t - 1))
          ((U F (τ - (t : AddCircle P)) : Lp B0223.SpaceC 2 (volume : Measure Space)) :
            Space → B0223.SpaceC) (Real.exp (t / 2) • y)) := by
    intro y
    have h0 : psfPhi ν ε t F (ε • y, τ) =
        Real.exp (t / 2) • Heat.heatConv (AddMonoidHom.id Space) (ν * ε ^ 2 * (Real.exp t - 1))
          (fun w => (F : B0223.PSpace P → B0223.SpaceC) (w, τ - (t : AddCircle P)))
          (Real.exp (t / 2) • (ε • y)) := by
      simp only [psfPhi]
      rw [psf_slice']
    have hpt : ε⁻¹ • (Real.exp (t / 2) • (ε • y)) = Real.exp (t / 2) • y := by
      rw [smul_smul, smul_smul, show ε⁻¹ * Real.exp (t / 2) * ε = Real.exp (t / 2) by
        field_simp]
    rw [h0, UnforcedLeray.Heat.heatConv_space_eq_average, e1, e2]
    dsimp only
    rw [e3]
    dsimp only
    rw [hθeq, hpt]
  have hSε : ∀ᵐ y ∂(volume : Measure Space),
      ((B0223.outerS (E := B0223.SpaceC) (P := P) hν ε).T t F : B0223.PSpace P → B0223.SpaceC)
          (ε • y, τ) = psfPhi ν ε t (F : B0223.PSpace P → B0223.SpaceC) (ε • y, τ) :=
    (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure Space)) hεne).ae hSτ
  filter_upwards [hAτ, hSε, psf_free_formula ν t hν ht (U F (τ - (t : AddCircle P)))] with
    y h1 h2 h3
  rw [h1, h2, hPhi y, h3, smul_comm, smul_inv_smul₀ hκC]

end UnforcedLeray.Short.PartIIa.N01
