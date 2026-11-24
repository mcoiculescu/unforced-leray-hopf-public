import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_4_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_4.KcJointMeasurable
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ZeroModeLinearity

/-!
# Continuity of the gradient maps `kcGQ`, `kcGE` (helper for `KcGradRep`)

Source `the November 2 reference manuscript` 3426-3430.  `nonzeroPart` is
continuous (`meanPart` is `tensorLI ∘ eval₀ ∘ modes`), `zeroVelEtaLp` is real-linear on the
zero-circulation subspace (as `zeroVelLp_add`, using `omegaBar_add_ae` and `ae_cellVol`) and
bounded by `norm_zeroVelEtaLp_le`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution
  (realBiotSavartKernelCLM zeroCirculationSubmodule mem_zeroCirculationSubmodule_iff
    omegaBar_add_ae omegaBar_smul_ae realPartVelocityLp)

theorem continuous_meanPart {c : ℝ} [Fact (0 < c)] :
    Continuous (fun ω : MeasureTheory.Lp ℂ 2 (B0581.cellVol c) => B0581.meanPart c ω) := by
  unfold B0581.meanPart
  have h1 : Continuous (fun ω : MeasureTheory.Lp ℂ 2 (B0581.cellVol c) =>
      ((B0581.modes c ω : B0581.ModeSeq ℂ) 0)) :=
    (lp.evalCLM (E := fun _ : ℤ => MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)) (p := 2) ℂ 0).continuous.comp
      (B0581.modes c).continuous
  exact (B0581.tensorLI c 0).continuous.comp h1

theorem continuous_nonzeroPart {c : ℝ} [Fact (0 < c)] :
    Continuous (fun ω : MeasureTheory.Lp ℂ 2 (B0581.cellVol c) => B0581.nonzeroPart c ω) := by
  unfold B0581.nonzeroPart
  exact continuous_id.sub continuous_meanPart

theorem zeroVelEtaLp_add {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)
    (w z : B0579.X c m) (hw0 : ∫ x in B0579.cell c, w x = 0)
    (hz0 : ∫ x in B0579.cell c, z x = 0)
    (hwz0 : ∫ x in B0579.cell c, (w + z) x = 0) :
    B0583.zeroVelEtaLp c hm (w + z) hwz0 =
      B0583.zeroVelEtaLp c hm w hw0 + B0583.zeroVelEtaLp c hm z hz0 := by
  apply Lp.ext
  have hae : ∀ᵐ x : B0579.Plane ∂(B0581.cellVol c),
      B0583.omegaBar c ((w + z : B0579.X c m) : B0579.Plane → ℝ) x.2 =
        B0583.omegaBar c (w : B0579.Plane → ℝ) x.2 + B0583.omegaBar c (z : B0579.Plane → ℝ) x.2 := by
    rw [B0581.cellVol_eq]
    exact (MeasureTheory.Measure.quasiMeasurePreserving_snd
      (μ := B0581.μq c) (ν := (volume : Measure ℝ))).ae_eq_comp (omegaBar_add_ae hm w z)
  filter_upwards [
    B0583.coeFn_zeroVelEtaLp c hm (w + z) hwz0,
    B0583.coeFn_zeroVelEtaLp c hm w hw0,
    B0583.coeFn_zeroVelEtaLp c hm z hz0,
    Lp.coeFn_add (B0583.zeroVelEtaLp c hm w hw0) (B0583.zeroVelEtaLp c hm z hz0), hae]
    with x hsum hw hz hadd hx
  rw [hsum, hadd, Pi.add_apply, hw, hz]
  change B0583.zeroVelEta c ((w + z : B0579.X c m) : B0579.Plane → ℝ) x =
    B0583.zeroVelEta c (w : B0579.Plane → ℝ) x + B0583.zeroVelEta c (z : B0579.Plane → ℝ) x
  simp only [B0583.zeroVelEta, B0583.profField]
  rw [hx]
  simp only [neg_add, Complex.ofReal_add, add_smul]

theorem zeroVelEtaLp_smul {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)
    (a : ℝ) (w : B0579.X c m) (hw0 : ∫ x in B0579.cell c, w x = 0)
    (haw0 : ∫ x in B0579.cell c, (a • w) x = 0) :
    B0583.zeroVelEtaLp c hm (a • w) haw0 = a • B0583.zeroVelEtaLp c hm w hw0 := by
  apply Lp.ext
  have hae : ∀ᵐ x : B0579.Plane ∂(B0581.cellVol c),
      B0583.omegaBar c ((a • w : B0579.X c m) : B0579.Plane → ℝ) x.2 =
        a * B0583.omegaBar c (w : B0579.Plane → ℝ) x.2 := by
    rw [B0581.cellVol_eq]
    exact (MeasureTheory.Measure.quasiMeasurePreserving_snd
      (μ := B0581.μq c) (ν := (volume : Measure ℝ))).ae_eq_comp (omegaBar_smul_ae hm a w)
  filter_upwards [
    B0583.coeFn_zeroVelEtaLp c hm (a • w) haw0,
    B0583.coeFn_zeroVelEtaLp c hm w hw0,
    Lp.coeFn_smul a (B0583.zeroVelEtaLp c hm w hw0), hae] with x hscaled hw hsmul hx
  rw [hscaled, hsmul, Pi.smul_apply, hw]
  change B0583.zeroVelEta c ((a • w : B0579.X c m) : B0579.Plane → ℝ) x =
    a • B0583.zeroVelEta c (w : B0579.Plane → ℝ) x
  simp only [B0583.zeroVelEta, B0583.profField]
  rw [hx]
  ext i
  fin_cases i <;> simp [Complex.ofReal_mul, smul_eq_mul]

/-- `zeroVelEtaLp` as a bounded real-linear map on the zero-circulation subspace. -/
def zeroVelEtaCLM {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m) :
    zeroCirculationSubmodule (c := c) (m := m) (by linarith : 1 / 2 < m) →L[ℝ]
      MeasureTheory.Lp B0581.Vel 2 (B0581.cellVol c) := by
  let Z := zeroCirculationSubmodule (c := c) (m := m) (by linarith : 1 / 2 < m)
  let L : Z →ₗ[ℝ] MeasureTheory.Lp B0581.Vel 2 (B0581.cellVol c) := {
    toFun := fun w => B0583.zeroVelEtaLp c hm w.1 ((mem_zeroCirculationSubmodule_iff
      (by linarith : 1 / 2 < m) w.1).1 w.2)
    map_add' := fun w z => zeroVelEtaLp_add hm w.1 z.1
        ((mem_zeroCirculationSubmodule_iff (by linarith : 1 / 2 < m) w.1).1 w.2)
        ((mem_zeroCirculationSubmodule_iff (by linarith : 1 / 2 < m) z.1).1 z.2)
        ((mem_zeroCirculationSubmodule_iff (by linarith : 1 / 2 < m) (w + z).1).1
          (Z.add_mem w.2 z.2))
    map_smul' := fun a w => zeroVelEtaLp_smul hm a w.1
        ((mem_zeroCirculationSubmodule_iff (by linarith : 1 / 2 < m) w.1).1 w.2)
        ((mem_zeroCirculationSubmodule_iff (by linarith : 1 / 2 < m) (a • w).1).1
          (Z.smul_mem a w.2)) }
  refine L.mkContinuous 1 ?_
  intro w
  have hcirc := (mem_zeroCirculationSubmodule_iff (by linarith : 1 / 2 < m) w.1).1 w.2
  calc ‖L w‖ = ‖B0583.zeroVelEtaLp c hm w.1 hcirc‖ := rfl
    _ ≤ ‖w.1‖ := B0583.norm_zeroVelEtaLp_le c hm w.1 hcirc
    _ = 1 * ‖w‖ := by rw [one_mul]; rfl

theorem continuous_kcGQ {c m : ℝ} [Fact (1 < m)] [Fact (0 < c)] :
    Continuous (fun ξ : Xmc c m => kcGQ ξ) := by
  unfold kcGQ B0583.velGradQ
  have hX : Continuous (fun ξ : Xmc c m =>
      B0581.ofX c m (zero_le_one.trans one_le_of_fact) (reX ξ.1)) :=
    (UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.complexifyXCLM c m
      (zero_le_one.trans one_le_of_fact)).continuous.comp
      (continuous_reX.comp continuous_subtype_val)
  exact (UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.realPartVelocityCLM.compLpL 2
    (B0581.cellVol c)).continuous.comp
    ((B0583.gradQ c).continuous.comp (continuous_nonzeroPart.comp hX))

theorem continuous_kcGE {c m : ℝ} [Fact (1 < m)] [Fact (0 < c)] :
    Continuous (fun ξ : Xmc c m => kcGE ξ) := by
  unfold kcGE B0583.velGradEta
  have hX : Continuous (fun ξ : Xmc c m =>
      B0581.ofX c m (zero_le_one.trans one_le_of_fact) (reX ξ.1)) :=
    (UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.complexifyXCLM c m
      (zero_le_one.trans one_le_of_fact)).continuous.comp
      (continuous_reX.comp continuous_subtype_val)
  have hZ : Continuous (fun ξ : Xmc c m =>
      B0583.zeroVelEtaLp c one_le_of_fact (reX ξ.1) (reX_circ ξ)) :=
    (zeroVelEtaCLM (c := c) (m := m) one_le_of_fact).continuous.comp continuous_kcZ
  exact (UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.realPartVelocityCLM.compLpL 2
    (B0581.cellVol c)).continuous.comp
    (((B0583.gradEta c).continuous.comp (continuous_nonzeroPart.comp hX)).add hZ)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
