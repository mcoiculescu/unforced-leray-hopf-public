import UnforcedLeray.Units.B0419
import UnforcedLeray.Lib.LerayLp.Duality
import UnforcedLeray.Analysis.Heat.Solenoidal
import UnforcedLeray.Analysis.ViscosityTransport.L2Dilation
import UnforcedLeray.Analysis.DerivativeScaling

/-!
# B0420 helper: the free semigroup `S_0(t)` commutes with the Leray projection

Blueprint unit B0420 (`background:eq:2.18`, `paper/main.tex` lines 5207--5216): the free
semigroup `S_0(t)f(y) = e^{t/2}[e^{ν(e^t-1)Δ}f](e^{t/2}y)` "from Section `sec:free-stress`"
is used on solenoidal data together with the Leray projection `𝔓` (`G_0 f = ∫ S_0(t) 𝔓 f`,
eq. (2.19), unit B0422). The manuscript's reason (tex lines 7336--7344, unit B0414 (iii)--(iv)):
the multiplier of `𝔓` is homogeneous of degree zero, so `𝔓` commutes with spatial dilations and
with the heat semigroup.

The proof here uses no Fourier multiplier (bypass BP2 of


* on `L²`, the orthogonal Leray projection `Leray.projection` commutes with every dilation
  `f ↦ a f(b·)`, `b > 0`, because the dilation and its adjoint `f ↦ a b^{-3} f(b^{-1}·)` both
  preserve distributional solenoidality (`DerivativeScaling.isSolenoidal_spatialScale`), so the
  dilation preserves the solenoidal subspace and its orthogonal complement
  (`projection_dilationL2`); it commutes with the heat semigroup by the library's
  `Heat.projection_heatOperator` (translation invariance through the Bochner convolution);
* on `L^p`, `1 < p < ∞`, the Leray projection is the drafted `RieszLp.lerayLp`

  `Leray.projection` on `L² ∩ L^p` (`RieszLp.lerayLp_ae_eq_projection`); `L² ∩ L^p` is dense in
  `L^p` (`RieszLp.dense_memLp_two_vec`) and both sides are bounded, so the `L²` identity
  extends (`lerayLp_comp_freeSemigroupLp`).

`S_0(t)` is the B0418 operator `B0418.freeSemigroupLp hp ν t` (literal formula
`AncientLocalization.freeEvolution ν t`), reused, not redefined.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace UnforcedLeray.B0420

open UnforcedLeray.AncientLocalization UnforcedLeray.B0418

/-! ### `L²`: the orthogonal Leray projection commutes with dilations -/

/-- A dilation `f ↦ a f(b·)`, `b > 0`, of a distributionally solenoidal `L²` class is
solenoidal. -/
theorem dilationL2_solenoidal (a : ℝ) {b : ℝ} (hb : 0 < b) {F : L2Space}
    (hF : IsSolenoidal (F : SpatialField)) :
    IsSolenoidal (ViscosityTransport.dilationL2 a b F : SpatialField) := by
  have hm := SpatialScaling.memLp_spatialScale (Lp.memLp F) a hb.ne'
  refine Leray.solenoidal_congr_ae
    (DerivativeScaling.isSolenoidal_spatialScale hF a hb.ne') ?_
  exact (coeFn_toL2 hm).symm

/-- The dilation `f ↦ a f(b·)`, `b > 0`, maps the orthogonal complement of the solenoidal
subspace into itself: its `L²` adjoint is the dilation `f ↦ a b^{-3} f(b^{-1}·)`, which
preserves solenoidality. -/
theorem dilationL2_mem_orthogonal (a : ℝ) {b : ℝ} (hb : 0 < b) {F : L2Space}
    (hF : F ∈ Leray.solenoidalSubspaceᗮ) :
    ViscosityTransport.dilationL2 a b F ∈ Leray.solenoidalSubspaceᗮ := by
  rw [Submodule.mem_orthogonal]
  intro G hG
  have hGs : IsSolenoidal (G : SpatialField) := (Leray.mem_solenoidalSubspace_iff G).mp hG
  have hbi : 0 < b⁻¹ := inv_pos.mpr hb
  have hG' : ViscosityTransport.dilationL2 a b⁻¹ G ∈ Leray.solenoidalSubspace :=
    (Leray.mem_solenoidalSubspace_iff _).mpr (dilationL2_solenoidal a hbi hGs)
  have h0 : inner ℝ (ViscosityTransport.dilationL2 a b⁻¹ G) F = 0 :=
    Submodule.inner_right_of_mem_orthogonal hG' hF
  have hmF := SpatialScaling.memLp_spatialScale (Lp.memLp F) a hb.ne'
  have hmG := SpatialScaling.memLp_spatialScale (Lp.memLp G) a hbi.ne'
  have e1 : inner ℝ G (ViscosityTransport.dilationL2 a b F) =
      ∫ x, inner ℝ ((G : SpatialField) x) (a • (F : SpatialField) (b • x)) := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_toL2 hmF] with x hx
    change inner ℝ ((G : SpatialField) x)
      ((toL2 (SpatialScaling.spatialScale a b (F : SpatialField)) : SpatialField) x) = _
    rw [hx]
    rfl
  have e2 : inner ℝ (ViscosityTransport.dilationL2 a b⁻¹ G) F =
      ∫ y, inner ℝ (a • (G : SpatialField) (b⁻¹ • y)) ((F : SpatialField) y) := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_toL2 hmG] with x hx
    change inner ℝ ((toL2 (SpatialScaling.spatialScale a b⁻¹ (G : SpatialField)) :
      SpatialField) x) ((F : SpatialField) x) = _
    rw [hx]
    rfl
  have e3 : ∫ x, inner ℝ ((G : SpatialField) x) (a • (F : SpatialField) (b • x)) =
      |((b ^ Module.finrank ℝ Space)⁻¹)| •
        ∫ y, inner ℝ (a • (G : SpatialField) (b⁻¹ • y)) ((F : SpatialField) y) := by
    rw [← Measure.integral_comp_smul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [smul_smul, inv_mul_cancel₀ hb.ne', one_smul, real_inner_smul_left,
      real_inner_smul_right]
  rw [e1, e3, ← e2, h0, smul_zero]

/-- **The `L²` Leray projection commutes with dilations** `f ↦ a f(b·)`, `b > 0`
(B0414 (iii), tex lines 7342--7343: "homogeneous of degree zero, so it commutes with spatial
dilations"; proved without the Fourier multiplier). -/
theorem projection_dilationL2 (a : ℝ) {b : ℝ} (hb : 0 < b) (F : L2Space) :
    Leray.projection (ViscosityTransport.dilationL2 a b F) =
      ViscosityTransport.dilationL2 a b (Leray.projection F) := by
  apply Leray.projection_eq_of_orthogonal
  · exact dilationL2_solenoidal a hb (Leray.projection_solenoidal F)
  · have hsub : ViscosityTransport.dilationL2 a b F -
        ViscosityTransport.dilationL2 a b (Leray.projection F) =
        ViscosityTransport.dilationL2 a b (F - Leray.projection F) := by
      have hm1 := SpatialScaling.memLp_spatialScale (Lp.memLp F) a hb.ne'
      have hm2 := SpatialScaling.memLp_spatialScale (Lp.memLp (Leray.projection F)) a hb.ne'
      have hm3 := SpatialScaling.memLp_spatialScale (Lp.memLp (F - Leray.projection F)) a hb.ne'
      have hs := SpatialScaling.ae_eq_spatialScale (Lp.coeFn_sub F (Leray.projection F)) a
        hb.ne'
      apply Lp.ext
      filter_upwards [Lp.coeFn_sub (ViscosityTransport.dilationL2 a b F)
          (ViscosityTransport.dilationL2 a b (Leray.projection F)),
        coeFn_toL2 hm1, coeFn_toL2 hm2, coeFn_toL2 hm3, hs] with x e0 e1 e2 e3 e4
      change _ = (toL2 (SpatialScaling.spatialScale a b
        ((F - Leray.projection F : L2Space) : SpatialField)) : SpatialField) x
      rw [e0, e3, e4]
      change (toL2 (SpatialScaling.spatialScale a b (F : SpatialField)) : SpatialField) x -
        (toL2 (SpatialScaling.spatialScale a b ((Leray.projection F : L2Space) :
          SpatialField)) : SpatialField) x = _
      rw [e1, e2]
      simp only [SpatialScaling.spatialScale, Pi.sub_apply, smul_sub]
    rw [hsub]
    exact dilationL2_mem_orthogonal a hb (Leray.residual_mem_orthogonal F)

/-! ### `L²`: the Leray projection commutes with `S_0(t)` -/

/-- On `L²`, `S_0(t) = D_{e^{t/2}} ∘ e^{ν(e^t-1)Δ}` with the library heat operator
`Heat.heatOperator` and the library dilation `ViscosityTransport.dilationL2`. -/
theorem freeSemigroupLp_two_eq (ν t : ℝ) (G : L2Space) :
    freeSemigroupLp (p := 2) ENNReal.ofNat_ne_top ν t G =
      ViscosityTransport.dilationL2 (Real.exp (t / 2)) (Real.exp (t / 2))
        (Heat.heatOperator (ν * (Real.exp t - 1)) G) := by
  have hH : MemLp (Heat.heatOperator (ν * (Real.exp t - 1)) G : SpatialField) 2 volume :=
    Lp.memLp _
  have hm := SpatialScaling.memLp_spatialScale hH (Real.exp (t / 2)) (Real.exp_pos (t / 2)).ne'
  have hflow : Heat.flow (G : SpatialField) (ν * (Real.exp t - 1)) =ᵐ[volume]
      (Heat.heatOperator (ν * (Real.exp t - 1)) G : SpatialField) := by
    by_cases hθ : 0 < ν * (Real.exp t - 1)
    · rw [Heat.flow_pos _ hθ]
      exact (Heat.heatOperator_rep hθ G).symm
    · rw [Heat.flow_nonpos _ (not_lt.mp hθ), Heat.heatOperator_nonpos (not_lt.mp hθ)]
      rfl
  apply Lp.ext
  have e : freeEvolution ν t (G : SpatialField) =
      SpatialScaling.spatialScale (Real.exp (t / 2)) (Real.exp (t / 2))
        (Heat.flow (G : SpatialField) (ν * (Real.exp t - 1))) := rfl
  refine (coeFn_freeSemigroupLp _ ν t G).trans ?_
  rw [e]
  refine (SpatialScaling.ae_eq_spatialScale hflow _ (Real.exp_pos (t / 2)).ne').trans ?_
  exact (coeFn_toL2 hm).symm

/-- **`𝔓 S_0(t) = S_0(t) 𝔓` on `L²`** with the orthogonal Leray projection, every `ν`, `t`. -/
theorem projection_freeSemigroupLp_two (ν t : ℝ) (G : L2Space) :
    Leray.projection (freeSemigroupLp (p := 2) ENNReal.ofNat_ne_top ν t G) =
      freeSemigroupLp (p := 2) ENNReal.ofNat_ne_top ν t (Leray.projection G) := by
  rw [freeSemigroupLp_two_eq, freeSemigroupLp_two_eq, projection_dilationL2 _ (Real.exp_pos _),
    Heat.projection_heatOperator]

/-! ### `L^p`, `1 < p < ∞`: density extension -/

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- On `L² ∩ L^p`, `𝔓_p S_0(t) u = S_0(t) 𝔓_p u` (both sides reduce to the `L²` identity). -/
theorem lerayLp_freeSemigroupLp_of_memLp_two (hp1 : 1 < p) (hp : p ≠ ∞) (ν t : ℝ)
    (u : Lp Space p (volume : Measure Space)) (hu : MemLp u 2 volume) :
    RieszLp.lerayLp p hp1 hp (freeSemigroupLp hp ν t u) =
      freeSemigroupLp hp ν t (RieszLp.lerayLp p hp1 hp u) := by
  have hSu2 : MemLp (freeSemigroupLp hp ν t u : SpatialField) 2 volume :=
    (freeEvolution_memLp one_le_two ENNReal.ofNat_ne_top hu ν t).ae_eq
      (coeFn_freeSemigroupLp hp ν t u).symm
  have h1 := RieszLp.lerayLp_ae_eq_projection hp1 hp (freeSemigroupLp hp ν t u) hSu2
  have e2 : hSu2.toLp (freeSemigroupLp hp ν t u : SpatialField) =
      freeSemigroupLp (p := 2) ENNReal.ofNat_ne_top ν t (hu.toLp u) := by
    apply Lp.ext
    refine hSu2.coeFn_toLp.trans ?_
    refine (coeFn_freeSemigroupLp hp ν t u).trans ?_
    refine (freeEvolution_congr_ae hu.coeFn_toLp.symm ν t).trans ?_
    exact (coeFn_freeSemigroupLp _ ν t _).symm
  rw [e2, projection_freeSemigroupLp_two] at h1
  have h3 := RieszLp.lerayLp_ae_eq_projection hp1 hp u hu
  apply Lp.ext
  refine h1.trans ?_
  refine (coeFn_freeSemigroupLp _ ν t _).trans ?_
  refine (freeEvolution_congr_ae h3.symm ν t).trans ?_
  exact (coeFn_freeSemigroupLp hp ν t _).symm

/-- **`𝔓 S_0(t) = S_0(t) 𝔓` on `L^p(ℝ³; ℝ³)`, `1 < p < ∞`**, as bounded operators, for every
`ν` and `t`, with the drafted `L^p` Leray projection `RieszLp.lerayLp`. -/
theorem lerayLp_comp_freeSemigroupLp (hp1 : 1 < p) (hp : p ≠ ∞) (ν t : ℝ) :
    (RieszLp.lerayLp p hp1 hp).comp (freeSemigroupLp hp ν t) =
      (freeSemigroupLp hp ν t).comp (RieszLp.lerayLp p hp1 hp) := by
  have hD := RieszLp.dense_memLp_two_vec p hp
  have key := Continuous.ext_on hD
    ((RieszLp.lerayLp p hp1 hp).comp (freeSemigroupLp hp ν t)).continuous
    ((freeSemigroupLp hp ν t).comp (RieszLp.lerayLp p hp1 hp)).continuous
    (fun u hu => lerayLp_freeSemigroupLp_of_memLp_two hp1 hp ν t u hu)
  exact ContinuousLinearMap.coe_injective (DFunLike.coe_injective key)

end UnforcedLeray.B0420
