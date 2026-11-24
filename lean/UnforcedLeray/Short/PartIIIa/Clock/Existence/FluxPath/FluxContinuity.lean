import UnforcedLeray.Short.PartIIIa.Sub.T21_3_TrainBounds
import UnforcedLeray.Short.PartIIIa.Clock.Existence.FluxPath.FluxContinuity.JointEc
import UnforcedLeray.Short.PartIIIa.Clock.Existence.FluxPath.FluxContinuity.MulDCT

/-!
# Part III-a, `PartIII-a:T21/3/1/1`: strong continuity of the clamped actual flux

Source of record: `the November 2 reference manuscript` lines 2819-2836
(`B(t)ω = vω + E K_cω` is a strongly continuous bounded perturbation).  On `[0, T]` the
coefficients are jointly continuous (`jointContinuousOn_Ec`, `smooth_v`) and bounded
(`hV`, `hE`); each flux component is `v_i w + E (K_i w)`, so continuity in the age follows from
dominated convergence (`tendsto_eLpNorm_mul_sub`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution
open UnforcedLeray.B0579 hiding Plane
open UnforcedLeray.B0581 (cellVol)

theorem fluxContinuityOn : UnforcedLeray.Short.IIIa.Exist.FluxContinuityOn := by
  intro ν c m _ hm tr T hT Cv CE hCv hCE hV hE w
  have hSv : ContinuousOn (fun p : ℝ × UnforcedLeray.Cyl.Plane => tr.v p.1 p.2)
      (Set.Ici 0 ×ˢ Set.univ) := tr.isTrain.smooth_v.continuousOn
  have hSe := jointContinuousOn_Ec tr
  -- continuity in the age of the coefficients at fixed `x`
  have hvc : ∀ x : UnforcedLeray.Cyl.Plane, ∀ i : Fin 2,
      Continuous (fun s : Icc (0 : ℝ) T => UnforcedLeray.B0238.Vc tr s.1 x i) := by
    intro x i
    have h1 : Continuous (fun s : Icc (0 : ℝ) T => tr.v s.1 x) :=
      hSv.comp_continuous (f := fun s : Icc (0 : ℝ) T => (s.1, x)) (by fun_prop)
        (fun s => ⟨s.2.1, mem_univ _⟩)
    exact (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) i).comp h1
  have hec : ∀ x : UnforcedLeray.Cyl.Plane,
      Continuous (fun s : Icc (0 : ℝ) T => UnforcedLeray.B0238.Ec tr s.1 x) :=
    fun x => hSe.comp_continuous (f := fun s : Icc (0 : ℝ) T => (s.1, x)) (by fun_prop)
      (fun s => ⟨s.2.1, mem_univ _⟩)
  -- the flux on the subtype `Icc 0 T`
  suffices hΦ : Continuous (fun s : Icc (0 : ℝ) T =>
      actualTrainFluxAtNonneg (s := s.1) hm tr s.2.1 hCv hCE (hV s) (hE s) w) from
    hΦ.comp (by
      have : Continuous (fun t : ℝ => max 0 (min T t)) := by fun_prop
      exact Continuous.subtype_mk this _)
  refine continuous_pi fun i => ?_
  -- unfold the component
  have hcomp : ∀ s : Icc (0 : ℝ) T,
      actualTrainFluxAtNonneg (s := s.1) hm tr s.2.1 hCv hCE (hV s) (hE s) w i =
      mulRCell c m (fun x => UnforcedLeray.B0238.Vc tr s.1 x i)
          (by have := continuous_actualTrainVelocity_slice tr s.2.1; fun_prop) hCv
          (fun x _ => hV s x i) w.1 +
        weightedCellMultiplier (UnforcedLeray.B0238.Ec tr s.1)
          (continuous_actualTrainCurl_slice tr s.2.1) hCE (hE s)
          (((trainVecComponentCLM i).compLpL 2 (cellVol c)).comp (realBiotSavartKernelCLM hm) w) :=
    fun s => rfl
  simp_rw [hcomp]
  refine Continuous.add ?_ ?_
  · -- velocity part, in `L²(cellMeasure c m)`
    refine continuous_iff_continuousAt.2 fun s0 => ?_
    refine (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).2 ?_
    have hlim := tendsto_eLpNorm_mul_sub (μ := cellMeasure c m) (l := 𝓝 s0)
      (h := ⇑(w.1 : X c m)) (Lp.memLp _)
      (fun s x => UnforcedLeray.B0238.Vc tr s.1 x i) (fun x => UnforcedLeray.B0238.Vc tr s0.1 x i)
      (C := Cv)
      (fun s => (by have := continuous_actualTrainVelocity_slice tr s.2.1;
                    exact (by fun_prop : Continuous fun x => UnforcedLeray.B0238.Vc tr s.1 x i)
                      |>.aestronglyMeasurable))
      ((by have := continuous_actualTrainVelocity_slice tr s0.2.1;
           exact (by fun_prop : Continuous fun x => UnforcedLeray.B0238.Vc tr s0.1 x i)
             |>.aestronglyMeasurable))
      (Eventually.of_forall fun s => Eventually.of_forall fun x => hV s x i)
      (Eventually.of_forall fun x => hV s0 x i)
      (Eventually.of_forall fun x => ((hvc x i).tendsto s0))
    refine hlim.congr fun s => ?_
    refine eLpNorm_congr_ae ?_
    filter_upwards [coeFn_mulRCell (by have := continuous_actualTrainVelocity_slice tr s.2.1; fun_prop)
          hCv (fun x _ => hV s x i) w.1,
      coeFn_mulRCell (by have := continuous_actualTrainVelocity_slice tr s0.2.1; fun_prop) hCv
          (fun x _ => hV s0 x i) w.1] with x h2 h3
    simp only [Pi.sub_apply]
    rw [h2, h3]
  · -- curl part, in `L²(cellVol c)` with weight `⟨x⟩^m`
    refine continuous_iff_continuousAt.2 fun s0 => ?_
    refine (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).2 ?_
    set K0 : Lp ℝ 2 (cellVol c) :=
      ((trainVecComponentCLM i).compLpL 2 (cellVol c)).comp (realBiotSavartKernelCLM hm) w with hK0
    have hM : ∀ s : Icc (0 : ℝ) T,
        ⇑(weightedCellMultiplier (UnforcedLeray.B0238.Ec tr s.1)
          (continuous_actualTrainCurl_slice tr s.2.1) hCE (hE s) K0) =ᵐ[cellMeasure c m]
        fun x => UnforcedLeray.B0238.Ec tr s.1 x * K0 x := by
      intro s
      rw [weightedCellMultiplier_eq_mul]
      exact MemLp.coeFn_toLp _
    have hmeas : ∀ s : Icc (0 : ℝ) T, AEStronglyMeasurable
        (fun x => bracket x ^ m * UnforcedLeray.B0238.Ec tr s.1 x) (cellVol c) := fun s =>
      ((continuous_bracket_rpow m).mul
        (continuous_actualTrainCurl_slice tr s.2.1)).aestronglyMeasurable
    have hbd : ∀ s : Icc (0 : ℝ) T, ∀ᵐ x ∂(cellVol c),
        |bracket x ^ m * UnforcedLeray.B0238.Ec tr s.1 x| ≤ CE := fun s =>
      ae_restrict_of_forall_mem (measurableSet_cell c) fun x hx => hE s x hx
    have hlim := tendsto_eLpNorm_mul_sub (μ := cellVol c) (l := 𝓝 s0) (h := ⇑K0) (Lp.memLp K0)
      (fun s x => bracket x ^ m * UnforcedLeray.B0238.Ec tr s.1 x)
      (fun x => bracket x ^ m * UnforcedLeray.B0238.Ec tr s0.1 x) (C := CE)
      hmeas (hmeas s0) (Eventually.of_forall hbd) (hbd s0)
      (Eventually.of_forall fun x => (continuous_const.mul (hec x)).tendsto s0)
    refine hlim.congr fun s => ?_
    symm
    beta_reduce
    refine (eLpNorm_congr_ae ((hM s).sub (hM s0))).trans ?_
    rw [eLpNorm_cellMeasure]
    congr 1
    funext x
    simp only [Pi.sub_apply, bracket_rpow]
    ring

end UnforcedLeray.Short.IIIa.Exist
