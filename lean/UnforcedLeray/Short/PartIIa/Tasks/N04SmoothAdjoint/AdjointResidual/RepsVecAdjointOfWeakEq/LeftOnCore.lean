import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N04_3_3_Org
import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointResidual.RepsVecAdjointOfWeakEq.OuterSGenPair.Core

/-!
# `RepsVecLeftOnCore` (task `PartII-a:N04/3/3/3`)

Source of record: `the November 2 reference manuscript`,
lines 3343–3363 (the outer semigroup `S_ε`, its generator and `R_ε^vec(μ) = J*(μ - A)^{-1}J`) and
1842–1845 (the identity `(μ̄ - A_ε^*)w = …` is tested against core tests).

Left inverse on axis-reaching core tests: for `IsMeridCoreTest ε c u`, the real and imaginary
lifts of `u` agree off the axis (a null set) with `C²` axis-reaching vector test fields `V`, on
which `outerSIsGenPairOnCoreTestFieldVec` gives the generator pair; off the axis the outer operator
of `V` is that of `fieldU ε b` (it is local), i.e. `fieldU ε (A_ε^vec b)` (`B0222.outerGenVec_fieldU`).
Hence `(J U, J A_ε^vec U)` is a generator pair and `B0223.RepsVec_left` applies (the axis-reaching
analogue of `repsVec_left_of_outerS`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0221 UnforcedLeray.B0222
open UnforcedLeray.B0223 UnforcedLeray.B0226
open UnforcedLeray.Short.PartIIIb.NearInst (merC)
open UnforcedLeray.Short.PartIIIb.NearInst.Masked
open UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

/-! ### Locality of the Cartesian outer operator -/

theorem outerGen_congr {ν ε : ℝ} {f g : Space × ℝ → ℝ} {y : Space × ℝ} (h : f =ᶠ[𝓝 y] g) :
    B0221.outerGen ν ε f y = B0221.outerGen ν ε g y := by
  obtain ⟨x, τ⟩ := y
  have hsl : (fun x' : Space => f (x', τ)) =ᶠ[𝓝 x] fun x' => g (x', τ) :=
    h.comp_tendsto ((continuous_id.prodMk continuous_const).tendsto x)
  have hsl' : (fun σ : ℝ => f (x, σ)) =ᶠ[𝓝 τ] fun σ => g (x, σ) :=
    h.comp_tendsto ((continuous_const.prodMk continuous_id).tendsto τ)
  have hD : fderiv ℝ (fun x' : Space => f (x', τ)) =ᶠ[𝓝 x]
      fderiv ℝ (fun x' : Space => g (x', τ)) := hsl.fderiv
  have e1 : B0221.spatialLap f (x, τ) = B0221.spatialLap g (x, τ) := by
    show ∑ i : Fin 3, fderiv ℝ (fun x₁ : Space => fderiv ℝ (fun x' : Space => f (x', τ)) x₁
        (UnforcedLeray.coordinateVector i)) x (UnforcedLeray.coordinateVector i) =
      ∑ i : Fin 3, fderiv ℝ (fun x₁ : Space => fderiv ℝ (fun x' : Space => g (x', τ)) x₁
        (UnforcedLeray.coordinateVector i)) x (UnforcedLeray.coordinateVector i)
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : (fun x₁ : Space => fderiv ℝ (fun x' : Space => f (x', τ)) x₁
        (UnforcedLeray.coordinateVector i)) =ᶠ[𝓝 x]
        (fun x₁ : Space => fderiv ℝ (fun x' : Space => g (x', τ)) x₁
          (UnforcedLeray.coordinateVector i)) :=
      hD.mono fun x₁ hx₁ => by simp only [hx₁]
    rw [hi.fderiv_eq]
  have e2 : ∀ i : Fin 3, B0221.spatialPartial f i (x, τ) = B0221.spatialPartial g i (x, τ) := by
    intro i
    show fderiv ℝ (fun x' : Space => f (x', τ)) x (UnforcedLeray.coordinateVector i) =
      fderiv ℝ (fun x' : Space => g (x', τ)) x (UnforcedLeray.coordinateVector i)
    rw [hsl.fderiv_eq]
  have e3 : B0221.timePartial f (x, τ) = B0221.timePartial g (x, τ) := by
    show deriv (fun σ : ℝ => f (x, σ)) τ = deriv (fun σ : ℝ => g (x, σ)) τ
    rw [hsl'.deriv_eq]
  have e4 : f (x, τ) = g (x, τ) := h.eq_of_nhds
  simp only [B0221.outerGen, e1, e2, e3, e4]

theorem outerGenVec_congr {ν ε : ℝ} {V U : Space × ℝ → Space} {y : Space × ℝ}
    (h : V =ᶠ[𝓝 y] U) : B0222.outerGenVec ν ε V y = B0222.outerGenVec ν ε U y := by
  ext j
  simp only [B0222.outerGenVec, PiLp.toLp_apply]
  exact outerGen_congr (h.fun_comp fun v : Space => v j)

/-! ### Generator pairs of the lifts of core tests -/

/-- For a real profile `b`, smooth for `s > 0` and `c`-periodic in `q`, whose lift agrees off the
axis with an axis-reaching vector test field, the complexified lifts of `b` and `A_ε^vec b` form a
generator pair for `B0223.outerS hν ε`. -/
theorem isGenPair_liftVec_cplxH_of_core
    {ν c ε P : ℝ} [Fact (0 < P)] (hν : 0 < ν) (hc : 0 < c) (hε : 0 < ε)
    (hP : P = 2 * ε * c) {b : Profile → Merid}
    (hb : ContDiffOn ℝ ∞ b {p : Profile | 0 < p.1}) (hper : QPeriodic c b)
    {V : Space × ℝ → Space} (hV : IsCoreTestFieldVec ε c V)
    (hVb : ∀ y : Space × ℝ, B0220.radius y.1 ≠ 0 → V y = B0220.fieldU ε b y)
    {bL Ab : HSpace c Merid}
    (hbL : (bL : Profile → Merid) =ᵐ[measureH c] b)
    (hAb : (Ab : Profile → Merid) =ᵐ[measureH c] B0222.AepsVec ν ε b) :
    B0223.IsGenPair (B0223.outerS hν ε)
      (B0223.liftVec hε hc hP (cplxH c bL))
      (B0223.liftVec hε hc hP (cplxH c Ab)) := by
  set k := B0220.jConst ε with hk_def
  have hk : k ≠ 0 := B0221.jConst_ne_zero hε
  have hJb := J_ae_of_periodic hε hc hper bL hbL
  have hJA := J_ae_of_periodic hε hc (qPeriodic_AepsVec ν ε hper) Ab hAb
  set W : B0220.PhysL2 ε c := k⁻¹ • B0220.J hε hc bL with hW_def
  set GW : B0220.PhysL2 ε c := k⁻¹ • B0220.J hε hc Ab with hGW_def
  have hopen : IsOpen {y : Space × ℝ | B0220.radius y.1 ≠ 0} :=
    isOpen_ne_fun (B0220.continuous_radius.comp continuous_fst) continuous_const
  have hopenS : IsOpen {p : Profile | 0 < p.1} := isOpen_lt continuous_const continuous_fst
  have hloc : ∀ y : Space × ℝ, B0220.radius y.1 ≠ 0 →
      B0222.outerGenVec ν ε V y = B0220.fieldU ε (B0222.AepsVec ν ε b) y := by
    intro y hy
    have hev : V =ᶠ[𝓝 y] B0220.fieldU ε b :=
      Filter.eventually_of_mem (hopen.mem_nhds hy) fun y' hy' => hVb y' hy'
    rw [outerGenVec_congr hev]
    obtain ⟨x, τ⟩ := y
    have hr : 0 < B0220.radius x := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hy)
    have hpos : 0 < (B0220.chart ε (x, τ)).1 := by
      rw [B0220.chart_fst]
      exact pow_pos (inv_pos.2 hr) 2
    have hbat : ContDiffAt ℝ 2 b (B0220.chart ε (x, τ)) :=
      (hb.contDiffAt (hopenS.mem_nhds hpos)).of_le (by simp)
    exact B0222.outerGenVec_fieldU hε.ne' hy hbat
  have hW : (W : Space × ℝ → Space) =ᵐ[B0220.physMeasure ε c] V := by
    filter_upwards [Lp.coeFn_smul k⁻¹ (B0220.J hε hc bL), hJb, B0220.ae_physMeasure ε c] with
      y h1 h2 h3
    rw [h1, Pi.smul_apply, h2, smul_smul, inv_mul_cancel₀ hk, one_smul, hVb y h3.1]
  have hGW : (GW : Space × ℝ → Space) =ᵐ[B0220.physMeasure ε c] B0222.outerGenVec ν ε V := by
    filter_upwards [Lp.coeFn_smul k⁻¹ (B0220.J hε hc Ab), hJA, B0220.ae_physMeasure ε c] with
      y h1 h2 h3
    rw [h1, Pi.smul_apply, h2, smul_smul, inv_mul_cancel₀ hk, one_smul, hloc y h3.1]
  have hgenW := outerSIsGenPairOnCoreTestFieldVec ν c ε hν hc hε P hP V hV W GW hW hGW
  have hgenk := isGenPair_smul hν (k : ℂ) hgenW
  have hJW : B0220.J hε hc bL = k • W := by
    rw [hW_def, smul_smul, mul_inv_cancel₀ hk, one_smul]
  have hJGW : B0220.J hε hc Ab = k • GW := by
    rw [hGW_def, smul_smul, mul_inv_cancel₀ hk, one_smul]
  have hJ1 : (k : ℂ) • toX hP W = B0223.liftVec hε hc hP (cplxH c bL) := by
    rw [liftVecCplx ε c P hε hc hP bL, hJW, (toX hP).map_smul k W, Complex.coe_smul]
    rfl
  have hJ2 : (k : ℂ) • toX hP GW = B0223.liftVec hε hc hP (cplxH c Ab) := by
    rw [liftVecCplx ε c P hε hc hP Ab, hJGW, (toX hP).map_smul k GW, Complex.coe_smul]
    rfl
  rwa [hJ1, hJ2] at hgenk

/-- For a complex core test `IsMeridCoreTest ε c u` with `U =ᵐ u` and `AεU =ᵐ AepsVecC ν ε u`,
the lifted pair `(liftVec U, liftVec AεU)` is in the generator graph of `B0223.outerS hν ε`. -/
theorem isGenPair_liftVec_isMeridCoreTest
    {ν c ε P : ℝ} [Fact (0 < P)] (hν : 0 < ν) (hc : 0 < c) (hε : 0 < ε)
    (hP : P = 2 * ε * c) {u : Profile → MeridC} {U AεU : HSpace c MeridC}
    (hu : IsMeridCoreTest ε c u)
    (hU : (U : Profile → MeridC) =ᵐ[measureH c] u)
    (hAεU : (AεU : Profile → MeridC) =ᵐ[measureH c] AepsVecC ν ε u) :
    B0223.IsGenPair (B0223.outerS hν ε)
      (B0223.liftVec hε hc hP U)
      (B0223.liftVec hε hc hP AεU) := by
  obtain ⟨Vr, hVr, hVr_eq⟩ := hu.re_core
  obtain ⟨Vi, hVi, hVi_eq⟩ := hu.im_core
  have hopenS : IsOpen {p : Profile | 0 < p.1} := isOpen_lt continuous_const continuous_fst
  have hRe_smooth : ContDiffOn ℝ ∞ (reMerid u) {p : Profile | 0 < p.1} :=
    merReL.contDiff.comp_contDiffOn hu.smooth
  have hIm_smooth : ContDiffOn ℝ ∞ (imMerid u) {p : Profile | 0 < p.1} :=
    merReL.contDiff.comp_contDiffOn (hu.smooth.const_smul (-Complex.I))
  have hRe_per : QPeriodic c (reMerid u) := fun p => by simp [reMerid, hu.periodic p]
  have hIm_per : QPeriodic c (imMerid u) := fun p => by simp [imMerid, hu.periodic p]
  have hU_re : (reHC c U : Profile → Merid) =ᵐ[measureH c] reMerid u := by
    filter_upwards [reHC_ae c U, hU] with p hp1 hp2
    rw [hp1, hp2]
    rfl
  have hU_im : (reHC c ((-Complex.I) • U) : Profile → Merid) =ᵐ[measureH c] imMerid u := by
    filter_upwards [reHC_ae c ((-Complex.I) • U), Lp.coeFn_smul (-Complex.I) U, hU] with
      p hp1 hp2 hp3
    rw [hp1, hp2, Pi.smul_apply, hp3]
    rfl
  have hA_re : (reHC c AεU : Profile → Merid) =ᵐ[measureH c] B0222.AepsVec ν ε (reMerid u) := by
    filter_upwards [reHC_ae c AεU, hAεU, B0220.ae_cell_measureH c] with p hp1 hp2 hp3
    have hpos : 0 < p.1 := hp3.1
    rw [hp1, hp2, merReL_AepsVecC ν ε
      ((hu.smooth.contDiffAt (hopenS.mem_nhds hpos)).of_le (by simp))]
  have hA_im : (reHC c ((-Complex.I) • AεU) : Profile → Merid) =ᵐ[measureH c]
      B0222.AepsVec ν ε (imMerid u) := by
    filter_upwards [reHC_ae c ((-Complex.I) • AεU), Lp.coeFn_smul (-Complex.I) AεU, hAεU,
      B0220.ae_cell_measureH c] with p hp1 hp2 hp3 hp4
    have hpos : 0 < p.1 := hp4.1
    rw [hp1, hp2, Pi.smul_apply, hp3, merIm_AepsVecC ν ε
      ((hu.smooth.contDiffAt (hopenS.mem_nhds hpos)).of_le (by simp))]
  have hgenRe := isGenPair_liftVec_cplxH_of_core hν hc hε hP hRe_smooth hRe_per hVr hVr_eq
    hU_re hA_re
  have hgenIm := isGenPair_liftVec_cplxH_of_core hν hc hε hP hIm_smooth hIm_per hVi hVi_eq
    hU_im hA_im
  have hgen := isGenPair_add hν hgenRe (isGenPair_smul hν Complex.I hgenIm)
  have hU_decomp : B0223.liftVec hε hc hP (cplxH c (reHC c U)) +
      Complex.I • B0223.liftVec hε hc hP (cplxH c (reHC c ((-Complex.I) • U))) =
      B0223.liftVec hε hc hP U := by
    rw [← map_smul, ← map_add, cplxH_reHC_add_im c U]
  have hA_decomp : B0223.liftVec hε hc hP (cplxH c (reHC c AεU)) +
      Complex.I • B0223.liftVec hε hc hP (cplxH c (reHC c ((-Complex.I) • AεU))) =
      B0223.liftVec hε hc hP AεU := by
    rw [← map_smul, ← map_add, cplxH_reHC_add_im c AεU]
  rwa [hU_decomp, hA_decomp] at hgen

/-- **`RepsVecLeftOnCore`**: `R_ε^vec(μ)((μ - A_ε^vec)u) = u` on axis-reaching core tests. -/
theorem repsVecLeftOnCore : RepsVecLeftOnCore := by
  intro ν c ε hν hc hε _hε1 P _ hP _hP1 μ hγ u U AUε hu hU hAUε
  have hAεU : ((μ • U - AUε : HSpace c MeridC) : Profile → MeridC) =ᵐ[measureH c]
      AepsVecC ν ε u := by
    filter_upwards [Lp.coeFn_sub (μ • U) AUε, Lp.coeFn_smul μ U, hU, hAUε] with p h1 h2 h3 h4
    rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3, h4]
    exact sub_sub_cancel _ _
  have key := B0223.RepsVec_left hν hε hc hP hγ
    (isGenPair_liftVec_isMeridCoreTest hν hc hε hP hu hU hAεU)
  rwa [sub_sub_cancel] at key

end UnforcedLeray.Short.PartIIa
