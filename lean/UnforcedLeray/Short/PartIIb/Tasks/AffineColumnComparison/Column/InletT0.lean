import UnforcedLeray.Short.PartIIb.Sub.G4_3_org
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletContDiff
import UnforcedLeray.Short.PartIIb.Tasks.DriftNvC.Smooth.SmoothPt.DriftOffAxis

/-!
# Part II-b, `PartII-b:G4/3/2`: the drift of the affine inlet in the chart (`InletT0Ptw`)

Source of record: `the November 2 reference manuscript` (SP) 1919, 2360-2366.
Off the axis the chain rule of `NvCDriftOffAxis` (proof in `DriftOffAxis.lean`) holds for every
differentiable profile, not only `NiceProf` ones: the proof uses only differentiability. We
reprove that general form (`drift_gen`) and apply it to the smooth complex profile
`cplx E`, `E = Σ α_i e_i` (`inletProfile` is `C^∞`, `InletContDiff` argument).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.InletT0

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412 UnforcedLeray.Short.IIb.DriftOff

/-- **The off-axis drift identity for an arbitrary differentiable profile** (the body of
`nvCDriftOffAxis_proof`, which uses only differentiability of `b`). -/
theorem drift_gen (R : ℝ) (hR : R ≠ 0) (b : CProf) (hbd : Differentiable ℝ b) (p : ℝ × Space)
    (hp : p.2 ∉ Axi.axis) :
    dτ (NvC R b) p - (1 / 2 : ℝ) • radialT (NvC R b) p =
      NvC R (fun x => x.1 • fderiv ℝ b x (cdir 0) + (1 / 2 : ℂ) • b x) p := by
  have hγ : HasDerivAt (offLine p) ((1 : ℝ), (-(1 / 2 : ℝ)) • p.2) 0 := by
    unfold offLine
    refine HasDerivAt.prodMk ?_ ?_
    · simpa using (hasDerivAt_id (0 : ℝ)).const_add p.1
    · have h1 : HasDerivAt (fun t : ℝ => Real.exp (-t / 2)) (-(1 / 2 : ℝ)) 0 := by
        have h := (((hasDerivAt_id (0 : ℝ)).neg).div_const 2).exp
        exact h.congr_deriv (by norm_num)
      exact h1.smul_const p.2
  have hγ0 : offLine p 0 = p := by simp [offLine]
  have hGd : HasFDerivAt (NvC R b)
      (fderiv ℝ (NvC R b) p) (offLine p 0) := by
    rw [hγ0]
    exact (nvC_diffAt hR hbd hp).hasFDerivAt
  have hline := hGd.comp_hasDerivAt (0 : ℝ) hγ
  have hder := hasDerivAt_nvC_offLine hR hbd hp
  have hkey := hline.unique hder
  have hlin : UnforcedLeray.PhaseSpace.dτ (NvC R b) p -
      (1 / 2 : ℝ) • UnforcedLeray.PhaseSpace.radialT (NvC R b) p =
      fderiv ℝ (NvC R b) p ((1 : ℝ), (-(1 / 2 : ℝ)) • p.2) := by
    have hy : ∑ j : Fin 3, p.2 j • UnforcedLeray.coordinateVector j = p.2 := by
      ext i
      fin_cases i <;> simp [UnforcedLeray.coordinateVector, Fin.sum_univ_three, EuclideanSpace.single_apply]
    have hsnd : ((0 : ℝ), p.2) = ∑ j : Fin 3, p.2 j • ((0 : ℝ), UnforcedLeray.coordinateVector j) := by
      refine Prod.ext ?_ ?_
      · simp [Prod.fst_sum]
      · rw [Prod.snd_sum]
        simp only [Prod.smul_snd]
        exact hy.symm
    have hv : ((1 : ℝ), (-(1 / 2 : ℝ)) • p.2) =
        ((1 : ℝ), (0 : UnforcedLeray.Space)) + (-(1 / 2 : ℝ)) • ((0 : ℝ), p.2) := by
      refine Prod.ext ?_ ?_ <;> simp
    simp only [UnforcedLeray.PhaseSpace.dτ, UnforcedLeray.PhaseSpace.radialT,
      UnforcedLeray.PhaseSpace.dy]
    rw [hv, map_add, map_smul, hsnd, map_sum]
    simp only [map_smul]
    module
  have hRHS : NvC R (fun x : ℝ × ℝ × ℝ => x.1 • fderiv ℝ b x (cdir 0) + (1 / 2 : ℂ) • b x) p =
      (√(Axi.age R p.2) * (1 / 2 : ℝ)) •
          pairL (realCL (Axi.eR p.2)) (realCL Axi.e3) (b (offCurve R p 0)) +
        √(Axi.age R p.2) •
          pairL (realCL (Axi.eR p.2)) (realCL Axi.e3)
            (fderiv ℝ b (offCurve R p 0) (Axi.age R p.2, ((0 : ℝ), (0 : ℝ)))) := by
    rw [offCurve_zero, nvC_rep, ← pairL_apply]
    have hc0 : (Axi.chart R p.1 p.2).1 = Axi.age R p.2 := rfl
    simp only [hc0, map_add, pairL_smul_real, pairL_half, cdir_zero_smul,
      ContinuousLinearMap.map_smul, smul_add, smul_smul]
    module
  rw [hlin, hkey, hRHS]

/-- Complex-linear-in-reals embedding of meridional vectors: `v ↦ (v_r, v_z) ∈ ℂ²`. -/
def mToC : Axi.Merid →L[ℝ] CMerid :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (fun i => ((v i : ℝ) : ℂ))
      map_add' := by
        intro u v
        ext i
        simp
      map_smul' := by
        intro c v
        ext i
        simp }

theorem mToC_apply (v : Axi.Merid) (i : Fin 2) : mToC v i = ((v i : ℝ) : ℂ) := by
  simp [mToC]

theorem cplx_eq_mToC (E : Coord → Axi.Merid) : cplx E = fun z => mToC (E z) := by
  funext z
  ext i
  simp [cplx, mToC_apply]

theorem cplx_hasFDerivAt {E : Coord → Axi.Merid} {L : Coord →L[ℝ] Axi.Merid} {x : Coord}
    (h : HasFDerivAt E L x) : HasFDerivAt (cplx E) (mToC.comp L) x := by
  rw [cplx_eq_mToC]
  exact mToC.hasFDerivAt.comp x h

/-- Real-linear combinations of real meridional fields lift to `ℂ`-combinations of the lifts. -/
theorem realC_lin (a b : ℝ) (u v : Space) :
    B0412.realC (a • u + b • v) = (a : ℂ) • B0412.realC u + (b : ℂ) • B0412.realC v := by
  ext j
  simp [B0412.realC_apply]

theorem reM_cplx (v : Axi.Merid) : reM (cplx (fun _ => v) (0 : Coord)) = v := by
  ext i
  simp [reM, cplx]

theorem nvC_half (R : ℝ) (b : CProf) (q : ℝ × Space) :
    NvC R (fun x => (1 / 2 : ℂ) • b x) q = (1 / 2 : ℝ) • NvC R b q := by
  rw [DriftOff.nvC_rep, DriftOff.nvC_rep]
  simp only [PiLp.smul_apply, smul_eq_mul, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  module

/-- The affine inlet `E_εα = N_v(Σα_i e_ε^{(i)})` as a real field on the chart. -/
def sumProf (p : Params) (α : E2) : Coord → Axi.Merid :=
  fun z => α 0 • p.inletProfile 0 z + α 1 • p.inletProfile 1 z

theorem inletC_eq (p : Params) (α : E2) :
    inletC p α = NvC p.R (cplx (sumProf p α)) := by
  funext x
  rcases x with ⟨τ, y⟩
  have h1 : (fun z => reM (cplx (sumProf p α) z)) = sumProf p α := by
    funext z
    ext j
    simp [reM, cplx]
  have h2 : (fun z => imM (cplx (sumProf p α) z)) = 0 := by
    funext z
    ext j
    simp [imM, cplx]
  have hsum : sumProf p α = α 0 • p.inletProfile 0 + α 1 • p.inletProfile 1 := rfl
  have hz : Axi.Nv p.R (0 : Coord → Axi.Merid) τ y = 0 := by
    simp [Axi.Nv]
  have hrz : B0412.realC (0 : Space) = 0 := by
    ext j
    simp [B0412.realC_apply]
  simp only [NvC, inletC, Fin.sum_univ_two, Params.Efun]
  rw [h1, h2, hz, hrz, smul_zero, add_zero, hsum, Axi.Nv_add, Axi.Nv_smul, Axi.Nv_smul,
    realC_lin]
  rfl

end UnforcedLeray.Short.IIb.InletT0

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint UnforcedLeray.Axi UnforcedLeray.Short.IIb.InletT0 UnforcedLeray.Short.IIb


/-- **Leaf `PartII-b:G4/3/2`** (`InletT0Ptw`, SP 1919, 2360-2366): off the axis,
`T₀(E_εα) - ½E_εα = N_v(s∂_s(Σα_i e_ε^{(i)}))`. -/
theorem inletT0Ptw : UnforcedLeray.Short.IIb.InletT0Ptw := by
  intro Sig lam q hSig hq dm dp hdm
  obtain ⟨C, κ, N, -, -, hper⟩ := frozenStreamBounds lam q hq 0
  refine ⟨1, one_pos, ?_⟩
  intro p d hreg hν hSig' hmode α τ y hy
  have hνpos : 0 < p.ν := p.ν_pos
  have hc1 : 1 ≤ p.c := by
    rw [hreg.c_eq, one_le_inv₀ (by positivity)]
    nlinarith
  have hP : ContDiff ℝ ∞ (periodicStream q p.c) := (hper p.c hc1).1
  have hfro : ∀ k : Fin 2, ContDiff ℝ ∞ (p.frozenStream k) :=
    fun k => inletCD_frozenStream hP hmode k
  have hH : 0 < p.H := div_pos p.ageCut_pos p.ν_pos
  have hBc : ∀ i : Fin 2, ContDiff ℝ ∞ (p.inletProfile i) := by
    intro i
    have hcut : ContDiff ℝ ∞ (p.cutStream i) := by
      unfold Params.cutStream
      exact ((contDiff_ageCutoff p.H).comp contDiff_fst).mul ((hfro i).comp contDiff_snd)
    unfold Params.inletProfile
    exact inletCD_ringStreamProfile hcut
  have hRne : p.R ≠ 0 := p.R_pos.ne'
  have hd : ∀ i : Fin 2, Differentiable ℝ (p.inletProfile i) :=
    fun i => (hBc i).differentiable (by simp)
  have hEd : ∀ z : Coord, HasFDerivAt (sumProf p α)
      (α 0 • fderiv ℝ (p.inletProfile 0) z + α 1 • fderiv ℝ (p.inletProfile 1) z) z :=
    fun z => (((hd 0 z).hasFDerivAt).const_smul (α 0)).add (((hd 1 z).hasFDerivAt).const_smul (α 1))
  have hb : ∀ z : Coord, HasFDerivAt (cplx (sumProf p α))
      (mToC.comp (α 0 • fderiv ℝ (p.inletProfile 0) z + α 1 • fderiv ℝ (p.inletProfile 1) z)) z :=
    fun z => cplx_hasFDerivAt (hEd z)
  have hbd : Differentiable ℝ (cplx (sumProf p α)) := fun z => (hb z).differentiableAt
  have hD : ∀ m : Coord, ∑ i : Fin 2, ((α i : ℝ) : ℂ) •
      cplx (fun x => x.1 • UnforcedLeray.Axi.dS (p.inletProfile i) x) m =
        m.1 • fderiv ℝ (cplx (sumProf p α)) m (cdir 0) := by
    intro m
    rw [(hb m).fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, Fin.sum_univ_two, UnforcedLeray.Axi.dS]
    have hc0 : cdir 0 = ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) := rfl
    rw [hc0]
    ext j
    simp [cplx, mToC_apply, Complex.real_smul]
    push_cast
    ring
  have hRHS : (fun m : Coord => ∑ i : Fin 2, ((α i : ℝ) : ℂ) •
      cplx (fun x => x.1 • UnforcedLeray.Axi.dS (p.inletProfile i) x) m) =
        fun m => m.1 • fderiv ℝ (cplx (sumProf p α)) m (cdir 0) :=
    funext hD
  rw [inletC_eq p α]
  unfold UnforcedLeray.B0411.T0
  rw [drift_gen p.R hRne (cplx (sumProf p α)) hbd (τ, y) hy, hRHS, NvC_add_apply, nvC_half]
  abel

#print axioms inletT0Ptw
