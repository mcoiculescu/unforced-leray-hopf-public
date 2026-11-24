import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N04.Defs

/-!
# Sub `PartII-a_N04_2`: Polynomial Observation-Box Adjoint Bounds (`AdjointPolynomialBound`)

Source of record: `the November 2 reference manuscript`,
lines 1800–1836 (Lemma `near:adjoint-polynomial`).

This file proves:
1. The `MeridC`-valued `Λ²` expansion (`opLam_opLam_eq`):
   `Λ² v = 4 S² v + 4 S(η ∂_η v) + 4 S v + η² ∂_η² v + 3 η ∂_η v + v`
   from `lambda_sq_expansion` (`PartII-a:N03`), and the resulting 6-term expansion
   `genDiff2_expand` of `genDiff2 ν v = ν s (Λ² v - E v)` on `{p : Profile | 0 < p.1}`.
2. `L²(measureH c)` membership and norm bound (`memLp_genDiff2_of_parts`, `norm_genDiff2_le_of_parts`)
   for `genDiff2 ν v` in terms of the six elementary `ν s`-weighted derivatives of `v`.
3. Reduction `adjointPolynomialBound_of` of `AdjointPolynomialBound` to two leaf propositions
   corresponding to the two stages of Lemma `near:adjoint-polynomial`:
   - `FlatLeraySmoothRep` (`PartII-a:N04/2/1`): smooth `c`-periodic band-supported representative `h`
     of `PepsC 0 c Z` with bounded and `measureH c`-integrable weighted moment derivatives and
     `flatProjMomentNorm c h ≤ C₁ * GammaBox^k₁ * h6Norm c z` (source lines 1800–1823).
   - `FlatAdjointElementaryBound` (`PartII-a:N04/2/2`): causal integral representation `v` of
     `T0flat.adjoint Z` from `h`, vanishing for `s > H₁`, with `L²` bounds on the elementary
     components of `genDiff1 ν v`, `genDiff2 ν v`, and `gradDiff1 v` via the age equations
     `S v = (μ̄ + 1/2 - ν s Δ_{q,η}) v - h` and `S² v` (source lines 1803–1836).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0221 UnforcedLeray.B0223

/-! ### 1. `MeridC`-valued `Λ²` expansion and `genDiff2` decomposition -/

private theorem clm_fderiv_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) {f : Profile → E} {p : Profile}
    (hf : DifferentiableAt ℝ f p) (v : Profile) :
    L (fderiv ℝ f p v) = fderiv ℝ (fun q => L (f q)) p v := by
  have h : HasFDerivAt (fun q => L (f q)) (L.comp (fderiv ℝ f p)) p :=
    L.hasFDerivAt.comp p hf.hasFDerivAt
  rw [h.fderiv]
  rfl

private theorem differentiableAt_fderiv_apply_of_contDiffAt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {u : Profile → E} {p : Profile}
    (hu : ContDiffAt ℝ 2 u p) (v : Profile) :
    DifferentiableAt ℝ (fun q => fderiv ℝ u q v) p := by
  have hD : DifferentiableAt ℝ (fderiv ℝ u) p :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact hD.clm_apply (differentiableAt_const v)

private theorem differentiableAt_opS_of_contDiffAt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {u : Profile → E} {p : Profile}
    (hu : ContDiffAt ℝ 2 u p) :
    DifferentiableAt ℝ (opS u) p := by
  have hS := differentiableAt_fderiv_apply_of_contDiffAt hu (1, 0, 0)
  have hfst : DifferentiableAt ℝ (fun q : Profile => q.1) p := differentiableAt_fst
  exact hfst.smul hS

private theorem differentiableAt_opK_of_contDiffAt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {u : Profile → E} {p : Profile}
    (hu : ContDiffAt ℝ 2 u p) :
    DifferentiableAt ℝ (opK u) p := by
  have hS := differentiableAt_opS_of_contDiffAt hu
  have hEta := differentiableAt_fderiv_apply_of_contDiffAt hu (0, 0, 1)
  have hsnd : DifferentiableAt ℝ (fun q : Profile => q.2.2) p :=
    differentiableAt_snd.comp p differentiableAt_snd
  exact (hS.const_smul (2 : ℝ)).add (hsnd.smul hEta)

private theorem differentiableAt_opLam_of_contDiffAt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {u : Profile → E} {p : Profile}
    (hu : ContDiffAt ℝ 2 u p) :
    DifferentiableAt ℝ (opLam u) p :=
  (differentiableAt_opK_of_contDiffAt hu).add (hu.differentiableAt (by norm_num))

private theorem clm_opS {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) {f : Profile → E} {p : Profile} (hf : DifferentiableAt ℝ f p) :
    L (opS f p) = B0221.opS (fun q => L (f q)) p := by
  simp only [opS, pdS, B0221.opS, B0221.dS, B0221.eS, map_smul, smul_eq_mul,
    clm_fderiv_apply L hf]

private theorem clm_opK {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) {f : Profile → E} {p : Profile} (hf : DifferentiableAt ℝ f p) :
    L (opK f p) = B0221.opK (fun q => L (f q)) p := by
  simp only [opK, opS, pdS, pdEta, B0221.opK, B0221.dS, B0221.dEta, B0221.eS, B0221.eEta,
    map_add, map_smul, smul_eq_mul, clm_fderiv_apply L hf]
  ring

private theorem clm_opLam {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) {f : Profile → E} {p : Profile} (hf : DifferentiableAt ℝ f p) :
    L (opLam f p) = B0221.opK (fun q => L (f q)) p + L (f p) := by
  simp only [opLam, map_add, clm_opK L hf]

private theorem clm_opLam_opLam {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) {u : Profile → E} {p : Profile} (hu : ContDiffAt ℝ 2 u p) :
    L (opLam (opLam u) p) =
      B0221.opK (fun q => B0221.opK (fun x => L (u x)) q + L (u q)) p +
        (B0221.opK (fun x => L (u x)) p + L (u p)) := by
  have hLam := differentiableAt_opLam_of_contDiffAt hu
  rw [clm_opLam L hLam]
  have hev : (fun q => L (opLam u q)) =ᶠ[nhds p]
      fun q => B0221.opK (fun x => L (u x)) q + L (u q) := by
    filter_upwards [hu.eventually (by simp)] with q hq
    exact clm_opLam L (hq.differentiableAt (by norm_num))
  simp only [B0221.opK, B0221.dS, B0221.dEta, hev.fderiv_eq, hev.self_of_nhds]

private theorem clm_opS_opS {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) {u : Profile → E} {p : Profile} (hu : ContDiffAt ℝ 2 u p) :
    L (opS (opS u) p) = B0221.opS (B0221.opS (fun q => L (u q))) p := by
  have hS := differentiableAt_opS_of_contDiffAt hu
  rw [clm_opS L hS]
  have hev : (fun q => L (opS u q)) =ᶠ[nhds p] B0221.opS (fun q => L (u q)) := by
    filter_upwards [hu.eventually (by simp)] with q hq
    exact clm_opS L (hq.differentiableAt (by norm_num))
  simp only [B0221.opS, B0221.dS, hev.fderiv_eq]

private theorem clm_opS_eta_pdEta {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) {u : Profile → E} {p : Profile} (hu : ContDiffAt ℝ 2 u p) :
    L (opS (fun q => q.2.2 • pdEta u q) p) =
      B0221.opS (fun q => q.2.2 * B0221.dEta (fun x => L (u x)) q) p := by
  have hsnd : DifferentiableAt ℝ (fun q : Profile => q.2.2) p :=
    differentiableAt_snd.comp p differentiableAt_snd
  have hEta : DifferentiableAt ℝ (fun q : Profile => q.2.2 • pdEta u q) p :=
    hsnd.smul (differentiableAt_fderiv_apply_of_contDiffAt hu (0, 0, 1))
  rw [clm_opS L hEta]
  have hev : (fun q : Profile => L (q.2.2 • pdEta u q)) =ᶠ[nhds p]
      fun q => q.2.2 * B0221.dEta (fun x => L (u x)) q := by
    filter_upwards [hu.eventually (by simp)] with q hq
    simp only [pdEta, B0221.dEta, B0221.eEta, map_smul, smul_eq_mul,
      clm_fderiv_apply L (hq.differentiableAt (by norm_num))]
  simp only [B0221.opS, B0221.dS, hev.fderiv_eq]

private theorem clm_pdEta_pdEta {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) {u : Profile → E} {p : Profile} (hu : ContDiffAt ℝ 2 u p) :
    L (pdEta (pdEta u) p) = B0221.dEta (B0221.dEta (fun q => L (u q))) p := by
  have hEta : DifferentiableAt ℝ (pdEta u) p :=
    differentiableAt_fderiv_apply_of_contDiffAt hu (0, 0, 1)
  change L (fderiv ℝ (pdEta u) p (0, 0, 1)) = B0221.dEta (B0221.dEta (fun q => L (u q))) p
  rw [clm_fderiv_apply L hEta]
  have hev : (fun q => L (pdEta u q)) =ᶠ[nhds p] B0221.dEta (fun q => L (u q)) := by
    filter_upwards [hu.eventually (by simp)] with q hq
    exact clm_fderiv_apply L (hq.differentiableAt (by norm_num)) (0, 0, 1)
  change fderiv ℝ (fun q => L (pdEta u q)) p B0221.eEta =
    fderiv ℝ (B0221.dEta (fun q => L (u q))) p B0221.eEta
  rw [hev.fderiv_eq]

/-- **Vector `Λ²` expansion** on `MeridC`-valued profiles (source line 1831):
`Λ² v = 4 S² v + 4 S(η ∂_η v) + 4 S v + η² ∂_η² v + 3 η ∂_η v + v` for `v` of class `C²` at `p`. -/
theorem opLam_opLam_eq {v : Profile → MeridC} {p : Profile} (hv : ContDiffAt ℝ 2 v p) :
    opLam (opLam v) p =
      (4 : ℝ) • opS (opS v) p + (4 : ℝ) • opS (fun q => q.2.2 • pdEta v q) p +
        (4 : ℝ) • opS v p + (p.2.2 ^ 2 : ℝ) • pdEta (pdEta v) p +
        (3 : ℝ) • (p.2.2 • pdEta v p) + v p := by
  have hv0 : DifferentiableAt ℝ v p := hv.differentiableAt (by norm_num)
  have hL : ∀ L : MeridC →L[ℝ] ℝ,
      L (opLam (opLam v) p) =
        L ((4 : ℝ) • opS (opS v) p + (4 : ℝ) • opS (fun q => q.2.2 • pdEta v q) p +
          (4 : ℝ) • opS v p + (p.2.2 ^ 2 : ℝ) • pdEta (pdEta v) p +
          (3 : ℝ) • (p.2.2 • pdEta v p) + v p) := by
    intro L
    have hLv : ContDiffAt ℝ 2 (fun q => L (v q)) p := L.contDiff.contDiffAt.comp p hv
    rw [clm_opLam_opLam L hv, lambda_sq_expansion (fun q => L (v q)) p hLv]
    simp only [map_add, map_smul, smul_eq_mul, clm_opS_opS L hv, clm_opS_eta_pdEta L hv,
      clm_opS L hv0, clm_pdEta_pdEta L hv]
    simp only [pdEta, B0221.dEta, B0221.eEta, clm_fderiv_apply L hv0]
  ext i
  apply Complex.ext
  · exact hL (Complex.reCLM.comp ((EuclideanSpace.proj i : MeridC →L[ℂ] ℂ).restrictScalars ℝ))
  · exact hL (Complex.imCLM.comp ((EuclideanSpace.proj i : MeridC →L[ℂ] ℂ).restrictScalars ℝ))

/-- The six elementary components of `genDiff2 ν v` on `{p : Profile | 0 < p.1}`
(source line 1831–1839). -/
def genDiff2Term1 (ν : ℝ) (v : Profile → MeridC) : Profile → MeridC :=
  fun p => (ν * p.1) • opS (opS v) p

def genDiff2Term2 (ν : ℝ) (v : Profile → MeridC) : Profile → MeridC :=
  fun p => (ν * p.1) • opS (fun q => q.2.2 • pdEta v q) p

def genDiff2Term3 (ν : ℝ) (v : Profile → MeridC) : Profile → MeridC :=
  fun p => (ν * p.1) • opS v p

def genDiff2Term4 (ν : ℝ) (v : Profile → MeridC) : Profile → MeridC :=
  fun p => (ν * p.1) • ((p.2.2 ^ 2 : ℝ) • pdEta (pdEta v) p)

def genDiff2Term5 (ν : ℝ) (v : Profile → MeridC) : Profile → MeridC :=
  fun p => (ν * p.1) • (p.2.2 • pdEta v p)

def genDiff2Term6 (ν : ℝ) (v : Profile → MeridC) : Profile → MeridC :=
  fun p => (ν * p.1) • (v p - opE v p)

/-- Pointwise decomposition of `genDiff2 ν v` at any `p` where `v` is `C²`. -/
theorem genDiff2_expand (ν : ℝ) {v : Profile → MeridC} {p : Profile} (hv : ContDiffAt ℝ 2 v p) :
    genDiff2 ν v p =
      (4 : ℝ) • genDiff2Term1 ν v p + (4 : ℝ) • genDiff2Term2 ν v p +
        (4 : ℝ) • genDiff2Term3 ν v p + genDiff2Term4 ν v p +
        (3 : ℝ) • genDiff2Term5 ν v p + genDiff2Term6 ν v p := by
  unfold genDiff2 genDiff2Term1 genDiff2Term2 genDiff2Term3 genDiff2Term4 genDiff2Term5 genDiff2Term6
  rw [opLam_opLam_eq hv]
  ext i
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, Complex.real_smul]
  ring

/-- Almost-everywhere decomposition of `genDiff2 ν v` on `measureH c` when `v` is smooth on
`{p : Profile | 0 < p.1}`. -/
theorem genDiff2_ae_eq (c ν : ℝ) {v : Profile → MeridC}
    (hv : ContDiffOn ℝ ∞ v {p : Profile | 0 < p.1}) :
    genDiff2 ν v =ᵐ[measureH c]
      ((4 : ℝ) • genDiff2Term1 ν v + (4 : ℝ) • genDiff2Term2 ν v +
        (4 : ℝ) • genDiff2Term3 ν v + genDiff2Term4 ν v +
        (3 : ℝ) • genDiff2Term5 ν v + genDiff2Term6 ν v) := by
  have hcellm : MeasurableSet (cell c) :=
    measurableSet_Ioi.prod (measurableSet_Ioc.prod MeasurableSet.univ)
  have hcell : ∀ᵐ p ∂(measureH c), p ∈ cell c := by
    unfold measureH cellMeasure
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hcellm)
  have hopen : IsOpen {p : Profile | 0 < p.1} := isOpen_lt continuous_const continuous_fst
  filter_upwards [hcell] with p hp
  have hp0 : 0 < p.1 := hp.1
  have hv2 : ContDiffAt ℝ 2 v p :=
    (hv.contDiffAt (hopen.mem_nhds hp0)).of_le (by simp)
  exact genDiff2_expand ν hv2

/-- `MemLp` of `genDiff2 ν v` from `MemLp` of its six elementary components. -/
theorem memLp_genDiff2_of_parts {c ν : ℝ} {v : Profile → MeridC}
    (hv : ContDiffOn ℝ ∞ v {p : Profile | 0 < p.1})
    (ht1 : MemLp (genDiff2Term1 ν v) 2 (measureH c))
    (ht2 : MemLp (genDiff2Term2 ν v) 2 (measureH c))
    (ht3 : MemLp (genDiff2Term3 ν v) 2 (measureH c))
    (ht4 : MemLp (genDiff2Term4 ν v) 2 (measureH c))
    (ht5 : MemLp (genDiff2Term5 ν v) 2 (measureH c))
    (ht6 : MemLp (genDiff2Term6 ν v) 2 (measureH c)) :
    MemLp (genDiff2 ν v) 2 (measureH c) := by
  have hsum : MemLp
      ((4 : ℝ) • genDiff2Term1 ν v + (4 : ℝ) • genDiff2Term2 ν v +
        (4 : ℝ) • genDiff2Term3 ν v + genDiff2Term4 ν v +
        (3 : ℝ) • genDiff2Term5 ν v + genDiff2Term6 ν v) 2 (measureH c) :=
    (((((ht1.const_smul (4 : ℝ)).add (ht2.const_smul (4 : ℝ))).add
      (ht3.const_smul (4 : ℝ))).add ht4).add (ht5.const_smul (3 : ℝ))).add ht6
  exact hsum.ae_eq (genDiff2_ae_eq c ν hv).symm

/-- `L²` norm bound on `genDiff2 ν v` from its six elementary components. -/
theorem norm_genDiff2_le_of_parts {c ν : ℝ} {v : Profile → MeridC}
    (hv : ContDiffOn ℝ ∞ v {p : Profile | 0 < p.1})
    (ht1 : MemLp (genDiff2Term1 ν v) 2 (measureH c))
    (ht2 : MemLp (genDiff2Term2 ν v) 2 (measureH c))
    (ht3 : MemLp (genDiff2Term3 ν v) 2 (measureH c))
    (ht4 : MemLp (genDiff2Term4 ν v) 2 (measureH c))
    (ht5 : MemLp (genDiff2Term5 ν v) 2 (measureH c))
    (ht6 : MemLp (genDiff2Term6 ν v) 2 (measureH c)) :
    ‖(memLp_genDiff2_of_parts hv ht1 ht2 ht3 ht4 ht5 ht6).toLp (genDiff2 ν v)‖ ≤
      4 * ‖ht1.toLp (genDiff2Term1 ν v)‖ + 4 * ‖ht2.toLp (genDiff2Term2 ν v)‖ +
        4 * ‖ht3.toLp (genDiff2Term3 ν v)‖ + ‖ht4.toLp (genDiff2Term4 ν v)‖ +
        3 * ‖ht5.toLp (genDiff2Term5 ν v)‖ + ‖ht6.toLp (genDiff2Term6 ν v)‖ := by
  set h2 := memLp_genDiff2_of_parts hv ht1 ht2 ht3 ht4 ht5 ht6
  set T1 := ht1.toLp (genDiff2Term1 ν v)
  set T2 := ht2.toLp (genDiff2Term2 ν v)
  set T3 := ht3.toLp (genDiff2Term3 ν v)
  set T4 := ht4.toLp (genDiff2Term4 ν v)
  set T5 := ht5.toLp (genDiff2Term5 ν v)
  set T6 := ht6.toLp (genDiff2Term6 ν v)
  have heq : h2.toLp (genDiff2 ν v) =
      ((4 : ℝ) : ℂ) • T1 + ((4 : ℝ) : ℂ) • T2 + ((4 : ℝ) : ℂ) • T3 + T4 +
        ((3 : ℝ) : ℂ) • T5 + T6 := by
    apply Lp.ext
    filter_upwards [h2.coeFn_toLp, genDiff2_ae_eq c ν hv,
      Lp.coeFn_add (((4 : ℝ) : ℂ) • T1 + ((4 : ℝ) : ℂ) • T2 + ((4 : ℝ) : ℂ) • T3 + T4 +
        ((3 : ℝ) : ℂ) • T5) T6,
      Lp.coeFn_add (((4 : ℝ) : ℂ) • T1 + ((4 : ℝ) : ℂ) • T2 + ((4 : ℝ) : ℂ) • T3 + T4)
        (((3 : ℝ) : ℂ) • T5),
      Lp.coeFn_add (((4 : ℝ) : ℂ) • T1 + ((4 : ℝ) : ℂ) • T2 + ((4 : ℝ) : ℂ) • T3) T4,
      Lp.coeFn_add (((4 : ℝ) : ℂ) • T1 + ((4 : ℝ) : ℂ) • T2) (((4 : ℝ) : ℂ) • T3),
      Lp.coeFn_add (((4 : ℝ) : ℂ) • T1) (((4 : ℝ) : ℂ) • T2),
      Lp.coeFn_smul ((4 : ℝ) : ℂ) T1, Lp.coeFn_smul ((4 : ℝ) : ℂ) T2,
      Lp.coeFn_smul ((4 : ℝ) : ℂ) T3, Lp.coeFn_smul ((3 : ℝ) : ℂ) T5,
      ht1.coeFn_toLp, ht2.coeFn_toLp, ht3.coeFn_toLp, ht4.coeFn_toLp,
      ht5.coeFn_toLp, ht6.coeFn_toLp] with p hp hae ha5 ha4 ha3 ha2 ha1 hs1 hs2 hs3 hs5
      hp1 hp2 hp3 hp4 hp5 hp6
    simp only [hp, hae, ha5, ha4, ha3, ha2, ha1, hs1, hs2, hs3, hs5, Pi.add_apply, Pi.smul_apply]
    rw [hp1, hp2, hp3, hp4, hp5, hp6]
    simp only [Complex.coe_smul]
  rw [heq]
  have hn1 : ‖((4 : ℝ) : ℂ) • T1‖ = 4 * ‖T1‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by norm_num)]
  have hn2 : ‖((4 : ℝ) : ℂ) • T2‖ = 4 * ‖T2‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by norm_num)]
  have hn3 : ‖((4 : ℝ) : ℂ) • T3‖ = 4 * ‖T3‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by norm_num)]
  have hn5 : ‖((3 : ℝ) : ℂ) • T5‖ = 3 * ‖T5‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by norm_num)]
  calc ‖((4 : ℝ) : ℂ) • T1 + ((4 : ℝ) : ℂ) • T2 + ((4 : ℝ) : ℂ) • T3 + T4 +
          ((3 : ℝ) : ℂ) • T5 + T6‖
      ≤ ‖((4 : ℝ) : ℂ) • T1 + ((4 : ℝ) : ℂ) • T2 + ((4 : ℝ) : ℂ) • T3 + T4 +
          ((3 : ℝ) : ℂ) • T5‖ + ‖T6‖ := norm_add_le _ _
    _ ≤ ‖((4 : ℝ) : ℂ) • T1 + ((4 : ℝ) : ℂ) • T2 + ((4 : ℝ) : ℂ) • T3 + T4‖ +
          ‖((3 : ℝ) : ℂ) • T5‖ + ‖T6‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ‖((4 : ℝ) : ℂ) • T1 + ((4 : ℝ) : ℂ) • T2 + ((4 : ℝ) : ℂ) • T3‖ + ‖T4‖ +
          ‖((3 : ℝ) : ℂ) • T5‖ + ‖T6‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ‖((4 : ℝ) : ℂ) • T1 + ((4 : ℝ) : ℂ) • T2‖ + ‖((4 : ℝ) : ℂ) • T3‖ + ‖T4‖ +
          ‖((3 : ℝ) : ℂ) • T5‖ + ‖T6‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ‖((4 : ℝ) : ℂ) • T1‖ + ‖((4 : ℝ) : ℂ) • T2‖ + ‖((4 : ℝ) : ℂ) • T3‖ + ‖T4‖ +
          ‖((3 : ℝ) : ℂ) • T5‖ + ‖T6‖ := by gcongr; exact norm_add_le _ _
    _ = 4 * ‖T1‖ + 4 * ‖T2‖ + 4 * ‖T3‖ + ‖T4‖ + 3 * ‖T5‖ + ‖T6‖ := by
        rw [hn1, hn2, hn3, hn5]

/-! ### 2. Leaf propositions for Lemma `near:adjoint-polynomial` and assembly -/

/-- Combined weighted `L²(measureH c)` norm of the flat Leray projection representative `h = P_0 z`
across age powers `S^a` (`a ∈ {0, 1}`), moments `|η|^j` (`j ∈ {0, 1, 2}`), and derivatives
up to order 4 (source lines 1809–1823). -/
def flatProjMomentNorm (c : ℝ) (h : Profile → MeridC) : ℝ :=
  ∑ a ∈ Finset.range 2, ∑ j ∈ Finset.range 3, ∑ m ∈ Finset.range 5,
    (∫ p, (|p.2.2| ^ j) ^ 2 *
      ‖iteratedFDeriv ℝ m (opS^[a] h) p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ)

/-- Regularity, periodicity, age-band support, pointwise moment-derivative boundedness, and
`measureH c`-integrability of a smooth representative `h` of `PepsC 0 c Z` for a test `z` in the
observation box (source lines 1800–1823). Including `bounded_moments` and `integrable_moments`
ensures that `flatProjMomentNorm c h` is a genuine sum of finite `L²(measureH c)` norms (avoiding
Bochner-integral junk values) and provides the domination needed to differentiate under the
planar heat integral. -/
structure IsFlatLerayRep (c σ H1 : ℝ) (h : Profile → MeridC) : Prop where
  smooth : ContDiff ℝ ∞ h
  periodic : QPeriodic c h
  support_s : ∀ p : Profile, p.1 < σ ∨ H1 < p.1 → h p = 0
  bounded_moments : ∀ a ∈ Finset.range 2, ∀ j ∈ Finset.range 3, ∀ m ∈ Finset.range 5,
    ∃ B : ℝ, ∀ p : Profile, |p.2.2| ^ j * ‖iteratedFDeriv ℝ m (opS^[a] h) p‖ ≤ B
  integrable_moments : ∀ a ∈ Finset.range 2, ∀ j ∈ Finset.range 3, ∀ m ∈ Finset.range 5,
    Integrable (fun p => (|p.2.2| ^ j) ^ 2 * ‖iteratedFDeriv ℝ m (opS^[a] h) p‖ ^ 2) (measureH c)

/-- **Leaf 1 (`FlatLeraySmoothRep`, task `PartII-a:N04/2/1`)**: flat Leray projection moment and
derivative bound on the observation box (source `the November 2 reference manuscript`
lines 1723–1726, 1800–1823). Since `PepsC 0 c` acts fiberwise at each `s > 0` as the orthogonal
Leray projection on `L²(ℝ/cℤ × ℝ)`, it commutes with `S = s ∂_s` and constant-coefficient
derivatives. For a smooth meridional test `z` supported in `σ ≤ s ≤ H₁`, `|η| ≤ L₁` with
`Z =ᵐ[measureH c] z`, `PepsC 0 c Z` has a representative `h` satisfying `IsFlatLerayRep c σ H1 h`
whose weighted moment/derivative norm `flatProjMomentNorm c h` is bounded by
`C₁ * GammaBox ν c σ H1 L1 M γs ^ k₁ * h6Norm c z`. -/
def FlatLeraySmoothRep : Prop :=
  ∃ (k1 : ℕ) (C1 : ℝ), 0 ≤ C1 ∧
    ∀ (ν c σ H1 L1 M γs : ℝ), 0 < ν → 0 < c → 0 < σ → σ ≤ H1 → 0 ≤ L1 → 0 ≤ M → 0 < γs →
      ∀ (z : Profile → MeridC) (Z : HSpace c MeridC), IsMeridTest c z →
        (∀ p, z p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1) →
        (Z : Profile → MeridC) =ᵐ[measureH c] z →
        ∃ h : Profile → MeridC,
          IsFlatLerayRep c σ H1 h ∧
          (PepsC 0 c Z : Profile → MeridC) =ᵐ[measureH c] h ∧
          flatProjMomentNorm c h ≤ C1 * GammaBox ν c σ H1 L1 M γs ^ k1 * h6Norm c z

/-- **Leaf 2 (`FlatAdjointElementaryBound`, task `PartII-a:N04/2/2`)**: causal flat adjoint
representation and elementary derivative bounds from the flat Leray representative `h`
(source `the November 2 reference manuscript`
lines 1803–1836). Given `h` satisfying `IsFlatLerayRep c σ H1 h` with
`PepsC 0 c Z =ᵐ[measureH c] h`, the flat adjoint
`V = (T0flat hc ν μ).adjoint Z = (B0225.R0 hc ν μ).adjoint (PepsC 0 c Z)` has a representative `v`
given on `s > 0` by the backward causal integral
`v(s, ·) = ∫_0^∞ e^{-(μ̄ + 1/2) t} e^{ν s (e^t - 1) Δ_{q,η}} (h(s e^t, ·)) dt`, which is smooth
on `{p : Profile | 0 < p.1}`, `c`-periodic in `q`, and vanishes for `s > H₁`. Using heat-semigroup
moment propagation (`η e^{θΔ} = e^{θΔ}(η - 2θ ∂_η)` and `η² e^{θΔ} = e^{θΔ}(η² - 4θ η ∂_η - 2θ + 4θ² ∂_η²)`)
with `0 ≤ θ ≤ ν H₁` and the age identities
`S v = (μ̄ + 1/2 - ν s Δ_{q,η}) v - h` and `S² v = (μ̄ + 1/2 - ν s Δ_{q,η}) S v - ν s Δ_{q,η} v - S h`,
the elementary components `genDiff1 ν v`, `genDiff2Term1..6 ν v`, and `gradDiff1 v` belong to
`L²(measureH c)` (resp. `L²(measureHT c)`) with norms bounded by
`C₂ * GammaBox ν c σ H1 L1 M γs ^ k₂ * flatProjMomentNorm c h`. -/
def FlatAdjointElementaryBound : Prop :=
  ∃ (k2 : ℕ) (C2 : ℝ), 0 ≤ C2 ∧
    ∀ (ν c σ H1 L1 M γs : ℝ) (hc : 0 < c), 0 < ν → 0 < σ → σ ≤ H1 → 0 ≤ L1 → 0 < γs →
      ∀ μ : ℂ, ‖μ‖ ≤ M → γs ≤ μ.re + 1 / 4 →
        ∀ (Z : HSpace c MeridC) (h : Profile → MeridC),
          IsFlatLerayRep c σ H1 h →
          (PepsC 0 c Z : Profile → MeridC) =ᵐ[measureH c] h →
          ∃ v : Profile → MeridC,
            ContDiffOn ℝ ∞ v {p : Profile | 0 < p.1} ∧ QPeriodic c v ∧
            (∀ p, H1 < p.1 → v p = 0) ∧
            ((ContinuousLinearMap.adjoint (T0flat hc ν μ) Z : HSpace c MeridC) :
              Profile → MeridC) =ᵐ[measureH c] v ∧
            ∃ (h1 : MemLp (genDiff1 ν v) 2 (measureH c))
              (ht1 : MemLp (genDiff2Term1 ν v) 2 (measureH c))
              (ht2 : MemLp (genDiff2Term2 ν v) 2 (measureH c))
              (ht3 : MemLp (genDiff2Term3 ν v) 2 (measureH c))
              (ht4 : MemLp (genDiff2Term4 ν v) 2 (measureH c))
              (ht5 : MemLp (genDiff2Term5 ν v) 2 (measureH c))
              (ht6 : MemLp (genDiff2Term6 ν v) 2 (measureH c))
              (hgd : MemLp (gradDiff1 v) 2 (measureHT c)),
              ‖h1.toLp (genDiff1 ν v)‖ +
                (4 * ‖ht1.toLp (genDiff2Term1 ν v)‖ + 4 * ‖ht2.toLp (genDiff2Term2 ν v)‖ +
                  4 * ‖ht3.toLp (genDiff2Term3 ν v)‖ + ‖ht4.toLp (genDiff2Term4 ν v)‖ +
                  3 * ‖ht5.toLp (genDiff2Term5 ν v)‖ + ‖ht6.toLp (genDiff2Term6 ν v)‖) +
                ‖hgd.toLp (gradDiff1 v)‖ ≤
                  C2 * GammaBox ν c σ H1 L1 M γs ^ k2 * flatProjMomentNorm c h

/-- Assembly of `AdjointPolynomialBound` (`PartII-a:N04/2`) from `FlatLeraySmoothRep` and
`FlatAdjointElementaryBound`, using the `Λ²` expansion `genDiff2_expand`. -/
theorem adjointPolynomialBound_of (hRep : FlatLeraySmoothRep)
    (hElem : FlatAdjointElementaryBound) : AdjointPolynomialBound := by
  obtain ⟨k1, C1, hC1, hRep⟩ := hRep
  obtain ⟨k2, C2, hC2, hElem⟩ := hElem
  refine ⟨k1 + k2, C1 * C2, mul_nonneg hC1 hC2, ?_⟩
  intro ν c σ H1 L1 M γs hc hν hσ hσH1 hL1 hγs μ hμM hμγ z Z hz hsupp hZ
  have hM0 : 0 ≤ M := (norm_nonneg μ).trans hμM
  have hG0 : 0 ≤ GammaBox ν c σ H1 L1 M γs := GammaBox_nonneg hν hc hσ hσH1 hL1 hM0 hγs
  obtain ⟨h, hh_rep, hh_ae, hh_bound⟩ :=
    hRep ν c σ H1 L1 M γs hν hc hσ hσH1 hL1 hM0 hγs z Z hz hsupp hZ
  obtain ⟨v, hv_smooth, hv_per, hv_supp, hv_ae,
      h1, ht1, ht2, ht3, ht4, ht5, ht6, hgd, hv_bound⟩ :=
    hElem ν c σ H1 L1 M γs hc hν hσ hσH1 hL1 hγs μ hμM hμγ Z h hh_rep hh_ae
  set h2 := memLp_genDiff2_of_parts hv_smooth ht1 ht2 ht3 ht4 ht5 ht6
  refine ⟨v, hv_smooth, hv_per, hv_supp, hv_ae, h1, h2, hgd, ?_⟩
  have h2_le := norm_genDiff2_le_of_parts hv_smooth ht1 ht2 ht3 ht4 ht5 ht6
  calc ‖h1.toLp (genDiff1 ν v)‖ + ‖h2.toLp (genDiff2 ν v)‖ + ‖hgd.toLp (gradDiff1 v)‖
      ≤ ‖h1.toLp (genDiff1 ν v)‖ +
          (4 * ‖ht1.toLp (genDiff2Term1 ν v)‖ + 4 * ‖ht2.toLp (genDiff2Term2 ν v)‖ +
            4 * ‖ht3.toLp (genDiff2Term3 ν v)‖ + ‖ht4.toLp (genDiff2Term4 ν v)‖ +
            3 * ‖ht5.toLp (genDiff2Term5 ν v)‖ + ‖ht6.toLp (genDiff2Term6 ν v)‖) +
          ‖hgd.toLp (gradDiff1 v)‖ := by linarith
    _ ≤ C2 * GammaBox ν c σ H1 L1 M γs ^ k2 * flatProjMomentNorm c h := hv_bound
    _ ≤ C2 * GammaBox ν c σ H1 L1 M γs ^ k2 *
          (C1 * GammaBox ν c σ H1 L1 M γs ^ k1 * h6Norm c z) := by
        gcongr
    _ = C1 * C2 * GammaBox ν c σ H1 L1 M γs ^ (k1 + k2) * h6Norm c z := by
        rw [pow_add]
        ring

end UnforcedLeray.Short.PartIIa
