import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N04_3

/-!
# Sub `PartII-a_N04_3_3`: Weak Characterization of `RepsVec.adjoint` (`RepsVecAdjointOfWeakEq`)

Source of record: `the November 2 reference manuscript`,
lines 1842–1845 (Lemma `near:smooth-adjoint-comparison`) and lines 3327–3368 (B0222–B0223,
the exact meridional vector generator `A_ε^vec`, outer semigroup `S_ε(t)`, and resolvent
`R_ε^vec(μ)`).

This file proves the unconditional reductions for `RepsVecAdjointOfWeakEq`:
1. `memLp_AepsVecC_isMeridTest` and `auEps_eq_mu_smul_sub`: for any smooth meridional test
   `IsMeridTest c u`, `AepsVecC ν ε u ∈ L²(measureH c)` and `AUε = μ • U - AεU` in `HSpace c MeridC`.
2. `merReL_AepsVecC` and `merIm_AepsVecC`: the real and imaginary parts of `AepsVecC ν ε u`
   coincide pointwise with the real meridional vector generator `B0222.AepsVec ν ε` applied to the
   real and imaginary profile components `reMerid u` and `imMerid u`.
3. `isTestFieldVec_fieldU_of_band` and `outerGenVec_fieldU_ae`: the physical lift `fieldU ε b` of
   any real smooth meridional test profile `b` is a `C²` vector test field (`IsTestFieldVec`)
   on which `B0222.outerGenVec ν ε` acts almost everywhere as `fieldU ε (B0222.AepsVec ν ε b)`.
4. `isGenPair_liftVec_cplxH_of_outerS` and `isGenPair_liftVec_isMeridTest`: combining
   `J_ae_of_periodic`, `liftVecCplx`, and `cplxH_reHC_add_im`, we reduce the generator-graph
   membership `B0223.IsGenPair (B0223.outerS hν ε) (liftVec U) (liftVec AεU)` for complex meridional
   tests `IsMeridTest c u` to `OuterSIsGenPairOnTestFieldVec` (the `IsGenPair` counterpart of
   `B0222.GeneratorOnTestFieldsVec`), and deduce `B0223.RepsVec hν hε hc hP μ AUε = U` via
   `B0223.RepsVec_left`.
5. `repsVecAdjointOfWeakEq_of`: assembles `RepsVecAdjointOfWeakEq` from
   `OuterSIsGenPairOnTestFieldVec` (`PartII-a:N04/3/3/1`) and
   `MeridTestResolventDense` (`PartII-a:N04/3/3/2`) via `repsVecAdjointOfWeakEq_of_left_and_ortho`.
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

/-! ### 1. `L²(measureH c)` membership of `AepsVecC` and decomposition of `AUε` -/

/-- For a smooth meridional test `u` (`IsMeridTest c u`), `AepsVecC ν ε u` belongs to
`L²(measureH c)`. -/
theorem memLp_AepsVecC_isMeridTest {c : ℝ} (ν ε : ℝ) {u : Profile → MeridC}
    (hu : IsMeridTest c u) :
    MemLp (AepsVecC ν ε u) 2 (measureH c) := by
  have heq : AepsVecC ν ε u = -fun p => (0 : ℂ) • u p - AepsVecC ν ε u p := by
    ext p i
    simp
  rw [heq]
  exact (memLp_mu_sub_AepsVecC ν ε 0 hu).neg

/-- If `U =ᵐ u`, `AεU =ᵐ AepsVecC ν ε u`, and `AUε =ᵐ μ • u - AepsVecC ν ε u`, then
`AUε = μ • U - AεU` in `HSpace c MeridC`. -/
theorem auEps_eq_mu_smul_sub {c : ℝ} (ν ε : ℝ) (μ : ℂ)
    {u : Profile → MeridC} {U AεU AUε : HSpace c MeridC}
    (hU : (U : Profile → MeridC) =ᵐ[measureH c] u)
    (hAεU : (AεU : Profile → MeridC) =ᵐ[measureH c] AepsVecC ν ε u)
    (hAUε : (AUε : Profile → MeridC) =ᵐ[measureH c] (fun p => μ • u p - AepsVecC ν ε u p)) :
    AUε = μ • U - AεU := by
  apply Lp.ext
  filter_upwards [hAUε, Lp.coeFn_sub (μ • U) AεU, Lp.coeFn_smul μ U, hU, hAεU] with
    p hpAU hpSub hpSmul hpU hpAεU
  rw [hpAU, hpSub, Pi.sub_apply, hpSmul, Pi.smul_apply, hpU, hpAεU]

/-! ### 2. Real and imaginary meridional components and `B0222.AepsVec` -/

/-- Real part of a `MeridC`-valued profile as a real meridional profile `Profile → Merid`. -/
def reMerid (u : Profile → MeridC) : Profile → Merid := fun p => merReL (u p)

/-- Imaginary part of a `MeridC`-valued profile as a real meridional profile `Profile → Merid`. -/
def imMerid (u : Profile → MeridC) : Profile → Merid := fun p => merReL ((-Complex.I) • u p)

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
    DifferentiableAt ℝ (PartIIa.opS u) p := by
  have hS := differentiableAt_fderiv_apply_of_contDiffAt hu (1, 0, 0)
  have hfst : DifferentiableAt ℝ (fun q : Profile => q.1) p := differentiableAt_fst
  exact hfst.smul hS

private theorem differentiableAt_opK_of_contDiffAt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {u : Profile → E} {p : Profile}
    (hu : ContDiffAt ℝ 2 u p) :
    DifferentiableAt ℝ (PartIIa.opK u) p := by
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

private theorem differentiableAt_opQ_of_contDiffAt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (ε : ℝ) {u : Profile → E} {p : Profile}
    (hu : ContDiffAt ℝ 2 u p) :
    DifferentiableAt ℝ (PartIIa.opQ ε u) p := by
  have hQ := differentiableAt_fderiv_apply_of_contDiffAt hu (0, 1, 0)
  have hLam := differentiableAt_opLam_of_contDiffAt hu
  exact hQ.sub (hLam.const_smul ε)

private theorem clm_opS {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) {f : Profile → E} {p : Profile} (hf : DifferentiableAt ℝ f p) :
    L (PartIIa.opS f p) = B0221.opS (fun q => L (f q)) p := by
  simp only [PartIIa.opS, pdS, B0221.opS, B0221.dS, B0221.eS, map_smul, smul_eq_mul,
    clm_fderiv_apply L hf]

private theorem clm_opK {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) {f : Profile → E} {p : Profile} (hf : DifferentiableAt ℝ f p) :
    L (PartIIa.opK f p) = B0221.opK (fun q => L (f q)) p := by
  simp only [PartIIa.opK, PartIIa.opS, pdS, pdEta, B0221.opK, B0221.dS, B0221.dEta,
    B0221.eS, B0221.eEta, map_add, map_smul, smul_eq_mul, clm_fderiv_apply L hf]
  ring

private theorem clm_opQ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) (ε : ℝ) {f : Profile → E} {p : Profile} (hf : DifferentiableAt ℝ f p) :
    L (PartIIa.opQ ε f p) = B0221.opQ ε (fun q => L (f q)) p := by
  simp only [PartIIa.opQ, pdQ, B0221.opQ, B0221.dQ, B0221.eQ, map_sub, map_add, map_smul,
    smul_eq_mul, clm_fderiv_apply L hf, clm_opK L hf]

private theorem clm_opQ_opQ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) (ε : ℝ) {u : Profile → E} {p : Profile} (hu : ContDiffAt ℝ 2 u p) :
    L (PartIIa.opQ ε (PartIIa.opQ ε u) p) =
      B0221.opQ ε (B0221.opQ ε (fun q => L (u q))) p := by
  rw [clm_opQ L ε (differentiableAt_opQ_of_contDiffAt ε hu)]
  have hev : (fun q => L (PartIIa.opQ ε u q)) =ᶠ[nhds p] B0221.opQ ε (fun q => L (u q)) := by
    filter_upwards [hu.eventually (by simp)] with q hq
    exact clm_opQ L ε (hq.differentiableAt (by norm_num))
  simp only [B0221.opQ, B0221.opK, B0221.dQ, B0221.dS, B0221.dEta, hev.fderiv_eq, hev.self_of_nhds]

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

/-- The real part of `AepsVecC ν ε u` on a `C²` profile `u` equals `B0222.AepsVec ν ε (reMerid u)`. -/
theorem merReL_AepsVecC (ν ε : ℝ) {u : Profile → MeridC} {p : Profile}
    (hu : ContDiffAt ℝ 2 u p) :
    merReL (AepsVecC ν ε u p) = B0222.AepsVec ν ε (reMerid u) p := by
  have hu0 : DifferentiableAt ℝ u p := hu.differentiableAt (by norm_num)
  ext i
  set L : MeridC →L[ℝ] ℝ :=
    Complex.reCLM.comp ((EuclideanSpace.proj i : MeridC →L[ℂ] ℂ).restrictScalars ℝ)
  have hLi : L (opE u p) = B0222.radialSel i * L (u p) := by
    fin_cases i <;> simp [L, opE, B0222.radialSel]
  have hL_apply : ∀ q, L (u q) = reMerid u q i := fun q => rfl
  change L (AepsVecC ν ε u p) = B0222.AepsVec ν ε (reMerid u) p i
  simp only [AepsVecC, B0222.AepsVec, PiLp.toLp_apply, map_add, map_sub, map_neg, map_smul,
    smul_eq_mul, clm_opS L hu0, clm_opQ_opQ L ε hu, clm_pdEta_pdEta L hu, hLi, hL_apply]
  ring

/-- The imaginary part of `AepsVecC ν ε u` on a `C²` profile `u` equals
`B0222.AepsVec ν ε (imMerid u)`. -/
theorem merIm_AepsVecC (ν ε : ℝ) {u : Profile → MeridC} {p : Profile}
    (hu : ContDiffAt ℝ 2 u p) :
    merReL ((-Complex.I) • AepsVecC ν ε u p) = B0222.AepsVec ν ε (imMerid u) p := by
  have hu0 : DifferentiableAt ℝ u p := hu.differentiableAt (by norm_num)
  ext i
  set L : MeridC →L[ℝ] ℝ :=
    Complex.imCLM.comp ((EuclideanSpace.proj i : MeridC →L[ℂ] ℂ).restrictScalars ℝ)
  have hLi : L (opE u p) = B0222.radialSel i * L (u p) := by
    fin_cases i <;> simp [L, opE, B0222.radialSel]
  have hL_apply : ∀ q, L (u q) = imMerid u q i := by
    intro q
    simp [L, imMerid, merReL_apply]
  have hL_A : merReL ((-Complex.I) • AepsVecC ν ε u p) i = L (AepsVecC ν ε u p) := by
    simp [L, merReL_apply]
  rw [hL_A]
  simp only [AepsVecC, B0222.AepsVec, PiLp.toLp_apply, map_add, map_sub, map_neg, map_smul,
    smul_eq_mul, clm_opS L hu0, clm_opQ_opQ L ε hu, clm_pdEta_pdEta L hu, hLi, hL_apply]
  ring

/-! ### 3. Physical lift of smooth meridional tests to vector test fields -/

/-- The physical vector test fields: every Cartesian component is a scalar test field of `B0221`
(`C²` off the axis, vanishing near the axis, bounded support in `x`, `2εc`-periodic in `τ`). -/
def IsTestFieldVec (ε c : ℝ) (V : Space × ℝ → Space) : Prop :=
  ∀ j : Fin 3, B0221.IsTestField ε c (fun y => V y j)

private theorem isTestField_mul_add {ε c : ℝ} {u v : Space × ℝ → ℝ}
    (hu : B0221.IsTestField ε c u) (hv : B0221.IsTestField ε c v) {g : Space → ℝ}
    (hg : ∀ x : Space, B0220.radius x ≠ 0 → ContDiffAt ℝ 2 g x) (k : ℝ) :
    B0221.IsTestField ε c (fun y => u y * g y.1 + v y * k) where
  smooth y hy :=
    ((hu.smooth y hy).mul ((hg y.1 hy).comp y contDiffAt_fst)).add
      ((hv.smooth y hy).mul contDiffAt_const)
  axis := by
    obtain ⟨δ1, hδ1, h1⟩ := hu.axis
    obtain ⟨δ2, hδ2, h2⟩ := hv.axis
    refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun y hy => ?_⟩
    simp only [h1 y (hy.trans_le (min_le_left _ _)), h2 y (hy.trans_le (min_le_right _ _))]
    ring
  bounded := by
    obtain ⟨R1, h1⟩ := hu.bounded
    obtain ⟨R2, h2⟩ := hv.bounded
    refine ⟨max R1 R2, fun y hy => ?_⟩
    simp only [h1 y ((le_max_left _ _).trans_lt hy), h2 y ((le_max_right _ _).trans_lt hy)]
    ring
  periodic x τ := by
    simp only [hu.periodic x τ, hv.periodic x τ]

/-- `B0222.AepsVec ν ε b` is `c`-periodic in `q` when `b` is. -/
theorem qPeriodic_AepsVec {c : ℝ} (ν ε : ℝ) {b : Profile → Merid} (hb : QPeriodic c b) :
    QPeriodic c (B0222.AepsVec ν ε b) := fun p => by
  rw [B0222.AepsVec_eq_scalar_sub, B0222.AepsVec_eq_scalar_sub, hb p]
  congr 2
  funext i
  exact B0221.qPeriodic_Aeps ν ε (fun q => by simp only [hb q]) p

/-- For an `H`-class `F` of a `q`-periodic profile `f`,
`J_ε F = (√(2π) ε)⁻¹ a (f_r e_r + f_z e_z)` almost everywhere. -/
theorem J_ae_of_periodic {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) {f : Profile → Merid}
    (hf : QPeriodic c f) (F : HSpace c Merid) (hF : (F : Profile → Merid) =ᵐ[measureH c] f) :
    (B0220.J hε hc F : Space × ℝ → Space) =ᵐ[B0220.physMeasure ε c]
      fun y => B0220.jConst ε • B0220.fieldU ε f y := by
  have h1 := (B0220.jComp hε hc).coeFn_toLI F
  have h2 := (B0220.jComp hε hc).compFun_congr hF
  filter_upwards [h1, h2] with y hy1 hy2
  change (B0220.jComp hε hc).toLI F y = _
  rw [hy1, hy2]
  have hcell : f (B0220.cellChart ε c y) = f (B0220.chart ε y) :=
    B0220.periodic_reduceIoc_eq f hf _ _ _
  simp only [B0220.WeightedComp.compFun, B0220.jComp, LinearMap.smul_apply, B0220.fieldU,
    smul_smul, hcell]

/-- Any smooth real meridional profile `b` that is `c`-periodic in `q` and supported in
`s ∈ [s0, s1]`, `|η| ≤ L` (`0 < s0`) lifts via `B0220.fieldU ε b` to a vector test field
`IsTestFieldVec ε c (B0220.fieldU ε b)`. -/
theorem isTestFieldVec_fieldU_of_band {ε c s0 s1 L : ℝ} (hε : 0 < ε) (hs0 : 0 < s0)
    {b : Profile → Merid} (hb : ContDiff ℝ ∞ b) (hper : QPeriodic c b)
    (hband : ∀ p, b p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) :
    IsTestFieldVec ε c (B0220.fieldU ε b) := by
  intro j
  have hcomp : ∀ i : Fin 2, ContDiffOn ℝ 2 (fun p => b p i) {p | 0 < p.1} := fun i =>
    ((EuclideanSpace.proj i : Merid →L[ℝ] ℝ).contDiff.comp hb).contDiffOn.of_le (by simp)
  have hsupp : ∀ i : Fin 2, ∀ p : Profile, 0 < p.1 → b p i ≠ 0 →
      p.1 ∈ Icc s0 (max s0 s1) ∧ |p.2.2| ≤ L := by
    intro i p _ hi
    have hne : b p ≠ 0 := fun h0 => hi (by simp [h0])
    obtain ⟨⟨hs0', hs1'⟩, hL⟩ := hband p hne
    exact ⟨⟨hs0', hs1'.trans (le_max_right s0 s1)⟩, hL⟩
  have hu := B0221.isTestField_liftU (c := c) hε hs0 (le_max_left s0 s1) (hcomp 0)
    (fun p => by simp only [hper p]) (hsupp 0)
  have hv := B0221.isTestField_liftU (c := c) hε hs0 (le_max_left s0 s1) (hcomp 1)
    (fun p => by simp only [hper p]) (hsupp 1)
  have h := isTestField_mul_add hu hv (g := fun x => B0220.unitR x j)
    (fun x hx => B0222.contDiffAt_unitR j hx) (B0220.unitZ j)
  have heq : (fun y => B0220.fieldU ε b y j) =
      fun y => B0220.liftU ε (fun p => b p 0) y * B0220.unitR y.1 j +
        B0220.liftU ε (fun p => b p 1) y * B0220.unitZ j := by
    funext y
    rw [B0222.fieldU_eq, PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul]
  rw [heq]
  exact h

/-- For any `C²` real meridional profile `b`, `B0222.outerGenVec ν ε (B0220.fieldU ε b)` agrees
`physMeasure ε c`-almost everywhere with `B0220.fieldU ε (B0222.AepsVec ν ε b)`. -/
theorem outerGenVec_fieldU_ae (ν ε c : ℝ) (hε : 0 < ε) {b : Profile → Merid}
    (hb : ContDiff ℝ ∞ b) :
    B0222.outerGenVec ν ε (B0220.fieldU ε b) =ᵐ[B0220.physMeasure ε c]
      B0220.fieldU ε (B0222.AepsVec ν ε b) := by
  filter_upwards [B0220.ae_physMeasure ε c] with y hy
  obtain ⟨x, τ⟩ := y
  exact B0222.outerGenVec_fieldU hε.ne' hy.1 (hb.contDiffAt.of_le (by simp))

/-! ### 4. Linearity of `B0223.IsGenPair` and reduction to `OuterSIsGenPairOnTestFieldVec` -/

theorem isGenPair_add {ν ε P : ℝ} [Fact (0 < P)] (hν : 0 < ν)
    {x1 y1 x2 y2 : B0223.X B0223.SpaceC P}
    (h1 : B0223.IsGenPair (B0223.outerS hν ε) x1 y1)
    (h2 : B0223.IsGenPair (B0223.outerS hν ε) x2 y2) :
    B0223.IsGenPair (B0223.outerS hν ε) (x1 + x2) (y1 + y2) := by
  intro t ht
  simp only [map_add]
  exact (h1 t ht).add (h2 t ht)

theorem isGenPair_smul {ν ε P : ℝ} [Fact (0 < P)] (hν : 0 < ν) (a : ℂ)
    {x y : B0223.X B0223.SpaceC P}
    (h : B0223.IsGenPair (B0223.outerS hν ε) x y) :
    B0223.IsGenPair (B0223.outerS hν ε) (a • x) (a • y) := by
  intro t ht
  simp only [map_smul]
  exact (h t ht).const_smul a

/-- **Leaf 1 (`OuterSIsGenPairOnTestFieldVec`)**: the outer semigroup `B0223.outerS hν ε`
differentiates in `X SpaceC P` on lifted real vector test fields `IsTestFieldVec ε c V`
as the classical Cartesian outer vector operator `B0222.outerGenVec ν ε V` (the `IsGenPair`
counterpart of `B0222.GeneratorOnTestFieldsVec`, Units `B0222`/`B0223`, tex lines 3343–3352). -/
def OuterSIsGenPairOnTestFieldVec : Prop :=
  ∀ (ν c ε : ℝ) (hν : 0 < ν) (_hc : 0 < c) (_hε : 0 < ε)
    (P : ℝ) [Fact (0 < P)] (hP : P = 2 * ε * c)
    (V : Space × ℝ → Space), IsTestFieldVec ε c V →
    ∀ W GW : B0220.PhysL2 ε c,
      (W : Space × ℝ → Space) =ᵐ[B0220.physMeasure ε c] V →
      (GW : Space × ℝ → Space) =ᵐ[B0220.physMeasure ε c] B0222.outerGenVec ν ε V →
      B0223.IsGenPair (B0223.outerS hν ε) (toX hP W) (toX hP GW)

/-- Under `OuterSIsGenPairOnTestFieldVec`, for any smooth real meridional profile `b` supported in
`s ∈ [s0, s1]`, `|η| ≤ L` (`0 < s0`) and `c`-periodic in `q`, the complexified lifts of `bL` and
`Ab` form a generator pair for `B0223.outerS hν ε`. -/
theorem isGenPair_liftVec_cplxH_of_outerS (hOuter : OuterSIsGenPairOnTestFieldVec)
    {ν c ε P s0 s1 L : ℝ} [Fact (0 < P)] (hν : 0 < ν) (hc : 0 < c) (hε : 0 < ε)
    (hP : P = 2 * ε * c) (hs0 : 0 < s0) {b : Profile → Merid}
    (hb : ContDiff ℝ ∞ b) (hper : QPeriodic c b)
    (hband : ∀ p, b p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L)
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
  have hW : (W : Space × ℝ → Space) =ᵐ[B0220.physMeasure ε c] B0220.fieldU ε b := by
    filter_upwards [Lp.coeFn_smul k⁻¹ (B0220.J hε hc bL), hJb] with y h1 h2
    rw [h1, Pi.smul_apply, h2, smul_smul, inv_mul_cancel₀ hk, one_smul]
  have hGW : (GW : Space × ℝ → Space) =ᵐ[B0220.physMeasure ε c]
      B0222.outerGenVec ν ε (B0220.fieldU ε b) := by
    filter_upwards [Lp.coeFn_smul k⁻¹ (B0220.J hε hc Ab), hJA,
      outerGenVec_fieldU_ae ν ε c hε hb] with y h1 h2 h3
    rw [h1, Pi.smul_apply, h2, smul_smul, inv_mul_cancel₀ hk, one_smul, h3]
  have hgenW := hOuter ν c ε hν hc hε P hP (B0220.fieldU ε b)
    (isTestFieldVec_fieldU_of_band hε hs0 hb hper hband) W GW hW hGW
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

/-- Under `OuterSIsGenPairOnTestFieldVec`, for any smooth complex meridional test `IsMeridTest c u`
with `U =ᵐ u` and `AεU =ᵐ AepsVecC ν ε u`, the lifted pair `(liftVec U, liftVec AεU)` belongs to
the generator graph of `B0223.outerS hν ε`. -/
theorem isGenPair_liftVec_isMeridTest (hOuter : OuterSIsGenPairOnTestFieldVec)
    {ν c ε P : ℝ} [Fact (0 < P)] (hν : 0 < ν) (hc : 0 < c) (hε : 0 < ε)
    (hP : P = 2 * ε * c) {u : Profile → MeridC} {U AεU : HSpace c MeridC}
    (hu : IsMeridTest c u)
    (hU : (U : Profile → MeridC) =ᵐ[measureH c] u)
    (hAεU : (AεU : Profile → MeridC) =ᵐ[measureH c] AepsVecC ν ε u) :
    B0223.IsGenPair (B0223.outerS hν ε)
      (B0223.liftVec hε hc hP U)
      (B0223.liftVec hε hc hP AεU) := by
  obtain ⟨s0, s1, L, hs0, hband⟩ := hu.band
  have hRe_smooth : ContDiff ℝ ∞ (reMerid u) := merReL.contDiff.comp hu.smooth
  have hIm_smooth : ContDiff ℝ ∞ (imMerid u) :=
    merReL.contDiff.comp (hu.smooth.const_smul (-Complex.I))
  have hRe_per : QPeriodic c (reMerid u) := fun p => by simp [reMerid, hu.periodic p]
  have hIm_per : QPeriodic c (imMerid u) := fun p => by simp [imMerid, hu.periodic p]
  have hRe_band : ∀ p, reMerid u p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L := by
    intro p hp
    refine hband p fun hu0 => hp ?_
    simp [reMerid, hu0]
  have hIm_band : ∀ p, imMerid u p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L := by
    intro p hp
    refine hband p fun hu0 => hp ?_
    simp [imMerid, hu0]
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
    filter_upwards [reHC_ae c AεU, hAεU] with p hp1 hp2
    rw [hp1, hp2, merReL_AepsVecC ν ε (hu.smooth.contDiffAt.of_le (by simp))]
  have hA_im : (reHC c ((-Complex.I) • AεU) : Profile → Merid) =ᵐ[measureH c]
      B0222.AepsVec ν ε (imMerid u) := by
    filter_upwards [reHC_ae c ((-Complex.I) • AεU), Lp.coeFn_smul (-Complex.I) AεU, hAεU] with
      p hp1 hp2 hp3
    rw [hp1, hp2, Pi.smul_apply, hp3, merIm_AepsVecC ν ε (hu.smooth.contDiffAt.of_le (by simp))]
  have hgenRe := isGenPair_liftVec_cplxH_of_outerS hOuter hν hc hε hP hs0
    hRe_smooth hRe_per hRe_band hU_re hA_re
  have hgenIm := isGenPair_liftVec_cplxH_of_outerS hOuter hν hc hε hP hs0
    hIm_smooth hIm_per hIm_band hU_im hA_im
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

/-- Left-inverse identity `B0223.RepsVec hν hε hc hP μ AUε = U` on smooth meridional tests
`IsMeridTest c u`, deduced from `OuterSIsGenPairOnTestFieldVec` via `B0223.RepsVec_left`. -/
theorem repsVec_left_of_outerS (hOuter : OuterSIsGenPairOnTestFieldVec)
    (ν c ε : ℝ) (hν : 0 < ν) (hc : 0 < c) (hε : 0 < ε) (_hε1 : ε ≤ 1)
    (P : ℝ) [Fact (0 < P)] (hP : P = 2 * ε * c) (_hP1 : P ≤ 1)
    (μ : ℂ) (hγ : 0 < μ.re + 1 / 4)
    (u : Profile → MeridC) (U AUε : HSpace c MeridC)
    (hu : IsMeridTest c u)
    (hU : (U : Profile → MeridC) =ᵐ[measureH c] u)
    (hAUε : (AUε : Profile → MeridC) =ᵐ[measureH c] (fun p => μ • u p - AepsVecC ν ε u p)) :
    B0223.RepsVec hν hε hc hP μ AUε = U := by
  have hAε_mem := memLp_AepsVecC_isMeridTest ν ε hu
  set AεU : HSpace c MeridC := hAε_mem.toLp (AepsVecC ν ε u)
  rw [auEps_eq_mu_smul_sub ν ε μ hU hAε_mem.coeFn_toLp hAUε]
  exact B0223.RepsVec_left hν hε hc hP hγ
    (isGenPair_liftVec_isMeridTest hOuter hν hc hε hP hu hU hAε_mem.coeFn_toLp)

/-! ### 5. Core density leaf and assembly of `RepsVecAdjointOfWeakEq` -/

/-- **Leaf 2 (`MeridTestResolventDense`)**: `(μ - AepsVecC ν ε)(IsMeridTest c)` has trivial
orthogonal complement in `HSpace c MeridC` for `0 < μ.re + 1 / 4` (i.e. smooth meridional tests
`IsMeridTest c` form a core for `A_ε^vec`, source lines 1842–1845). -/
def MeridTestResolventDense : Prop :=
  ∀ (ν c ε : ℝ), 0 < ν → 0 < c → 0 < ε → ε ≤ 1 →
    ∀ (P : ℝ) [Fact (0 < P)], P = 2 * ε * c → P ≤ 1 →
      ∀ μ : ℂ, 0 < μ.re + 1 / 4 →
        ∀ W : HSpace c MeridC,
          (∀ (u : Profile → MeridC) (AUε : HSpace c MeridC),
            IsMeridTest c u →
            (AUε : Profile → MeridC) =ᵐ[measureH c] (fun p => μ • u p - AepsVecC ν ε u p) →
            inner ℂ AUε W = 0) →
          W = 0

/-- Helper reduction for `MeridTestResolventDense`: it suffices to verify `W = 0` assuming
orthogonality against the canonical `toLp` representative `(memLp_mu_sub_AepsVecC ν ε μ hu).toLp _`
for each `hu : IsMeridTest c u`. -/
theorem meridTestResolventDense_of_toLp
    (h : ∀ (ν c ε : ℝ), 0 < ν → 0 < c → 0 < ε → ε ≤ 1 →
      ∀ (P : ℝ) [Fact (0 < P)], P = 2 * ε * c → P ≤ 1 →
        ∀ μ : ℂ, 0 < μ.re + 1 / 4 →
          ∀ W : HSpace c MeridC,
            (∀ (u : Profile → MeridC) (hu : IsMeridTest c u),
              inner ℂ ((memLp_mu_sub_AepsVecC ν ε μ hu).toLp
                (fun p => μ • u p - AepsVecC ν ε u p)) W = 0) →
            W = 0) :
    MeridTestResolventDense := by
  intro ν c ε hν hc hε hε1 P _ hP hP1 μ hγ W hW
  exact h ν c ε hν hc hε hε1 P hP hP1 μ hγ W fun u hu =>
    hW u _ hu (memLp_mu_sub_AepsVecC ν ε μ hu).coeFn_toLp

/-- Conditional assembly of `RepsVecAdjointOfWeakEq` from `OuterSIsGenPairOnTestFieldVec`
and `MeridTestResolventDense`. -/
theorem repsVecAdjointOfWeakEq_of
    (hOuter : OuterSIsGenPairOnTestFieldVec)
    (hDense : MeridTestResolventDense) :
    RepsVecAdjointOfWeakEq :=
  repsVecAdjointOfWeakEq_of_left_and_ortho (repsVec_left_of_outerS hOuter) hDense

end UnforcedLeray.Short.PartIIa
