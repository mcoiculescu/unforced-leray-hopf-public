import UnforcedLeray.Short.PartIIa.Sub.N02

/-!


Source of record: `the November 2 reference manuscript`, lines 1730-1732
("the second lifts to a Cartesian gradient"). Specification: `NearGradMember` in
`Short/PartII-a/Sub/N02.lean`.

Proof outline. For a complex band potential `Φ = Φ₁ + i Φ₂` the real and imaginary parts
`Φ₁ = reP Φ`, `Φ₂ = imP Φ` are real `IsProfileTest`s, and the complex `ε`-gradient splits pointwise,
`cgradC ε Φ = cgrad ε Φ₁ + i • cgrad ε Φ₂` (`cgradC_eq_add`). Each real `cgrad ε Φ_k` is a
`L²(measureH c)` function (continuous, vanishing off the band; `memLp_cgrad`), and its class is a
generator of the span whose double orthogonal complement is `(solenoidalHC ε c)ᗮ`
(`gen_mem_orth`). The class of `cgradC ε Φ` is then a `ℂ`-linear combination of two members.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa.NearGradMemberAux

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-- Real part of a complex profile function. -/
def reP (Φ : Profile → ℂ) : Profile → ℝ := fun p => (Φ p).re

/-- Imaginary part of a complex profile function. -/
def imP (Φ : Profile → ℂ) : Profile → ℝ := fun p => (Φ p).im

/-- The derivative of a complex function splits into the derivatives of its real and imaginary
parts. -/
theorem fderiv_re_im {Φ : Profile → ℂ} {p : Profile} (hd : DifferentiableAt ℝ Φ p) (v : Profile) :
    fderiv ℝ Φ p v =
      ((fderiv ℝ (reP Φ) p v : ℝ) : ℂ) + ((fderiv ℝ (imP Φ) p v : ℝ) : ℂ) * Complex.I := by
  have hre : HasFDerivAt (reP Φ) (Complex.reCLM.comp (fderiv ℝ Φ p)) p :=
    Complex.reCLM.hasFDerivAt.comp p hd.hasFDerivAt
  have him : HasFDerivAt (imP Φ) (Complex.imCLM.comp (fderiv ℝ Φ p)) p :=
    Complex.imCLM.hasFDerivAt.comp p hd.hasFDerivAt
  rw [hre.fderiv, him.fderiv]
  simp only [ContinuousLinearMap.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply]
  exact (Complex.re_add_im _).symm

/-- The real part of a complex band test is a real band test. -/
theorem isProfileTest_reP {c : ℝ} {Φ : Profile → ℂ} (hΦ : IsCTest c Φ) :
    IsProfileTest c (reP Φ) where
  smooth := Complex.reCLM.contDiff.comp hΦ.smooth
  periodic := fun p => congrArg Complex.re (hΦ.periodic p)
  band := by
    obtain ⟨s0, s1, L, hs0, hb⟩ := hΦ.band
    exact ⟨s0, s1, L, hs0, fun p hp => hb p (fun h => hp (by simp [reP, h]))⟩

/-- The imaginary part of a complex band test is a real band test. -/
theorem isProfileTest_imP {c : ℝ} {Φ : Profile → ℂ} (hΦ : IsCTest c Φ) :
    IsProfileTest c (imP Φ) where
  smooth := Complex.imCLM.contDiff.comp hΦ.smooth
  periodic := fun p => congrArg Complex.im (hΦ.periodic p)
  band := by
    obtain ⟨s0, s1, L, hs0, hb⟩ := hΦ.band
    exact ⟨s0, s1, L, hs0, fun p hp => hb p (fun h => hp (by simp [imP, h]))⟩

/-- Pointwise splitting of the complex `ε`-gradient into real parts. -/
theorem cgradC_eq_add {ε : ℝ} {Φ : Profile → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (p : Profile) :
    cgradC ε Φ p = cgrad ε (reP Φ) p + Complex.I • cgrad ε (imP Φ) p := by
  have hd : DifferentiableAt ℝ Φ p := (hΦ.differentiable (by simp)) p
  have hS := fderiv_re_im hd (1, 0, 0)
  have hQ := fderiv_re_im hd (0, 1, 0)
  have hE := fderiv_re_im hd (0, 0, 1)
  ext i
  fin_cases i
  · simp only [cgradC, cgrad, pdQ, pdS, pdEta, opK, opS, Deps, Kop, Axi.dS, Axi.dQ, Axi.dEta,
      hS, hQ, hE, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Complex.real_smul,
      PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Fin.zero_eta, Fin.mk_one, Fin.isValue]
    push_cast
    ring
  · simp only [cgradC, cgrad, pdEta, Axi.dEta, hE, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Fin.zero_eta, Fin.mk_one, Fin.isValue]
    ring

/-- Continuity of a vector built from two continuous complex functions. -/
theorem continuous_mk {a b : Profile → ℂ} (ha : Continuous a) (hb : Continuous b) :
    Continuous fun p : Profile => (!₂[a p, b p] : MeridC) := by
  have h : Continuous fun p : Profile => (![a p, b p] : Fin 2 → ℂ) := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · simpa using ha
    · simpa using hb
  exact (PiLp.continuous_toLp _ _).comp h

/-- The real `ε`-gradient of a smooth function is continuous. -/
theorem continuous_cgrad (ε : ℝ) {R : Profile → ℝ} (hR : ContDiff ℝ ∞ R) :
    Continuous (cgrad ε R) := by
  have hD : Continuous fun p => fderiv ℝ R p := hR.continuous_fderiv (by simp)
  have h1 : ∀ v : Profile, Continuous fun p => fderiv ℝ R p v := fun v =>
    hD.clm_apply continuous_const
  have hA : Continuous fun p => Deps ε R p := by
    unfold Deps Kop Axi.dS Axi.dQ Axi.dEta
    fun_prop
  have hB : Continuous fun p => Axi.dEta R p := by
    unfold Axi.dEta
    fun_prop
  unfold cgrad
  exact continuous_mk (Complex.continuous_ofReal.comp hA) (Complex.continuous_ofReal.comp hB)

/-- The real `ε`-gradient vanishes outside the support of the potential. -/
theorem cgrad_eq_zero_of_notMem {ε : ℝ} {R : Profile → ℝ} {p : Profile}
    (hp : p ∉ tsupport R) : cgrad ε R p = 0 := by
  have h := fderiv_of_notMem_tsupport ℝ hp
  ext i
  fin_cases i <;> simp [cgrad, Deps, Kop, Axi.dS, Axi.dQ, Axi.dEta, h]

/-- A continuous function supported in the band `s0 ≤ s ≤ s1`, `|η| ≤ L` is in `L²(measureH c)`. -/
theorem memLp_of_band {c s0 s1 L : ℝ} {E : Type*} [NormedAddCommGroup E]
    [SecondCountableTopologyEither Profile E] {f : Profile → E} (hf : Continuous f)
    (hs0 : 0 < s0) (hz : ∀ p : Profile, ¬(p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) → f p = 0) :
    MemLp f 2 (measureH c) := by
  refine memLp_of_continuous_of_ae_vanish hf
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)) (measureH_band_ne_top c hs0 s1 L) ?_ 2
  filter_upwards [ae_cell_measureH c] with p hp hpA
  apply hz p
  intro hb
  exact hpA ⟨hb.1, Ioc_subset_Icc_self hp.2.1, abs_le.1 hb.2⟩

/-- The real `ε`-gradient of a real band test is in `L²(measureH c)`. -/
theorem memLp_cgrad {c ε : ℝ} {R : Profile → ℝ} (hR : IsProfileTest c R) :
    MemLp (cgrad ε R) 2 (measureH c) := by
  obtain ⟨s0, s1, L, hs0, hb⟩ := hR.band
  refine memLp_of_band (c := c) (s0 := s0) (s1 := s1) (L := L)
    (continuous_cgrad ε hR.smooth) hs0 ?_
  intro p hp
  apply cgrad_eq_zero_of_notMem
  intro hmem
  exact hp (tsupport_subset_band hb hmem)

/-- The class of a real `ε`-gradient of a real band test is a generator of `span ℂ`, hence lies in
`(solenoidalHC ε c)ᗮ`, because `(solenoidalHC ε c)ᗮ` is the double orthogonal complement of that
span. -/
theorem gen_mem_orth {ε c : ℝ} {R : Profile → ℝ} (hR : IsProfileTest c R)
    (hm : MemLp (cgrad ε R) 2 (measureH c)) :
    hm.toLp (cgrad ε R) ∈ (solenoidalHC ε c)ᗮ := by
  show _ ∈ (Submodule.span ℂ _)ᗮᗮ
  exact Submodule.le_orthogonal_orthogonal _ (Submodule.subset_span ⟨⟨R, hR⟩, hm, rfl⟩)

end UnforcedLeray.Short.PartIIa.NearGradMemberAux

namespace UnforcedLeray.Short.PartIIa

open NearGradMemberAux
open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-- **`ε`-gradients of band potentials lie in the closed span of gradients** (target
`nearGradMember_proof` for the Prop `NearGradMember`, tex lines 1730-1732). -/
theorem nearGradMember_proof : UnforcedLeray.Short.PartIIa.NearGradMember := by
  intro ε c Φ hΦ
  have hR : IsProfileTest c (reP Φ) := isProfileTest_reP hΦ
  have hJ : IsProfileTest c (imP Φ) := isProfileTest_imP hΦ
  have h1 : MemLp (cgrad ε (reP Φ)) 2 (measureH c) := memLp_cgrad hR
  have h2 : MemLp (cgrad ε (imP Φ)) 2 (measureH c) := memLp_cgrad hJ
  have hfg : (cgrad ε (reP Φ) + Complex.I • cgrad ε (imP Φ)) =ᵐ[measureH c] cgradC ε Φ :=
    Filter.Eventually.of_forall fun p => (cgradC_eq_add hΦ.smooth p).symm
  have hmC : MemLp (cgradC ε Φ) 2 (measureH c) :=
    MemLp.ae_eq hfg (h1.add (h2.const_smul Complex.I))
  refine ⟨hmC, ?_⟩
  have hfun : cgradC ε Φ =ᵐ[measureH c] (cgrad ε (reP Φ) + Complex.I • cgrad ε (imP Φ)) :=
    Filter.Eventually.of_forall fun p => cgradC_eq_add hΦ.smooth p
  have hEq : hmC.toLp (cgradC ε Φ) =
      h1.toLp (cgrad ε (reP Φ)) + Complex.I • h2.toLp (cgrad ε (imP Φ)) := by
    rw [MemLp.toLp_congr hmC (h1.add (h2.const_smul Complex.I)) hfun,
      MemLp.toLp_add h1 (h2.const_smul Complex.I), MemLp.toLp_const_smul Complex.I h2]
  rw [hEq]
  exact Submodule.add_mem _ (gen_mem_orth hR h1)
    (Submodule.smul_mem _ _ (gen_mem_orth hJ h2))

end UnforcedLeray.Short.PartIIa
