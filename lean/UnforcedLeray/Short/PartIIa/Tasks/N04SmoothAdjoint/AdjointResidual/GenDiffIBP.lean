import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N04_3
import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.GradDiffIBP
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.IbpQCell

/-!


Source of record: `the November 2 reference manuscript`,
lines 1838–1840.

Target: `theorem genDiffIBP : GenDiffIBP` (`Sub/PartII-a_N04_3.lean`).
For a smooth meridional test `u` (`IsMeridTest c u`) and `v : Profile → MeridC` smooth on
`{p | 0 < p.1}` and `c`-periodic in `q` with `genDiff1 ν v, genDiff2 ν v ∈ L²(measureH c)`,
`⟨genDiffC ν ε u, V⟩_H = ⟨U, genDiffC ν ε v⟩_H`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226
open N04GradDiffIBPAux

namespace N04GenDiffIBPAux

/-- Conjugated component `p ↦ conj (u p i)` of a meridional profile. -/
def uConj (u : Profile → MeridC) (i : Fin 2) : Profile → ℂ :=
  fun p => starRingEnd ℂ (u p i)

theorem contDiff_comp_merid (u : Profile → MeridC) (hu : ContDiff ℝ ∞ u) (i : Fin 2) :
    ContDiff ℝ ∞ (fun p => u p i) :=
  ((EuclideanSpace.proj i : MeridC →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp hu

theorem isCTest_uConj {c : ℝ} {u : Profile → MeridC} (hu : IsMeridTest c u) (i : Fin 2) :
    IsCTest c (uConj u i) where
  smooth := Complex.conjCLE.contDiff.comp (contDiff_comp_merid u hu.smooth i)
  periodic := fun p => by simp only [uConj, hu.periodic p]
  band := by
    obtain ⟨s0, s1, L, hs0, hband⟩ := hu.band
    refine ⟨s0, s1, L, hs0, fun p hp => hband p fun h0 => hp ?_⟩
    simp [uConj, h0]

theorem contDiffOn_pd {g : Profile → ℂ} (hg : ContDiffOn ℝ ∞ g {p : Profile | 0 < p.1})
    (dir : Profile) :
    ContDiffOn ℝ ∞ (fun p => fderiv ℝ g p dir) {p : Profile | 0 < p.1} := by
  have hopen : IsOpen {p : Profile | 0 < p.1} := isOpen_lt continuous_const continuous_fst
  intro p hp
  have hcd : ContDiffAt ℝ ∞ g p := hg.contDiffAt (hopen.mem_nhds hp)
  exact (((hcd.fderiv_right (by simp)).clm_apply contDiffAt_const).contDiffWithinAt)

theorem contDiffOn_opLam {g : Profile → ℂ} (hg : ContDiffOn ℝ ∞ g {p : Profile | 0 < p.1}) :
    ContDiffOn ℝ ∞ (opLam g) {p : Profile | 0 < p.1} := by
  have hfun : opLam g = fun p =>
      (p.1 : ℂ) * ((2 : ℂ) * pdS g p) + (p.2.2 : ℂ) * pdEta g p + g p := by
    funext p
    rw [opLam, NearStreamMemberAux.opK_eq]
  rw [hfun]
  have hs : ContDiffOn ℝ ∞ (fun p : Profile => (p.1 : ℂ)) {p : Profile | 0 < p.1} :=
    (Complex.ofRealCLM.contDiff.comp contDiff_fst).contDiffOn
  have heta : ContDiffOn ℝ ∞ (fun p : Profile => (p.2.2 : ℂ)) {p : Profile | 0 < p.1} :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_snd.comp contDiff_snd)).contDiffOn
  have hS : ContDiffOn ℝ ∞ (pdS g) {p : Profile | 0 < p.1} := contDiffOn_pd hg (1, 0, 0)
  have hE : ContDiffOn ℝ ∞ (pdEta g) {p : Profile | 0 < p.1} := contDiffOn_pd hg (0, 0, 1)
  exact ((hs.mul (contDiffOn_const.mul hS)).add (heta.mul hE)).add hg

theorem fderiv_qPeriodic {c : ℝ} {g : Profile → ℂ} (hper : QPeriodic c g)
    (dir p : Profile) :
    fderiv ℝ g (p.1, p.2.1 + c, p.2.2) dir = fderiv ℝ g p dir := by
  have h1 : (fun x : Profile => g (x + (0, c, 0))) = g := by
    funext x
    have e : x + ((0 : ℝ), c, (0 : ℝ)) = (x.1, x.2.1 + c, x.2.2) := by ext <;> simp
    rw [e, hper x]
  have h2 : fderiv ℝ (fun x : Profile => g (x + (0, c, 0))) p = fderiv ℝ g (p + (0, c, 0)) :=
    fderiv_comp_add_right _
  rw [h1] at h2
  have e : p + ((0 : ℝ), c, (0 : ℝ)) = (p.1, p.2.1 + c, p.2.2) := by ext <;> simp
  rw [e] at h2
  exact congrArg (fun L => L dir) h2.symm

theorem qPeriodic_pd {c : ℝ} {g : Profile → ℂ} (hper : QPeriodic c g) (dir : Profile) :
    QPeriodic c (fun p => fderiv ℝ g p dir) :=
  fun p => fderiv_qPeriodic hper dir p

theorem qPeriodic_opLam {c : ℝ} {g : Profile → ℂ} (hper : QPeriodic c g) :
    QPeriodic c (opLam g) := by
  intro p
  have hS := fderiv_qPeriodic hper (1, 0, 0) p
  have hE := fderiv_qPeriodic hper (0, 0, 1) p
  have hg := hper p
  change opK g (p.1, p.2.1 + c, p.2.2) + g (p.1, p.2.1 + c, p.2.2) = opK g p + g p
  rw [NearStreamMemberAux.opK_eq, NearStreamMemberAux.opK_eq]
  change (p.1 : ℂ) * (2 * fderiv ℝ g (p.1, p.2.1 + c, p.2.2) (1, 0, 0)) +
      (p.2.2 : ℂ) * fderiv ℝ g (p.1, p.2.1 + c, p.2.2) (0, 0, 1) + g (p.1, p.2.1 + c, p.2.2) =
    (p.1 : ℂ) * (2 * fderiv ℝ g p (1, 0, 0)) +
      (p.2.2 : ℂ) * fderiv ℝ g p (0, 0, 1) + g p
  rw [hS, hE, hg]

/-- `starRingEnd ℂ` commutes with directional derivatives on smooth complex profiles. -/
theorem star_pd {f : Profile → ℂ} (hf : ContDiff ℝ ∞ f) (dir p : Profile) :
    starRingEnd ℂ (fderiv ℝ f p dir) = fderiv ℝ (fun q => starRingEnd ℂ (f q)) p dir := by
  have hd : DifferentiableAt ℝ f p := (hf.differentiable (by simp)) p
  have h : HasFDerivAt (fun q => starRingEnd ℂ (f q))
      (Complex.conjCLE.toContinuousLinearMap.comp (fderiv ℝ f p)) p :=
    Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp p hd.hasFDerivAt
  rw [h.fderiv]
  rfl

/-- `pdQ` commutes with `opLam` on smooth complex profiles. -/
theorem pdQ_opLam_eq {f : Profile → ℂ} (hf : ContDiff ℝ ∞ f) (p : Profile) :
    pdQ (opLam f) p = opLam (pdQ f) p := by
  have hfun : opLam f = fun x =>
      (x.1 : ℂ) * (2 * pdS f x) + (x.2.2 : ℂ) * pdEta f x + f x := by
    funext x
    rw [opLam, NearStreamMemberAux.opK_eq]
  have h2 : Differentiable ℝ (fun x => (2 : ℂ) * pdS f x) :=
    (NearStreamMemberAux.differentiable_fderiv_apply hf (1, 0, 0)).const_mul 2
  have h4 : Differentiable ℝ (pdEta f) :=
    NearStreamMemberAux.differentiable_fderiv_apply hf (0, 0, 1)
  have h1 : DifferentiableAt ℝ (fun x : Profile => (x.1 : ℂ) * (2 * pdS f x)) p :=
    (NearStreamMemberAux.hasFDerivAt_ofReal_fst p).differentiableAt.mul (h2 p)
  have h3 : DifferentiableAt ℝ (fun x : Profile => (x.2.2 : ℂ) * pdEta f x) p :=
    (NearStreamMemberAux.hasFDerivAt_ofReal_snd_snd p).differentiableAt.mul (h4 p)
  have hdf : DifferentiableAt ℝ f p := (hf.differentiable (by simp)) p
  have e1 := NearStreamMemberAux.fderiv_fst_mul h2 p (0, 1, 0)
  have e3 := NearStreamMemberAux.fderiv_snd_snd_mul h4 p (0, 1, 0)
  have hdS : DifferentiableAt ℝ (pdS f) p :=
    NearStreamMemberAux.differentiable_fderiv_apply hf (1, 0, 0) p
  have e2 : fderiv ℝ (fun x => (2 : ℂ) * pdS f x) p (0, 1, 0) = 2 * pdQ (pdS f) p := by
    rw [fderiv_const_mul hdS 2]
    simp only [smul_apply, smul_eq_mul]
    rfl
  have hcS : pdQ (pdS f) p = pdS (pdQ f) p :=
    NearStreamMemberAux.fderiv_comm_apply hf (0, 1, 0) (1, 0, 0) p
  have hcE : pdQ (pdEta f) p = pdEta (pdQ f) p :=
    NearStreamMemberAux.pdQ_pdEta_comm hf p
  rw [hfun]
  show fderiv ℝ (fun x : Profile =>
      ((x.1 : ℂ) * (2 * pdS f x) + (x.2.2 : ℂ) * pdEta f x) + f x) p (0, 1, 0) =
    opLam (pdQ f) p
  have hA : HasFDerivAt (fun x : Profile =>
      ((x.1 : ℂ) * (2 * pdS f x) + (x.2.2 : ℂ) * pdEta f x) + f x)
      ((fderiv ℝ (fun x : Profile => (x.1 : ℂ) * (2 * pdS f x)) p +
        fderiv ℝ (fun x : Profile => (x.2.2 : ℂ) * pdEta f x) p) + fderiv ℝ f p) p :=
    (h1.hasFDerivAt.add h3.hasFDerivAt).add hdf.hasFDerivAt
  rw [hA.fderiv, add_apply, add_apply, e1, e3, e2, hcS,
    show (fderiv ℝ (pdEta f) p) (0, 1, 0) = pdQ (pdEta f) p from rfl, hcE,
    show (fderiv ℝ f p) (0, 1, 0) = pdQ f p from rfl,
    opLam, NearStreamMemberAux.opK_eq (pdQ f) p]
  simp only [Complex.ofReal_zero, zero_mul, add_zero]

/-- Product rule for `pdQ (s f g)`: since `pdQ s = 0`,
`pdQ (s f g) = s (pdQ f) g + s f (pdQ g)`. -/
theorem pdQ_s_mul_mul {f g : Profile → ℂ} {p : Profile}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) :
    pdQ (fun x : Profile => (x.1 : ℂ) * f x * g x) p =
      (p.1 : ℂ) * pdQ f p * g p + (p.1 : ℂ) * f p * pdQ g p := by
  have hs : DifferentiableAt ℝ (fun x : Profile => (x.1 : ℂ)) p :=
    (NearStreamMemberAux.hasFDerivAt_ofReal_fst p).differentiableAt
  have hsf : DifferentiableAt ℝ (fun x : Profile => (x.1 : ℂ) * f x) p := hs.mul hf
  have h1 := NearStreamMemberAux.fderiv_mul_apply' (fun x : Profile => (x.1 : ℂ) * f x) g
    (0, 1, 0) p hsf hg
  have h2 := NearStreamMemberAux.fderiv_mul_apply' (fun x : Profile => (x.1 : ℂ)) f
    (0, 1, 0) p hs hf
  rw [NearStreamMemberAux.fderiv_ofReal_fst_apply] at h2
  unfold pdQ
  rw [h1, h2]
  simp only [Complex.ofReal_zero]
  ring

/-- Pointwise identity for `genDiff1` component on `s > 0`:
`s (opLam (pdQ f)) g = s f (opLam (pdQ g)) + pdQ (s (opLam f) g) - opK (s f (pdQ g))`. -/
theorem s_opLam_pdQ_mul_eq {f g : Profile → ℂ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiffOn ℝ ∞ g {p : Profile | 0 < p.1}) {p : Profile} (hp : 0 < p.1) :
    (p.1 : ℂ) * opLam (pdQ f) p * g p =
      (p.1 : ℂ) * f p * opLam (pdQ g) p +
        pdQ (fun x => (x.1 : ℂ) * opLam f x * g x) p -
        opK (fun x => (x.1 : ℂ) * f x * pdQ g x) p := by
  have hopen : IsOpen {q : Profile | 0 < q.1} := isOpen_lt continuous_const continuous_fst
  have hdf : DifferentiableAt ℝ f p := (hf.differentiable (by simp)) p
  have hdLamf : DifferentiableAt ℝ (opLam f) p :=
    (NearStreamMemberAux.differentiable_opK hf p).add hdf
  have hdg : DifferentiableAt ℝ g p :=
    (hg.contDiffAt (hopen.mem_nhds hp)).differentiableAt (by simp)
  have hdQg : DifferentiableAt ℝ (pdQ g) p :=
    ((contDiffOn_pd hg (0, 1, 0)).contDiffAt (hopen.mem_nhds hp)).differentiableAt (by simp)
  have hQ := pdQ_s_mul_mul hdLamf hdg
  have hK := opK_s_mul_mul hdf hdQg
  have hcomm := pdQ_opLam_eq hf p
  rw [hQ, hK, hcomm]
  ring

/-- Pointwise identity for `genDiff2` `Λ²` component on `s > 0`:
`s (opLam (opLam f)) g = s f (opLam (opLam g)) + opK (s (opLam f) g) - opK (s f (opLam g))`. -/
theorem s_opLam_opLam_mul_eq {f g : Profile → ℂ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiffOn ℝ ∞ g {p : Profile | 0 < p.1}) {p : Profile} (hp : 0 < p.1) :
    (p.1 : ℂ) * opLam (opLam f) p * g p =
      (p.1 : ℂ) * f p * opLam (opLam g) p +
        opK (fun x => (x.1 : ℂ) * opLam f x * g x) p -
        opK (fun x => (x.1 : ℂ) * f x * opLam g x) p := by
  have hopen : IsOpen {q : Profile | 0 < q.1} := isOpen_lt continuous_const continuous_fst
  have hdf : DifferentiableAt ℝ f p := (hf.differentiable (by simp)) p
  have hdLamf : DifferentiableAt ℝ (opLam f) p :=
    (NearStreamMemberAux.differentiable_opK hf p).add hdf
  have hdg : DifferentiableAt ℝ g p :=
    (hg.contDiffAt (hopen.mem_nhds hp)).differentiableAt (by simp)
  have hdLamg : DifferentiableAt ℝ (opLam g) p :=
    ((contDiffOn_opLam hg).contDiffAt (hopen.mem_nhds hp)).differentiableAt (by simp)
  have hK1 := opK_s_mul_mul hdLamf hdg
  have hK2 := opK_s_mul_mul hdf hdLamg
  rw [hK1, hK2]
  ring

/-- Cell integral identity for a single component of `genDiff1`:
`∫_{cell c} s^{-3/2} s (opLam (pdQ f)) g = ∫_{cell c} s^{-3/2} s f (opLam (pdQ g))`. -/
theorem cell_integral_opLam_pdQ_eq {c : ℝ} (f g : Profile → ℂ) (hf : IsCTest c f)
    (hg : ContDiffOn ℝ ∞ g {p : Profile | 0 < p.1}) (hper : QPeriodic c g) :
    ∫ p in cell c, ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * ((p.1 : ℂ) * opLam (pdQ f) p * g p) =
      ∫ p in cell c, ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * ((p.1 : ℂ) * f p * opLam (pdQ g) p) := by
  have hcd_Qg : ContDiffOn ℝ ∞ (pdQ g) {p : Profile | 0 < p.1} := contDiffOn_pd hg (0, 1, 0)
  have hper_Qg : QPeriodic c (pdQ g) := qPeriodic_pd hper (0, 1, 0)
  have hcd_LamQg : ContDiffOn ℝ ∞ (opLam (pdQ g)) {p : Profile | 0 < p.1} :=
    contDiffOn_opLam hcd_Qg
  have hper_LamQg : QPeriodic c (opLam (pdQ g)) := qPeriodic_opLam hper_Qg
  have hR_test : IsCTest c (fun x => (x.1 : ℂ) * f x * opLam (pdQ g) x) :=
    isCTest_mul_of_contDiffOn (isCTest_s_mul hf) hcd_LamQg hper_LamQg
  have hF1 : IsCTest c (fun x => (x.1 : ℂ) * opLam f x * g x) :=
    isCTest_mul_of_contDiffOn (isCTest_s_mul (isCTest_opLam hf)) hg hper
  have hF2 : IsCTest c (fun x => (x.1 : ℂ) * f x * pdQ g x) :=
    isCTest_mul_of_contDiffOn (isCTest_s_mul hf) hcd_Qg hper_Qg
  have hint_R : IntegrableOn (fun p =>
      ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * ((p.1 : ℂ) * f p * opLam (pdQ g) p)) (cell c) :=
    (bandIntegrable c _ hR_test).2
  have hint_Q : IntegrableOn (fun p =>
      ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * pdQ (fun x => (x.1 : ℂ) * opLam f x * g x) p) (cell c) :=
    (bandIntegrable c _ (cTestFderiv c _ hF1 (0, 1, 0))).2
  have hint_K : IntegrableOn (fun p =>
      ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * opK (fun x => (x.1 : ℂ) * f x * pdQ g x) p) (cell c) :=
    (bandIntegrable c _ (cTestOpK c _ hF2)).2
  have hint_QK : IntegrableOn (fun p =>
      ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * pdQ (fun x => (x.1 : ℂ) * opLam f x * g x) p -
        ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * opK (fun x => (x.1 : ℂ) * f x * pdQ g x) p) (cell c) :=
    hint_Q.sub hint_K
  have hcongr : ∫ p in cell c,
        ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * ((p.1 : ℂ) * opLam (pdQ f) p * g p) =
      ∫ p in cell c,
        (((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * ((p.1 : ℂ) * f p * opLam (pdQ g) p) +
          (((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * pdQ (fun x => (x.1 : ℂ) * opLam f x * g x) p -
            ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * opK (fun x => (x.1 : ℂ) * f x * pdQ g x) p)) := by
    refine setIntegral_congr_fun (measurableSet_cell c) fun p hp => ?_
    rw [s_opLam_pdQ_mul_eq hf.smooth hg hp.1]
    ring
  rw [hcongr, integral_add hint_R hint_QK, integral_sub hint_Q hint_K,
    ibpQCell c _ hF1, ibpKCell c _ hF2]
  ring

/-- Cell integral identity for a single component of `genDiff2`:
`∫_{cell c} s^{-3/2} s (opLam (opLam f)) g = ∫_{cell c} s^{-3/2} s f (opLam (opLam g))`. -/
theorem cell_integral_opLam_opLam_eq {c : ℝ} (f g : Profile → ℂ) (hf : IsCTest c f)
    (hg : ContDiffOn ℝ ∞ g {p : Profile | 0 < p.1}) (hper : QPeriodic c g) :
    ∫ p in cell c, ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * ((p.1 : ℂ) * opLam (opLam f) p * g p) =
      ∫ p in cell c, ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * ((p.1 : ℂ) * f p * opLam (opLam g) p) := by
  have hcd_Lamg : ContDiffOn ℝ ∞ (opLam g) {p : Profile | 0 < p.1} := contDiffOn_opLam hg
  have hper_Lamg : QPeriodic c (opLam g) := qPeriodic_opLam hper
  have hcd_Lam2g : ContDiffOn ℝ ∞ (opLam (opLam g)) {p : Profile | 0 < p.1} :=
    contDiffOn_opLam hcd_Lamg
  have hper_Lam2g : QPeriodic c (opLam (opLam g)) := qPeriodic_opLam hper_Lamg
  have hR_test : IsCTest c (fun x => (x.1 : ℂ) * f x * opLam (opLam g) x) :=
    isCTest_mul_of_contDiffOn (isCTest_s_mul hf) hcd_Lam2g hper_Lam2g
  have hF1 : IsCTest c (fun x => (x.1 : ℂ) * opLam f x * g x) :=
    isCTest_mul_of_contDiffOn (isCTest_s_mul (isCTest_opLam hf)) hg hper
  have hF2 : IsCTest c (fun x => (x.1 : ℂ) * f x * opLam g x) :=
    isCTest_mul_of_contDiffOn (isCTest_s_mul hf) hcd_Lamg hper_Lamg
  have hint_R : IntegrableOn (fun p =>
      ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * ((p.1 : ℂ) * f p * opLam (opLam g) p)) (cell c) :=
    (bandIntegrable c _ hR_test).2
  have hint_K1 : IntegrableOn (fun p =>
      ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * opK (fun x => (x.1 : ℂ) * opLam f x * g x) p) (cell c) :=
    (bandIntegrable c _ (cTestOpK c _ hF1)).2
  have hint_K2 : IntegrableOn (fun p =>
      ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * opK (fun x => (x.1 : ℂ) * f x * opLam g x) p) (cell c) :=
    (bandIntegrable c _ (cTestOpK c _ hF2)).2
  have hint_K12 : IntegrableOn (fun p =>
      ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * opK (fun x => (x.1 : ℂ) * opLam f x * g x) p -
        ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * opK (fun x => (x.1 : ℂ) * f x * opLam g x) p) (cell c) :=
    hint_K1.sub hint_K2
  have hcongr : ∫ p in cell c,
        ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * ((p.1 : ℂ) * opLam (opLam f) p * g p) =
      ∫ p in cell c,
        (((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * ((p.1 : ℂ) * f p * opLam (opLam g) p) +
          (((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * opK (fun x => (x.1 : ℂ) * opLam f x * g x) p -
            ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * opK (fun x => (x.1 : ℂ) * f x * opLam g x) p)) := by
    refine setIntegral_congr_fun (measurableSet_cell c) fun p hp => ?_
    rw [s_opLam_opLam_mul_eq hf.smooth hg hp.1]
    ring
  rw [hcongr, integral_add hint_R hint_K12, integral_sub hint_K1 hint_K2,
    ibpKCell c _ hF1, ibpKCell c _ hF2]
  ring

theorem proj_fderiv_merid {w : Profile → MeridC} {p : Profile}
    (hw : DifferentiableAt ℝ w p) (dir : Profile) (i : Fin 2) :
    (fderiv ℝ w p dir) i = fderiv ℝ (fun q => w q i) p dir := by
  let L : MeridC →L[ℝ] ℂ := (EuclideanSpace.proj i : MeridC →L[ℂ] ℂ).restrictScalars ℝ
  have h : HasFDerivAt (fun q => L (w q)) (L.comp (fderiv ℝ w p)) p :=
    L.hasFDerivAt.comp p hw.hasFDerivAt
  exact (congrArg (fun M => M dir) h.fderiv).symm

theorem proj_opLam_merid {w : Profile → MeridC} {p : Profile}
    (hw : DifferentiableAt ℝ w p) (i : Fin 2) :
    (opLam w p) i = opLam (fun q => w q i) p := by
  simp only [opLam, opK, opS, pdS, pdEta, PiLp.add_apply, PiLp.smul_apply,
    Complex.real_smul, proj_fderiv_merid hw]

theorem proj_opLam_pdQ_merid {w : Profile → MeridC} {p : Profile}
    (hw : ContDiffAt ℝ ∞ w p) (i : Fin 2) :
    (opLam (pdQ w) p) i = opLam (pdQ (fun q => w q i)) p := by
  have hdQw : DifferentiableAt ℝ (pdQ w) p :=
    ((hw.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).differentiableAt (by simp)
  rw [proj_opLam_merid hdQw i]
  have hev : (fun q => pdQ w q i) =ᶠ[nhds p] pdQ (fun q => w q i) := by
    filter_upwards [(hw.of_le (m := 2) (by simp)).eventually (by simp)] with q hq
    exact proj_fderiv_merid (hq.differentiableAt (by norm_num)) (0, 1, 0) i
  change (2 : ℝ) • p.1 • fderiv ℝ (fun q => pdQ w q i) p (1, 0, 0) +
      p.2.2 • fderiv ℝ (fun q => pdQ w q i) p (0, 0, 1) + (fun q => pdQ w q i) p =
    (2 : ℝ) • p.1 • fderiv ℝ (pdQ (fun q => w q i)) p (1, 0, 0) +
      p.2.2 • fderiv ℝ (pdQ (fun q => w q i)) p (0, 0, 1) + pdQ (fun q => w q i) p
  rw [hev.fderiv_eq, hev.self_of_nhds]

theorem proj_opLam_opLam_merid {w : Profile → MeridC} {p : Profile}
    (hw : ContDiffAt ℝ ∞ w p) (i : Fin 2) :
    (opLam (opLam w) p) i = opLam (opLam (fun q => w q i)) p := by
  have hdSw : ContDiffAt ℝ ∞ (pdS w) p :=
    (hw.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const
  have hdEw : ContDiffAt ℝ ∞ (pdEta w) p :=
    (hw.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const
  have hdLamw : DifferentiableAt ℝ (opLam w) p := by
    have h1 : DifferentiableAt ℝ (opS w) p :=
      differentiableAt_fst.smul (hdSw.differentiableAt (by simp))
    have hsnd : DifferentiableAt ℝ (fun q : Profile => q.2.2) p :=
      differentiableAt_snd.comp p differentiableAt_snd
    have h2 : DifferentiableAt ℝ (opK w) p :=
      (h1.const_smul (2 : ℝ)).add (hsnd.smul (hdEw.differentiableAt (by simp)))
    exact h2.add (hw.differentiableAt (by simp))
  rw [proj_opLam_merid hdLamw i]
  have hev : (fun q => opLam w q i) =ᶠ[nhds p] opLam (fun q => w q i) := by
    filter_upwards [(hw.of_le (m := 2) (by simp)).eventually (by simp)] with q hq
    exact proj_opLam_merid (hq.differentiableAt (by norm_num)) i
  change (2 : ℝ) • p.1 • fderiv ℝ (fun q => opLam w q i) p (1, 0, 0) +
      p.2.2 • fderiv ℝ (fun q => opLam w q i) p (0, 0, 1) + (fun q => opLam w q i) p =
    (2 : ℝ) • p.1 • fderiv ℝ (opLam (fun q => w q i)) p (1, 0, 0) +
      p.2.2 • fderiv ℝ (opLam (fun q => w q i)) p (0, 0, 1) + opLam (fun q => w q i) p
  rw [hev.fderiv_eq, hev.self_of_nhds]

theorem star_opLam_pdQ_merid {u : Profile → MeridC} (hu : ContDiff ℝ ∞ u)
    (p : Profile) (i : Fin 2) :
    starRingEnd ℂ ((opLam (pdQ u) p) i) = opLam (pdQ (uConj u i)) p := by
  have hui : ContDiff ℝ ∞ (fun q => u q i) := contDiff_comp_merid u hu i
  have hdQu : ContDiff ℝ ∞ (pdQ (fun q => u q i)) :=
    NearStreamMemberAux.contDiff_fderiv_apply hui (0, 1, 0)
  rw [proj_opLam_pdQ_merid hu.contDiffAt i, star_opLam hdQu p]
  have heq : (fun q => starRingEnd ℂ (pdQ (fun x => u x i) q)) = pdQ (uConj u i) := by
    funext q
    exact star_pd hui (0, 1, 0) q
  rw [heq]

theorem star_opLam_opLam_merid {u : Profile → MeridC} (hu : ContDiff ℝ ∞ u)
    (p : Profile) (i : Fin 2) :
    starRingEnd ℂ ((opLam (opLam u) p) i) = opLam (opLam (uConj u i)) p := by
  have hui : ContDiff ℝ ∞ (fun q => u q i) := contDiff_comp_merid u hu i
  have hLam_ui : ContDiff ℝ ∞ (opLam (fun q => u q i)) := by
    have hfun : opLam (fun q => u q i) = fun q =>
        (q.1 : ℂ) * ((2 : ℂ) * pdS (fun x => u x i) q) +
          (q.2.2 : ℂ) * pdEta (fun x => u x i) q + u q i := by
      funext q
      rw [opLam, NearStreamMemberAux.opK_eq]
    rw [hfun]
    have hs : ContDiff ℝ ∞ (fun q : Profile => (q.1 : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp contDiff_fst
    have heta : ContDiff ℝ ∞ (fun q : Profile => (q.2.2 : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_snd.comp contDiff_snd)
    exact ((hs.mul (contDiff_const.mul
        (NearStreamMemberAux.contDiff_fderiv_apply hui (1, 0, 0)))).add
      (heta.mul (NearStreamMemberAux.contDiff_fderiv_apply hui (0, 0, 1)))).add hui
  rw [proj_opLam_opLam_merid hu.contDiffAt i, star_opLam hLam_ui p]
  have heq : (fun q => starRingEnd ℂ (opLam (fun x => u x i) q)) = opLam (uConj u i) := by
    funext q
    exact star_opLam hui q
  rw [heq]

theorem inner_genDiff1_lhs (ν : ℝ) {u v : Profile → MeridC} (hu : ContDiff ℝ ∞ u) (p : Profile) :
    inner ℂ (genDiff1 ν u p) (v p) =
      (ν : ℂ) * ((p.1 : ℂ) * opLam (pdQ (uConj u 0)) p * v p 0 +
        (p.1 : ℂ) * opLam (pdQ (uConj u 1)) p * v p 1) := by
  have h0 := star_opLam_pdQ_merid hu p 0
  have h1 := star_opLam_pdQ_merid hu p 1
  simp [genDiff1, PiLp.inner_apply, Fin.sum_univ_two, Complex.real_smul, h0, h1]
  ring

theorem inner_genDiff1_rhs (ν : ℝ) {u v : Profile → MeridC}
    (hv : ContDiffOn ℝ ∞ v {p : Profile | 0 < p.1}) {p : Profile} (hp : 0 < p.1) :
    inner ℂ (u p) (genDiff1 ν v p) =
      (ν : ℂ) * ((p.1 : ℂ) * uConj u 0 p * opLam (pdQ (fun q => v q 0)) p +
        (p.1 : ℂ) * uConj u 1 p * opLam (pdQ (fun q => v q 1)) p) := by
  have hcd : ContDiffAt ℝ ∞ v p :=
    hv.contDiffAt ((isOpen_lt continuous_const continuous_fst).mem_nhds hp)
  have h0 := proj_opLam_pdQ_merid hcd 0
  have h1 := proj_opLam_pdQ_merid hcd 1
  simp [genDiff1, PiLp.inner_apply, Fin.sum_univ_two, Complex.real_smul, h0, h1, uConj]
  ring

theorem inner_genDiff2_lhs (ν : ℝ) {u v : Profile → MeridC} (hu : ContDiff ℝ ∞ u) (p : Profile) :
    inner ℂ (genDiff2 ν u p) (v p) =
      (ν : ℂ) * (((p.1 : ℂ) * opLam (opLam (uConj u 0)) p * v p 0 +
        (p.1 : ℂ) * opLam (opLam (uConj u 1)) p * v p 1) -
        (p.1 : ℂ) * uConj u 0 p * v p 0) := by
  have h0 := star_opLam_opLam_merid hu p 0
  have h1 := star_opLam_opLam_merid hu p 1
  simp only [genDiff2, opE, PiLp.inner_apply, Fin.sum_univ_two, PiLp.smul_apply,
    PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, RCLike.inner_apply, Complex.real_smul, Complex.ofReal_mul,
    map_mul, map_sub, map_zero, Complex.conj_ofReal, h0, h1]
  unfold uConj
  ring

theorem inner_genDiff2_rhs (ν : ℝ) {u v : Profile → MeridC}
    (hv : ContDiffOn ℝ ∞ v {p : Profile | 0 < p.1}) {p : Profile} (hp : 0 < p.1) :
    inner ℂ (u p) (genDiff2 ν v p) =
      (ν : ℂ) * (((p.1 : ℂ) * uConj u 0 p * opLam (opLam (fun q => v q 0)) p +
        (p.1 : ℂ) * uConj u 1 p * opLam (opLam (fun q => v q 1)) p) -
        (p.1 : ℂ) * uConj u 0 p * v p 0) := by
  have hcd : ContDiffAt ℝ ∞ v p :=
    hv.contDiffAt ((isOpen_lt continuous_const continuous_fst).mem_nhds hp)
  have h0 := proj_opLam_opLam_merid hcd 0
  have h1 := proj_opLam_opLam_merid hcd 1
  simp only [genDiff2, opE, PiLp.inner_apply, Fin.sum_univ_two, PiLp.smul_apply,
    PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, RCLike.inner_apply, Complex.real_smul, Complex.ofReal_mul, h0, h1]
  unfold uConj
  ring

theorem cell_integral_genDiff1_eq {c : ℝ} (ν : ℝ) {u v : Profile → MeridC}
    (hu : IsMeridTest c u) (hv : ContDiffOn ℝ ∞ v {p : Profile | 0 < p.1})
    (hper : QPeriodic c v) :
    ∫ p in cell c, ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * inner ℂ (genDiff1 ν u p) (v p) =
      ∫ p in cell c, ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * inner ℂ (u p) (genDiff1 ν v p) := by
  have hu0 : IsCTest c (uConj u 0) := isCTest_uConj hu 0
  have hu1 : IsCTest c (uConj u 1) := isCTest_uConj hu 1
  have hv0_cd := contDiffOn_comp_merid hv 0
  have hv1_cd := contDiffOn_comp_merid hv 1
  have hv0_per := qPeriodic_comp_merid hper 0
  have hv1_per := qPeriodic_comp_merid hper 1
  have hL0 : IsCTest c (fun p => (p.1 : ℂ) * opLam (pdQ (uConj u 0)) p * v p 0) :=
    isCTest_mul_of_contDiffOn (isCTest_s_mul (isCTest_opLam (cTestFderiv c _ hu0 (0, 1, 0))))
      hv0_cd hv0_per
  have hL1 : IsCTest c (fun p => (p.1 : ℂ) * opLam (pdQ (uConj u 1)) p * v p 1) :=
    isCTest_mul_of_contDiffOn (isCTest_s_mul (isCTest_opLam (cTestFderiv c _ hu1 (0, 1, 0))))
      hv1_cd hv1_per
  have hR0 : IsCTest c (fun p => (p.1 : ℂ) * uConj u 0 p * opLam (pdQ (fun q => v q 0)) p) :=
    isCTest_mul_of_contDiffOn (isCTest_s_mul hu0)
      (contDiffOn_opLam (contDiffOn_pd hv0_cd (0, 1, 0)))
      (qPeriodic_opLam (qPeriodic_pd hv0_per (0, 1, 0)))
  have hR1 : IsCTest c (fun p => (p.1 : ℂ) * uConj u 1 p * opLam (pdQ (fun q => v q 1)) p) :=
    isCTest_mul_of_contDiffOn (isCTest_s_mul hu1)
      (contDiffOn_opLam (contDiffOn_pd hv1_cd (0, 1, 0)))
      (qPeriodic_opLam (qPeriodic_pd hv1_per (0, 1, 0)))
  have hL_congr : ∫ p in cell c,
        ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * inner ℂ (genDiff1 ν u p) (v p) =
      (ν : ℂ) * (∫ p in cell c,
        (((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * ((p.1 : ℂ) * opLam (pdQ (uConj u 0)) p * v p 0) +
          ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * ((p.1 : ℂ) * opLam (pdQ (uConj u 1)) p * v p 1))) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun (measurableSet_cell c) fun p _ => ?_
    rw [inner_genDiff1_lhs ν hu.smooth p]
    ring
  have hR_congr : ∫ p in cell c,
        ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * inner ℂ (u p) (genDiff1 ν v p) =
      (ν : ℂ) * (∫ p in cell c,
        (((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
            ((p.1 : ℂ) * uConj u 0 p * opLam (pdQ (fun q => v q 0)) p) +
          ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
            ((p.1 : ℂ) * uConj u 1 p * opLam (pdQ (fun q => v q 1)) p))) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun (measurableSet_cell c) fun p hp => ?_
    rw [inner_genDiff1_rhs ν hv hp.1]
    ring
  rw [hL_congr, hR_congr,
    integral_add (bandIntegrable c _ hL0).2 (bandIntegrable c _ hL1).2,
    integral_add (bandIntegrable c _ hR0).2 (bandIntegrable c _ hR1).2,
    cell_integral_opLam_pdQ_eq (uConj u 0) (fun q => v q 0) hu0 hv0_cd hv0_per,
    cell_integral_opLam_pdQ_eq (uConj u 1) (fun q => v q 1) hu1 hv1_cd hv1_per]

theorem cell_integral_genDiff2_eq {c : ℝ} (ν : ℝ) {u v : Profile → MeridC}
    (hu : IsMeridTest c u) (hv : ContDiffOn ℝ ∞ v {p : Profile | 0 < p.1})
    (hper : QPeriodic c v) :
    ∫ p in cell c, ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * inner ℂ (genDiff2 ν u p) (v p) =
      ∫ p in cell c, ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * inner ℂ (u p) (genDiff2 ν v p) := by
  have hu0 : IsCTest c (uConj u 0) := isCTest_uConj hu 0
  have hu1 : IsCTest c (uConj u 1) := isCTest_uConj hu 1
  have hv0_cd := contDiffOn_comp_merid hv 0
  have hv1_cd := contDiffOn_comp_merid hv 1
  have hv0_per := qPeriodic_comp_merid hper 0
  have hv1_per := qPeriodic_comp_merid hper 1
  have hL0 : IsCTest c (fun p => (p.1 : ℂ) * opLam (opLam (uConj u 0)) p * v p 0) :=
    isCTest_mul_of_contDiffOn (isCTest_s_mul (isCTest_opLam (isCTest_opLam hu0))) hv0_cd hv0_per
  have hL1 : IsCTest c (fun p => (p.1 : ℂ) * opLam (opLam (uConj u 1)) p * v p 1) :=
    isCTest_mul_of_contDiffOn (isCTest_s_mul (isCTest_opLam (isCTest_opLam hu1))) hv1_cd hv1_per
  have hE0 : IsCTest c (fun p => (p.1 : ℂ) * uConj u 0 p * v p 0) :=
    isCTest_mul_of_contDiffOn (isCTest_s_mul hu0) hv0_cd hv0_per
  have hR0 : IsCTest c (fun p => (p.1 : ℂ) * uConj u 0 p * opLam (opLam (fun q => v q 0)) p) :=
    isCTest_mul_of_contDiffOn (isCTest_s_mul hu0)
      (contDiffOn_opLam (contDiffOn_opLam hv0_cd))
      (qPeriodic_opLam (qPeriodic_opLam hv0_per))
  have hR1 : IsCTest c (fun p => (p.1 : ℂ) * uConj u 1 p * opLam (opLam (fun q => v q 1)) p) :=
    isCTest_mul_of_contDiffOn (isCTest_s_mul hu1)
      (contDiffOn_opLam (contDiffOn_opLam hv1_cd))
      (qPeriodic_opLam (qPeriodic_opLam hv1_per))
  have hint_L0 := (bandIntegrable c _ hL0).2
  have hint_L1 := (bandIntegrable c _ hL1).2
  have hint_E0 := (bandIntegrable c _ hE0).2
  have hint_R0 := (bandIntegrable c _ hR0).2
  have hint_R1 := (bandIntegrable c _ hR1).2
  have hint_L1E : IntegrableOn (fun p =>
      ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * ((p.1 : ℂ) * opLam (opLam (uConj u 1)) p * v p 1) -
        ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * ((p.1 : ℂ) * uConj u 0 p * v p 0)) (cell c) :=
    hint_L1.sub hint_E0
  have hint_R1E : IntegrableOn (fun p =>
      ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
          ((p.1 : ℂ) * uConj u 1 p * opLam (opLam (fun q => v q 1)) p) -
        ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * ((p.1 : ℂ) * uConj u 0 p * v p 0)) (cell c) :=
    hint_R1.sub hint_E0
  have hL_congr : ∫ p in cell c,
        ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * inner ℂ (genDiff2 ν u p) (v p) =
      (ν : ℂ) * (∫ p in cell c,
        (((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * ((p.1 : ℂ) * opLam (opLam (uConj u 0)) p * v p 0) +
          (((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * ((p.1 : ℂ) * opLam (opLam (uConj u 1)) p * v p 1) -
            ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * ((p.1 : ℂ) * uConj u 0 p * v p 0)))) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun (measurableSet_cell c) fun p _ => ?_
    rw [inner_genDiff2_lhs ν hu.smooth p]
    ring
  have hR_congr : ∫ p in cell c,
        ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * inner ℂ (u p) (genDiff2 ν v p) =
      (ν : ℂ) * (∫ p in cell c,
        (((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
            ((p.1 : ℂ) * uConj u 0 p * opLam (opLam (fun q => v q 0)) p) +
          (((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
              ((p.1 : ℂ) * uConj u 1 p * opLam (opLam (fun q => v q 1)) p) -
            ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * ((p.1 : ℂ) * uConj u 0 p * v p 0)))) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun (measurableSet_cell c) fun p hp => ?_
    rw [inner_genDiff2_rhs ν hv hp.1]
    ring
  rw [hL_congr, hR_congr,
    integral_add hint_L0 hint_L1E, integral_sub hint_L1 hint_E0,
    integral_add hint_R0 hint_R1E, integral_sub hint_R1 hint_E0,
    cell_integral_opLam_opLam_eq (uConj u 0) (fun q => v q 0) hu0 hv0_cd hv0_per,
    cell_integral_opLam_opLam_eq (uConj u 1) (fun q => v q 1) hu1 hv1_cd hv1_per]

end N04GenDiffIBPAux

open N04GenDiffIBPAux

/-- **Target `PartII-a:N04/3/2`**: `GenDiffIBP`, integration by parts of `A_ε - A_0` on `H`. -/
theorem genDiffIBP : GenDiffIBP := by
  intro ν c ε _hν _hc u v U DU V hu hU hDU hv_smooth hv_per hV h1 h2
  have hDU1_mem : MemLp (genDiff1 ν u) 2 (measureH c) := by
    have h := memLp_genDiffC_isMeridTest ν (-1 / 2) hu
    have heq : genDiff1 ν u = genDiffC ν (-1 / 2) u -
        ((((-1 / 2 : ℝ) ^ 2 : ℝ) : ℂ) • genDiff2 ν u) := by
      funext p
      simp only [genDiffC, Pi.sub_apply, Pi.smul_apply]
      have h21 : (-2 * (-1 / 2 : ℝ) : ℝ) = 1 := by ring
      rw [h21, Complex.ofReal_one, one_smul, add_sub_cancel_right]
    have h0 := memLp_genDiffC_isMeridTest ν 1 hu
    have h0' := memLp_genDiffC_isMeridTest ν (-1) hu
    have h2_eq : genDiff2 ν u = (1 / 2 : ℂ) • (genDiffC ν 1 u + genDiffC ν (-1) u) := by
      funext p
      simp only [genDiffC, Pi.add_apply, Pi.smul_apply]
      ext i
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      push_cast
      ring
    have h2m : MemLp (genDiff2 ν u) 2 (measureH c) := by
      rw [h2_eq]
      exact (h0.add h0').const_smul (1 / 2 : ℂ)
    rw [heq]
    exact h.sub (h2m.const_smul _)
  have hDU2_mem : MemLp (genDiff2 ν u) 2 (measureH c) := by
    have h0 := memLp_genDiffC_isMeridTest ν 1 hu
    have h0' := memLp_genDiffC_isMeridTest ν (-1) hu
    have h2_eq : genDiff2 ν u = (1 / 2 : ℂ) • (genDiffC ν 1 u + genDiffC ν (-1) u) := by
      funext p
      simp only [genDiffC, Pi.add_apply, Pi.smul_apply]
      ext i
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      push_cast
      ring
    rw [h2_eq]
    exact (h0.add h0').const_smul (1 / 2 : ℂ)
  set DU1 : HSpace c MeridC := hDU1_mem.toLp (genDiff1 ν u)
  set DU2 : HSpace c MeridC := hDU2_mem.toLp (genDiff2 ν u)
  set DV1 : HSpace c MeridC := h1.toLp (genDiff1 ν v)
  set DV2 : HSpace c MeridC := h2.toLp (genDiff2 ν v)
  have hDU_eq : DU = ((-2 * ε : ℝ) : ℂ) • DU1 + ((ε ^ 2 : ℝ) : ℂ) • DU2 := by
    rw [← toLp_genDiffC hDU1_mem hDU2_mem ε]
    apply Lp.ext
    filter_upwards [hDU, (memLp_genDiffC hDU1_mem hDU2_mem ε).coeFn_toLp] with p hp1 hp2
    rw [hp1, hp2]
  rw [hDU_eq, toLp_genDiffC h1 h2 ε, inner_add_left, inner_smul_left, inner_smul_left,
    inner_add_right, inner_smul_right, inner_smul_right,
    Complex.conj_ofReal, Complex.conj_ofReal]
  have hI1 : inner ℂ DU1 V = inner ℂ U DV1 := by
    have hL : inner ℂ DU1 V = ∫ p, inner ℂ (genDiff1 ν u p) (v p) ∂(measureH c) := by
      rw [MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hDU1_mem.coeFn_toLp, hV] with p hp1 hp2
      rw [hp1, hp2]
    have hR : inner ℂ U DV1 = ∫ p, inner ℂ (u p) (genDiff1 ν v p) ∂(measureH c) := by
      rw [MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hU, h1.coeFn_toLp] with p hp1 hp2
      rw [hp1, hp2]
    rw [hL, hR, integralMeasureHCell, integralMeasureHCell]
    exact cell_integral_genDiff1_eq ν hu hv_smooth hv_per
  have hI2 : inner ℂ DU2 V = inner ℂ U DV2 := by
    have hL : inner ℂ DU2 V = ∫ p, inner ℂ (genDiff2 ν u p) (v p) ∂(measureH c) := by
      rw [MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hDU2_mem.coeFn_toLp, hV] with p hp1 hp2
      rw [hp1, hp2]
    have hR : inner ℂ U DV2 = ∫ p, inner ℂ (u p) (genDiff2 ν v p) ∂(measureH c) := by
      rw [MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hU, h2.coeFn_toLp] with p hp1 hp2
      rw [hp1, hp2]
    rw [hL, hR, integralMeasureHCell, integralMeasureHCell]
    exact cell_integral_genDiff2_eq ν hu hv_smooth hv_per
  rw [hI1, hI2]

end UnforcedLeray.Short.PartIIa
