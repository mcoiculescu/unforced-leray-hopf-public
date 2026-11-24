import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N04.Defs

/-!


Source of record: `the November 2 reference manuscript`,
lines 1849–1869 (specifically lines 1856–1863).

Target: `theorem gradDiffIBP : GradDiffIBP` (`Sub/PartII-a_N04/Defs.lean`).
For a smooth tensor test `M` (`IsTensorTest c M`) and `v : Profile → MeridC` smooth on `{p | 0 < p.1}`
and `c`-periodic in `q`,
`⟨s(div_ε - div_0) M, v⟩_H = ⟨M, gradDiff ε v⟩_{H_T}`.

## Route

On `s > 0`, `s^{-1/2} = s^{-3/2} s` and for differentiable `f, g : Profile → ℂ`,
`opK (s f g) = s (opLam f) g + s f (opLam g)`.
Applying this with `f = conj (M · i)` and `g = v · i` (`i ∈ {0, 1}`) shows that on `cell c`,
the `measureHT c` integrand of `⟨M, gradDiff ε v⟩_{H_T}` equals the `measureH c` integrand of
`⟨s(div_ε - div_0) M, v⟩_H` plus `ε s^{-3/2} opK (s conj(M_0) v_0)` and
`ε s^{-3/2} opK (s conj(M_1) v_1)`. Both `s conj(M_i) v_i` are complex band tests (`IsCTest c`),
so their `s^{-3/2} opK` cell integrals vanish by `ibpKCell`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

namespace N04GradDiffIBPAux

/-- Conjugated component `p ↦ conj (M p j)` of a tensor profile. -/
def mConj (M : Profile → TensorVal) (j : Fin 4) : Profile → ℂ :=
  fun p => starRingEnd ℂ (M p j)

theorem contDiff_comp_tensor (M : Profile → TensorVal) (hM : ContDiff ℝ ∞ M) (j : Fin 4) :
    ContDiff ℝ ∞ (fun p => M p j) :=
  ((EuclideanSpace.proj j : TensorVal →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp hM

theorem isCTest_mConj {c : ℝ} {M : Profile → TensorVal} (hM : IsTensorTest c M) (j : Fin 4) :
    IsCTest c (mConj M j) where
  smooth := Complex.conjCLE.contDiff.comp (contDiff_comp_tensor M hM.smooth j)
  periodic := fun p => by simp only [mConj, hM.periodic p]
  band := by
    obtain ⟨s0, s1, L, hs0, hband⟩ := hM.band
    refine ⟨s0, s1, L, hs0, fun p hp => hband p fun h0 => hp ?_⟩
    simp [mConj, h0]

theorem contDiffOn_comp_merid {v : Profile → MeridC}
    (hv : ContDiffOn ℝ ∞ v {p : Profile | 0 < p.1}) (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun p => v p i) {p : Profile | 0 < p.1} :=
  ((EuclideanSpace.proj i : MeridC →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp_contDiffOn hv

theorem qPeriodic_comp_merid {c : ℝ} {v : Profile → MeridC} (hv : QPeriodic c v) (i : Fin 2) :
    QPeriodic c (fun p => v p i) :=
  fun p => congrArg (fun x => x i) (hv p)

/-- Multiplying a complex band test `f` by a `q`-periodic function `g` smooth on `{p | 0 < p.1}`
yields a complex band test. -/
theorem isCTest_mul_of_contDiffOn {c : ℝ} {f g : Profile → ℂ}
    (hf : IsCTest c f) (hg : ContDiffOn ℝ ∞ g {p : Profile | 0 < p.1}) (hper : QPeriodic c g) :
    IsCTest c (fun p => f p * g p) where
  smooth := by
    obtain ⟨s0, s1, L, hs0, hb⟩ := hf.band
    rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : 0 < p.1
    · exact hf.smooth.contDiffAt.mul
        (hg.contDiffAt ((isOpen_lt continuous_const continuous_fst).mem_nhds hp))
    · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      have hW : IsOpen {q : Profile | q.1 < s0} := isOpen_lt continuous_fst continuous_const
      filter_upwards [hW.mem_nhds (show p.1 < s0 by linarith [not_lt.1 hp])] with q hq
      have hfq : f q = 0 := by
        by_contra h
        exact absurd (hb q h).1.1 (not_le.2 hq)
      simp [hfq]
  periodic := fun p => by dsimp only; rw [hf.periodic p, hper p]
  band := by
    obtain ⟨s0, s1, L, hs0, hb⟩ := hf.band
    exact ⟨s0, s1, L, hs0, fun p hp => hb p (left_ne_zero_of_mul hp)⟩

theorem isCTest_s_mul {c : ℝ} {f : Profile → ℂ} (hf : IsCTest c f) :
    IsCTest c (fun p => (p.1 : ℂ) * f p) :=
  cTestAlgebra.2.2.2 c f (fun p => ((p.1 : ℝ) : ℂ)) hf ctoCoeffS_smooth (ctoCoeffS_periodic c)

theorem isCTest_opLam {c : ℝ} {f : Profile → ℂ} (hf : IsCTest c f) :
    IsCTest c (opLam f) :=
  cTestAlgebra.2.1 c (opK f) f (cTestOpK c f hf) hf

/-- `starRingEnd ℂ` commutes with `opLam` on smooth complex profiles. -/
theorem star_opLam {f : Profile → ℂ} (hf : ContDiff ℝ ∞ f) (p : Profile) :
    starRingEnd ℂ (opLam f p) = opLam (fun q => starRingEnd ℂ (f q)) p := by
  have hd : DifferentiableAt ℝ f p := (hf.differentiable (by simp)) p
  have hfd : ∀ w : Profile,
      fderiv ℝ (fun q => starRingEnd ℂ (f q)) p w = starRingEnd ℂ (fderiv ℝ f p w) := by
    intro w
    have h : HasFDerivAt (fun q => starRingEnd ℂ (f q))
        (Complex.conjCLE.toContinuousLinearMap.comp (fderiv ℝ f p)) p :=
      Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp p hd.hasFDerivAt
    rw [h.fderiv]
    rfl
  simp only [opLam, opK, opS, pdS, pdEta, Complex.real_smul, map_add, map_mul,
    Complex.conj_ofReal, hfd]

/-- Product rule for `opK (s f g)`:
`opK (s f g) = s (opLam f) g + s f (opLam g)`. -/
theorem opK_s_mul_mul {f g : Profile → ℂ} {p : Profile}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) :
    opK (fun x : Profile => (x.1 : ℂ) * f x * g x) p =
      (p.1 : ℂ) * opLam f p * g p + (p.1 : ℂ) * f p * opLam g p := by
  have hs : DifferentiableAt ℝ (fun x : Profile => (x.1 : ℂ)) p :=
    (NearStreamMemberAux.hasFDerivAt_ofReal_fst p).differentiableAt
  have hsf : DifferentiableAt ℝ (fun x : Profile => (x.1 : ℂ) * f x) p := hs.mul hf
  have h1S := NearStreamMemberAux.fderiv_mul_apply' (fun x : Profile => (x.1 : ℂ) * f x) g
    (1, 0, 0) p hsf hg
  have h2S := NearStreamMemberAux.fderiv_mul_apply' (fun x : Profile => (x.1 : ℂ)) f
    (1, 0, 0) p hs hf
  have h1E := NearStreamMemberAux.fderiv_mul_apply' (fun x : Profile => (x.1 : ℂ) * f x) g
    (0, 0, 1) p hsf hg
  have h2E := NearStreamMemberAux.fderiv_mul_apply' (fun x : Profile => (x.1 : ℂ)) f
    (0, 0, 1) p hs hf
  rw [NearStreamMemberAux.fderiv_ofReal_fst_apply] at h2S h2E
  rw [NearStreamMemberAux.opK_eq, opLam, opLam, NearStreamMemberAux.opK_eq,
    NearStreamMemberAux.opK_eq]
  unfold pdS pdEta
  rw [h1S, h2S, h1E, h2E]
  simp only [Complex.ofReal_one, Complex.ofReal_zero]
  ring

/-- `measureHT c` integrals as weighted cell integrals. -/
theorem integralMeasureHTCell (c : ℝ) (G : Profile → ℂ) :
    ∫ p, G p ∂(measureHT c) = ∫ p in cell c, ((p.1 ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * G p := by
  have hm : Measurable fun p : Profile => ENNReal.ofReal (p.1 ^ (-(1 / 2 : ℝ))) :=
    ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)
  rw [measureHT, integral_withDensity_eq_integral_toReal_smul hm
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top), cellMeasure]
  refine setIntegral_congr_fun (measurableSet_cell c) fun p hp => ?_
  have hp1 : 0 < p.1 := hp.1
  simp only [ENNReal.toReal_ofReal (Real.rpow_nonneg hp1.le _), Complex.real_smul]

/-- Pointwise expansion of the `H`-inner product `⟨s(div_ε - div_0) M, v⟩` at `p`. -/
theorem inner_s_divEps_sub_eq (ε : ℝ) (M : Profile → TensorVal) (hM : ContDiff ℝ ∞ M)
    (v : Profile → MeridC) (p : Profile) :
    inner ℂ ((p.1 : ℂ) • divEps ε M p - (p.1 : ℂ) • divEps 0 M p) (v p) =
      -((ε : ℝ) : ℂ) * ((p.1 : ℂ) * opLam (mConj M 0) p * v p 0 +
        (p.1 : ℂ) * opLam (mConj M 1) p * v p 1 +
        (p.1 : ℂ) * mConj M 3 p * v p 0) := by
  rw [s_smul_divEps_sub]
  have h0 := star_opLam (contDiff_comp_tensor M hM 0) p
  have h1 := star_opLam (contDiff_comp_tensor M hM 1) p
  unfold mConj
  simp [PiLp.inner_apply, Fin.sum_univ_two, h0, h1]
  ring

/-- Pointwise identity on `s > 0` relating the `H_T` pairing and `H` pairing via `opK`. -/
theorem weighted_inner_gradDiff_eq (ε : ℝ) (M : Profile → TensorVal) (hM : ContDiff ℝ ∞ M)
    (v : Profile → MeridC) (hv : ContDiffOn ℝ ∞ v {p : Profile | 0 < p.1})
    (p : Profile) (hp : 0 < p.1) :
    ((p.1 ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * inner ℂ (M p) (gradDiff ε v p) =
      ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
        inner ℂ ((p.1 : ℂ) • divEps ε M p - (p.1 : ℂ) • divEps 0 M p) (v p) +
      (((ε : ℝ) : ℂ) * (((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
        opK (fun x => (x.1 : ℂ) * mConj M 0 x * v x 0) p) +
      ((ε : ℝ) : ℂ) * (((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
        opK (fun x => (x.1 : ℂ) * mConj M 1 x * v x 1) p)) := by
  have hdf0 : DifferentiableAt ℝ (mConj M 0) p :=
    ((Complex.conjCLE.contDiff.comp (contDiff_comp_tensor M hM 0)).differentiable (by simp)) p
  have hdf1 : DifferentiableAt ℝ (mConj M 1) p :=
    ((Complex.conjCLE.contDiff.comp (contDiff_comp_tensor M hM 1)).differentiable (by simp)) p
  have hdv0 : DifferentiableAt ℝ (fun q => v q 0) p :=
    ((contDiffOn_comp_merid hv 0).contDiffAt
      ((isOpen_lt continuous_const continuous_fst).mem_nhds hp)).differentiableAt (by simp)
  have hdv1 : DifferentiableAt ℝ (fun q => v q 1) p :=
    ((contDiffOn_comp_merid hv 1).contDiffAt
      ((isOpen_lt continuous_const continuous_fst).mem_nhds hp)).differentiableAt (by simp)
  have hK0 := opK_s_mul_mul hdf0 hdv0
  have hK1 := opK_s_mul_mul hdf1 hdv1
  have hb : p.1 ^ (-(3 / 2 : ℝ)) * p.1 = p.1 ^ (-(1 / 2 : ℝ)) := by
    have h32 : (-(1 / 2 : ℝ)) = -(3 / 2 : ℝ) + 1 := by norm_num
    rw [h32, Real.rpow_add hp, Real.rpow_one]
  have hc : ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * ((p.1 : ℝ) : ℂ) =
      ((p.1 ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, hb]
  rw [← hc, inner_s_divEps_sub_eq ε M hM v p, hK0, hK1]
  simp [gradDiff, gradDiff1, PiLp.inner_apply, Fin.sum_univ_four, mConj]
  ring

end N04GradDiffIBPAux

open N04GradDiffIBPAux

/-- **Target `PartII-a:N04/4`**: `GradDiffIBP`, integration by parts of `s(div_ε - div_0) M`
against `v` on `H`. -/
theorem gradDiffIBP : GradDiffIBP := by
  intro c ε H1 _hc M v F G1 G2 V hgd hM hv_smooth hv_per _hv_supp hF hG1 hG2 hV
  have hL_ae : inner ℂ (G1 - G2) V =
      ∫ p, inner ℂ ((p.1 : ℂ) • divEps ε M p - (p.1 : ℂ) • divEps 0 M p) (v p) ∂(measureH c) := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub G1 G2, hG1, hG2, hV] with p hsub hp1 hp2 hpv
    rw [hsub, Pi.sub_apply, hp1, hp2, hpv]
  have hR_ae : inner ℂ F ((memLp_gradDiff hgd ε).toLp (gradDiff ε v)) =
      ∫ p, inner ℂ (M p) (gradDiff ε v p) ∂(measureHT c) := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hF, (memLp_gradDiff hgd ε).coeFn_toLp] with p hpF hpG
    rw [hpF, hpG]
  rw [hL_ae, hR_ae, integralMeasureHCell, integralMeasureHTCell]
  have hm0 : IsCTest c (mConj M 0) := isCTest_mConj hM 0
  have hm1 : IsCTest c (mConj M 1) := isCTest_mConj hM 1
  have hm3 : IsCTest c (mConj M 3) := isCTest_mConj hM 3
  have hv0_cd := contDiffOn_comp_merid hv_smooth 0
  have hv1_cd := contDiffOn_comp_merid hv_smooth 1
  have hv0_per := qPeriodic_comp_merid hv_per 0
  have hv1_per := qPeriodic_comp_merid hv_per 1
  have hF0 : IsCTest c (fun x => (x.1 : ℂ) * mConj M 0 x * v x 0) :=
    isCTest_mul_of_contDiffOn (isCTest_s_mul hm0) hv0_cd hv0_per
  have hF1 : IsCTest c (fun x => (x.1 : ℂ) * mConj M 1 x * v x 1) :=
    isCTest_mul_of_contDiffOn (isCTest_s_mul hm1) hv1_cd hv1_per
  have hT0 : IsCTest c (fun x => (x.1 : ℂ) * opLam (mConj M 0) x * v x 0) :=
    isCTest_mul_of_contDiffOn (isCTest_s_mul (isCTest_opLam hm0)) hv0_cd hv0_per
  have hT1 : IsCTest c (fun x => (x.1 : ℂ) * opLam (mConj M 1) x * v x 1) :=
    isCTest_mul_of_contDiffOn (isCTest_s_mul (isCTest_opLam hm1)) hv1_cd hv1_per
  have hT3 : IsCTest c (fun x => (x.1 : ℂ) * mConj M 3 x * v x 0) :=
    isCTest_mul_of_contDiffOn (isCTest_s_mul hm3) hv0_cd hv0_per
  have hTsum : IsCTest c (fun p =>
      -((ε : ℝ) : ℂ) * ((p.1 : ℂ) * opLam (mConj M 0) p * v p 0 +
        (p.1 : ℂ) * opLam (mConj M 1) p * v p 1 +
        (p.1 : ℂ) * mConj M 3 p * v p 0)) := by
    have h01 := cTestAlgebra.2.1 c _ _ hT0 hT1
    have h013 := cTestAlgebra.2.1 c _ _ h01 hT3
    exact cTestAlgebra.2.2.2 c _ (fun _ => -((ε : ℝ) : ℂ)) h013 contDiff_const (fun _ => rfl)
  have hint_L : IntegrableOn (fun p => ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
      inner ℂ ((p.1 : ℂ) • divEps ε M p - (p.1 : ℂ) • divEps 0 M p) (v p)) (cell c) := by
    have heq : (fun p => ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
        inner ℂ ((p.1 : ℂ) • divEps ε M p - (p.1 : ℂ) • divEps 0 M p) (v p)) =
      (fun p => ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
        (-((ε : ℝ) : ℂ) * ((p.1 : ℂ) * opLam (mConj M 0) p * v p 0 +
          (p.1 : ℂ) * opLam (mConj M 1) p * v p 1 +
          (p.1 : ℂ) * mConj M 3 p * v p 0))) := by
      funext p
      rw [inner_s_divEps_sub_eq ε M hM.smooth v p]
    rw [heq]
    exact (bandIntegrable c _ hTsum).2
  have hint_K0 : IntegrableOn (fun p => ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
      opK (fun x => (x.1 : ℂ) * mConj M 0 x * v x 0) p) (cell c) :=
    (bandIntegrable c _ (cTestOpK c _ hF0)).2
  have hint_K1 : IntegrableOn (fun p => ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
      opK (fun x => (x.1 : ℂ) * mConj M 1 x * v x 1) p) (cell c) :=
    (bandIntegrable c _ (cTestOpK c _ hF1)).2
  have hint_K01 : IntegrableOn (fun p =>
      ((ε : ℝ) : ℂ) * (((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
        opK (fun x => (x.1 : ℂ) * mConj M 0 x * v x 0) p) +
      ((ε : ℝ) : ℂ) * (((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
        opK (fun x => (x.1 : ℂ) * mConj M 1 x * v x 1) p)) (cell c) :=
    (hint_K0.const_mul _).add (hint_K1.const_mul _)
  have hcongr : ∫ p in cell c, ((p.1 ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * inner ℂ (M p) (gradDiff ε v p) =
      ∫ p in cell c, (((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
          inner ℂ ((p.1 : ℂ) • divEps ε M p - (p.1 : ℂ) • divEps 0 M p) (v p) +
        (((ε : ℝ) : ℂ) * (((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
          opK (fun x => (x.1 : ℂ) * mConj M 0 x * v x 0) p) +
        ((ε : ℝ) : ℂ) * (((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
          opK (fun x => (x.1 : ℂ) * mConj M 1 x * v x 1) p))) :=
    setIntegral_congr_fun (measurableSet_cell c) fun p hp =>
      weighted_inner_gradDiff_eq ε M hM.smooth v hv_smooth p hp.1
  rw [hcongr, integral_add hint_L hint_K01,
    integral_add (hint_K0.const_mul _) (hint_K1.const_mul _),
    integral_const_mul, integral_const_mul,
    ibpKCell c _ hF0, ibpKCell c _ hF1]
  ring

end UnforcedLeray.Short.PartIIa
