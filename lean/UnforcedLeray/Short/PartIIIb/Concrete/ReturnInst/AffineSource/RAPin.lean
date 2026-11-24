import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.RADefs
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.VelPairAE
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.PairFunctional.PairLinear
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.StressLift.StrSumAE
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.StressLift.CartLift
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T7
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_8_5
import UnforcedLeray.Lib.Axisymmetric.Measure

/-!
# The pin `IsRAOp` of the constructed `𝔯_A` (Lemma `ret:physical-affine`, source 5001-5008)

Source of record: `the November 2 reference manuscript` (73 pages).

Part (a) of `ORG:return-concrete/instance-3/affine-source`, the identity half.  At one regime
`L` (`ReturnLevel`, `c = ν⁻²`, `R = ε⁻¹`, `P = 2εc`) and Floquet exponent `μ`, let `r` be the
continuous linear map `A ↦ [rAcoef … L.U (ιA)]` into `SrcG` (an `IsL2Family`, built in
`RABound.lean`).  Then `r` satisfies the pin `IsRAOp` of `𝔯_A` with the pinned operators
`multOp`, `hAOp`, `FAOp`, `EAOp` of `Concrete/ReturnInst.lean` (`isRAOp_of`):

1. the pairings see only a.e. classes (`NearInst.velPairAE`, `NearInst.stressPairAE`), so the Lp
   representatives of `hAOp A`, `FAOp A`, `EAOp A`, `r A` may be replaced by the chart fields
   `hAcoef`, `FAcoef`, `EAcoef`, `rAcoef` (pins `hAOp_spec`, `FAOp_spec`, `EAOp_spec`);
2. the stress of `multOp` is the chart tensor of `U ⊗ ĥ + ĥ ⊗ U` (`strSumExactAE_proved`, through
   the exact-multiplier pin `NearInst.MultPinOfLink`, task `PartIII-b:C/near/link/2`, applied to
   the auxiliary base `multBase` whose multiplier is `multOp`), and its physical lift is
   `symProd U ĥ` (`cartLiftSymOuter_proved`, `U` axisymmetric without swirl and periodic);
3. `velPhys (coefOf 𝔯) = 𝔯` off the axis (`velPhysCoefOf_of` with `RAPhysAxi`);
4. the identity itself is integration by parts of the pointwise definition of `𝔯_A`
   (`raWeakIdentity`, from `IBPAdjointC2`, `IBPDivC1`, `IBPGradC1`, `IBPContC`, `ibpLin_proved`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest Params)
open UnforcedLeray.Blueprint.Planar (PlanarData)

/-! ## 1. Measure transfers and pairing congruences -/

/-- An a.e. statement for the gained body measure holds for `ageμ c (-3/2)` (the density
`π g⁻²` is positive). -/
theorem ae_ageμ_of_ae_bodyMeasure {c γ ν : ℝ} {P : Chart → Prop}
    (h : ∀ᵐ p ∂(bodyMeasure c γ ν), P p) : ∀ᵐ p ∂(ageμ c (-3 / 2)), P p := by
  unfold bodyMeasure at h
  have hmeas : Measurable fun p : Chart => ENNReal.ofReal (Real.pi * ginv γ ν p ^ 2) :=
    ENNReal.measurable_ofReal.comp
      (measurable_const.mul ((NearInst.gainFun_measurable γ ν).inv.pow_const 2))
  have h2 := (ae_withDensity_iff hmeas).1 h
  filter_upwards [h2] with p hp
  refine hp ?_
  have : 0 < ginv γ ν p := by
    have : 0 < NearInst.gainFun γ ν p := NearInst.gainFun_pos γ ν p
    exact inv_pos.2 this
  exact (ENNReal.ofReal_pos.2 (by positivity)).ne'

/-- An a.e. statement for `srcMeasure c = π·ageμ c (-3/2)` holds for `ageμ c (-3/2)`. -/
theorem ae_ageμ_of_ae_srcMeasure {c : ℝ} {P : Chart → Prop}
    (h : ∀ᵐ p ∂(srcMeasure c), P p) : ∀ᵐ p ∂(ageμ c (-3 / 2)), P p := by
  unfold srcMeasure at h
  exact (Measure.absolutelyContinuous_smul (ENNReal.ofReal_pos.2 Real.pi_pos).ne').ae_le h

/-- The phase pairing sees its field only off the axis. -/
theorem ra_pairF_congr_offAxis {P : ℝ} (Φ u v : ℝ × Space → CVec3)
    (h : ∀ τ y, y ∉ axis → u (τ, y) = v (τ, y)) : pairF P Φ u = pairF P Φ v := by
  unfold pairF phaseInt
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  refine integral_congr_ae ?_
  filter_upwards [ae_not_mem_axis] with y hy
  simp only [h t y hy]

theorem ra_realC_add (x y : Space) :
    B0412.realC (x + y) = B0412.realC x + B0412.realC y := by
  ext i
  simp only [B0412.realC_apply, PiLp.add_apply, Complex.ofReal_add]

/-! ## 2. Periodicity of the lift -/

/-- The ring chart at the phase `τ + 2εc` is the chart at `τ` shifted by one cell in `q`. -/
theorem chart_add_period {ε c : ℝ} (hε : 0 < ε) (τ : ℝ) (y : Space) :
    UnforcedLeray.Axi.chart ε⁻¹ (τ + 2 * ε * c) y =
      ((UnforcedLeray.Axi.chart ε⁻¹ τ y).1,
        ((UnforcedLeray.Axi.chart ε⁻¹ τ y).2.1 + c, (UnforcedLeray.Axi.chart ε⁻¹ τ y).2.2)) := by
  simp only [UnforcedLeray.Axi.chart, UnforcedLeray.Axi.phase]
  congr 2
  field_simp
  ring

/-- `ĥ_A` (any `𝒩_v` lift with `perExt`) is `2εc`-periodic in the phase. -/
theorem nvPerExt_periodic {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) (b : Chart → Merid) (τ : ℝ)
    (y : Space) : Nv ε⁻¹ (perExt c b) (τ + 2 * ε * c) y = Nv ε⁻¹ (perExt c b) τ y := by
  unfold Nv
  rw [chart_add_period hε τ y, perExt_periodic hc.ne']

/-! ## 3. The multiplier of the level as an exact multiplier -/

section Level

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)

/-- A return base whose multiplier is `multOp` (`S_N = 0`, `D_N⁻¹ = id`, all other fields `0`):
it carries the exact-multiplier pin of `multOp` (the pin `IsExactMultiplier` reads only `B.M`). -/
def multBase : ReturnBase (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν (AffSp K.as) where
  M := multOp Pl K L
  S := 0
  SN := 0
  R := 0
  Yf := 0
  hf := 0
  Ef := 0
  Lj := 0
  hA := 0
  FA := 0
  EA := 0
  rA := 0
  DNinv := ContinuousLinearMap.id ℝ _
  DNinv_left := fun T => by simp
  DNinv_right := fun T => by simp
  aMu := 0
  Lam := 0
  Kflat := 0

variable {Pl K L}

/-- `multOp` is the exact multiplier `M_U` (source 2669-2672, 3876-3877, 4147, 5779-5782), from the
transport pin `MultPinOfLink` and the split pin of `nearMU`. -/
theorem multBase_isExactMultiplier (hpin : NearInst.MultPinOfLink)
    (hs : ∃ M : Hsp (cOf L.ν) →L[ℝ] Zsp (cOf L.ν) K.mZ (L.ρb Pl K),
      NearInst.IsSplitMult M (L.params Pl).R L.V L.rb) :
    IsExactMultiplier (multBase Pl K L) L.ε⁻¹ L.V L.rb :=
  hpin _ _ _ _ _ L.ν_pos _ (multBase Pl K L) ⟨0, 0, 0, nearMU Pl K L⟩ _ _ _ (nearMU_spec hs) rfl

theorem rhoB_pos (hC0 : 0 < K.C0) : 0 < L.ρb Pl K := by
  unfold ReturnLevel.ρb UnforcedLeray.Short.IIb.rhoB
  have h1 : 0 < ((L.params Pl).ν ^ K.k0)⁻¹ := inv_pos.2 (pow_pos (L.params Pl).ν_pos _)
  have h2 : 0 < (L.params Pl).ε ^ (3 / 11 : ℝ) := Real.rpow_pos_of_pos (L.params Pl).ε_pos _
  have h3 := Real.exp_pos (K.m0 / (L.params Pl).ν)
  positivity

/-! ## 4. The three pairings of `IsRAOp` -/

variable {μ : ℝ}

/-- The velocity pairing of `hAOp A` is that of the physical `ĥ_A`. -/
theorem pairF_hAOp (hd : AffineFieldData K.as L.ν μ L.ε (gRate Pl) K.χf (affIota K.as))
    (A : AffSp K.as) (Ψ : ℝ × Space → CVec3) :
    pairF (2 * L.ε * cOf L.ν) Ψ (velPhys L.ε⁻¹ (cOf L.ν) (hAOp Pl K L A)) =
      pairF (2 * L.ε * cOf L.ν) Ψ (realCf (hLift L.ν L.ε (cOf L.ν) K.χf (affIota K.as A))) :=
  NearInst.velPairAE (cOf L.ν) L.ε (cOf_pos L.ν_pos) L.ε_pos _ _
    (ae_ageμ_of_ae_bodyMeasure (hAOp_spec ⟨hd.hAL, hd.hA.toCLM_ae⟩ A)) Ψ

/-- The stress pairing of `multOp (hAOp A)` is that of `U ⊗ ĥ_A + ĥ_A ⊗ U`
(source 4147, 2683, 5779-5782). -/
theorem stressPair_multOp_hAOp (hpin : NearInst.MultPinOfLink)
    (hs : ∃ M : Hsp (cOf L.ν) →L[ℝ] Zsp (cOf L.ν) K.mZ (L.ρb Pl K),
      NearInst.IsSplitMult M (L.params Pl).R L.V L.rb) (hC0 : 0 < K.C0)
    (hax : ∀ τ, AxiNoSwirlPt (L.U τ)) (hper : ∀ τ y, L.U (τ + 2 * L.ε * cOf L.ν) y = L.U τ y)
    (hd : AffineFieldData K.as L.ν μ L.ε (gRate Pl) K.χf (affIota K.as)) (A : AffSp K.as)
    (Φ : ℝ × Space → CVec3) :
    stressPair (2 * L.ε * cOf L.ν)
        (strPhys L.ε⁻¹ (cOf L.ν) (strSum (multOp Pl K L (hAOp Pl K L A)))) Φ =
      stressPair (2 * L.ε * cOf L.ν) (fun x => symProd (L.U x.1 x.2)
        (hLift L.ν L.ε (cOf L.ν) K.χf (affIota K.as A) x.1 x.2)) Φ := by
  have hc : 0 < cOf L.ν := cOf_pos L.ν_pos
  have hR : 0 < L.ε⁻¹ := inv_pos.2 L.ε_pos
  have hM := multBase_isExactMultiplier hpin hs
  have h1 := strSumExactAE_proved (multBase Pl K L) hc (rhoB_pos hC0) L.ε L.V L.rb hM
    (hAOp Pl K L A)
  have h2 : (hAOp Pl K L A : Chart → Merid) =ᵐ[ageμ (cOf L.ν) (-1 / 2)]
      hAcoef L.ν L.ε K.χf (affIota K.as A) :=
    (NearInst.ageμ_absCont (cOf L.ν) (-1 / 2) (-3 / 2)).ae_le
      (ae_ageμ_of_ae_bodyMeasure (hAOp_spec ⟨hd.hAL, hd.hA.toCLM_ae⟩ A))
  have h3 : strSum (multOp Pl K L (hAOp Pl K L A)) =ᵐ[ageμ (cOf L.ν) (-1 / 2)]
      fun p => NearInst.ten3Of (IIIa.symOuter (IIIa.chartCoeff L.ε⁻¹ L.U p)
        (hAcoef L.ν L.ε K.χf (affIota K.as A) p)) := by
    filter_upwards [h1, h2] with p hp1 hp2
    rw [show strSum (multOp Pl K L (hAOp Pl K L A)) p =
      strSum ((multBase Pl K L).M (hAOp Pl K L A)) p from rfl, hp1, hp2]
    rfl
  rw [NearInst.stressPairAE (cOf L.ν) L.ε hc L.ε_pos _ _ h3 Φ]
  have hper' : ∀ τ y, L.U (τ + 2 * cOf L.ν / L.ε⁻¹) y = L.U τ y := by
    intro τ y
    have e : 2 * cOf L.ν / L.ε⁻¹ = 2 * L.ε * cOf L.ν := by field_simp
    rw [e]
    exact hper τ y
  congr 1
  funext x
  exact cartLiftSymOuter_proved L.ε⁻¹ (cOf L.ν) L.U hR hc hax hper'
    (hAcoef L.ν L.ε K.χf (affIota K.as A)) x.1 x.2

/-- The force pairing of `F_A + E_A + r A` is that of the physical `F_A + E_A + 𝔯_A`. -/
theorem pairF_force (hd : AffineFieldData K.as L.ν μ L.ε (gRate Pl) K.χf (affIota K.as))
    (r : AffSp K.as →L[ℝ] LSrc L)
    (hr : ∀ A, (r A : Chart → Merid) =ᵐ[srcMeasure (cOf L.ν)]
      rAcoef L.ν μ L.ε (cOf L.ν) K.χf L.U (affIota K.as A))
    (A : AffSp K.as)
    (haxi : AxiNoSwirl (rAPhys L.ν μ L.ε (cOf L.ν) K.χf L.U (affIota K.as A)))
    (hpr : ∀ τ y, rAPhys L.ν μ L.ε (cOf L.ν) K.χf L.U (affIota K.as A) (τ + 2 * cOf L.ν / L.ε⁻¹) y =
      rAPhys L.ν μ L.ε (cOf L.ν) K.χf L.U (affIota K.as A) τ y)
    (Φ : ℝ × Space → CVec3) :
    pairF (2 * L.ε * cOf L.ν) Φ (velPhys L.ε⁻¹ (cOf L.ν)
        ((FAOp K L μ A + EAOp K L μ A + r A : SrcG (cOf L.ν)) : Chart → Merid)) =
      pairF (2 * L.ε * cOf L.ν) Φ (realCf fun τ y =>
        feLift L.ν μ L.ε (cOf L.ν) K.χf (affIota K.as A) τ y +
          rAPhys L.ν μ L.ε (cOf L.ν) K.χf L.U (affIota K.as A) τ y) := by
  have hc : 0 < cOf L.ν := cOf_pos L.ν_pos
  have hR : 0 < L.ε⁻¹ := inv_pos.2 L.ε_pos
  have hae : ((FAOp K L μ A + EAOp K L μ A + r A : SrcG (cOf L.ν)) : Chart → Merid)
      =ᵐ[srcMeasure (cOf L.ν)] (FAcoef L.ν μ K.χf (affIota K.as A) +
        EAcoef L.ν μ K.χf (affIota K.as A)) + rAcoef L.ν μ L.ε (cOf L.ν) K.χf L.U (affIota K.as A) := by
    filter_upwards [Lp.coeFn_add (FAOp K L μ A + EAOp K L μ A) (r A),
      Lp.coeFn_add (FAOp K L μ A) (EAOp K L μ A), FAOp_spec ⟨hd.FAL, hd.FA.toCLM_ae⟩ A,
      EAOp_spec ⟨hd.EAL, hd.EA.toCLM_ae⟩ A, hr A] with p h1 h2 h3 h4 h5
    rw [h1, Pi.add_apply, h2, Pi.add_apply, h3, h4, h5]
    rfl
  rw [NearInst.velPairAE (cOf L.ν) L.ε hc L.ε_pos _ _ (ae_ageμ_of_ae_srcMeasure hae) Φ]
  refine ra_pairF_congr_offAxis _ _ _ fun τ y hy => ?_
  rw [NearInst.pl_velPhys_add]
  have h1 : velPhys L.ε⁻¹ (cOf L.ν) (rAcoef L.ν μ L.ε (cOf L.ν) K.χf L.U (affIota K.as A)) (τ, y) =
      B0412.realC (rAPhys L.ν μ L.ε (cOf L.ν) K.χf L.U (affIota K.as A) τ y) :=
    velPhysCoefOf_of L.ε⁻¹ (cOf L.ν) hR hc _ haxi hpr (τ, y) hy
  simp only [Pi.add_apply]
  rw [h1]
  show B0412.realC (feLift L.ν μ L.ε (cOf L.ν) K.χf (affIota K.as A) τ y) +
      B0412.realC (rAPhys L.ν μ L.ε (cOf L.ν) K.χf L.U (affIota K.as A) τ y) =
    B0412.realC (feLift L.ν μ L.ε (cOf L.ν) K.χf (affIota K.as A) τ y +
      rAPhys L.ν μ L.ε (cOf L.ν) K.χf L.U (affIota K.as A) τ y)
  rw [ra_realC_add]

end Level

/-! ## 5. The weak identity from the pointwise definition -/

/-- **Integration by parts of the pointwise residual** (source 5001-5008): for `h ∈ C²`
(`P`-periodic), `U, q ∈ C¹` and any field `fe`,
`⟨L₀ᵗΦ + μΦ, h⟩ - ⟨U⊗h + h⊗U, ∇Φ⟩ = ⟨Φ, fe + (D_μh + div(U⊗h+h⊗U) - fe - ∇q)⟩ - ⟨q, div Φ⟩`. -/
theorem raWeakIdentity (hAdj : IBPAdjointC2) (hDiv : IBPDivC1) (hGrad : IBPGradC1)
    (hCont : IBPContC) {P ν μ : ℝ} (hP : 0 < P) {h U fe : ℝ → Space → Space}
    {q : ℝ → Space → ℝ} (hh : ContDiff ℝ 2 (fun x : ℝ × Space => h x.1 x.2))
    (hper : ∀ τ y, h (τ + P) y = h τ y) (hU : ContDiff ℝ 1 (fun x : ℝ × Space => U x.1 x.2))
    (hq : ContDiff ℝ 1 (fun x : ℝ × Space => q x.1 x.2)) (Φ : ℝ × Space → CVec3)
    (hΦ : IsPhaseTest P Φ) :
    pairF P (fun x => L0T ν Φ x + (μ : ℂ) • Φ x) (realCf h) -
        stressPair P (fun x => symProd (U x.1 x.2) (h x.1 x.2)) Φ =
      pairF P Φ (realCf fun τ y => fe τ y +
        (physDmu ν μ h τ y + physDivSym (U τ) (h τ) y - fe τ y - physGrad (q τ) y)) -
        scalarPair P (fun x => q x.1 x.2) Φ := by
  have hh1 : ContDiff ℝ 1 (fun x : ℝ × Space => h x.1 x.2) := hh.of_le (by norm_num)
  have cD := hCont.1 ν μ h hh
  have cS := hCont.2.1 U h hU hh1
  have cG := hCont.2.2 q hq
  have e : (realCf fun τ y => fe τ y +
      (physDmu ν μ h τ y + physDivSym (U τ) (h τ) y - fe τ y - physGrad (q τ) y)) =
      fun x => (realCf (physDmu ν μ h) x + realCf (fun τ y => physDivSym (U τ) (h τ) y) x) -
        realCf (fun τ y => physGrad (q τ) y) x := by
    funext x
    ext i
    simp only [realCf, B0412.realC_apply, PiLp.add_apply, PiLp.sub_apply]
    push_cast
    ring
  rw [e, (ibpLin_proved P Φ hΦ
      (fun x => realCf (physDmu ν μ h) x + realCf (fun τ y => physDivSym (U τ) (h τ) y) x)
      (realCf fun τ y => physGrad (q τ) y) (cD.add cS) cG).2,
    (ibpLin_proved P Φ hΦ _ _ cD cS).1,
    hAdj P ν μ hP h hh hper Φ hΦ, hDiv P U h hU hh1 Φ hΦ, hGrad P q hq Φ hΦ]
  ring

/-! ## 6. The pin -/

/-- **The pin `IsRAOp` of the constructed `𝔯_A`** (Lemma `ret:physical-affine`, source 5001-5008):
for `r` with `r A = [rAcoef … U (ιA)]` a.e., on an exact profile `U = V + r_b` that is
axisymmetric without swirl, with the split pin of `M_U` and the exact-multiplier transport pin. -/
theorem isRAOp_of {Pl : PlanarData} {K : ReturnConsts} {L : ReturnLevel} {μ : ℝ}
    (hAdj : IBPAdjointC2) (hDiv : IBPDivC1) (hGrad : IBPGradC1) (hCont : IBPContC)
    (hreg : AffineLiftReg K.as K.χf) (haxi : RAPhysAxi K.as K.χf) (hχf : IsSourceCutoffC K.χf)
    (hpin : NearInst.MultPinOfLink)
    (hs : ∃ M : Hsp (cOf L.ν) →L[ℝ] Zsp (cOf L.ν) K.mZ (L.ρb Pl K),
      NearInst.IsSplitMult M (L.params Pl).R L.V L.rb) (hC0 : 0 < K.C0)
    (hax : ∀ τ, AxiNoSwirlPt (L.U τ)) (hprof : IsExactProfile L.ν (2 * L.ε * cOf L.ν) L.U L.pres)
    (hd : AffineFieldData K.as L.ν μ L.ε (gRate Pl) K.χf (affIota K.as))
    (r : AffSp K.as →L[ℝ] LSrc L)
    (hr : ∀ A, (r A : Chart → Merid) =ᵐ[srcMeasure (cOf L.ν)]
      rAcoef L.ν μ L.ε (cOf L.ν) K.χf L.U (affIota K.as A)) :
    IsRAOp (multOp Pl K L) (hAOp Pl K L) (FAOp K L μ) (EAOp K L μ) r (affIota K.as) K.χf L.ε μ := by
  intro A Φ hΦ
  have hc : 0 < cOf L.ν := cOf_pos L.ν_pos
  have hP : 0 < 2 * L.ε * cOf L.ν := by have := L.ε_pos; positivity
  have hU1 : ContDiff ℝ 1 (fun x : ℝ × Space => L.U x.1 x.2) :=
    hprof.smoothU.of_le (by exact_mod_cast le_top)
  obtain ⟨hh, hq, -⟩ := hreg hχf L.ν μ L.ε L.ν_pos L.ε_pos (affIota K.as A) (affIota_mem K.as A)
  obtain ⟨hax1, hax2⟩ := haxi hχf L.ν μ L.ε L.ν_pos L.ε_pos L.U hax hU1 hprof.periodicU
    (affIota K.as A) (affIota_mem K.as A)
  rw [pairF_hAOp hd, stressPair_multOp_hAOp hpin hs hC0 hax hprof.periodicU hd,
    pairF_force hd r hr A hax1 hax2]
  exact raWeakIdentity hAdj hDiv hGrad hCont hP hh
    (fun τ y => nvPerExt_periodic L.ε_pos hc _ τ y) hU1 hq Φ hΦ

end UnforcedLeray.Short.PartIIIb.Concrete
