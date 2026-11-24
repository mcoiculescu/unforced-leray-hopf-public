import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F6
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F5_2_2
import UnforcedLeray.Short.PartIIb.Tasks.FlatInverse
import UnforcedLeray.Short.PartIIb.Tasks.BodySource.SliceHolder.CylProjection.FlatBvSliceGoodAe.JointWeak
import UnforcedLeray.Short.PartIIIa.T20_2_BiotSavartUnique
import UnforcedLeray.Lib.BochnerTime.Slices

/-!
# Part II-b, task `PartII-b:F6/1`: Linear body-source and curl-source maps (`LinearBodySourceMap`, SP 2213–2239, 2265–2267)

Source of record: `the November 2 reference manuscript`
(SP), lines 2213–2239 (`short-bg:source`) and 2265–2267 (`short-bg:early`).

This file proves `linearBodySourceMap_proof : UnforcedLeray.Short.IIb.LinearBodySourceMap`
unconditionally via:
1. `inFlatClass_zero`, `inFlatClass_add`, `inFlatClass_smul_real`, `isFlatResponse_zero_toProf`,
   `isFlatResponse_add_toProf`, `isFlatResponse_smul_real_toProf`, `flatBv_*`, `isBodySource_*`:
   full `ℝ`-linear closure of the flat class, flat response, weak derivatives, and `IsBodySource`;
2. `exists_real_sm_rep`, `upgrade_bodySource_witness`, and `mk_curl_path`: Borel-measurable
   real-valued `q`-periodic upgrades via `F10K0Help.reProf` + `exists_sm_rep_vol`, and slice-curve
   construction in `Xmc p.c m` via `BochnerTime.toPathLq`;
3. `ae_cell_eq_of_isBodySource`: slice uniqueness on `B0579.cell p.c` for any two finite-`H¹`
   `IsBodySource` solutions with the same `(b0, b0q, b0η)` via `JointWeakToSlice` and
   `T20_2.biot_re`;
4. `linearBodySourceMap_proof`: Hamel-basis `ℝ`-linear extension from `HpR p.c` combined with
   slice uniqueness against upgraded `BodySourceBound` witnesses to transfer the weighted `Lᵖ`
   and Hardy `L¹(0, p.H; X_{m,c})` norm bounds to all `F : HpR p.c`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03 UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint

namespace LinearBodySourceHelp

/-! ## 1. `ℝ`-linear closure of `InFlatClass`, `IsFlatResponse`, `HasWeakVec`, and `IsBodySource` -/

lemma qPeriodic_zero (c : ℝ) : QPeriodic c (0 : CProf) :=
  Eventually.of_forall fun _ => rfl

lemma qPeriodic_add {c : ℝ} {f g : CProf} (hf : QPeriodic c f) (hg : QPeriodic c g) :
    QPeriodic c (f + g) := by
  filter_upwards [hf, hg] with x hfx hgx
  simp only [Pi.add_apply, hfx, hgx]

lemma qPeriodic_smul_real {c : ℝ} (a : ℝ) {f : CProf} (hf : QPeriodic c f) :
    QPeriodic c (a • f) := by
  filter_upwards [hf] with x hfx
  simp only [Pi.smul_apply, hfx]

lemma inHr_zero (c r : ℝ) : InHr c r (0 : CProf) :=
  ⟨qPeriodic_zero c, aestronglyMeasurable_zero, by simp [hNorm]⟩

lemma hasWeakFO_zero (v : Coord → Fin 3 → ℝ) (d : Coord → ℝ) :
    HasWeakFO v d (0 : Coord → ℂ) (0 : Coord → ℂ) := by
  refine ⟨fun φ _ => ⟨by simp, by simp⟩, fun φ _ => by simp⟩

lemma hasWeakVec_zero (v : Coord → Fin 3 → ℝ) (d : Coord → ℝ) :
    HasWeakVec v d (0 : CProf) (0 : CProf) := by
  intro m
  exact hasWeakFO_zero v d

lemma hasWeakVec_smul_real {v : Coord → Fin 3 → ℝ} {d : Coord → ℝ} (a : ℝ) {b g : CProf}
    (h : HasWeakVec v d b g) :
    HasWeakVec v d (a • b) (a • g) := by
  have heB : (a • b : CProf) = fun x => (a : ℂ) • b x := by
    funext x; ext i; simp [Complex.real_smul]
  have heG : (a • g : CProf) = fun x => (a : ℂ) • g x := by
    funext x; ext i; simp [Complex.real_smul]
  rw [heB, heG]
  exact F10Help.hasWeakVec_smul (a : ℂ) h

lemma sqrtS_zero : sqrtS (0 : CProf) = 0 := by
  funext x; ext i; simp [sqrtS]

lemma inFlatClass_zero (c r : ℝ) : InFlatClass c r (0 : CProf) := by
  refine ⟨inHr_zero c r, 0, 0, 0,
    hasWeakVec_zero vS dZero, hasWeakVec_zero vQ0 dZero, hasWeakVec_zero vEta dZero,
    inHr_zero c r, ?_, ?_⟩
  · rw [sqrtS_zero]; exact inHr_zero c r
  · rw [sqrtS_zero]; exact inHr_zero c r

lemma inFlatClass_smul_real {c r : ℝ} (a : ℝ) {b : CProf} (hb : InFlatClass c r b) :
    InFlatClass c r (a • b) := by
  have he : (a • b : CProf) = fun x => (a : ℂ) • b x := by
    funext x; ext i; simp [Complex.real_smul]
  rw [he]
  exact F10K0Help.inFlatClass_smul (a : ℂ) hb

lemma toProf_zero_ae {c : ℝ} (hc : 0 < c) :
    toProf c (0 : HpR c) =ᵐ[hMeas c bgp] (0 : CProf) := by
  filter_upwards [toProf_ae_eq hc (0 : HpR c), Lp.coeFn_zero Axi.Merid (ENNReal.ofReal bgp) (hMeas c bgp)]
    with x hx h0
  rw [hx, h0]
  ext i
  simp [liftM]

lemma toProf_add_ae {c : ℝ} (hc : 0 < c) (F₁ F₂ : HpR c) :
    toProf c (F₁ + F₂) =ᵐ[hMeas c bgp] fun x => toProf c F₁ x + toProf c F₂ x := by
  filter_upwards [toProf_ae_eq hc (F₁ + F₂), toProf_ae_eq hc F₁, toProf_ae_eq hc F₂,
    Lp.coeFn_add F₁ F₂] with x h12 h1 h2 hadd
  rw [h12, hadd, Pi.add_apply, h1, h2]
  ext i
  simp [liftM]

lemma toProf_smul_ae {c : ℝ} (hc : 0 < c) (a : ℝ) (F : HpR c) :
    toProf c (a • F) =ᵐ[hMeas c bgp] fun x => (a : ℂ) • toProf c F x := by
  filter_upwards [toProf_ae_eq hc (a • F), toProf_ae_eq hc F, Lp.coeFn_smul a F]
    with x haF hF hsmul
  rw [haF, hsmul, Pi.smul_apply, hF]
  ext i
  simp [liftM, Complex.real_smul]

lemma isFlatResponse_zero (ν : ℝ) (μ : ℂ) :
    IsFlatResponse ν μ (0 : CProf) (0 : CProf) := by
  refine ⟨fun φ _ => ⟨by simp, by simp⟩, fun Ψ _ => ?_⟩
  have h0 : cdot (0 : CProf) Ψ = 0 := by funext x; simp [cdot]
  rw [h0]
  refine ⟨by simp, integrable_zero _ _ _, by simp⟩

lemma isFlatResponse_zero_toProf {ν c : ℝ} (hc : 0 < c) :
    IsFlatResponse ν 0 (toProf c (0 : HpR c)) (0 : CProf) :=
  F10K0Help.isFlatResponse_congr_F hc (qPeriodic_zero c) (toProf_periodic hc 0)
    (toProf_zero_ae hc).symm (isFlatResponse_zero ν 0)

lemma isFlatResponse_add_toProf {ν c : ℝ} (hc : 0 < c) {F₁ F₂ : HpR c} {b₁ b₂ : CProf}
    (h₁ : IsFlatResponse ν 0 (toProf c F₁) b₁)
    (h₂ : IsFlatResponse ν 0 (toProf c F₂) b₂) :
    IsFlatResponse ν 0 (toProf c (F₁ + F₂)) (b₁ + b₂) :=
  F10K0Help.isFlatResponse_congr_F hc
    (qPeriodic_add (toProf_periodic hc F₁) (toProf_periodic hc F₂))
    (toProf_periodic hc (F₁ + F₂))
    (toProf_add_ae hc F₁ F₂).symm
    (F10K0Help.isFlatResponse_add h₁ h₂)

lemma isFlatResponse_smul_real_toProf {ν c : ℝ} (hc : 0 < c) (a : ℝ) {F : HpR c} {b : CProf}
    (h : IsFlatResponse ν 0 (toProf c F) b) :
    IsFlatResponse ν 0 (toProf c (a • F)) (a • b) := by
  have heb : (a • b : CProf) = fun x => (a : ℂ) • b x := by
    funext x; ext i; simp [Complex.real_smul]
  have heF : (fun x => (a : ℂ) • toProf c F x) = (a • toProf c F) := by
    funext x; ext i; simp [Complex.real_smul]
  rw [heb]
  exact F10K0Help.isFlatResponse_congr_F hc
    (heF ▸ qPeriodic_smul_real a (toProf_periodic hc F))
    (toProf_periodic hc (a • F))
    (toProf_smul_ae hc a F).symm
    (F10K0Help.isFlatResponse_smul (a : ℂ) h)

/-! ## 2. Linearity and weak-derivative congruence of `flatBv` and `IsBodySource` -/

lemma flatBv_zero {ν c : ℝ} (tr : B0140.TrainSol ν c) :
    flatBv tr 0 0 0 = 0 := by
  funext x; ext i
  simp [flatBv]

lemma flatBv_add {ν c : ℝ} (tr : B0140.TrainSol ν c) (b₁ bq₁ bη₁ b₂ bq₂ bη₂ : CProf) :
    flatBv tr (b₁ + b₂) (bq₁ + bq₂) (bη₁ + bη₂) =
      flatBv tr b₁ bq₁ bη₁ + flatBv tr b₂ bq₂ bη₂ := by
  funext x; ext i
  simp only [flatBv, Pi.add_apply, PiLp.add_apply, WithLp.ofLp_toLp]
  ring

lemma flatBv_smul_real {ν c : ℝ} (tr : B0140.TrainSol ν c) (a : ℝ) (b bq bη : CProf) :
    flatBv tr (a • b) (a • bq) (a • bη) = a • flatBv tr b bq bη := by
  funext x; ext i
  simp only [flatBv, Pi.smul_apply, PiLp.smul_apply, WithLp.ofLp_toLp, Complex.real_smul]
  ring

lemma isBodySource_zero {ν c : ℝ} (tr : B0140.TrainSol ν c) :
    IsBodySource tr 0 0 0 0 := by
  refine ⟨fun φ _ => ⟨by simp, by simp⟩, fun Ψ _ => ?_⟩
  rw [flatBv_zero]
  have h0 : cdot (0 : CProf) Ψ = 0 := by funext x; simp [cdot]
  rw [h0]
  refine ⟨integrable_zero _ _ _, integrable_zero _ _ _, by simp⟩

lemma isBodySource_add {ν c : ℝ} {tr : B0140.TrainSol ν c}
    {b₁ bq₁ bη₁ g₁ b₂ bq₂ bη₂ g₂ : CProf}
    (h₁ : IsBodySource tr b₁ bq₁ bη₁ g₁)
    (h₂ : IsBodySource tr b₂ bq₂ bη₂ g₂) :
    IsBodySource tr (b₁ + b₂) (bq₁ + bq₂) (bη₁ + bη₂) (g₁ + g₂) := by
  refine ⟨fun φ hφ => ?_, fun Ψ hΨ => ?_⟩
  · obtain ⟨i1, e1⟩ := h₁.solenoidal φ hφ
    obtain ⟨i2, e2⟩ := h₂.solenoidal φ hφ
    have hfun : (fun x : Coord => (g₁ + g₂) x 0 * (cpd 1 φ x : ℂ) +
        (g₁ + g₂) x 1 * (cpd 2 φ x : ℂ)) =
        fun x => (g₁ x 0 * (cpd 1 φ x : ℂ) + g₁ x 1 * (cpd 2 φ x : ℂ)) +
          (g₂ x 0 * (cpd 1 φ x : ℂ) + g₂ x 1 * (cpd 2 φ x : ℂ)) := by
      funext x; simp only [Pi.add_apply, PiLp.add_apply]; ring
    rw [hfun]
    refine ⟨i1.add i2, ?_⟩
    rw [integral_add i1 i2, e1, e2, add_zero]
  · obtain ⟨hG₁, hB₁, hEq₁⟩ := h₁.equation Ψ hΨ
    obtain ⟨hG₂, hB₂, hEq₂⟩ := h₂.equation Ψ hΨ
    rw [flatBv_add]
    have hfunG : cdot (g₁ + g₂) Ψ = fun x => cdot g₁ Ψ x + cdot g₂ Ψ x := by
      funext x; simp only [cdot, Pi.add_apply, PiLp.add_apply, add_mul, Finset.sum_add_distrib]
    have hfunB : cdot (flatBv tr b₁ bq₁ bη₁ + flatBv tr b₂ bq₂ bη₂) Ψ =
        fun x => cdot (flatBv tr b₁ bq₁ bη₁) Ψ x + cdot (flatBv tr b₂ bq₂ bη₂) Ψ x := by
      funext x; simp only [cdot, Pi.add_apply, PiLp.add_apply, add_mul, Finset.sum_add_distrib]
    rw [hfunG, hfunB]
    refine ⟨hG₁.add hG₂, hB₁.add hB₂, ?_⟩
    rw [integral_add hG₁ hG₂, integral_add hB₁ hB₂, hEq₁, hEq₂, neg_add]

lemma isBodySource_smul_real {ν c : ℝ} {tr : B0140.TrainSol ν c} (a : ℝ)
    {b bq bη g : CProf} (h : IsBodySource tr b bq bη g) :
    IsBodySource tr (a • b) (a • bq) (a • bη) (a • g) := by
  refine ⟨fun φ hφ => ?_, fun Ψ hΨ => ?_⟩
  · obtain ⟨i1, e1⟩ := h.solenoidal φ hφ
    have hfun : (fun x : Coord => (a • g) x 0 * (cpd 1 φ x : ℂ) +
        (a • g) x 1 * (cpd 2 φ x : ℂ)) =
        fun x => (a : ℂ) * (g x 0 * (cpd 1 φ x : ℂ) + g x 1 * (cpd 2 φ x : ℂ)) := by
      funext x; simp only [Pi.smul_apply, PiLp.smul_apply, Complex.real_smul]; ring
    rw [hfun]
    refine ⟨i1.const_mul (a : ℂ), ?_⟩
    rw [integral_const_mul, e1, mul_zero]
  · obtain ⟨hG, hB, hEq⟩ := h.equation Ψ hΨ
    rw [flatBv_smul_real]
    have hfunG : cdot (a • g) Ψ = fun x => (a : ℂ) * cdot g Ψ x := by
      funext x
      simp only [cdot, Pi.smul_apply, PiLp.smul_apply, Complex.real_smul, mul_assoc, ← Finset.mul_sum]
    have hfunB : cdot (a • flatBv tr b bq bη) Ψ =
        fun x => (a : ℂ) * cdot (flatBv tr b bq bη) Ψ x := by
      funext x
      simp only [cdot, Pi.smul_apply, PiLp.smul_apply, Complex.real_smul, mul_assoc, ← Finset.mul_sum]
    rw [hfunG, hfunB]
    refine ⟨hG.const_mul (a : ℂ), hB.const_mul (a : ℂ), ?_⟩
    rw [integral_const_mul, integral_const_mul, hEq, mul_neg]

lemma isBodySource_congr_deriv {ν c : ℝ} {tr : B0140.TrainSol ν c}
    {b bq₁ bη₁ bq₂ bη₂ g : CProf}
    (hq : ∀ᵐ x : Coord, 0 < x.1 → bq₁ x = bq₂ x)
    (hη : ∀ᵐ x : Coord, 0 < x.1 → bη₁ x = bη₂ x)
    (h : IsBodySource tr b bq₁ bη₁ g) :
    IsBodySource tr b bq₂ bη₂ g := by
  refine ⟨h.solenoidal, fun Ψ hΨ => ?_⟩
  obtain ⟨hG, hB, hEq⟩ := h.equation Ψ hΨ
  have hae : cdot (flatBv tr b bq₁ bη₁) Ψ =ᵐ[volume] cdot (flatBv tr b bq₂ bη₂) Ψ := by
    filter_upwards [hq, hη] with x hqx hηx
    by_cases hpos : 0 < x.1
    · have hbv : flatBv tr b bq₁ bη₁ x = flatBv tr b bq₂ bη₂ x := by
        ext i
        simp only [flatBv, WithLp.ofLp_toLp, hqx hpos, hηx hpos]
      simp only [cdot, hbv]
    · have h0 : ∀ i : Fin 2, Ψ x i = 0 :=
        fun i => F10K0Help.isCoordTest_zero_of_nonpos (hΨ.smooth i) hpos
      simp [cdot, h0]
  refine ⟨hG, hB.congr hae, ?_⟩
  rw [hEq, integral_congr_ae hae]

lemma profCurl_zero : profCurl (0 : CProf) (0 : CProf) = 0 := by
  funext x
  simp [profCurl]

lemma profCurl_add (gq₁ gη₁ gq₂ gη₂ : CProf) :
    profCurl (gq₁ + gq₂) (gη₁ + gη₂) = profCurl gq₁ gη₁ + profCurl gq₂ gη₂ := by
  funext x
  simp only [profCurl, Pi.add_apply, PiLp.add_apply]
  ring

lemma profCurl_smul_real (a : ℝ) (gq gη : CProf) :
    profCurl (a • gq) (a • gη) = fun x => (a : ℂ) * profCurl gq gη x := by
  funext x
  simp only [profCurl, Pi.smul_apply, PiLp.smul_apply, Complex.real_smul]
  ring

lemma hasZeroCirculationR_zero (c : ℝ) :
    HasZeroCirculationR c (0 : B0579.Plane → ℝ) :=
  ⟨integrableOn_zero, by simp⟩

lemma hasZeroCirculationR_add {c : ℝ} {f₁ f₂ : B0579.Plane → ℝ}
    (h₁ : HasZeroCirculationR c f₁) (h₂ : HasZeroCirculationR c f₂) :
    HasZeroCirculationR c (f₁ + f₂) := by
  refine ⟨h₁.1.add h₂.1, ?_⟩
  change ∫ x in B0579.cell c, (f₁ x + f₂ x) = 0
  rw [integral_add h₁.1 h₂.1, h₁.2, h₂.2, add_zero]

lemma hasZeroCirculationR_smul_real {c : ℝ} (a : ℝ) {f : B0579.Plane → ℝ}
    (h : HasZeroCirculationR c f) :
    HasZeroCirculationR c (a • f) := by
  refine ⟨h.1.smul a, ?_⟩
  change ∫ x in B0579.cell c, a * f x = 0
  rw [integral_const_mul, h.2, mul_zero]

lemma sliceH1Norm_congr_ae_cell {c s : ℝ} {g₁ gq₁ gη₁ g₂ gq₂ gη₂ : CProf}
    (hg : (fun z => g₁ (s, z)) =ᵐ[volume.restrict (B0579.cell c)] (fun z => g₂ (s, z)))
    (hgq : (fun z => gq₁ (s, z)) =ᵐ[volume.restrict (B0579.cell c)] (fun z => gq₂ (s, z)))
    (hgη : (fun z => gη₁ (s, z)) =ᵐ[volume.restrict (B0579.cell c)] (fun z => gη₂ (s, z))) :
    sliceH1Norm c g₁ gq₁ gη₁ s = sliceH1Norm c g₂ gq₂ gη₂ s := by
  unfold sliceH1Norm
  rw [eLpNorm_congr_ae hg, eLpNorm_congr_ae hgq, eLpNorm_congr_ae hgη]

lemma sliceXmNorm_profCurl_congr_ae_cell {c m s : ℝ} {gq₁ gη₁ gq₂ gη₂ : CProf}
    (hgq : (fun z => gq₁ (s, z)) =ᵐ[volume.restrict (B0579.cell c)] (fun z => gq₂ (s, z)))
    (hgη : (fun z => gη₁ (s, z)) =ᵐ[volume.restrict (B0579.cell c)] (fun z => gη₂ (s, z))) :
    sliceXmNorm c m (profCurl gq₁ gη₁) s = sliceXmNorm c m (profCurl gq₂ gη₂) s := by
  have hae_res : (fun z => profCurl gq₁ gη₁ (s, z)) =ᵐ[volume.restrict (B0579.cell c)]
      (fun z => profCurl gq₂ gη₂ (s, z)) := by
    filter_upwards [hgq, hgη] with z hqz hηz
    simp only [profCurl, hqz, hηz]
  have hae_cm : (fun z => profCurl gq₁ gη₁ (s, z)) =ᵐ[B0579.cellMeasure c m]
      (fun z => profCurl gq₂ gη₂ (s, z)) :=
    (B0579.cellMeasure_ac c m).ae_le hae_res
  unfold sliceXmNorm
  exact eLpNorm_congr_ae hae_cm

/-! ## 3. Unconditional construction of `b0Of, b0qOf, b0ηOf, gOf, gqOf, gηOf : HpR p.c →ₗ[ℝ] CProf` -/

/-- From `BodySourceBound` and `profileGraphFlat_bgp`, for every `BgRegime` parameter point `p` with
`p.ν ≤ ν₀` and `p.ageCut = Sig`, there exist `ℝ`-linear maps
`b0Of, b0qOf, b0ηOf, gOf, gqOf, gηOf : HpR p.c →ₗ[ℝ] CProf` such that for every `F : HpR p.c`:
1. `b0Of F` is in `InFlatClass p.c bgp` and solves `IsFlatResponse p.ν 0 (toProf p.c F) (b0Of F)`
   with weak derivatives `b0qOf F, b0ηOf F`;
2. `gOf F` is `c`-periodic in `q`, has weak derivatives `gqOf F, gηOf F`, and solves
   `IsBodySource p.train (b0Of F) (b0qOf F) (b0ηOf F) (gOf F)`;
3. there exist `g, gq, gη : CProf` solving `IsBodySource p.train (b0Of F) (b0qOf F) (b0ηOf F) g`
   with measurable `sliceH1Norm` and `sliceXmNorm (profCurl gq gη)`, vanishing cell circulation
   of `profCurl gq gη` a.e. on `(0, p.H]`, and combined `sLpNorm (13 / 8)` bound
   `≤ ENNReal.ofReal (C_src * (p.ν ^ k_src)⁻¹ * ‖F‖)`. -/
theorem exists_linear_b0_and_pointwise_source
    (hBS : BodySourceBound)
    {m Sig dm dp : ℝ} (hm : 8 < m) (hSig : 0 < Sig) (hdm : 0 < dm) :
    ∃ (C_src : ℝ) (k_src : ℕ) (ν₀ : ℝ), 0 < C_src ∧ 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig →
        ∃ (b0Of b0qOf b0ηOf gOf gqOf gηOf : HpR p.c →ₗ[ℝ] CProf),
          ∀ F : HpR p.c,
            InFlatClass p.c bgp (b0Of F) ∧
            IsFlatResponse p.ν 0 (toProf p.c F) (b0Of F) ∧
            HasWeakVec vQ0 dZero (b0Of F) (b0qOf F) ∧
            HasWeakVec vEta dZero (b0Of F) (b0ηOf F) ∧
            QPeriodic p.c (gOf F) ∧
            HasWeakVec vQ0 dZero (gOf F) (gqOf F) ∧
            HasWeakVec vEta dZero (gOf F) (gηOf F) ∧
            IsBodySource p.train (b0Of F) (b0qOf F) (b0ηOf F) (gOf F) ∧
            ∃ g gq gη : CProf,
              QPeriodic p.c g ∧
              HasWeakVec vQ0 dZero g gq ∧
              HasWeakVec vEta dZero g gη ∧
              IsBodySource p.train (b0Of F) (b0qOf F) (b0ηOf F) g ∧
              Measurable (sliceH1Norm p.c g gq gη) ∧
              Measurable (sliceXmNorm p.c m (profCurl gq gη)) ∧
              sLpNorm (13 / 8) p.H (sliceH1Norm p.c g gq gη) +
                  sLpNorm (13 / 8) p.H (sliceXmNorm p.c m (profCurl gq gη)) ≤
                ENNReal.ofReal (C_src * (p.ν ^ k_src)⁻¹ * ‖F‖) ∧
              (∀ᵐ s ∂volume, s ∈ Ioc 0 p.H →
                IntegrableOn (fun z => profCurl gq gη (s, z)) (B0579.cell p.c) volume ∧
                  ∫ z in B0579.cell p.c, profCurl gq gη (s, z) = 0) := by
  obtain ⟨C_src, k_src, ν₀, hC_src, hν₀, hBS_p⟩ := hBS m hm Sig hSig dm dp hdm
  obtain ⟨_, _, hPGF⟩ := profileGraphFlat_bgp
  refine ⟨C_src, k_src, ν₀, hC_src, hν₀, ?_⟩
  intro p d hreg hν hAge
  have hν_pos : 0 < p.ν := p.ν_pos
  have hc_pos : 0 < p.c := p.c_pos
  have hH_eq : p.H = Sig / p.ν := by rw [Params.H, hAge]
  -- Pointwise existence of (b0, b0q, b0η, g, gq, gη) for each F : HpR p.c
  have h_pt : ∀ F : HpR p.c, ∃ b0 b0q b0η g gq gη : CProf,
      InFlatClass p.c bgp b0 ∧
      IsFlatResponse p.ν 0 (toProf p.c F) b0 ∧
      HasWeakVec vQ0 dZero b0 b0q ∧
      HasWeakVec vEta dZero b0 b0η ∧
      QPeriodic p.c g ∧
      HasWeakVec vQ0 dZero g gq ∧
      HasWeakVec vEta dZero g gη ∧
      IsBodySource p.train b0 b0q b0η g := by
    intro F
    obtain ⟨b0, hb0_cls, hb0_resp, _, _⟩ :=
      hPGF p.ν p.c hν_pos hc_pos (toProf p.c F) (inHr_toProf hc_pos F)
    obtain ⟨b0q, b0η, g, gq, gη, hb0q, hb0η, hg_per, hgq, hgη, hg_src, _⟩ :=
      hBS_p p d hreg hν (toProf p.c F) b0 (inHr_toProf hc_pos F) hb0_cls hb0_resp
    exact ⟨b0, b0q, b0η, g, gq, gη, hb0_cls, hb0_resp, hb0q, hb0η, hg_per, hgq, hgη, hg_src⟩
  -- Extend from a Hamel basis of HpR p.c over ℝ
  let B := Module.Basis.ofVectorSpace ℝ (HpR p.c)
  choose b0_bas b0q_bas b0η_bas g_bas gq_bas gη_bas h_bas using fun i => h_pt (B i)
  let b0Of : HpR p.c →ₗ[ℝ] CProf := B.constr ℝ b0_bas
  let b0qOf : HpR p.c →ₗ[ℝ] CProf := B.constr ℝ b0q_bas
  let b0ηOf : HpR p.c →ₗ[ℝ] CProf := B.constr ℝ b0η_bas
  let gOf : HpR p.c →ₗ[ℝ] CProf := B.constr ℝ g_bas
  let gqOf : HpR p.c →ₗ[ℝ] CProf := B.constr ℝ gq_bas
  let gηOf : HpR p.c →ₗ[ℝ] CProf := B.constr ℝ gη_bas
  have h_lin_props : ∀ F : HpR p.c,
      InFlatClass p.c bgp (b0Of F) ∧
      IsFlatResponse p.ν 0 (toProf p.c F) (b0Of F) ∧
      HasWeakVec vQ0 dZero (b0Of F) (b0qOf F) ∧
      HasWeakVec vEta dZero (b0Of F) (b0ηOf F) ∧
      QPeriodic p.c (gOf F) ∧
      HasWeakVec vQ0 dZero (gOf F) (gqOf F) ∧
      HasWeakVec vEta dZero (gOf F) (gηOf F) ∧
      IsBodySource p.train (b0Of F) (b0qOf F) (b0ηOf F) (gOf F) := by
    let S : Submodule ℝ (HpR p.c) :=
      { carrier := {F |
          InFlatClass p.c bgp (b0Of F) ∧
          IsFlatResponse p.ν 0 (toProf p.c F) (b0Of F) ∧
          HasWeakVec vQ0 dZero (b0Of F) (b0qOf F) ∧
          HasWeakVec vEta dZero (b0Of F) (b0ηOf F) ∧
          QPeriodic p.c (gOf F) ∧
          HasWeakVec vQ0 dZero (gOf F) (gqOf F) ∧
          HasWeakVec vEta dZero (gOf F) (gηOf F) ∧
          IsBodySource p.train (b0Of F) (b0qOf F) (b0ηOf F) (gOf F)}
        zero_mem' := by
          change InFlatClass p.c bgp (b0Of 0) ∧ _
          simp only [map_zero]
          exact ⟨inFlatClass_zero p.c bgp, isFlatResponse_zero_toProf hc_pos,
            hasWeakVec_zero vQ0 dZero, hasWeakVec_zero vEta dZero,
            qPeriodic_zero p.c, hasWeakVec_zero vQ0 dZero, hasWeakVec_zero vEta dZero,
            isBodySource_zero p.train⟩
        add_mem' := by
          intro F₁ F₂ h₁ h₂
          change InFlatClass p.c bgp (b0Of (F₁ + F₂)) ∧ _
          simp only [map_add]
          have hr1 : (1 : ℝ) ≤ bgp := by norm_num [bgp]
          exact ⟨F10K0Help.inFlatClass_add hr1 h₁.1 h₂.1,
            isFlatResponse_add_toProf hc_pos h₁.2.1 h₂.2.1,
            F10Help.hasWeakVec_add' h₁.2.2.1 h₂.2.2.1,
            F10Help.hasWeakVec_add' h₁.2.2.2.1 h₂.2.2.2.1,
            qPeriodic_add h₁.2.2.2.2.1 h₂.2.2.2.2.1,
            F10Help.hasWeakVec_add' h₁.2.2.2.2.2.1 h₂.2.2.2.2.2.1,
            F10Help.hasWeakVec_add' h₁.2.2.2.2.2.2.1 h₂.2.2.2.2.2.2.1,
            isBodySource_add h₁.2.2.2.2.2.2.2 h₂.2.2.2.2.2.2.2⟩
        smul_mem' := by
          intro a F hF
          change InFlatClass p.c bgp (b0Of (a • F)) ∧ _
          simp only [map_smul]
          exact ⟨inFlatClass_smul_real a hF.1,
            isFlatResponse_smul_real_toProf hc_pos a hF.2.1,
            hasWeakVec_smul_real a hF.2.2.1,
            hasWeakVec_smul_real a hF.2.2.2.1,
            qPeriodic_smul_real a hF.2.2.2.2.1,
            hasWeakVec_smul_real a hF.2.2.2.2.2.1,
            hasWeakVec_smul_real a hF.2.2.2.2.2.2.1,
            isBodySource_smul_real a hF.2.2.2.2.2.2.2⟩ }
    have h_range : Set.range B ⊆ (S : Set (HpR p.c)) := by
      rintro _ ⟨i, rfl⟩
      change InFlatClass p.c bgp (b0Of (B i)) ∧ _
      simp only [b0Of, b0qOf, b0ηOf, gOf, gqOf, gηOf, Module.Basis.constr_basis]
      exact h_bas i
    have h_top : S = ⊤ :=
      top_unique (by rw [← B.span_eq]; exact Submodule.span_le.2 h_range)
    intro F
    have hmem : F ∈ S := by rw [h_top]; exact Submodule.mem_top
    exact hmem
  refine ⟨b0Of, b0qOf, b0ηOf, gOf, gqOf, gηOf, fun F => ?_⟩
  obtain ⟨hb0_cls, hb0_resp, hb0q, hb0η, hgOf_per, hgqOf, hgηOf, hgOf_src⟩ := h_lin_props F
  obtain ⟨b0q', b0η', g, gq, gη, hb0q', hb0η', hg_per, hgq, hgη, hg_src',
      hm_H1, hm_Xm, h_sLp, h_circ⟩ :=
    hBS_p p d hreg hν (toProf p.c F) (b0Of F) (inHr_toProf hc_pos F) hb0_cls hb0_resp
  have hq_eq : ∀ᵐ x : Coord, 0 < x.1 → b0q' x = b0qOf F x :=
    GradBoundHelp.hasWeakVec_unique hb0q' hb0q
  have hη_eq : ∀ᵐ x : Coord, 0 < x.1 → b0η' x = b0ηOf F x :=
    GradBoundHelp.hasWeakVec_unique hb0η' hb0η
  have hg_src : IsBodySource p.train (b0Of F) (b0qOf F) (b0ηOf F) g :=
    isBodySource_congr_deriv hq_eq hη_eq hg_src'
  rw [← hH_eq] at h_sLp h_circ
  have h_sLp' : sLpNorm (13 / 8) p.H (sliceH1Norm p.c g gq gη) +
      sLpNorm (13 / 8) p.H (sliceXmNorm p.c m (profCurl gq gη)) ≤
        ENNReal.ofReal (C_src * (p.ν ^ k_src)⁻¹ * ‖F‖) := by
    refine h_sLp.trans_eq ?_
    rw [hNorm_toProf hc_pos F, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
  exact ⟨hb0_cls, hb0_resp, hb0q, hb0η, hgOf_per, hgqOf, hgηOf, hgOf_src,
    g, gq, gη, hg_per, hgq, hgη, hg_src, hm_H1, hm_Xm, h_sLp', h_circ⟩

/-! ## 4. Norm equivalence and Hardy `L¹` bound for `curlSourceOf` -/

/-- If `w : Xmc c m` agrees a.e. on `B0579.cell c` with `profCurl gq gη (s, ·)`, then
`‖w‖ₑ = sliceXmNorm c m (profCurl gq gη) s`. -/
theorem enorm_Xmc_eq_sliceXmNorm_of_ae_cell {c m s : ℝ} {w : Xmc c m} {gq gη : CProf}
    (hae : ∀ᵐ x ∂volume, x ∈ B0579.cell c → ((w x : ℝ) : ℂ) = profCurl gq gη (s, x)) :
    ‖w‖ₑ = sliceXmNorm c m (profCurl gq gη) s := by
  have hae_res : (fun x => ((w x : ℝ) : ℂ)) =ᵐ[volume.restrict (B0579.cell c)]
      fun x => profCurl gq gη (s, x) :=
    (ae_restrict_iff' (B0579.measurableSet_cell c)).mpr hae
  have hae_cm : (fun x => ((w x : ℝ) : ℂ)) =ᵐ[B0579.cellMeasure c m]
      fun x => profCurl gq gη (s, x) :=
    (B0579.cellMeasure_ac c m).ae_le hae_res
  unfold sliceXmNorm
  rw [← eLpNorm_congr_ae hae_cm]
  have h_enorm : eLpNorm (fun x => ((w x : ℝ) : ℂ)) 2 (B0579.cellMeasure c m) =
      eLpNorm (w : B0579.Plane → ℝ) 2 (B0579.cellMeasure c m) := by
    refine eLpNorm_congr_norm_ae (Eventually.of_forall fun x => ?_)
    exact Complex.norm_real (w x)
  rw [h_enorm, ← Lp.enorm_def]

/-- From `curl_L1_le_of_sLpNorm` (`PartII-b:T01`), if `curlSource : ℝ → Xmc p.c m` is Bochner
integrable on `Ioc 0 p.H` and represents `profCurl gq gη (s, ·)` a.e. on `B0579.cell p.c` for a.e.
`s ∈ Ioc 0 p.H`, then its Bochner `L¹(0, p.H; X_{m,c})` integral is bounded by
`(14^{7/11} Sig^{1/22} p.ν⁻¹) * (C_src * (p.ν ^ k_src)⁻¹) * ‖F‖`. -/
theorem integral_norm_curlSource_le
    {p : Params} {m Sig C_src : ℝ} {k_src : ℕ}
    (hSig : 0 < Sig) (hν1 : p.ν ≤ 1) (hAge : p.ageCut = Sig) (hC_src : 0 < C_src)
    (F : HpR p.c) {gq gη : CProf} {curlSource : ℝ → Xmc p.c m}
    (hm_Xm : Measurable (sliceXmNorm p.c m (profCurl gq gη)))
    (h_sLp_Xm : sLpNorm (13 / 8) p.H (sliceXmNorm p.c m (profCurl gq gη)) ≤
      ENNReal.ofReal (C_src * (p.ν ^ k_src)⁻¹ * ‖F‖))
    (h_int : IntegrableOn curlSource (Ioc 0 p.H) volume)
    (h_ae_cell : ∀ᵐ s ∂volume, s ∈ Ioc 0 p.H →
      ∀ᵐ x ∂volume, x ∈ B0579.cell p.c →
        ((curlSource s x : ℝ) : ℂ) = profCurl gq gη (s, x)) :
    ∫ t in Ioc 0 p.H, ‖curlSource t‖ ≤
      (14 ^ (7 / 11 : ℝ) * Sig ^ (1 / 22 : ℝ) * p.ν⁻¹) *
        (C_src * (p.ν ^ k_src)⁻¹) * ‖F‖ := by
  have hν0 : 0 < p.ν := p.ν_pos
  have hH_eq : p.H = Sig / p.ν := by rw [Params.H, hAge]
  have hae_enorm : ∀ᵐ s ∂volume.restrict (Ioc 0 p.H),
      ‖curlSource s‖ₑ = sliceXmNorm p.c m (profCurl gq gη) s := by
    filter_upwards [(ae_restrict_iff' measurableSet_Ioc).mpr h_ae_cell] with s hs
    exact enorm_Xmc_eq_sliceXmNorm_of_ae_cell hs
  have h_lint_eq : (∫⁻ t in Ioc 0 p.H, ‖curlSource t‖ₑ) =
      ∫⁻ t in Ioc 0 p.H, sliceXmNorm p.c m (profCurl gq gη) t :=
    lintegral_congr_ae hae_enorm
  have h_hardy := curl_L1_le_of_sLpNorm hSig hν0 hν1 hm_Xm
  rw [← hH_eq] at h_hardy
  set R : ℝ :=
    (14 ^ (7 / 11 : ℝ) * Sig ^ (1 / 22 : ℝ) * p.ν⁻¹) * (C_src * (p.ν ^ k_src)⁻¹) * ‖F‖
  have hR_nn : 0 ≤ R := by dsimp [R]; positivity
  have h_lint_le : (∫⁻ t in Ioc 0 p.H, ‖curlSource t‖ₑ) ≤ ENNReal.ofReal R := by
    rw [h_lint_eq]
    calc ∫⁻ t in Ioc 0 p.H, sliceXmNorm p.c m (profCurl gq gη) t
        ≤ ENNReal.ofReal (14 ^ (7 / 11 : ℝ) * Sig ^ (1 / 22 : ℝ) * p.ν⁻¹) *
            sLpNorm (13 / 8) p.H (sliceXmNorm p.c m (profCurl gq gη)) := h_hardy
      _ ≤ ENNReal.ofReal (14 ^ (7 / 11 : ℝ) * Sig ^ (1 / 22 : ℝ) * p.ν⁻¹) *
            ENNReal.ofReal (C_src * (p.ν ^ k_src)⁻¹ * ‖F‖) :=
          mul_le_mul_of_nonneg_left h_sLp_Xm zero_le
      _ = ENNReal.ofReal R := by
          dsimp [R]
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  rw [← ofReal_integral_norm_eq_lintegral_enorm h_int] at h_lint_le
  exact (ENNReal.ofReal_le_ofReal_iff hR_nn).1 h_lint_le

/-- If `φ =ᵐ 0` on `B0579.cell c` (`c > 0`) and `g ∈ L²(B0579.cell c)` is a weak cylinder
derivative of `φ`, then `g =ᵐ 0` on `B0579.cell c`. -/
theorem hasWeakCellDerivC_ae_zero_of_ae_zero {c : ℝ} (hc : 0 < c) {j : Fin 2}
    {φ g : ℝ × ℝ → ℂ}
    (hφ : φ =ᵐ[volume.restrict (B0579.cell c)] 0)
    (hg : MemLp g 2 (volume.restrict (B0579.cell c)))
    (hw : IIIa.HasWeakCellDerivC c j φ g) :
    g =ᵐ[volume.restrict (B0579.cell c)] 0 := by
  have hzero_pair : ∀ ψ : ℝ × ℝ → ℝ, UnforcedLeray.Sob.IsCylTest c ψ →
      ∫ z in UnforcedLeray.Cyl.cell c, ψ z * (g z).re = 0 ∧
        ∫ z in UnforcedLeray.Cyl.cell c, ψ z * (g z).im = 0 := by
    intro ψ hψ
    have hψB := Short.IIIa.CTE.T20_2.B0579_of_sob hψ
    have hφ0 : ∫ x in B0579.cell c, φ x * (B0579.pd j ψ x : ℂ) = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hφ] with x hx
      simp [hx]
    have hg0 : ∫ x in B0579.cell c, g x * (ψ x : ℂ) = 0 := by
      have he := hw.2 ψ hψB
      rw [hφ0] at he
      exact neg_eq_zero.mp he.symm
    have hInt : IntegrableOn (fun x => g x * (ψ x : ℂ)) (UnforcedLeray.Cyl.cell c) := by
      rw [← Short.IIIa.CTE.T20_2.cell_eq]
      exact (hw.1 ψ hψB).2
    rw [Short.IIIa.CTE.T20_2.cell_eq] at hg0
    obtain ⟨hre, him⟩ := Short.IIIa.CTE.T20_2.integral_re_im hInt hg0
    refine ⟨?_, ?_⟩
    · convert hre using 2 with z
      simp [Complex.mul_re, mul_comm]
    · convert him using 2 with z
      simp [Complex.mul_im, mul_comm]
  have hg_cell : MemLp g 2 (UnforcedLeray.Cyl.cellμ c) := by
    rwa [Short.IIIa.CTE.T20_2.cellμ_eq_B0579]
  have hre_mem : MemLp (fun z => (g z).re) 2 (UnforcedLeray.Cyl.cellμ c) :=
    Complex.reCLM.comp_memLp' hg_cell
  have him_mem : MemLp (fun z => (g z).im) 2 (UnforcedLeray.Cyl.cellμ c) :=
    Complex.imCLM.comp_memLp' hg_cell
  have hre0 : (fun z => (g z).re) =ᵐ[UnforcedLeray.Cyl.cellμ c] 0 := by
    refine Short.IIIa.CTE.T20_2.ae_zero_of_pairings hc hre_mem fun n ψ hψ => ⟨?_, ?_⟩
    · exact (hzero_pair _ (UnforcedLeray.Cyl.isCylTest_cosTest hc n hψ)).1
    · exact (hzero_pair _ (UnforcedLeray.Cyl.isCylTest_sinTest hc n hψ)).1
  have him0 : (fun z => (g z).im) =ᵐ[UnforcedLeray.Cyl.cellμ c] 0 := by
    refine Short.IIIa.CTE.T20_2.ae_zero_of_pairings hc him_mem fun n ψ hψ => ⟨?_, ?_⟩
    · exact (hzero_pair _ (UnforcedLeray.Cyl.isCylTest_cosTest hc n hψ)).2
    · exact (hzero_pair _ (UnforcedLeray.Cyl.isCylTest_sinTest hc n hψ)).2
  rw [← Short.IIIa.CTE.T20_2.cellμ_eq_B0579]
  filter_upwards [hre0, him0] with z hre him
  exact Complex.ext hre him

end LinearBodySourceHelp

open LinearBodySourceHelp

/-! ## 5. Linear body-source and Bochner curl-source lift step and conditional assembly -/

/-- **Remaining linear body-source and Bochner curl-source lift step for `PartII-b:F6/1`**
(SP 2213–2239, 2265–2267): given the unconditionally constructed `ℝ`-linear maps
`b0Of, b0qOf, b0ηOf : HpR p.c →ₗ[ℝ] CProf` and their pointwise `BodySourceBound` witnesses on
`(0, p.H]`, package the projected body source `gOf, gqOf, gηOf : HpR p.c →ₗ[ℝ] CProf` and the
Bochner-integrable zero-circulation vorticity source `curlSourceOf : HpR p.c →ₗ[ℝ] (ℝ → Xmc p.c m)`
on `Ioc 0 p.H` as `ℝ`-linear maps satisfying the `sLpNorm (13 / 8)` bounds. -/
def LinearBodySourceLiftStep : Prop :=
  ∀ (m : ℝ), 8 < m →
  ∀ (p : Params) (d dm dp : ℝ), BgRegime p d dm dp → p.ν ≤ 1 →
  ∀ (C_src : ℝ) (k_src : ℕ), 0 < C_src →
  ∀ (b0Of b0qOf b0ηOf gOf gqOf gηOf : HpR p.c →ₗ[ℝ] CProf),
    (∀ F : HpR p.c,
      InFlatClass p.c bgp (b0Of F) ∧
      IsFlatResponse p.ν 0 (toProf p.c F) (b0Of F) ∧
      HasWeakVec vQ0 dZero (b0Of F) (b0qOf F) ∧
      HasWeakVec vEta dZero (b0Of F) (b0ηOf F) ∧
      QPeriodic p.c (gOf F) ∧
      HasWeakVec vQ0 dZero (gOf F) (gqOf F) ∧
      HasWeakVec vEta dZero (gOf F) (gηOf F) ∧
      IsBodySource p.train (b0Of F) (b0qOf F) (b0ηOf F) (gOf F) ∧
      ∃ g gq gη : CProf,
        QPeriodic p.c g ∧
        HasWeakVec vQ0 dZero g gq ∧
        HasWeakVec vEta dZero g gη ∧
        IsBodySource p.train (b0Of F) (b0qOf F) (b0ηOf F) g ∧
        Measurable (sliceH1Norm p.c g gq gη) ∧
        Measurable (sliceXmNorm p.c m (profCurl gq gη)) ∧
        sLpNorm (13 / 8) p.H (sliceH1Norm p.c g gq gη) +
            sLpNorm (13 / 8) p.H (sliceXmNorm p.c m (profCurl gq gη)) ≤
          ENNReal.ofReal (C_src * (p.ν ^ k_src)⁻¹ * ‖F‖) ∧
        (∀ᵐ s ∂volume, s ∈ Ioc 0 p.H →
          IntegrableOn (fun z => profCurl gq gη (s, z)) (B0579.cell p.c) volume ∧
            ∫ z in B0579.cell p.c, profCurl gq gη (s, z) = 0)) →
    ∃ (curlSourceOf : HpR p.c →ₗ[ℝ] (ℝ → Xmc p.c m)),
      ∀ F : HpR p.c,
        Measurable (sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F)) ∧
        Measurable (sliceXmNorm p.c m (profCurl (gqOf F) (gηOf F))) ∧
        sLpNorm (13 / 8) p.H (sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F)) +
            sLpNorm (13 / 8) p.H (sliceXmNorm p.c m (profCurl (gqOf F) (gηOf F))) ≤
          ENNReal.ofReal (C_src * (p.ν ^ k_src)⁻¹ * ‖F‖) ∧
        IntegrableOn (curlSourceOf F) (Ioc 0 p.H) volume ∧
        (∀ᵐ t ∂volume, t ∈ Ioc 0 p.H → HasZeroCirculationR p.c (curlSourceOf F t)) ∧
        (∀ᵐ s ∂volume, s ∈ Ioc 0 p.H →
          ∀ᵐ x ∂volume, x ∈ B0579.cell p.c →
            ((curlSourceOf F s x : ℝ) : ℂ) = profCurl (gqOf F) (gηOf F) (s, x))

/-- **Assembly of `LinearBodySourceMap` (`PartII-b:F6/1`)** from the proved linear flat-response
and body-source construction `exists_linear_b0_and_pointwise_source`, the proved Hardy `L¹` bound
`integral_norm_curlSource_le`, and `LinearBodySourceLiftStep`. -/
theorem linearBodySourceMap_of
    (hLift : LinearBodySourceLiftStep) :
    LinearBodySourceMap := by
  intro hBS m hm Sig lam q hSig _hEig dm dp hdm
  obtain ⟨C_src, k_src, ν_s, hC_src, hν_s, h_b0⟩ :=
    exists_linear_b0_and_pointwise_source hBS hm hSig hdm
  refine ⟨C_src, k_src, ν_s, hC_src, hν_s, ?_⟩
  intro p d hreg hν_s' hν1 hAge _hMode
  obtain ⟨b0Of, b0qOf, b0ηOf, gOf, gqOf, gηOf, hb0_F⟩ := h_b0 p d hreg hν_s' hAge
  obtain ⟨curlSourceOf, hg_F⟩ :=
    hLift m hm p d dm dp hreg hν1 C_src k_src hC_src b0Of b0qOf b0ηOf gOf gqOf gηOf hb0_F
  refine ⟨b0Of, b0qOf, b0ηOf, gOf, gqOf, gηOf, curlSourceOf, fun F => ?_⟩
  obtain ⟨hb0_cls, hb0_resp, hb0q, hb0η, hg_per, hgq, hgη, hg_src, _⟩ := hb0_F F
  obtain ⟨hm_H1, hm_Xm, h_sLp, h_int, h_circ, h_ae_cell⟩ := hg_F F
  have h_sLp_H1 : sLpNorm (13 / 8) p.H (sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F)) ≤
      ENNReal.ofReal (C_src * (p.ν ^ k_src)⁻¹ * ‖F‖) :=
    le_self_add.trans h_sLp
  have h_sLp_Xm : sLpNorm (13 / 8) p.H (sliceXmNorm p.c m (profCurl (gqOf F) (gηOf F))) ≤
      ENNReal.ofReal (C_src * (p.ν ^ k_src)⁻¹ * ‖F‖) :=
    le_add_self.trans h_sLp
  have h_L1 :=
    integral_norm_curlSource_le hSig hν1 hAge hC_src F hm_Xm h_sLp_Xm h_int h_ae_cell
  exact ⟨hb0_cls, hb0_resp, hb0q, hb0η, hg_per, hgq, hgη, hg_src, hm_H1, h_sLp_H1,
    h_int, h_circ, h_ae_cell, h_L1⟩

/-! ## 6. Unconditional proof of `LinearBodySourceMap` (`PartII-b:F6/1`) -/

namespace LinearBodySourceProof

/-! ### 6A. Real-valued projection `F10K0Help.reProf` and real profiles -/

private def IsRealProf (u : CProf) : Prop :=
  ∀ (x : Coord) (i : Fin 2), (u x i).im = 0

private lemma isRealProf_reProf (u : CProf) : IsRealProf (F10K0Help.reProf u) := by
  intro x i
  simp [F10K0Help.reProf_apply]

private lemma isRealProf_ite_pos {u : CProf} (hu : IsRealProf u) :
    IsRealProf (fun x => if 0 < x.1 then u x else 0) := by
  intro x i
  by_cases hx : 0 < x.1 <;> simp [hx, hu x i]

private lemma profCurl_eq_ofReal_re {gq gη : CProf}
    (hq : IsRealProf gq) (hη : IsRealProf gη) (x : Coord) :
    (((profCurl gq gη x).re : ℝ) : ℂ) = profCurl gq gη x := by
  apply Complex.ext
  · simp
  · simp [profCurl, hq x 1, hη x 0]

private lemma qPeriodic_reProf {c : ℝ} {u : CProf} (hu : QPeriodic c u) :
    QPeriodic c (F10K0Help.reProf u) := by
  filter_upwards [hu] with x hx
  simp only [F10K0Help.reProf, hx]

private lemma reProf_flatBv {ν c : ℝ} (tr : B0140.TrainSol ν c) (b bq bη : CProf) :
    F10K0Help.reProf (flatBv tr b bq bη) =
      flatBv tr (F10K0Help.reProf b) (F10K0Help.reProf bq) (F10K0Help.reProf bη) := by
  funext x
  ext i
  simp [F10K0Help.reProf, liftM, reM, flatBv, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im]

private lemma isBodySource_reProf {ν c : ℝ} {tr : B0140.TrainSol ν c}
    {b0 b0q b0η g : CProf} (h : IsBodySource tr b0 b0q b0η g) :
    IsBodySource tr (F10K0Help.reProf b0) (F10K0Help.reProf b0q) (F10K0Help.reProf b0η)
      (F10K0Help.reProf g) := by
  refine ⟨fun φ hφ => ?_, fun Ψ hΨ => ?_⟩
  · obtain ⟨hI, h0⟩ := h.solenoidal φ hφ
    have hfun : (fun x => F10K0Help.reProf g x 0 * (cpd 1 φ x : ℂ) +
          F10K0Help.reProf g x 1 * (cpd 2 φ x : ℂ)) =
        fun x => F10K0Help.reCLM (g x 0 * (cpd 1 φ x : ℂ) + g x 1 * (cpd 2 φ x : ℂ)) := by
      funext x
      simp only [F10K0Help.reProf_apply, map_add, F10K0Help.reCLM_mul_ofReal]
    rw [hfun]
    refine ⟨F10K0Help.reCLM.integrable_comp hI, ?_⟩
    rw [F10K0Help.reCLM.integral_comp_comm hI, h0, map_zero]
  · obtain ⟨hG, hB, hEq⟩ := h.equation Ψ hΨ
    rw [← reProf_flatBv]
    have hfunG : cdot (F10K0Help.reProf g) Ψ = fun x => F10K0Help.reCLM (cdot g Ψ x) := by
      funext x
      simp only [cdot, Fin.sum_univ_two, map_add, F10K0Help.reProf_apply,
        F10K0Help.reCLM_mul_ofReal]
    have hfunB : cdot (F10K0Help.reProf (flatBv tr b0 b0q b0η)) Ψ =
        fun x => F10K0Help.reCLM (cdot (flatBv tr b0 b0q b0η) Ψ x) := by
      funext x
      simp only [cdot, Fin.sum_univ_two, map_add, F10K0Help.reProf_apply,
        F10K0Help.reCLM_mul_ofReal]
    rw [hfunG, hfunB]
    refine ⟨F10K0Help.reCLM.integrable_comp hG, F10K0Help.reCLM.integrable_comp hB, ?_⟩
    rw [F10K0Help.reCLM.integral_comp_comm hG, F10K0Help.reCLM.integral_comp_comm hB,
      hEq, map_neg]

private lemma sliceH1Norm_reProf_le (c : ℝ) (g gq gη : CProf) (s : ℝ) :
    sliceH1Norm c (F10K0Help.reProf g) (F10K0Help.reProf gq) (F10K0Help.reProf gη) s ≤
      sliceH1Norm c g gq gη s := by
  unfold sliceH1Norm
  gcongr
  · exact eLpNorm_mono (fun z => F10K0Help.norm_reProf_le g (s, z))
  · exact eLpNorm_mono (fun z => F10K0Help.norm_reProf_le gq (s, z))
  · exact eLpNorm_mono (fun z => F10K0Help.norm_reProf_le gη (s, z))

private lemma profCurl_reProf (gq gη : CProf) (x : Coord) :
    profCurl (F10K0Help.reProf gq) (F10K0Help.reProf gη) x =
      F10K0Help.reCLM (profCurl gq gη x) := by
  simp [profCurl, F10K0Help.reProf_apply, map_sub]

private lemma sliceXmNorm_profCurl_reProf_le (c m : ℝ) (gq gη : CProf) (s : ℝ) :
    sliceXmNorm c m (profCurl (F10K0Help.reProf gq) (F10K0Help.reProf gη)) s ≤
      sliceXmNorm c m (profCurl gq gη) s := by
  unfold sliceXmNorm
  refine eLpNorm_mono fun z => ?_
  rw [profCurl_reProf, F10K0Help.reCLM_apply, Complex.norm_real, Real.norm_eq_abs]
  exact Complex.abs_re_le_norm _

private lemma circ_profCurl_reProf {c s : ℝ} {gq gη : CProf}
    (h : IntegrableOn (fun z => profCurl gq gη (s, z)) (B0579.cell c) volume ∧
      ∫ z in B0579.cell c, profCurl gq gη (s, z) = 0) :
    IntegrableOn (fun z => profCurl (F10K0Help.reProf gq) (F10K0Help.reProf gη) (s, z))
        (B0579.cell c) volume ∧
      ∫ z in B0579.cell c,
        profCurl (F10K0Help.reProf gq) (F10K0Help.reProf gη) (s, z) = 0 := by
  have heq : (fun z => profCurl (F10K0Help.reProf gq) (F10K0Help.reProf gη) (s, z)) =
      fun z => F10K0Help.reCLM (profCurl gq gη (s, z)) := by
    funext z; exact profCurl_reProf gq gη (s, z)
  rw [heq]
  refine ⟨F10K0Help.reCLM.integrable_comp h.1, ?_⟩
  rw [F10K0Help.reCLM.integral_comp_comm h.1, h.2, map_zero]

/-! ### 6B. Local integrability, `q`-periodicity of weak derivatives, and Borel upgrade -/

private def perpGradTest (φ : Coord → ℝ) : Coord → Fin 2 → ℝ :=
  fun x => ![cpd 2 φ x, -cpd 1 φ x]

private lemma isPlanarSolTest_perpGradTest {φ : Coord → ℝ} (hφ : IsCoordTest φ) :
    IsPlanarSolTest (perpGradTest φ) where
  smooth i := by
    fin_cases i
    · exact planarTest_isCoordTest_partial hφ (cdir 2)
    · exact planarTest_isCoordTest_neg (planarTest_isCoordTest_partial hφ (cdir 1))
  div_free x := planarTest_div_free hφ.smooth x

private lemma isCoordTest_mul_smooth_left {ψ φ : Coord → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hφ : IsCoordTest φ) :
    IsCoordTest (fun x => ψ x * φ x) :=
  ⟨hψ.mul hφ.smooth, hφ.compact.mul_left, tsupport_mul_subset_right.trans hφ.supp⟩

private lemma locInt_of_isBodySource {ν c : ℝ} {tr : B0140.TrainSol ν c}
    {b0 b0q b0η g : CProf} (hg : IsBodySource tr b0 b0q b0η g) (i : Fin 2) :
    LocallyIntegrableOn (fun x => g x i) DriftWeakSHelp.Upos volume := by
  intro x₀ hx₀
  have hx₀' : 0 < x₀.1 := DriftWeakSHelp.mem_Upos.1 hx₀
  let χ := DriftWeakSHelp.mkBump x₀ hx₀'
  have hχ : IsCoordTest χ := DriftWeakSHelp.mkBump_isTest x₀ hx₀'
  let r : ℝ := χ.rIn / 2
  have hr : 0 < r := half_pos χ.rIn_pos
  have hχ_one : ∀ y ∈ Metric.closedBall x₀ r, (χ : Coord → ℝ) =ᶠ[𝓝 y] fun _ => (1 : ℝ) := by
    intro y hy
    have hy_ball : y ∈ Metric.ball x₀ χ.rIn :=
      Metric.mem_ball.2 (lt_of_le_of_lt (Metric.mem_closedBall.1 hy) (half_lt_self χ.rIn_pos))
    filter_upwards [Metric.isOpen_ball.mem_nhds hy_ball] with z hz
    exact χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hz)
  fin_cases i
  · let φ₀ : Coord → ℝ := fun z => (z.2.2 - x₀.2.2) * χ z
    have hφ₀ : IsCoordTest φ₀ :=
      isCoordTest_mul_smooth_left ((contDiff_snd.comp contDiff_snd).sub contDiff_const) hχ
    have hint := (hg.equation (perpGradTest φ₀) (isPlanarSolTest_perpGradTest hφ₀)).1.integrableOn
      (s := Metric.closedBall x₀ r)
    refine ⟨Metric.closedBall x₀ r,
      mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds x₀ hr), ?_⟩
    refine hint.congr_fun (fun y hy => ?_) measurableSet_closedBall
    have hev : φ₀ =ᶠ[𝓝 y] fun z : Coord => z.2.2 - x₀.2.2 := by
      filter_upwards [hχ_one y hy] with z hz
      simp [φ₀, hz]
    have hfd : fderiv ℝ φ₀ y =
        (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) := by
      rw [hev.fderiv_eq]
      exact ((hasFDerivAt_snd.comp y hasFDerivAt_snd).sub_const x₀.2.2).fderiv
    have hc1 : cpd 1 φ₀ y = 0 := by simp [cpd, hfd, cdir]
    have hc2 : cpd 2 φ₀ y = 1 := by simp [cpd, hfd, cdir]
    simp [cdot, perpGradTest, Fin.sum_univ_two, hc1, hc2]
  · let φ₁ : Coord → ℝ := fun z => -(z.2.1 - x₀.2.1) * χ z
    have hφ₁ : IsCoordTest φ₁ :=
      isCoordTest_mul_smooth_left (((contDiff_fst.comp contDiff_snd).sub contDiff_const).neg) hχ
    have hint := (hg.equation (perpGradTest φ₁) (isPlanarSolTest_perpGradTest hφ₁)).1.integrableOn
      (s := Metric.closedBall x₀ r)
    refine ⟨Metric.closedBall x₀ r,
      mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds x₀ hr), ?_⟩
    refine hint.congr_fun (fun y hy => ?_) measurableSet_closedBall
    have hev : φ₁ =ᶠ[𝓝 y] fun z : Coord => -(z.2.1 - x₀.2.1) := by
      filter_upwards [hχ_one y hy] with z hz
      simp [φ₁, hz]
    have hfd : fderiv ℝ φ₁ y =
        -((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) := by
      rw [hev.fderiv_eq]
      exact (((hasFDerivAt_fst.comp y hasFDerivAt_snd).sub_const x₀.2.1).neg).fderiv
    have hc1 : cpd 1 φ₁ y = -1 := by simp [cpd, hfd, cdir]
    have hc2 : cpd 2 φ₁ y = 0 := by simp [cpd, hfd, cdir]
    simp [cdot, perpGradTest, Fin.sum_univ_two, hc1, hc2]

private lemma hasWeakFO_shift {c : ℝ} (w : Fin 3 → ℝ) {u g : Coord → ℂ}
    (h : HasWeakFO (fun _ => w) dZero u g) :
    HasWeakFO (fun _ => w) dZero (fun x => u (qShift c x)) (fun x => g (qShift c x)) := by
  let e : Coord := (0, (c, 0))
  have hqe : qShift c = fun x => x + e := by
    funext x
    ext <;> simp [qShift, e]
  have hS : ∀ x : Coord, qShift c x + -e = x := by
    intro x; rw [hqe]; simp
  have hmp : MeasurePreserving (qShift c) (volume : Measure Coord) volume := by
    rw [hqe]
    exact measurePreserving_add_right volume e
  have hem : MeasurableEmbedding (qShift c) := by
    rw [hqe]
    exact (Homeomorph.addRight e).measurableEmbedding
  have htest : ∀ φ, IsCoordTest φ → IsCoordTest (fun y => φ (y + -e)) := by
    intro φ hφ
    refine ⟨hφ.smooth.comp (contDiff_id.add contDiff_const),
      hφ.compact.comp_homeomorph (Homeomorph.addRight (-e)), ?_⟩
    have hc : IsClosed ((fun y : Coord => y + -e) ⁻¹' tsupport φ) :=
      (isClosed_tsupport φ).preimage (continuous_id.add continuous_const)
    have hsub : tsupport (fun y => φ (y + -e)) ⊆ (fun y : Coord => y + -e) ⁻¹' tsupport φ :=
      closure_minimal (fun y hy => subset_tsupport φ (by simpa [Function.mem_support] using hy)) hc
    intro y hy
    have := hφ.supp (hsub hy)
    simpa [e] using this
  have hTr_const : ∀ (ψ : Coord → ℝ), Differentiable ℝ ψ → ∀ y : Coord,
      coordTranspose (fun _ => w) dZero ψ y = -(∑ j : Fin 3, w j * cpd j ψ y) := by
    intro ψ hψ y
    simp only [coordTranspose, dZero, zero_mul, add_zero]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [cpd]
    rw [fderiv_const_mul (hψ y)]
    simp
  have hTr : ∀ φ, IsCoordTest φ → ∀ y : Coord,
      coordTranspose (fun _ => w) dZero (fun z => φ (z + -e)) y =
        coordTranspose (fun _ => w) dZero φ (y + -e) := by
    intro φ hφ y
    have hd : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
    have hd' : Differentiable ℝ (fun z => φ (z + -e)) := hd.comp (differentiable_id.add_const _)
    rw [hTr_const _ hd', hTr_const _ hd]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [cpd]
    rw [fderiv_comp_add_right]
  refine ⟨fun φ hφ => ⟨?_, ?_⟩, fun φ hφ => ?_⟩
  · have hI : Integrable (fun y => u y * ((coordTranspose (fun _ => w) dZero φ (y + -e) : ℝ) : ℂ)) :=
      (h.1 _ (htest φ hφ)).1.congr (Eventually.of_forall fun y => by simp [hTr φ hφ y])
    exact ((hmp.integrable_comp_emb hem).2 hI).congr
      (Eventually.of_forall fun x => by simp [Function.comp, hS])
  · have hI := (h.1 _ (htest φ hφ)).2
    exact ((hmp.integrable_comp_emb hem).2 hI).congr
      (Eventually.of_forall fun x => by simp [Function.comp, hS])
  · have e1 : ∫ x, g (qShift c x) * (φ x : ℂ) = ∫ y, g y * (φ (y + -e) : ℂ) := by
      simpa [hS] using hmp.integral_comp hem (fun y => g y * (φ (y + -e) : ℂ))
    have e2 : ∫ x, u (qShift c x) * (coordTranspose (fun _ => w) dZero φ x : ℂ) =
        ∫ y, u y * ((coordTranspose (fun _ => w) dZero φ (y + -e) : ℝ) : ℂ) := by
      simpa [hS] using hmp.integral_comp hem
        (fun y => u y * ((coordTranspose (fun _ => w) dZero φ (y + -e) : ℝ) : ℂ))
    rw [e1, e2, h.2 _ (htest φ hφ)]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp [hTr φ hφ y]

private lemma qPeriodic_of_hasWeakVec {c : ℝ} (w : Fin 3 → ℝ) {u g : CProf}
    (hu : QPeriodic c u) (hw : HasWeakVec (fun _ => w) dZero u g) :
    QPeriodic c g := by
  have hshift : HasWeakVec (fun _ => w) dZero (fun x => u (qShift c x))
      (fun x => g (qShift c x)) := fun i => hasWeakFO_shift w (hw i)
  have hu_ae : ∀ᵐ x : Coord, 0 < x.1 → u (qShift c x) = u x := QPerHalf.ae_imp hu
  have hw' : HasWeakVec (fun _ => w) dZero (fun x => u (qShift c x)) g :=
    hasWeakVec_congr hu_ae (Eventually.of_forall fun _ _ => rfl) hw
  exact QPerHalf.of_ae_imp (GradBoundHelp.hasWeakVec_unique hshift hw')

private lemma isBodySource_congr_g {ν c : ℝ} {tr : B0140.TrainSol ν c}
    {b0 b0q b0η g g' : CProf}
    (hg : ∀ᵐ x : Coord, 0 < x.1 → g' x = g x)
    (h : IsBodySource tr b0 b0q b0η g) :
    IsBodySource tr b0 b0q b0η g' := by
  refine ⟨fun φ hφ => ?_, fun Ψ hΨ => ?_⟩
  · obtain ⟨hI, h0⟩ := h.solenoidal φ hφ
    have hae : (fun x => g' x 0 * (cpd 1 φ x : ℂ) + g' x 1 * (cpd 2 φ x : ℂ)) =ᵐ[volume]
        fun x => g x 0 * (cpd 1 φ x : ℂ) + g x 1 * (cpd 2 φ x : ℂ) := by
      filter_upwards [hg] with x hx
      by_cases hp : 0 < x.1
      · simp [hx hp]
      · have h1 := F10K0Help.isCoordTest_zero_of_nonpos
          (planarTest_isCoordTest_partial hφ (cdir 1)) hp
        have h2 := F10K0Help.isCoordTest_zero_of_nonpos
          (planarTest_isCoordTest_partial hφ (cdir 2)) hp
        change fderiv ℝ φ x (cdir 1) = 0 at h1
        change fderiv ℝ φ x (cdir 2) = 0 at h2
        simp [cpd, h1, h2]
    exact ⟨hI.congr hae.symm, (integral_congr_ae hae).trans h0⟩
  · obtain ⟨hG, hB, hEq⟩ := h.equation Ψ hΨ
    have hae : cdot g' Ψ =ᵐ[volume] cdot g Ψ := by
      filter_upwards [hg] with x hx
      by_cases hp : 0 < x.1
      · simp [cdot, hx hp]
      · have h0 : ∀ i : Fin 2, Ψ x i = 0 :=
          fun i => F10K0Help.isCoordTest_zero_of_nonpos (hΨ.smooth i) hp
        simp [cdot, h0]
    exact ⟨hG.congr hae.symm, hB, (integral_congr_ae hae).trans hEq⟩

private lemma exists_real_sm_rep {c : ℝ} {u : CProf}
    (hper : QPeriodic c u)
    (hloc : ∀ i : Fin 2, LocallyIntegrableOn (fun x => u x i) DriftWeakSHelp.Upos volume) :
    ∃ u' : CProf, StronglyMeasurable u' ∧ IsRealProf u' ∧ QPeriodic c u' ∧
      (∀ᵐ x : Coord, 0 < x.1 → u' x = F10K0Help.reProf u x) := by
  have hmeas_U : MeasurableSet DriftWeakSHelp.Upos := measurableSet_Ioi.prod MeasurableSet.univ
  have haesm_comp : ∀ i : Fin 2,
      AEStronglyMeasurable (DriftWeakSHelp.Upos.indicator (fun x => u x i)) volume :=
    fun i => (aestronglyMeasurable_indicator_iff hmeas_U).2
      (hloc i).aestronglyMeasurable
  set u₀ : CProf := fun x => if 0 < x.1 then u x else 0
  have hu₀_eq : u₀ = wbdVec (fun i => DriftWeakSHelp.Upos.indicator (fun x => u x i)) := by
    funext x
    ext i
    by_cases hp : 0 < x.1 <;> simp [u₀, wbdVec, hp]
  have hu₀_aesm : AEStronglyMeasurable u₀ volume := by
    rw [hu₀_eq]
    exact wbdVec_aesm haesm_comp
  have hu₀_per : QPeriodic c u₀ := by
    refine QPerHalf.of_ae_imp ?_
    filter_upwards [QPerHalf.ae_imp hper] with x hx hp
    simp [u₀, hp, hx hp]
  obtain ⟨u₁, hu₁_sm, hu₁_per, hu₁_ae⟩ := exists_sm_rep_vol hu₀_per hu₀_aesm
  set u' : CProf := fun x => if 0 < x.1 then F10K0Help.reProf u₁ x else 0
  have hu'_sm : StronglyMeasurable u' :=
    ((continuous_liftM.comp continuous_reM).comp_stronglyMeasurable hu₁_sm).ite
      (measurableSet_lt measurable_const measurable_fst) stronglyMeasurable_const
  have hu'_real : IsRealProf u' := isRealProf_ite_pos (isRealProf_reProf u₁)
  have hu'_per : QPeriodic c u' := by
    refine QPerHalf.of_ae_imp ?_
    filter_upwards [QPerHalf.ae_imp (qPeriodic_reProf hu₁_per)] with x hx hp
    simp [u', hp, hx hp]
  have hu'_ae : ∀ᵐ x : Coord, 0 < x.1 → u' x = F10K0Help.reProf u x := by
    filter_upwards [hu₁_ae] with x hx hp
    have hu₀x : u₀ x = u x := by simp [u₀, hp]
    ext i
    simp [u', hp, F10K0Help.reProf_apply, hx, hu₀x]
  exact ⟨u', hu'_sm, hu'_real, hu'_per, hu'_ae⟩

private lemma ae_slice_cell_of_ae_pos {c : ℝ} {u v : CProf}
    (h : ∀ᵐ x : Coord, 0 < x.1 → u x = v x) :
    ∀ᵐ s ∂volume, 0 < s →
      (fun z => u (s, z)) =ᵐ[volume.restrict (B0579.cell c)] (fun z => v (s, z)) := by
  have hprod : ∀ᵐ s ∂(volume : Measure ℝ), ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)),
      0 < (s, z).1 → u (s, z) = v (s, z) :=
    Measure.ae_ae_of_ae_prod h
  filter_upwards [hprod] with s hs hpos
  exact ae_restrict_of_ae (hs.mono fun z hz => hz hpos)

private lemma sLpNorm_congr_ae_Ioc {b T : ℝ} {f g : ℝ → ℝ≥0∞}
    (h : ∀ᵐ s ∂volume, s ∈ Ioc 0 T → f s = g s) :
    sLpNorm b T f = sLpNorm b T g := by
  have hac : sMeas b ≪ volume :=
    (withDensity_absolutelyContinuous _ _).trans
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  have hs : ∀ᵐ s ∂(sMeas b).restrict (Ioc 0 T), f s ^ bgp = g s ^ bgp := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hac.ae_le h] with s hs hm
    rw [hs hm]
  unfold sLpNorm
  rw [lintegral_congr_ae hs]

/-! ### 6C. Upgrading a `BodySourceBound` witness to Borel real-valued representatives -/

private lemma upgrade_bodySource_witness
    {m Sig : ℝ} {p : Params} (hSig : 0 < Sig) (hAge : p.ageCut = Sig)
    {C_rhs : ℝ} {b0 b0q b0η g gq gη : CProf}
    (hg_per : QPeriodic p.c g)
    (hgq : HasWeakVec vQ0 dZero g gq)
    (hgη : HasWeakVec vEta dZero g gη)
    (hg_src : IsBodySource p.train b0 b0q b0η g)
    (h_sLp : sLpNorm (13 / 8) p.H (sliceH1Norm p.c g gq gη) +
        sLpNorm (13 / 8) p.H (sliceXmNorm p.c m (profCurl gq gη)) ≤
      ENNReal.ofReal C_rhs)
    (h_circ : ∀ᵐ s ∂volume, s ∈ Ioc 0 p.H →
      IntegrableOn (fun z => profCurl gq gη (s, z)) (B0579.cell p.c) volume ∧
        ∫ z in B0579.cell p.c, profCurl gq gη (s, z) = 0) :
    ∃ g' gq' gη' : CProf,
      StronglyMeasurable g' ∧ StronglyMeasurable gq' ∧ StronglyMeasurable gη' ∧
      IsRealProf g' ∧ IsRealProf gq' ∧ IsRealProf gη' ∧
      QPeriodic p.c g' ∧ QPeriodic p.c gq' ∧ QPeriodic p.c gη' ∧
      HasWeakVec vQ0 dZero g' gq' ∧
      HasWeakVec vEta dZero g' gη' ∧
      IsBodySource p.train (F10K0Help.reProf b0) (F10K0Help.reProf b0q) (F10K0Help.reProf b0η) g' ∧
      sLpNorm (13 / 8) p.H (sliceH1Norm p.c g' gq' gη') +
          sLpNorm (13 / 8) p.H (sliceXmNorm p.c m (profCurl gq' gη')) ≤
        ENNReal.ofReal C_rhs ∧
      (∀ᵐ s ∂volume, s ∈ Ioc 0 p.H →
        IntegrableOn (fun z => profCurl gq' gη' (s, z)) (B0579.cell p.c) volume ∧
          ∫ z in B0579.cell p.c, profCurl gq' gη' (s, z) = 0) := by
  have _ := hSig; have _ := hAge
  have hgq_per : QPeriodic p.c gq := qPeriodic_of_hasWeakVec ![0, 1, 0] hg_per hgq
  have hgη_per : QPeriodic p.c gη := qPeriodic_of_hasWeakVec ![0, 0, 1] hg_per hgη
  have hg_loc : ∀ i : Fin 2, LocallyIntegrableOn (fun x => g x i) DriftWeakSHelp.Upos volume :=
    locInt_of_isBodySource hg_src
  have hgq_loc : ∀ i : Fin 2, LocallyIntegrableOn (fun x => gq x i) DriftWeakSHelp.Upos volume :=
    fun i => DriftWeakSHelp.locInt_of_tests _ (fun φ hφ => ((hgq i).1 φ hφ).2)
  have hgη_loc : ∀ i : Fin 2, LocallyIntegrableOn (fun x => gη x i) DriftWeakSHelp.Upos volume :=
    fun i => DriftWeakSHelp.locInt_of_tests _ (fun φ hφ => ((hgη i).1 φ hφ).2)
  obtain ⟨g', hg'_sm, hg'_re, hg'_per, hg'_ae⟩ := exists_real_sm_rep hg_per hg_loc
  obtain ⟨gq', hgq'_sm, hgq'_re, hgq'_per, hgq'_ae⟩ := exists_real_sm_rep hgq_per hgq_loc
  obtain ⟨gη', hgη'_sm, hgη'_re, hgη'_per, hgη'_ae⟩ := exists_real_sm_rep hgη_per hgη_loc
  have hgq' : HasWeakVec vQ0 dZero g' gq' :=
    hasWeakVec_congr hg'_ae hgq'_ae (F10K0Help.hasWeakVec_reProf hgq)
  have hgη' : HasWeakVec vEta dZero g' gη' :=
    hasWeakVec_congr hg'_ae hgη'_ae (F10K0Help.hasWeakVec_reProf hgη)
  have hg'_src : IsBodySource p.train (F10K0Help.reProf b0) (F10K0Help.reProf b0q)
      (F10K0Help.reProf b0η) g' :=
    isBodySource_congr_g hg'_ae (isBodySource_reProf hg_src)
  have hsl_g := ae_slice_cell_of_ae_pos (c := p.c) hg'_ae
  have hsl_gq := ae_slice_cell_of_ae_pos (c := p.c) hgq'_ae
  have hsl_gη := ae_slice_cell_of_ae_pos (c := p.c) hgη'_ae
  have hH1_eq : sLpNorm (13 / 8) p.H (sliceH1Norm p.c g' gq' gη') =
      sLpNorm (13 / 8) p.H
        (sliceH1Norm p.c (F10K0Help.reProf g) (F10K0Help.reProf gq) (F10K0Help.reProf gη)) := by
    refine sLpNorm_congr_ae_Ioc ?_
    filter_upwards [hsl_g, hsl_gq, hsl_gη] with s h1 h2 h3 hs
    exact sliceH1Norm_congr_ae_cell (h1 hs.1) (h2 hs.1) (h3 hs.1)
  have hXm_eq : sLpNorm (13 / 8) p.H (sliceXmNorm p.c m (profCurl gq' gη')) =
      sLpNorm (13 / 8) p.H
        (sliceXmNorm p.c m (profCurl (F10K0Help.reProf gq) (F10K0Help.reProf gη))) := by
    refine sLpNorm_congr_ae_Ioc ?_
    filter_upwards [hsl_gq, hsl_gη] with s h2 h3 hs
    exact sliceXmNorm_profCurl_congr_ae_cell (h2 hs.1) (h3 hs.1)
  have h_sLp' : sLpNorm (13 / 8) p.H (sliceH1Norm p.c g' gq' gη') +
      sLpNorm (13 / 8) p.H (sliceXmNorm p.c m (profCurl gq' gη')) ≤
        ENNReal.ofReal C_rhs := by
    rw [hH1_eq, hXm_eq]
    refine (add_le_add
      (sLpNorm_mono_Ioc _ _ fun s _ => sliceH1Norm_reProf_le p.c g gq gη s)
      (sLpNorm_mono_Ioc _ _ fun s _ => sliceXmNorm_profCurl_reProf_le p.c m gq gη s)).trans h_sLp
  have h_circ' : ∀ᵐ s ∂volume, s ∈ Ioc 0 p.H →
      IntegrableOn (fun z => profCurl gq' gη' (s, z)) (B0579.cell p.c) volume ∧
        ∫ z in B0579.cell p.c, profCurl gq' gη' (s, z) = 0 := by
    filter_upwards [h_circ, hsl_gq, hsl_gη] with s hc_s h2 h3 hs
    obtain ⟨hI_re, h0_re⟩ := circ_profCurl_reProf (hc_s hs)
    have hae_curl : (fun z => profCurl gq' gη' (s, z)) =ᵐ[volume.restrict (B0579.cell p.c)]
        fun z => profCurl (F10K0Help.reProf gq) (F10K0Help.reProf gη) (s, z) := by
      filter_upwards [h2 hs.1, h3 hs.1] with z hz2 hz3
      simp [profCurl, hz2, hz3]
    exact ⟨hI_re.congr hae_curl.symm, (integral_congr_ae hae_curl).trans h0_re⟩
  exact ⟨g', gq', gη', hg'_sm, hgq'_sm, hgη'_sm, hg'_re, hgq'_re, hgη'_re,
    hg'_per, hgq'_per, hgη'_per, hgq', hgη', hg'_src, h_sLp', h_circ'⟩

/-! ### 6D. Uniqueness of `IsBodySource` on cylinder slices -/

private lemma ae_zero_on_Upos_of_tests {f : Coord → ℂ}
    (hloc : LocallyIntegrableOn f DriftWeakSHelp.Upos volume)
    (htest : ∀ φ : Coord → ℝ, IsCoordTest φ → ∫ x, f x * (φ x : ℂ) = 0) :
    ∀ᵐ x : Coord, 0 < x.1 → f x = 0 := by
  have : (volume : Measure Coord).IsAddHaarMeasure := DriftWeakSHelp.instIsAddHaarVolCoord
  have hae := (isOpen_Ioi.prod isOpen_univ).ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc (by
    intro χ hχs hχc hχU
    have hχ := htest χ ⟨hχs, hχc, hχU⟩
    simp only [Complex.real_smul]
    convert hχ using 2
    funext x; ring)
  filter_upwards [hae] with x hx hp
  exact hx (DriftWeakSHelp.mem_Upos.2 hp)

private lemma ae_cell_eq_of_isBodySource
    {ν c H : ℝ} {tr : B0140.TrainSol ν c} (hc : 0 < c)
    {b0 b0q b0η g₁ gq₁ gη₁ g₂ gq₂ gη₂ : CProf}
    (hg₁_sm : StronglyMeasurable g₁) (hgq₁_sm : StronglyMeasurable gq₁)
    (hgη₁_sm : StronglyMeasurable gη₁)
    (hg₂_sm : StronglyMeasurable g₂) (hgq₂_sm : StronglyMeasurable gq₂)
    (hgη₂_sm : StronglyMeasurable gη₂)
    (hg₁_per : QPeriodic c g₁) (hgq₁_per : QPeriodic c gq₁) (hgη₁_per : QPeriodic c gη₁)
    (hg₂_per : QPeriodic c g₂) (hgq₂_per : QPeriodic c gq₂) (hgη₂_per : QPeriodic c gη₂)
    (hgq₁ : HasWeakVec vQ0 dZero g₁ gq₁) (hgη₁ : HasWeakVec vEta dZero g₁ gη₁)
    (hgq₂ : HasWeakVec vQ0 dZero g₂ gq₂) (hgη₂ : HasWeakVec vEta dZero g₂ gη₂)
    (hsrc₁ : IsBodySource tr b0 b0q b0η g₁) (hsrc₂ : IsBodySource tr b0 b0q b0η g₂)
    (hfin₁ : ∀ᵐ s ∂volume, s ∈ Ioc 0 H → sliceH1Norm c g₁ gq₁ gη₁ s < ⊤)
    (hfin₂ : ∀ᵐ s ∂volume, s ∈ Ioc 0 H → sliceH1Norm c g₂ gq₂ gη₂ s < ⊤) :
    ∀ᵐ s ∂volume, s ∈ Ioc 0 H →
      (fun z => g₁ (s, z)) =ᵐ[volume.restrict (B0579.cell c)] (fun z => g₂ (s, z)) ∧
      (fun z => gq₁ (s, z)) =ᵐ[volume.restrict (B0579.cell c)] (fun z => gq₂ (s, z)) ∧
      (fun z => gη₁ (s, z)) =ᵐ[volume.restrict (B0579.cell c)] (fun z => gη₂ (s, z)) := by
  let w : CProf := g₁ - g₂
  let wq : CProf := gq₁ - gq₂
  let wη : CProf := gη₁ - gη₂
  have hw_sm : StronglyMeasurable w := hg₁_sm.sub hg₂_sm
  have hwq_sm : StronglyMeasurable wq := hgq₁_sm.sub hgq₂_sm
  have hwη_sm : StronglyMeasurable wη := hgη₁_sm.sub hgη₂_sm
  have hsub_eq : ∀ u₁ u₂ : CProf, u₁ - u₂ = u₁ + (-1 : ℝ) • u₂ := by
    intro u₁ u₂; funext x; ext i; simp [sub_eq_add_neg]
  have hw_per : QPeriodic c w := by
    change QPeriodic c (g₁ - g₂)
    rw [hsub_eq]; exact qPeriodic_add hg₁_per (qPeriodic_smul_real (-1) hg₂_per)
  have hwq_per : QPeriodic c wq := by
    change QPeriodic c (gq₁ - gq₂)
    rw [hsub_eq]; exact qPeriodic_add hgq₁_per (qPeriodic_smul_real (-1) hgq₂_per)
  have hwη_per : QPeriodic c wη := by
    change QPeriodic c (gη₁ - gη₂)
    rw [hsub_eq]; exact qPeriodic_add hgη₁_per (qPeriodic_smul_real (-1) hgη₂_per)
  have hwq : HasWeakVec vQ0 dZero w wq := by
    change HasWeakVec vQ0 dZero (g₁ - g₂) (gq₁ - gq₂)
    rw [hsub_eq g₁ g₂, hsub_eq gq₁ gq₂]
    exact F10Help.hasWeakVec_add' hgq₁ (hasWeakVec_smul_real (-1) hgq₂)
  have hwη : HasWeakVec vEta dZero w wη := by
    change HasWeakVec vEta dZero (g₁ - g₂) (gη₁ - gη₂)
    rw [hsub_eq g₁ g₂, hsub_eq gη₁ gη₂]
    exact F10Help.hasWeakVec_add' hgη₁ (hasWeakVec_smul_real (-1) hgη₂)
  -- Space-time weak divergence wq_0 + wη_1 = 0 a.e. on s > 0
  have hdiv_ae : ∀ᵐ x : Coord, 0 < x.1 → wq x 0 + wη x 1 = 0 := by
    have hloc : LocallyIntegrableOn (fun x => wq x 0 + wη x 1) DriftWeakSHelp.Upos volume :=
      (DriftWeakSHelp.locInt_of_tests _ (fun φ hφ => ((hwq 0).1 φ hφ).2)).add
        (DriftWeakSHelp.locInt_of_tests _ (fun φ hφ => ((hwη 1).1 φ hφ).2))
    refine ae_zero_on_Upos_of_tests hloc fun φ hφ => ?_
    have hIq := ((hwq 0).1 φ hφ).2
    have hIη := ((hwη 1).1 φ hφ).2
    have hadd : ∫ x, (wq x 0 + wη x 1) * (φ x : ℂ) =
        (∫ x, wq x 0 * (φ x : ℂ)) + ∫ x, wη x 1 * (φ x : ℂ) := by
      rw [← integral_add hIq hIη]; congr 1; funext x; ring
    rw [hadd, (hwq 0).2 φ hφ, (hwη 1).2 φ hφ]
    have hctQ : (fun x => w x 0 * (coordTranspose vQ0 dZero φ x : ℂ)) =
        fun x => -(w x 0 * (cpd 1 φ x : ℂ)) := by
      funext x; rw [wb_ct_Q]; push_cast; ring
    have hctE : (fun x => w x 1 * (coordTranspose vEta dZero φ x : ℂ)) =
        fun x => -(w x 1 * (cpd 2 φ x : ℂ)) := by
      funext x; rw [wb_ct_E]; push_cast; ring
    rw [hctQ, hctE, integral_neg, integral_neg]
    obtain ⟨hIs1, h01⟩ := hsrc₁.solenoidal φ hφ
    obtain ⟨hIs2, h02⟩ := hsrc₂.solenoidal φ hφ
    have hsol_w : ∫ x, (w x 0 * (cpd 1 φ x : ℂ) + w x 1 * (cpd 2 φ x : ℂ)) = 0 := by
      have heq : (fun x => w x 0 * (cpd 1 φ x : ℂ) + w x 1 * (cpd 2 φ x : ℂ)) =
          fun x => (g₁ x 0 * (cpd 1 φ x : ℂ) + g₁ x 1 * (cpd 2 φ x : ℂ)) -
            (g₂ x 0 * (cpd 1 φ x : ℂ) + g₂ x 1 * (cpd 2 φ x : ℂ)) := by
        funext x; simp only [w, Pi.sub_apply, PiLp.sub_apply]; ring
      rw [heq, integral_sub hIs1 hIs2, h01, h02, sub_self]
    have hIq' : Integrable (fun x => w x 0 * (cpd 1 φ x : ℂ)) := by
      have := ((hwq 0).1 φ hφ).1; rw [hctQ] at this
      exact this.neg.congr (Eventually.of_forall fun x => neg_neg _)
    have hIη' : Integrable (fun x => w x 1 * (cpd 2 φ x : ℂ)) := by
      have := ((hwη 1).1 φ hφ).1; rw [hctE] at this
      exact this.neg.congr (Eventually.of_forall fun x => neg_neg _)
    rw [← neg_add, ← integral_add hIq' hIη', hsol_w, neg_zero]
  -- Space-time weak curl wq_1 - wη_0 = 0 a.e. on s > 0
  have hcurl_ae : ∀ᵐ x : Coord, 0 < x.1 → wq x 1 - wη x 0 = 0 := by
    have hloc : LocallyIntegrableOn (fun x => wq x 1 - wη x 0) DriftWeakSHelp.Upos volume :=
      (DriftWeakSHelp.locInt_of_tests _ (fun φ hφ => ((hwq 1).1 φ hφ).2)).sub
        (DriftWeakSHelp.locInt_of_tests _ (fun φ hφ => ((hwη 0).1 φ hφ).2))
    refine ae_zero_on_Upos_of_tests hloc fun φ hφ => ?_
    have hIq := ((hwq 1).1 φ hφ).2
    have hIη := ((hwη 0).1 φ hφ).2
    have hsub : ∫ x, (wq x 1 - wη x 0) * (φ x : ℂ) =
        (∫ x, wq x 1 * (φ x : ℂ)) - ∫ x, wη x 0 * (φ x : ℂ) := by
      rw [← integral_sub hIq hIη]; congr 1; funext x; ring
    rw [hsub, (hwq 1).2 φ hφ, (hwη 0).2 φ hφ]
    have hctQ : (fun x => w x 1 * (coordTranspose vQ0 dZero φ x : ℂ)) =
        fun x => -(w x 1 * (cpd 1 φ x : ℂ)) := by
      funext x; rw [wb_ct_Q]; push_cast; ring
    have hctE : (fun x => w x 0 * (coordTranspose vEta dZero φ x : ℂ)) =
        fun x => -(w x 0 * (cpd 2 φ x : ℂ)) := by
      funext x; rw [wb_ct_E]; push_cast; ring
    rw [hctQ, hctE, integral_neg, integral_neg]
    let Ψ := perpGradTest φ
    have hΨ := isPlanarSolTest_perpGradTest hφ
    obtain ⟨hIg1, _, heq1⟩ := hsrc₁.equation Ψ hΨ
    obtain ⟨hIg2, _, heq2⟩ := hsrc₂.equation Ψ hΨ
    have heq_w : ∫ x, cdot w Ψ x = 0 := by
      have hfun : cdot w Ψ = fun x => cdot g₁ Ψ x - cdot g₂ Ψ x := by
        funext x; simp only [cdot, w, Pi.sub_apply, PiLp.sub_apply, Fin.sum_univ_two]; ring
      rw [hfun, integral_sub hIg1 hIg2, heq1, heq2, sub_self]
    have hIq' : Integrable (fun x => w x 1 * (cpd 1 φ x : ℂ)) := by
      have := ((hwq 1).1 φ hφ).1; rw [hctQ] at this
      exact this.neg.congr (Eventually.of_forall fun x => neg_neg _)
    have hIη' : Integrable (fun x => w x 0 * (cpd 2 φ x : ℂ)) := by
      have := ((hwη 0).1 φ hφ).1; rw [hctE] at this
      exact this.neg.congr (Eventually.of_forall fun x => neg_neg _)
    have hcomb : -(∫ x, w x 1 * (cpd 1 φ x : ℂ)) - -(∫ x, w x 0 * (cpd 2 φ x : ℂ)) =
        ∫ x, (w x 0 * (cpd 2 φ x : ℂ) - w x 1 * (cpd 1 φ x : ℂ)) := by
      calc -(∫ x, w x 1 * (cpd 1 φ x : ℂ)) - -(∫ x, w x 0 * (cpd 2 φ x : ℂ))
          = (∫ x, w x 0 * (cpd 2 φ x : ℂ)) - ∫ x, w x 1 * (cpd 1 φ x : ℂ) := by ring
        _ = ∫ x, (w x 0 * (cpd 2 φ x : ℂ) - w x 1 * (cpd 1 φ x : ℂ)) :=
            (integral_sub hIη' hIq').symm
    rw [hcomb]
    convert heq_w using 2
    funext x
    simp only [cdot, Ψ, perpGradTest, Fin.sum_univ_two]
    push_cast
    ring
  -- Disintegrate to cylinder slices via jointWeakToSlice_proof
  have hjw0 := FlatBvSliceGoodAeNeeded.jointWeakToSlice_proof c hc 0 w wq
    hw_sm hwq_sm hw_per hwq_per (by simpa using hwq)
  have hjw1 := FlatBvSliceGoodAeNeeded.jointWeakToSlice_proof c hc 1 w wη
    hw_sm hwη_sm hw_per hwη_per (by simpa using hwη)
  have hdiv_sl : ∀ᵐ s ∂(volume : Measure ℝ), ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)),
      0 < (s, z).1 → wq (s, z) 0 + wη (s, z) 1 = 0 :=
    Measure.ae_ae_of_ae_prod hdiv_ae
  have hcurl_sl : ∀ᵐ s ∂(volume : Measure ℝ), ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)),
      0 < (s, z).1 → wq (s, z) 1 - wη (s, z) 0 = 0 :=
    Measure.ae_ae_of_ae_prod hcurl_ae
  have hmem_of_h1 : ∀ (u uq uη : CProf) (s : ℝ),
      StronglyMeasurable u → StronglyMeasurable uq → StronglyMeasurable uη →
      sliceH1Norm c u uq uη s < ⊤ →
      MemLp (fun z => u (s, z)) 2 (volume.restrict (B0579.cell c)) ∧
      MemLp (fun z => uq (s, z)) 2 (volume.restrict (B0579.cell c)) ∧
      MemLp (fun z => uη (s, z)) 2 (volume.restrict (B0579.cell c)) := by
    intro u uq uη s hu huq huη hfin
    unfold sliceH1Norm at hfin
    refine ⟨⟨(hu.comp_measurable measurable_prodMk_left).aestronglyMeasurable,
        lt_of_le_of_lt (le_self_add.trans le_self_add) hfin⟩,
      ⟨(huq.comp_measurable measurable_prodMk_left).aestronglyMeasurable,
        lt_of_le_of_lt (le_add_self.trans le_self_add) hfin⟩,
      ⟨(huη.comp_measurable measurable_prodMk_left).aestronglyMeasurable,
        lt_of_le_of_lt le_add_self hfin⟩⟩
  filter_upwards [hfin₁, hfin₂, hjw0, hjw1, hdiv_sl, hcurl_sl] with s hf1 hf2 hw0 hw1 hds hcs hs
  obtain ⟨hmg1, hmgq1, hmgη1⟩ := hmem_of_h1 g₁ gq₁ gη₁ s hg₁_sm hgq₁_sm hgη₁_sm (hf1 hs)
  obtain ⟨hmg2, hmgq2, hmgη2⟩ := hmem_of_h1 g₂ gq₂ gη₂ s hg₂_sm hgq₂_sm hgη₂_sm (hf2 hs)
  have hmw : MemLp (fun z => w (s, z)) 2 (volume.restrict (B0579.cell c)) := hmg1.sub hmg2
  have hmwq : MemLp (fun z => wq (s, z)) 2 (volume.restrict (B0579.cell c)) := hmgq1.sub hmgq2
  have hmwη : MemLp (fun z => wη (s, z)) 2 (volume.restrict (B0579.cell c)) := hmgη1.sub hmgη2
  have hcd0 := hw0 hs.1 hmw hmwq
  have hcd1 := hw1 hs.1 hmw hmwη
  have hmw_comp : ∀ j : Fin 2, MemLp (fun z => w (s, z) j) 2 (UnforcedLeray.Cyl.cellμ c) := by
    intro j
    rw [Short.IIIa.CTE.T20_2.cellμ_eq_B0579]
    exact (EuclideanSpace.proj j : CMerid →L[ℂ] ℂ).comp_memLp' hmw
  have hdiv_test : ∀ ψ : ℝ × ℝ → ℝ, UnforcedLeray.Sob.IsCylTest c ψ →
      ∫ z in UnforcedLeray.Cyl.cell c,
        (w (s, z) 0 * (fderiv ℝ ψ z (1, 0) : ℂ) +
          w (s, z) 1 * (fderiv ℝ ψ z (0, 1) : ℂ)) = 0 := by
    intro ψ hψ
    have hψB := Short.IIIa.CTE.T20_2.B0579_of_sob hψ
    rw [← Short.IIIa.CTE.T20_2.cell_eq]
    simp only [← Short.IIIa.CTE.T20_2.pd0_eq, ← Short.IIIa.CTE.T20_2.pd1_eq]
    rw [integral_add ((hcd0 0).1 ψ hψB).1 ((hcd1 1).1 ψ hψB).1,
      (hcd0 0).2 ψ hψB, (hcd1 1).2 ψ hψB, ← neg_add,
      ← integral_add ((hcd0 0).1 ψ hψB).2 ((hcd1 1).1 ψ hψB).2]
    have h0 : ∫ z in B0579.cell c, (wq (s, z) 0 * (ψ z : ℂ) + wη (s, z) 1 * (ψ z : ℂ)) = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [ae_restrict_of_ae hds] with z hz
      calc wq (s, z) 0 * (ψ z : ℂ) + wη (s, z) 1 * (ψ z : ℂ)
          = (wq (s, z) 0 + wη (s, z) 1) * (ψ z : ℂ) := by ring
        _ = 0 := by rw [hz hs.1, zero_mul]
    rw [h0, neg_zero]
  have hcurl_test : ∀ ψ : ℝ × ℝ → ℝ, UnforcedLeray.Sob.IsCylTest c ψ →
      ∫ z in UnforcedLeray.Cyl.cell c,
        (w (s, z) 0 * (fderiv ℝ ψ z (0, 1) : ℂ) -
          w (s, z) 1 * (fderiv ℝ ψ z (1, 0) : ℂ)) = 0 := by
    intro ψ hψ
    have hψB := Short.IIIa.CTE.T20_2.B0579_of_sob hψ
    rw [← Short.IIIa.CTE.T20_2.cell_eq]
    simp only [← Short.IIIa.CTE.T20_2.pd0_eq, ← Short.IIIa.CTE.T20_2.pd1_eq]
    rw [integral_sub ((hcd1 0).1 ψ hψB).1 ((hcd0 1).1 ψ hψB).1,
      (hcd1 0).2 ψ hψB, (hcd0 1).2 ψ hψB]
    have hcomb : -(∫ z in B0579.cell c, wη (s, z) 0 * (ψ z : ℂ)) -
        -(∫ z in B0579.cell c, wq (s, z) 1 * (ψ z : ℂ)) =
        ∫ z in B0579.cell c, (wq (s, z) 1 * (ψ z : ℂ) - wη (s, z) 0 * (ψ z : ℂ)) := by
      calc -(∫ z in B0579.cell c, wη (s, z) 0 * (ψ z : ℂ)) -
            -(∫ z in B0579.cell c, wq (s, z) 1 * (ψ z : ℂ))
          = (∫ z in B0579.cell c, wq (s, z) 1 * (ψ z : ℂ)) -
            ∫ z in B0579.cell c, wη (s, z) 0 * (ψ z : ℂ) := by ring
        _ = ∫ z in B0579.cell c, (wq (s, z) 1 * (ψ z : ℂ) - wη (s, z) 0 * (ψ z : ℂ)) :=
            (integral_sub ((hcd0 1).1 ψ hψB).2 ((hcd1 0).1 ψ hψB).2).symm
    rw [hcomb]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [ae_restrict_of_ae hcs] with z hz
    calc wq (s, z) 1 * (ψ z : ℂ) - wη (s, z) 0 * (ψ z : ℂ)
        = (wq (s, z) 1 - wη (s, z) 0) * (ψ z : ℂ) := by ring
      _ = 0 := by rw [hz hs.1, zero_mul]
  have hw_zero := Short.IIIa.CTE.T20_2.biot_re hc (fun z j => w (s, z) j) hmw_comp
    hdiv_test hcurl_test
  rw [Short.IIIa.CTE.T20_2.cellμ_eq_B0579] at hw_zero
  have hw_comp_zero : ∀ j : Fin 2,
      (fun z => w (s, z) j) =ᵐ[volume.restrict (B0579.cell c)] 0 := by
    intro j
    filter_upwards [hw_zero] with z hz
    exact congrFun hz j
  have hwq_comp_zero : ∀ j : Fin 2,
      (fun z => wq (s, z) j) =ᵐ[volume.restrict (B0579.cell c)] 0 :=
    fun j => hasWeakCellDerivC_ae_zero_of_ae_zero hc (hw_comp_zero j)
      ((EuclideanSpace.proj j : CMerid →L[ℂ] ℂ).comp_memLp' hmwq) (hcd0 j)
  have hwη_comp_zero : ∀ j : Fin 2,
      (fun z => wη (s, z) j) =ᵐ[volume.restrict (B0579.cell c)] 0 :=
    fun j => hasWeakCellDerivC_ae_zero_of_ae_zero hc (hw_comp_zero j)
      ((EuclideanSpace.proj j : CMerid →L[ℂ] ℂ).comp_memLp' hmwη) (hcd1 j)
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hw_comp_zero 0, hw_comp_zero 1] with z h0 h1
    ext j; fin_cases j
    · exact sub_eq_zero.mp h0
    · exact sub_eq_zero.mp h1
  · filter_upwards [hwq_comp_zero 0, hwq_comp_zero 1] with z h0 h1
    ext j; fin_cases j
    · exact sub_eq_zero.mp h0
    · exact sub_eq_zero.mp h1
  · filter_upwards [hwη_comp_zero 0, hwη_comp_zero 1] with z h0 h1
    ext j; fin_cases j
    · exact sub_eq_zero.mp h0
    · exact sub_eq_zero.mp h1

/-! ### 6E. `Xmc` slice path construction and linear closure -/

private lemma hasZeroCirculationR_congr_ae {c : ℝ} {f g : B0579.Plane → ℝ}
    (hfg : f =ᵐ[volume.restrict (B0579.cell c)] g) (hf : HasZeroCirculationR c f) :
    HasZeroCirculationR c g :=
  ⟨hf.1.congr hfg, (integral_congr_ae hfg.symm).trans hf.2⟩

private lemma sliceH1Norm_add_le (c : ℝ) {g₁ gq₁ gη₁ g₂ gq₂ gη₂ : CProf}
    (hg₁ : StronglyMeasurable g₁) (hgq₁ : StronglyMeasurable gq₁) (hgη₁ : StronglyMeasurable gη₁)
    (hg₂ : StronglyMeasurable g₂) (hgq₂ : StronglyMeasurable gq₂) (hgη₂ : StronglyMeasurable gη₂)
    (s : ℝ) :
    sliceH1Norm c (g₁ + g₂) (gq₁ + gq₂) (gη₁ + gη₂) s ≤
      sliceH1Norm c g₁ gq₁ gη₁ s + sliceH1Norm c g₂ gq₂ gη₂ s := by
  have hsm : Measurable (fun z : B0579.Plane => (s, z)) :=
    measurable_const.prodMk measurable_id
  have h0 : eLpNorm (fun z => (g₁ + g₂) (s, z)) 2 (volume.restrict (B0579.cell c)) ≤
      eLpNorm (fun z => g₁ (s, z)) 2 (volume.restrict (B0579.cell c)) +
      eLpNorm (fun z => g₂ (s, z)) 2 (volume.restrict (B0579.cell c)) :=
    eLpNorm_add_le (hg₁.comp_measurable hsm).aestronglyMeasurable
      (hg₂.comp_measurable hsm).aestronglyMeasurable (by norm_num)
  have h1 : eLpNorm (fun z => (gq₁ + gq₂) (s, z)) 2 (volume.restrict (B0579.cell c)) ≤
      eLpNorm (fun z => gq₁ (s, z)) 2 (volume.restrict (B0579.cell c)) +
      eLpNorm (fun z => gq₂ (s, z)) 2 (volume.restrict (B0579.cell c)) :=
    eLpNorm_add_le (hgq₁.comp_measurable hsm).aestronglyMeasurable
      (hgq₂.comp_measurable hsm).aestronglyMeasurable (by norm_num)
  have h2 : eLpNorm (fun z => (gη₁ + gη₂) (s, z)) 2 (volume.restrict (B0579.cell c)) ≤
      eLpNorm (fun z => gη₁ (s, z)) 2 (volume.restrict (B0579.cell c)) +
      eLpNorm (fun z => gη₂ (s, z)) 2 (volume.restrict (B0579.cell c)) :=
    eLpNorm_add_le (hgη₁.comp_measurable hsm).aestronglyMeasurable
      (hgη₂.comp_measurable hsm).aestronglyMeasurable (by norm_num)
  unfold sliceH1Norm
  calc eLpNorm (fun z => (g₁ + g₂) (s, z)) 2 (volume.restrict (B0579.cell c)) +
        eLpNorm (fun z => (gq₁ + gq₂) (s, z)) 2 (volume.restrict (B0579.cell c)) +
        eLpNorm (fun z => (gη₁ + gη₂) (s, z)) 2 (volume.restrict (B0579.cell c))
      ≤ (eLpNorm (fun z => g₁ (s, z)) 2 (volume.restrict (B0579.cell c)) +
          eLpNorm (fun z => g₂ (s, z)) 2 (volume.restrict (B0579.cell c))) +
        (eLpNorm (fun z => gq₁ (s, z)) 2 (volume.restrict (B0579.cell c)) +
          eLpNorm (fun z => gq₂ (s, z)) 2 (volume.restrict (B0579.cell c))) +
        (eLpNorm (fun z => gη₁ (s, z)) 2 (volume.restrict (B0579.cell c)) +
          eLpNorm (fun z => gη₂ (s, z)) 2 (volume.restrict (B0579.cell c))) :=
        add_le_add (add_le_add h0 h1) h2
    _ = (eLpNorm (fun z => g₁ (s, z)) 2 (volume.restrict (B0579.cell c)) +
          eLpNorm (fun z => gq₁ (s, z)) 2 (volume.restrict (B0579.cell c)) +
          eLpNorm (fun z => gη₁ (s, z)) 2 (volume.restrict (B0579.cell c))) +
        (eLpNorm (fun z => g₂ (s, z)) 2 (volume.restrict (B0579.cell c)) +
          eLpNorm (fun z => gq₂ (s, z)) 2 (volume.restrict (B0579.cell c)) +
          eLpNorm (fun z => gη₂ (s, z)) 2 (volume.restrict (B0579.cell c))) := by
        ac_rfl

private lemma sliceH1Norm_smul_le (c : ℝ) (a : ℝ) (g gq gη : CProf) (s : ℝ) :
    sliceH1Norm c (a • g) (a • gq) (a • gη) s ≤
      ‖a‖ₑ * sliceH1Norm c g gq gη s := by
  unfold sliceH1Norm
  rw [mul_add, mul_add]
  gcongr <;> exact eLpNorm_const_smul_le

private lemma mk_curl_path
    {p : Params} {m Sig : ℝ} (hSig : 0 < Sig) (hν1 : p.ν ≤ 1) (hAge : p.ageCut = Sig)
    {gq gη : CProf}
    (hgq_sm : StronglyMeasurable gq) (hgη_sm : StronglyMeasurable gη)
    (hgq_re : IsRealProf gq) (hgη_re : IsRealProf gη)
    (h_sLp_Xm : sLpNorm (13 / 8) p.H (sliceXmNorm p.c m (profCurl gq gη)) < ⊤)
    (h_circ : ∀ᵐ s ∂volume, s ∈ Ioc 0 p.H →
      IntegrableOn (fun z => profCurl gq gη (s, z)) (B0579.cell p.c) volume ∧
        ∫ z in B0579.cell p.c, profCurl gq gη (s, z) = 0) :
    let cs : ℝ → Xmc p.c m :=
      UnforcedLeray.BochnerTime.toPathLq 2 (B0579.cellMeasure p.c m)
        (fun x => (profCurl gq gη x).re)
    IntegrableOn cs (Ioc 0 p.H) volume ∧
    (∀ᵐ t ∂volume, t ∈ Ioc 0 p.H → HasZeroCirculationR p.c (cs t)) ∧
    (∀ᵐ s ∂volume, s ∈ Ioc 0 p.H →
      ∀ᵐ x ∂volume, x ∈ B0579.cell p.c →
        ((cs s x : ℝ) : ℂ) = profCurl gq gη (s, x)) := by
  intro cs
  have : SigmaFinite (B0579.cellMeasure p.c m) := by unfold B0579.cellMeasure; infer_instance
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let w : Coord → ℝ := fun x => (profCurl gq gη x).re
  have hw_m : Measurable w :=
    Complex.continuous_re.measurable.comp (CylProjectionSub.measurable_profCurl_cp hgq_sm hgη_sm)
  have hcs_sm : StronglyMeasurable cs :=
    UnforcedLeray.BochnerTime.stronglyMeasurable_toPathLq hw_m.stronglyMeasurable
  have hm_Xm : Measurable (sliceXmNorm p.c m (profCurl gq gη)) :=
    CylProjectionSub.measurable_sliceXmNorm_cp p.c m
      (CylProjectionSub.measurable_profCurl_cp hgq_sm hgη_sm)
  have hH_eq : p.H = Sig / p.ν := by rw [Params.H, hAge]
  have h_lint_lt : ∫⁻ s in Ioc 0 p.H, sliceXmNorm p.c m (profCurl gq gη) s < ⊤ := by
    rw [hH_eq] at h_sLp_Xm ⊢
    exact lt_of_le_of_lt (curl_L1_le_of_sLpNorm hSig p.ν_pos hν1 hm_Xm)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top h_sLp_Xm)
  have hae_fin : ∀ᵐ s ∂volume, s ∈ Ioc 0 p.H → sliceXmNorm p.c m (profCurl gq gη) s < ⊤ := by
    rw [← ae_restrict_iff' measurableSet_Ioc]
    exact ae_lt_top hm_Xm h_lint_lt.ne
  have hae_props : ∀ᵐ s ∂volume, s ∈ Ioc 0 p.H →
      HasZeroCirculationR p.c (cs s) ∧
      (∀ᵐ x ∂volume, x ∈ B0579.cell p.c → ((cs s x : ℝ) : ℂ) = profCurl gq gη (s, x)) := by
    filter_upwards [hae_fin, h_circ] with s hfin hc_s hs
    have hw_eq : ∀ z, ((w (s, z) : ℝ) : ℂ) = profCurl gq gη (s, z) :=
      fun z => profCurl_eq_ofReal_re hgq_re hgη_re (s, z)
    have hnorm_eq : eLpNorm (fun z => w (s, z)) 2 (B0579.cellMeasure p.c m) =
        sliceXmNorm p.c m (profCurl gq gη) s := by
      unfold sliceXmNorm
      refine eLpNorm_congr_norm_ae (Eventually.of_forall fun z => ?_)
      rw [← hw_eq z, Complex.norm_real]
    have hmem : MemLp (fun z => w (s, z)) 2 (B0579.cellMeasure p.c m) :=
      ⟨(hw_m.comp measurable_prodMk_left).aestronglyMeasurable,
        by rw [hnorm_eq]; exact hfin hs⟩
    have hcs_eq : cs s = hmem.toLp (fun z => w (s, z)) :=
      UnforcedLeray.BochnerTime.toPathLq_of_memLp hmem
    have hae_res : (cs s : B0579.Plane → ℝ) =ᵐ[volume.restrict (B0579.cell p.c)]
        fun z => w (s, z) := by
      rw [hcs_eq]
      exact (B0579.ac_cellMeasure p.c m).ae_le hmem.coeFn_toLp
    have hcirc_w : HasZeroCirculationR p.c (fun z => w (s, z)) := by
      obtain ⟨hI, h0⟩ := hc_s hs
      refine ⟨Complex.reCLM.integrable_comp hI, ?_⟩
      change ∫ z in B0579.cell p.c, Complex.reCLM (profCurl gq gη (s, z)) = 0
      rw [Complex.reCLM.integral_comp_comm hI, h0, map_zero]
    refine ⟨hasZeroCirculationR_congr_ae hae_res.symm hcirc_w, ?_⟩
    rw [← ae_restrict_iff' (B0579.measurableSet_cell p.c)]
    filter_upwards [hae_res] with z hz
    rw [hz, hw_eq z]
  have hae_cell : ∀ᵐ s ∂volume, s ∈ Ioc 0 p.H →
      ∀ᵐ x ∂volume, x ∈ B0579.cell p.c → ((cs s x : ℝ) : ℂ) = profCurl gq gη (s, x) :=
    hae_props.mono fun _ h hs => (h hs).2
  have hae_circ : ∀ᵐ s ∂volume, s ∈ Ioc 0 p.H → HasZeroCirculationR p.c (cs s) :=
    hae_props.mono fun _ h hs => (h hs).1
  have h_int : IntegrableOn cs (Ioc 0 p.H) volume := by
    refine ⟨hcs_sm.aestronglyMeasurable, ?_⟩
    have hae_enorm : ∀ᵐ s ∂volume.restrict (Ioc 0 p.H),
        ‖cs s‖ₑ = sliceXmNorm p.c m (profCurl gq gη) s := by
      filter_upwards [(ae_restrict_iff' measurableSet_Ioc).2 hae_cell] with s hs
      exact enorm_Xmc_eq_sliceXmNorm_of_ae_cell hs
    change ∫⁻ s in Ioc 0 p.H, ‖cs s‖ₑ < ⊤
    rw [lintegral_congr_ae hae_enorm]
    exact h_lint_lt
  exact ⟨h_int, hae_circ, hae_cell⟩

end LinearBodySourceProof

/-- **Main theorem (`PartII-b:F6/1`, `LinearBodySourceMap`, SP 2213–2239, 2265–2267)**:
unconditional construction of the `ℝ`-linear flat response, projected body-source, and
Bochner-integrable zero-circulation vorticity source maps on `HpR p.c`. -/
theorem linearBodySourceMap_proof : UnforcedLeray.Short.IIb.LinearBodySourceMap := by
  open LinearBodySourceProof in
  intro hBS m hm Sig lam q hSig _hEig dm dp hdm
  obtain ⟨C_src, k_src, ν_s, hC_src, hν_s, hBS_p⟩ := hBS m hm Sig hSig dm dp hdm
  obtain ⟨_, _, hPGF⟩ := profileGraphFlat_bgp
  refine ⟨C_src, k_src, ν_s, hC_src, hν_s, ?_⟩
  intro p d hreg hν_s' hν1 hAge _hMode
  have hν_pos : 0 < p.ν := p.ν_pos
  have hc_pos : 0 < p.c := p.c_pos
  have hH_eq : p.H = Sig / p.ν := by rw [Params.H, hAge]
  -- Pointwise upgraded witness for every F : HpR p.c
  have h_pt : ∀ F : HpR p.c,
      ∃ (b0 b0q b0η g gq gη : CProf) (cs : ℝ → Xmc p.c m),
        InFlatClass p.c bgp b0 ∧
        IsFlatResponse p.ν 0 (toProf p.c F) b0 ∧
        HasWeakVec vQ0 dZero b0 b0q ∧
        HasWeakVec vEta dZero b0 b0η ∧
        StronglyMeasurable g ∧ StronglyMeasurable gq ∧ StronglyMeasurable gη ∧
        QPeriodic p.c g ∧ QPeriodic p.c gq ∧ QPeriodic p.c gη ∧
        HasWeakVec vQ0 dZero g gq ∧
        HasWeakVec vEta dZero g gη ∧
        IsBodySource p.train b0 b0q b0η g ∧
        (∀ᵐ s ∂volume, s ∈ Ioc 0 p.H → sliceH1Norm p.c g gq gη s < ⊤) ∧
        IntegrableOn cs (Ioc 0 p.H) volume ∧
        (∀ᵐ t ∂volume, t ∈ Ioc 0 p.H → HasZeroCirculationR p.c (cs t)) ∧
        (∀ᵐ s ∂volume, s ∈ Ioc 0 p.H →
          ∀ᵐ x ∂volume, x ∈ B0579.cell p.c →
            ((cs s x : ℝ) : ℂ) = profCurl gq gη (s, x)) := by
    intro F
    obtain ⟨b0₀, hb0₀_cls, hb0₀_resp, _, _⟩ :=
      hPGF p.ν p.c hν_pos hc_pos (toProf p.c F) (inHr_toProf hc_pos F)
    obtain ⟨b0q₀, b0η₀, g₀, gq₀, gη₀, hb0q₀, hb0η₀, hg₀_per, hgq₀, hgη₀, hg₀_src,
        _, _, h_sLp₀, h_circ₀⟩ :=
      hBS_p p d hreg hν_s' (toProf p.c F) b0₀ (inHr_toProf hc_pos F) hb0₀_cls hb0₀_resp
    rw [← hH_eq] at h_sLp₀ h_circ₀
    have h_sLp₀' : sLpNorm (13 / 8) p.H (sliceH1Norm p.c g₀ gq₀ gη₀) +
        sLpNorm (13 / 8) p.H (sliceXmNorm p.c m (profCurl gq₀ gη₀)) ≤
          ENNReal.ofReal (C_src * (p.ν ^ k_src)⁻¹ * ‖F‖) := by
      refine h_sLp₀.trans_eq ?_
      rw [hNorm_toProf hc_pos F, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
    obtain ⟨g', gq', gη', hg'_sm, hgq'_sm, hgη'_sm, _, hgq'_re, hgη'_re,
        hg'_per, hgq'_per, hgη'_per, hgq', hgη', hg'_src, h_sLp', h_circ'⟩ :=
      upgrade_bodySource_witness hSig hAge hg₀_per hgq₀ hgη₀ hg₀_src h_sLp₀' h_circ₀
    have hb0_cls : InFlatClass p.c bgp (F10K0Help.reProf b0₀) := F10K0Help.inFlatClass_reProf hb0₀_cls
    have hb0_resp : IsFlatResponse p.ν 0 (toProf p.c F) (F10K0Help.reProf b0₀) := by
      rw [← F10K0Help.reProf_toProf p.c F]
      exact F10K0Help.isFlatResponse_reProf hb0₀_resp
    have hb0q : HasWeakVec vQ0 dZero (F10K0Help.reProf b0₀) (F10K0Help.reProf b0q₀) :=
      F10K0Help.hasWeakVec_reProf hb0q₀
    have hb0η : HasWeakVec vEta dZero (F10K0Help.reProf b0₀) (F10K0Help.reProf b0η₀) :=
      F10K0Help.hasWeakVec_reProf hb0η₀
    have hH1_lt : sLpNorm (13 / 8) p.H (sliceH1Norm p.c g' gq' gη') < ⊤ :=
      lt_of_le_of_lt (le_self_add.trans h_sLp') ENNReal.ofReal_lt_top
    have hXm_lt : sLpNorm (13 / 8) p.H (sliceXmNorm p.c m (profCurl gq' gη')) < ⊤ :=
      lt_of_le_of_lt (le_add_self.trans h_sLp') ENNReal.ofReal_lt_top
    have hm_H1 : Measurable (sliceH1Norm p.c g' gq' gη') :=
      CylProjectionSub.measurable_sliceH1Norm_cp p.c hg'_sm hgq'_sm hgη'_sm
    have h_lint_H1 : ∫⁻ s in Ioc 0 p.H, sliceH1Norm p.c g' gq' gη' s < ⊤ := by
      rw [hH_eq] at hH1_lt ⊢
      exact lt_of_le_of_lt (curl_L1_le_of_sLpNorm hSig hν_pos hν1 hm_H1)
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hH1_lt)
    have hae_fin_H1 : ∀ᵐ s ∂volume, s ∈ Ioc 0 p.H → sliceH1Norm p.c g' gq' gη' s < ⊤ := by
      rw [← ae_restrict_iff' measurableSet_Ioc]
      exact ae_lt_top hm_H1 h_lint_H1.ne
    obtain ⟨h_int, h_circ_cs, h_ae_cell⟩ :=
      mk_curl_path hSig hν1 hAge hgq'_sm hgη'_sm hgq'_re hgη'_re hXm_lt h_circ'
    exact ⟨F10K0Help.reProf b0₀, F10K0Help.reProf b0q₀, F10K0Help.reProf b0η₀,
      g', gq', gη', _, hb0_cls, hb0_resp, hb0q, hb0η, hg'_sm, hgq'_sm, hgη'_sm,
      hg'_per, hgq'_per, hgη'_per, hgq', hgη', hg'_src, hae_fin_H1,
      h_int, h_circ_cs, h_ae_cell⟩
  -- Extend linearly from a Hamel basis of HpR p.c over ℝ
  let B := Module.Basis.ofVectorSpace ℝ (HpR p.c)
  choose b0_bas b0q_bas b0η_bas g_bas gq_bas gη_bas curl_bas h_bas using fun i => h_pt (B i)
  let b0Of : HpR p.c →ₗ[ℝ] CProf := B.constr ℝ b0_bas
  let b0qOf : HpR p.c →ₗ[ℝ] CProf := B.constr ℝ b0q_bas
  let b0ηOf : HpR p.c →ₗ[ℝ] CProf := B.constr ℝ b0η_bas
  let gOf : HpR p.c →ₗ[ℝ] CProf := B.constr ℝ g_bas
  let gqOf : HpR p.c →ₗ[ℝ] CProf := B.constr ℝ gq_bas
  let gηOf : HpR p.c →ₗ[ℝ] CProf := B.constr ℝ gη_bas
  let curlSourceOf : HpR p.c →ₗ[ℝ] (ℝ → Xmc p.c m) := B.constr ℝ curl_bas
  have h_lin : ∀ F : HpR p.c,
      InFlatClass p.c bgp (b0Of F) ∧
      IsFlatResponse p.ν 0 (toProf p.c F) (b0Of F) ∧
      HasWeakVec vQ0 dZero (b0Of F) (b0qOf F) ∧
      HasWeakVec vEta dZero (b0Of F) (b0ηOf F) ∧
      StronglyMeasurable (gOf F) ∧ StronglyMeasurable (gqOf F) ∧ StronglyMeasurable (gηOf F) ∧
      QPeriodic p.c (gOf F) ∧ QPeriodic p.c (gqOf F) ∧ QPeriodic p.c (gηOf F) ∧
      HasWeakVec vQ0 dZero (gOf F) (gqOf F) ∧
      HasWeakVec vEta dZero (gOf F) (gηOf F) ∧
      IsBodySource p.train (b0Of F) (b0qOf F) (b0ηOf F) (gOf F) ∧
      (∀ᵐ s ∂volume, s ∈ Ioc 0 p.H → sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F) s < ⊤) ∧
      IntegrableOn (curlSourceOf F) (Ioc 0 p.H) volume ∧
      (∀ᵐ t ∂volume, t ∈ Ioc 0 p.H → HasZeroCirculationR p.c (curlSourceOf F t)) ∧
      (∀ᵐ s ∂volume, s ∈ Ioc 0 p.H →
        ∀ᵐ x ∂volume, x ∈ B0579.cell p.c →
          ((curlSourceOf F s x : ℝ) : ℂ) = profCurl (gqOf F) (gηOf F) (s, x)) := by
    let S : Submodule ℝ (HpR p.c) :=
      { carrier := {F |
          InFlatClass p.c bgp (b0Of F) ∧
          IsFlatResponse p.ν 0 (toProf p.c F) (b0Of F) ∧
          HasWeakVec vQ0 dZero (b0Of F) (b0qOf F) ∧
          HasWeakVec vEta dZero (b0Of F) (b0ηOf F) ∧
          StronglyMeasurable (gOf F) ∧ StronglyMeasurable (gqOf F) ∧ StronglyMeasurable (gηOf F) ∧
          QPeriodic p.c (gOf F) ∧ QPeriodic p.c (gqOf F) ∧ QPeriodic p.c (gηOf F) ∧
          HasWeakVec vQ0 dZero (gOf F) (gqOf F) ∧
          HasWeakVec vEta dZero (gOf F) (gηOf F) ∧
          IsBodySource p.train (b0Of F) (b0qOf F) (b0ηOf F) (gOf F) ∧
          (∀ᵐ s ∂volume, s ∈ Ioc 0 p.H → sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F) s < ⊤) ∧
          IntegrableOn (curlSourceOf F) (Ioc 0 p.H) volume ∧
          (∀ᵐ t ∂volume, t ∈ Ioc 0 p.H → HasZeroCirculationR p.c (curlSourceOf F t)) ∧
          (∀ᵐ s ∂volume, s ∈ Ioc 0 p.H →
            ∀ᵐ x ∂volume, x ∈ B0579.cell p.c →
              ((curlSourceOf F s x : ℝ) : ℂ) = profCurl (gqOf F) (gηOf F) (s, x))}
        zero_mem' := by
          change InFlatClass p.c bgp (b0Of 0) ∧ _
          simp only [map_zero]
          have h0_cell : ∀ s : ℝ,
              ((0 : Xmc p.c m) : B0579.Plane → ℝ) =ᵐ[volume.restrict (B0579.cell p.c)] 0 :=
            fun _ => (B0579.ac_cellMeasure p.c m).ae_le
              (Lp.coeFn_zero ℝ 2 (B0579.cellMeasure p.c m))
          refine ⟨inFlatClass_zero p.c bgp, isFlatResponse_zero_toProf hc_pos,
            hasWeakVec_zero vQ0 dZero, hasWeakVec_zero vEta dZero,
            stronglyMeasurable_zero, stronglyMeasurable_zero, stronglyMeasurable_zero,
            qPeriodic_zero p.c, qPeriodic_zero p.c, qPeriodic_zero p.c,
            hasWeakVec_zero vQ0 dZero, hasWeakVec_zero vEta dZero,
            isBodySource_zero p.train,
            Eventually.of_forall fun s _ => by simp [sliceH1Norm],
            integrableOn_zero,
            Eventually.of_forall fun t _ =>
              hasZeroCirculationR_congr_ae (h0_cell t).symm (hasZeroCirculationR_zero p.c),
            Eventually.of_forall fun s _ => ?_⟩
          rw [← ae_restrict_iff' (B0579.measurableSet_cell p.c)]
          filter_upwards [h0_cell s] with x hx
          have hx0 : ((0 : Xmc p.c m) : B0579.Plane → ℝ) x = 0 := hx
          change (((0 : Xmc p.c m) : B0579.Plane → ℝ) x : ℂ) = profCurl 0 0 (s, x)
          rw [hx0]
          simp [profCurl]
        add_mem' := by
          intro F₁ F₂ h₁ h₂
          change InFlatClass p.c bgp (b0Of (F₁ + F₂)) ∧ _
          simp only [map_add]
          rcases h₁ with ⟨hc1, hr1, hq1, hη1, smg1, smgq1, smgη1, pg1, pgq1, pgη1,
            wgq1, wgη1, bs1, fin1, int1, circ1, cell1⟩
          rcases h₂ with ⟨hc2, hr2, hq2, hη2, smg2, smgq2, smgη2, pg2, pgq2, pgη2,
            wgq2, wgη2, bs2, fin2, int2, circ2, cell2⟩
          have hr_bgp : (1 : ℝ) ≤ bgp := by norm_num [bgp]
          refine ⟨F10K0Help.inFlatClass_add hr_bgp hc1 hc2,
            isFlatResponse_add_toProf hc_pos hr1 hr2,
            F10Help.hasWeakVec_add' hq1 hq2,
            F10Help.hasWeakVec_add' hη1 hη2,
            smg1.add smg2, smgq1.add smgq2, smgη1.add smgη2,
            qPeriodic_add pg1 pg2, qPeriodic_add pgq1 pgq2, qPeriodic_add pgη1 pgη2,
            F10Help.hasWeakVec_add' wgq1 wgq2,
            F10Help.hasWeakVec_add' wgη1 wgη2,
            isBodySource_add bs1 bs2,
            ?_, int1.add int2, ?_, ?_⟩
          · filter_upwards [fin1, fin2] with s hs1 hs2 hs
            exact lt_of_le_of_lt
              (sliceH1Norm_add_le p.c smg1 smgq1 smgη1 smg2 smgq2 smgη2 s)
              (ENNReal.add_lt_top.2 ⟨hs1 hs, hs2 hs⟩)
          · filter_upwards [circ1, circ2] with t ht1 ht2 ht
            have hadd_ae : (((curlSourceOf F₁ + curlSourceOf F₂) t : Xmc p.c m) :
                B0579.Plane → ℝ) =ᵐ[volume.restrict (B0579.cell p.c)]
                ((curlSourceOf F₁ t : B0579.Plane → ℝ) +
                  (curlSourceOf F₂ t : B0579.Plane → ℝ)) :=
              (B0579.ac_cellMeasure p.c m).ae_le
                (Lp.coeFn_add (curlSourceOf F₁ t) (curlSourceOf F₂ t))
            exact hasZeroCirculationR_congr_ae hadd_ae.symm
              (hasZeroCirculationR_add (ht1 ht) (ht2 ht))
          · filter_upwards [cell1, cell2] with s hs1 hs2 hs
            have hadd_ae : (((curlSourceOf F₁ + curlSourceOf F₂) s : Xmc p.c m) :
                B0579.Plane → ℝ) =ᵐ[volume.restrict (B0579.cell p.c)]
                (fun x => curlSourceOf F₁ s x + curlSourceOf F₂ s x) :=
              (B0579.ac_cellMeasure p.c m).ae_le
                (Lp.coeFn_add (curlSourceOf F₁ s) (curlSourceOf F₂ s))
            rw [← ae_restrict_iff' (B0579.measurableSet_cell p.c)]
            filter_upwards [hadd_ae, (ae_restrict_iff' (B0579.measurableSet_cell p.c)).2 (hs1 hs),
              (ae_restrict_iff' (B0579.measurableSet_cell p.c)).2 (hs2 hs)] with x hx hx1 hx2
            rw [hx, Complex.ofReal_add, hx1, hx2, profCurl_add, Pi.add_apply]
        smul_mem' := by
          intro a F hF
          change InFlatClass p.c bgp (b0Of (a • F)) ∧ _
          simp only [map_smul]
          rcases hF with ⟨hc1, hr1, hq1, hη1, smg1, smgq1, smgη1, pg1, pgq1, pgη1,
            wgq1, wgη1, bs1, fin1, int1, circ1, cell1⟩
          refine ⟨inFlatClass_smul_real a hc1,
            isFlatResponse_smul_real_toProf hc_pos a hr1,
            hasWeakVec_smul_real a hq1,
            hasWeakVec_smul_real a hη1,
            smg1.const_smul a, smgq1.const_smul a, smgη1.const_smul a,
            qPeriodic_smul_real a pg1, qPeriodic_smul_real a pgq1, qPeriodic_smul_real a pgη1,
            hasWeakVec_smul_real a wgq1,
            hasWeakVec_smul_real a wgη1,
            isBodySource_smul_real a bs1,
            ?_, int1.smul a, ?_, ?_⟩
          · filter_upwards [fin1] with s hs1 hs
            exact lt_of_le_of_lt (sliceH1Norm_smul_le p.c a _ _ _ s)
              (ENNReal.mul_lt_top enorm_lt_top (hs1 hs))
          · filter_upwards [circ1] with t ht1 ht
            have hsmul_ae : (((a • curlSourceOf F) t : Xmc p.c m) :
                B0579.Plane → ℝ) =ᵐ[volume.restrict (B0579.cell p.c)]
                (a • (curlSourceOf F t : B0579.Plane → ℝ)) :=
              (B0579.ac_cellMeasure p.c m).ae_le
                (Lp.coeFn_smul a (curlSourceOf F t))
            exact hasZeroCirculationR_congr_ae hsmul_ae.symm
              (hasZeroCirculationR_smul_real a (ht1 ht))
          · filter_upwards [cell1] with s hs1 hs
            have hsmul_ae : (((a • curlSourceOf F) s : Xmc p.c m) :
                B0579.Plane → ℝ) =ᵐ[volume.restrict (B0579.cell p.c)]
                (fun x => a * curlSourceOf F s x) :=
              (B0579.ac_cellMeasure p.c m).ae_le
                (Lp.coeFn_smul a (curlSourceOf F s))
            rw [← ae_restrict_iff' (B0579.measurableSet_cell p.c)]
            filter_upwards [hsmul_ae,
              (ae_restrict_iff' (B0579.measurableSet_cell p.c)).2 (hs1 hs)] with x hx hx1
            rw [hx, Complex.ofReal_mul, hx1, profCurl_smul_real] }
    have h_range : Set.range B ⊆ (S : Set (HpR p.c)) := by
      rintro _ ⟨i, rfl⟩
      change InFlatClass p.c bgp (b0Of (B i)) ∧ _
      simp only [b0Of, b0qOf, b0ηOf, gOf, gqOf, gηOf, curlSourceOf, Module.Basis.constr_basis]
      exact h_bas i
    have h_top : S = ⊤ :=
      top_unique (by rw [← B.span_eq]; exact Submodule.span_le.2 h_range)
    intro F
    have hmem : F ∈ S := by rw [h_top]; exact Submodule.mem_top
    exact hmem
  refine ⟨b0Of, b0qOf, b0ηOf, gOf, gqOf, gηOf, curlSourceOf, fun F => ?_⟩
  rcases h_lin F with ⟨hb0_cls, hb0_resp, hb0q, hb0η, hgOf_sm, hgqOf_sm, hgηOf_sm,
    hgOf_per, hgqOf_per, hgηOf_per, hgqOf, hgηOf, hgOf_src, hgOf_fin,
    h_int, h_circ, h_ae_cell⟩
  have hm_H1 : Measurable (sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F)) :=
    CylProjectionSub.measurable_sliceH1Norm_cp p.c hgOf_sm hgqOf_sm hgηOf_sm
  have hm_Xm : Measurable (sliceXmNorm p.c m (profCurl (gqOf F) (gηOf F))) :=
    CylProjectionSub.measurable_sliceXmNorm_cp p.c m
      (CylProjectionSub.measurable_profCurl_cp hgqOf_sm hgηOf_sm)
  -- Compare (gOf F, gqOf F, gηOf F) with an upgraded BodySourceBound witness for (toProf p.c F, b0Of F)
  obtain ⟨b0q', b0η', g₀, gq₀, gη₀, hb0q', hb0η', hg₀_per, hgq₀, hgη₀, hg₀_src',
      _, _, h_sLp₀, h_circ₀⟩ :=
    hBS_p p d hreg hν_s' (toProf p.c F) (b0Of F) (inHr_toProf hc_pos F) hb0_cls hb0_resp
  have hg₀_src : IsBodySource p.train (b0Of F) (b0qOf F) (b0ηOf F) g₀ :=
    isBodySource_congr_deriv
      (GradBoundHelp.hasWeakVec_unique hb0q' hb0q)
      (GradBoundHelp.hasWeakVec_unique hb0η' hb0η)
      hg₀_src'
  rw [← hH_eq] at h_sLp₀ h_circ₀
  have h_sLp₀' : sLpNorm (13 / 8) p.H (sliceH1Norm p.c g₀ gq₀ gη₀) +
      sLpNorm (13 / 8) p.H (sliceXmNorm p.c m (profCurl gq₀ gη₀)) ≤
        ENNReal.ofReal (C_src * (p.ν ^ k_src)⁻¹ * ‖F‖) := by
    refine h_sLp₀.trans_eq ?_
    rw [hNorm_toProf hc_pos F, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
  obtain ⟨g', gq', gη', hg'_sm, hgq'_sm, hgη'_sm, _, _, _,
      hg'_per, hgq'_per, hgη'_per, hgq', hgη', hg'_src_re, h_sLp', _⟩ :=
    upgrade_bodySource_witness hSig hAge hg₀_per hgq₀ hgη₀ hg₀_src h_sLp₀' h_circ₀
  -- Note reProf (b0Of F), reProf (b0qOf F), reProf (b0ηOf F) agree a.e. on s > 0 with b0Of F, b0qOf F, b0ηOf F
  have hb0_re_cls : InFlatClass p.c bgp (F10K0Help.reProf (b0Of F)) :=
    F10K0Help.inFlatClass_reProf hb0_cls
  have hb0_re_resp : IsFlatResponse p.ν 0 (toProf p.c F) (F10K0Help.reProf (b0Of F)) := by
    rw [← F10K0Help.reProf_toProf p.c F]
    exact F10K0Help.isFlatResponse_reProf hb0_resp
  have hb0_ae : ∀ᵐ x : Coord, 0 < x.1 → F10K0Help.reProf (b0Of F) x = b0Of F x :=
    CongrHelp.ae_volume_of_ageμ hc_pos hb0_re_cls.inHr.periodic hb0_cls.inHr.periodic
      (flatResponse_unique_ae hν_pos hc_pos (inHr_toProf hc_pos F)
        hb0_re_cls hb0_re_resp hb0_cls hb0_resp)
  have hb0_ae' : ∀ᵐ x : Coord, 0 < x.1 → b0Of F x = F10K0Help.reProf (b0Of F) x :=
    hb0_ae.mono fun _ hx hp => (hx hp).symm
  have hb0q_ae : ∀ᵐ x : Coord, 0 < x.1 → F10K0Help.reProf (b0qOf F) x = b0qOf F x :=
    GradBoundHelp.hasWeakVec_unique
      (hasWeakVec_congr hb0_ae' (Eventually.of_forall fun _ _ => rfl)
        (F10K0Help.hasWeakVec_reProf hb0q))
      hb0q
  have hb0η_ae : ∀ᵐ x : Coord, 0 < x.1 → F10K0Help.reProf (b0ηOf F) x = b0ηOf F x :=
    GradBoundHelp.hasWeakVec_unique
      (hasWeakVec_congr hb0_ae' (Eventually.of_forall fun _ _ => rfl)
        (F10K0Help.hasWeakVec_reProf hb0η))
      hb0η
  have hg'_src : IsBodySource p.train (b0Of F) (b0qOf F) (b0ηOf F) g' := by
    refine ⟨hg'_src_re.solenoidal, fun Ψ hΨ => ?_⟩
    obtain ⟨hG, hB, hEq⟩ := hg'_src_re.equation Ψ hΨ
    have hae : cdot (flatBv p.train (F10K0Help.reProf (b0Of F))
          (F10K0Help.reProf (b0qOf F)) (F10K0Help.reProf (b0ηOf F))) Ψ =ᵐ[volume]
        cdot (flatBv p.train (b0Of F) (b0qOf F) (b0ηOf F)) Ψ := by
      filter_upwards [hb0_ae, hb0q_ae, hb0η_ae] with x hb hq hη
      by_cases hp : 0 < x.1
      · have hbv : flatBv p.train (F10K0Help.reProf (b0Of F))
            (F10K0Help.reProf (b0qOf F)) (F10K0Help.reProf (b0ηOf F)) x =
            flatBv p.train (b0Of F) (b0qOf F) (b0ηOf F) x := by
          ext i; simp only [flatBv, WithLp.ofLp_toLp, hb hp, hq hp, hη hp]
        simp only [cdot, hbv]
      · have h0 : ∀ i : Fin 2, Ψ x i = 0 :=
          fun i => F10K0Help.isCoordTest_zero_of_nonpos (hΨ.smooth i) hp
        simp [cdot, h0]
    exact ⟨hG, hB.congr hae, hEq.trans (congrArg Neg.neg (integral_congr_ae hae))⟩
  have hm_H1' : Measurable (sliceH1Norm p.c g' gq' gη') :=
    CylProjectionSub.measurable_sliceH1Norm_cp p.c hg'_sm hgq'_sm hgη'_sm
  have hH1'_lt : sLpNorm (13 / 8) p.H (sliceH1Norm p.c g' gq' gη') < ⊤ :=
    lt_of_le_of_lt (le_self_add.trans h_sLp') ENNReal.ofReal_lt_top
  have h_lint_H1' : ∫⁻ s in Ioc 0 p.H, sliceH1Norm p.c g' gq' gη' s < ⊤ := by
    rw [hH_eq] at hH1'_lt ⊢
    exact lt_of_le_of_lt (curl_L1_le_of_sLpNorm hSig hν_pos hν1 hm_H1')
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hH1'_lt)
  have hg'_fin : ∀ᵐ s ∂volume, s ∈ Ioc 0 p.H → sliceH1Norm p.c g' gq' gη' s < ⊤ := by
    rw [← ae_restrict_iff' measurableSet_Ioc]
    exact ae_lt_top hm_H1' h_lint_H1'.ne
  have hae_eq := ae_cell_eq_of_isBodySource hc_pos hgOf_sm hgqOf_sm hgηOf_sm
    hg'_sm hgq'_sm hgη'_sm hgOf_per hgqOf_per hgηOf_per hg'_per hgq'_per hgη'_per
    hgqOf hgηOf hgq' hgη' hgOf_src hg'_src hgOf_fin hg'_fin
  have hH1_eq : sLpNorm (13 / 8) p.H (sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F)) =
      sLpNorm (13 / 8) p.H (sliceH1Norm p.c g' gq' gη') := by
    refine sLpNorm_congr_ae_Ioc ?_
    filter_upwards [hae_eq] with s hs hm
    exact sliceH1Norm_congr_ae_cell (hs hm).1 (hs hm).2.1 (hs hm).2.2
  have hXm_eq : sLpNorm (13 / 8) p.H (sliceXmNorm p.c m (profCurl (gqOf F) (gηOf F))) =
      sLpNorm (13 / 8) p.H (sliceXmNorm p.c m (profCurl gq' gη')) := by
    refine sLpNorm_congr_ae_Ioc ?_
    filter_upwards [hae_eq] with s hs hm
    exact sliceXmNorm_profCurl_congr_ae_cell (hs hm).2.1 (hs hm).2.2
  have h_sLp_H1 : sLpNorm (13 / 8) p.H (sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F)) ≤
      ENNReal.ofReal (C_src * (p.ν ^ k_src)⁻¹ * ‖F‖) := by
    rw [hH1_eq]
    exact le_self_add.trans h_sLp'
  have h_sLp_Xm : sLpNorm (13 / 8) p.H (sliceXmNorm p.c m (profCurl (gqOf F) (gηOf F))) ≤
      ENNReal.ofReal (C_src * (p.ν ^ k_src)⁻¹ * ‖F‖) := by
    rw [hXm_eq]
    exact le_add_self.trans h_sLp'
  have h_L1 :=
    integral_norm_curlSource_le hSig hν1 hAge hC_src F hm_Xm h_sLp_Xm h_int h_ae_cell
  exact ⟨hb0_cls, hb0_resp, hb0q, hb0η, hgOf_per, hgqOf, hgηOf, hgOf_src, hm_H1, h_sLp_H1,
    h_int, h_circ, h_ae_cell, h_L1⟩

end UnforcedLeray.Short.IIb

end
