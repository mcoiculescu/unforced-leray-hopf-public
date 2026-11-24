import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F9
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Mem
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Difference
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanDecay
import UnforcedLeray.Short.PartI.Tasks.TrainVorticityTail
import UnforcedLeray.Short.PartI.Tasks.TrainStreamTails
import UnforcedLeray.Short.PartI.Tasks.TrainFluctuationDecayProof
import UnforcedLeray.Short.PartI.Tasks.TrainTransverseTailsProof
import UnforcedLeray.Short.PartI.Tasks.TrainFixedBandProof

/-!
# Part II-b, task `PartII-b:F9/2`: Flat inlet column `H_p` bound (`FlatColumnHpStep`)

Source of record: `the November 2 reference manuscript` (SP), lines 2328,
2370–2385.

Proves `FlatColumnHpStep`: each flat inlet column
`flatColumn p i = s[(∂_s - νΔ)e_0 + B_v e_0]` lies in `H_p` (`QPeriodic`, `AEStronglyMeasurable`,
and finite `H_p` norm) with polynomial `ν⁻¹` norm bound
`hNorm p.c bgp (flatColumn p i) ≤ ENNReal.ofReal (C * (p.ν ^ k)⁻¹)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Short

namespace FlatColumnBoundAux

private abbrev posU : Set Coord := {x : Coord | 0 < x.1}

private theorem isOpen_posU : IsOpen posU := isOpen_lt continuous_const continuous_fst

private theorem qShift_eq (c : ℝ) (x : Coord) : qShift c x = x + (0, (c, 0)) := by
  simp [qShift, Prod.ext_iff]

private theorem fderiv_qShift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Coord → E} {c : ℝ} {U : Set Coord} (hU : IsOpen U)
    (hF : ∀ y ∈ U, F (qShift c y) = F y) {x : Coord} (hx : x ∈ U) :
    fderiv ℝ F (qShift c x) = fderiv ℝ F x := by
  have hev : (fun y => F (qShift c y)) =ᶠ[𝓝 x] F := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hF y hy
  have hfun : (fun y => F (qShift c y)) = fun y => F (y + (0, (c, 0))) := by
    funext y
    rw [qShift_eq]
  have h1 : fderiv ℝ (fun y => F (qShift c y)) x = fderiv ℝ F x := hev.fderiv_eq
  rw [hfun, fderiv_comp_add_right] at h1
  rw [qShift_eq]
  exact h1

private theorem dS_qShift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Coord → E} {c : ℝ} {U : Set Coord} (hU : IsOpen U)
    (hF : ∀ y ∈ U, F (qShift c y) = F y) {x : Coord} (hx : x ∈ U) :
    Axi.dS F (qShift c x) = Axi.dS F x := by
  unfold Axi.dS
  rw [fderiv_qShift hU hF hx]

private theorem dQ_qShift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Coord → E} {c : ℝ} {U : Set Coord} (hU : IsOpen U)
    (hF : ∀ y ∈ U, F (qShift c y) = F y) {x : Coord} (hx : x ∈ U) :
    Axi.dQ F (qShift c x) = Axi.dQ F x := by
  unfold Axi.dQ
  rw [fderiv_qShift hU hF hx]

private theorem dEta_qShift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Coord → E} {c : ℝ} {U : Set Coord} (hU : IsOpen U)
    (hF : ∀ y ∈ U, F (qShift c y) = F y) {x : Coord} (hx : x ∈ U) :
    Axi.dEta F (qShift c x) = Axi.dEta F x := by
  unfold Axi.dEta
  rw [fderiv_qShift hU hF hx]

private theorem cutStream_qShift (p : Params) (i : Fin 2) :
    ∀ y ∈ (univ : Set Coord), p.cutStream i (qShift p.c y) = p.cutStream i y := by
  intro y _
  rw [qShift_eq]
  exact p.cutStream_add i y

private theorem inletE0_qShift (p : Params) (i : Fin 2) :
    ∀ y ∈ posU, inletE0 p i (qShift p.c y) = inletE0 p i y := by
  intro y _
  have hQ := dQ_qShift isOpen_univ (cutStream_qShift p i) (mem_univ y)
  have hE := dEta_qShift isOpen_univ (cutStream_qShift p i) (mem_univ y)
  unfold inletE0
  rw [hQ, hE]

private theorem trainProf_qShift (p : Params) :
    ∀ y ∈ posU, trainProf p (qShift p.c y) = trainProf p y := by
  intro y (hy : 0 < y.1)
  exact p.train.isTrain.periodic_v y.1 hy.le y.2

private theorem flatReal_qShift (p : Params) (i : Fin 2) {x : Coord} (hx : x ∈ posU) :
    flatReal p i (qShift p.c x) = flatReal p i x := by
  have hU := isOpen_posU
  have hE0 := inletE0_qShift p i
  have hdQ1 : ∀ y ∈ posU, Axi.dQ (inletE0 p i) (qShift p.c y) = Axi.dQ (inletE0 p i) y :=
    fun y hy => dQ_qShift hU hE0 hy
  have hdE1 : ∀ y ∈ posU, Axi.dEta (inletE0 p i) (qShift p.c y) = Axi.dEta (inletE0 p i) y :=
    fun y hy => dEta_qShift hU hE0 hy
  have hTr := trainProf_qShift p
  have hs : (qShift p.c x).1 = x.1 := rfl
  unfold flatReal flatB
  rw [hs, dS_qShift hU hE0 hx, dQ_qShift hU hdQ1 hx, dEta_qShift hU hdE1 hx,
    hTr x hx, hdQ1 x hx, hdE1 x hx, hE0 x hx, dQ_qShift hU hTr hx, dEta_qShift hU hTr hx]

private theorem qPeriodic_flatColumn (p : Params) (i : Fin 2)
    (hfr : ∀ x : Coord, 0 < x.1 → flatColumn p i x = cplx (flatReal p i) x) :
    QPeriodic p.c (flatColumn p i) := by
  unfold QPeriodic
  filter_upwards [ae_restrict_mem isOpen_posU.measurableSet] with x hx
  have hx' : 0 < (qShift p.c x).1 := hx
  rw [hfr (qShift p.c x) hx', hfr x hx]
  simp only [cplx, flatReal_qShift p i hx]

private theorem cd_fderiv_apply {G : Coord → Axi.Merid}
    (hG : ContDiffOn ℝ ∞ G posU) (v : Coord) :
    ContDiffOn ℝ ∞ (fun x => fderiv ℝ G x v) posU :=
  (hG.fderiv_of_isOpen isOpen_posU (m := ∞) (by simp)).clm_apply contDiffOn_const

private theorem cd_dS {G : Coord → Axi.Merid} (hG : ContDiffOn ℝ ∞ G posU) :
    ContDiffOn ℝ ∞ (Axi.dS G) posU :=
  cd_fderiv_apply hG (1, (0, 0))

private theorem cd_dQ {G : Coord → Axi.Merid} (hG : ContDiffOn ℝ ∞ G posU) :
    ContDiffOn ℝ ∞ (Axi.dQ G) posU :=
  cd_fderiv_apply hG (0, (1, 0))

private theorem cd_dEta {G : Coord → Axi.Merid} (hG : ContDiffOn ℝ ∞ G posU) :
    ContDiffOn ℝ ∞ (Axi.dEta G) posU :=
  cd_fderiv_apply hG (0, (0, 1))

private theorem cd_coord {G : Coord → Axi.Merid} (hG : ContDiffOn ℝ ∞ G posU) (j : Fin 2) :
    ContDiffOn ℝ ∞ (fun x => G x j) posU :=
  (EuclideanSpace.proj j : Axi.Merid →L[ℝ] ℝ).contDiff.comp_contDiffOn hG

private theorem cd_flatReal (p : Params) (i : Fin 2)
    (hE0 : ContDiff ℝ ∞ (inletE0 p i)) :
    ContDiffOn ℝ ∞ (flatReal p i) posU := by
  have hF : ContDiffOn ℝ ∞ (inletE0 p i) posU := hE0.contDiffOn
  have hv : ContDiffOn ℝ ∞ (trainProf p) posU :=
    p.train.isTrain.smooth_v.mono (fun x (hx : 0 < x.1) => ⟨hx.le, trivial⟩)
  have hB : ContDiffOn ℝ ∞ (flatB p (inletE0 p i)) posU := by
    unfold flatB
    exact (((cd_coord hv 0).smul (cd_dQ hF)).add ((cd_coord hv 1).smul (cd_dEta hF))).add
      (((cd_coord hF 0).smul (cd_dQ hv)).add ((cd_coord hF 1).smul (cd_dEta hv)))
  unfold flatReal
  exact contDiff_fst.contDiffOn.smul
    (((cd_dS hF).sub ((contDiffOn_const (c := p.ν)).smul
      ((cd_dQ (cd_dQ hF)).add (cd_dEta (cd_dEta hF))))).add hB)

private theorem cplx_continuous :
    Continuous (fun v : Axi.Merid => (WithLp.toLp 2 (fun j => ((v j : ℝ) : ℂ)) : CMerid)) :=
  (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℂ)).comp
    (continuous_pi fun j => Complex.continuous_ofReal.comp (EuclideanSpace.proj j).continuous)

private theorem aestronglyMeasurable_flatColumn (p : Params) (i : Fin 2)
    (hc : 0 < p.c) (hE0 : ContDiff ℝ ∞ (inletE0 p i))
    (hfr : ∀ x : Coord, 0 < x.1 → flatColumn p i x = cplx (flatReal p i) x) :
    AEStronglyMeasurable (flatColumn p i) (hMeas p.c bgp) := by
  have hcont : ContinuousOn (cplx (flatReal p i)) posU :=
    cplx_continuous.comp_continuousOn (cd_flatReal p i hE0).continuousOn
  have hind : AEStronglyMeasurable (posU.indicator (cplx (flatReal p i))) (hMeas p.c bgp) :=
    (aestronglyMeasurable_indicator_iff isOpen_posU.measurableSet).mpr
      (hcont.aestronglyMeasurable isOpen_posU.measurableSet)
  refine hind.congr ?_
  filter_upwards [Axi.ae_ageμ_mem hc (bgp / 2 - 5 / 2)] with x hx
  have hxU : x ∈ posU := hx.1
  rw [Set.indicator_of_mem hxU, hfr x hx.1]

private theorem rawJetBound_proved : RawJetBound :=
  let hFD0 : PartI.OverlapFluctuationDecay :=
    PartI.overlap_fluctuation_decay PartI.overlap_highnorm_uniform
  let hOv : PartI.TrainOverlap :=
    PartI.trainOverlap_proof hFD0
      (PartI.overlap_mean_decay PartI.overlap_highnorm_uniform hFD0 PartI.overlap_mean_primitive)
  let hVort : PartI.TrainVorticityGaussianTail := PartI.train_vorticity_gaussian_tail hOv
  let hTails : PartI.TrainStreamVelocityPressureTails :=
    PartI.train_stream_velocity_pressure_tails hOv hVort
  let hFD : PartI.TrainFluctuationDecay := PartI.trainFluctuationDecay_proof hTails hFD0 hOv
  rawJetBound_of (PartI.trainTransverseTails_proof hVort hTails)
    (PartI.trainFixedBand_proof hTails hFD)

private theorem colEps_hNorm_bound :
    ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
      Blueprint.Planar.IsGrowingEigenpair lam q →
    ∀ dm dp : ℝ, 0 < dm →
      ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
        ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
          ∀ i : Fin 2,
            hNorm p.c bgp (colEps p i) ≤ ENNReal.ofReal (C * (p.ν ^ k)⁻¹) := by
  intro Sig lam q hSig hq dm dp hdm
  have hEnv : ColEnvelope :=
    colEnvelope_of_parts (rawProfJet_of rawJetBound_proved)
      inletJetDecay jetLe vecDiffJet bEpsJet colVanish
  obtain ⟨A, κ, k, N, ν₀, hA, hκ, hν₀, hν₀1, HE⟩ := hEnv Sig lam q hSig hq dm dp hdm
  obtain ⟨K, hK, HW⟩ := colWeightNorm N κ hκ
  refine ⟨K * A * (1 + Sig), k + 1 + 2 * (N + 1), ν₀, by positivity, hν₀, ?_⟩
  intro p d hreg hν hS hm i
  have hνpos : 0 < p.ν := p.ν_pos
  have hν1 : p.ν ≤ 1 := hν.trans hν₀1
  have hc1 : 1 ≤ p.c := by
    rw [hreg.c_eq, one_le_inv₀ (by positivity)]
    nlinarith
  have hH : 0 < p.H := div_pos p.ageCut_pos hνpos
  obtain ⟨hvan, hbd⟩ := HE p d ⟨hreg, hν, hS, hm⟩ i
  have hMnn : 0 ≤ A * (p.ν ^ k)⁻¹ := by positivity
  have hle := HW p.c p.H (A * (p.ν ^ k)⁻¹) (colEps p i) hc1 hH hMnn
    (fun x hx => by
      have := hvan x hx
      ext j
      simp [colEps, cplx, this])
    (fun x hx0 hx1 => by
      have e : ‖colEps p i x‖ = ‖colEpsR p i x‖ := liftM_norm _
      rw [e]
      exact hbd x hx0 hx1)
  have hHle : 1 + p.H ≤ (1 + Sig) * p.ν⁻¹ := by
    have hHeq : p.H = Sig / p.ν := by simp [Params.H, hS]
    rw [hHeq]
    have hinv1 : 1 ≤ p.ν⁻¹ := (one_le_inv₀ hνpos).2 hν1
    have h4 : (1 + Sig) * p.ν⁻¹ = p.ν⁻¹ + Sig / p.ν := by ring
    rw [h4]
    linarith
  have hcpow : p.c ^ (N + 1) = (p.ν ^ (2 * (N + 1)))⁻¹ := by
    rw [hreg.c_eq, inv_pow, ← pow_mul]
  refine hle.trans (ENNReal.ofReal_le_ofReal ?_)
  calc K * (A * (p.ν ^ k)⁻¹) * (1 + p.H) * p.c ^ (N + 1)
      ≤ K * (A * (p.ν ^ k)⁻¹) * ((1 + Sig) * p.ν⁻¹) * p.c ^ (N + 1) := by gcongr
    _ = K * A * (1 + Sig) * (p.ν ^ (k + 1 + 2 * (N + 1)))⁻¹ := by
        rw [hcpow]
        have hp : (p.ν ^ (k + 1 + 2 * (N + 1)))⁻¹ =
            (p.ν ^ k)⁻¹ * p.ν⁻¹ * (p.ν ^ (2 * (N + 1)))⁻¹ := by
          rw [pow_add, pow_add, pow_one, mul_inv, mul_inv]
        rw [hp]
        ring

end FlatColumnBoundAux

open FlatColumnBoundAux in
/-- **`PartII-b:F9/2`** (`FlatColumnHpStep`, SP 2328, 2370–2385): each flat inlet column
`flatColumn p i` lies in `H_p` with polynomial `ν⁻¹` norm bound. -/
theorem flatColumnHpStep_proof : UnforcedLeray.Short.IIb.FlatColumnHpStep := by
  intro Sig lam q hSig hq dm dp hdm
  obtain ⟨C₁, k₁, ν₁, hC₁, hν₁, HB₁⟩ := colEps_hNorm_bound Sig lam q hSig hq dm dp hdm
  obtain ⟨C₂, k₂, ν₂, hC₂, hν₂, HB₂⟩ :=
    columnDifference_of rawJetBound_proved Sig lam q hSig hq dm dp hdm
  obtain ⟨ν₃, hν₃, HM₃⟩ := colAEMeas Sig lam q hSig hq dm dp hdm
  obtain ⟨ν₄, hν₄, HFR⟩ := flatColumnReal Sig lam q hSig hq dm dp hdm
  obtain ⟨_CJ, _κJ, _kJ, _NJ, ν₅, _hCJ, _hκJ, hν₅, _hν₅1, HCJ⟩ :=
    inletComponentJets Sig lam q hSig hq dm dp hdm 0
  set C : ℝ := C₁ + C₂
  set k : ℕ := max k₁ k₂
  set ν₀ : ℝ := min 1 (min ν₁ (min ν₂ (min ν₃ (min ν₄ ν₅))))
  have hC : 0 < C := add_pos hC₁ hC₂
  have hν₀ : 0 < ν₀ :=
    lt_min zero_lt_one (lt_min hν₁ (lt_min hν₂ (lt_min hν₃ (lt_min hν₄ hν₅))))
  refine ⟨C, k, ν₀, hC, hν₀, ?_⟩
  intro p d hreg hν hS hm i
  have hνpos : 0 < p.ν := p.ν_pos
  have hν_le1 : p.ν ≤ 1 := hν.trans (min_le_left _ _)
  have h1 : p.ν ≤ ν₁ := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have h2 : p.ν ≤ ν₂ :=
    hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have h3 : p.ν ≤ ν₃ :=
    hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have h4 : p.ν ≤ ν₄ :=
    hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have h5 : p.ν ≤ ν₅ :=
    hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
  have hfr : ∀ x : Coord, 0 < x.1 → flatColumn p i x = cplx (flatReal p i) x :=
    HFR p d ⟨hreg, h4, hS, hm⟩ i
  have hE0_cd : ContDiff ℝ ∞ (inletE0 p i) := (HCJ p d ⟨hreg, h5, hS, hm⟩ i).1
  have hper : QPeriodic p.c (flatColumn p i) := qPeriodic_flatColumn p i hfr
  have hmeas_flat : AEStronglyMeasurable (flatColumn p i) (hMeas p.c bgp) :=
    aestronglyMeasurable_flatColumn p i p.c_pos hE0_cd hfr
  have hmeas_eps : AEStronglyMeasurable (colEps p i) (hMeas p.c bgp) :=
    HM₃ p d ⟨hreg, h3, hS, hm⟩ i
  have hmeas_diff :
      AEStronglyMeasurable (fun x => colEps p i x - flatColumn p i x) (hMeas p.c bgp) :=
    hmeas_eps.sub hmeas_flat
  have hε_le1 : p.ε ≤ 1 := by
    rw [hreg.eps_eq, Real.exp_le_one_iff, neg_div]
    have hd : 0 < d := lt_of_lt_of_le hreg.dm_pos hreg.dm_le
    have hdν : 0 ≤ d / p.ν := div_nonneg hd.le hνpos.le
    linarith
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal bgp := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by norm_num [bgp])
  have heq_sub : flatColumn p i = colEps p i - (fun x => colEps p i x - flatColumn p i x) := by
    funext x
    simp
  have htri : hNorm p.c bgp (flatColumn p i) ≤
      hNorm p.c bgp (colEps p i) + hNorm p.c bgp (fun x => colEps p i x - flatColumn p i x) := by
    unfold hNorm
    have hsub := eLpNorm_sub_le hmeas_eps hmeas_diff hp1
    rwa [← heq_sub] at hsub
  have hb1 : hNorm p.c bgp (colEps p i) ≤ ENNReal.ofReal (C₁ * (p.ν ^ k₁)⁻¹) :=
    HB₁ p d hreg h1 hS hm i
  have hb2 : hNorm p.c bgp (fun x => colEps p i x - flatColumn p i x) ≤
      ENNReal.ofReal (C₂ * (p.ν ^ k₂)⁻¹) := by
    refine (HB₂ p d hreg h2 hS hm i).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_of_le_one_right (by positivity) hε_le1
  have hle1 : C₁ * (p.ν ^ k₁)⁻¹ ≤ C₁ * (p.ν ^ k)⁻¹ :=
    poly_nu_mono hC₁.le le_rfl hνpos hν_le1 (le_max_left k₁ k₂)
  have hle2 : C₂ * (p.ν ^ k₂)⁻¹ ≤ C₂ * (p.ν ^ k)⁻¹ :=
    poly_nu_mono hC₂.le le_rfl hνpos hν_le1 (le_max_right k₁ k₂)
  have hnorm_le : hNorm p.c bgp (flatColumn p i) ≤ ENNReal.ofReal (C * (p.ν ^ k)⁻¹) := by
    calc hNorm p.c bgp (flatColumn p i)
        ≤ ENNReal.ofReal (C₁ * (p.ν ^ k₁)⁻¹) + ENNReal.ofReal (C₂ * (p.ν ^ k₂)⁻¹) :=
          htri.trans (add_le_add hb1 hb2)
      _ = ENNReal.ofReal (C₁ * (p.ν ^ k₁)⁻¹ + C₂ * (p.ν ^ k₂)⁻¹) :=
          (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      _ ≤ ENNReal.ofReal (C * (p.ν ^ k)⁻¹) := by
          refine ENNReal.ofReal_le_ofReal ?_
          show C₁ * (p.ν ^ k₁)⁻¹ + C₂ * (p.ν ^ k₂)⁻¹ ≤ (C₁ + C₂) * (p.ν ^ k)⁻¹
          linarith
  exact ⟨⟨hper, hmeas_flat, lt_of_le_of_lt hnorm_le ENNReal.ofReal_lt_top⟩, hnorm_le⟩

end UnforcedLeray.Short.IIb

end
