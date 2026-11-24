import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_6.Inlet.Lin
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_6.Inlet.Quad
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet
import UnforcedLeray.Short.PartI.Tasks.OverlapHighNorm
import UnforcedLeray.Short.PartI.Tasks.OverlapFluctuationDecay
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanPrimitive
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanDecay
import UnforcedLeray.Short.PartI.Tasks.TrainOverlapProof
import UnforcedLeray.Short.PartI.Tasks.TrainVorticityTail
import UnforcedLeray.Short.PartI.Tasks.TrainStreamTails
import UnforcedLeray.Short.PartI.Tasks.TrainFluctuationDecayProof
import UnforcedLeray.Short.PartI.Tasks.TrainTransverseTailsProof
import UnforcedLeray.Short.PartI.Tasks.TrainFixedBandProof

/-!
# The physical inlet source bound `InletSrcPhys` (`PartIII-b:C/rep/8/2/pres/3/2/6/1`)

Source `the November 2 reference manuscript`
2346-2347, 2370-2392 (`short-bg:affine`: the complete inlet source is `N_v(𝒞_εα)`, `𝒞_ε - 𝒞_0 =
εsr_ε` with `r_ε` smooth at zero, compact in upper age and with polynomial weighted bounds; "the
quadratic inlet source has the same bound with `|α|²`"), 2385-2386 (`-9/8 + p = 13/8 > -1`),
2681-2688 (the Jacobian `πR²s^{-5/2} ds dη`), 2419-2423 (the raw jets, from Part I).

Pointwise, off the axis, both inlet sources are bounded by a ring envelope
`1_{0<s≤H/2} M s^{3/2}(1+|η|)^N e^{-κ|η|/c}` at `s = R²/ϱ²`, `η = Ry₃/ϱ` (no factor `R`):
`Inlet/Lin.lean` (`lin_ptw`, with `M = 2Aν^{-k}|α|`; it uses the raw jet bound
`IIb.RawJetBound`, SP 2419-2423, since the linear source contains `E·∇U_raw + U_raw·∇E`) and
`Inlet/Quad.lean` (`quad_ptw`, `M = B(1+H)ν^{-k}|α|²`, unconditional).  The change of variables
`Inlet/Integral.lean` (`eLpNorm_le_of_ringEnv`) turns an envelope into
`‖·‖_{L^{11/4}} ≤ K M (1+H) c^{N+1} R^{8/11}`; with `H = Σ/ν`, `c = ν^{-2}` all costs are powers of
`ν⁻¹`.

* `inletSrcPhys_of`: `RawJetBound → InletSrcPhys`;
* `inletSrcPhys_of_train`: the same from the Part I statements `TrainTransverseTails`,
  `TrainFixedBand` (`IIb.rawJetBound_of`).

The only non-proved input is the uniform (polynomial in `ν⁻¹`) size of the actual train on the slow
band: `BgRegime` constrains the train only qualitatively (`IsBUCTrain`, bounds depending on the
train), while the constant of `InletSrcPhys` is chosen before the parameters.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`InletSrcPhys` from the raw jet bound** (source 2370-2392, 2681-2688; the raw jets
2419-2423). -/
theorem inletSrcPhys_of (hR : UnforcedLeray.Short.IIb.RawJetBound) : InletSrcPhys := by
  intro Sig lam q hSig hq dm dp hdm
  obtain ⟨A, κ₁, k₁, N, ν₁, hA, hκ₁, hν₁, hν₁1, HL⟩ :=
    ES326Inlet.lin_ptw hR Sig lam q hSig hq dm dp hdm
  obtain ⟨B, κ₂, k₂, ν₂, hB, hκ₂, hν₂, -, HQ⟩ :=
    ES326Inlet.quad_ptw Sig lam q hSig hq dm dp hdm
  obtain ⟨K₁, hK₁, HK₁⟩ := ES326Inlet.eLpNorm_le_of_ringEnv N hκ₁
  obtain ⟨K₂, hK₂, HK₂⟩ := ES326Inlet.eLpNorm_le_of_ringEnv 1 hκ₂
  have hSig0 : 0 ≤ 1 + Sig := by linarith
  refine ⟨2 * K₁ * A * (1 + Sig) + K₂ * B * (1 + Sig) ^ 2, k₁ + 2 * N + 3 + (k₂ + 6),
    min ν₁ ν₂, by positivity, lt_min hν₁ hν₂, ?_⟩
  intro p d hreg hν hS hm α τ
  have hνpos : 0 < p.ν := p.ν_pos
  have hνL : p.ν ≤ ν₁ := hν.trans (min_le_left _ _)
  have hνQ : p.ν ≤ ν₂ := hν.trans (min_le_right _ _)
  have hν1 : p.ν ≤ 1 := hνL.trans hν₁1
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = p.ν⁻¹ := ⟨_, rfl⟩
  have hu1 : 1 ≤ u := by
    rw [hu]
    exact (one_le_inv₀ hνpos).2 hν1
  have hu0 : 0 ≤ u := zero_le_one.trans hu1
  have hpow : ∀ k : ℕ, (p.ν ^ k)⁻¹ = u ^ k := fun k => by rw [hu, inv_pow]
  have hc : p.c = u ^ 2 := by rw [hreg.c_eq, hpow]
  have hc1 : 1 ≤ p.c := by
    rw [hc]
    exact one_le_pow₀ hu1
  have hHpos : 0 < p.H := p.H_pos
  have hH : 1 + p.H ≤ (1 + Sig) * u := by
    have e : p.H = Sig * u := by
      rw [UnforcedLeray.Cons.C03.Concrete.Params.H, hS, hu, div_eq_mul_inv]
    rw [e]
    nlinarith
  have hRpos : 0 < p.R := p.R_pos
  have hRp : 0 ≤ p.R ^ (8 / 11 : ℝ) := Real.rpow_nonneg hRpos.le _
  have ha : 0 ≤ ‖α‖ := norm_nonneg _
  have hC1 : 2 * K₁ * A * (1 + Sig) ≤ 2 * K₁ * A * (1 + Sig) + K₂ * B * (1 + Sig) ^ 2 :=
    le_add_of_nonneg_right (by positivity)
  have hC2 : K₂ * B * (1 + Sig) ^ 2 ≤ 2 * K₁ * A * (1 + Sig) + K₂ * B * (1 + Sig) ^ 2 :=
    le_add_of_nonneg_left (by positivity)
  constructor
  · have hM : 0 ≤ 2 * A * (p.ν ^ k₁)⁻¹ * ‖α‖ := by positivity
    refine (HK₁ p.R p.c p.H _ (inletLinSrc p α τ) hRpos hc1 hHpos hM
      (HL p d hreg hνL hS hm α τ)).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hpow, hpow, hc]
    calc K₁ * (2 * A * u ^ k₁ * ‖α‖) * (1 + p.H) * (u ^ 2) ^ (N + 1) * p.R ^ (8 / 11 : ℝ)
        ≤ K₁ * (2 * A * u ^ k₁ * ‖α‖) * ((1 + Sig) * u) * (u ^ 2) ^ (N + 1) *
            p.R ^ (8 / 11 : ℝ) := by gcongr
      _ = 2 * K₁ * A * (1 + Sig) * u ^ (k₁ + 2 * N + 3) * p.R ^ (8 / 11 : ℝ) * ‖α‖ := by ring
      _ ≤ (2 * K₁ * A * (1 + Sig) + K₂ * B * (1 + Sig) ^ 2) * u ^ (k₁ + 2 * N + 3 + (k₂ + 6)) *
            p.R ^ (8 / 11 : ℝ) * ‖α‖ := by
          gcongr ?_ * ?_ * _ * _
          all_goals first | exact hC1 | exact hC2 | exact pow_le_pow_right₀ hu1 (by omega)
  · have hM : 0 ≤ B * (1 + p.H) * (p.ν ^ k₂)⁻¹ * ‖α‖ ^ 2 := by positivity
    refine (HK₂ p.R p.c p.H _ (inletQuadSrc p α τ) hRpos hc1 hHpos hM
      (HQ p d hreg hνQ hS hm α τ)).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hpow, hpow, hc]
    have hH0 : 0 ≤ 1 + p.H := by linarith
    calc K₂ * (B * (1 + p.H) * u ^ k₂ * ‖α‖ ^ 2) * (1 + p.H) * (u ^ 2) ^ (1 + 1) *
          p.R ^ (8 / 11 : ℝ)
        ≤ K₂ * (B * ((1 + Sig) * u) * u ^ k₂ * ‖α‖ ^ 2) * ((1 + Sig) * u) * (u ^ 2) ^ (1 + 1) *
            p.R ^ (8 / 11 : ℝ) := by gcongr
      _ = K₂ * B * (1 + Sig) ^ 2 * u ^ (k₂ + 6) * p.R ^ (8 / 11 : ℝ) * ‖α‖ ^ 2 := by ring
      _ ≤ (2 * K₁ * A * (1 + Sig) + K₂ * B * (1 + Sig) ^ 2) * u ^ (k₁ + 2 * N + 3 + (k₂ + 6)) *
            p.R ^ (8 / 11 : ℝ) * ‖α‖ ^ 2 := by
          gcongr ?_ * ?_ * _ * _
          all_goals first | exact hC1 | exact hC2 | exact pow_le_pow_right₀ hu1 (by omega)

/-- **`InletSrcPhys` from the Part I train statements** `sct:transverse`, `sct:fixed-band`
(through `IIb.rawJetBound_of`, SP 2419-2423). -/
theorem inletSrcPhys_of_train (hT : UnforcedLeray.Short.PartI.TrainTransverseTails)
    (hF : UnforcedLeray.Short.PartI.TrainFixedBand) : InletSrcPhys :=
  inletSrcPhys_of (UnforcedLeray.Short.IIb.rawJetBound_of hT hF)

/-- **Physical inlet source bound** (`PartIII-b:C/rep/8/2/pres/3/2/6/1`, source 2370-2392,
2419-2423, 2681-2688): unconditional assembly of `InletSrcPhys` from `inletSrcPhys_of_train` and
the Part I train tail / fixed-band theorems (`PartI:T24`, `PartI:T25`). -/
theorem inletSrcPhys : InletSrcPhys := by
  have hHN : UnforcedLeray.Short.PartI.OverlapHighNormUniform :=
    UnforcedLeray.Short.PartI.overlap_highnorm_uniform
  have hOFD : UnforcedLeray.Short.PartI.OverlapFluctuationDecay :=
    UnforcedLeray.Short.PartI.overlap_fluctuation_decay hHN
  have hMP : UnforcedLeray.Short.PartI.OverlapMeanPrimitive :=
    UnforcedLeray.Short.PartI.overlap_mean_primitive
  have hMD : UnforcedLeray.Short.PartI.OverlapMeanDecay :=
    UnforcedLeray.Short.PartI.overlap_mean_decay hHN hOFD hMP
  have hOv : UnforcedLeray.Short.PartI.TrainOverlap :=
    UnforcedLeray.Short.PartI.trainOverlap_proof hOFD hMD
  have hVort : UnforcedLeray.Short.PartI.TrainVorticityGaussianTail :=
    UnforcedLeray.Short.PartI.train_vorticity_gaussian_tail hOv
  have hTails : UnforcedLeray.Short.PartI.TrainStreamVelocityPressureTails :=
    UnforcedLeray.Short.PartI.train_stream_velocity_pressure_tails hOv hVort
  have hFD : UnforcedLeray.Short.PartI.TrainFluctuationDecay :=
    UnforcedLeray.Short.PartI.trainFluctuationDecay_proof hTails hOFD hOv
  exact inletSrcPhys_of_train
    (UnforcedLeray.Short.PartI.trainTransverseTails_proof hVort hTails)
    (UnforcedLeray.Short.PartI.trainFixedBand_proof hTails hFD)

end UnforcedLeray.Short.PartIIIb.Concrete

