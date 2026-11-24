import UnforcedLeray.Short.PartIIIa.Clock.Moving

/-!
# Part III-a, task `PartIII-a:T21/c2` (`FreeMovingEnergy`): decomposition

Source of record: `the November 2 reference manuscript`, lines 2937-2958
(`eq:short-causal-free-moving`; the Reynolds boundary term cancels the dilation seam term and
`d/dz ‖W‖_p² ≤ [θ⁻¹ sup(Δp/p + 3 - ½ y·∇log p) + δ_ν] ‖W‖_p²`, `p = (1+|y|²)^m`, `C_m = (m²+3m+3)/2`).

Three leaves:
* `FmeScale`: the change of variables `J_a⁻¹` turns the moving norm on the cell of length `c/√a` into
  `a^{3/2}` times the energy of `g` on the cell of length `c` with the dilating weight
  `(1 + |x|²/a)^m` (`x = √a y`, `dy = dx/a`, `a⁴/a = a³`).
* `FmeRate`: the genuinely new analytic content (dilation drift, SP 2943-2952): the energy
  `𝓔(σ) = a(σ)³ ∫_{C_c} ω(σ)² (1+|x|²/a(σ))^m dx` of the free flow is continuous, has a right
  derivative with `𝓔' ≤ 2 (C_m/b + ε) a⁻² 𝓔` on `[t, s]` when `b ≤ θ(s)`.
* `FmeGronwall`: a real-variable Gronwall lemma for a right derivative.

`freeMovingEnergy_of` proves `FreeMovingEnergy` from the three (`z' = a⁻²`, so
`∫_t^s 2k a⁻² = 2k (z_s - z_t)`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- The energy of `g` on the cell of length `c` with the dilating weight `(1 + |x|²/a)^m`. -/
def movEnergy (c m a : ℝ) (g : ℝ × ℝ → ℝ) : ℝ :=
  ∫ x in B0579.cell c, g x ^ 2 * (1 + (x.1 ^ 2 + x.2 ^ 2) / a) ^ m

/-- The moving energy along a flow: `𝓔(σ) = a(σ)³ movEnergy c m a(σ) (ω σ)`. -/
def movFlowEnergy (ν c m : ℝ) (ω : ℝ → ℝ × ℝ → ℝ) (σ : ℝ) : ℝ :=
  clockA ν σ ^ 3 * movEnergy c m (clockA ν σ) (ω σ)

/-- **Leaf `FmeScale`** (SP 2861, change of variables `x = √a y`): for `0 < c`, `0 < a` and `g`
with finite dilated-weight energy on the cell,
`‖J_a⁻¹ g‖_{X_{m, c/√a}} = √(a³ · movEnergy c m a g)`. Proof: `eLpNorm` for `p = 2` as
`(∫⁻ ‖·‖₊²)^{1/2}`, `lintegral_withDensity_eq_lintegral_mul`, the scaling of Lebesgue measure on the
plane by `√a` (`Measure.addHaar_preimage_smul`/`lintegral_comp`-type rule, `Real.sqrt` and
`cell (c/√a)` mapped to `cell c`), and `ofReal_integral_eq_lintegral_ofReal`. -/
def FmeScale : Prop :=
  ∀ c m a : ℝ, 0 < c → 0 < a → ∀ g : ℝ × ℝ → ℝ,
    IntegrableOn (fun x : ℝ × ℝ => g x ^ 2 * (1 + (x.1 ^ 2 + x.2 ^ 2) / a) ^ m) (B0579.cell c) →
      xNorm (cellLen c a) m (JscaleInv a (fun x => ((g x : ℝ) : ℂ))) =
        ENNReal.ofReal (Real.sqrt (a ^ 3 * movEnergy c m a g))

/-- **Leaf `FmeRate`** (SP 2937-2958): the dilated-weight energy rate of the free cylinder flow.
Includes the integrability of the dilated-weight integrands on `[t, s]` and of the datum `f` at
`a(t)`. Proof: PartII-b's `FreeCylEnergy` machinery (`CylClassicalExists`, `CylWeakEqClassical`,
`RegularEnergyDeriv`, `CylDiffusionBound`, `CylTransportIBP`, `CylTrainGap` in
`PartII-b/Sub/T22.lean`) with the weight `p(x/√a(σ))` whose `σ`-derivative adds the dilation term
`-(a'/2a) x·∇p`; weight-bracket bound with `C_m` as in SP 2947-2954; train errors in `δ_ν`.
The train is in the BUC class `PartI.IsBUCTrain` (SP 270-288): the velocity bound on `[t, s]` and
the actual-base velocity error `sup δ_ν → 0` (SP 2955, `sct:comparison`) hold for the source
train, not for an arbitrary `B0140.TrainSol` (`Short/PartI/TrainClass.lean`). -/
def FmeRate : Prop :=
  ∀ m : ℝ, 8 < m → ∀ ε : ℝ, 0 < ε → ∃ b₀ : ℝ, ∀ b : ℝ, b₀ ≤ b → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ ν ∈ Ioc 0 ν₀, ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ t s : ℝ, 0 ≤ t → t ≤ s → b ≤ clockTheta ν s →
        ∀ f : B0579.Plane → ℝ, B0579.IsCylTest (ν ^ (-2 : ℝ)) f →
          ∀ ω : ℝ → B0579.Plane → ℝ, UnforcedLeray.Short.IIb.IsFreeCylFlow m tr t f ω →
            IntegrableOn (fun x : ℝ × ℝ => f x ^ 2 * (1 + (x.1 ^ 2 + x.2 ^ 2) / clockA ν t) ^ m)
                (B0579.cell (ν ^ (-2 : ℝ))) ∧
            (∀ σ ∈ Icc t s, IntegrableOn
                (fun x : ℝ × ℝ => ω σ x ^ 2 * (1 + (x.1 ^ 2 + x.2 ^ 2) / clockA ν σ) ^ m)
                (B0579.cell (ν ^ (-2 : ℝ)))) ∧
            ContinuousOn (movFlowEnergy ν (ν ^ (-2 : ℝ)) m ω) (Icc t s) ∧
            ∃ E' : ℝ → ℝ, ∀ τ ∈ Ico t s,
              HasDerivWithinAt (movFlowEnergy ν (ν ^ (-2 : ℝ)) m ω) (E' τ) (Ici τ) τ ∧
                E' τ ≤ 2 * ((normGrowthConst m / b + ε) / clockA ν τ ^ 2) *
                  movFlowEnergy ν (ν ^ (-2 : ℝ)) m ω τ

/-- **Leaf `FmeGronwall`**: Gronwall for a continuous function with a right derivative:
if `𝓔` is continuous on `[t, s]`, has right derivative `𝓔' τ ≤ κ τ · 𝓔 τ` on `[t, s)` and `κ` is
continuous on `[t, s]`, then `𝓔 s ≤ 𝓔 t · exp(∫_t^s κ)`. Proof: `h(σ) = 𝓔(σ) exp(-∫_t^σ κ)` is
continuous with right derivative `≤ 0` on `[t, s)`, hence antitone (right-derivative monotonicity,
e.g. `image_le_of_liminf_slope_right_lt_deriv_boundary'` or a closed-form argument). -/
def FmeGronwall : Prop :=
  ∀ (t s : ℝ) (𝓔 𝓔' κ : ℝ → ℝ), t ≤ s → ContinuousOn 𝓔 (Icc t s) → ContinuousOn κ (Icc t s) →
    (∀ τ ∈ Ico t s, HasDerivWithinAt 𝓔 (𝓔' τ) (Ici τ) τ ∧ 𝓔' τ ≤ κ τ * 𝓔 τ) →
      𝓔 s ≤ 𝓔 t * Real.exp (∫ τ in t..s, κ τ)

theorem freeMovingEnergy_of (hS : FmeScale) (hR : FmeRate) (hG : FmeGronwall) :
    FreeMovingEnergy := by
  intro m hm ε hε
  obtain ⟨b₀, hb⟩ := hR m hm ε hε
  refine ⟨b₀, fun b hb0 => ?_⟩
  obtain ⟨ν₀, hν₀, H⟩ := hb b hb0
  refine ⟨ν₀, hν₀, fun ν hν tr htr t s ht hts hθ f hf ω hω => ?_⟩
  obtain ⟨hfi, hωi, hcont, E', hE⟩ := H ν hν tr htr t s ht hts hθ f hf ω hω
  have hν0 : 0 < ν := hν.1
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν0 _
  have hapos : ∀ σ, 0 ≤ σ → 0 < clockA ν σ := fun σ hσ => by
    unfold clockA; positivity
  set k : ℝ := normGrowthConst m / b + ε with hk
  set 𝓔 := movFlowEnergy ν (ν ^ (-2 : ℝ)) m ω with h𝓔
  have hκ : ContinuousOn (fun σ => 2 * k / clockA ν σ ^ 2) (Icc t s) := by
    refine continuousOn_const.div ?_ ?_
    · unfold clockA; fun_prop
    · intro σ hσ; exact pow_ne_zero _ (hapos σ (ht.trans hσ.1)).ne'
  have hgr := hG t s 𝓔 E' (fun σ => 2 * k / clockA ν σ ^ 2) hts hcont hκ (fun τ hτ => by
    refine ⟨(hE τ hτ).1, le_of_le_of_eq (hE τ hτ).2 ?_⟩
    ring)
  have hint : ∫ τ in t..s, 2 * k / clockA ν τ ^ 2 = 2 * k * (movingZ ν s - movingZ ν t) := by
    have hd : ∀ τ ∈ uIcc t s, HasDerivAt (fun τ => 2 * k * (τ / (1 + ν * τ)))
        (2 * k / clockA ν τ ^ 2) τ := by
      intro τ hτ
      rw [uIcc_of_le hts] at hτ
      have h0 : (1 + ν * τ) ≠ 0 := (hapos τ (ht.trans hτ.1)).ne'
      have h1 : HasDerivAt (fun τ : ℝ => 1 + ν * τ) ν τ := by
        simpa using ((hasDerivAt_id τ).const_mul ν).const_add 1
      have h2 := ((hasDerivAt_id τ).div h1 h0).const_mul (2 * k)
      refine h2.congr_deriv ?_
      unfold clockA
      simp only [id]
      field_simp
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
    · unfold movingZ clockA; ring
    · rw [intervalIntegrable_iff_integrableOn_Icc_of_le hts]
      exact hκ.integrableOn_Icc
  rw [hint] at hgr
  have hns : 0 ≤ 𝓔 t := by
    simp only [h𝓔, movFlowEnergy, movEnergy]
    refine mul_nonneg (pow_nonneg (hapos t ht).le _) (integral_nonneg fun x => ?_)
    refine mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ?_ _)
    have := (hapos t ht).le
    positivity
  have hfs := hS (ν ^ (-2 : ℝ)) m (clockA ν s) hc (hapos s (ht.trans hts)) (ω s)
    (hωi s ⟨hts, le_rfl⟩)
  have hft := hS (ν ^ (-2 : ℝ)) m (clockA ν t) hc (hapos t ht) f hfi
  have hae : movEnergy (ν ^ (-2 : ℝ)) m (clockA ν t) (ω t) =
      movEnergy (ν ^ (-2 : ℝ)) m (clockA ν t) f := by
    unfold movEnergy
    refine integral_congr_ae ?_
    filter_upwards [hω.initial] with x hx
    simp [hx]
  rw [hfs, hft, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : Real.sqrt (clockA ν s ^ 3 * movEnergy (ν ^ (-2 : ℝ)) m (clockA ν s) (ω s)) =
      Real.sqrt (𝓔 s) := rfl
  have h2 : Real.sqrt (clockA ν t ^ 3 * movEnergy (ν ^ (-2 : ℝ)) m (clockA ν t) f) =
      Real.sqrt (𝓔 t) := by
    rw [← hae]; rfl
  rw [h1, h2]
  calc Real.sqrt (𝓔 s) ≤ Real.sqrt (𝓔 t * Real.exp (2 * k * (movingZ ν s - movingZ ν t))) :=
        Real.sqrt_le_sqrt hgr
    _ = Real.sqrt (𝓔 t) * Real.exp (k * (movingZ ν s - movingZ ν t)) := by
        rw [Real.sqrt_mul hns]
        congr 1
        have : Real.exp (2 * k * (movingZ ν s - movingZ ν t)) =
            Real.exp (k * (movingZ ν s - movingZ ν t)) ^ 2 := by
          rw [sq, ← Real.exp_add]; ring_nf
        rw [this, Real.sqrt_sq (Real.exp_pos _).le]
    _ = Real.exp (k * (movingZ ν s - movingZ ν t)) * Real.sqrt (𝓔 t) := mul_comm _ _

end UnforcedLeray.Short.IIIa
