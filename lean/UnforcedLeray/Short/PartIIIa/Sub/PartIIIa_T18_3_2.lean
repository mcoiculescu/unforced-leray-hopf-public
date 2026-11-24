import UnforcedLeray.Short.PartIIIa.Sub.T18_3
import UnforcedLeray.Short.PartIIIa.FlatCausalMeas

/-!
# `PartIII-a:T18/3/2` (decomposition): `FreeEnergyInequalities` from the weighted energy identity

Source: `the November 2 reference manuscript` lines 3541-3552 (the energy identity
tested with the cutoff, Young's inequality, `δ ↓ 0`, `B ↑ ∞`) and 3427-3440 (zero entrance).

Reduction: the slice integrals `A = ∫_cell |g⁻¹b|²`, `N = ∫_cell |g⁻¹G|²`, `Q = ∫_cell |g⁻¹F|²`,
`M = ∫_cell |g⁻¹F||g⁻¹G|` are real functions of the age `s`; `WeightedEnergyIdentity` becomes a
scalar inequality for every `C¹` cutoff `ψ`, and `CutoffLimit` (scalar real analysis) removes the
cutoff.  The remaining Props identify the cell/age norms with the slice integrals.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The slice integral `s ↦ ∫_{cell c} g(s, x) dx`. -/
def sliceSq (c : ℝ) (g : ℝ × (ℝ × ℝ) → ℝ) (s : ℝ) : ℝ := ∫ x in B0579.cell c, g (s, x)

/-- **Ramp family** (L2). A fixed `C`: for `0 < δ`, `2δ < B` a `C¹` cutoff `ψ ∈ [0,1]`, compactly
supported in `(0,∞)`, `ψ = 1` on `[2δ, B]`, with `ψ' ≤ (C/δ)·1_{[δ,2δ]}` (so `ψ' ≤ 0` elsewhere).
Sketch: `ψ(s) = σ((s-δ)/δ)·σ((2B-s)/B)` with `σ = Real.smoothTransition` (`C^∞`, monotone, `0`
on `(-∞,0]`, `1` on `[1,∞)`); `C = sup σ'` (continuous on `[0,1]`); `ψ' ≤ 0` on `[B,2B]`. -/
def RampFamily : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ δ B : ℝ, 0 < δ → 2 * δ < B → ∃ ψ : ℝ → ℝ,
    ContDiff ℝ 1 ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ Ioi 0 ∧ (∀ s, 0 ≤ ψ s ∧ ψ s ≤ 1) ∧
    (∀ s ∈ Icc (2 * δ) B, ψ s = 1) ∧
    ∀ s, deriv ψ s ≤ C / δ * (Icc δ (2 * δ)).indicator (fun _ => (1 : ℝ)) s

/-- **Cutoff limit** (scalar; SP 3541-3552). `A, N, Q ≥ 0` measurable and locally integrable on
`(0,∞)`, `M ≥ 0` with a.e. `2M ≤ θN + Q/θ` (Young), `α ≥ 2k`, zero entrance
`∫_0^δ s^{-3/2}A < ∞`, and the weighted inequality for every `C¹` cutoff; then
`2k ∫ s^{-3/2}A + (2ν-θ) ∫ s^{-1/2}N ≤ θ⁻¹ ∫ s^{-1/2}Q` in `[0,∞]`.
Proof from `RampFamily` with `ψ_n = ψ_{1/n, n+1}`: absorb Young at each `ψ` (everything finite on
the compact support of `ψ`, `integral_mono_of_nonneg` for `M`), drop `ψ' ≤ 0` outside `[δ,2δ]`,
`∫ψ' s^{-1/2}A ≤ (C/δ)∫_δ^{2δ}s^{-1/2}A ≤ 2C∫_0^{2δ}s^{-3/2}A → 0` (`s^{-1/2} ≤ 2δ s^{-3/2}`,
`tendsto_setLIntegral_zero`), and Fatou (`lintegral_liminf_le`) with `ψ_n → 1` on `(0,∞)`;
`ψ ≤ 1` bounds the `Q` term. -/
def CutoffLimit : Prop :=
  ∀ (k ν α θ : ℝ) (A N M Q : ℝ → ℝ), 0 < k → 0 < ν → 0 < θ → θ ≤ 2 * ν → 2 * k ≤ α →
    (∀ s, 0 ≤ A s ∧ 0 ≤ N s ∧ 0 ≤ M s ∧ 0 ≤ Q s) →
    Measurable A → Measurable N → Measurable Q →
    (∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      IntegrableOn A (Icc s₁ s₂) ∧ IntegrableOn N (Icc s₁ s₂) ∧ IntegrableOn Q (Icc s₁ s₂)) →
    (∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), 2 * M s ≤ θ * N s + θ⁻¹ * Q s) →
    (∃ δ : ℝ, 0 < δ ∧
      ∫⁻ s in Ioo 0 δ, ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s) < ⊤) →
    (∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ioi 0 → (∀ s, 0 ≤ ψ s) →
      (∫ s in Ioi (0 : ℝ), ψ s * (α * s ^ (-3 / 2 : ℝ) * A s + 2 * ν * s ^ (-1 / 2 : ℝ) * N s))
        ≤ (∫ s in Ioi (0 : ℝ), deriv ψ s * (s ^ (-1 / 2 : ℝ) * A s)) +
          2 * ∫ s in Ioi (0 : ℝ), ψ s * s ^ (-1 / 2 : ℝ) * M s) →
    ENNReal.ofReal (2 * k) * (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s)) +
        ENNReal.ofReal (2 * ν - θ) * ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * N s)
      ≤ ENNReal.ofReal θ⁻¹ * ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * Q s)

/-- **Slice integrals** (Tonelli on the cell). For `c > 0` and measurable `g ≥ 0` with finite
`∫⁻` over every `[s₁,s₂] × cell` (`0 < s₁`): the slice integral `s ↦ ∫_cell g(s,·)` is measurable
(`StronglyMeasurable.integral_prod_right`), integrable on every `[s₁,s₂]` (Fubini/Tonelli,
`integrable_prod_iff`), and a.e. `s > 0` the slice `g(s,·)` is integrable on the cell. -/
def SliceLoc : Prop :=
  ∀ (c : ℝ) (g : ℝ × (ℝ × ℝ) → ℝ), 0 < c → Measurable g → (∀ p, 0 ≤ g p) →
    (∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (g p) < ⊤) →
    Measurable (sliceSq c g) ∧
    (∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ → IntegrableOn (sliceSq c g) (Icc s₁ s₂)) ∧
    ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), IntegrableOn (fun x => g (s, x)) (B0579.cell c)

/-- The `𝓗`, `𝒯` norms squared as `∫⁻` against the age measures (`eLpNorm_eq_lintegral_rpow_enorm`,
`enorm` of a nonnegative real is `ofReal`). -/
def NormSq : Prop :=
  (∀ (c : ℝ) (f : ℝ × (ℝ × ℝ) → Fin 2 → ℂ),
    hCalNorm c f ^ 2 = ∫⁻ p, ENNReal.ofReal (vnorm2 (f p) ^ 2) ∂(ageμ c (-3 / 2))) ∧
  (∀ (c : ℝ) (T : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ),
    tCalNorm c T ^ 2 = ∫⁻ p, ENNReal.ofReal (tnorm2 (T p) ^ 2) ∂(ageμ c (-1 / 2)))

/-- **Age measure = slice integrals** (`Axi.lintegral_ageμ`, Tonelli, `SliceLoc` a.e. integrability,
`ofReal_integral_eq_lintegral_ofReal`; note `qCell c = Ico (-c/2) (c/2) ×ˢ univ` against
`B0579.cell c = Ico (-(c/2)) (c/2) ×ˢ univ`). For `c > 0`, measurable `g ≥ 0` locally finite on
`(0,∞)`: `∫ g dageμ c a = c⁻¹ ∫_0^∞ s^a ∫_cell g`, and the same restricted to `s ∈ (0,δ)`. -/
def AgeSlice : Prop :=
  ∀ (c a : ℝ) (g : ℝ × (ℝ × ℝ) → ℝ), 0 < c → Measurable g → (∀ p, 0 ≤ g p) →
    (∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (g p) < ⊤) →
    (∫⁻ p, ENNReal.ofReal (g p) ∂(ageμ c a) =
      ENNReal.ofReal c⁻¹ * ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ a * sliceSq c g s)) ∧
    ∀ δ : ℝ, ∫⁻ p, ENNReal.ofReal (g p) ∂((ageμ c a).restrict (Ioo 0 δ ×ˢ univ)) =
      ENNReal.ofReal c⁻¹ * ∫⁻ s in Ioo 0 δ, ENNReal.ofReal (s ^ a * sliceSq c g s)

/-- **Young on slices.** `F, G` measurable tensor fields with `tnorm2²` locally finite; then for
`θ > 0` and a.e. `s > 0`: `2∫_cell |F||G| ≤ θ∫_cell |G|² + θ⁻¹∫_cell |F|²`. Proof: a.e. slice
integrability (`SliceLoc`), pointwise `2xy ≤ θx² + y²/θ`, `integral_mono_of_nonneg`. -/
def YoungSlice : Prop :=
  ∀ (c : ℝ) (F G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ), 0 < c →
    (∀ i j, Measurable fun p => F p i j) → (∀ i j, Measurable fun p => G p i j) →
    (∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (tnorm2 (F p) ^ 2) < ⊤) →
    (∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (tnorm2 (G p) ^ 2) < ⊤) →
    ∀ θ : ℝ, 0 < θ → ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      2 * sliceSq c (fun p => tnorm2 (F p) * tnorm2 (G p)) s ≤
        θ * sliceSq c (fun p => tnorm2 (G p) ^ 2) s + θ⁻¹ * sliceSq c (fun p => tnorm2 (F p) ^ 2) s

/-- **Gain conjugation of `(b, G)` stays locally `L²`.** For `γ ≥ 0`, `ν > 0`, `s > 0`:
`1 ≤ g(s) = exp(γs/(1+νs))`, so `|g⁻¹ f| ≤ |f|` (`vnorm2`/`tnorm2` are homogeneous under real
scalars); `lintegral_mono`. -/
def GainLocBG : Prop :=
  ∀ (c ν γ : ℝ), 0 ≤ γ → 0 < ν → ∀ (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ),
    (∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
        ENNReal.ofReal (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) < ⊤) →
    ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      (∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
        ENNReal.ofReal (vnorm2 (gainConj γ ν b p) ^ 2) < ⊤) ∧
      (∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
        ENNReal.ofReal (tnorm2 (gainConj γ ν G p) ^ 2) < ⊤)

/-- **`F ∈ L²_loc` from `‖g⁻¹F‖_𝒯 < ∞`.** For `c > 0`, `γ ≥ 0`, `ν > 0`: `tCalNorm c (g⁻¹F) < ⊤`
gives finite `∫⁻` of `tnorm2(g⁻¹F)²` and of `tnorm2(F)²` over `[s₁,s₂] × cell` (`0 < s₁`).
Proof: `NormSq` + `lintegral_ageμ` give `∫⁻_{(0,∞)×cell} s^{-1/2} tnorm2(g⁻¹F)² < ⊤`; on
`[s₁,s₂]` the weight `s^{-1/2} ≥ s₂^{-1/2}`; and `1 ≤ g ≤ exp(γ/ν)` (`γ s/(1+νs) ≤ γ/ν`). -/
def GainLocF : Prop :=
  ∀ (c ν γ : ℝ), 0 < c → 0 ≤ γ → 0 < ν → ∀ (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ),
    (∀ i j, Measurable fun p => F p i j) →
    tCalNorm c (gainConj γ ν F) < ⊤ →
    ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      (∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (tnorm2 (F p) ^ 2) < ⊤) ∧
      (∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
        ENNReal.ofReal (tnorm2 (gainConj γ ν F p) ^ 2) < ⊤)


/-! ## Measurability helpers -/

theorem measurable_gainG (γ ν : ℝ) : Measurable fun p : ℝ × (ℝ × ℝ) => gainG γ ν p.1 := by
  unfold gainG; fun_prop

-- `measurable_gainConj_vec` (implicit `γ ν`) and `measurable_tnorm2` are in `FlatCausalMeas.lean`.

theorem measurable_gainConj_ten (γ ν : ℝ) {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hF : ∀ i j, Measurable fun p => F p i j) (i j : Fin 2) :
    Measurable fun p => gainConj γ ν F p i j := by
  have := (measurable_gainG γ ν).inv.smul (hF i j)
  exact this

theorem measurable_vnorm2_sq {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} (hb : ∀ i, Measurable fun p => b p i) :
    Measurable fun p => vnorm2 (b p) ^ 2 := by
  unfold vnorm2
  have : Measurable fun p => ∑ i : Fin 2, ‖b p i‖ ^ 2 :=
    Finset.measurable_sum _ fun i _ => (measurable_norm.comp (hb i)).pow_const 2
  exact (Real.continuous_sqrt.measurable.comp this).pow_const 2

theorem sliceSq_nonneg {c : ℝ} {g : ℝ × (ℝ × ℝ) → ℝ} (hg : ∀ p, 0 ≤ g p) (s : ℝ) :
    0 ≤ sliceSq c g s :=
  integral_nonneg fun x => hg (s, x)

theorem gainG_inv_le_one {γ ν s : ℝ} (hγ : 0 ≤ γ) (hν : 0 < ν) (hs : 0 < s) :
    (gainG γ ν s)⁻¹ ≤ 1 := by
  have h1 : 1 ≤ gainG γ ν s := by
    unfold gainG
    apply Real.one_le_exp
    positivity
  exact inv_le_one_of_one_le₀ h1

theorem vnorm2_smul_le {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1) (a : Fin 2 → ℂ) :
    vnorm2 (r • a) ≤ vnorm2 a := by
  unfold vnorm2
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  have : ‖(r • a) i‖ ≤ ‖a i‖ := by
    simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr0]
    exact mul_le_of_le_one_left (norm_nonneg _) hr
  exact pow_le_pow_left₀ (norm_nonneg _) this 2

theorem tnorm2_smul_le {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1) (a : Fin 2 → Fin 2 → ℂ) :
    tnorm2 (r • a) ≤ tnorm2 a := by
  unfold tnorm2
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have : ‖(r • a) i j‖ ≤ ‖a i j‖ := by
    simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr0]
    exact mul_le_of_le_one_left (norm_nonneg _) hr
  exact pow_le_pow_left₀ (norm_nonneg _) this 2

/-- **`FreeEnergyInequalities` from the scalar lemmas.** -/
theorem freeEnergyInequalities_of (hCL : CutoffLimit) (hSL : SliceLoc) (hNS : NormSq)
    (hAS : AgeSlice) (hY : YoungSlice) (hGB : GainLocBG) (hGF : GainLocF)
    (hW : WeightedEnergyIdentity) : FreeEnergyInequalities := by
  intro P hP K hK
  refine ⟨1, one_pos, ?_⟩
  intro ν hν μ hμ F _hs hFm hF b G hsol
  have hν0 : 0 < ν := hν.1
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν0 _
  set c : ℝ := ν ^ (-2 : ℝ) with hcdef
  have hγ : 0 ≤ P.eigenvalue.re := hP.eigenpair.re_pos.le
  set γ : ℝ := P.eigenvalue.re with hγdef
  have hk1 : (1 / 4 : ℝ) ≤ ⨅ μ' : K, μ'.1.re + 1 / 4 := kStar_ge hμ (fun μ' h => (hK.2 μ' h).1)
  have hkμ : (⨅ μ' : K, μ'.1.re + 1 / 4) ≤ μ.re + 1 / 4 := by
    refine ciInf_le (f := fun μ' : K => μ'.1.re + 1 / 4) ⟨1 / 4, ?_⟩ ⟨μ, hμ⟩
    rintro _ ⟨μ', rfl⟩
    have := (hK.2 μ'.1 μ'.2).1
    linarith
  set k : ℝ := ⨅ μ' : K, μ'.1.re + 1 / 4 with hkdef
  have hkpos : 0 < k := by linarith
  -- local finiteness
  have hBG := hGB c ν γ hγ hν0 b G hsol.energyLoc
  have hFl := hGF c ν γ hc hγ hν0 F hFm hF
  -- measurability of conjugated fields
  have hbm : ∀ i, Measurable fun p => b p i := hsol.measurable
  have hGm : ∀ i j, Measurable fun p => G p i j := hsol.gradMeasurable
  have hbm' := measurable_gainConj_vec (γ := γ) (ν := ν) hbm
  have hGm' := measurable_gainConj_ten γ ν hGm
  have hFm' := measurable_gainConj_ten γ ν hFm
  -- the four nonnegative integrands
  set gV : ℝ × (ℝ × ℝ) → ℝ := fun p => vnorm2 (gainConj γ ν b p) ^ 2 with hgV
  set gN : ℝ × (ℝ × ℝ) → ℝ := fun p => tnorm2 (gainConj γ ν G p) ^ 2 with hgN
  set gQ : ℝ × (ℝ × ℝ) → ℝ := fun p => tnorm2 (gainConj γ ν F p) ^ 2 with hgQ
  have hgVm : Measurable gV := measurable_vnorm2_sq hbm'
  have hgNm : Measurable gN := (measurable_tnorm2 hGm').pow_const 2
  have hgQm : Measurable gQ := (measurable_tnorm2 hFm').pow_const 2
  have hgV0 : ∀ p, 0 ≤ gV p := fun p => sq_nonneg _
  have hgN0 : ∀ p, 0 ≤ gN p := fun p => sq_nonneg _
  have hgQ0 : ∀ p, 0 ≤ gQ p := fun p => sq_nonneg _
  obtain ⟨hVm, hVi, -⟩ := hSL c gV hc hgVm hgV0 fun s₁ s₂ h1 h2 => (hBG s₁ s₂ h1 h2).1
  obtain ⟨hNm, hNi, -⟩ := hSL c gN hc hgNm hgN0 fun s₁ s₂ h1 h2 => (hBG s₁ s₂ h1 h2).2
  obtain ⟨hQm, hQi, -⟩ := hSL c gQ hc hgQm hgQ0 fun s₁ s₂ h1 h2 => (hFl s₁ s₂ h1 h2).2
  -- weighted identity
  have hWEI := hW c ν γ μ hc hν0 hγ F b G (fun s₁ s₂ h1 h2 => (hFl s₁ s₂ h1 h2).1) hFm hsol
  -- zero entrance
  have hZ : ∃ δ : ℝ, 0 < δ ∧
      ∫⁻ s in Ioo 0 δ, ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * sliceSq c gV s) < ⊤ := by
    obtain ⟨δ, hδ, hfin⟩ := hsol.zeroEntrance
    refine ⟨δ, hδ, ?_⟩
    obtain ⟨-, h2⟩ := hAS c (-3 / 2) gV hc hgVm hgV0 fun s₁ s₂ h1 h2 => (hBG s₁ s₂ h1 h2).1
    have hle : ∫⁻ p, ENNReal.ofReal (gV p)
        ∂((ageμ c (-3 / 2)).restrict (Ioo 0 δ ×ˢ univ)) ≤
        ∫⁻ p, ENNReal.ofReal (vnorm2 (b p) ^ 2)
        ∂((ageμ c (-3 / 2)).restrict (Ioo 0 δ ×ˢ univ)) := by
      refine lintegral_mono_ae ?_
      have hm : MeasurableSet (Ioo (0 : ℝ) δ ×ˢ (univ : Set (ℝ × ℝ))) :=
        measurableSet_Ioo.prod MeasurableSet.univ
      filter_upwards [ae_restrict_mem hm] with p hp
      have hp1 : 0 < p.1 := hp.1.1
      apply ENNReal.ofReal_le_ofReal
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _)
        (vnorm2_smul_le (inv_nonneg.2 (Real.exp_pos _).le) (gainG_inv_le_one hγ hν0 hp1) _) 2
    have := (hle.trans_lt hfin)
    rw [h2 δ] at this
    have hc' : ENNReal.ofReal c⁻¹ ≠ 0 := by
      simpa using inv_pos.2 hc
    rcases ENNReal.mul_lt_top_iff.1 this with h | h | h
    · exact h.2
    · exact absurd h hc'
    · simp [h]
  have hbase := fun (θ : ℝ) (hθ : 0 < θ) (hθ2 : θ ≤ 2 * ν) =>
    hCL k ν (1 / 2 + 2 * μ.re) θ (sliceSq c gV) (sliceSq c gN)
      (sliceSq c (fun p => tnorm2 (gainConj γ ν F p) * tnorm2 (gainConj γ ν G p)))
      (sliceSq c gQ) hkpos hν0 hθ hθ2 (by linarith [hk1, hkμ])
      (fun s => ⟨sliceSq_nonneg hgV0 s, sliceSq_nonneg hgN0 s,
        sliceSq_nonneg (fun p => mul_nonneg (by unfold tnorm2; positivity)
          (by unfold tnorm2; positivity)) s, sliceSq_nonneg hgQ0 s⟩)
      hVm hNm hQm
      (fun s₁ s₂ h1 h2 => ⟨hVi s₁ s₂ h1 h2, hNi s₁ s₂ h1 h2, hQi s₁ s₂ h1 h2⟩)
      (hY c _ _ hc hFm' hGm' (fun s₁ s₂ h1 h2 => (hFl s₁ s₂ h1 h2).2)
        (fun s₁ s₂ h1 h2 => (hBG s₁ s₂ h1 h2).2) θ hθ)
      hZ hWEI
  -- norms as slice integrals
  have eH : hCalNorm c (gainConj γ ν b) ^ 2 = ENNReal.ofReal c⁻¹ *
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * sliceSq c gV s) := by
    rw [hNS.1]
    exact (hAS c (-3 / 2) gV hc hgVm hgV0 fun s₁ s₂ h1 h2 => (hBG s₁ s₂ h1 h2).1).1
  have eN : tCalNorm c (gainConj γ ν G) ^ 2 = ENNReal.ofReal c⁻¹ *
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * sliceSq c gN s) := by
    rw [hNS.2]
    exact (hAS c (-1 / 2) gN hc hgNm hgN0 fun s₁ s₂ h1 h2 => (hBG s₁ s₂ h1 h2).2).1
  have eQ : tCalNorm c (gainConj γ ν F) ^ 2 = ENNReal.ofReal c⁻¹ *
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * sliceSq c gQ s) := by
    rw [hNS.2]
    exact (hAS c (-1 / 2) gQ hc hgQm hgQ0 fun s₁ s₂ h1 h2 => (hFl s₁ s₂ h1 h2).2).1
  rw [eH, eN, eQ]
  constructor
  · have h := hbase ν hν0 (by linarith)
    have h' : 2 * ν - ν = ν := by ring
    rw [h'] at h
    have h2 := mul_le_mul' (le_refl (ENNReal.ofReal c⁻¹)) h
    refine le_trans (le_of_eq ?_) (h2.trans (le_of_eq ?_)) <;> ring
  · have h := hbase (2 * ν) (by linarith) le_rfl
    simp only [sub_self, ENNReal.ofReal_zero, zero_mul, add_zero] at h
    have h2 := mul_le_mul' (le_refl (ENNReal.ofReal c⁻¹)) h
    refine le_trans (le_of_eq ?_) (h2.trans (le_of_eq ?_)) <;> ring

end UnforcedLeray.Short.IIIa
