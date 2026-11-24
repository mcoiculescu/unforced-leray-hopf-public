import UnforcedLeray.Short.PartIIIa.Sub.T20
import UnforcedLeray.Cons.L2.SolAudit.LocalModeBridge

/-!
# Part III-a, task `PartIII-a:T20/4`: the library velocity solves Biot-Savart (conditional)

Target (`Sub/T20.lean`): `CTE.VelocityIsBiotSavart`: for `m > 1` and `ω ∈ X_{m,c}` with zero
circulation, `IsBiotSavart c ω (B0583.velocity c ω)`.
Source of record: `the November 2 reference manuscript`, lines 3236-3240 (the
velocity `u = K_c ω`, `K_c = ∇^⊥Δ⁻¹`, is the Biot-Savart velocity: `div u = 0`,
`curl u = ∂_q u_η - ∂_η u_q = ω`) and, for the definition of the library velocity, `B0581`/`B0583`
(`paper/main.tex` 9405-9433).

## Mathematical proof

`B0583.velocity = velNe (nonzeroPart (ofX ω)) + zeroVelLp`, and `B0583.hasWeakVelDeriv_velocity_q`,
`hasWeakVelDeriv_velocity_eta` say that `velGradQ = gradQ (nonzeroPart (ofX ω))` and
`velGradEta = gradEta (nonzeroPart (ofX ω)) + zeroVelEtaLp` are the weak `∂_q`, `∂_η` of the
velocity, componentwise. Testing with a cylinder test function `ψ`:

* `div`: `∫ u₀ ∂_qψ + u₁ ∂_ηψ = -∫ ψ (g_q)₀ - ∫ ψ (g_η)₁`. The zero mode contributes nothing
  (`zeroVelEtaLp = (-ω̄, 0)` has vanishing second component), and for the nonzero modes
  `iκ · bsSym₀ + iζ · bsSym₁ = 0` (leaf `NonzeroDivWeak`).
* `curl`: `∫ u₀ ∂_ηψ - u₁ ∂_qψ = -∫ ψ (g_η)₀ + ∫ ψ (g_q)₁`. For the nonzero modes
  `iκ · bsSym₁ - iζ · bsSym₀ = 1` gives `∫ ψ · nonzeroPart(ofX ω)` (leaf `NonzeroCurlWeak`), and
  the zero mode gives `∫ ψ ω̄` (from `zeroVelEtaLp = (-ω̄, 0)`), where `ω̄ = meanPart (ofX ω)`
  (leaf `MeanPartOfX`); `meanPart + nonzeroPart = ofX ω` and `ofX ω = ω` a.e.
* `L²` components: from `Lp` membership of the `ℂ²`-valued velocity.

Proved here (conditional on the leaves, queued as `PartIII-a:T20/4/1 ... /5`):
* `velocityIsBiotSavart_of_weak`: all of the gluing above from `NonzeroDivWeak`,
  `NonzeroCurlWeak`, `MeanPartOfX`.
* `nonzeroDivWeak_of` (`ModeDiv` => `NonzeroDivWeak`): `inner_synth_right`, `lp.inner_eq_tsum`.
* `nonzeroCurlWeak_of` (`ModeCurl`, `SynthEmbed0` => `NonzeroCurlWeak`): the right side
  `∫ ψ · nonzeroPart W = ⟪ψ e₀, (nonzeroPart W) e₀⟫`, completeness of the scalar modes
  (`Cons.L2.SolAudit.b0581_synth_modes`), `SynthEmbed0`, `inner_synth_right`; mode `0` vanishes on
  both sides.
* `velocityIsBiotSavart_of (hD : ModeDiv) (hC : ModeCurl) (hE : SynthEmbed0) (hM : MeanPartOfX)`.
* The symbol identities `bsSym_div_identity` and `bsSym_curl_identity`.

Leaves: `TestModeFourier` (`/1`, the Fourier shape of the modes of a test field, used by `/2`
and `/3`), `ModeDiv` (`/2`), `ModeCurl` (`/3`), `SynthEmbed0` (`/4`), `MeanPartOfX` (`/5`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology FourierTransform
open scoped ENNReal InnerProductSpace

namespace UnforcedLeray.Short.IIIa

namespace CTE

/-! ## Leaf statements -/

/-- **Divergence of the nonzero-mode velocity, weakly** (`PartIII-a:T20/4/2`; SP 3236-3240).
For every `W ∈ L²(cell; ℂ)` and cylinder test function `ψ`,
`⟪ψ e₀, ∂_q K W⟫ + ⟪ψ e₁, ∂_η K W⟫ = 0` (`gradQ`, `gradEta` of `B0583/Gradient.lean`): modewise
`iκ_k · bsSym₀ + iζ · bsSym₁ = 0` (`κ_k = 2πk/c`, `ζ = 2πξ`, `bsSym κ ζ = (iζ, -iκ)/(κ²+ζ²)`).
True for every `W` (the mean mode is killed by `qModeCLM 0 = etaModeCLM 0 = 0`). -/
def NonzeroDivWeak : Prop :=
  ∀ (c : ℝ) [Fact (0 < c)] (W : Lp ℂ 2 (B0581.cellVol c)) {ψ : B0579.Plane → ℝ}
    (hψ : B0579.IsCylTest c ψ),
    ⟪B0583.testLp c hψ 0, B0583.gradQ c W⟫_ℂ + ⟪B0583.testLp c hψ 1, B0583.gradEta c W⟫_ℂ = 0

/-- **Curl of the nonzero-mode velocity, weakly** (`PartIII-a:T20/4/4`; SP 3236-3240).
For every `W ∈ L²(cell; ℂ)` and cylinder test function `ψ`,
`⟪ψ e₁, ∂_q K W⟫ - ⟪ψ e₀, ∂_η K W⟫ = ∫ ψ · (nonzeroPart W)`: modewise
`iκ_k · bsSym₁ - iζ · bsSym₀ = 1` for `k ≠ 0`, and both sides vanish for `k = 0`. -/
def NonzeroCurlWeak : Prop :=
  ∀ (c : ℝ) [Fact (0 < c)] (W : Lp ℂ 2 (B0581.cellVol c)) {ψ : B0579.Plane → ℝ}
    (hψ : B0579.IsCylTest c ψ),
    ⟪B0583.testLp c hψ 1, B0583.gradQ c W⟫_ℂ - ⟪B0583.testLp c hψ 0, B0583.gradEta c W⟫_ℂ =
      ∫ x, (ψ x : ℂ) * (B0581.nonzeroPart c W : B0579.Plane → ℂ) x ∂(B0581.cellVol c)

/-- **The horizontal mean of `ω ∈ X_{m,c}` is `ω̄`** (`PartIII-a:T20/4/5`; SP 3236-3240): the
`k = 0` part `B0581.meanPart (ofX ω)` equals `ω̄(η) = c⁻¹ ∫_{-c/2}^{c/2} ω(q, η) dq`
(`B0583.omegaBar`) a.e. on the cell. From `B0581.meanPart_ae`
(`meanPart ω =ᵐ modeCoeff c 0 ω x.2`, `modeCoeff_zero`), `coeFn_ofX` and a Fubini-type
a.e. argument on `cellVol c = (μq c).prod volume`. -/
def MeanPartOfX : Prop :=
  ∀ (c : ℝ) [Fact (0 < c)] (m : ℝ) (hm : 0 ≤ m) (ω : B0579.X c m),
    (B0581.meanPart c (B0581.ofX c m hm ω) : B0579.Plane → ℂ) =ᵐ[B0581.cellVol c]
      fun x => ((B0583.omegaBar c ω x.2 : ℝ) : ℂ)

/-- The inclusion `z ↦ z e_j` of `ℂ` into `ℂ²`. -/
def embedJ (j : Fin 2) : ℂ →L[ℂ] B0581.Vel :=
  ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ)
    (EuclideanSpace.single j (1 : ℂ) : B0581.Vel)

theorem embedJ_apply (j : Fin 2) (z : ℂ) :
    embedJ j z = z • (EuclideanSpace.single j (1 : ℂ) : B0581.Vel) := rfl

theorem norm_embedJ (j : Fin 2) (z : ℂ) : ‖embedJ j z‖ = ‖z‖ := by
  simp [embedJ_apply, norm_smul]

/-- The inclusion `z ↦ z e₀` of `ℂ` into `ℂ²`. -/
abbrev embed0 : ℂ →L[ℂ] B0581.Vel := embedJ 0

/-- The inclusion `W ↦ W e₀` of `L²(cell; ℂ)` into `L²(cell; ℂ²)`. -/
def embed0Lp (c : ℝ) : Lp ℂ 2 (B0581.cellVol c) →L[ℂ] Lp B0581.Vel 2 (B0581.cellVol c) :=
  ContinuousLinearMap.compLpL 2 (B0581.cellVol c) embed0

theorem norm_embed0_le (z : ℂ) : ‖embed0 z‖ ≤ 1 * ‖z‖ := by
  rw [norm_embedJ, one_mul]

theorem norm_compLpL_embed0_le (a : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖ContinuousLinearMap.compLpL 2 (volume : Measure ℝ) embed0 a‖ ≤ 1 * ‖a‖ := by
  have h1 : ‖(embed0 : ℂ →L[ℂ] B0581.Vel)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one norm_embed0_le
  have h2 := ContinuousLinearMap.norm_compLpL_le (p := 2) (μ := (volume : Measure ℝ)) embed0
  calc ‖ContinuousLinearMap.compLpL 2 (volume : Measure ℝ) embed0 a‖
      ≤ ‖ContinuousLinearMap.compLpL 2 (volume : Measure ℝ) embed0‖ * ‖a‖ :=
        ContinuousLinearMap.le_opNorm _ a
    _ ≤ 1 * ‖a‖ := by
        gcongr
        exact h2.trans h1

/-- `z ↦ z e₀` on the modes: `(g_k) ↦ (g_k e₀)` (an isometry `ℓ²(ℤ; L²(ℝ; ℂ)) → ℓ²(ℤ; L²(ℝ; ℂ²))`). -/
def embed0Modes : B0581.ModeSeq ℂ →L[ℂ] B0581.ModeSeq B0581.Vel :=
  B0581.diagCLM (fun _ : ℤ => ContinuousLinearMap.compLpL 2 (volume : Measure ℝ) embed0) 1
    zero_le_one (fun _ a => norm_compLpL_embed0_le a)

theorem embed0Modes_apply (g : B0581.ModeSeq ℂ) (k : ℤ) :
    (embed0Modes g : B0581.ModeSeq B0581.Vel) k =
      ContinuousLinearMap.compLpL 2 (volume : Measure ℝ) embed0 (g k) := rfl

/-- **Fourier shape of the modes of a test field** (`PartIII-a:T20/4/1`): for each horizontal
mode `k` there is ONE scalar function `z ∈ L²(ℝ)` with, for both `j = 0, 1`,
`(modes (ψ e_j))_k = z e_j` (physical side) and `𝓕 ((modes (ψ e_j))_k) = (𝓕 z) e_j` a.e.
(Fourier side). (`(modes (ψ e_j))_k` is the Schwartz function `tSchwartz c k hψ j = z(η) e_j`,
`z = √c c⁻¹ sc c k ψ`, `B0583/TestModes.lean`, `modes_testLp`.) -/
def TestModeFourier : Prop :=
  ∀ (c : ℝ) [Fact (0 < c)] (k : ℤ) {ψ : B0579.Plane → ℝ} (hψ : B0579.IsCylTest c ψ),
    ∃ z : Lp ℂ 2 (volume : Measure ℝ),
      (∀ j : Fin 2, (B0581.modes c (B0583.testLp c hψ j) : B0581.ModeSeq B0581.Vel) k =
        ContinuousLinearMap.compLpL 2 (volume : Measure ℝ) (embedJ j) z) ∧
      ∀ j : Fin 2,
        ((𝓕 ((B0581.modes c (B0583.testLp c hψ j) : B0581.ModeSeq B0581.Vel) k) :
            Lp B0581.Vel 2 (volume : Measure ℝ)) : ℝ → B0581.Vel) =ᵐ[volume]
          fun ξ => ((𝓕 z : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ •
            (EuclideanSpace.single j (1 : ℂ) : B0581.Vel)

/-- **Mode `k` of the divergence identity** (`PartIII-a:T20/4/2`): for every `g ∈ L²(ℝ)`,
`⟪(modes (ψ e₀))_k, iκ_k · bsModeCLM_k g⟫ + ⟪(modes (ψ e₁))_k, etaModeCLM_k g⟫ = 0`
(`qModeCLM c k g = iκ_k · 𝓕⁻¹(bsSymbol · 𝓕 g)`, `etaModeCLM c k g = 𝓕⁻¹(2πiξ · bsSymbol · 𝓕 g)`),
because `iκ · bsSym₀ + iζ · bsSym₁ = 0` (`bsSym_div_identity`). -/
def ModeDiv : Prop :=
  ∀ (c : ℝ) [Fact (0 < c)] (k : ℤ) {ψ : B0579.Plane → ℝ} (hψ : B0579.IsCylTest c ψ)
    (g : Lp ℂ 2 (volume : Measure ℝ)),
    ⟪(B0581.modes c (B0583.testLp c hψ 0) : B0581.ModeSeq B0581.Vel) k, B0583.qModeCLM c k g⟫_ℂ +
      ⟪(B0581.modes c (B0583.testLp c hψ 1) : B0581.ModeSeq B0581.Vel) k,
        B0583.etaModeCLM c k g⟫_ℂ = 0

/-- **Mode `k ≠ 0` of the curl identity** (`PartIII-a:T20/4/3`): for every `g ∈ L²(ℝ)`,
`⟪(modes (ψ e₁))_k, qModeCLM_k g⟫ - ⟪(modes (ψ e₀))_k, etaModeCLM_k g⟫ = ⟪(modes (ψ e₀))_k, g e₀⟫`,
because `iκ · bsSym₁ - iζ · bsSym₀ = 1` (`bsSym_curl_identity`, `κ_k ≠ 0` for `k ≠ 0`). -/
def ModeCurl : Prop :=
  ∀ (c : ℝ) [Fact (0 < c)] (k : ℤ), k ≠ 0 → ∀ {ψ : B0579.Plane → ℝ} (hψ : B0579.IsCylTest c ψ)
    (g : Lp ℂ 2 (volume : Measure ℝ)),
    ⟪(B0581.modes c (B0583.testLp c hψ 1) : B0581.ModeSeq B0581.Vel) k, B0583.qModeCLM c k g⟫_ℂ -
      ⟪(B0581.modes c (B0583.testLp c hψ 0) : B0581.ModeSeq B0581.Vel) k,
        B0583.etaModeCLM c k g⟫_ℂ =
      ⟪(B0581.modes c (B0583.testLp c hψ 0) : B0581.ModeSeq B0581.Vel) k,
        ContinuousLinearMap.compLpL 2 (volume : Measure ℝ) embed0 g⟫_ℂ

/-- **Synthesis commutes with the inclusion `z ↦ z e₀`** (`PartIII-a:T20/4/4`): for every mode
sequence `g`, `(∑ₖ (√c)⁻¹ e_k(q) g_k(η)) e₀ = ∑ₖ (√c)⁻¹ e_k(q) (g_k(η) e₀)`. (Both are sums of
`tensorLI c k`; use `B0581.hasSum_synth`, continuity of `embed0Lp c`, and
`embed0Lp c (tensorLI c k g) = tensorLI c k (g e₀)` pointwise, `coeFn_tensorLM`.) -/
def SynthEmbed0 : Prop :=
  ∀ (c : ℝ) [Fact (0 < c)] (g : B0581.ModeSeq ℂ),
    embed0Lp c (B0581.synth c g) = B0581.synth c (embed0Modes g)

/-! ## Algebra of the Biot-Savart symbol -/

/-- `iκ · bsSym₀ + iζ · bsSym₁ = 0` (the divergence of `∇^⊥Δ⁻¹` vanishes). -/
theorem bsSym_div_identity {κ ζ : ℝ} (h : κ ^ 2 + ζ ^ 2 ≠ 0) :
    (Complex.I * (κ : ℂ)) * (B0581.bsSym κ ζ) 0 + (((ζ : ℝ) : ℂ) * Complex.I) * (B0581.bsSym κ ζ) 1
      = 0 := by
  have hD : ((κ : ℂ) ^ 2 + (ζ : ℂ) ^ 2) ≠ 0 := by exact_mod_cast h
  simp only [B0581.bsSym]
  push_cast
  field_simp
  ring

/-- `iκ · bsSym₁ - iζ · bsSym₀ = 1` (the curl of `∇^⊥Δ⁻¹` is the identity). -/
theorem bsSym_curl_identity {κ ζ : ℝ} (h : κ ^ 2 + ζ ^ 2 ≠ 0) :
    (Complex.I * (κ : ℂ)) * (B0581.bsSym κ ζ) 1 - (((ζ : ℝ) : ℂ) * Complex.I) * (B0581.bsSym κ ζ) 0
      = 1 := by
  have hD : ((κ : ℂ) ^ 2 + (ζ : ℂ) ^ 2) ≠ 0 := by exact_mod_cast h
  simp only [B0581.bsSym]
  push_cast
  field_simp
  ring_nf
  simp [Complex.I_sq]

/-! ## Glue -/

/-- A cylinder test function times an `L²(cell)` function is integrable on the cell. -/
theorem integrable_psi_mul_lp (c : ℝ) {ψ : B0579.Plane → ℝ} (hψ : B0579.IsCylTest c ψ)
    (f : Lp ℂ 2 (B0581.cellVol c)) :
    Integrable (fun x => (ψ x : ℂ) * (f : B0579.Plane → ℂ) x) (B0581.cellVol c) :=
  (B0583.memLp_cellVol_of_isCylTest hψ).ofReal.integrable_mul (Lp.memLp f)

/-- **`velocityIsBiotSavart` from the weak nonzero-mode identities** (`NonzeroDivWeak`,
`NonzeroCurlWeak`) and the mean-part identity (`MeanPartOfX`). -/
theorem velocityIsBiotSavart_of_weak (hD : NonzeroDivWeak) (hC : NonzeroCurlWeak)
    (hM : MeanPartOfX) : VelocityIsBiotSavart := by
  intro c hc m hm ω hcirc
  have hm0 : 0 ≤ m := (zero_le_one.trans hm.le)
  set u : Lp B0581.Vel 2 (B0581.cellVol c) := B0583.velocity c hm.le ω hcirc with hu
  set W : Lp ℂ 2 (B0581.cellVol c) := B0581.ofX c m hm0 ω with hW
  set nz : Lp ℂ 2 (B0581.cellVol c) := B0581.nonzeroPart c W with hnz
  have hq := (B0583.hasWeakVelDeriv_iff_inner c 0 u _).1
    (B0583.hasWeakVelDeriv_velocity_q c hm.le ω hcirc)
  have he := (B0583.hasWeakVelDeriv_iff_inner c 1 u _).1
    (B0583.hasWeakVelDeriv_velocity_eta c hm.le ω hcirc)
  have hw2 : MemLp (fun η => -B0583.omegaBar c ω η) 2 volume :=
    (B0583.zeroMode_facts hc.out hm.le ω hcirc).2.1.neg
  refine ⟨?_, ?_, ?_⟩
  · intro j
    exact ContinuousLinearMap.comp_memLp' (EuclideanSpace.proj j : B0581.Vel →L[ℂ] ℂ)
      (Lp.memLp u)
  · intro ψ hψ
    have I0 := B0583.integrable_testLp_mul c (hψ.pd 0) 0 u
    have I1 := B0583.integrable_testLp_mul c (hψ.pd 1) 1 u
    have hz1 : ⟪B0583.testLp c hψ 1, B0583.zeroVelEtaLp c hm.le ω hcirc⟫_ℂ = 0 := by
      rw [show B0583.zeroVelEtaLp c hm.le ω hcirc = (B0583.memLp_profField c hw2).toLp
          (B0583.profField fun η => -B0583.omegaBar c ω η) from rfl,
        B0583.inner_testLp_profField c hψ 1 hw2]
      simp
    have h0 := hq ψ hψ 0
    have h1 := he ψ hψ 1
    have hdiv := hD c nz hψ
    have e1 : ∫ x in B0579.cell c, (u x 0 * (B0579.pd 0 ψ x : ℂ) + u x 1 * (B0579.pd 1 ψ x : ℂ)) =
        ⟪B0583.testLp c (hψ.pd 0) 0, u⟫_ℂ + ⟪B0583.testLp c (hψ.pd 1) 1, u⟫_ℂ := by
      rw [B0583.inner_testLp, B0583.inner_testLp, ← integral_add I0 I1]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [mul_comm]
    have hg : B0583.velGradEta c hm.le ω hcirc =
        B0583.gradEta c nz + B0583.zeroVelEtaLp c hm.le ω hcirc := rfl
    have hg' : B0583.velGradQ c hm.le ω = B0583.gradQ c nz := rfl
    rw [e1, h0, h1, hg, hg', inner_add_right, hz1, add_zero]
    linear_combination -hdiv
  · intro ψ hψ
    have J0 := B0583.integrable_testLp_mul c (hψ.pd 1) 0 u
    have J1 := B0583.integrable_testLp_mul c (hψ.pd 0) 1 u
    have hz0 : ⟪B0583.testLp c hψ 0, B0583.zeroVelEtaLp c hm.le ω hcirc⟫_ℂ =
        -(∫ x, (ψ x : ℂ) * ((B0583.omegaBar c ω x.2 : ℝ) : ℂ) ∂(B0581.cellVol c)) := by
      rw [show B0583.zeroVelEtaLp c hm.le ω hcirc = (B0583.memLp_profField c hw2).toLp
          (B0583.profField fun η => -B0583.omegaBar c ω η) from rfl,
        B0583.inner_testLp_profField c hψ 0 hw2]
      simp only [PiLp.single_apply, ite_true, mul_one]
      have : ∫ x, ψ x * -B0583.omegaBar c ω x.2 ∂(B0581.cellVol c) =
          -∫ x, ψ x * B0583.omegaBar c ω x.2 ∂(B0581.cellVol c) := by
        simp only [mul_neg]
        exact integral_neg _
      rw [this, Complex.ofReal_neg, ← integral_complex_ofReal]
      push_cast
      rfl
    have hidem : B0581.nonzeroPart c nz = nz := by
      have h0 : B0581.meanPart c nz = 0 := by
        rw [B0581.meanPart, hnz, B0581.modes_nonzeroPart]
        simp only [↓reduceIte, map_zero]
      rw [B0581.nonzeroPart, h0, sub_zero]
    have hcurl := hC c nz hψ
    rw [hidem] at hcurl
    have e2 : ∫ x in B0579.cell c, (u x 0 * (B0579.pd 1 ψ x : ℂ) - u x 1 * (B0579.pd 0 ψ x : ℂ)) =
        ⟪B0583.testLp c (hψ.pd 1) 0, u⟫_ℂ - ⟪B0583.testLp c (hψ.pd 0) 1, u⟫_ℂ := by
      rw [B0583.inner_testLp, B0583.inner_testLp, ← integral_sub J0 J1]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [mul_comm]
    have hmean : ∫ x, (ψ x : ℂ) * (B0581.meanPart c W : B0579.Plane → ℂ) x ∂(B0581.cellVol c) =
        ∫ x, (ψ x : ℂ) * ((B0583.omegaBar c ω x.2 : ℝ) : ℂ) ∂(B0581.cellVol c) := by
      refine integral_congr_ae ?_
      filter_upwards [hM c m hm0 ω] with x hx
      rw [hx]
    have hsplit : ∫ x, ((ω x : ℝ) : ℂ) * (ψ x : ℂ) ∂(B0581.cellVol c) =
        ∫ x, (ψ x : ℂ) * (B0581.meanPart c W : B0579.Plane → ℂ) x ∂(B0581.cellVol c) +
          ∫ x, (ψ x : ℂ) * (nz : B0579.Plane → ℂ) x ∂(B0581.cellVol c) := by
      rw [← integral_add (integrable_psi_mul_lp c hψ _) (integrable_psi_mul_lp c hψ nz)]
      refine integral_congr_ae ?_
      filter_upwards [B0581.coeFn_ofX c m hm0 ω,
        Lp.coeFn_add (B0581.meanPart c W) nz] with x h1 h2
      rw [B0581.meanPart_add_nonzeroPart c W] at h2
      have h1' : (W : B0579.Plane → ℂ) x = ((ω x : ℝ) : ℂ) := h1
      rw [← h1', h2, Pi.add_apply]
      ring
    have hg : B0583.velGradEta c hm.le ω hcirc =
        B0583.gradEta c nz + B0583.zeroVelEtaLp c hm.le ω hcirc := rfl
    have hg' : B0583.velGradQ c hm.le ω = B0583.gradQ c nz := rfl
    beta_reduce
    rw [e2, he ψ hψ 0, hq ψ hψ 1, hg, hg', inner_add_right, hz0]
    show ∫ x, ((ω x : ℝ) : ℂ) * (ψ x : ℂ) ∂(B0581.cellVol c) = _
    rw [hsplit, hmean]
    linear_combination -hcurl

/-! ## From the modewise identities to the weak identities -/

theorem qModeCLM_zero (c : ℝ) [Fact (0 < c)] : B0583.qModeCLM c 0 = 0 := by
  ext1 g
  simp [B0583.qModeCLM_apply, B0581.bsModeCLM_zero, B0581.kappa]

/-- `NonzeroDivWeak` from the modewise identity `ModeDiv` (Parseval for `synth`, no completeness). -/
theorem nonzeroDivWeak_of (h : ModeDiv) : NonzeroDivWeak := by
  intro c hc W ψ hψ
  rw [B0583.gradQ_apply, B0583.gradEta_apply, B0583.inner_synth_right, B0583.inner_synth_right,
    lp.inner_eq_tsum, lp.inner_eq_tsum,
    ← Summable.tsum_add
      (lp.summable_inner (𝕜 := ℂ) (B0581.modes c (B0583.testLp c hψ 0) : B0581.ModeSeq B0581.Vel)
        (B0583.qModes c (B0581.modes c W)))
      (lp.summable_inner (𝕜 := ℂ) (B0581.modes c (B0583.testLp c hψ 1) : B0581.ModeSeq B0581.Vel)
        (B0583.etaModes c (B0581.modes c W)))]
  refine (tsum_congr fun k => ?_).trans tsum_zero
  exact h c k hψ ((B0581.modes c W : B0581.ModeSeq ℂ) k)

/-- `NonzeroCurlWeak` from the modewise identity `ModeCurl`, `SynthEmbed0` and the completeness
of the scalar modes (`b0581_synth_modes`). -/
theorem nonzeroCurlWeak_of (h : ModeCurl) (hE : SynthEmbed0) : NonzeroCurlWeak := by
  intro c hc W ψ hψ
  set N : Lp ℂ 2 (B0581.cellVol c) := B0581.nonzeroPart c W with hN
  have hR : ∫ x, (ψ x : ℂ) * (N : B0579.Plane → ℂ) x ∂(B0581.cellVol c) =
      ⟪B0583.testLp c hψ 0, embed0Lp c N⟫_ℂ := by
    rw [B0583.inner_testLp]
    refine integral_congr_ae ?_
    filter_upwards [ContinuousLinearMap.coeFn_compLpL embed0 N] with x hx
    have hx' : (embed0Lp c N : B0579.Plane → B0581.Vel) x = embed0 (N x) := hx
    rw [hx', embedJ_apply]
    simp
  have hS : embed0Lp c N = B0581.synth c (embed0Modes (B0581.modes c N)) := by
    rw [← hE c (B0581.modes c N), UnforcedLeray.Cons.L2.SolAudit.b0581_synth_modes]
  set m1 : B0581.ModeSeq B0581.Vel := B0581.modes c (B0583.testLp c hψ 1) with hm1
  set m0 : B0581.ModeSeq B0581.Vel := B0581.modes c (B0583.testLp c hψ 0) with hm0
  set Wm : B0581.ModeSeq ℂ := B0581.modes c W with hWm
  set Nm : B0581.ModeSeq ℂ := B0581.modes c N with hNm
  have L1 : ⟪B0583.testLp c hψ 1, B0583.gradQ c W⟫_ℂ = ⟪m1, B0583.qModes c Wm⟫_ℂ := by
    rw [B0583.gradQ_apply]
    exact B0583.inner_synth_right c _ _
  have L2 : ⟪B0583.testLp c hψ 0, B0583.gradEta c W⟫_ℂ = ⟪m0, B0583.etaModes c Wm⟫_ℂ := by
    rw [B0583.gradEta_apply]
    exact B0583.inner_synth_right c _ _
  have L3 : ⟪B0583.testLp c hψ 0, B0581.synth c (embed0Modes Nm)⟫_ℂ = ⟪m0, embed0Modes Nm⟫_ℂ :=
    B0583.inner_synth_right c _ _
  rw [hR, hS, L1, L2, L3, lp.inner_eq_tsum m1, lp.inner_eq_tsum m0, lp.inner_eq_tsum m0,
    ← Summable.tsum_sub (lp.summable_inner (𝕜 := ℂ) m1 (B0583.qModes c Wm))
      (lp.summable_inner (𝕜 := ℂ) m0 (B0583.etaModes c Wm))]
  refine tsum_congr fun k => ?_
  by_cases hk : k = 0
  · subst hk
    have h0 : (B0581.modes c N : B0581.ModeSeq ℂ) 0 = 0 := by
      rw [hN, B0581.modes_nonzeroPart]; simp
    have e1 : (B0583.qModes c (B0581.modes c W) : B0581.ModeSeq B0581.Vel) 0 = 0 := by
      show B0583.qModeCLM c 0 _ = 0
      rw [qModeCLM_zero]; rfl
    have e2 : (B0583.etaModes c (B0581.modes c W) : B0581.ModeSeq B0581.Vel) 0 = 0 := by
      show B0583.etaModeCLM c 0 _ = 0
      rw [B0583.etaModeCLM_zero]; rfl
    rw [e1, e2, embed0Modes_apply, h0]
    simp
  · have hk' : (B0581.modes c N : B0581.ModeSeq ℂ) k = (B0581.modes c W : B0581.ModeSeq ℂ) k := by
      rw [hN, B0581.modes_nonzeroPart]
      simp [hk]
    rw [embed0Modes_apply, hk']
    exact h c k hk hψ ((B0581.modes c W : B0581.ModeSeq ℂ) k)

/-- **`velocityIsBiotSavart` from the four leaves** (the conditional theorem of
`PartIII-a:T20/4`): the modewise divergence and curl identities, the commutation of synthesis with
`z ↦ z e₀`, and the identification of the horizontal mean. -/
theorem velocityIsBiotSavart_of (hD : ModeDiv) (hC : ModeCurl) (hE : SynthEmbed0)
    (hM : MeanPartOfX) : VelocityIsBiotSavart :=
  velocityIsBiotSavart_of_weak (nonzeroDivWeak_of hD) (nonzeroCurlWeak_of hC hE) hM

end CTE

end UnforcedLeray.Short.IIIa
