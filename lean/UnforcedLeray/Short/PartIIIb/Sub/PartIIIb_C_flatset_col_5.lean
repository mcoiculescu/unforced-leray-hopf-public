import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Leaves

/-!
# Decomposition of `FlatColumnVorticity` (source 4610, 4464-4467, 2819-2836)

Source of record: `the November 2 reference manuscript` (73 pages).
Write `⟨x, φ⟩ = ∫_cell x φ` (`cellPair`) and `ℓ_r(ω) = ∫_cell flowIntegrand tr (xFn ω) (kcC ω) r φ`
(`ellFn`).  The target follows from five lemmas:

* `FcvDuhamelDatum` : the pin of `𝒰` per datum `g(t)` (4464-4467, 2819-2836);
* `FcvMellin` : `s^μ ξ(s) = ∫₀^s t^μ 𝒰(s,t)g(t)dt` tested against `φ` (4610);
* `FcvGInt`, `FcvXiInt` : the two integrability claims;
* `FcvFubini` : the Fubini exchange on `{0 < t < ρ < s}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- `⟨x, φ⟩ = ∫_cell x φ`. -/
def cellPair {c m : ℝ} [Fact (1 < m)] (φ : ℝ × ℝ → ℝ) (x : Xmc c m) : ℂ :=
  ∫ y in B0579.cell c, xFn x y * (φ y : ℂ)

/-- `ℓ_r(ω) = ⟨L(r)ω, φ⟩`, the tested linearised vorticity operator with the Biot-Savart velocity
`kcC ω` (source 2819-2836). -/
def ellFn {ν c m : ℝ} [Fact (1 < m)] [Fact (0 < c)] (tr : UnforcedLeray.B0140.TrainSol ν c)
    (φ : ℝ × ℝ → ℝ) (r : ℝ) (ω : Xmc c m) : ℂ :=
  ∫ y in B0579.cell c, IIIa.flowIntegrand tr (xFn ω) (kcC ω) r φ y

/-- **Pin per datum** (source 2819-2836, 4464-4467): for `g = gBD D B t` (real) and `t ≤ s`,
`⟨𝒰(s,t)g, φ⟩ = ⟨g, φ⟩ + ∫_t^s ℓ_ρ(𝒰(ρ,t)g)dρ`, the integrand integrable on `(t, s]`.
Route: `TrainEvolution.flow` gives the weak flow with some velocity `u`; `𝒰(ρ,t)g` is real
(`TrainEvolution.real`, `gBD_real`), so `u ρ = kcC (𝒰(ρ,t)g)` a.e. (`isBiotSavart_kc`,
`IIIa.CTE.BiotSavartUnique`); convert the interval integral. -/
def FcvDuhamelDatum : Prop :=
  ∀ (κ : IIIa.PlanarFrameKernels) (ν c m : ℝ) [Fact (1 < m)] [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) (D : FlatInstData κ ν c m tr) (B : ℝ → Mat3)
    (φ : ℝ × ℝ → ℝ), B0579.IsCylTest c φ → ∀ t : ℝ, 0 < t → ∀ s : ℝ, t ≤ s →
      IntegrableOn (fun ρ : ℝ => ellFn tr φ ρ (D.ev.U ρ t (gBD D B t))) (Ioc t s) ∧
      cellPair φ (D.ev.U s t (gBD D B t)) =
        cellPair φ (gBD D B t) + ∫ ρ in Ioc t s, ellFn tr φ ρ (D.ev.U ρ t (gBD D B t))

/-- **Mellin form of `ξ_B`** (source 4610): `s^μ⟨ξ_B(s), φ⟩ = ∫₀^s t^μ⟨𝒰(s,t)g_B(t), φ⟩dt`
(`xiD_apply`, `(s:ℂ)^μ (s:ℂ)^(-μ) = 1`, the functional `⟨·,φ⟩` is continuous linear and commutes
with the Bochner integral; the integrand is integrable by the bounds of `locBdd` and the local
boundedness of `gBD`). -/
def FcvMellin : Prop :=
  ∀ (κ : IIIa.PlanarFrameKernels) (ν c m : ℝ) [Fact (1 < m)] [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) (D : FlatInstData κ ν c m tr) (μ as : ℝ)
    (χf : ℝ → ℝ) (A : ℝ → Mat3), 0 < ν → 0 < μ → IsSourceCutoffC χf → IsAffElem as A →
    ∀ φ : ℝ × ℝ → ℝ, B0579.IsCylTest c φ → ∀ s : ℝ, 0 < s →
      ((s : ℂ) ^ (μ : ℂ)) * cellPair φ (xiD D (μ : ℂ) (Bmat ν μ χf A) s) =
        ∫ t in Ioc 0 s, ((t : ℂ) ^ (μ : ℂ)) *
          cellPair φ (D.ev.U s t (gBD D (Bmat ν μ χf A) t))

/-- **Integrability of the source term** (first conjunct of `FlatColumnVorticity`; `gBD` is locally
bounded and measurable on `(0, s]`, `μ > 0`; source 4614-4615 `g_B = O(s^{3/2})`). -/
def FcvGInt : Prop :=
  ∀ (κ : IIIa.PlanarFrameKernels) (ν c m : ℝ) [Fact (1 < m)] [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) (D : FlatInstData κ ν c m tr) (μ as : ℝ)
    (χf : ℝ → ℝ) (A : ℝ → Mat3), 0 < ν → 0 < μ → IsSourceCutoffC χf → IsAffElem as A →
    ∀ φ : ℝ × ℝ → ℝ, B0579.IsCylTest c φ → ∀ s : ℝ, 0 < s →
      IntegrableOn (fun t : ℝ => ((t : ℂ) ^ (μ : ℂ)) *
        cellPair φ (gBD D (Bmat ν μ χf A) t)) (Ioc 0 s)

/-- **Integrability of the flow term** (second conjunct of `FlatColumnVorticity`): `ρ ↦ ρ^μ
ℓ_ρ(ξ_B(ρ))` is integrable on `(0, s]`; uses `‖ξ_B(ρ)‖ ≤ C ρ^{5/2}` near `0` and continuity on
`(0,∞)` (`FlatXiRegular`, 4614-4615), the bound `|ℓ_ρ ω| ≤ C_ρ‖ω‖` locally uniform in `ρ`
(`train smooth`, `φ` compactly supported) and measurability of `ρ ↦ ℓ_ρ(ξ_B(ρ))`. -/
def FcvXiInt : Prop :=
  ∀ (κ : IIIa.PlanarFrameKernels) (ν c m : ℝ) [Fact (1 < m)] [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) (D : FlatInstData κ ν c m tr) (μ as : ℝ)
    (χf : ℝ → ℝ) (A : ℝ → Mat3), 0 < ν → 0 < μ → IsSourceCutoffC χf → IsAffElem as A →
    ∀ φ : ℝ × ℝ → ℝ, B0579.IsCylTest c φ → ∀ s : ℝ, 0 < s →
      IntegrableOn (fun r : ℝ => ((r : ℂ) ^ (μ : ℂ)) *
        ellFn tr φ r (xiD D (μ : ℂ) (Bmat ν μ χf A) r)) (Ioc 0 s)

/-- **The Fubini exchange on `{0 < t < ρ < s}`** (source 4610): the inner integrals
`t ↦ t^μ ∫_{(t,s]} ℓ_ρ(𝒰(ρ,t)g(t))dρ` are integrable on `(0, s]` and
`∫₀^s t^μ ∫_t^s ℓ_ρ(𝒰(ρ,t)g(t))dρ dt = ∫₀^s ρ^μ ℓ_ρ(ξ_B(ρ))dρ` (`ℓ_ρ` is real-linear and
continuous, so it commutes with `∫₀^ρ t^μ 𝒰(ρ,t)g(t)dt = ρ^μ ξ_B(ρ)`; `ρ^μ` is real). -/
def FcvFubini : Prop :=
  ∀ (κ : IIIa.PlanarFrameKernels) (ν c m : ℝ) [Fact (1 < m)] [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) (D : FlatInstData κ ν c m tr) (μ as : ℝ)
    (χf : ℝ → ℝ) (A : ℝ → Mat3), 0 < ν → 0 < μ → IsSourceCutoffC χf → IsAffElem as A →
    ∀ φ : ℝ × ℝ → ℝ, B0579.IsCylTest c φ → ∀ s : ℝ, 0 < s →
      IntegrableOn (fun t : ℝ => ((t : ℂ) ^ (μ : ℂ)) *
        ∫ ρ in Ioc t s, ellFn tr φ ρ (D.ev.U ρ t (gBD D (Bmat ν μ χf A) t))) (Ioc 0 s) ∧
      ∫ t in Ioc 0 s, ((t : ℂ) ^ (μ : ℂ)) *
          ∫ ρ in Ioc t s, ellFn tr φ ρ (D.ev.U ρ t (gBD D (Bmat ν μ χf A) t)) =
        ∫ ρ in Ioc 0 s, ((ρ : ℂ) ^ (μ : ℂ)) *
          ellFn tr φ ρ (xiD D (μ : ℂ) (Bmat ν μ χf A) ρ)

theorem flatColumnVorticity_of (h1 : FcvDuhamelDatum) (h2 : FcvMellin) (h3 : FcvGInt)
    (h4 : FcvXiInt) (h5 : FcvFubini) : FlatColumnVorticity := by
  intro κ ν c m _ _ tr D μ as χf A hν hμ hχ hA φ hφ s hs
  have g3 := h3 κ ν c m tr D μ as χf A hν hμ hχ hA φ hφ s hs
  have g4 := h4 κ ν c m tr D μ as χf A hν hμ hχ hA φ hφ s hs
  obtain ⟨g5a, g5b⟩ := h5 κ ν c m tr D μ as χf A hν hμ hχ hA φ hφ s hs
  refine ⟨g3, g4, ?_⟩
  have e2 := h2 κ ν c m tr D μ as χf A hν hμ hχ hA φ hφ s hs
  have e1 : ∫ t in Ioc 0 s, ((t : ℂ) ^ (μ : ℂ)) *
        cellPair φ (D.ev.U s t (gBD D (Bmat ν μ χf A) t)) =
      ∫ t in Ioc 0 s, (((t : ℂ) ^ (μ : ℂ)) * cellPair φ (gBD D (Bmat ν μ χf A) t) +
        ((t : ℂ) ^ (μ : ℂ)) *
          ∫ ρ in Ioc t s, ellFn tr φ ρ (D.ev.U ρ t (gBD D (Bmat ν μ χf A) t))) := by
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    have := (h1 κ ν c m tr D (Bmat ν μ χf A) φ hφ t ht.1 s ht.2).2
    show _ * _ = _ * _ + _ * _
    rw [this, mul_add]
  have e3 := integral_add g3 g5a
  show ((s : ℂ) ^ (μ : ℂ)) * cellPair φ (xiD D (μ : ℂ) (Bmat ν μ χf A) s) = _
  rw [e2, e1, e3, g5b]
  rfl

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
