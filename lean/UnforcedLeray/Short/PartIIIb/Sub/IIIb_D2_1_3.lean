import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- Pointwise complex conjugate of a `ℂ³`-valued field. -/
def cjF (w : ℝ × Space → CVec3) : ℝ × Space → CVec3 :=
  fun x => WithLp.toLp 2 fun i => (starRingEnd ℂ) (w x i)

/-- **Duality (adjoint solvability + density)** (source 1351-1362, `bg:common-body-graph` at
`r = 2`: "the adjoint has the same maximal graph and the same bound"; Leray projection of the
datum, 1361): for `0 < P ≤ 1`, `ν > 0`, `a_2 = μ + 1/4 > 0`, every weakly solenoidal `f ∈ Y_2` is
the `Y_2`-limit of `(μ + L₀ᵗ)Φₙ` with `Φₙ` *solenoidal phase tests* (the adjoint solution
`Φ ∈ D_2^*` of `(μ + L₀ᵗ)Φ = ℙf = f` is solenoidal, and is approximated in the adjoint graph norm
by solenoidal compactly supported tests via a solenoidal cutoff `curl(χₙ ψ)` for the stream
potential `ψ` of `Φ`).  The combinations lie in `Y_2`. -/
def FWUDense : Prop :=
  ∀ (P ν μ : ℝ), 0 < P → P ≤ 1 → 0 < ν → 0 < μ + 1 / 4 →
    ∀ f : ℝ × Space → CVec3, UnforcedLeray.Short.IIb.IsInYr P 2 f → IsWeakSolenoidal P f →
      ∃ Φ : ℕ → ℝ × Space → CVec3, (∀ n, IsSolTest P (Φ n)) ∧
        (∀ n, UnforcedLeray.Short.IIb.IsInYr P 2 (fun x => L0T ν (Φ n) x + (μ : ℂ) • Φ n x)) ∧
        Tendsto (fun n => UnforcedLeray.Short.IIb.phaseLpNorm P 2
          (fun x => L0T ν (Φ n) x + (μ : ℂ) • Φ n x - f x)) atTop (𝓝 0)

/-- **Continuity of the `Y_2` pairing** (Cauchy-Schwarz on the normalized phase measure,
`|⟪g, w⟫| ≤ ‖g‖_{Y_2}‖w‖_{Y_2}`, source 1341-1344): if `gₙ → f` in `Y_2` then
`⟪gₙ, w⟫ → ⟪f, w⟫` for `w ∈ Y_2`. -/
def FWUPairCont : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ (g : ℕ → ℝ × Space → CVec3) (f w : ℝ × Space → CVec3),
    (∀ n, UnforcedLeray.Short.IIb.IsInYr P 2 (g n)) → UnforcedLeray.Short.IIb.IsInYr P 2 f →
    UnforcedLeray.Short.IIb.IsInYr P 2 w →
    Tendsto (fun n => UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => g n x - f x)) atTop (𝓝 0) →
    Tendsto (fun n => pairF P (g n) w) atTop (𝓝 (pairF P f w))

/-- **Conjugation preserves** `Y_2` and weak solenoidality (`div w̄ = conj(div w)`; the phase
tests are closed under conjugation; source 1351-1362 for the pairing used). -/
def FWUConj : Prop :=
  ∀ (P : ℝ) (w : ℝ × Space → CVec3), UnforcedLeray.Short.IIb.IsInYr P 2 w →
    IsWeakSolenoidal P w →
    UnforcedLeray.Short.IIb.IsInYr P 2 (cjF w) ∧ IsWeakSolenoidal P (cjF w)

/-- **Self-pairing** `⟪w̄, w⟫ = P⁻¹∫₀ᴾ∫ |w|² = 0` forces `w = 0` a.e. (`w ∈ Y_2` ensures
integrability, so the iterated integral is `‖w‖²_{Y_2}`). -/
def FWUSelfPair : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ w : ℝ × Space → CVec3, UnforcedLeray.Short.IIb.IsInYr P 2 w →
    pairF P (cjF w) w = 0 → w =ᵐ[volume] 0

/-- **Homogeneous uniqueness by duality** (source 1580-1583 via `bg:common-body-graph` 1351-1362
adjoint at `r = 2`).  The Leray-extension route (equation against all phase tests) is NOT valid
for a general weakly solenoidal `w`: only `ℙ(μ+L)w = 0`, i.e. `(μ+L)w = ∇π`, holds; the solenoidal
datum `f = w̄` is instead solved on the adjoint side. -/
theorem fwuHomog_of (hD : FWUDense) (hC : FWUPairCont) (hJ : FWUConj) (hS : FWUSelfPair) :
    FWUHomog := by
  intro P ν μ hP hP1 hν hμ w hw hweq
  obtain ⟨hwj, hwj'⟩ := hJ P w hw hweq.solenoidal
  obtain ⟨Φ, hΦ, hΦY, hΦt⟩ := hD P ν μ hP hP1 hν hμ (cjF w) hwj hwj'
  have hlim := hC P hP (fun n x => L0T ν (Φ n) x + (μ : ℂ) • Φ n x) (cjF w) w hΦY hwj hw hΦt
  have h0 : ∀ n, pairF P (fun x => L0T ν (Φ n) x + (μ : ℂ) • Φ n x) w = 0 := fun n => by
    simpa using hweq.equation (Φ n) (hΦ n)
  have hz : pairF P (cjF w) w = 0 :=
    tendsto_nhds_unique hlim (by simp only [h0]; exact tendsto_const_nhds)
  exact hS P hP w hw hz

end UnforcedLeray.Short.PartIIIb.Concrete
