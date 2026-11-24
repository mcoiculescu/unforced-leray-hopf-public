import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7

/-!
# `BodyColumnEnergy` from two source facts (decomposition of `PartIII-b:C/flatset/col/7/1`)

Source of record `the November 2 reference manuscript` 1684-1689 (pairing with
`s^{-1/2}b̄` gives the coercive constant `Re μ + 1/4`), 3426-3430, 1650-1656.

* `BodyColumnSmoothSeq`: approximate `h` by smooth compactly supported forces `h_k`, for which
  `b_k = R₀ h_k` is a classical energy field (`B0225.R0_Ms_ae`), use
  `(Re μ + 1/4)‖b_k‖²_H + ν‖∇b_k‖²_{H_T} ≤ ‖h_k‖_H‖b_k‖_H` to get that `(b_k, ∇b_k)` is Cauchy in
  `H ∩ H_T`; `R₀` is continuous on `H`, so `b_k → velC (R₀ h)` in `H`.
* `EnergyCauchyLimit`: the energy class with a.e.-age `divFree`, `weakGrad` is closed under limits
  Cauchy in `H ∩ H_T` (a.e. subsequence of age slices; `zeroEntrance` from the `H`-limit).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (vnorm2 tnorm2)

/-- `(b_k, G_k)` is Cauchy in `H ∩ H_T`: `H` has the age weight `s^{-3/2}ds`, `H_T` has `s^{-1/2}ds`. -/
def EnergyCauchy (c : ℝ) (b : ℕ → Chart → Fin 2 → ℂ) (G : ℕ → Chart → Fin 2 → Fin 2 → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ n, N ≤ n →
    ∫⁻ p, ENNReal.ofReal (vnorm2 (b m p - b n p) ^ 2) ∂(ageμ c (-3 / 2)) +
      ∫⁻ p, ENNReal.ofReal (tnorm2 (G m p - G n p) ^ 2) ∂(ageμ c (-1 / 2)) < ENNReal.ofReal ε

/-- `b_k → v` in `L²(ageμ c (-3/2))` (the norm of `H`). -/
def HConverges (c : ℝ) (b : ℕ → Chart → Fin 2 → ℂ) (v : Chart → Fin 2 → ℂ) : Prop :=
  Tendsto (fun k => ∫⁻ p, ENNReal.ofReal (vnorm2 (b k p - v p) ^ 2) ∂(ageμ c (-3 / 2)))
    atTop (𝓝 0)

/-- **Smooth approximation and coercive estimate** (source 1684-1689, 1650-1656). -/
def BodyColumnSmoothSeq : Prop :=
  ∀ (c ν μ : ℝ) (hc : 0 < c), 0 < ν → 0 < μ + 1 / 4 → ∀ R0 : Hsp c →L[ℝ] Hsp c,
    NearInst.IsBodyTransport R0 (UnforcedLeray.Short.PartIIa.T0flat hc ν (μ : ℂ)) →
    ∀ (h : Hsp c),
      ∃ (b : ℕ → Chart → Fin 2 → ℂ) (G : ℕ → Chart → Fin 2 → Fin 2 → ℂ),
        (∀ k, IsEnergyField c (b k) (G k)) ∧ EnergyCauchy c b G ∧
          HConverges c b (NearInst.velC (R0 h))

/-- **Closure of the energy class under `H ∩ H_T`-Cauchy limits** (source 3426-3430). -/
def EnergyCauchyLimit : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (b : ℕ → Chart → Fin 2 → ℂ) (G : ℕ → Chart → Fin 2 → Fin 2 → ℂ)
    (v : Chart → Fin 2 → ℂ),
    (∀ k, IsEnergyField c (b k) (G k)) → EnergyCauchy c b G → HConverges c b v →
    (∀ i, AEMeasurable (fun p => v p i) (ageμ c (-3 / 2))) →
    ∃ (b' : Chart → Fin 2 → ℂ) (G' : Chart → Fin 2 → Fin 2 → ℂ),
      b' =ᵐ[ageμ c (-3 / 2)] v ∧ IsEnergyFieldAE c b' G'

theorem velC_aemeasurable {c : ℝ} (u : Hsp c) (i : Fin 2) :
    AEMeasurable (fun p => NearInst.velC u p i) (ageμ c (-3 / 2)) := by
  have h1 : AEMeasurable (fun p => (u : Chart → EuclideanSpace ℝ (Fin 2)) p) (ageμ c (-3 / 2)) :=
    (Lp.aestronglyMeasurable u).aemeasurable
  have h2 : AEMeasurable (fun p => (u : Chart → EuclideanSpace ℝ (Fin 2)) p i)
      (ageμ c (-3 / 2)) :=
    ((EuclideanSpace.proj i).continuous.measurable).comp_aemeasurable h1
  exact Complex.measurable_ofReal.comp_aemeasurable h2

theorem bodyColumnEnergy_of (hS : BodyColumnSmoothSeq) (hL : EnergyCauchyLimit) :
    BodyColumnEnergy := by
  intro c ν μ hc hν hμ R0 hR h f _
  obtain ⟨b, G, hE, hC, hH⟩ := hS c ν μ hc hν hμ R0 hR h
  exact hL c hc b G _ hE hC hH (velC_aemeasurable (R0 h))

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
