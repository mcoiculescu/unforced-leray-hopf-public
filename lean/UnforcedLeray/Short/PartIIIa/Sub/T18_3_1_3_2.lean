import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_3

/-!
# Part III-a, `PartIII-a:T18/3/1/3/2` (`MollIdentity`): the mollified energy identity, decomposed

Source of record: `the November 2 reference manuscript` (SP) lines 3541-3552 and
3427-3440.

`MollifiedEnergyIdentity` follows from two statements:

* `LMEnergyBridge` (generic, no equation): if `u, u' : ℝ → L²(cell; ℂ²)` are locally square
  integrable on `(0,∞) × cell` and `u'` is the weak time derivative of `u` (tested against every
  `χ ∈ L²(cell)`), then `∫ w' ‖u‖² = -2 ∫ w Re⟨u', u⟩` for every smooth `w` with compact support in
  `(0,∞)`. This is `HasWeakDerivTime.weighted_norm_sq_sub` (`Lib/BochnerTime/Energy.lean:209`)
  after identifying `u` with an `H`-valued function.
* `MollDerivData` (the equation): for the mollified field `u_k(s) = J_k b(s)` there is such a `u'`
  (namely `-(μ/s) u_k + νΔu_k + J_k 𝒫₀ div F`, from `ExtWeakH1` tested with `J_k φ`, using
  `selfAdj`, `commute`, `divFree`) with
  `2 Re⟨u', u_k⟩ = -(2 Re μ s⁻¹ E_k + 2 ν N_k + 2 R_k)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The `L²(cell; ℂ²)` pairing `⟨f, g⟩ = ∫_cell ∑ᵢ conj(fᵢ) gᵢ`. -/
def LMIp (c : ℝ) (f g : LMSpField) : ℂ :=
  ∫ x in B0579.cell c, ∑ i : Fin 2, starRingEnd ℂ (f x i) * g x i

/-- `u' ` is the weak time derivative of `u` as `L²(cell; ℂ²)`-valued functions on `(0,∞)`:
joint measurability, local square integrability on `[s₁,s₂] × cell` (`0 < s₁ < s₂`), and
`∫ ψ' ⟨χ, u⟩ = -∫ ψ ⟨χ, u'⟩` for every `ψ ∈ C_c^∞(0,∞)` and every `χ ∈ L²(cell)`. -/
structure LMWeakDeriv (c : ℝ) (u u' : ℝ → LMSpField) : Prop where
  measU : ∀ i : Fin 2, Measurable fun p : ℝ × (ℝ × ℝ) => u p.1 p.2 i
  measU' : ∀ i : Fin 2, Measurable fun p : ℝ × (ℝ × ℝ) => u' p.1 p.2 i
  l2U : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
    ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (vnorm2 (fun i => u p.1 p.2 i) ^ 2) < ⊤
  l2U' : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
    ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (vnorm2 (fun i => u' p.1 p.2 i) ^ 2) < ⊤
  identity : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ioi (0 : ℝ) →
    ∀ χ : LMSpField, LMCellL2 c χ →
      ∫ s in Ioi (0 : ℝ), ((deriv ψ s : ℝ) : ℂ) * LMIp c χ (u s) =
        -∫ s in Ioi (0 : ℝ), (ψ s : ℂ) * LMIp c χ (u' s)

/-- **Lemma D (the `H`-valued energy identity)**: SP 3541-3552 with
`Lib/BochnerTime/Energy.lean:209` (`HasWeakDerivTime.weighted_norm_sq_sub`). -/
def LMEnergyBridge : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ u u' : ℝ → LMSpField, LMWeakDeriv c u u' →
    ∀ w : ℝ → ℝ, ContDiff ℝ ∞ w → HasCompactSupport w → tsupport w ⊆ Ioi (0 : ℝ) →
      ∫ s in Ioi (0 : ℝ), deriv w s * ∫ x in B0579.cell c, vnorm2 (u s x) ^ 2 =
        -∫ s in Ioi (0 : ℝ), w s * (2 * (LMIp c (u' s) (u s)).re)

/-- **Lemmas A-C (the equation)**: for the mollified field `u_k = J_k b` there is a weak derivative
`u'` (`-(μ/s) u_k + νΔu_k + J_k 𝒫₀ div F`; SP 3427-3440, 3541-3552) with
`2 Re⟨u', u_k⟩ = -(2 Re μ s⁻¹ E_k + 2 ν N_k + 2 R_k)` for a.e. `s > 0`. -/
def MollDerivData : Prop :=
  ∀ (c ν : ℝ) (μ : ℂ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ),
    FreeSolData c ν μ F b G → ∀ J : ℕ → LMSpField → LMSpField, IsLMMollifier c J →
    ExtWeakH1 c ν μ F b G → ∀ k : ℕ,
      ∃ u' : ℝ → LMSpField, LMWeakDeriv c (LMMollU J b k) u' ∧
        ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
          2 * (LMIp c (u' s) (LMMollU J b k s)).re =
            -(2 * μ.re / s * LMMollE c J b k s + 2 * ν * LMMollN c J b k s +
              2 * LMMollR c J F b k s)

theorem mollifiedEnergyIdentity_of (hD : LMEnergyBridge) (hM : MollDerivData) :
    MollifiedEnergyIdentity := by
  intro c ν μ F b G hS J hJ hE w hw hcs hts k
  obtain ⟨u', hu', hpair⟩ := hM c ν μ F b G hS J hJ hE k
  have h := hD c hS.pos_c _ u' hu' w hw hcs hts
  have h2 : ∫ s in Ioi (0 : ℝ), deriv w s * LMMollE c J b k s =
      ∫ s in Ioi (0 : ℝ), deriv w s * ∫ x in B0579.cell c, vnorm2 (LMMollU J b k s x) ^ 2 := rfl
  rw [h2, h, ← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [hpair] with s hs
  rw [hs]; ring

end UnforcedLeray.Short.IIIa
