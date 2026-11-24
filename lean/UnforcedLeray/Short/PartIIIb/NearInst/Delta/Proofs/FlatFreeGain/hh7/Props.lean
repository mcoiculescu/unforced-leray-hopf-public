import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Lemmas

/-!
# Decomposition of `flatFreeGainBound_of` (item `PartIII-b:C/near/delta/7`)

Source of record `the November 2 reference manuscript`,
3420-3440 (`prop:short-polynomial-causal` with `v = 0`: `‖g⁻¹b‖_𝓗 ≤ (2√(k_*ν))⁻¹‖g⁻¹F‖_𝒯`, zero
entrance, uniqueness) and 3564-3571 (`‖F₁+F₂‖_𝒯 ≤ ‖F‖_Z` for `W ≥ 1`, `ρ_b ≤ 1`).

The energy-to-`L²` bridge is split into four lemmas (the free solver `hU` is used as is):

* `FreeSolAEInvariant` : the class of causal solutions only sees the source up to a.e. equality;
* `SourceMeasRep` : the meridional block of `g·F` has a symmetric measurable representative whose
  `g⁻¹`-conjugate has `𝒯`-norm `≤ ‖F‖_Z` (3564-3571);
* `VelNormBridge` : the `𝓗`-norm of the conjugated energy field dominates the `H`-norm of `g⁻¹ v`;
* `AgeMeasureAC` : `s^a ds dq dη` is absolutely continuous w.r.t. Lebesgue on `(0,∞) × cell`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.Blueprint.Planar

/-- The class of free causal energy solutions only depends on the source up to a.e. equality
(`F` enters only through the integrable weak identity, 3426-3440). -/
def FreeSolAEInvariant : Prop :=
  ∀ (c ν : ℝ) (μ : ℂ), 0 < c →
    ∀ (F F' : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
      (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ),
      UnforcedLeray.Short.IIIa.IsCausalEnergySolution c ν μ (fun _ _ _ => 0) F b G →
      F =ᵐ[ageμ c (-1 / 2)] F' →
      UnforcedLeray.Short.IIIa.IsCausalEnergySolution c ν μ (fun _ _ _ => 0) F' b G

/-- **The source of the flat equation** (3564-3571): for `m_Z ≥ 0`, `0 < ρ_b ≤ 1`, the meridional
block of `𝖦F ∈ Z` has a symmetric measurable representative `Fm` with
`‖g⁻¹Fm‖_𝒯 ≤ ‖F‖_Z`. -/
def SourceMeasRep : Prop :=
  ∀ (c mZ ρb γ ν : ℝ) (hν : 0 < ν), 0 < c → 0 ≤ mZ → 0 < ρb → ρb ≤ 1 →
    ∀ F : Zsp c mZ ρb, ∃ Fm : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ,
      (∀ p i j, Fm p i j = Fm p j i) ∧ (∀ i j, Measurable fun p => Fm p i j) ∧
      Fm =ᵐ[ageμ c (-1 / 2)] merBlockC (zsum (gainEquiv c mZ ρb γ hν F)) ∧
      UnforcedLeray.Short.IIIa.tCalNorm c (UnforcedLeray.Short.IIIa.gainConj γ ν Fm) ≤
        ENNReal.ofReal ‖F‖

/-- **The velocity norm** (3412: `𝓗 = L²(s^{-3/2}ds; L²)`): if `b` represents `v ∈ H`, then
`‖g⁻¹v‖_H ≤ ‖g⁻¹b‖_𝓗`. -/
def VelNormBridge : Prop :=
  ∀ (c γ ν : ℝ) (hν : 0 < ν) (v : Hsp c) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ),
    b =ᵐ[ageμ c (-3 / 2)] velC (v : Chart → Merid) →
      ENNReal.ofReal ‖(gainH c γ hν).symm v‖ ≤
        UnforcedLeray.Short.IIIa.hCalNorm c (UnforcedLeray.Short.IIIa.gainConj γ ν b)

/-- The age measures are absolutely continuous w.r.t. Lebesgue measure on `(0,∞) × cell`. -/
def AgeMeasureAC : Prop :=
  ∀ (c a : ℝ), 0 < c →
    ageμ c a ≪ volume.restrict (Ioi (0 : ℝ) ×ˢ UnforcedLeray.B0579.cell c)

/-- Arithmetic: `(2√(k_*ν))⁻¹ ≤ ν⁻¹` for `k_* ≥ 1/4`, `0 < ν ≤ 1`. -/
theorem inv_two_sqrt_le {k ν : ℝ} (hk : 1 / 4 ≤ k) (hν : 0 < ν) (hν1 : ν ≤ 1) :
    (2 * Real.sqrt (k * ν))⁻¹ ≤ ν⁻¹ := by
  have h1 : Real.sqrt ν / 2 ≤ Real.sqrt (k * ν) := by
    have : Real.sqrt (ν / 4) ≤ Real.sqrt (k * ν) :=
      Real.sqrt_le_sqrt (by nlinarith)
    rwa [show ν / 4 = (1 / 2) ^ 2 * ν by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num), one_div, ← div_eq_inv_mul] at this
  have hs : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hs1 : Real.sqrt ν ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hν1
  have h2 : Real.sqrt ν ≤ 2 * Real.sqrt (k * ν) := by linarith
  have h3 : (2 * Real.sqrt (k * ν))⁻¹ ≤ (Real.sqrt ν)⁻¹ :=
    inv_anti₀ hs h2
  have h4 : (Real.sqrt ν)⁻¹ ≤ ν⁻¹ := by
    have : ν = Real.sqrt ν * Real.sqrt ν := (Real.mul_self_sqrt hν.le).symm
    rw [inv_le_inv₀ hs hν]
    nlinarith
  exact h3.trans h4

/-- The flat free response in the gain norm, from the four lemmas and the free solver. -/
theorem flatFreeGainBound_core (hU : UnforcedLeray.Short.IIIa.FreeCausalExistsUnique)
    (hA : FreeSolAEInvariant) (hB : SourceMeasRep) (hC : VelNormBridge) (hD : AgeMeasureAC) :
    FlatFreeGainBound := by
  intro P hP Kset hK hKs mZ hmZ dm dp hdm
  have hadm : UnforcedLeray.Short.IIIa.IsAdmissibleK (Complex.ofReal '' Kset) :=
    ⟨hK.image Complex.continuous_ofReal, by
      rintro _ ⟨x, hx, rfl⟩
      have := hKs hx
      exact ⟨by simpa using this.1, by simpa using this.2⟩⟩
  obtain ⟨ν₀, hν₀, hex⟩ := hU P hP _ hadm
  refine ⟨1, 1, min ν₀ 1, lt_min hν₀ one_pos, ?_⟩
  intro p d hreg hν ρb hρ hρ1 μ hμ S0 hS0
  have hν0 : p.ν ≤ ν₀ := hν.trans (min_le_left _ _)
  have hν1 : p.ν ≤ 1 := hν.trans (min_le_right _ _)
  have hc : (p.ν ^ (-2 : ℝ)) = p.c := by
    rw [hreg.c_eq, Real.rpow_neg p.ν_pos.le, Real.rpow_two]
  have hexμ := hex p.ν ⟨p.ν_pos, hν0⟩ (μ : ℂ) ⟨μ, hμ, rfl⟩
  simp only [hc] at hexμ
  have hcpos : 0 < p.c := p.c_pos
  have hk : (1 / 4 : ℝ) ≤ ⨅ μ' : (Complex.ofReal '' Kset), μ'.1.re + 1 / 4 := by
    haveI : Nonempty (Complex.ofReal '' Kset) := ⟨⟨(μ : ℂ), μ, hμ, rfl⟩⟩
    refine le_ciInf fun μ' => ?_
    obtain ⟨x, hx, hxe⟩ := μ'.2
    have := (hKs hx).1
    have h' : μ'.1.re = x := by rw [← hxe]; simp
    rw [h']; linarith
  refine ContinuousLinearMap.opNorm_le_bound _ (by
      have := p.ν_pos; positivity) fun F => ?_
  rw [gainConjS_apply]
  obtain ⟨b, G, hbv, hsol⟩ := hS0 (gainEquiv p.c mZ ρb P.eigenvalue.re p.ν_pos F)
  obtain ⟨Fm, hsym, hmeas, hae, hnorm⟩ :=
    hB p.c mZ ρb P.eigenvalue.re p.ν p.ν_pos hcpos hmZ hρ hρ1 F
  have hsol' := hA p.c p.ν (μ : ℂ) hcpos _ Fm b G hsol hae.symm
  have hfin : UnforcedLeray.Short.IIIa.tCalNorm p.c
      (UnforcedLeray.Short.IIIa.gainConj P.eigenvalue.re p.ν Fm) < ⊤ :=
    hnorm.trans_lt ENNReal.ofReal_lt_top
  obtain ⟨b₁, G₁, hsol₁, hH, -, huniq⟩ := hexμ Fm hsym hmeas hfin
  have hbb : b =ᵐ[ageμ p.c (-3 / 2)] b₁ :=
    (hD p.c (-3 / 2) hcpos).ae_le (huniq b G hsol')
  have hbb' : UnforcedLeray.Short.IIIa.gainConj P.eigenvalue.re p.ν b =ᵐ[ageμ p.c (-3 / 2)]
      UnforcedLeray.Short.IIIa.gainConj P.eigenvalue.re p.ν b₁ := by
    filter_upwards [hbb] with x hx
    simp [UnforcedLeray.Short.IIIa.gainConj, hx]
  have h1 := hC p.c P.eigenvalue.re p.ν p.ν_pos (S0 (gainEquiv p.c mZ ρb P.eigenvalue.re p.ν_pos F))
    b hbv
  have h2 : UnforcedLeray.Short.IIIa.hCalNorm p.c
      (UnforcedLeray.Short.IIIa.gainConj P.eigenvalue.re p.ν b) =
        UnforcedLeray.Short.IIIa.hCalNorm p.c
          (UnforcedLeray.Short.IIIa.gainConj P.eigenvalue.re p.ν b₁) := by
    unfold UnforcedLeray.Short.IIIa.hCalNorm
    exact eLpNorm_congr_ae (by filter_upwards [hbb'] with x hx; simp [hx])
  have hc1 := inv_two_sqrt_le hk p.ν_pos hν1
  have h3 : ENNReal.ofReal ‖(gainH p.c P.eigenvalue.re p.ν_pos).symm
      (S0 (gainEquiv p.c mZ ρb P.eigenvalue.re p.ν_pos F))‖ ≤
      ENNReal.ofReal (p.ν⁻¹ * ‖F‖) := by
    calc _ ≤ _ := h1
      _ = _ := h2
      _ ≤ _ := hH
      _ ≤ ENNReal.ofReal ((2 * Real.sqrt ((⨅ μ' : (Complex.ofReal '' Kset), μ'.1.re + 1 / 4) *
            p.ν))⁻¹) * ENNReal.ofReal ‖F‖ := by gcongr
      _ = ENNReal.ofReal (((2 * Real.sqrt ((⨅ μ' : (Complex.ofReal '' Kset), μ'.1.re + 1 / 4) *
            p.ν))⁻¹) * ‖F‖) := by
          rw [ENNReal.ofReal_mul (by positivity)]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hc1 (norm_nonneg _))
  have := (ENNReal.ofReal_le_ofReal_iff (by have := p.ν_pos; positivity)).1 h3
  simpa [pow_one] using this

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
