import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_of

/-!
# `BodyColumnSmoothSeq` from four source facts (decomposition of `PartIII-b:C/flatset/col/7/1/1`)

Source of record `the November 2 reference manuscript`: 1650-1656
(`A₀ = -S + νsΔ`, `T₀ = (μ - A₀)⁻¹P₀`), 1684-1689 (the flat equation
`(∂_s + μ/s - νΔ)b = P₀ div₀ M`, "pairing it with `s^{-1/2} b̄` gives the coercive constant
`Re μ + 1/4`").

* `SmoothForceDense` (L1): smooth `c`-periodic forces with compact age/`η` support are dense in `H`.
* `SmoothForceClassical` (L2): for such `g`, `R₀ g` has a representative in the energy class
  (Duhamel formula `B0225.R0_Ms_ae` + heat-kernel regularity).
* `SmoothForcePairing` (L3): the coercive pairing with `s^{-1/2} b̄`, in Cauchy-ready form
  `‖b - b'‖²_H + ‖∇(b - b')‖²_{H_T} ≤ (κ⁻² + (νκ)⁻¹)‖g - g'‖²_H`, `κ = Re μ + 1/4`
  (from `κ A + ν B ≤ √(Gn · A)`, `A = ‖Δb‖²_H`, `B = ‖∇Δb‖²_{H_T}`).
* `HspNormLintegral` (L4): the `Hsp c` norm is the `ageμ c (-3/2)` `L²` norm.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (vnorm2 tnorm2)

/-- **Smooth compactly supported force** in `Hsp c`: an a.e. representative `F` that is `C^∞` on
`ℝ³`, `c`-periodic in `q`, supported in `s ∈ [s₀, s₁]`, `|η| ≤ L` with `s₀ > 0`
(source 1684-1689: the classical case of the flat equation). -/
def IsSmoothForce (c : ℝ) (g : Hsp c) : Prop :=
  ∃ F : Chart → Fin 2 → ℝ, (∀ i, ContDiff ℝ ∞ fun p => F p i) ∧
    (∀ s q η, F (s, (q + c, η)) = F (s, (q, η))) ∧
    (∃ s0 s1 L : ℝ, 0 < s0 ∧ ∀ p, F p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) ∧
    ∀ᵐ p ∂(ageμ c (-3 / 2)), ∀ i, NearInst.velC g p i = ((F p i : ℝ) : ℂ)

/-- **L1** Density of smooth compactly supported forces in `H` (source 1678, 1684-1689). -/
def SmoothForceDense : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (h : Hsp c) (ε : ℝ), 0 < ε → ∃ g : Hsp c, IsSmoothForce c g ∧ ‖h - g‖ < ε

/-- **L2** For a smooth compactly supported force `g`, the free body column `R₀ g` has a classical
representative in the energy class (source 1650-1656, 1684-1689; Duhamel formula
`B0225.R0_Ms_ae`, `R0_apply`, `R0_ae_eq`: `R₀(μ) M_s g(s) = ∫₀^s (σ/s)^μ e^{ν(s-σ)Δ} g(σ) dσ`;
the integral is smooth for `s > 0`, divergence free, with `b ∈ H` at zero entrance). -/
def SmoothForceClassical : Prop :=
  ∀ (c ν μ : ℝ) (hc : 0 < c), 0 < ν → 0 < μ + 1 / 4 → ∀ R0 : Hsp c →L[ℝ] Hsp c,
    NearInst.IsBodyTransport R0 (UnforcedLeray.Short.PartIIa.T0flat hc ν (μ : ℂ)) →
    ∀ g : Hsp c, IsSmoothForce c g →
      ∃ (b : Chart → Fin 2 → ℂ) (G : Chart → Fin 2 → Fin 2 → ℂ),
        IsEnergyField c b G ∧ b =ᵐ[ageμ c (-3 / 2)] NearInst.velC (R0 g)

/-- **L3** Coercive pairing with `s^{-1/2} b̄` (source 1684-1689), for the difference of the
columns of two smooth forces (linearity of `R₀`; the energy fields subtract, `IsEnergyField.sub`):
`‖b-b'‖²_H + ‖G-G'‖²_{H_T} ≤ (κ⁻² + (νκ)⁻¹) ‖g-g'‖²_H`, `κ = Re μ + 1/4`. -/
def SmoothForcePairing : Prop :=
  ∀ (c ν μ : ℝ) (hc : 0 < c), 0 < ν → 0 < μ + 1 / 4 → ∀ R0 : Hsp c →L[ℝ] Hsp c,
    NearInst.IsBodyTransport R0 (UnforcedLeray.Short.PartIIa.T0flat hc ν (μ : ℂ)) →
    ∀ (g g' : Hsp c), IsSmoothForce c g → IsSmoothForce c g' →
    ∀ (b b' : Chart → Fin 2 → ℂ) (G G' : Chart → Fin 2 → Fin 2 → ℂ),
      IsEnergyField c b G → IsEnergyField c b' G' →
      b =ᵐ[ageμ c (-3 / 2)] NearInst.velC (R0 g) → b' =ᵐ[ageμ c (-3 / 2)] NearInst.velC (R0 g') →
      ∫⁻ p, ENNReal.ofReal (vnorm2 (b p - b' p) ^ 2) ∂(ageμ c (-3 / 2)) +
        ∫⁻ p, ENNReal.ofReal (tnorm2 (G p - G' p) ^ 2) ∂(ageμ c (-1 / 2)) ≤
      ENNReal.ofReal (1 / (μ + 1 / 4) ^ 2 + 1 / (ν * (μ + 1 / 4))) *
        ∫⁻ p, ENNReal.ofReal (vnorm2 (NearInst.velC g p - NearInst.velC g' p) ^ 2)
          ∂(ageμ c (-3 / 2))

/-- **L4** The norm of `Hsp c` is the `L²(ageμ c (-3/2))` norm of the complexified field. -/
def HspNormLintegral : Prop :=
  ∀ (c : ℝ) (u v : Hsp c),
    ∫⁻ p, ENNReal.ofReal (vnorm2 (NearInst.velC u p - NearInst.velC v p) ^ 2) ∂(ageμ c (-3 / 2)) =
      ENNReal.ofReal (‖u - v‖ ^ 2)

theorem bodyColumnSmoothSeq_of (h1 : SmoothForceDense) (h2 : SmoothForceClassical)
    (h3 : SmoothForcePairing) (h4 : HspNormLintegral) : BodyColumnSmoothSeq := by
  intro c ν μ hc hν hμ R0 hR h
  have hδ : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => by positivity
  choose g hg hgd using fun k : ℕ => h1 c hc h (1 / ((k : ℝ) + 1)) (hδ k)
  choose b G hE hb using fun k : ℕ => h2 c ν μ hc hν hμ R0 hR (g k) (hg k)
  refine ⟨b, G, hE, ?_, ?_⟩
  · intro ε hε
    set Cr : ℝ := 1 / (μ + 1 / 4) ^ 2 + 1 / (ν * (μ + 1 / 4)) with hCr
    have hCrpos : 0 < Cr := by positivity
    obtain ⟨N, hN⟩ := exists_nat_gt (4 * Cr / ε)
    refine ⟨N, fun m hm n hn => ?_⟩
    have key := h3 c ν μ hc hν hμ R0 hR (g m) (g n) (hg m) (hg n) (b m) (b n) (G m) (G n)
      (hE m) (hE n) (hb m) (hb n)
    rw [h4 c (g m) (g n), ← ENNReal.ofReal_mul hCrpos.le] at key
    refine lt_of_le_of_lt key ((ENNReal.ofReal_lt_ofReal_iff hε).2 ?_)
    have hm' : (1 : ℝ) / ((m : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hm 1)
    have hn' : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)
    have hnorm : ‖g m - g n‖ ≤ 2 / ((N : ℝ) + 1) := by
      have e : g m - g n = (h - g n) - (h - g m) := by abel
      rw [e]
      have := norm_sub_le (h - g n) (h - g m)
      have h5 := hgd m
      have h6 := hgd n
      have : (2 : ℝ) / ((N : ℝ) + 1) = 1 / ((N : ℝ) + 1) + 1 / ((N : ℝ) + 1) := by ring
      linarith
    have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hNε : 4 * Cr / ε < (N : ℝ) + 1 := by linarith
    have hx0 : 0 ≤ ‖g m - g n‖ := norm_nonneg _
    have hsq : ‖g m - g n‖ ^ 2 ≤ (2 / ((N : ℝ) + 1)) ^ 2 := pow_le_pow_left₀ hx0 hnorm 2
    have hle1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      linarith
    have h7 : (2 / ((N : ℝ) + 1)) ^ 2 ≤ 4 / ((N : ℝ) + 1) := by
      rw [div_pow, div_le_div_iff₀ (by positivity) hN1]
      nlinarith
    have h8 : Cr * (4 / ((N : ℝ) + 1)) < ε := by
      have : 4 * Cr / ε < (N : ℝ) + 1 := hNε
      rw [div_lt_iff₀ hε] at this
      rw [← mul_div_assoc, div_lt_iff₀ hN1]
      linarith
    calc Cr * ‖g m - g n‖ ^ 2 ≤ Cr * (4 / ((N : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left (hsq.trans h7) hCrpos.le
      _ < ε := h8
  · have hup : Tendsto (fun k : ℕ => ENNReal.ofReal ((‖R0‖ * (1 / ((k : ℝ) + 1))) ^ 2)) atTop
        (𝓝 0) := by
      have h0 : Tendsto (fun k : ℕ => (‖R0‖ * (1 / ((k : ℝ) + 1))) ^ 2) atTop (𝓝 0) := by
        have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ‖R0‖
        simpa using this.pow 2
      simpa using ENNReal.tendsto_ofReal h0
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun k => zero_le)
      (fun k => ?_)
    have e1 : ∫⁻ p, ENNReal.ofReal (vnorm2 (b k p - NearInst.velC (R0 h) p) ^ 2)
          ∂(ageμ c (-3 / 2)) =
        ∫⁻ p, ENNReal.ofReal (vnorm2 (NearInst.velC (R0 (g k)) p - NearInst.velC (R0 h) p) ^ 2)
          ∂(ageμ c (-3 / 2)) := by
      refine lintegral_congr_ae ?_
      filter_upwards [hb k] with p hp
      rw [hp]
    rw [e1, h4 c (R0 (g k)) (R0 h)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hn : ‖R0 (g k) - R0 h‖ ≤ ‖R0‖ * (1 / ((k : ℝ) + 1)) := by
      rw [← map_sub]
      calc ‖R0 (g k - h)‖ ≤ ‖R0‖ * ‖g k - h‖ := R0.le_opNorm _
        _ ≤ ‖R0‖ * (1 / ((k : ℝ) + 1)) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          rw [norm_sub_rev]; exact (hgd k).le
    exact pow_le_pow_left₀ (norm_nonneg _) hn 2

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
