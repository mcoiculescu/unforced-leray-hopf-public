import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_4
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.EnergyGradUnique

/-!
# `SmoothForcePairing` (L3) from the classical pairing on the smooth representative
(helper of `PartIII-b:C/flatset/col/7/1/1/3`)

Source of record `the November 2 reference manuscript` 1684-1689: the flat
equation `(∂_s + μ/s - νΔ)b = P₀ g` is paired with `s^{-1/2} b̄`; the coercive constant is
`κ = Re μ + 1/4`.

* (a) `IsSmoothForce.sub` : the difference of two smooth forces is a smooth force.
* (b) the weak gradient `G - G'` of the difference energy field `b - b'` is the classical
  gradient `cellGrad u` of the smooth representative `u` of `R₀ (g - g')` (`sfcRep`, the energy
  class from `sfcGradMeas`, `sfcEnergy`, `sfcZero`, `sfcDiv`, `sfcWeak`; a.e. uniqueness of weak
  gradients `PartIIa.N01.energyGradUnique`).
* (c) `SmoothRepPairing` : the classical pairing inequality `κ A + ν B ≤ √(Gn · A)` for the smooth
  representative (`A = ‖u‖²_H`, `B = ‖∇u‖²_{H_T}`, `Gn = ‖g‖²_H`).  Not proved here.
* `pairing_algebra` : `κ A + ν B ≤ √(Gn A)` gives `A ≤ Gn/κ²`, `B ≤ Gn/(νκ)`.
* `smoothForcePairing_of` : `SmoothRepPairing → SmoothForcePairing`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (vnorm2 tnorm2)

/-- **(c) Classical pairing on the smooth representative** (source 1684-1689).  For a smooth
compactly supported force `g` (`ClassicalCtx`), the smooth representative `b` of `R₀ g` (the
Duhamel integral `∫₀^s (σ/s)^μ e^{ν(s-σ)Δ} G(σ) dσ` of the `H_g`-density `G = P₀g/s`,
`DuhamelBridge`) solves `∂_s b + (μ/s) b - νΔb = G` classically for `s > 0` and vanishes for
`s < s₀`.  Pair with `s^{-1/2} b̄` over `(0,∞) × cell` with cutoffs `θ(s)` (decreasing) and
`χ_R(η)`: integration by parts in `s` (the `θ'` term has the good sign, `b = 0` near `s = 0`),
in `q` (periodicity) and in `η` (the `χ_R'` term tends to `0` by `sfcEnergy`), then `R → ∞`,
`S → ∞` by monotone convergence.  With `‖P₀ g‖_H ≤ ‖g‖_H` and Cauchy-Schwarz:
`κ ‖b‖²_H + ν ‖∇b‖²_{H_T} ≤ Re ⟨P₀ g, b⟩_H ≤ √(‖g‖²_H ‖b‖²_H)`, `κ = μ + 1/4`. -/
def SmoothRepPairing : Prop :=
  ∀ (c ν μ : ℝ) (hc : 0 < c) (R0 : Hsp c →L[ℝ] Hsp c) (g : Hsp c), ClassicalCtx c ν μ hc R0 g →
    ∀ b : Chart → Fin 2 → ℂ, SmoothRep c b → b =ᵐ[ageμ c (-3 / 2)] NearInst.velC (R0 g) →
      ENNReal.ofReal (μ + 1 / 4) * (∫⁻ p, ENNReal.ofReal (vnorm2 (b p) ^ 2) ∂(ageμ c (-3 / 2))) +
          ENNReal.ofReal ν *
            (∫⁻ p, ENNReal.ofReal (tnorm2 (fun i j => cellGrad b p i j) ^ 2) ∂(ageμ c (-1 / 2))) ≤
        ((∫⁻ p, ENNReal.ofReal (vnorm2 (NearInst.velC g p) ^ 2) ∂(ageμ c (-3 / 2))) *
          (∫⁻ p, ENNReal.ofReal (vnorm2 (b p) ^ 2) ∂(ageμ c (-3 / 2)))) ^ (1 / 2 : ℝ)

/-- The complexified field of a difference is the difference of the complexified fields. -/
theorem sfp_velC_sub_ae {c : ℝ} (u v : Hsp c) :
    NearInst.velC ((u - v : Hsp c) : Chart → EuclideanSpace ℝ (Fin 2)) =ᵐ[ageμ c (-3 / 2)]
      fun p => NearInst.velC u p - NearInst.velC v p := by
  filter_upwards [Lp.coeFn_sub u v] with p hp
  funext i
  simp only [NearInst.velC]
  rw [hp]
  simp [NearInst.velC]

/-- **(a)** The difference of two smooth compactly supported forces is one. -/
theorem IsSmoothForce.sub {c : ℝ} {g g' : Hsp c} (hg : IsSmoothForce c g)
    (hg' : IsSmoothForce c g') : IsSmoothForce c (g - g') := by
  obtain ⟨F, hFs, hFp, ⟨s0, s1, L, hs0, hFsupp⟩, hFae⟩ := hg
  obtain ⟨F', hFs', hFp', ⟨t0, t1, L', ht0, hFsupp'⟩, hFae'⟩ := hg'
  refine ⟨fun p => F p - F' p, fun i => (hFs i).sub (hFs' i), fun s q η => ?_,
    ⟨min s0 t0, max s1 t1, max L L', lt_min hs0 ht0, fun p hp => ?_⟩, ?_⟩
  · simp only [hFp, hFp']
  · by_cases h : F p = 0
    · have h' : F' p ≠ 0 := by
        intro h'
        apply hp
        simp [h, h']
      obtain ⟨⟨h1, h2⟩, h3⟩ := hFsupp' p h'
      exact ⟨⟨le_trans (min_le_right _ _) h1, le_trans h2 (le_max_right _ _)⟩,
        le_trans h3 (le_max_right _ _)⟩
    · obtain ⟨⟨h1, h2⟩, h3⟩ := hFsupp p h
      exact ⟨⟨le_trans (min_le_left _ _) h1, le_trans h2 (le_max_left _ _)⟩,
        le_trans h3 (le_max_left _ _)⟩
  · filter_upwards [hFae, hFae', sfp_velC_sub_ae g g'] with p h1 h2 h3
    intro i
    rw [h3]
    simp [h1 i, h2 i]

/-- The energy class is contained in the a.e. energy class. -/
theorem sfp_toAE {c : ℝ} {b : Chart → Fin 2 → ℂ} {G : Chart → Fin 2 → Fin 2 → ℂ}
    (h : IsEnergyField c b G) : IsEnergyFieldAE c b G :=
  ⟨h.measurable, h.gradMeasurable, h.energyLoc, h.zeroEntrance,
    Eventually.of_forall fun s hs => h.divFree s hs,
    Eventually.of_forall fun s hs => h.weakGrad s hs⟩

/-- The smooth representative with its classical gradient is an energy field
(the clauses of `smoothForceClassical_of`). -/
theorem sfp_smoothRep_energyField {c ν μ : ℝ} {hc : 0 < c} {R0 : Hsp c →L[ℝ] Hsp c}
    {g : Hsp c} (hctx : ClassicalCtx c ν μ hc R0 g) {u : Chart → Fin 2 → ℂ}
    (hu : SmoothRep c u) (hue : u =ᵐ[ageμ c (-3 / 2)] NearInst.velC (R0 g)) :
    IsEnergyField c u (fun p i j => cellGrad u p i j) :=
  { measurable := hu.1
    gradMeasurable := sfcGradMeas c u hu
    energyLoc := sfcEnergy c ν μ hc R0 g hctx u hu hue
    zeroEntrance := sfcZero c ν μ hc R0 g hctx u hu hue
    divFree := sfcDiv c ν μ hc R0 g hctx u hu hue
    weakGrad := sfcWeak c u hu }

/-- **Algebra of the pairing**: `κ A + ν B ≤ √(Gn A)` with `A, Gn` finite gives
`A + B ≤ (κ⁻² + (νκ)⁻¹) Gn` (`A ≤ Gn/κ²`, `√(Gn A) ≤ Gn/κ`, `ν B ≤ √(Gn A)`). -/
theorem pairing_algebra {κ ν : ℝ} (hκ : 0 < κ) (hν : 0 < ν) {A B Gn : ℝ≥0∞} (hA : A ≠ ⊤)
    (hG : Gn ≠ ⊤) (h : ENNReal.ofReal κ * A + ENNReal.ofReal ν * B ≤ (Gn * A) ^ (1 / 2 : ℝ)) :
    A + B ≤ ENNReal.ofReal (1 / κ ^ 2 + 1 / (ν * κ)) * Gn := by
  have hGA : (Gn * A) ^ (1 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ENNReal.mul_ne_top hG hA)
  have hνpos : ENNReal.ofReal ν ≠ 0 := by simpa using hν
  have hB : B ≠ ⊤ := by
    intro hB
    rw [hB, ENNReal.mul_top hνpos, add_top, top_le_iff] at h
    exact hGA h
  have hL : ENNReal.ofReal κ * A + ENNReal.ofReal ν * B ≠ ⊤ := ne_top_of_le_ne_top hGA h
  have hr := (ENNReal.toReal_le_toReal hL hGA).2 h
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hκ.le, ENNReal.toReal_ofReal hν.le, ← ENNReal.toReal_rpow,
    ENNReal.toReal_mul, ← Real.sqrt_eq_rpow] at hr
  set a := A.toReal with ha_def
  set b := B.toReal with hb_def
  set gn := Gn.toReal with hgn_def
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have hb0 : 0 ≤ b := ENNReal.toReal_nonneg
  have hg0 : 0 ≤ gn := ENNReal.toReal_nonneg
  set r := Real.sqrt (gn * a) with hr_def
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r ^ 2 = gn * a := Real.sq_sqrt (mul_nonneg hg0 ha0)
  have hκa : κ * a ≤ r := by nlinarith
  -- `A ≤ Gn/κ²`
  have haκ : κ ^ 2 * a ≤ gn := by
    rcases eq_or_lt_of_le ha0 with h0 | hpos
    · rw [← h0]; simp [hg0]
    · have h1 : (κ * a) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (by positivity) hκa 2
      rw [hrsq] at h1
      have h2 : a * (κ ^ 2 * a) ≤ a * gn := by nlinarith
      exact le_of_mul_le_mul_left h2 hpos
  -- `√(Gn A) ≤ Gn/κ`
  have hrκ : r ≤ gn / κ := by
    have h1 : gn * a ≤ (gn / κ) ^ 2 := by
      rw [div_pow]
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    calc r = Real.sqrt (gn * a) := rfl
      _ ≤ Real.sqrt ((gn / κ) ^ 2) := Real.sqrt_le_sqrt h1
      _ = gn / κ := Real.sqrt_sq (by positivity)
  have hνb : ν * b ≤ gn / κ := by nlinarith
  have ha' : a ≤ gn / κ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have hb' : b ≤ gn / (ν * κ) := by
    rw [le_div_iff₀ (by positivity)]
    have : ν * b * κ ≤ gn := by
      have := mul_le_mul_of_nonneg_right hνb hκ.le
      rwa [div_mul_cancel₀ _ hκ.ne'] at this
    linarith
  have hsum : a + b ≤ (1 / κ ^ 2 + 1 / (ν * κ)) * gn := by
    have e : (1 / κ ^ 2 + 1 / (ν * κ)) * gn = gn / κ ^ 2 + gn / (ν * κ) := by ring
    rw [e]; linarith
  rw [← ENNReal.ofReal_toReal hA, ← ENNReal.ofReal_toReal hB, ← ENNReal.ofReal_toReal hG,
    ← ENNReal.ofReal_add ha0 hb0, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hsum

/-- **`SmoothForcePairing` (L3) from the classical pairing (c)** (source 1684-1689). -/
theorem smoothForcePairing_of (hC : SmoothRepPairing) : SmoothForcePairing := by
  intro c ν μ hc hν hμ R0 hR g g' hg hg' b b' G G' hE hE' hb hb'
  have hctx : ClassicalCtx c ν μ hc R0 (g - g') := ⟨hν, hμ, hR, hg.sub hg'⟩
  obtain ⟨u, hu, hue⟩ := sfcRep c ν μ hc R0 (g - g') hctx
  have hEu := sfp_smoothRep_energyField hctx hu hue
  -- `b - b'` represents `R₀ (g - g')`
  have hR0 : NearInst.velC (R0 (g - g')) =ᵐ[ageμ c (-3 / 2)]
      fun p => NearInst.velC (R0 g) p - NearInst.velC (R0 g') p := by
    have e : R0 (g - g') = R0 g - R0 g' := map_sub R0 g g'
    rw [e]; exact sfp_velC_sub_ae (R0 g) (R0 g')
  have hbu : (fun p i => b p i - b' p i) =ᵐ[ageμ c (-3 / 2)] u := by
    filter_upwards [hb, hb', hR0, hue] with p e1 e2 e3 e4
    rw [e4, e3, e1, e2]
    rfl
  -- (b) the weak gradient of the difference is the classical gradient
  have hGu : (fun p i j => G p i j - G' p i j) =ᵐ[ageμ c (-1 / 2)]
      (fun p i j => cellGrad u p i j) :=
    UnforcedLeray.Short.PartIIa.N01.energyGradUnique c hc _ _ _ _ (sfp_toAE (hE.sub hE'))
      (sfp_toAE hEu) hbu
  -- (c)
  have key := hC c ν μ hc R0 (g - g') hctx u hu hue
  have eA : ∫⁻ p, ENNReal.ofReal (vnorm2 (u p) ^ 2) ∂(ageμ c (-3 / 2)) =
      ∫⁻ p, ENNReal.ofReal (vnorm2 (b p - b' p) ^ 2) ∂(ageμ c (-3 / 2)) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hbu] with p hp
    have hp' : b p - b' p = u p := hp
    rw [hp']
  have eB : ∫⁻ p, ENNReal.ofReal (tnorm2 (fun i j => cellGrad u p i j) ^ 2) ∂(ageμ c (-1 / 2)) =
      ∫⁻ p, ENNReal.ofReal (tnorm2 (G p - G' p) ^ 2) ∂(ageμ c (-1 / 2)) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hGu] with p hp
    have hp' : G p - G' p = fun i j => cellGrad u p i j := hp
    rw [hp']
  have eG : ∫⁻ p, ENNReal.ofReal (vnorm2 (NearInst.velC ((g - g' : Hsp c) :
      Chart → EuclideanSpace ℝ (Fin 2)) p) ^ 2) ∂(ageμ c (-3 / 2)) =
      ∫⁻ p, ENNReal.ofReal (vnorm2 (NearInst.velC g p - NearInst.velC g' p) ^ 2)
        ∂(ageμ c (-3 / 2)) := by
    refine lintegral_congr_ae ?_
    filter_upwards [sfp_velC_sub_ae g g'] with p hp
    rw [hp]
  rw [eA, eB, eG] at key
  have hAfin : ∫⁻ p, ENNReal.ofReal (vnorm2 (b p - b' p) ^ 2) ∂(ageμ c (-3 / 2)) ≠ ⊤ := by
    have e : ∫⁻ p, ENNReal.ofReal (vnorm2 (b p - b' p) ^ 2) ∂(ageμ c (-3 / 2)) =
        ∫⁻ p, ENNReal.ofReal (vnorm2 (NearInst.velC (R0 g) p - NearInst.velC (R0 g') p) ^ 2)
          ∂(ageμ c (-3 / 2)) := by
      refine lintegral_congr_ae ?_
      filter_upwards [hb, hb'] with p e1 e2
      rw [e1, e2]
    rw [e, hspNormLintegral c (R0 g) (R0 g')]
    exact ENNReal.ofReal_ne_top
  have hGfin : ∫⁻ p, ENNReal.ofReal (vnorm2 (NearInst.velC g p - NearInst.velC g' p) ^ 2)
      ∂(ageμ c (-3 / 2)) ≠ ⊤ := by
    rw [hspNormLintegral c g g']
    exact ENNReal.ofReal_ne_top
  exact pairing_algebra hμ hν hAfin hGfin key

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
