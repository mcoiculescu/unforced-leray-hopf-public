import UnforcedLeray.Short.PartIIa.StatementsNear

/-!
# Part II-a, `near/free-comparison.tex`: composition

The last paragraph of the proof of Proposition `near:compact-free-comparison` (source lines
1824-1840): *a dual vector of unit norm is low-frequency up to an error that is small by the
local regularity; low-frequency test vectors have `H⁶` norm `≲ N⁶`; the smooth adjoint
comparison then bounds the operator by `Γ^k (N^{-1} + √ε N⁶)` (resp. `N^{-1/4} + √ε N⁶`);
choose `N = ε^{-1/14}` (resp. `ε^{-2/25}`)`. Here this is a compiled argument:

* `opNorm_of_band`: abstract Hilbert-space lemma (distance to a subspace plus adjoint bound on
  the subspace controls the operator norm),
* `arith_T`, `arith_S`: the choices of `N` and the resulting exponents `1/14`, `1/50`,
* `nearCompactFreeComparison_of_parts`: Proposition `near:compact-free-comparison` from
  `NearBandLimited` and `NearSmoothAdjointComparison`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223

/-- **Abstract lemma.** If every `A x` is within `α‖x‖` of a subspace `V` and the adjoint
satisfies `‖A* z‖ ≤ β‖z‖` for `z ∈ V`, then `‖A x‖ ≤ (2α + β)‖x‖`. -/
theorem opNorm_of_band {X K : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [CompleteSpace X] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (A : X →L[ℂ] K) (V : Submodule ℂ K) {α β : ℝ} (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β)
    (hα : ∀ x, ∃ v ∈ V, ‖A x - v‖ ≤ α * ‖x‖)
    (hβ : ∀ z ∈ V, ‖ContinuousLinearMap.adjoint A z‖ ≤ β * ‖z‖) (x : X) :
    ‖A x‖ ≤ (2 * α + β) * ‖x‖ := by
  obtain ⟨v, hv, hxv⟩ := hα x
  have h1 : inner ℂ v v = inner ℂ (A x) v - inner ℂ (A x - v) v := by rw [inner_sub_left]; ring
  have h2 : ‖inner ℂ (A x) v‖ ≤ β * ‖x‖ * ‖v‖ := by
    rw [← ContinuousLinearMap.adjoint_inner_right A x v]
    calc ‖inner ℂ x (ContinuousLinearMap.adjoint A v)‖
        ≤ ‖x‖ * ‖ContinuousLinearMap.adjoint A v‖ := norm_inner_le_norm _ _
      _ ≤ ‖x‖ * (β * ‖v‖) := mul_le_mul_of_nonneg_left (hβ v hv) (norm_nonneg _)
      _ = β * ‖x‖ * ‖v‖ := by ring
  have h3 : ‖inner ℂ (A x - v) v‖ ≤ α * ‖x‖ * ‖v‖ :=
    (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hxv (norm_nonneg _))
  have h4 : ‖v‖ ^ 2 = ‖inner ℂ v v‖ := by
    rw [inner_self_eq_norm_sq_to_K]; simp [norm_pow]
  have h5 : ‖v‖ * ‖v‖ ≤ ((α + β) * ‖x‖) * ‖v‖ := by
    calc ‖v‖ * ‖v‖ = ‖v‖ ^ 2 := by ring
      _ = ‖inner ℂ (A x) v - inner ℂ (A x - v) v‖ := by rw [h4, h1]
      _ ≤ ‖inner ℂ (A x) v‖ + ‖inner ℂ (A x - v) v‖ := norm_sub_le _ _
      _ ≤ ((α + β) * ‖x‖) * ‖v‖ := by nlinarith
  have h6 : ‖v‖ ≤ (α + β) * ‖x‖ := by
    rcases eq_or_lt_of_le (norm_nonneg v) with h | h
    · rw [← h]; positivity
    · exact le_of_mul_le_mul_right h5 h
  calc ‖A x‖ = ‖(A x - v) + v‖ := by rw [sub_add_cancel]
    _ ≤ ‖A x - v‖ + ‖v‖ := norm_add_le _ _
    _ ≤ α * ‖x‖ + (α + β) * ‖x‖ := add_le_add hxv h6
    _ = (2 * α + β) * ‖x‖ := by ring

/-- Choice `N = ε^{-1/14}`: `N ≥ 1`, `N⁻¹ = ε^{1/14}` and `√ε N⁶ = ε^{1/14}`. -/
theorem arith_T {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1) :
    1 ≤ ε ^ (-(1 / 14 : ℝ)) ∧ (ε ^ (-(1 / 14 : ℝ)))⁻¹ = ε ^ (1 / 14 : ℝ) ∧
      Real.sqrt ε * (ε ^ (-(1 / 14 : ℝ))) ^ (6 : ℕ) = ε ^ (1 / 14 : ℝ) := by
  refine ⟨Real.one_le_rpow_of_pos_of_le_one_of_nonpos h0 h1 (by norm_num), ?_, ?_⟩
  · rw [Real.rpow_neg h0.le, inv_inv]
  · rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul h0.le, ← Real.rpow_add h0]
    norm_num

/-- Choice `N = ε^{-2/25}`: `N ≥ 1`, `N^{-1/4} = ε^{1/50}` and `√ε N⁶ = ε^{1/50}`. -/
theorem arith_S {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1) :
    1 ≤ ε ^ (-(2 / 25 : ℝ)) ∧ (ε ^ (-(2 / 25 : ℝ))) ^ (-(1 / 4 : ℝ)) = ε ^ (1 / 50 : ℝ) ∧
      Real.sqrt ε * (ε ^ (-(2 / 25 : ℝ))) ^ (6 : ℕ) = ε ^ (1 / 50 : ℝ) := by
  refine ⟨Real.one_le_rpow_of_pos_of_le_one_of_nonpos h0 h1 (by norm_num), ?_, ?_⟩
  · rw [← Real.rpow_mul h0.le]; norm_num
  · rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul h0.le, ← Real.rpow_add h0]
    norm_num

theorem cNorm8_nonneg (f : Profile → ℝ) : 0 ≤ cNorm8 f :=
  Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _

theorem h6Norm_nonneg (c : ℝ) (z : Profile → MeridC) : 0 ≤ h6Norm c z :=
  Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (integral_nonneg fun _ => by positivity) _

/-- The elementary final estimate: `2·(2 C₁ G^{k₁} e) + C₂ GB^{k₂} C₁ G^{k₁} e ≤ (4C₁ + C₂C₁) G^{k₁+k₂} e`. -/
theorem arith_combine {C₁ C₂ G GB e : ℝ} {k₁ k₂ : ℕ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hG : 1 ≤ G) (hGB0 : 0 ≤ GB) (hGB : GB ≤ G) (he : 0 ≤ e) :
    2 * (2 * C₁ * G ^ k₁ * e) + C₂ * GB ^ k₂ * C₁ * G ^ k₁ * e ≤
      (4 * C₁ + C₂ * C₁) * G ^ (k₁ + k₂) * e := by
  have hG0 : 0 ≤ G := by linarith
  have e1 : G ^ k₁ ≤ G ^ (k₁ + k₂) := pow_le_pow_right₀ hG (Nat.le_add_right _ _)
  have e2 : GB ^ k₂ ≤ G ^ k₂ := pow_le_pow_left₀ hGB0 hGB _
  have e3 : GB ^ k₂ * G ^ k₁ ≤ G ^ (k₁ + k₂) := by
    calc GB ^ k₂ * G ^ k₁ ≤ G ^ k₂ * G ^ k₁ := by gcongr
      _ = G ^ (k₁ + k₂) := by rw [← pow_add, add_comm]
  have e4 : 2 * (2 * C₁ * G ^ k₁ * e) = 4 * C₁ * G ^ k₁ * e := by ring
  have e5 : C₂ * GB ^ k₂ * C₁ * G ^ k₁ * e = C₂ * C₁ * (GB ^ k₂ * G ^ k₁) * e := by ring
  rw [e4, e5]
  have f1 : 4 * C₁ * G ^ k₁ * e ≤ 4 * C₁ * G ^ (k₁ + k₂) * e := by gcongr
  have f2 : C₂ * C₁ * (GB ^ k₂ * G ^ k₁) * e ≤ C₂ * C₁ * G ^ (k₁ + k₂) * e := by gcongr
  nlinarith [f1, f2]

/-- One half (body or tensor part) of the final argument: `‖M (D₁ - D₀) x‖ ≤ (4a + b)‖x‖`
when both localised outputs are `a`-close to `V` and `V` is `b`-controlled for the adjoint. -/
theorem part_bound {X K : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [CompleteSpace X] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (Mχ : K →L[ℂ] K) (D1 D0 : X →L[ℂ] K) (V : Submodule ℂ K) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hα : ∀ x, (∃ v ∈ V, ‖Mχ (D1 x) - v‖ ≤ a * ‖x‖) ∧ (∃ v ∈ V, ‖Mχ (D0 x) - v‖ ≤ a * ‖x‖))
    (hβ : ∀ z ∈ V, ‖(ContinuousLinearMap.adjoint D1 - ContinuousLinearMap.adjoint D0)
      (ContinuousLinearMap.adjoint Mχ z)‖ ≤ b * ‖z‖) (x : X) :
    ‖Mχ ((D1 - D0) x)‖ ≤ (4 * a + b) * ‖x‖ := by
  have key := opNorm_of_band (Mχ.comp (D1 - D0)) V (α := 2 * a) (β := b) (by positivity) hb
    (fun x => by
      obtain ⟨⟨v1, hv1, h1⟩, ⟨v0, hv0, h0⟩⟩ := hα x
      refine ⟨v1 - v0, V.sub_mem hv1 hv0, ?_⟩
      have h : (Mχ.comp (D1 - D0)) x - (v1 - v0) = (Mχ (D1 x) - v1) - (Mχ (D0 x) - v0) := by
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, map_sub]
        abel
      rw [h]
      calc _ ≤ _ := norm_sub_le _ _
        _ ≤ a * ‖x‖ + a * ‖x‖ := add_le_add h1 h0
        _ = 2 * a * ‖x‖ := by ring)
    (fun z hz => by
      rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply,
        map_sub ContinuousLinearMap.adjoint D1 D0]
      exact hβ z hz) x
  calc ‖Mχ ((D1 - D0) x)‖ = ‖(Mχ.comp (D1 - D0)) x‖ := rfl
    _ ≤ (2 * (2 * a) + b) * ‖x‖ := key
    _ = (4 * a + b) * ‖x‖ := by ring

/-- Final real arithmetic of one half: with `e` the common value of the two exponent factors. -/
theorem part_final {X K : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [CompleteSpace X] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (Mχ : K →L[ℂ] K) (D1 D0 : X →L[ℂ] K) (V : Submodule ℂ K) {C₁ C₂ G GB e : ℝ} {k₁ k₂ : ℕ}
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hG1 : 1 ≤ G) (hGB0 : 0 ≤ GB) (hGBG : GB ≤ G) (he : 0 ≤ e)
    (hα : ∀ x, (∃ v ∈ V, ‖Mχ (D1 x) - v‖ ≤ C₁ * G ^ k₁ * e * ‖x‖) ∧
      (∃ v ∈ V, ‖Mχ (D0 x) - v‖ ≤ C₁ * G ^ k₁ * e * ‖x‖))
    (hβ : ∀ z ∈ V, ‖(ContinuousLinearMap.adjoint D1 - ContinuousLinearMap.adjoint D0)
      (ContinuousLinearMap.adjoint Mχ z)‖ ≤ C₂ * GB ^ k₂ * C₁ * G ^ k₁ * e * ‖z‖) (x : X) :
    ‖Mχ ((D1 - D0) x)‖ ≤ (4 * C₁ + C₂ * C₁) * G ^ (k₁ + k₂) * e * ‖x‖ := by
  have hG0 : 0 ≤ G := by linarith
  have h := part_bound Mχ D1 D0 V (a := C₁ * G ^ k₁ * e) (b := C₂ * GB ^ k₂ * C₁ * G ^ k₁ * e)
    (by positivity) (by positivity) hα hβ x
  have hc := arith_combine (k₁ := k₁) (k₂ := k₂) hC₁ hC₂ hG1 hGB0 hGBG he
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  nlinarith [hc]

/-- Arithmetic of the dual estimate: from the smooth adjoint comparison, the `H⁶` bound of the
band-limited vector and `√ε N⁶ = e`. -/
theorem beta_arith {C₁ C₂ G GB e s Nn h6 y z : ℝ} {k₁ k₂ : ℕ} (hC₂ : 0 ≤ C₂) (hGB0 : 0 ≤ GB)
    (hs : 0 ≤ s) (hz : 0 ≤ z)
    (hsa : y ≤ C₂ * GB ^ k₂ * s * h6) (h6b : h6 ≤ C₁ * G ^ k₁ * Nn * z) (hse : s * Nn = e) :
    y ≤ C₂ * GB ^ k₂ * C₁ * G ^ k₁ * e * z := by
  have h0 : 0 ≤ C₂ * GB ^ k₂ * s := by positivity
  calc y ≤ C₂ * GB ^ k₂ * s * h6 := hsa
    _ ≤ C₂ * GB ^ k₂ * s * (C₁ * G ^ k₁ * Nn * z) := mul_le_mul_of_nonneg_left h6b h0
    _ = C₂ * GB ^ k₂ * C₁ * G ^ k₁ * (s * Nn) * z := by ring
    _ = C₂ * GB ^ k₂ * C₁ * G ^ k₁ * e * z := by rw [hse]

set_option maxHeartbeats 400000 in
/-- **Proposition `near:compact-free-comparison`** (lines 1692-1722) from the local regularity
with band-limited dual vectors (`NearBandLimited`) and the smooth adjoint comparison
(`NearSmoothAdjointComparison`): the source's final paragraph, lines 1824-1840. -/
theorem nearCompactFreeComparison_of_parts (hB : NearBandLimited)
    (hA : NearSmoothAdjointComparison) : NearCompactFreeComparison := by
  obtain ⟨k₁, C₁, hC₁, hBL⟩ := hB
  obtain ⟨k₂, C₂, hC₂, hSA⟩ := hA
  refine ⟨k₁ + k₂, 4 * C₁ + C₂ * C₁, by positivity, ?_⟩
  intro ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ hχ hχ1 hm B hB' ε hε hε1 P _ hP hP1 μ hμM hμγ
  have hGB2 : 2 ≤ GammaBox ν c σ H1 L1 M γs := by
    unfold GammaBox
    have : 0 < σ⁻¹ := inv_pos.2 hσ
    have : 0 < ν⁻¹ := inv_pos.2 hν
    have : 0 < c⁻¹ := inv_pos.2 hc
    have : 0 < γs⁻¹ := inv_pos.2 hγ
    have : 0 ≤ M := (norm_nonneg μ).trans hμM
    linarith
  have hGBG : GammaBox ν c σ H1 L1 M γs ≤ Gamma ν c σ H1 L1 M γs χ χ1 := by
    unfold Gamma
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hG1 : 1 ≤ Gamma ν c σ H1 L1 M γs χ χ1 := by linarith
  have hGB0 : 0 ≤ GammaBox ν c σ H1 L1 M γs := by linarith
  have hsq : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg _
  constructor
  · -- body part, `N = ε^{-1/14}`
    intro b
    obtain ⟨hN1, hN2, hN3⟩ := arith_T hε hε1
    obtain ⟨V, hVT, -, hVz⟩ := hBL ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ hχ hχ1 hm B hB' ε hε
      hε1 P hP hP1 μ hμM hμγ (ε ^ (-(1 / 14 : ℝ))) hN1
    rw [hN2] at hVT
    refine part_final (mulChi (E := MeridC) (measureH c) χ hm hB') (Teps hν hε hc hP μ) (T0flat hc ν μ) V
      (C₁ := C₁) (C₂ := C₂) (G := Gamma ν c σ H1 L1 M γs χ χ1)
      (GB := GammaBox ν c σ H1 L1 M γs) (e := ε ^ (1 / 14 : ℝ)) (k₁ := k₁) (k₂ := k₂)
      hC₁ hC₂ hG1 hGB0 hGBG (Real.rpow_nonneg hε.le _) hVT ?_ b
    intro z hz
    obtain ⟨ζ, hζ, hbox, hae, h6⟩ := hVz z hz
    have hsa := (hSA ν c σ H1 L1 M γs hν hc hσ hσH hL1 hγ ε hε hε1 P hP hP1 μ hμM hμγ ζ
      (ContinuousLinearMap.adjoint (mulChi (E := MeridC) (measureH c) χ hm hB') z) hζ hbox hae).1
    exact beta_arith (k₁ := k₁) (k₂ := k₂) hC₂ hGB0 hsq (norm_nonneg z) hsa h6 hN3
  · -- tensor part, `N = ε^{-2/25}`
    intro Seps S0 hSe hS0 F
    obtain ⟨hN1, hN2, hN3⟩ := arith_S hε hε1
    obtain ⟨V, -, hVS, hVz⟩ := hBL ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ hχ hχ1 hm B hB' ε hε
      hε1 P hP hP1 μ hμM hμγ (ε ^ (-(2 / 25 : ℝ))) hN1
    rw [hN2] at hVS
    refine part_final (mulChi (E := MeridC) (measureH c) χ hm hB') Seps S0 V
      (C₁ := C₁) (C₂ := C₂) (G := Gamma ν c σ H1 L1 M γs χ χ1)
      (GB := GammaBox ν c σ H1 L1 M γs) (e := ε ^ (1 / 50 : ℝ)) (k₁ := k₁) (k₂ := k₂)
      hC₁ hC₂ hG1 hGB0 hGBG (Real.rpow_nonneg hε.le _) (hVS Seps S0 hSe hS0) ?_ F
    intro z hz
    obtain ⟨ζ, hζ, hbox, hae, h6⟩ := hVz z hz
    have hsa := (hSA ν c σ H1 L1 M γs hν hc hσ hσH hL1 hγ ε hε hε1 P hP hP1 μ hμM hμγ ζ
      (ContinuousLinearMap.adjoint (mulChi (E := MeridC) (measureH c) χ hm hB') z) hζ hbox hae).2
      Seps S0 hSe hS0
    exact beta_arith (k₁ := k₁) (k₂ := k₂) hC₂ hGB0 hsq (norm_nonneg z) hsa h6 hN3

end UnforcedLeray.Short.PartIIa
