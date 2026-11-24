import UnforcedLeray.Short.PartIIa.Sub.N01.Reduction

/-!
# `PartII-a:N01/12` — the dissipation bound

Proves `dissipationBound_of` (target `DissipationBound`, `Sub/N01/Defs.lean`): for a smooth complex
tensor test `M = tv4 m₁ + i tv4 m₂` (`TensorTestReIm`), the phase lift `U` of `T_ε(s div_ε M)` has a
distributional gradient in `Y₂` with `∑_j ‖g_j‖ ≤ 12 ν⁻¹ ‖F‖_{H_T}`.

Route: for a real test `m` (`dissRealGrad`), `U(liftVec(Teps G)) = κ • S X` with `κ = (√2π)⁻¹√(Pε)`
(`phaseLift_liftVec_Teps`), `S` the weak stress inverse of `weakStressExists`, whose gradient clause
gives `√(∑‖g_j‖²) ≤ ν⁻¹‖X‖`; `CartLiftNorm` gives `κ‖X‖ ≤ √2‖F‖`.  The complex test splits as in
`epsSmoothBound_of`, and `∑_j ‖g_j‖ ≤ 3√(∑‖g_j‖²)` on `Fin 3`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp
open UnforcedLeray.B0220 (Profile HSpace measureH)
open UnforcedLeray.B0223 (MeridC SpaceC)
open UnforcedLeray.Short.PartIIIb.Concrete (Chart Ten3)
open UnforcedLeray.Short.PartIIIb.NearInst (tv4 cartLift)

/-- **The real-test gradient bound**: for a real smooth tensor test `m` with `F =ᵐ 𝒯 m`, the phase
lift of `T_ε G` (with `G = s div_ε m`) has a gradient in `Y₂` with `∑_j ‖g_j‖ ≤ 3 ν⁻¹√2 ‖F‖`. -/
theorem dissRealGrad (hS : PhaseSemigroupConj) (hL : PhaseLerayConj)
    (hD : PhaseDivScale) (hR : CartLiftRows) (hN : CartLiftNorm)
    {ν ε c P : ℝ} [Fact (0 < P)] (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c)
    (hP1 : P ≤ 1) {μ : ℂ} (hγ : 0 < μ.re + 1 / 4)
    {U : B0223.X SpaceC P →ₗᵢ[ℂ] Yq P 2} (hU : IsPhaseLift ε P U)
    (m : Chart → Ten3) (hm : IsTensorTest c (fun p => tv4 (m p)))
    (F : HTSpace c) (hF : (F : Profile → TensorVal) =ᵐ[measureHT c] (fun p => tv4 (m p)))
    (G : HSpace c MeridC)
    (hG : (G : Profile → MeridC) =ᵐ[measureH c]
      (fun p => (p.1 : ℂ) • divEps ε (fun q => tv4 (m q)) p)) :
    ∃ g : Fin 3 → Yq P 2,
      HasGrad (U (B0223.liftVec hε hc hP (Teps hν hε hc hP μ G))) g ∧
        ∑ j, ‖g j‖ ≤ 3 * (ν⁻¹ * (Real.sqrt 2 * ‖F‖)) := by
  obtain ⟨S, hSw, hSb⟩ := weakStressExists P hP1 ν hν μ hγ
  obtain ⟨X, hX, hEq⟩ :=
    phaseLift_liftVec_Teps hS hL hD hR hν hε hc hP hP1 hγ hU S hSw m hm G hG
  obtain ⟨-, gS, hgS, hgSb⟩ := hSb X
  have hκ0 : 0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (P * ε) := by positivity
  have hpos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  refine ⟨fun j => (((Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (P * ε) : ℝ) : ℂ) • gS j, ?_, ?_⟩
  · rw [hEq]
    unfold HasGrad at hgS ⊢
    intro j
    exact (hgS j).smul _
  · dsimp only
    have hκ : ∑ j, ‖(((Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (P * ε) : ℝ) : ℂ) • gS j‖ =
        ((Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (P * ε)) * ∑ j, ‖gS j‖ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hκ0]
    have hXn : (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (P * ε) * ‖(X : Y2Sym P)‖ ≤
        Real.sqrt 2 * ‖F‖ := by
      have h1 := hN ε c P hε hc hP m hm F hF
      rw [← hX] at h1
      calc (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (P * ε) * ‖(X : Y2Sym P)‖
          = (Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt (P * ε) * ‖(X : Y2Sym P)‖) := by ring
        _ ≤ (Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt (2 * Real.pi) * Real.sqrt 2 * ‖F‖) :=
            mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hpos.le)
        _ = Real.sqrt 2 * ‖F‖ := by field_simp
    have hsq : ∀ j, ‖gS j‖ ≤ Real.sqrt (∑ k, ‖gS k‖ ^ 2) := by
      intro j
      calc ‖gS j‖ = Real.sqrt (‖gS j‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt (∑ k, ‖gS k‖ ^ 2) :=
          Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun k => ‖gS k‖ ^ 2)
            (fun k _ => sq_nonneg _) (Finset.mem_univ j))
    have hs3 : ∑ j, ‖gS j‖ ≤ 3 * Real.sqrt (∑ k, ‖gS k‖ ^ 2) := by
      rw [Fin.sum_univ_three]
      have h0 := hsq 0
      have h1 := hsq 1
      have h2 := hsq 2
      linarith
    rw [hκ]
    calc (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (P * ε) * ∑ j, ‖gS j‖
        ≤ (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (P * ε) * (3 * (ν⁻¹ * ‖(X : Y2Sym P)‖)) := by
          apply mul_le_mul_of_nonneg_left _ hκ0
          have hR3 : 3 * Real.sqrt (∑ k, ‖gS k‖ ^ 2) ≤ 3 * (ν⁻¹ * ‖(X : Y2Sym P)‖) := by
            linarith [hgSb]
          exact hs3.trans hR3
      _ = 3 * (ν⁻¹ * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (P * ε) * ‖(X : Y2Sym P)‖)) := by
          ring
      _ ≤ 3 * (ν⁻¹ * (Real.sqrt 2 * ‖F‖)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_left hXn (inv_nonneg.2 hν.le)

/-- **`PartII-a:N01/12` — the dissipation bound** (lines 1679-1683, 1562-1564), from the six
hypotheses of the leaf statements; the constant `C = 12`. -/
theorem dissipationBound_of (h2 : PhaseSemigroupConj) (h3 : PhaseLerayConj) (h4 : PhaseDivScale)
    (h5 : CartLiftRows) (h6 : CartLiftNorm) (h7 : TensorTestReIm) : DissipationBound := by
  unfold DissipationBound
  refine ⟨12, by norm_num, ?_⟩
  intro ν ε c P _ hν hε hc hP hP1 μ hγ U hU M hM F G hF hG
  obtain ⟨m₁, m₂, hm₁, hm₂, -, hn₁, hn₂, hdiv⟩ := h7 c hc M hM
  have hMLp : MemLp M 2 (measureHT c) := (Lp.memLp F).ae_eq hF
  have hL₁ : MemLp (fun p => tv4 (m₁ p)) 2 (measureHT c) :=
    hMLp.of_le hm₁.smooth.continuous.aestronglyMeasurable (Eventually.of_forall hn₁)
  have hL₂ : MemLp (fun p => tv4 (m₂ p)) 2 (measureHT c) :=
    hMLp.of_le hm₂.smooth.continuous.aestronglyMeasurable (Eventually.of_forall hn₂)
  obtain ⟨F₁, F₂, hF₁, hF₂, hF₁n, hF₂n⟩ : ∃ F₁ F₂ : HTSpace c,
      (F₁ : Profile → TensorVal) =ᵐ[measureHT c] (fun p => tv4 (m₁ p)) ∧
      (F₂ : Profile → TensorVal) =ᵐ[measureHT c] (fun p => tv4 (m₂ p)) ∧
      ‖F₁‖ ≤ ‖F‖ ∧ ‖F₂‖ ≤ ‖F‖ := by
    refine ⟨hL₁.toLp _, hL₂.toLp _, hL₁.coeFn_toLp, hL₂.coeFn_toLp, ?_, ?_⟩
    · refine Lp.norm_le_norm_of_ae_le ?_
      filter_upwards [hL₁.coeFn_toLp, hF] with p h1 h2
      rw [h1, h2]
      exact hn₁ p
    · refine Lp.norm_le_norm_of_ae_le ?_
      filter_upwards [hL₂.coeFn_toLp, hF] with p h1 h2
      rw [h1, h2]
      exact hn₂ p
  have hG₁L := UnforcedLeray.Short.PartIIIb.NearInst.Masked.tensorTestDivMem c ε hc _ hm₁
  have hG₂L := UnforcedLeray.Short.PartIIIb.NearInst.Masked.tensorTestDivMem c ε hc _ hm₂
  obtain ⟨G₁, G₂, hG₁, hG₂, hGsplit⟩ : ∃ G₁ G₂ : HSpace c MeridC,
      (G₁ : Profile → MeridC) =ᵐ[measureH c]
        (fun p => (p.1 : ℂ) • divEps ε (fun q => tv4 (m₁ q)) p) ∧
      (G₂ : Profile → MeridC) =ᵐ[measureH c]
        (fun p => (p.1 : ℂ) • divEps ε (fun q => tv4 (m₂ q)) p) ∧
      G = G₁ + Complex.I • G₂ := by
    refine ⟨hG₁L.toLp _, hG₂L.toLp _, hG₁L.coeFn_toLp, hG₂L.coeFn_toLp, ?_⟩
    apply Lp.ext
    filter_upwards [hG, hG₁L.coeFn_toLp, hG₂L.coeFn_toLp,
      Lp.coeFn_add (hG₁L.toLp _) (Complex.I • hG₂L.toLp _),
      Lp.coeFn_smul Complex.I (hG₂L.toLp _)] with p h h1 h2 h3 h4
    rw [h, h3, Pi.add_apply, h4, Pi.smul_apply, h1, h2, hdiv ε p, smul_add,
      smul_comm (p.1 : ℂ) Complex.I]
  subst hGsplit
  obtain ⟨g₁, hg₁, hb₁⟩ :=
    dissRealGrad h2 h3 h4 h5 h6 hν hε hc hP hP1 hγ hU m₁ hm₁ F₁ hF₁ G₁ hG₁
  obtain ⟨g₂, hg₂, hb₂⟩ :=
    dissRealGrad h2 h3 h4 h5 h6 hν hε hc hP hP1 hγ hU m₂ hm₂ F₂ hF₂ G₂ hG₂
  simp only [map_add, map_smul]
  refine ⟨fun j => g₁ j + Complex.I • g₂ j, ?_, ?_⟩
  · unfold HasGrad at hg₁ hg₂ ⊢
    intro j
    exact (hg₁ j).add ((hg₂ j).smul Complex.I)
  · dsimp only
    have hterm : ∀ j, ‖g₁ j + Complex.I • g₂ j‖ ≤ ‖g₁ j‖ + ‖g₂ j‖ := fun j => by
      calc ‖g₁ j + Complex.I • g₂ j‖ ≤ ‖g₁ j‖ + ‖Complex.I • g₂ j‖ := norm_add_le _ _
        _ = ‖g₁ j‖ + ‖g₂ j‖ := by rw [norm_smul, Complex.norm_I, one_mul]
    have hs2 : Real.sqrt 2 ≤ 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    have hi : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    have hsum : 0 ≤ ‖F₁‖ + ‖F₂‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
    have e1 : Real.sqrt 2 * (‖F₁‖ + ‖F₂‖) ≤ 2 * (2 * ‖F‖) := by
      have := mul_le_mul_of_nonneg_right hs2 hsum
      linarith
    have e2 : ν⁻¹ * (Real.sqrt 2 * (‖F₁‖ + ‖F₂‖)) ≤ ν⁻¹ * (2 * (2 * ‖F‖)) :=
      mul_le_mul_of_nonneg_left e1 hi
    calc ∑ j, ‖g₁ j + Complex.I • g₂ j‖ ≤ ∑ j, (‖g₁ j‖ + ‖g₂ j‖) :=
          Finset.sum_le_sum (fun j _ => hterm j)
      _ = ∑ j, ‖g₁ j‖ + ∑ j, ‖g₂ j‖ := Finset.sum_add_distrib
      _ ≤ 12 * ν⁻¹ * ‖F‖ := by linarith

end UnforcedLeray.Short.PartIIa.N01
