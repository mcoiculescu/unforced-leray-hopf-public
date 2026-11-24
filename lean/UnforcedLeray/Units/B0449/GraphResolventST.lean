import UnforcedLeray.Units.B0449.GraphResolventComplex
import UnforcedLeray.Units.B0448.Fundamental

/-!
# ST-coordinate compact complex graph resolvent

This leaf transports the actual compact complex graph identity from ordinary product coordinates
to the Euclidean `WithLp 2` coordinates used by the heat resolvent theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

noncomputable section

open MeasureTheory SchwartzMap Set
open scoped ENNReal NNReal ContDiff SchwartzMap

namespace UnforcedLeray.B0449

open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace UnforcedLeray.B0448

variable {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- The cutoff resolvent field in the Euclidean space-time coordinates used by B0448. -/
def chartJCutoffHST (ν : ℝ) (τ₀ : ℝ) (e : CVec3) (w : Yq P q) (X : ST) : ℂ :=
  (resolventTimeCutoff (productToST.symm X).1 : ℂ) *
    dotL e (chartJ w ν τ₀ (productToST.symm X))

/-- The corresponding source field in the Euclidean space-time coordinates used by B0448. -/
def chartJCutoffFST (ν : ℝ) (τ₀ : ℝ) (e : CVec3) (w b a : Yq P q) (X : ST) : ℂ :=
  let p := productToST.symm X
  (resolventTimeCutoffDeriv p.1 : ℂ) * dotL e (chartJ w ν τ₀ p) +
    (resolventTimeCutoff p.1 : ℂ) * dotL e (chartJ b ν τ₀ p) -
    (resolventTimeCutoff p.1 : ℂ) * (Real.exp (-p.1) : ℂ) *
      dotL e (chartJ a ν τ₀ p) +
    (resolventTimeCutoff p.1 : ℂ) * dotL e (chartJ w ν τ₀ p)

/-- Pointwise form of the B0448 product-coordinate transpose operator. -/
theorem productResolventOpT_apply_eq (ψ : 𝓢(ℝ × Space, ℂ)) (p : ℝ × Space) :
    productResolventOpT ψ p =
      -productTimeDerivativeComplex ψ p - productSpatialLaplacianComplex ψ p + ψ p := by
  unfold productResolventOpT productTimeDerivativeComplex productSpatialLaplacianComplex
  change -((LineDeriv.lineDerivOp ((1 : ℝ), (0 : Space)) ψ) p) -
      ∑ i : Fin 3, (LineDeriv.lineDerivOp ((0 : ℝ), coordinateVector i)
        (LineDeriv.lineDerivOp ((0 : ℝ), coordinateVector i) ψ)) p + ψ p = _
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv ((1 : ℝ), (0 : Space)) ψ p]
  congr 1

set_option maxHeartbeats 8000000 in
/-- The fixed cutoff graph identity in ST coordinates, for every compactly supported complex
Schwartz test. -/
theorem chartJ_cutoff_ST_resolvent {ν : ℝ} (hν : 0 < ν)
    (hq : q ≠ ⊤) (hq1 : 1 < q) {w a b : Yq P q}
    (hTime : HasPhaseOp driftT w b) (hLap : HasPhaseOp (nuLapT ν) w a)
    (τ₀ : ℝ) (e : CVec3) {φ : 𝓢(ST, ℂ)}
    (hφc : HasCompactSupport (φ : ST → ℂ)) :
    ∫ X : ST, resolventOpT φ X * chartJCutoffHST ν τ₀ e w X =
      ∫ X, φ X * chartJCutoffFST ν τ₀ e w b a X := by
  let ψ : 𝓢(ℝ × Space, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ productToST φ
  have hψc : HasCompactSupport (ψ : ℝ × Space → ℂ) := by
    let K : Set (ℝ × Space) := productToST.symm '' tsupport (φ : ST → ℂ)
    have hK : IsCompact K := hφc.isCompact.image productToST.symm.continuous
    refine HasCompactSupport.intro hK ?_
    intro p hp
    by_contra hne
    apply hp
    refine ⟨productToST p, subset_tsupport φ (Function.mem_support.mpr ?_), ?_⟩
    · simpa [ψ, SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using hne
    · exact productToST.symm_apply_apply p
  have hprod := chartJ_cutoff_complexTest_resolvent hν hq hq1 hTime hLap τ₀ e
    (ψ := ψ) hψc
  have hIntegral (g : ST → ℂ) :
      ∫ p : ℝ × Space, g (productToST p) = ∫ X : ST, g X := by
    simpa [productToST] using
      (UnforcedLeray.B0448.integral_ST_eq
        (fun p : ℝ × Space => g (WithLp.toLp 2 p))).symm
  have hop : ∀ p, productResolventOpT ψ p =
      -productTimeDerivativeComplex ψ p - productSpatialLaplacianComplex ψ p + ψ p :=
    productResolventOpT_apply_eq ψ
  have hprodOp : ∫ p : ℝ × Space, productResolventOpT ψ p *
      ((resolventTimeCutoff p.1 : ℂ) * dotL e (chartJ w ν τ₀ p)) =
      ∫ p, ψ p * ((resolventTimeCutoffDeriv p.1 : ℂ) * dotL e (chartJ w ν τ₀ p) +
        (resolventTimeCutoff p.1 : ℂ) * dotL e (chartJ b ν τ₀ p) -
        (resolventTimeCutoff p.1 : ℂ) * (Real.exp (-p.1) : ℂ) *
          dotL e (chartJ a ν τ₀ p) +
        (resolventTimeCutoff p.1 : ℂ) * dotL e (chartJ w ν τ₀ p)) := by
    simpa only [hop] using hprod
  let HL : ST → ℂ := chartJCutoffHST ν τ₀ e w
  let FL : ST → ℂ := chartJCutoffFST ν τ₀ e w b a
  have hleft : ∫ p : ℝ × Space,
      productResolventOpT ψ p * ((resolventTimeCutoff p.1 : ℂ) * dotL e
        (chartJ w ν τ₀ p)) = ∫ X : ST, resolventOpT φ X * HL X := by
    calc
      _ = ∫ p : ℝ × Space,
          (fun X : ST => resolventOpT φ X * HL X) (productToST p) := by
            apply integral_congr_ae
            filter_upwards [] with p
            have hOp : productResolventOpT ψ p = resolventOpT φ (productToST p) := by
              have h := congrArg (fun f : 𝓢(ℝ × Space, ℂ) => f p)
                (productResolventOpT_comp φ)
              simpa [ψ, SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using h
            simpa [ψ, HL, chartJCutoffHST, productToST, Function.comp_def] using
              congrArg (fun z : ℂ => z * ((resolventTimeCutoff p.1 : ℂ) *
                dotL e (chartJ w ν τ₀ p))) hOp
      _ = ∫ X : ST, resolventOpT φ X * HL X := hIntegral (fun X => resolventOpT φ X * HL X)
  have hright : ∫ p : ℝ × Space,
      ψ p * ((resolventTimeCutoffDeriv p.1 : ℂ) * dotL e (chartJ w ν τ₀ p) +
        (resolventTimeCutoff p.1 : ℂ) * dotL e (chartJ b ν τ₀ p) -
        (resolventTimeCutoff p.1 : ℂ) * (Real.exp (-p.1) : ℂ) *
          dotL e (chartJ a ν τ₀ p) +
        (resolventTimeCutoff p.1 : ℂ) * dotL e (chartJ w ν τ₀ p)) =
      ∫ X : ST, φ X * FL X := by
    calc
      _ = ∫ p : ℝ × Space, (fun X : ST => φ X * FL X) (productToST p) := by
            apply integral_congr_ae
            filter_upwards [] with p
            simp [ψ, FL, chartJCutoffFST, productToST]
      _ = ∫ X : ST, φ X * FL X := hIntegral (fun X => φ X * FL X)
  calc
    _ = ∫ p : ℝ × Space, productResolventOpT ψ p *
        ((resolventTimeCutoff p.1 : ℂ) * dotL e (chartJ w ν τ₀ p)) := hleft.symm
    _ = ∫ p, ψ p * ((resolventTimeCutoffDeriv p.1 : ℂ) * dotL e
          (chartJ w ν τ₀ p) +
        (resolventTimeCutoff p.1 : ℂ) * dotL e (chartJ b ν τ₀ p) -
        (resolventTimeCutoff p.1 : ℂ) * (Real.exp (-p.1) : ℂ) *
          dotL e (chartJ a ν τ₀ p) +
        (resolventTimeCutoff p.1 : ℂ) * dotL e (chartJ w ν τ₀ p)) := hprodOp
    _ = ∫ X : ST, φ X * FL X := hright
    _ = _ := rfl

end UnforcedLeray.B0449
