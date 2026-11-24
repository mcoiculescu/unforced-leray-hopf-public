import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.L7_WardGradYPhase.WreCut
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.L3_SepX0PhaseBound

/-!
# `PartIII-b:C/rep/2/7`, the phase bound of the jets of `Re W_μ`

Source 3622-3647, 5219-5221.  `sepWre = Re ∘ sepW`, so `|D^j Re W_μ| ≤ ‖Re‖ |D^j W_μ|` and the slice
density `wgyWJet j` is bounded in `L^{22/3}` by `SepWPhaseSup` (`j ≤ 2`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem wgy_jet_le {ν μ rOut P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hr : 0 ≤ rOut) (hP : 0 < P)
    (hS : IIIa.IsSepSource P rOut T) (hM : SepMoment P T) (τ : ℝ) {j : ℕ} (hj : j ≤ 2)
    {y : Space} (hy : rOut < ϱ y) :
    ‖iteratedFDeriv ℝ j (sepWre ν μ T τ) y‖ₑ ≤
      ENNReal.ofReal ‖reL‖ * ‖iteratedFDeriv ℝ j (fun z => IIIa.sepW ν (μ : ℂ) T z τ) y‖ₑ := by
  have hU : IsOpen {y : Space | rOut < ϱ y} := isOpen_lt continuous_const continuous_ϱ
  have hμ' : -(1 / 4) < (μ : ℂ).re := by simpa using hμ
  have hf : ContDiffOn ℝ 2 (fun z => IIIa.sepW ν (μ : ℂ) T z τ) {y : Space | rOut < ϱ y} :=
    contDiffOn_pi.2 (fun i => sepWSmoothOn_of IIIa.sepKernelBounds ν (μ : ℂ) rOut P T hν hμ' hr hP
      hS hM τ i)
  have hfy : ContDiffWithinAt ℝ 2 (fun z => IIIa.sepW ν (μ : ℂ) T z τ) {y : Space | rOut < ϱ y} y :=
    hf.contDiffWithinAt hy
  have h1 := reL.norm_iteratedFDerivWithin_comp_left (n := j) hfy hU.uniqueDiffOn hy
    (by exact_mod_cast hj)
  have e0 : sepWre ν μ T τ = reL ∘ (fun z => IIIa.sepW ν (μ : ℂ) T z τ) := rfl
  have e1 := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
    (f := reL ∘ (fun z => IIIa.sepW ν (μ : ℂ) T z τ)) j hU hy
  have e2 := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
    (f := fun z => IIIa.sepW ν (μ : ℂ) T z τ) j hU hy
  rw [e0, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← e1, ← e2]
  exact h1

/-- The slice density of `D^j Re W_μ` is bounded in `L^{22/3}` (S1 for `Re W_μ`). -/
theorem wgy_jet_phase (σ₁ σ₂ : ℝ) (hσ : -(1 / 4) < σ₁) (j : ℕ) (hj : j ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν μ rOut rIn P : ℝ), 0 < ν → μ ∈ Icc σ₁ σ₂ → 0 ≤ rOut → rOut < rIn →
      0 < P → P ≤ 1 → ∀ T, IIIa.IsSepSource P rOut T → SepMoment P T → ∀ τ : ℝ,
        lqNorm (22 / 3) (wgyWJet j ν μ rIn T τ) ≤
          ENNReal.ofReal (C * (rIn - rOut) ^ (-4 - (j : ℝ) + 9 / 11)) *
            IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T) := by
  set K : Set ℂ := ((fun x : ℝ => (x : ℂ)) '' Icc σ₁ σ₂) with hKdef
  have hKc : IsCompact K := isCompact_Icc.image Complex.continuous_ofReal
  have hKre : ∀ m ∈ K, -(1 / 4) < m.re := by
    rintro m ⟨x, hx, rfl⟩
    simp only [Complex.ofReal_re]
    linarith [hx.1]
  obtain ⟨C, hC0, hB⟩ := sepWPhaseSup K hKc hKre j
  refine ⟨‖reL‖ * C, by positivity, ?_⟩
  intro ν μ rOut rIn P hν hμ hrO hrr hP hP1 T hT hS τ
  have hμre : -(1 / 4) < μ := lt_of_lt_of_le hσ hμ.1
  have hm1 : (μ : ℂ) ∈ K := ⟨μ, hμ, rfl⟩
  have hB1 := hB ν hν (μ : ℂ) hm1 rOut rIn P hrO hrr hP hP1 T hT τ
  have hpt : ∀ y : Space, wgyWJet j ν μ rIn T τ y ≤
      ENNReal.ofReal ‖reL‖ * IIIa.youngDerivNorm ν (μ : ℂ) T j rIn τ y := by
    intro y
    by_cases h : rIn ≤ ϱ y
    · have h' : rIn ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) := h
      unfold wgyWJet
      rw [if_pos h]
      simp only [IIIa.youngDerivNorm, IIIa.wDerivNorm, h', ite_true]
      exact wgy_jet_le hν hμre hrO hP hT hS τ hj (lt_of_lt_of_le hrr h)
    · unfold wgyWJet
      rw [if_neg h]
      exact zero_le
  have ht : 0 ≤ C * (rIn - rOut) ^ (-4 - (j : ℝ) + 9 / 11) :=
    mul_nonneg hC0 (Real.rpow_nonneg (sub_pos.2 hrr).le _)
  calc lqNorm (22 / 3) (wgyWJet j ν μ rIn T τ)
      ≤ lqNorm (22 / 3) (fun y => ENNReal.ofReal ‖reL‖ *
          IIIa.youngDerivNorm ν (μ : ℂ) T j rIn τ y) := lqNorm_mono (by norm_num) hpt
    _ = ENNReal.ofReal ‖reL‖ * lqNorm (22 / 3) (IIIa.youngDerivNorm ν (μ : ℂ) T j rIn τ) :=
        lqNorm_const_mul (by norm_num) _ ENNReal.ofReal_ne_top _
    _ ≤ ENNReal.ofReal ‖reL‖ * (ENNReal.ofReal (C * (rIn - rOut) ^ (-4 - (j : ℝ) + 9 / 11)) *
          IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T)) := mul_le_mul_of_nonneg_left hB1 zero_le
    _ = ENNReal.ofReal (‖reL‖ * C * (rIn - rOut) ^ (-4 - (j : ℝ) + 9 / 11)) *
          IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (norm_nonneg _), mul_assoc]

end UnforcedLeray.Short.PartIIIb.Concrete

end
