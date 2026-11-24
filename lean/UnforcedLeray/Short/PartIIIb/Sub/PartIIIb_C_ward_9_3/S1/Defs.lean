import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_2_2_11_4

/-! Relaxed standing context for `TransCommPoint`: only `0 < ν`, `0 < R` (no `ν ≤ 1 ≤ R`). -/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Relaxed context: `ν > 0`, `R > 0` (the `True` slot replaces `ν ≤ 1`, `0 < R` replaces `1 ≤ R`). -/
def TCCtxW (σ₁ σ₂ ν μ R P : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (y : Space) : Prop :=
  -(1 / 4) < σ₁ ∧ 0 < ν ∧ True ∧ 0 < R ∧ 0 < P ∧ μ ∈ Icc σ₁ σ₂ ∧
    IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T ∧ SepMoment P T ∧ IsAxiSource T ∧
    y ∈ streamAnn ν R

def TCRegW : Prop :=
  ∀ σ₁ σ₂ ν μ R P (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (y : Space),
    TCCtxW σ₁ σ₂ ν μ R P T y →
      ContDiffAt ℝ 2 (sepX0 ν μ T τ) y ∧ DifferentiableAt ℝ (fun t => sepX0 ν μ T t y) τ ∧
        ContDiffAt ℝ 2 (psiFld (sepX0 ν μ T) τ) y ∧
        DifferentiableAt ℝ (fun t => psiFld (sepX0 ν μ T) t y) τ

def TCIntW : Prop :=
  ∀ σ₁ σ₂ ν μ R P (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (y : Space),
    TCCtxW σ₁ σ₂ ν μ R P T y →
      IntegrableOn (fun ρ : ℝ => ρ * sepX0 ν μ T τ !₂[ρ, 0, y 2] 2) (Ioi (ϱ y)) ∧
      IntegrableOn (fun ρ : ℝ => ρ * (deriv (fun s => sepX0 ν μ T s !₂[ρ, 0, y 2]) τ) 2)
        (Ioi (ϱ y)) ∧
      IntegrableOn (fun ρ : ℝ => ρ *
        (fderiv ℝ (sepX0 ν μ T τ) !₂[ρ, 0, y 2] !₂[ρ, 0, y 2]) 2) (Ioi (ϱ y)) ∧
      IntegrableOn (fun ρ : ℝ => ρ * (physLap (sepX0 ν μ T τ) !₂[ρ, 0, y 2]) 2) (Ioi (ϱ y))

def TCTimeW : Prop :=
  ∀ σ₁ σ₂ ν μ R P (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (y : Space),
    TCCtxW σ₁ σ₂ ν μ R P T y →
      deriv (fun t => psiFld (sepX0 ν μ T) t y) τ =
        psiFld (fun t y' => deriv (fun s => sepX0 ν μ T s y') t) τ y

def TCGradW : Prop :=
  ∀ σ₁ σ₂ ν μ R P (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (y : Space),
    TCCtxW σ₁ σ₂ ν μ R P T y →
      psiFld (fun t y' => fderiv ℝ (sepX0 ν μ T t) y' y') τ y =
        fderiv ℝ (psiFld (sepX0 ν μ T) τ) y y - (2 : ℝ) • psiFld (sepX0 ν μ T) τ y

def TCLapW : Prop :=
  ∀ σ₁ σ₂ ν μ R P (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (y : Space),
    TCCtxW σ₁ σ₂ ν μ R P T y →
      psiFld (fun t y' => physLap (sepX0 ν μ T t) y') τ y =
        physLap (psiFld (sepX0 ν μ T) τ) y - (2 * sepX0 ν μ T τ y 2) • coordinateVector 2

def TCRadW : Prop :=
  ∀ σ₁ σ₂ ν μ R P (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (y : Space),
    TCCtxW σ₁ σ₂ ν μ R P T y →
      fderiv ℝ (psiFld (sepX0 ν μ T) τ) y (radialUnit y) =
        (ϱ y * sepX0 ν μ T τ y 2) • coordinateVector 2

def TCGradX0StructW : Prop :=
  ∀ σ₁ σ₂ ν μ R P (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (y : Space),
    TCCtxW σ₁ σ₂ ν μ R P T y →
      ContDiffOn ℝ 2 (sepX0 ν μ T τ) (youngOpen ν R) ∧
      (∀ y' ∈ youngOpen ν R, ∑ j : Fin 3, physPd (sepX0 ν μ T τ) j y' j = 0) ∧
      AxiNoSwirlOn (youngOpen ν R) (sepX0 ν μ T)

def TCGradX0DecayW : Prop :=
  ∀ σ₁ σ₂ ν μ R P (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (y : Space),
    TCCtxW σ₁ σ₂ ν μ R P T y →
      StreamDecay ν R (sepX0 ν μ T) τ ∧
      IntegrableOn (fun ρ : ℝ => ρ *
        (fderiv ℝ (sepX0 ν μ T τ) !₂[ρ, 0, y 2] !₂[ρ, 0, y 2]) 2) (Ioi (ϱ y))

end UnforcedLeray.Short.PartIIIb.Concrete

end
