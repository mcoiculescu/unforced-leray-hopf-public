import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Defs

/-!
# `BSSlice` from three slice facts

Source `the November 2 reference manuscript` lines 1351-1362 (stream potential of
the solenoidal cutoff, `L² * |w|⁻² → L⁶`) and 1334-1337 (`Y_r`).  Inputs:

* `BSHLSSlice`: Hardy-Littlewood-Sobolev for the Biot-Savart kernel, `|K(w)| = 1/(4π|w|²)`:
  `F ∈ L²(ℝ³) ⇒ F * K ∈ L⁶(ℝ³)`;
* `PhaseSliceL2`: a.e. phase slice of `Ψ ∈ Y_2` is in `L²(ℝ³)` (Fubini over one period);
* `PhaseSliceWeakGrad`: a weak `y`-gradient relation tested against phase tests holds slice-wise
  for a.e. phase against all `C_c^∞` spatial tests (Fubini, product tests `s(τ) g(y)` and a
  countable dense family of `g`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- HLS for the Biot-Savart kernel (source 1351-1362). -/
def BSHLSSlice : Prop :=
  ∀ F : Space → CVec3, MemLp F 2 volume →
    MemLp (fun y : Space => ∫ z : Space, crossC (F z) (bsKernel (y - z))) 6 volume

/-- A.e. phase slice of an `L²` phase field is in `L²(ℝ³)` (source 1334-1337). -/
def PhaseSliceL2 : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ Ψ : ℝ × Space → CVec3, UnforcedLeray.Short.IIb.IsInYr P 2 Ψ →
    ∀ᵐ τ : ℝ, MemLp (fun z : Space => Ψ (τ, z)) 2 volume

/-- Slice-wise weak `y`-gradient (source 1351-1362). -/
def PhaseSliceWeakGrad : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ Φ : ℝ × Space → CVec3,
    UnforcedLeray.Short.IIb.IsInYr P 2 Φ →
    ∀ Dψ : Fin 3 → ℝ × Space → CVec3,
      (∀ j : Fin 3, UnforcedLeray.Short.IIb.IsInYr P 2 (Dψ j) ∧
        UnforcedLeray.Short.IIb.HasPtwOp P (fun Θ => -dy j Θ) (bsPot Φ) (Dψ j)) →
      ∀ᵐ τ : ℝ, ∀ j : Fin 3, ∀ φ : Space → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
        ∫ y : Space, (fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))) • bsPot Φ (τ, y)
          = -∫ y : Space, φ y • Dψ j (τ, y)

theorem bsSlice_of (h1 : BSHLSSlice) (h2 : PhaseSliceL2) (h3 : PhaseSliceWeakGrad) : BSSlice := by
  intro P hP Φ hΦ _ Dψ hD
  have hΦs := h2 P hP Φ hΦ
  have hDs : ∀ᵐ τ : ℝ, ∀ j : Fin 3, MemLp (fun z : Space => Dψ j (τ, z)) 2 volume :=
    ae_all_iff.2 fun j => h2 P hP (Dψ j) (hD j).1
  have hw := h3 P hP Φ hΦ Dψ hD
  filter_upwards [hΦs, hDs, hw] with τ hτ hDτ hwτ
  have h6 : MemLp (fun y : Space => bsPot Φ (τ, y)) 6 volume := h1 (fun z : Space => Φ (τ, z)) hτ
  exact ⟨h6, fun j => ⟨hDτ j, hwτ j⟩⟩

end UnforcedLeray.Short.PartIIIb.Concrete
