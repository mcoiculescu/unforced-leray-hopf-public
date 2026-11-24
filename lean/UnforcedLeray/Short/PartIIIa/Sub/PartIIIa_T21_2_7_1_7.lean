import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.AdjWeakDefs

/-!
# `PartIII-a:T21/2/7/1/7`: decomposition of `AdjLocalizedCoeff`

Source of record: `the November 2 reference manuscript`
(SP) lines 3052-3058 (adjoint localized interaction), 2875-2896 (periodic kernel `K_c`).
Route: `c = ν⁻² ≥ 1`, `F_j = w ∂_jE(r)`, `KernelAdjointBound` gives `χ = K_c^T F`; uniqueness
of the cylinder-tested class makes `w ↦ K r w` linear; the coefficient bound is the
weighted Cauchy-Schwarz bound; strong continuity is dominated convergence.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **(L3) Fundamental lemma on the cylinder** (SP 3052-3058): an element of `X_{-m,c}` whose
pairing with every cylinder test vanishes is zero. -/
def LocCylUniq : Prop :=
  ∀ c m : ℝ, 0 < c → ∀ f : AdjX c m,
    (∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ → ∫ x in B0579.cell c, f x * (ψ x : ℂ) = 0) → f = 0

/-- **(L1) Field bounds** (SP 3052-3058, train bounds `LadTrainBdd`): `F_j = w ∂_jE(r)` lies in
`L¹ ∩ L²(cell)` with `‖F_j‖₁ + ‖F_j‖₂ ≤ C' ‖w‖_{X_{-m,c}}` (`|F| ≤ C|w| jb^{-m/2-1}`, weighted
Cauchy-Schwarz, `jb^{-1} ∈ L² ∩ L^∞` on the cell). -/
def LocFieldBound (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)), ∀ T C : ℝ,
    0 ≤ T → LadTrainBdd tr m T C →
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ r ∈ Icc (0 : ℝ) T, ∀ w : AdjX (ν ^ (-2 : ℝ)) m, ∀ j : Fin 2,
      IntegrableOn (fun x => w x * ((B0579.pd j (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ))
          (B0579.cell (ν ^ (-2 : ℝ))) ∧
        MemLp (fun x => w x * ((B0579.pd j (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ)) 2
          (volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))) ∧
        eLpNorm (fun x => w x * ((B0579.pd j (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ)) 1
            (volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))) +
          eLpNorm (fun x => w x * ((B0579.pd j (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ)) 2
            (volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))) ≤ ENNReal.ofReal C' * ‖w‖ₑ

/-- **(L1') Integrability of the pairing** (SP 3052-3058: `uψ - meanShear ∈ L²`, `meanShear`
bounded, `jb^{-1} ∈ L²`): `w (uψ·∇E)` is integrable on the cell. -/
def LocPairInt (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)), ∀ T C : ℝ,
    0 ≤ T → LadTrainBdd tr m T C →
    ∀ r ∈ Icc (0 : ℝ) T, ∀ (w : AdjX (ν ^ (-2 : ℝ)) m) (ψ : ℝ × ℝ → ℝ)
      (uψ : ℝ × ℝ → Fin 2 → ℝ),
      B0579.IsCylTest (ν ^ (-2 : ℝ)) ψ → IsKernelBiotSavart (ν ^ (-2 : ℝ)) ψ uψ →
        IntegrableOn (fun x => w x * ((uψ x 0 * B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x +
            uψ x 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ))
          (B0579.cell (ν ^ (-2 : ℝ)))

/-- **(L2) Pointwise-in-`r` adjoint operators** (SP 3052-3058, `KernelAdjointBound` applied to
`F_j = w ∂_jE(r)`, linear by `LocCylUniq`): a uniform bound `β` and, for each `r ∈ [0, T]`, a
bounded operator `K r` on `X_{-m,c}` with `∫ (K r w) ψ = ∫ w (K_cψ·∇E(r))`. -/
def LocAdjPointwise (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)), ∀ T C : ℝ,
    0 ≤ T → LadTrainBdd tr m T C →
    ∃ β : ℝ, ∀ r ∈ Icc (0 : ℝ) T,
      ∃ Kr : AdjX (ν ^ (-2 : ℝ)) m →L[ℂ] AdjX (ν ^ (-2 : ℝ)) m, ‖Kr‖ ≤ β ∧
        ∀ (w : AdjX (ν ^ (-2 : ℝ)) m) (ψ : ℝ × ℝ → ℝ) (uψ : ℝ × ℝ → Fin 2 → ℝ),
          B0579.IsCylTest (ν ^ (-2 : ℝ)) ψ → IsKernelBiotSavart (ν ^ (-2 : ℝ)) ψ uψ →
            ∫ x in B0579.cell (ν ^ (-2 : ℝ)), (Kr w) x * (ψ x : ℂ) =
              ∫ x in B0579.cell (ν ^ (-2 : ℝ)), w x *
                ((uψ x 0 * B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x +
                  uψ x 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ)

/-- **(L4) Strong continuity** (SP 3052-3058; dominated convergence in `r`, using
`‖K r w - K r₀ w‖ ≤ C ‖F(r) - F(r₀)‖_{L¹∩L²}` by linearity of the kernel adjoint and
`LocCylUniq`): any family of bounded operators on `X_{-m,c}` satisfying the characterising
identity for `r ∈ [0, T]` is strongly continuous there. -/
def LocAdjStrongCont (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)), ∀ T C : ℝ,
    0 ≤ T → LadTrainBdd tr m T C →
    ∀ (K : ℝ → AdjX (ν ^ (-2 : ℝ)) m →L[ℂ] AdjX (ν ^ (-2 : ℝ)) m) (β : ℝ),
      (∀ r ∈ Icc (0 : ℝ) T, ‖K r‖ ≤ β) →
      (∀ r ∈ Icc (0 : ℝ) T, ∀ (w : AdjX (ν ^ (-2 : ℝ)) m) (ψ : ℝ × ℝ → ℝ)
        (uψ : ℝ × ℝ → Fin 2 → ℝ),
          B0579.IsCylTest (ν ^ (-2 : ℝ)) ψ → IsKernelBiotSavart (ν ^ (-2 : ℝ)) ψ uψ →
            ∫ x in B0579.cell (ν ^ (-2 : ℝ)), (K r w) x * (ψ x : ℂ) =
              ∫ x in B0579.cell (ν ^ (-2 : ℝ)), w x *
                ((uψ x 0 * B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x +
                  uψ x 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ)) →
      ∀ w, ContinuousOn (fun r => K r w) (Icc (0 : ℝ) T)

/-- Assembly: the adjoint localized interaction from the pointwise operators, the integrability
of the pairing and strong continuity. -/
theorem adjLocalizedCoeff_of (m : ℝ) (hI : LocPairInt m) (hP : LocAdjPointwise m)
    (hC : LocAdjStrongCont m) : AdjLocalizedCoeff m := by
  intro ν hν hν1 tr T C hT hb
  obtain ⟨β, hβ⟩ := hP ν hν hν1 tr T C hT hb
  choose! K hKn hKid using hβ
  refine ⟨K, β, hKn, ?_, ?_⟩
  · exact hC ν hν hν1 tr T C hT hb K β hKn hKid
  · intro r hr w ψ uψ hψ hu
    exact ⟨hI ν hν hν1 tr T C hT hb r hr w ψ uψ hψ hu, hKid r hr w ψ uψ hψ hu⟩

end UnforcedLeray.Short.IIIa
