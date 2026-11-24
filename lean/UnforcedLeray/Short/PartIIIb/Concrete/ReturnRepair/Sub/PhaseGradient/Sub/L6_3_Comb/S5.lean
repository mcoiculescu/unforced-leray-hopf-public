import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_5
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_3_Comb.S1a
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_2_KerPDE.D
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_3_Comb.S5.YGrad
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_3_Comb.S5.Lap

/-!
# `KdOpSplit` (`PartIII-b:C/rep/2/6/3/5`, source 3603-3626, 3800-3807, 4171-4200, 5223)

Helper layer: the pointwise splitting of `KdOp` into the four kernels and the linearity of
`kerInt` over integrable integrands.  The integrability of the six integrands is the open input.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Pointwise splitting of `KdOp = (∂_h - L + μ + ½)Kd` into the four kernels. -/
theorem kdOp_pointwise_split (ν μ : ℝ) (h : ℝ) (y z : Space) (i j k : Fin 3) :
    KdOp ν μ h y z i j k =
      kdDh ν μ h y z i j k - (1 / 2 : ℂ) * kdYGrad ν μ h y z i j k
        - (ν : ℂ) * ∑ l : Fin 3, kdLap ν μ l h y z i j k
        + ((μ : ℂ) + 1 / 2) * Kd ν μ h y z i j k := by
  simp only [KdOp, Lker, kdDh, kdYGrad, kdLap]
  ring

/-- The integrand of `kerInt` (before the `-∫`). -/
def kerIntegrand (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (Φ : ℝ → Space → Space → Fin 3 → Fin 3 → Fin 3 → ℂ) (τ : ℝ) (y : Space) (i : Fin 3)
    (p : ℝ × Space) : ℂ :=
  ∑ j : Fin 3, ∑ k : Fin 3, Φ p.1 y p.2 i j k * ((T (τ - p.1) p.2 j k : ℝ) : ℂ)

/-- `kerInt` as a single integral over the product measure `(vol|_{Ioi 0}) ⊗ vol`. -/
theorem kerInt_eq_prod (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (Φ : ℝ → Space → Space → Fin 3 → Fin 3 → Fin 3 → ℂ) (τ : ℝ) (y : Space) (i : Fin 3)
    (hint : Integrable (kerIntegrand T Φ τ y i) ((volume.restrict (Ioi (0 : ℝ))).prod volume)) :
    kerInt T Φ τ y i = -∫ p, kerIntegrand T Φ τ y i p ∂((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  unfold kerInt
  congr 1
  rw [integral_prod _ hint]
  rfl

/-- Linearity of `kerInt` in the kernel, given integrability of both integrands. -/
theorem kerInt_sub_of_integrable_S5 (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (Φ Ψ : ℝ → Space → Space → Fin 3 → Fin 3 → Fin 3 → ℂ) (τ : ℝ) (y : Space) (i : Fin 3)
    (hΦ : Integrable (kerIntegrand T Φ τ y i) ((volume.restrict (Ioi (0 : ℝ))).prod volume))
    (hΨ : Integrable (kerIntegrand T Ψ τ y i) ((volume.restrict (Ioi (0 : ℝ))).prod volume)) :
    kerInt T (fun h y' z i' j k => Φ h y' z i' j k - Ψ h y' z i' j k) τ y i =
      kerInt T Φ τ y i - kerInt T Ψ τ y i := by
  have hsub : kerIntegrand T (fun h y' z i' j k => Φ h y' z i' j k - Ψ h y' z i' j k) τ y i =
      fun p => kerIntegrand T Φ τ y i p - kerIntegrand T Ψ τ y i p := by
    funext p
    simp only [kerIntegrand, sub_mul, Finset.sum_sub_distrib]
  rw [kerInt_eq_prod T _ τ y i (by rw [hsub]; exact hΦ.sub hΨ), kerInt_eq_prod T Φ τ y i hΦ,
    kerInt_eq_prod T Ψ τ y i hΨ, hsub, integral_sub hΦ hΨ]
  ring


/-- Interchange of the `l`-sum past the `j,k`-sums. -/
theorem sum_jk_comm_l (f : Fin 3 → Fin 3 → Fin 3 → ℂ) :
    ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, f l j k = ∑ l : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, f l j k := by
  calc ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, f l j k
      = ∑ j : Fin 3, ∑ l : Fin 3, ∑ k : Fin 3, f l j k :=
        Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ l : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, f l j k := Finset.sum_comm

/-- Pointwise splitting of the `kerInt` integrand. -/
theorem kerIntegrand_KdOp_split (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (ν μ τ : ℝ)
    (y : Space) (i : Fin 3) (p : ℝ × Space) :
    kerIntegrand T (KdOp ν μ) τ y i p =
      kerIntegrand T (kdDh ν μ) τ y i p - (1 / 2 : ℂ) * kerIntegrand T (kdYGrad ν μ) τ y i p
        - (ν : ℂ) * ∑ l : Fin 3, kerIntegrand T (kdLap ν μ l) τ y i p
        + ((μ : ℂ) + 1 / 2) * kerIntegrand T (Kd ν μ) τ y i p := by
  unfold kerIntegrand
  simp only [kdOp_pointwise_split, sub_mul, add_mul, mul_assoc, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  rw [sum_jk_comm_l]


/-- The six integrands of `KdOpSplit` are integrable on `(vol|_{Ioi 0}) ⊗ vol` (open input: the
`y`-derivative and `h`-derivative domination of `Gker`, `Kd`). -/
def KdIntegrands : Prop :=
  ∀ (ν μ rOut P : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ), SepData ν μ rOut P T →
    ∀ (τ : ℝ) (y : Space), rOut < ϱ y → ∀ i : Fin 3,
      Integrable (kerIntegrand T (kdDh ν μ) τ y i) ((volume.restrict (Ioi (0 : ℝ))).prod volume) ∧
      Integrable (kerIntegrand T (kdYGrad ν μ) τ y i) ((volume.restrict (Ioi (0 : ℝ))).prod volume) ∧
      (∀ l : Fin 3, Integrable (kerIntegrand T (kdLap ν μ l) τ y i)
        ((volume.restrict (Ioi (0 : ℝ))).prod volume)) ∧
      Integrable (kerIntegrand T (Kd ν μ) τ y i) ((volume.restrict (Ioi (0 : ℝ))).prod volume)

/-- **`KdOpSplit`, conditional on the integrability of the six integrands.** -/
theorem kdOpSplit_of (hI : KdIntegrands) : KdOpSplit := by
  intro ν μ rOut P T hd τ y hy i
  obtain ⟨A, B, C, D⟩ := hI ν μ rOut P T hd τ y hy i
  have hCs : Integrable (fun p : ℝ × Space => ∑ l : Fin 3, kerIntegrand T (kdLap ν μ l) τ y i p)
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) :=
    integrable_finsetSum _ fun l _ => C l
  have hKOint : Integrable (kerIntegrand T (KdOp ν μ) τ y i)
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    have hfun : kerIntegrand T (KdOp ν μ) τ y i = fun p =>
        kerIntegrand T (kdDh ν μ) τ y i p - (1 / 2 : ℂ) * kerIntegrand T (kdYGrad ν μ) τ y i p
          - (ν : ℂ) * ∑ l : Fin 3, kerIntegrand T (kdLap ν μ l) τ y i p
          + ((μ : ℂ) + 1 / 2) * kerIntegrand T (Kd ν μ) τ y i p :=
      funext fun p => kerIntegrand_KdOp_split T ν μ τ y i p
    rw [hfun]
    exact (((A.sub (B.const_mul _)).sub (hCs.const_mul _)).add (D.const_mul _))
  have hLap : ∑ l : Fin 3, kerInt T (kdLap ν μ l) τ y i =
      -∑ l : Fin 3, ∫ p, kerIntegrand T (kdLap ν μ l) τ y i p
        ∂((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    rw [Finset.sum_congr rfl fun l _ => kerInt_eq_prod T _ τ y i (C l), ← Finset.sum_neg_distrib]
  rw [kerInt_eq_prod T _ τ y i hKOint, kerInt_eq_prod T _ τ y i A, kerInt_eq_prod T _ τ y i B,
    kerInt_eq_prod T _ τ y i D, hLap]
  simp only [kerIntegrand_KdOp_split]
  have hB' : Integrable (fun p : ℝ × Space => (1 / 2 : ℂ) * kerIntegrand T (kdYGrad ν μ) τ y i p)
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := B.const_mul _
  have hS' : Integrable (fun p : ℝ × Space => (ν : ℂ) * ∑ l : Fin 3,
      kerIntegrand T (kdLap ν μ l) τ y i p) ((volume.restrict (Ioi (0 : ℝ))).prod volume) :=
    hCs.const_mul _
  have hD' : Integrable (fun p : ℝ × Space => ((μ : ℂ) + 1 / 2) * kerIntegrand T (Kd ν μ) τ y i p)
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := D.const_mul _
  have h1 : Integrable (fun p : ℝ × Space => kerIntegrand T (kdDh ν μ) τ y i p - (1 / 2 : ℂ) *
      kerIntegrand T (kdYGrad ν μ) τ y i p) ((volume.restrict (Ioi (0 : ℝ))).prod volume) :=
    A.sub hB'
  have h2 : Integrable (fun p : ℝ × Space => kerIntegrand T (kdDh ν μ) τ y i p - (1 / 2 : ℂ) *
      kerIntegrand T (kdYGrad ν μ) τ y i p - (ν : ℂ) * ∑ l : Fin 3,
      kerIntegrand T (kdLap ν μ l) τ y i p) ((volume.restrict (Ioi (0 : ℝ))).prod volume) :=
    h1.sub hS'
  rw [integral_add h2 hD', integral_sub h1 hS', integral_sub A hB', integral_const_mul,
    integral_const_mul, integral_const_mul, integral_finsetSum _ fun l _ => C l]
  ring

/-- **`kdOpSplit`** (`PartIII-b:C/rep/2/6/3/5`): the splitting of `KdOp` under `kerInt`; the six
integrands are integrable by `kdIntegrands_of` from `gkerIntegrable`, `gkerYGradInt`,
`gkerLapInt`, `gkerHasDerivH`. -/
theorem kdOpSplit : KdOpSplit :=
  kdOpSplit_of (kdIntegrands_of gkerIntegrable gkerYGradInt gkerLapInt gkerHasDerivH)

end UnforcedLeray.Short.PartIIIb.Concrete