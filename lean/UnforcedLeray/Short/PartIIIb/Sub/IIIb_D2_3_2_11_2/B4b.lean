import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_2_11_2_5
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2_11_2.B4b.Far

/-!
# `wardX0IntegrandDecay_proved` (`PartIII-b:IIIb-D2/3/2/11/2/5/2`, source 4177-4179, 3604-3621)

Source of record: `the November 2 reference manuscript`.
`Far.lean` gives `‖D^j_{(τ,y)} (wardX0)_z‖ ≤ C_j ϱ(y)^{-4}` for `ϱ(y) ≥ 4 rOut + 2`, uniformly in `τ`
(and hence on every compact set of `(τ, z)`).  Here the linear embedding
`e(τ,ρ,z) = (τ,(ρ,0,z))` (`ContinuousLinearMap.iteratedFDerivWithin_comp_right`) and the Leibniz rule
(`norm_iteratedFDerivWithin_mul_le`) for the factor `ρ` give `C ρ^{-2}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- The linear embedding `(ρ, z) ↦ (ρ, 0, z)`. -/
def b4bLsp : ℝ × ℝ →L[ℝ] Space :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (EuclideanSpace.single (2 : Fin 3) (1 : ℝ))

/-- The linear embedding `(τ, ρ, z) ↦ (τ, (ρ, 0, z))`. -/
def b4bE : ℝ × ℝ × ℝ →L[ℝ] ℝ × Space :=
  (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod (b4bLsp.comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))

theorem b4bE_apply (x : ℝ × ℝ × ℝ) : b4bE x = (x.1, !₂[x.2.1, 0, x.2.2]) := by
  ext i
  · simp [b4bE]
  · fin_cases i <;> simp [b4bE, b4bLsp]

theorem b4b_rho (ρ z : ℝ) (hρ : 0 ≤ ρ) : ϱ (!₂[ρ, 0, z] : Space) = ρ := by
  unfold ϱ
  simp [Real.sqrt_sq hρ]

theorem b4b_lin_iter (i : ℕ) (x : ℝ × ℝ × ℝ) :
    ‖iteratedFDeriv ℝ i (fun y : ℝ × ℝ × ℝ => y.2.1) x‖ ≤ |x.2.1| + 1 := by
  set L : ℝ × ℝ × ℝ →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))
    with hL
  have hLf : (fun y : ℝ × ℝ × ℝ => y.2.1) = fun y => L y := by funext y; simp [hL]
  have hLn : ‖L‖ ≤ 1 := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    calc ‖ContinuousLinearMap.fst ℝ ℝ ℝ‖ * ‖ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)‖
        ≤ 1 * 1 := mul_le_mul (ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ)
          (ContinuousLinearMap.norm_snd_le ℝ ℝ (ℝ × ℝ)) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  rw [hLf]
  rcases i with _ | _ | m
  · rw [norm_iteratedFDeriv_zero]
    have : L x = x.2.1 := by simp [hL]
    rw [this, Real.norm_eq_abs]; linarith
  · rw [← paramNormFDeriv1, ContinuousLinearMap.fderiv]
    linarith [abs_nonneg x.2.1]
  · rw [← norm_iteratedFDeriv_fderiv]
    have : fderiv ℝ (fun y => L y) = fun _ => L := funext fun y => L.fderiv
    rw [this, iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, norm_zero]
    positivity

theorem b4b_comp_norm (W : ℝ × Space → ℝ) (S : Set (ℝ × Space)) (hS : IsOpen S)
    (hW : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W S) (j : ℕ) (x : ℝ × ℝ × ℝ) (hx : b4bE x ∈ S) :
    ‖iteratedFDeriv ℝ j (W ∘ b4bE) x‖ ≤ ‖iteratedFDeriv ℝ j W (b4bE x)‖ * ‖b4bE‖ ^ j := by
  have ht : IsOpen (b4bE ⁻¹' S) := hS.preimage b4bE.continuous
  have hj : (j : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have hx' : x ∈ b4bE ⁻¹' S := hx
  have h := ContinuousLinearMap.iteratedFDerivWithin_comp_right b4bE hW hS.uniqueDiffOn
    ht.uniqueDiffOn hx hj
  rw [iteratedFDerivWithin_of_isOpen j ht hx', iteratedFDerivWithin_of_isOpen j hS hx] at h
  rw [h]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

set_option maxHeartbeats 2000000 in
theorem wardX0IntegrandDecay_proved : WardX0IntegrandDecay := by
  intro ν μ R c g hν hR hc hμ hg n K hK
  set rOut : ℝ := R * Real.sqrt (5 * ν / 6) with hrOut
  have hr : 0 ≤ rOut := by positivity
  have hsm := wardX0SmoothInf_proved ν μ R c g hν hR hc hμ hg
  set S : Set (ℝ × Space) := {q | rOut < ϱ q.2} with hSdef
  have hSo : IsOpen S := isOpen_lt continuous_const (by unfold ϱ; fun_prop)
  set W : ℝ × Space → ℝ := fun q => wardX0 ν μ R c g q.1 q.2 2 with hWdef
  have hWs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W S := by
    have hp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v : Space => v 2) :=
      (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).contDiff
    exact hp.comp_contDiffOn hsm
  choose C hC using fun j : ℕ => wardX0FarIter ν μ R c g hν hR hc hμ hg j
  set En : ℝ := ‖b4bE‖ with hEn
  refine ⟨4 * rOut + 2, ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (2 * (|C (n - i)| * En ^ (n - i))),
    by linarith, by linarith, fun τ z _ ρ hρ => ?_⟩
  have hρ2 : 2 ≤ ρ := by linarith
  have hρ0 : 0 ≤ ρ := by linarith
  set x : ℝ × ℝ × ℝ := (τ, ρ, z) with hxdef
  have hex : b4bE x = (τ, !₂[ρ, 0, z]) := b4bE_apply x
  have hexS : b4bE x ∈ S := by
    rw [hex]
    show rOut < ϱ (!₂[ρ, 0, z] : Space)
    rw [b4b_rho ρ z hρ0]; linarith
  have hϱ : ϱ (b4bE x).2 = ρ := by rw [hex]; exact b4b_rho ρ z hρ0
  -- derivative bounds for the composed factor
  have hWe : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (W ∘ b4bE) (b4bE ⁻¹' S) :=
    hWs.comp b4bE.contDiff.contDiffOn (fun y hy => hy)
  have hbnd : ∀ j : ℕ, ‖iteratedFDeriv ℝ j (W ∘ b4bE) x‖ ≤ |C j| * En ^ j * (ρ ^ 4)⁻¹ := by
    intro j
    refine (b4b_comp_norm W S hSo hWs j x hexS).trans ?_
    have h1 := hC j (b4bE x) (by rw [hϱ]; linarith)
    rw [hϱ] at h1
    have h2 : C j * (ρ ^ 4)⁻¹ ≤ |C j| * (ρ ^ 4)⁻¹ :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    calc ‖iteratedFDeriv ℝ j W (b4bE x)‖ * ‖b4bE‖ ^ j ≤ (|C j| * (ρ ^ 4)⁻¹) * En ^ j :=
          mul_le_mul_of_nonneg_right (h1.trans h2) (by positivity)
      _ = |C j| * En ^ j * (ρ ^ 4)⁻¹ := by ring
  -- Leibniz
  have hft : IsOpen (b4bE ⁻¹' S) := hSo.preimage b4bE.continuous
  have hxt : x ∈ b4bE ⁻¹' S := hexS
  have hfs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℝ × ℝ × ℝ => y.2.1) :=
    contDiff_fst.comp contDiff_snd
  have hn : (n : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have hL := norm_iteratedFDerivWithin_mul_le hfs.contDiffOn hWe hft.uniqueDiffOn hxt hn
  have hFeq : (fun y : ℝ × ℝ × ℝ => y.2.1 * wardX0 ν μ R c g y.1 !₂[y.2.1, 0, y.2.2] 2) =
      fun y => (fun y : ℝ × ℝ × ℝ => y.2.1) y * (W ∘ b4bE) y := by
    funext y
    simp only [Function.comp_apply, hWdef, b4bE_apply]
  rw [hFeq]
  have hρpos : 0 < ρ := by linarith
  have hkey : (ρ + 1) * (ρ ^ 4)⁻¹ ≤ 2 / ρ ^ 2 := by
    rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : ρ + 1 ≤ 2 * ρ ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right h1 (sq_nonneg ρ)]
  rw [iteratedFDerivWithin_of_isOpen n hft hxt] at hL
  refine hL.trans ?_
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun i _ => ?_
  · have hi := b4b_lin_iter i x
    rw [iteratedFDerivWithin_of_isOpen i hft hxt, iteratedFDerivWithin_of_isOpen (n - i) hft hxt]
    have hj := hbnd (n - i)
    have hxρ : |x.2.1| = ρ := abs_of_nonneg hρ0
    rw [hxρ] at hi
    have hC0 : (0 : ℝ) ≤ (n.choose i : ℝ) := Nat.cast_nonneg _
    calc (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y : ℝ × ℝ × ℝ => y.2.1) x‖ *
          ‖iteratedFDeriv ℝ (n - i) (W ∘ b4bE) x‖
        ≤ (n.choose i : ℝ) * (ρ + 1) * (|C (n - i)| * En ^ (n - i) * (ρ ^ 4)⁻¹) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hi hC0) hj (norm_nonneg _)
            (mul_nonneg hC0 (by positivity))
      _ = (n.choose i : ℝ) * (|C (n - i)| * En ^ (n - i)) * ((ρ + 1) * (ρ ^ 4)⁻¹) := by ring
      _ ≤ (n.choose i : ℝ) * (|C (n - i)| * En ^ (n - i)) * (2 / ρ ^ 2) :=
          mul_le_mul_of_nonneg_left hkey (mul_nonneg hC0 (by positivity))
      _ = ((n.choose i : ℝ) * (2 * (|C (n - i)| * En ^ (n - i)))) / ρ ^ 2 := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
