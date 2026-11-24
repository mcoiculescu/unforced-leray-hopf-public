import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3.VtvEtaStream

/-!
# Pointwise expansion of `streamSlice` (source 4464-4467, 3511-3514)

With `η = s^{-μ}ζ` and `ζ(s) = s^μ η(s)`, `∂_sζ = μ s^{μ-1} η + s^μ ∂_sη`, so
`⟨ω,∂_sζ⟩ - (μ/s)⟨ω,ζ⟩ = s^μ⟨ω,∂_sη⟩`, and the flow and force terms are linear in the test.

Parsing note: in `streamSlice` (Sub/PartIII-b_C_flatset_col_6.lean) the body of the integral
`∫ x in cell, ω s x * (ζ s x : ℂ) + (∫ flow) + ∫ x, g ...` extends to the right, so the
`(μ/s)` term is `(μ/s) * ∫ x, (ω ζ + ∫flow)` and the flow term is not in the sum.  This file
proves the intended identity `vtvSliceExpandCorrected` with the parenthesised statement.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (flowIntegrand)

/-- `s`-derivative of a stream test is a cylinder test. -/
theorem vtvDerivCylStream {c : ℝ} {ζ : ℝ → ℝ × ℝ → ℝ} (hζ : IsStreamTest c ζ) (s : ℝ) :
    B0579.IsCylTest c (fun x => deriv (fun s' => ζ s' x) s) := by
  obtain ⟨hsm, hcyl, s1, s2, R, hs1, hsupp⟩ := hζ
  have hF : ∀ x : ℝ × ℝ, HasDerivAt (fun s' => ζ s' x)
      (fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => ζ p.1 p.2) (s, x) (1, 0)) s := by
    intro x
    have hd : DifferentiableAt ℝ (fun p : ℝ × (ℝ × ℝ) => ζ p.1 p.2) (s, x) :=
      (hsm.differentiable (by simp)) (s, x)
    have hl : HasDerivAt (fun s' : ℝ => ((s', x) : ℝ × (ℝ × ℝ)))
        ((1 : ℝ), (0 : ℝ × ℝ)) s :=
      (hasDerivAt_id s).prodMk (hasDerivAt_const s x)
    exact hd.hasFDerivAt.comp_hasDerivAt s hl
  have hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ × ℝ => fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => ζ p.1 p.2) (s, x) (1, 0)) := by
    have h1 := (contDiff_infty_iff_fderiv.1 hsm).2
    have h2 := h1.clm_apply (contDiff_const (c := ((1 : ℝ), (0 : ℝ × ℝ))))
    exact h2.comp (contDiff_const.prodMk contDiff_id)
  have hfun : (fun x : ℝ × ℝ => deriv (fun s' => ζ s' x) s) =
      fun x : ℝ × ℝ => fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => ζ p.1 p.2) (s, x) (1, 0) :=
    funext fun x => (hF x).deriv
  refine ⟨?_, ?_, ?_⟩
  · rw [hfun]
    exact hsmooth
  · intro x
    have hper : (fun s' => ζ s' (x.1 + c, x.2)) = fun s' => ζ s' x :=
      funext fun s' => (hcyl s').periodic x
    show deriv (fun s' => ζ s' (x.1 + c, x.2)) s = deriv (fun s' => ζ s' x) s
    rw [hper]
  · refine ⟨R, fun x hx => ?_⟩
    have hz : (fun s' => ζ s' x) = fun _ => (0 : ℝ) :=
      funext fun s' => hsupp s' x (Or.inr (Or.inr hx))
    show deriv (fun s' => ζ s' x) s = 0
    rw [hz, deriv_const]

/-- For `s > 0`: `ζ s x = s^μ η s x`. -/
theorem vtvZeta_eq {μ : ℝ} {ζ : ℝ → ℝ × ℝ → ℝ} {s : ℝ} (hs : 0 < s) (x : ℝ × ℝ) :
    ζ s x = s ^ μ * vtvEta μ ζ s x := by
  unfold vtvEta
  rw [← mul_assoc, ← Real.rpow_add hs, add_neg_cancel, Real.rpow_zero, one_mul]

/-- Product rule for `ζ = s^μ η` at `s > 0`. -/
theorem vtvDeriv_split {c μ : ℝ} {ζ : ℝ → ℝ × ℝ → ℝ} (hζ : IsStreamTest c ζ) {s : ℝ}
    (hs : 0 < s) (x : ℝ × ℝ) :
    deriv (fun s' => ζ s' x) s =
      (μ * s ^ (μ - 1)) * vtvEta μ ζ s x + s ^ μ * deriv (fun s' => vtvEta μ ζ s' x) s := by
  obtain ⟨hsm, -, -⟩ := hζ
  have hζd : DifferentiableAt ℝ (fun s' => ζ s' x) s := by
    have hd : DifferentiableAt ℝ (fun p : ℝ × (ℝ × ℝ) => ζ p.1 p.2) (s, x) :=
      (hsm.differentiable (by simp)) (s, x)
    have hl : DifferentiableAt ℝ (fun s' : ℝ => ((s', x) : ℝ × (ℝ × ℝ))) s :=
      differentiableAt_id.prodMk (differentiableAt_const x)
    exact hd.comp s hl
  have hηd : DifferentiableAt ℝ (fun s' => vtvEta μ ζ s' x) s := by
    have h1 : DifferentiableAt ℝ (fun s' : ℝ => s' ^ (-μ)) s :=
      (Real.hasDerivAt_rpow_const (Or.inl hs.ne')).differentiableAt
    exact h1.mul hζd
  have hEq : (fun s' => ζ s' x) =ᶠ[𝓝 s] (fun s' => s' ^ μ * vtvEta μ ζ s' x) := by
    filter_upwards [Ioi_mem_nhds hs] with s' hs'
    exact vtvZeta_eq (μ := μ) (ζ := ζ) hs' x
  rw [hEq.deriv_eq]
  have hP : HasDerivAt (fun s' : ℝ => s' ^ μ) (μ * s ^ (μ - 1)) s :=
    Real.hasDerivAt_rpow_const (Or.inl hs.ne')
  exact (hP.mul hηd.hasDerivAt).deriv

/-- Scaling a cylinder test scales its `η`-derivatives linearly. -/
theorem vtvPd_smul {c : ℝ} {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ) (a : ℝ) (j : Fin 2) :
    B0579.pd j (fun y => a * φ y) = fun y => a * B0579.pd j φ y := by
  funext y
  simp only [B0579.pd]
  rw [fderiv_const_mul hφ.differentiable.differentiableAt]
  simp

theorem vtvLap_smul {c : ℝ} {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ) (a : ℝ) (x : ℝ × ℝ) :
    UnforcedLeray.Short.IIIa.lapP (fun y => a * φ y) x = a * UnforcedLeray.Short.IIIa.lapP φ x := by
  unfold UnforcedLeray.Short.IIIa.lapP
  rw [vtvPd_smul hφ a 0, vtvPd_smul (hφ.pd 0) a 0, vtvPd_smul hφ a 1, vtvPd_smul (hφ.pd 1) a 1]
  ring

/-- The flow integrand is linear in the test function (pointwise). -/
theorem vtvFlow_smul {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (ω : ℝ × ℝ → ℂ)
    (u : ℝ × ℝ → Fin 2 → ℂ) (r : ℝ) {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ) (a : ℝ)
    (x : ℝ × ℝ) :
    flowIntegrand tr ω u r (fun y => a * φ y) x = (a : ℂ) * flowIntegrand tr ω u r φ x := by
  unfold flowIntegrand
  rw [vtvLap_smul hφ a x, vtvPd_smul hφ a 0, vtvPd_smul hφ a 1]
  push_cast
  ring

/-- **Pointwise expansion, intended form** (source 4464-4467, 3511-3514): the `(μ/s)` term
multiplies `⟨ω,ζ⟩` alone, and the flow term is a separate summand. -/
theorem vtvSliceExpandCorrected {ν c μ : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    (ω g : ℝ → ℝ × ℝ → ℂ) (b : Chart → Fin 2 → ℂ) (ζ : ℝ → ℝ × ℝ → ℝ)
    (hζ : IsStreamTest c ζ) (hOm : ∀ s, 0 < s → ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ →
      IntegrableOn (fun x => ω s x * (ψ x : ℂ)) (B0579.cell c)) (s : ℝ) (hs : 0 < s) :
    (∫ x in B0579.cell c, ω s x * ((deriv (fun s' => ζ s' x) s : ℝ) : ℂ)) -
        ((μ : ℂ) / (s : ℂ)) * (∫ x in B0579.cell c, ω s x * (ζ s x : ℂ)) +
      (∫ x in B0579.cell c, flowIntegrand tr (ω s) (fun x => b (s, x)) s (ζ s) x) +
      (∫ x in B0579.cell c, g s x * (ζ s x : ℂ)) =
      (((s : ℂ) ^ (μ : ℂ)) * ∫ x in B0579.cell c,
          ω s x * ((deriv (fun s' => vtvEta μ ζ s' x) s : ℝ) : ℂ)) +
        (((s : ℂ) ^ (μ : ℂ)) * ((∫ x in B0579.cell c, g s x * ((vtvEta μ ζ s x : ℝ) : ℂ)) +
          ∫ x in B0579.cell c, flowIntegrand tr (ω s) (fun x => b (s, x)) s (vtvEta μ ζ s) x)) := by
  have hη : IsStreamTest c (vtvEta μ ζ) := vtvEtaStream c μ ζ hζ
  have hPc : ((s : ℂ) ^ (μ : ℂ)) = ((s ^ μ : ℝ) : ℂ) := (Complex.ofReal_cpow hs.le μ).symm
  have hsub : s ^ (μ - 1) = s ^ μ / s := Real.rpow_sub_one hs.ne' μ
  have hcyη : B0579.IsCylTest c (vtvEta μ ζ s) := hη.2.1 s
  have hcyD : B0579.IsCylTest c (fun x => deriv (fun s' => vtvEta μ ζ s' x) s) :=
    vtvDerivCylStream hη s
  have hI1 : IntegrableOn (fun x => ω s x * ((vtvEta μ ζ s x : ℝ) : ℂ)) (B0579.cell c) :=
    hOm s hs _ hcyη
  have hI2 : IntegrableOn (fun x => ω s x * ((deriv (fun s' => vtvEta μ ζ s' x) s : ℝ) : ℂ))
      (B0579.cell c) :=
    hOm s hs _ hcyD
  have hsplit : (fun x => ω s x * ((deriv (fun s' => ζ s' x) s : ℝ) : ℂ)) =
      fun x => ((μ * s ^ (μ - 1) : ℝ) : ℂ) * (ω s x * ((vtvEta μ ζ s x : ℝ) : ℂ)) +
        ((s ^ μ : ℝ) : ℂ) * (ω s x * ((deriv (fun s' => vtvEta μ ζ s' x) s : ℝ) : ℂ)) := by
    funext x
    rw [vtvDeriv_split hζ hs x]
    push_cast
    ring
  have hK1 : ∫ x in B0579.cell c, ω s x * ((deriv (fun s' => ζ s' x) s : ℝ) : ℂ) =
      ((μ * s ^ (μ - 1) : ℝ) : ℂ) * (∫ x in B0579.cell c,
          ω s x * ((vtvEta μ ζ s x : ℝ) : ℂ)) +
        ((s ^ μ : ℝ) : ℂ) * (∫ x in B0579.cell c,
          ω s x * ((deriv (fun s' => vtvEta μ ζ s' x) s : ℝ) : ℂ)) := by
    rw [hsplit, integral_add (Integrable.const_mul hI1 _) (Integrable.const_mul hI2 _),
      integral_const_mul, integral_const_mul]
  have hK2 : (∫ x in B0579.cell c, ω s x * ((ζ s x : ℝ) : ℂ)) =
      ((s ^ μ : ℝ) : ℂ) * (∫ x in B0579.cell c, ω s x * ((vtvEta μ ζ s x : ℝ) : ℂ)) := by
    rw [← integral_const_mul]
    congr 1
    funext x
    rw [vtvZeta_eq (μ := μ) (ζ := ζ) hs x]
    push_cast
    ring
  have hζfun : ζ s = fun y => s ^ μ * vtvEta μ ζ s y :=
    funext fun y => vtvZeta_eq (μ := μ) (ζ := ζ) hs y
  have hI3 : (∫ x in B0579.cell c,
        flowIntegrand tr (ω s) (fun x => b (s, x)) s (ζ s) x) =
      ((s ^ μ : ℝ) : ℂ) * (∫ x in B0579.cell c,
        flowIntegrand tr (ω s) (fun x => b (s, x)) s (vtvEta μ ζ s) x) := by
    rw [← integral_const_mul]
    congr 1
    funext x
    rw [hζfun]
    exact vtvFlow_smul tr (ω s) (fun x => b (s, x)) s hcyη (s ^ μ) x
  have hI4 : (∫ x in B0579.cell c, g s x * ((ζ s x : ℝ) : ℂ)) =
      ((s ^ μ : ℝ) : ℂ) * (∫ x in B0579.cell c, g s x * ((vtvEta μ ζ s x : ℝ) : ℂ)) := by
    rw [← integral_const_mul]
    congr 1
    funext x
    rw [vtvZeta_eq (μ := μ) (ζ := ζ) hs x]
    push_cast
    ring
  have hcoef : ((μ * s ^ (μ - 1) : ℝ) : ℂ) = (μ : ℂ) / (s : ℂ) * ((s ^ μ : ℝ) : ℂ) := by
    rw [hsub]
    push_cast
    field_simp
  rw [hK1, hK2, hI3, hI4, hPc, hcoef]
  ring

/-- **Pointwise expansion** (source 4464-4467, 3511-3514), glue. -/
theorem vtvSliceExpand : VtvSliceExpand := by
  intro ν c μ tr ω g b G f H ζ hζ s hs
  have hOm := H.2.2.2.2.2.2.2.2
  have := vtvSliceExpandCorrected (μ := μ) tr ω g b ζ hζ hOm s hs
  simpa [streamSlice, vtvY, vtvR, mul_add] using this

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
