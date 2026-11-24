import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFluxLemmas
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.DivFreeCutoffDensity.CutPd

/-!
# `VtvForcedAdd`: the forced integrand is additive in the test (source 3511-3514)

Pointwise additivity of `flatDt`, `flatGrad`, `flatLap` for smooth flat tests, hence of
`forcedIntegrand`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (IsFlatTest flatIntegrand trainVel flatDt flatGrad flatLap fibK1)

private theorem vtv_diffS {c : ℝ} {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ} (hΦ : IsFlatTest c Φ) (i : Fin 2)
    (x : ℝ × ℝ) (s : ℝ) : DifferentiableAt ℝ (fun s' => Φ s' x i) s := by
  have h := (hΦ.smooth i).differentiable (by simp) (s, x)
  have hf : DifferentiableAt ℝ (fun s' : ℝ => ((s', x) : ℝ × (ℝ × ℝ))) s :=
    differentiableAt_id.prodMk (differentiableAt_const x)
  exact h.comp s hf

private theorem vtv_diffY {c : ℝ} {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ} (hΦ : IsFlatTest c Φ) (i : Fin 2)
    (s : ℝ) (x : ℝ × ℝ) : DifferentiableAt ℝ (fun y => Φ s y i) x := by
  have h := (hΦ.smooth i).differentiable (by simp) (s, x)
  have hf : DifferentiableAt ℝ (fun y : ℝ × ℝ => ((s, y) : ℝ × (ℝ × ℝ))) x :=
    (differentiableAt_const s).prodMk differentiableAt_id
  exact h.comp x hf

private theorem vtv_cdY {c : ℝ} {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ} (hΦ : IsFlatTest c Φ) (i : Fin 2)
    (s : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℝ × ℝ => Φ s y i) := by
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℝ × ℝ => ((s, y) : ℝ × (ℝ × ℝ))) :=
    contDiff_const.prodMk contDiff_id
  exact (hΦ.smooth i).comp hf

private theorem vtv_pd_cd {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (j : Fin 2) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (B0579.pd j g) := by
  have e : B0579.pd j g = fun y => fderiv ℝ g y (B0579.dir j) := rfl
  rw [e]
  exact (hg.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_apply contDiff_const

private theorem vtv_pd_add_fun {A B : ℝ × ℝ → ℝ}
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A) (hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) B)
    (j : Fin 2) :
    B0579.pd j (fun y => A y + B y) = fun y => B0579.pd j A y + B0579.pd j B y := by
  funext y
  exact UnforcedLeray.Short.IIIa.DfcCutPdAux.pdAddAux j A B y
    (hA.differentiable (by simp) y) (hB.differentiable (by simp) y)

private theorem vtv_lap_add {A B : ℝ × ℝ → ℝ}
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A) (hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) B)
    (x : ℝ × ℝ) :
    UnforcedLeray.Short.IIIa.lapP (fun y => A y + B y) x =
      UnforcedLeray.Short.IIIa.lapP A x + UnforcedLeray.Short.IIIa.lapP B x := by
  unfold UnforcedLeray.Short.IIIa.lapP
  rw [vtv_pd_add_fun hA hB 0, vtv_pd_add_fun hA hB 1,
    UnforcedLeray.Short.IIIa.DfcCutPdAux.pdAddAux 0 (B0579.pd 0 A) (B0579.pd 0 B) x
      ((vtv_pd_cd hA 0).differentiable (by simp) x) ((vtv_pd_cd hB 0).differentiable (by simp) x),
    UnforcedLeray.Short.IIIa.DfcCutPdAux.pdAddAux 1 (B0579.pd 1 A) (B0579.pd 1 B) x
      ((vtv_pd_cd hA 1).differentiable (by simp) x) ((vtv_pd_cd hB 1).differentiable (by simp) x)]
  ring

private theorem vtv_flatDt_add {c : ℝ} {Φ Ψ : ℝ → ℝ × ℝ → Fin 2 → ℝ} (hΦ : IsFlatTest c Φ)
    (hΨ : IsFlatTest c Ψ) (s : ℝ) (x : ℝ × ℝ) (i : Fin 2) :
    flatDt (fun s' x' i' => Φ s' x' i' + Ψ s' x' i') s x i = flatDt Φ s x i + flatDt Ψ s x i := by
  unfold flatDt
  exact deriv_add (vtv_diffS hΦ i x s) (vtv_diffS hΨ i x s)

private theorem vtv_flatGrad_add {c : ℝ} {Φ Ψ : ℝ → ℝ × ℝ → Fin 2 → ℝ} (hΦ : IsFlatTest c Φ)
    (hΨ : IsFlatTest c Ψ) (s : ℝ) (x : ℝ × ℝ) (i j : Fin 2) :
    flatGrad (fun s' x' i' => Φ s' x' i' + Ψ s' x' i') s x i j =
      flatGrad Φ s x i j + flatGrad Ψ s x i j := by
  unfold flatGrad
  exact UnforcedLeray.Short.IIIa.DfcCutPdAux.pdAddAux j (fun y => Φ s y i) (fun y => Ψ s y i) x
    (vtv_diffY hΦ i s x) (vtv_diffY hΨ i s x)

private theorem vtv_flatLap_add {c : ℝ} {Φ Ψ : ℝ → ℝ × ℝ → Fin 2 → ℝ} (hΦ : IsFlatTest c Φ)
    (hΨ : IsFlatTest c Ψ) (s : ℝ) (x : ℝ × ℝ) (i : Fin 2) :
    flatLap (fun s' x' i' => Φ s' x' i' + Ψ s' x' i') s x i =
      flatLap Φ s x i + flatLap Ψ s x i := by
  unfold flatLap
  exact vtv_lap_add (vtv_cdY hΦ i s) (vtv_cdY hΨ i s) x

theorem vtvForcedAdd : VtvForcedAdd := by
  intro c ν μ vel f b Φ Ψ hΦ hΨ p
  simp only [forcedIntegrand, flatIntegrand, vtv_flatDt_add hΦ hΨ, vtv_flatGrad_add hΦ hΨ,
    vtv_flatLap_add hΦ hΨ, Complex.ofReal_add, mul_add, neg_add,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
