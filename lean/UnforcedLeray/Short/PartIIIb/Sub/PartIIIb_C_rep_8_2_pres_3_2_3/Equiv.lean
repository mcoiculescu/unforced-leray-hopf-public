import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_2.AxiU
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_4.Merid
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_1_org

/-!
# Generic leaves for `pres/3/2/3`: equivariance and joint continuity of derivatives

Source `the November 2 reference manuscript`:
121-124, 2031, 2681-2688 (axisymmetry without swirl), 4139-4141 (`D_μ`).

* `pf3_fderiv_equiv`: `D f (g y) (g v) = g (D f y v)` for a pointwise axisymmetric `f`
  (no differentiability needed);
* `pf3_ringResidual_equiv`: `F_R(g y) = g F_R(y)`;
* `pf3_continuous_physDmu`: `(τ, y) ↦ D₀S(τ, y)` is continuous for a jointly `C^∞` field `S`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short.PartIIa (ringResidual physResidualField)

theorem pf3_fderiv_equiv {f : Space → Space} (hf : AxiNoSwirlPt f) (g : Space ≃ₗᵢ[ℝ] Space)
    (hg : FixesAxis g) (y v : Space) : fderiv ℝ f (g y) (g v) = g (fderiv ℝ f y v) := by
  have hfun : (fun x => g (f (g.symm x))) = f := funext fun x => hf g hg x
  have key := axiDens_fderiv_conj g g f (g y)
  rw [hfun, g.symm_apply_apply] at key
  rw [key]
  simp

theorem pf3_selfAdvect_equiv {f : Space → Space} (hf : AxiNoSwirlPt f) (g : Space ≃ₗᵢ[ℝ] Space)
    (hg : FixesAxis g) (y : Space) :
    fderiv ℝ f (g y) (f (g y)) = g (fderiv ℝ f y (f y)) := by
  have h1 : f (g y) = g (f y) := by
    have := hf g hg (g y)
    rw [g.symm_apply_apply] at this
    exact this.symm
  rw [h1, pf3_fderiv_equiv hf g hg]

theorem pf3_axi_Nv (R : ℝ) (b : ℝ × (ℝ × ℝ) → Merid) (τ : ℝ) : AxiNoSwirlPt (Nv R b τ) := by
  intro g hg x
  rw [Nv_eq_liftMer]
  exact liftMer_equivariant g _ hg x

theorem pf3_varrho_apply (g : Space ≃ₗᵢ[ℝ] Space) (hg : FixesAxis g) (y : Space) :
    ϱ (g y) = ϱ y := by
  have := ϱ_symm_apply g hg (g y)
  rw [g.symm_apply_apply] at this
  exact this.symm

theorem pf3_apply_two (g : Space ≃ₗᵢ[ℝ] Space) (hg : FixesAxis g) (y : Space) :
    (g y) 2 = y 2 := by
  have := symm_apply_two g hg (g y)
  rw [g.symm_apply_apply] at this
  exact this.symm

theorem pf3_eR_equiv (g : Space ≃ₗᵢ[ℝ] Space) (hg : FixesAxis g) (x : Space) :
    eR (g x) = g (eR x) := by
  have := map_eR_symm g hg (g x)
  rw [g.symm_apply_apply] at this
  exact this.symm

/-- The ring residual is equivariant under isometries fixing `e₃` (source 2031, 1263). -/
theorem pf3_ringResidual_equiv (R ν : ℝ) (ψ pr : UnforcedLeray.B0184.ProfilePoint → ℝ) (τ : ℝ)
    (g : Space ≃ₗᵢ[ℝ] Space) (hg : FixesAxis g) (y : Space) :
    ringResidual R ν ψ pr τ (g y) = g (ringResidual R ν ψ pr τ y) := by
  have h1 : Real.exp (τ / 2) • g y = g (Real.exp (τ / 2) • y) := by rw [map_smul]
  have h2 := pf3_varrho_apply g hg (Real.exp (τ / 2) • y)
  have h3 := pf3_apply_two g hg (Real.exp (τ / 2) • y)
  unfold ringResidual physResidualField
  rw [h1, h2, h3, pf3_eR_equiv g hg, map_smul, map_add, map_smul, map_smul]
  have h4 : g e3 = e3 := hg
  rw [h4]

theorem pf3_partial_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ℝ × Space → E}
    {x : ℝ × Space} (hF : DifferentiableAt ℝ F x) (v : Space) :
    fderiv ℝ (fun y => F (x.1, y)) x.2 v = fderiv ℝ F x (0, v) := by
  have hg : HasFDerivAt (fun y : Space => (x.1, y))
      (ContinuousLinearMap.inr ℝ ℝ Space) x.2 :=
    (hasFDerivAt_const x.1 x.2).prodMk (hasFDerivAt_id x.2)
  have hc : HasFDerivAt (fun y : Space => F (x.1, y))
      ((fderiv ℝ F x).comp (ContinuousLinearMap.inr ℝ ℝ Space)) x.2 :=
    HasFDerivAt.comp x.2 hF.hasFDerivAt hg
  rw [hc.fderiv]
  rfl

/-- `D₀S` is jointly continuous for a jointly `C^∞` field `S` (source 4140-4141). -/
theorem pf3_continuous_physDmu (ν : ℝ) (S : ℝ → Space → Space)
    (hS : ContDiff ℝ ∞ (fun x : ℝ × Space => S x.1 x.2)) :
    Continuous (fun x : ℝ × Space => physDmu ν 0 S x.1 x.2) := by
  set Sj : ℝ × Space → Space := fun x => S x.1 x.2 with hSj
  have hd : ∀ x, DifferentiableAt ℝ Sj x := fun x => hS.differentiable (by simp) x
  have dS : ContDiff ℝ ∞ (fun x => fderiv ℝ Sj x) := hS.fderiv_right (m := ∞) (by simp)
  set G : Fin 3 → ℝ × Space → Space := fun j x => fderiv ℝ Sj x (0, coordinateVector j) with hG
  have hGs : ∀ j, ContDiff ℝ ∞ (G j) := fun j => dS.clm_apply contDiff_const
  have hGd : ∀ j x, DifferentiableAt ℝ (G j) x := fun j x => (hGs j).differentiable (by simp) x
  have dG : ∀ j, ContDiff ℝ ∞ (fun x => fderiv ℝ (G j) x) := fun j =>
    (hGs j).fderiv_right (m := ∞) (by simp)
  have key : ∀ x : ℝ × Space, physDmu ν 0 S x.1 x.2 =
      fderiv ℝ Sj x (1, 0) - (1 / 2 : ℝ) • fderiv ℝ Sj x (0, x.2) -
        ν • ∑ j : Fin 3, fderiv ℝ (G j) x (0, coordinateVector j) + ((0 : ℝ) - 1 / 2) • Sj x := by
    intro x
    obtain ⟨τ, y⟩ := x
    have e1 : deriv (fun t => S t y) τ = fderiv ℝ Sj (τ, y) (1, 0) := by
      have hs : HasFDerivAt (fun t : ℝ => ((t, y) : ℝ × Space))
          (ContinuousLinearMap.inl ℝ ℝ Space) τ :=
        hasFDerivAt_prodMk_left τ y
      have := (hd (τ, y)).hasFDerivAt.comp τ hs
      rw [show (fun t => S t y) = Sj ∘ (fun t : ℝ => ((t, y) : ℝ × Space)) from rfl,
        this.hasDerivAt.deriv]
      simp
    have e2 : fderiv ℝ (S τ) y y = fderiv ℝ Sj (τ, y) (0, y) :=
      pf3_partial_eq (F := Sj) (x := (τ, y)) (hd (τ, y)) y
    have e3 : physLap (S τ) y = ∑ j : Fin 3, fderiv ℝ (G j) (τ, y) (0, coordinateVector j) := by
      unfold physLap physPd2
      refine Finset.sum_congr rfl fun j _ => ?_
      have hfun : (fun y' => physPd (S τ) j y') = fun y' => G j (τ, y') := by
        funext y'
        exact pf3_partial_eq (F := Sj) (x := (τ, y')) (hd (τ, y')) (coordinateVector j)
      rw [hfun]
      exact pf3_partial_eq (F := G j) (x := (τ, y)) (hGd j (τ, y)) (coordinateVector j)
    unfold physDmu
    rw [e1, e2, e3]
  clear_value G Sj
  have hcont : Continuous (fun x : ℝ × Space =>
      fderiv ℝ Sj x (1, 0) - (1 / 2 : ℝ) • fderiv ℝ Sj x (0, x.2) -
        ν • ∑ j : Fin 3, fderiv ℝ (G j) x (0, coordinateVector j) + ((0 : ℝ) - 1 / 2) • Sj x) := by
    have a1 : Continuous fun x : ℝ × Space => fderiv ℝ Sj x (1, 0) :=
      (dS.clm_apply (contDiff_const : ContDiff ℝ ∞
        fun _ : ℝ × Space => ((1 : ℝ), (0 : Space)))).continuous
    have a2 : Continuous fun x : ℝ × Space => fderiv ℝ Sj x (0, x.2) :=
      (dS.clm_apply ((contDiff_const : ContDiff ℝ ∞ fun _ : ℝ × Space => (0 : ℝ)).prodMk
        contDiff_snd)).continuous
    have a3j : ∀ j : Fin 3, Continuous fun x : ℝ × Space =>
        fderiv ℝ (G j) x (0, coordinateVector j) := fun j =>
      ((dG j).clm_apply (contDiff_const : ContDiff ℝ ∞
        fun _ : ℝ × Space => ((0 : ℝ), coordinateVector j))).continuous
    have a3 : Continuous fun x : ℝ × Space =>
        ∑ j : Fin 3, fderiv ℝ (G j) x (0, coordinateVector j) :=
      continuous_finsetSum _ fun j _ => a3j j
    have a4 : Continuous Sj := hS.continuous
    have b2 : Continuous fun x : ℝ × Space => (1 / 2 : ℝ) • fderiv ℝ Sj x (0, x.2) :=
      a2.const_smul (1 / 2 : ℝ)
    have b3 : Continuous fun x : ℝ × Space =>
        ν • ∑ j : Fin 3, fderiv ℝ (G j) x (0, coordinateVector j) :=
      a3.const_smul ν
    have b4 : Continuous fun x : ℝ × Space => ((0 : ℝ) - 1 / 2) • Sj x :=
      a4.const_smul ((0 : ℝ) - 1 / 2)
    exact (a1.sub b2).sub b3 |>.add b4
  exact hcont.congr fun x => (key x).symm

end UnforcedLeray.Short.PartIIIb.Concrete
