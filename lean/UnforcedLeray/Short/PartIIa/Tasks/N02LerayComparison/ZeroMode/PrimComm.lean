import UnforcedLeray.Short.PartIIa.Sub.N02_3
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ZeroMode.PrimSmooth

/-!


Source of record: `the November 2 reference manuscript`, lines 1731-1732
("including one `S` derivative"; "All projection operations commute with `S`").
Prop: `ZeroPrimComm` (`Sub/N02_3.lean`).

Plan. `opS (zPrimC g) p = p.1 • pdS (zPrimC g) p` and `zPrimC (opS g) p = p.1 • zPrimC (pdS g) p`
(the factor `p.1` is independent of `t`). So it suffices that `pdS (zPrimC g) = zPrimC (pdS g)`.
Let `Φ = zPrimC g`, `h = pdS g`, and `D(p) = ∂_s Φ(p) - zPrimC h (p)`.
1. `∂_η ∂_s Φ = ∂_s ∂_η Φ = ∂_s g = h` (symmetry of mixed second derivatives of the smooth `Φ`).
2. `∂_η (zPrimC h) = h` (`pdEta_zPrimC`).
3. So `∂_η D = 0` along each `η`-line, hence `D` is constant in `η`.
4. `D(s, q, 0) = 0`: `Φ(·, q, 0) ≡ 0` and `zPrimC h (s, q, 0) = 0`.
No band hypothesis is used.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

namespace ZeroPrimCommAux

/-- The derivative along the `η`-line of a differentiable function. -/
lemma hasDerivAt_eta {F : Profile → ℂ} (hF : Differentiable ℝ F) (p : Profile) :
    HasDerivAt (fun η : ℝ => F (p.1, p.2.1, η)) (fderiv ℝ F p (0, 0, 1)) p.2.2 := by
  have hl : HasDerivAt (fun η : ℝ => ((p.1, p.2.1, η) : Profile))
      ((0 : ℝ), (0 : ℝ), (1 : ℝ)) p.2.2 := by
    have h1 : HasDerivAt (fun _ : ℝ => p.1) (0 : ℝ) p.2.2 := by apply hasDerivAt_const
    have h2 : HasDerivAt (fun _ : ℝ => p.2.1) (0 : ℝ) p.2.2 := by apply hasDerivAt_const
    have h3 : HasDerivAt (fun η : ℝ => η) (1 : ℝ) p.2.2 := hasDerivAt_id' _
    exact h1.prodMk (h2.prodMk h3)
  exact (hF p).hasFDerivAt.comp_hasDerivAt p.2.2 hl

/-- The derivative along the `s`-line of a differentiable function. -/
lemma hasDerivAt_s {F : Profile → ℂ} (hF : Differentiable ℝ F) (p : Profile) :
    HasDerivAt (fun σ : ℝ => F (σ, p.2.1, p.2.2)) (fderiv ℝ F p (1, 0, 0)) p.1 := by
  have hl : HasDerivAt (fun σ : ℝ => ((σ, p.2.1, p.2.2) : Profile))
      ((1 : ℝ), (0 : ℝ), (0 : ℝ)) p.1 := by
    have h1 : HasDerivAt (fun σ : ℝ => σ) (1 : ℝ) p.1 := hasDerivAt_id' _
    have h2 : HasDerivAt (fun _ : ℝ => p.2.1) (0 : ℝ) p.1 := by apply hasDerivAt_const
    have h3 : HasDerivAt (fun _ : ℝ => p.2.2) (0 : ℝ) p.1 := by apply hasDerivAt_const
    exact h1.prodMk (h2.prodMk h3)
  exact (hF p).hasFDerivAt.comp_hasDerivAt p.1 hl

/-- Mixed second derivatives of a `C^2` profile function commute. -/
lemma fderiv_comm {Φ : Profile → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (p v w : Profile) :
    fderiv ℝ (fun x => fderiv ℝ Φ x v) p w = fderiv ℝ (fun x => fderiv ℝ Φ x w) p v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ Φ) p :=
    ((hΦ.fderiv_right (m := 1) (by norm_cast)).differentiable one_ne_zero) p
  have hsymm : IsSymmSndFDerivAt ℝ Φ p :=
    ContDiffAt.isSymmSndFDerivAt (hΦ.contDiffAt) (by simp)
  have key : ∀ u z : Profile,
      fderiv ℝ (fun x => fderiv ℝ Φ x u) p z = fderiv ℝ (fderiv ℝ Φ) p z u := by
    intro u z
    have hu : DifferentiableAt ℝ (fun _ : Profile => u) p := differentiableAt_const u
    rw [fderiv_clm_apply hd hu]
    simp
  rw [key, key]
  exact hsymm w v

/-- `pdS g` is smooth when `g` is. -/
lemma pdS_contDiff {g : Profile → ℂ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (pdS g) := by
  have h1 : ContDiff ℝ ∞ (fderiv ℝ g) := hg.fderiv_right (by simp)
  exact h1.clm_apply contDiff_const

/-- Key identity: `pdS (zPrimC g) = zPrimC (pdS g)`. -/
lemma pdS_zPrimC {g : Profile → ℂ} (hg : ContDiff ℝ ∞ g) (p : Profile) :
    pdS (zPrimC g) p = zPrimC (pdS g) p := by
  have hΦ : ContDiff ℝ ∞ (zPrimC g) := ZeroPrimSmoothAux.zPrimC_contDiff hg
  have hΦd : Differentiable ℝ (zPrimC g) := hΦ.differentiable (by simp)
  have hh : ContDiff ℝ ∞ (pdS g) := pdS_contDiff hg
  have hhd : Differentiable ℝ (zPrimC (pdS g)) :=
    (ZeroPrimSmoothAux.zPrimC_contDiff hh).differentiable (by simp)
  have hAdiff : Differentiable ℝ (fun x : Profile => fderiv ℝ (zPrimC g) x (1, 0, 0)) :=
    ((hΦ.fderiv_right (m := 1) (by norm_cast)).clm_apply contDiff_const).differentiable
      one_ne_zero
  have hEta : (fun x : Profile => fderiv ℝ (zPrimC g) x (0, 0, 1)) = g :=
    funext fun x => ZeroPrimSmoothAux.pdEta_zPrimC hg x
  -- `∂_η D = 0` along every η-line
  have hF : ∀ s q η : ℝ, HasDerivAt
      (fun η' : ℝ => fderiv ℝ (zPrimC g) (s, q, η') (1, 0, 0) - zPrimC (pdS g) (s, q, η')) 0 η := by
    intro s q η
    have hA := hasDerivAt_eta hAdiff (s, q, η)
    have hB := hasDerivAt_eta hhd (s, q, η)
    have hsym : fderiv ℝ (fun x => fderiv ℝ (zPrimC g) x (1, 0, 0)) (s, q, η) (0, 0, 1)
        = pdS g (s, q, η) := by
      rw [fderiv_comm hΦ (s, q, η) (1, 0, 0) (0, 0, 1), hEta]
      rfl
    have hB' : fderiv ℝ (zPrimC (pdS g)) (s, q, η) (0, 0, 1) = pdS g (s, q, η) :=
      ZeroPrimSmoothAux.pdEta_zPrimC hh (s, q, η)
    have hdiff := hA.sub hB
    rw [hsym, hB', sub_self] at hdiff
    exact hdiff
  -- `D` is constant in `η`
  have hconst : ∀ s q η : ℝ,
      fderiv ℝ (zPrimC g) (s, q, η) (1, 0, 0) - zPrimC (pdS g) (s, q, η) = 0 := by
    intro s q η
    have hc := is_const_of_deriv_eq_zero
      (f := fun η' : ℝ => fderiv ℝ (zPrimC g) (s, q, η') (1, 0, 0)
        - zPrimC (pdS g) (s, q, η'))
      (fun x => (hF s q x).differentiableAt) (fun x => (hF s q x).deriv) η 0
    have h0 : HasDerivAt (fun σ : ℝ => zPrimC g (σ, q, 0))
        (fderiv ℝ (zPrimC g) (s, q, 0) (1, 0, 0)) s := hasDerivAt_s hΦd (s, q, 0)
    have hz : HasDerivAt (fun σ : ℝ => zPrimC g (σ, q, 0)) 0 s := by
      have hfun : (fun σ : ℝ => zPrimC g (σ, q, 0)) = fun _ => (0 : ℂ) := by
        funext σ
        simp [zPrimC]
      rw [hfun]
      exact hasDerivAt_const _ _
    have hz0 : fderiv ℝ (zPrimC g) (s, q, 0) (1, 0, 0) = 0 := h0.unique hz
    have hzc : zPrimC (pdS g) (s, q, 0) = 0 := by simp [zPrimC]
    simpa [hz0, hzc] using hc
  exact sub_eq_zero.mp (hconst p.1 p.2.1 p.2.2)

end ZeroPrimCommAux

/-- **L1b (primitive commutes with `S`), proved.** For a smooth band function `g`,
`opS (zPrimC g) = zPrimC (opS g)`. The band hypothesis is not used. -/
theorem zeroPrimComm : UnforcedLeray.Short.PartIIa.ZeroPrimComm := by
  intro g hg _
  funext p
  have hR : zPrimC (opS g) p = p.1 • zPrimC (pdS g) p := by
    show (∫ t in (0 : ℝ)..p.2.2, opS g (p.1, p.2.1, t))
      = p.1 • ∫ t in (0 : ℝ)..p.2.2, pdS g (p.1, p.2.1, t)
    rw [← intervalIntegral.integral_smul]
    exact intervalIntegral.integral_congr fun t _ => rfl
  show p.1 • pdS (zPrimC g) p = zPrimC (opS g) p
  rw [hR, ZeroPrimCommAux.pdS_zPrimC hg p]

end UnforcedLeray.Short.PartIIa
