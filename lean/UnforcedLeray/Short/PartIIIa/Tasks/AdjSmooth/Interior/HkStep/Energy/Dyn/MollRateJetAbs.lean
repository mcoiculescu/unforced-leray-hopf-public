import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Dyn.Defs
import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Shared
import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.TimeJets.Defs
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Normed.Group.Basic

/-!
# `PartIII-a:T21/2/7/2/1/1/5/18/1/4`: `MollRateJetAbs` (`mollRateJetAbs`)

Source of record: `the November 2 reference manuscript` (SP) lines 3060-3071.

`mollRateV ν n φ V χ = -(ν (∂₀₀ + ∂₁₁)(ρ_n ⋆ φ) + Σ_l (∂_l ρ_n) ⋆ V_l - ρ_n ⋆ χ)`, and by
`CellConvDeriv` every `adjSpatial [0,0] (cellMoll n φ)` is `cellConv (pdWordR [0,0] ρ_n) φ`, so the
rate is a fixed linear combination of the five convolutions `cellConv K_i (f_i r)` with
`K_i ∈ {∂₀∂₀ρ_n, ∂₁∂₁ρ_n, ∂₀ρ_n, ∂₁ρ_n, ρ_n}` and `f_i ∈ {φ, V₀, V₁, χ}`.  Each convolution is in
`C((a,b); H^∞_{-m,c})` by `MollConvJet`.  The linear combination is handled by the
linear-combination lemma `mrjAdjHkAll_lin` (the content of `AdjHkAllLinear`, written out here so that
the statement of `mollRateJetAbs` needs no extra hypothesis), and the smoothness of the fields by
`mrjAdj_lin` (classical linearity of `pdCx` on smooth fields).  The mollifier facts
(`MollKerProps`, `pdWordR_props`) are proved inline.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## The mollifier kernel -/

theorem mrj_molKer (n : ℕ) :
    ContDiff ℝ ∞ (molKer n) ∧ HasCompactSupport (molKer n) ∧
      ∀ y : ℝ × ℝ, 1 < ‖y‖ → molKer n y = 0 := by
  refine ⟨(molBump n).contDiff_normed, (molBump n).hasCompactSupport_normed, ?_⟩
  intro y hy
  unfold molKer
  by_contra hne
  have hmem : y ∈ Function.support ((molBump n).normed volume) := hne
  rw [(molBump n).support_normed_eq] at hmem
  rw [Metric.mem_ball, dist_zero_right] at hmem
  have hrOut : (molBump n).rOut ≤ 1 := by
    show 1 / ((n : ℝ) + 1) ≤ 1
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [div_le_one (by positivity)]
    linarith
  linarith

/-- The iterated partials of a smooth compactly supported kernel vanishing outside the unit ball. -/
theorem mrj_pdWordR_props (K : ℝ × ℝ → ℝ) (hK : ContDiff ℝ ∞ K) (hKs : HasCompactSupport K)
    (hK1 : ∀ y : ℝ × ℝ, 1 < ‖y‖ → K y = 0) (w : List (Fin 2)) :
    ContDiff ℝ ∞ (pdWordR w K) ∧ HasCompactSupport (pdWordR w K) ∧
      ∀ y : ℝ × ℝ, 1 < ‖y‖ → pdWordR w K y = 0 := by
  induction w with
  | nil => exact ⟨hK, hKs, hK1⟩
  | cons j w ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · exact B0579.contDiff_pd h1 j
    · have hpd : B0579.pd j (pdWordR w K) =
          fun x => fderiv ℝ (pdWordR w K) x (B0579.dir j) := rfl
      show HasCompactSupport (B0579.pd j (pdWordR w K))
      rw [hpd]
      exact h2.fderiv_apply ℝ (B0579.dir j)
    · intro y hy
      show B0579.pd j (pdWordR w K) y = 0
      have hopen : IsOpen {z : ℝ × ℝ | 1 < ‖z‖} := isOpen_lt continuous_const continuous_norm
      have hev : pdWordR w K =ᶠ[𝓝 y] (fun _ : ℝ × ℝ => (0 : ℝ)) :=
        Filter.eventually_of_mem (hopen.mem_nhds hy) (fun z hz => h3 z hz)
      unfold B0579.pd
      rw [hev.fderiv_eq]
      simp

/-! ## Linear combinations and `adjSpatial` -/

/-- The pointwise linear combination `α F + β G` of two fields. -/
def mrjLin2 (α β : ℂ) (F G : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ := fun x => α * F x + β * G x

theorem mrj_contDiff_pdCx {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (k : Fin 2) :
    ContDiff ℝ ∞ (pdCx k g) :=
  ((contDiff_infty_iff_fderiv.1 hg).2).clm_apply contDiff_const

theorem mrj_contDiff_adjSpatial {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (w : List (Fin 2)) :
    ContDiff ℝ ∞ (adjSpatial w g) := by
  induction w with
  | nil => exact hg
  | cons k w ih => exact mrj_contDiff_pdCx ih k

theorem mrjLin2_contDiff (α β : ℂ) {F G : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F)
    (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (mrjLin2 α β F G) :=
  (contDiff_const.mul hF).add (contDiff_const.mul hG)

theorem mrjPdCx_lin (k : Fin 2) (α β : ℂ) {A B : ℝ × ℝ → ℂ}
    (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) :
    pdCx k (mrjLin2 α β A B) = mrjLin2 α β (pdCx k A) (pdCx k B) := by
  funext y
  have hdA : DifferentiableAt ℝ A y := (contDiff_infty_iff_fderiv.1 hA).1 y
  have hdB : DifferentiableAt ℝ B y := (contDiff_infty_iff_fderiv.1 hB).1 y
  show fderiv ℝ (fun x => α * A x + β * B x) y (B0579.dir k) =
    α * fderiv ℝ A y (B0579.dir k) + β * fderiv ℝ B y (B0579.dir k)
  rw [fderiv_fun_add (hdA.const_mul α) (hdB.const_mul β), fderiv_const_mul hdA α,
    fderiv_const_mul hdB β]
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- `adjSpatial w` is linear on smooth fields. -/
theorem mrjAdj_lin (w : List (Fin 2)) (α β : ℂ) :
    ∀ {F G : ℝ × ℝ → ℂ}, ContDiff ℝ ∞ F → ContDiff ℝ ∞ G →
      adjSpatial w (mrjLin2 α β F G) = mrjLin2 α β (adjSpatial w F) (adjSpatial w G) := by
  induction w with
  | nil => intro F G _ _; rfl
  | cons k w ih =>
    intro F G hF hG
    show pdCx k (adjSpatial w (mrjLin2 α β F G)) =
      mrjLin2 α β (pdCx k (adjSpatial w F)) (pdCx k (adjSpatial w G))
    rw [ih hF hG]
    exact mrjPdCx_lin k α β (mrj_contDiff_adjSpatial hF w) (mrj_contDiff_adjSpatial hG w)

/-- The four-term combination of the rate, with its `adjSpatial` jets. -/
theorem mrjAdj_chain (w : List (Fin 2)) (a : ℂ) {F1 F2 F3 F4 F5 : ℝ × ℝ → ℂ}
    (h1 : ContDiff ℝ ∞ F1) (h2 : ContDiff ℝ ∞ F2) (h3 : ContDiff ℝ ∞ F3)
    (h4 : ContDiff ℝ ∞ F4) (h5 : ContDiff ℝ ∞ F5) :
    adjSpatial w (mrjLin2 1 1 (mrjLin2 1 (-1) (mrjLin2 1 (-1) (mrjLin2 a a F1 F2) F3) F4) F5)
      = mrjLin2 1 1 (mrjLin2 1 (-1) (mrjLin2 1 (-1) (mrjLin2 a a (adjSpatial w F1)
          (adjSpatial w F2)) (adjSpatial w F3)) (adjSpatial w F4)) (adjSpatial w F5) := by
  have s12 := mrjLin2_contDiff a a h1 h2
  have s123 := mrjLin2_contDiff 1 (-1) s12 h3
  have s1234 := mrjLin2_contDiff 1 (-1) s123 h4
  rw [mrjAdj_lin w 1 1 s1234 h5, mrjAdj_lin w 1 (-1) s123 h4, mrjAdj_lin w 1 (-1) s12 h3,
    mrjAdj_lin w a a h1 h2]

/-! ## Linear combinations of `C(I; H^∞_{-m,c})` families (the content of `AdjHkAllLinear`) -/

theorem mrj_eLp_lin_le {μ : Measure (ℝ × ℝ)} (α β : ℂ) (u v : ℝ × ℝ → ℂ)
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    eLpNorm (fun x => α * u x + β * v x) 2 μ ≤ ‖α‖ₑ * eLpNorm u 2 μ + ‖β‖ₑ * eLpNorm v 2 μ := by
  have e1 : eLpNorm (fun x => α * u x) 2 μ = ‖α‖ₑ * eLpNorm u 2 μ := by
    have := eLpNorm_const_smul α u 2 μ
    simpa [Pi.smul_def, smul_eq_mul] using this
  have e2 : eLpNorm (fun x => β * v x) 2 μ = ‖β‖ₑ * eLpNorm v 2 μ := by
    have := eLpNorm_const_smul β v 2 μ
    simpa [Pi.smul_def, smul_eq_mul] using this
  calc eLpNorm (fun x => α * u x + β * v x) 2 μ
      ≤ eLpNorm (fun x => α * u x) 2 μ + eLpNorm (fun x => β * v x) 2 μ :=
        eLpNorm_add_le (hu.const_mul α).1 (hv.const_mul β).1 one_le_two
    _ = ‖α‖ₑ * eLpNorm u 2 μ + ‖β‖ₑ * eLpNorm v 2 μ := by rw [e1, e2]

theorem mrj_int_lin {μ : Measure (ℝ × ℝ)} (α β : ℂ) (φ φ' ψ : ℝ × ℝ → ℂ)
    (h1 : Integrable (fun x => φ x * ψ x) μ) (h2 : Integrable (fun x => φ' x * ψ x) μ) :
    ∫ x, (α * φ x + β * φ' x) * ψ x ∂μ = α * ∫ x, φ x * ψ x ∂μ + β * ∫ x, φ' x * ψ x ∂μ := by
  have e : (fun x => (α * φ x + β * φ' x) * ψ x) =
      fun x => α * (φ x * ψ x) + β * (φ' x * ψ x) := by
    funext x
    ring
  rw [e, integral_add (h1.const_mul α) (h2.const_mul β), integral_const_mul, integral_const_mul]

theorem mrj_hwcd_lin {c : ℝ} {j : Fin 2} {φ φ' g g' : ℝ × ℝ → ℂ} (α β : ℂ)
    (h1 : HasWeakCellDerivC c j φ g) (h2 : HasWeakCellDerivC c j φ' g') :
    HasWeakCellDerivC c j (fun x => α * φ x + β * φ' x) (fun x => α * g x + β * g' x) := by
  unfold HasWeakCellDerivC at h1 h2 ⊢
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  refine ⟨fun ψ hψ => ⟨?_, ?_⟩, fun ψ hψ => ?_⟩
  · have e : (fun x => (α * φ x + β * φ' x) * (B0579.pd j ψ x : ℂ)) =
        fun x => α * (φ x * (B0579.pd j ψ x : ℂ)) + β * (φ' x * (B0579.pd j ψ x : ℂ)) := by
      funext x
      ring
    show IntegrableOn (fun x => (α * φ x + β * φ' x) * (B0579.pd j ψ x : ℂ)) (B0579.cell c)
    rw [e]
    exact (Integrable.const_mul (h1a ψ hψ).1 α).add (Integrable.const_mul (h2a ψ hψ).1 β)
  · have e : (fun x => (α * g x + β * g' x) * (ψ x : ℂ)) =
        fun x => α * (g x * (ψ x : ℂ)) + β * (g' x * (ψ x : ℂ)) := by
      funext x
      ring
    show IntegrableOn (fun x => (α * g x + β * g' x) * (ψ x : ℂ)) (B0579.cell c)
    rw [e]
    exact (Integrable.const_mul (h1a ψ hψ).2 α).add (Integrable.const_mul (h2a ψ hψ).2 β)
  · show ∫ x in B0579.cell c, (α * φ x + β * φ' x) * (B0579.pd j ψ x : ℂ) =
      -∫ x in B0579.cell c, (α * g x + β * g' x) * (ψ x : ℂ)
    rw [mrj_int_lin α β φ φ' (fun x => (B0579.pd j ψ x : ℂ)) (h1a ψ hψ).1 (h2a ψ hψ).1,
      mrj_int_lin α β g g' (fun x => (ψ x : ℂ)) (h1a ψ hψ).2 (h2a ψ hψ).2,
      h1b ψ hψ, h2b ψ hψ]
    ring

theorem mrj_isCellJet_lin {c m : ℝ} {k : ℕ} {f g : ℝ × ℝ → ℂ} {D E : List (Fin 2) → ℝ × ℝ → ℂ}
    (α β : ℂ) (h1 : IsCellJet c m k f D) (h2 : IsCellJet c m k g E) :
    IsCellJet c m k (mrjLin2 α β f g) (fun w => mrjLin2 α β (D w) (E w)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show mrjLin2 α β (D []) (E []) = mrjLin2 α β f g
    rw [h1.base, h2.base]
  · intro w hw x
    show mrjLin2 α β (D w) (E w) (x.1 + c, x.2) = mrjLin2 α β (D w) (E w) x
    unfold mrjLin2
    rw [h1.periodic w hw x, h2.periodic w hw x]
  · intro w hw
    exact ((h1.memX w hw).const_mul α).add ((h2.memX w hw).const_mul β)
  · intro j w hw
    exact mrj_hwcd_lin α β (h1.deriv j w hw) (h2.deriv j w hw)

/-- Linear combinations of `C(I; H^∞_{-m,c})` families (fields `α D + β E`). -/
theorem mrjAdjHkAll_lin {c m : ℝ} {I : Set ℝ} {f g : ℝ → ℝ × ℝ → ℂ}
    {D E : ℝ → List (Fin 2) → ℝ × ℝ → ℂ} (α β : ℂ)
    (hf : AdjHkAll c m I f D) (hg : AdjHkAll c m I g E) :
    AdjHkAll c m I (fun r => mrjLin2 α β (f r) (g r))
      (fun r w => mrjLin2 α β (D r w) (E r w)) := by
  obtain ⟨hf1, hf2⟩ := hf
  obtain ⟨hg1, hg2⟩ := hg
  refine ⟨fun r hr k => mrj_isCellJet_lin α β (hf1 r hr k) (hg1 r hr k), fun w r hr => ?_⟩
  have hbd : ∀ᶠ r' in 𝓝[I] r,
      xNorm c (-m) (mrjLin2 α β (D r' w) (E r' w) - mrjLin2 α β (D r w) (E r w)) ≤
        ‖α‖ₑ * xNorm c (-m) (D r' w - D r w) + ‖β‖ₑ * xNorm c (-m) (E r' w - E r w) := by
    filter_upwards [self_mem_nhdsWithin] with r' hr'
    have m1 : MemLp (D r' w) 2 (B0579.cellMeasure c (-m)) :=
      (hf1 r' hr' w.length).memX w le_rfl
    have m0 : MemLp (D r w) 2 (B0579.cellMeasure c (-m)) :=
      (hf1 r hr w.length).memX w le_rfl
    have n1 : MemLp (E r' w) 2 (B0579.cellMeasure c (-m)) :=
      (hg1 r' hr' w.length).memX w le_rfl
    have n0 : MemLp (E r w) 2 (B0579.cellMeasure c (-m)) :=
      (hg1 r hr w.length).memX w le_rfl
    have e : mrjLin2 α β (D r' w) (E r' w) - mrjLin2 α β (D r w) (E r w) =
        mrjLin2 α β (D r' w - D r w) (E r' w - E r w) := by
      funext x
      simp only [Pi.sub_apply, mrjLin2]
      ring
    rw [e]
    exact mrj_eLp_lin_le (μ := B0579.cellMeasure c (-m)) α β (D r' w - D r w)
      (E r' w - E r w) (m1.sub m0) (n1.sub n0)
  have hT : Tendsto (fun r' => ‖α‖ₑ * xNorm c (-m) (D r' w - D r w) +
      ‖β‖ₑ * xNorm c (-m) (E r' w - E r w)) (𝓝[I] r) (𝓝 0) := by
    have h1 := ENNReal.Tendsto.const_mul (hf2 w r hr) (Or.inr (enorm_ne_top (x := α)))
    have h2 := ENNReal.Tendsto.const_mul (hg2 w r hr) (Or.inr (enorm_ne_top (x := β)))
    have := h1.add h2
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hT
    (Eventually.of_forall fun _ => zero_le) hbd

/-- `AdjHkAll` depends only on the values on `I`. -/
theorem mrjAdjHkAll_congr {c m : ℝ} {I : Set ℝ} {f g : ℝ → ℝ × ℝ → ℂ}
    {D E : ℝ → List (Fin 2) → ℝ × ℝ → ℂ}
    (hfg : ∀ r ∈ I, f r = g r) (hDE : ∀ r ∈ I, ∀ w, D r w = E r w)
    (h : AdjHkAll c m I f D) : AdjHkAll c m I g E := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun r hr k => ?_, fun w r hr => ?_⟩
  · have e1 : g r = f r := (hfg r hr).symm
    have e2 : E r = D r := funext fun w => (hDE r hr w).symm
    rw [e1, e2]
    exact h1 r hr k
  · refine Tendsto.congr' ?_ (h2 w r hr)
    filter_upwards [self_mem_nhdsWithin] with r' hr'
    simp only [hDE r' hr' w, hDE r hr w]

/-! ## The main theorem -/

theorem mollRateJetAbs (hJ : UnforcedLeray.Short.IIIa.MollConvJet)
    (hD : UnforcedLeray.Short.IIIa.CellConvDeriv) :
    UnforcedLeray.Short.IIIa.MollRateJetAbs := by
  intro c m ν n a b φ χ V hc hφ hV hχ
  obtain ⟨hK, hKs, hK1⟩ := mrj_molKer n
  -- each convolution piece is an `AdjHkAll` family (`MollConvJet`)
  have J : ∀ (w : List (Fin 2)) (f : ℝ → ℝ × ℝ → ℂ), XFam c m a b f →
      AdjHkAll c m (Ioo a b) (fun r => cellConv (pdWordR w (molKer n)) (f r))
        (fun r w' => adjSpatial w' (cellConv (pdWordR w (molKer n)) (f r))) := by
    intro w f hf
    obtain ⟨p1, p2, p3⟩ := mrj_pdWordR_props (molKer n) hK hKs hK1 w
    exact hJ c m (pdWordR w (molKer n)) f a b hc p1 p2 p3 hf
  -- and it is smooth at each time
  have Sm : ∀ (w : List (Fin 2)) (f : ℝ → ℝ × ℝ → ℂ), XFam c m a b f → ∀ r ∈ Ioo a b,
      ContDiff ℝ ∞ (cellConv (pdWordR w (molKer n)) (f r)) := by
    intro w f hf r hr
    obtain ⟨p1, p2, _⟩ := mrj_pdWordR_props (molKer n) hK hKs hK1 w
    exact (hD c m (pdWordR w (molKer n)) (f r) hc p1 p2 (hf.1 r hr).1 (hf.1 r hr).2).1
  have hA := mrjAdjHkAll_lin (-(ν : ℂ)) (-(ν : ℂ)) (J [0, 0] φ hφ) (J [1, 1] φ hφ)
  have hB := mrjAdjHkAll_lin 1 (-1) hA (J [0] (V 0) (hV 0))
  have hC := mrjAdjHkAll_lin 1 (-1) hB (J [1] (V 1) (hV 1))
  have hG := mrjAdjHkAll_lin 1 1 hC (J [] χ hχ)
  -- the rate is this combination pointwise on `(a, b)`
  have hfun : ∀ r ∈ Ioo a b, mollRateV ν n (φ r) (fun l => V l r) (χ r) =
      mrjLin2 1 1 (mrjLin2 1 (-1) (mrjLin2 1 (-1) (mrjLin2 (-(ν : ℂ)) (-(ν : ℂ))
        (cellConv (pdWordR [0, 0] (molKer n)) (φ r))
        (cellConv (pdWordR [1, 1] (molKer n)) (φ r)))
        (cellConv (pdWordR [0] (molKer n)) (V 0 r)))
        (cellConv (pdWordR [1] (molKer n)) (V 1 r)))
        (cellConv (molKer n) (χ r)) := by
    intro r hr
    have e1 : adjSpatial [0, 0] (cellMoll n (φ r)) =
        cellConv (pdWordR [0, 0] (molKer n)) (φ r) :=
      (hD c m (molKer n) (φ r) hc hK hKs (hφ.1 r hr).1 (hφ.1 r hr).2).2.2 [0, 0]
    have e2 : adjSpatial [1, 1] (cellMoll n (φ r)) =
        cellConv (pdWordR [1, 1] (molKer n)) (φ r) :=
      (hD c m (molKer n) (φ r) hc hK hKs (hφ.1 r hr).1 (hφ.1 r hr).2).2.2 [1, 1]
    funext x
    simp only [mollRateV, mrjLin2]
    rw [e1, e2]
    simp only [pdWordR, cellMoll, Fin.sum_univ_two]
    ring
  -- the jets of the rate are the same combination of the jets of the pieces
  have hDeq : ∀ r ∈ Ioo a b, ∀ w : List (Fin 2),
      adjSpatial w (mollRateV ν n (φ r) (fun l => V l r) (χ r)) =
        mrjLin2 1 1 (mrjLin2 1 (-1) (mrjLin2 1 (-1) (mrjLin2 (-(ν : ℂ)) (-(ν : ℂ))
          (adjSpatial w (cellConv (pdWordR [0, 0] (molKer n)) (φ r)))
          (adjSpatial w (cellConv (pdWordR [1, 1] (molKer n)) (φ r))))
          (adjSpatial w (cellConv (pdWordR [0] (molKer n)) (V 0 r))))
          (adjSpatial w (cellConv (pdWordR [1] (molKer n)) (V 1 r))))
          (adjSpatial w (cellConv (molKer n) (χ r))) := by
    intro r hr w
    rw [hfun r hr]
    have s1 : ContDiff ℝ ∞ (cellConv (pdWordR [0, 0] (molKer n)) (φ r)) :=
      Sm [0, 0] φ hφ r hr
    have s2 : ContDiff ℝ ∞ (cellConv (pdWordR [1, 1] (molKer n)) (φ r)) :=
      Sm [1, 1] φ hφ r hr
    have s3 : ContDiff ℝ ∞ (cellConv (pdWordR [0] (molKer n)) (V 0 r)) :=
      Sm [0] (V 0) (hV 0) r hr
    have s4 : ContDiff ℝ ∞ (cellConv (pdWordR [1] (molKer n)) (V 1 r)) :=
      Sm [1] (V 1) (hV 1) r hr
    have s5 : ContDiff ℝ ∞ (cellConv (molKer n) (χ r)) := Sm [] χ hχ r hr
    exact mrjAdj_chain w (-(ν : ℂ)) s1 s2 s3 s4 s5
  refine mrjAdjHkAll_congr ?_ ?_ hG
  · intro r hr
    exact (hfun r hr).symm
  · intro r hr w
    exact (hDeq r hr w).symm

end UnforcedLeray.Short.IIIa
