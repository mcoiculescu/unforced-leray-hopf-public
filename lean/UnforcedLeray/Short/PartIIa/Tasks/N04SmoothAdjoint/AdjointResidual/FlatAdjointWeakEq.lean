import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N04_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2.R0Invariant
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3.R0Transpose

/-!


Source of record: `the November 2 reference manuscript`,
lines 1842–1843 (Lemma `near:smooth-adjoint-comparison`).

This file proves `theorem flatAdjointWeakEq : FlatAdjointWeakEq` in namespace
`UnforcedLeray.Short.PartIIa` via `flatAdjointWeakEq_of_apply`:
1. `T0flat_eq_PepsC_comp_R0`: `T0flat hc ν μ x = PepsC 0 c (B0225.R0 hc ν μ x)` for all
   `x : HSpace c MeridC`, proved from `r0SolenoidalInvariant` together with the orthogonal
   gradient-closure invariance `r0OrthogonalInvariant` (obtained from `t0adjGradPres` and
   `t0_complex_adjoint` via the exact operator identity
   `T0 hc ν t = e^{t/2} T0adj hc (ν e^{-t}) t ∘ dilH e^{-2t}`).
2. `R0_left_inverse_isMeridTest`: `B0225.R0 hc ν μ AU0 = U` for every smooth meridional test
   `IsMeridTest c u` with `U =ᵐ u` and `AU0 =ᵐ μ • u - AepsVecC ν 0 u`, proved by differentiating
   `t ↦ B0224.T0 hc ν t U` on `(0, ∞)` (`t0_strong_deriv`) and integrating by parts against
   `e^{-μ t}` with `t0_strong_cont_zero`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0224 UnforcedLeray.B0225
  UnforcedLeray.B0226
open UnforcedLeray.Gaussian (Euc gaussKernel)
open UnforcedLeray.Heat (gaussDt)
open UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-! ### 1. Commutation `T0flat hc ν μ x = PepsC 0 c (B0225.R0 hc ν μ x)` -/

/-- Age dilation of a scalar profile by `a > 0`: `(s, q, η) ↦ Φ(a s, q, η)`. -/
private def dilProfile (a : ℝ) (Φ : Profile → ℝ) : Profile → ℝ :=
  fun p => Φ (a * p.1, p.2)

/-- Continuous linear map `(s, q, η) ↦ (a s, q, η)` on `Profile = ℝ × ℝ × ℝ`. -/
private def dilCLM (a : ℝ) : Profile →L[ℝ] Profile :=
  (a • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

private theorem dilProfile_eq_comp (a : ℝ) (Φ : Profile → ℝ) :
    dilProfile a Φ = Φ ∘ dilCLM a := rfl

private theorem isProfileTest_dilProfile {c a : ℝ} (ha : 0 < a) {Φ : Profile → ℝ}
    (hΦ : IsProfileTest c Φ) : IsProfileTest c (dilProfile a Φ) := by
  obtain ⟨s0, s1, L, hs0, hb⟩ := hΦ.band
  refine ⟨?_, ?_, s0 / a, s1 / a, L, div_pos hs0 ha, ?_⟩
  · rw [dilProfile_eq_comp]
    exact hΦ.smooth.comp (dilCLM a).contDiff
  · intro p
    exact hΦ.periodic (a * p.1, p.2)
  · intro p hp
    obtain ⟨h1, h2⟩ := hb (a * p.1, p.2) hp
    refine ⟨⟨?_, ?_⟩, h2⟩
    · rw [div_le_iff₀ ha, mul_comm]
      exact h1.1
    · rw [le_div_iff₀ ha, mul_comm]
      exact h1.2

private theorem cgrad_zero_dilProfile (a : ℝ) {Φ : Profile → ℝ}
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ) :
    cgrad 0 (dilProfile a Φ) = B0224.dil a (cgrad 0 Φ) := by
  funext p
  have hd : DifferentiableAt ℝ Φ (dilCLM a p) :=
    hΦ.differentiable (by simp) (dilCLM a p)
  have hcomp : HasFDerivAt (dilProfile a Φ) ((fderiv ℝ Φ (dilCLM a p)).comp (dilCLM a)) p :=
    hd.hasFDerivAt.comp p (dilCLM a).hasFDerivAt
  have hclm_p : dilCLM a p = (a * p.1, p.2) := by ext <;> simp [dilCLM]
  have hclm_q : dilCLM a (0, 1, 0) = (0, 1, 0) := by ext <;> simp [dilCLM]
  have hclm_e : dilCLM a (0, 0, 1) = (0, 0, 1) := by ext <;> simp [dilCLM]
  have hQ : Axi.dQ (dilProfile a Φ) p = Axi.dQ Φ (a * p.1, p.2) := by
    unfold Axi.dQ
    rw [hcomp.fderiv, ContinuousLinearMap.comp_apply, hclm_p, hclm_q]
  have hE : Axi.dEta (dilProfile a Φ) p = Axi.dEta Φ (a * p.1, p.2) := by
    unfold Axi.dEta
    rw [hcomp.fderiv, ContinuousLinearMap.comp_apply, hclm_p, hclm_e]
  simp only [cgrad, Deps_zero, B0224.dil, hQ, hE]

/-- Exact relation between `T0` and `T0adj`:
`T0 hc ν t f = e^{t/2} • T0adj hc (ν e^{-t}) t (dilH e^{-2t} f)`. -/
private theorem T0_eq_smul_T0adj_comp_dilH {c : ℝ} (hc : 0 < c) (ν t : ℝ)
    (f : HSpace c MeridC) :
    B0224.T0 hc ν t f =
      Real.exp (t / 2) • B0224.T0adj hc (ν * Real.exp (-t)) t
        (B0224.dilH (Real.exp_pos (-2 * t)) f) := by
  have hht : B0224.heatTime ν t = B0224.heatTimeAdj (ν * Real.exp (-t)) t := by
    funext s
    unfold B0224.heatTime B0224.heatTimeAdj
    have hexp : Real.exp (-t) * Real.exp t = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    linear_combination -(ν * s) * hexp
  have hdil_eq : Real.exp (-t) = Real.exp (-2 * t) * Real.exp t := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h1 : (B0224.heatH hc (B0224.measurable_heatTime ν t) :
      HSpace c MeridC →L[ℝ] HSpace c MeridC) =
      B0224.heatH hc (B0224.measurable_heatTimeAdj (ν * Real.exp (-t)) t) :=
    B0224.heatH_congr hc hht _ _
  have h2 : (B0224.dilH (Real.exp_pos (-t)) : HSpace c MeridC →L[ℝ] HSpace c MeridC) =
      B0224.dilH (Real.exp_pos t) ∘L B0224.dilH (Real.exp_pos (-2 * t)) := by
    rw [B0224.dilH_comp_dilH (Real.exp_pos t) (Real.exp_pos (-2 * t))]
    exact B0224.dilH_congr hdil_eq _ _
  have hT0 : B0224.T0 hc ν t f =
      B0224.heatH hc (B0224.measurable_heatTimeAdj (ν * Real.exp (-t)) t)
        (B0224.dilH (Real.exp_pos t) (B0224.dilH (Real.exp_pos (-2 * t)) f)) := by
    change (B0224.heatH hc (B0224.measurable_heatTime ν t) ∘L B0224.dilH (Real.exp_pos (-t))) f = _
    rw [h1, h2]
    rfl
  rw [hT0]
  unfold B0224.T0adj
  rw [smul_apply, ContinuousLinearMap.comp_apply, smul_smul, ← Real.exp_add]
  have h0 : t / 2 + -t / 2 = 0 := by ring
  rw [h0, Real.exp_zero, one_smul]

/-- `T0 hc ν t` maps every profile-test gradient `toLp (cgrad 0 Φ.1)` into `(solenoidalHC 0 c)ᗮ`. -/
private theorem t0GradPres (c ν : ℝ) (hc : 0 < c) (t : ℝ) (ht : 0 < t)
    (Φ : ProfileTest c) (h : MemLp (cgrad 0 Φ.1) 2 (measureH c)) :
    B0224.T0 hc ν t (h.toLp (cgrad 0 Φ.1)) ∈ (solenoidalHC 0 c)ᗮ := by
  set a : ℝ := Real.exp (-2 * t)
  have ha : 0 < a := Real.exp_pos (-2 * t)
  set Φa : ProfileTest c := ⟨dilProfile a Φ.1, isProfileTest_dilProfile ha Φ.2⟩
  set g : HSpace c MeridC := B0224.dilH ha (h.toLp (cgrad 0 Φ.1))
  have hg_ae : (g : Profile → MeridC) =ᵐ[measureH c] cgrad 0 Φa.1 := by
    have h1 := B0224.coeFn_dilH ha (h.toLp (cgrad 0 Φ.1))
    have hsm : StronglyMeasurable (cgrad 0 Φ.1) := by
      obtain ⟨hcont, -, -⟩ := t0gCgradBand_proof c Φ.1 Φ.2
      exact hcont.stronglyMeasurable
    have h2 := B0224.dil_congr_ae ha (Lp.stronglyMeasurable _) hsm h.coeFn_toLp
    filter_upwards [h1, h2] with p hp1 hp2
    rw [hp1, hp2, ← cgrad_zero_dilProfile a Φ.2.smooth]
  have ha_mem : MemLp (cgrad 0 Φa.1) 2 (measureH c) := (Lp.memLp g).ae_eq hg_ae
  have hg_eq : g = ha_mem.toLp (cgrad 0 Φa.1) := by
    apply Lp.ext
    exact hg_ae.trans ha_mem.coeFn_toLp.symm
  rw [T0_eq_smul_T0adj_comp_dilH hc ν t (h.toLp (cgrad 0 Φ.1))]
  change Real.exp (t / 2) • B0224.T0adj hc (ν * Real.exp (-t)) t g ∈ (solenoidalHC 0 c)ᗮ
  rw [hg_eq, RCLike.real_smul_eq_coe_smul (K := ℂ) (Real.exp (t / 2))]
  exact Submodule.smul_mem (solenoidalHC 0 c)ᗮ ((Real.exp (t / 2) : ℝ) : ℂ)
    (t0adjGradPres c (ν * Real.exp (-t)) hc t ht Φa ha_mem)

/-- Dually, `T0adj hc ν t` maps `solenoidalHC 0 c` into `solenoidalHC 0 c`. -/
private theorem t0adjSolenoidalInvariant (c ν : ℝ) (hc : 0 < c) (t : ℝ) (ht : 0 < t)
    (u : HSpace c MeridC) (hu : u ∈ solenoidalHC 0 c) :
    B0224.T0adj hc ν t u ∈ solenoidalHC 0 c := by
  unfold solenoidalHC
  rw [Submodule.mem_orthogonal]
  intro g hg
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨Φ, h, rfl⟩ := hg
    rw [← inner_eq_zero_symm, ← t0_complex_adjoint c ν hc t u (h.toLp (cgrad 0 Φ.1))]
    exact Submodule.inner_right_of_mem_orthogonal hu (t0GradPres c ν hc t ht Φ h)
  | zero => simp
  | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
  | smul a x _ hx => rw [inner_smul_left, hx, mul_zero]

/-- `T0 hc ν t` preserves `(solenoidalHC 0 c)ᗮ` for `t > 0`. -/
private theorem t0OrthogonalInvariant (c ν : ℝ) (hc : 0 < c) (t : ℝ) (ht : 0 < t)
    (w : HSpace c MeridC) (hw : w ∈ (solenoidalHC 0 c)ᗮ) :
    B0224.T0 hc ν t w ∈ (solenoidalHC 0 c)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  rw [t0_complex_adjoint c ν hc t u w]
  have hmem := t0adjSolenoidalInvariant c ν hc t ht u hu
  exact Submodule.inner_right_of_mem_orthogonal hmem hw

/-- `B0225.R0 hc ν μ` preserves `(solenoidalHC 0 c)ᗮ` for `0 < μ.re + 1 / 4`. -/
private theorem r0OrthogonalInvariant (c ν : ℝ) (hc : 0 < c) {μ : ℂ} (hμ : 0 < μ.re + 1 / 4)
    (w : HSpace c MeridC) (hw : w ∈ (solenoidalHC 0 c)ᗮ) :
    B0225.R0 hc ν μ w ∈ (solenoidalHC 0 c)ᗮ := by
  have hint := B0225.integrableOn_lapT0 hc ν hμ w
  rw [B0225.R0_apply hc ν hμ]
  rw [Submodule.mem_orthogonal]
  intro u hu
  have hK : ∀ t : ℝ, 0 < t → inner ℂ u (B0224.T0 hc ν t w) = 0 := fun t ht =>
    Submodule.inner_right_of_mem_orthogonal hu (t0OrthogonalInvariant c ν hc t ht w hw)
  have h1 := integral_inner (𝕜 := ℂ) (μ := volume.restrict (Ioi (0 : ℝ))) hint u
  change inner ℂ u (∫ t in Ioi (0 : ℝ), B0225.lapT0 hc ν μ w t) = 0
  rw [← h1]
  refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
  simp only [B0225.lapT0]
  rw [inner_smul_right (𝕜 := ℂ), hK t ht, mul_zero]

/-- `T0flat hc ν μ` commutes with `PepsC 0 c`:
`T0flat hc ν μ x = PepsC 0 c (B0225.R0 hc ν μ x)`. -/
theorem T0flat_eq_PepsC_comp_R0 {c ν : ℝ} (hc : 0 < c) {μ : ℂ} (hμ : 0 < μ.re + 1 / 4)
    (x : HSpace c MeridC) :
    T0flat hc ν μ x = PepsC 0 c (B0225.R0 hc ν μ x) := by
  have hdecomp : x = PepsC 0 c x + (x - PepsC 0 c x) := (add_sub_cancel (PepsC 0 c x) x).symm
  conv_rhs => rw [hdecomp, map_add, map_add]
  have hsol : B0225.R0 hc ν μ (PepsC 0 c x) ∈ solenoidalHC 0 c :=
    r0SolenoidalInvariant c ν hc μ hμ (PepsC 0 c x)
      (Submodule.starProjection_apply_mem (solenoidalHC 0 c) x)
  have horth_in : x - PepsC 0 c x ∈ (solenoidalHC 0 c)ᗮ :=
    Submodule.sub_starProjection_mem_orthogonal x
  have horth : B0225.R0 hc ν μ (x - PepsC 0 c x) ∈ (solenoidalHC 0 c)ᗮ :=
    r0OrthogonalInvariant c ν hc hμ (x - PepsC 0 c x) horth_in
  have hp1 : PepsC 0 c (B0225.R0 hc ν μ (PepsC 0 c x)) = B0225.R0 hc ν μ (PepsC 0 c x) :=
    Submodule.starProjection_eq_self_iff.mpr hsol
  have hp2 : PepsC 0 c (B0225.R0 hc ν μ (x - PepsC 0 c x)) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff (solenoidalHC 0 c)).mpr horth
  rw [hp1, hp2, add_zero]
  rfl

/-! ### 2. Strong time derivative of `T0` and left-inverse `R0 AU0 = U` -/

/-- Explicit pointwise formula of `B0224.T0 hc ν s` applied to a profile `φ`. -/
private def t0Formula (c ν s : ℝ) (φ : Profile → MeridC) : Profile → MeridC := fun p =>
  B0224.planeHeat (ν * p.1 * (1 - Real.exp (-s)))
    (fun z => B0220.periodize c φ (Real.exp (-s) * p.1, z)) p.2

/-- If `f` has measurable representative `φ`, then `T0 hc ν s f` has representative
`t0Formula c ν s φ`. -/
private theorem t0_rep_ae (c ν : ℝ) (hc : 0 < c) (s : ℝ) (f : HSpace c MeridC)
    (φ : Profile → MeridC) (hφ : StronglyMeasurable φ)
    (hfφ : (f : Profile → MeridC) =ᵐ[measureH c] φ) :
    (B0224.T0 hc ν s f : Profile → MeridC) =ᵐ[measureH c] t0Formula c ν s φ := by
  have hf := Lp.stronglyMeasurable f
  have h2a := B0224.coeFn_heatH hc (B0224.measurable_heatTime ν s)
    (B0224.dilH (Real.exp_pos (-s)) f)
  have hdil : (B0224.dilH (Real.exp_pos (-s)) f : Profile → MeridC) =ᵐ[measureH c]
      B0224.dil (Real.exp (-s)) φ :=
    (B0224.coeFn_dilH (Real.exp_pos (-s)) f).trans
      (B0224.dil_congr_ae (Real.exp_pos (-s)) hf hφ hfφ)
  have h2b := B0224.fiberHeat_congr_ae hc (B0224.measurable_heatTime ν s)
    (Lp.stronglyMeasurable _) (B0224.stronglyMeasurable_dil _ hφ) hdil
  filter_upwards [h2a, h2b] with p hpa hpb
  change (B0224.heatH hc (B0224.measurable_heatTime ν s)
    (B0224.dilH (Real.exp_pos (-s)) f) : Profile → MeridC) p = _
  rw [hpa, hpb]
  simp only [B0224.fiberHeat, B0224.dil, B0220.periodize, B0224.heatTime, t0Formula]

/-- At `ε = 0`, `AepsVecC ν 0 u p = -(p.1 • pdS u p) + (ν * p.1) • (pdQ (pdQ u) p + pdEta (pdEta u) p)`. -/
private theorem AepsVecC_zero_eq (ν : ℝ) (u : Profile → MeridC) (p : Profile) :
    AepsVecC ν 0 u p =
      -(p.1 • pdS u p) + (ν * p.1) • (pdQ (pdQ u) p + pdEta (pdEta u) p) := by
  have hQ0 : opQ (0 : ℝ) = (pdQ : (Profile → MeridC) → Profile → MeridC) := by
    funext f q
    simp [opQ]
  simp only [AepsVecC, opS, hQ0, sq, zero_mul, zero_smul, sub_zero]

/-- Smooth meridional tests are closed under `AepsVecC ν 0`. -/
private theorem isMeridTest_AepsVecC_zero {c : ℝ} (ν : ℝ) {u : Profile → MeridC}
    (hu : IsMeridTest c u) : IsMeridTest c (AepsVecC ν 0 u) := by
  have hA : IsMeridTest c (A0adj ν u) := isMeridTest_A0adj ν hu
  have hS : IsMeridTest c (pdS u) := ptPdS_meridTest hu
  obtain ⟨s0, s1, L, hs0, hb⟩ := hu.band
  have hK : IsClosed {p : Profile | p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L} :=
    (isClosed_Icc.preimage continuous_fst).inter
      (isClosed_le (continuous_abs.comp (continuous_snd.comp continuous_snd)) continuous_const)
  have hsub : tsupport u ⊆ {p : Profile | p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L} :=
    closure_minimal (fun p hp => hb p hp) hK
  have hrel : AepsVecC ν 0 u = fun p =>
      A0adj ν u p - (2 * p.1) • pdS u p + (1 / 2 : ℝ) • u p := by
    funext p
    rw [AepsVecC_zero_eq]
    simp only [A0adj]
    module
  rw [hrel]
  refine ⟨?_, ?_, s0, s1, L, hs0, ?_⟩
  · exact (hA.smooth.sub ((contDiff_const.mul contDiff_fst).smul hS.smooth)).add
      ((contDiff_const (c := (1 / 2 : ℝ))).smul hu.smooth)
  · intro p
    simp only [hA.periodic p, hS.periodic p, hu.periodic p]
  · intro p hp
    by_contra hnot
    have hn : p ∉ tsupport u := fun hm => hnot (hsub hm)
    have hA0 : A0adj ν u p = 0 := by
      have hts : ∀ (g : Profile → MeridC) (v : Profile), tsupport g ⊆ tsupport u →
          tsupport (fun q => fderiv ℝ g q v) ⊆ tsupport u := fun g v hg => by
        refine closure_minimal (fun q hq => ?_) isClosed_closure
        have : fderiv ℝ g q ≠ 0 := fun h0 => hq (by simp [h0])
        exact hg (support_fderiv_subset ℝ this)
      have h1 : tsupport (pdS u) ⊆ tsupport u := hts u _ subset_rfl
      have h2 : tsupport (pdQ u) ⊆ tsupport u := hts u _ subset_rfl
      have h3 : tsupport (pdEta u) ⊆ tsupport u := hts u _ subset_rfl
      have h4 : tsupport (pdQ (pdQ u)) ⊆ tsupport u := hts _ _ h2
      have h5 : tsupport (pdEta (pdEta u)) ⊆ tsupport u := hts _ _ h3
      simp only [A0adj, image_eq_zero_of_notMem_tsupport hn,
        image_eq_zero_of_notMem_tsupport (fun hm => hn (h1 hm)),
        image_eq_zero_of_notMem_tsupport (fun hm => hn (h4 hm)),
        image_eq_zero_of_notMem_tsupport (fun hm => hn (h5 hm))]
      simp
    have hS0 : pdS u p = 0 := by
      have hf0 : fderiv ℝ u p = 0 := fderiv_of_notMem_tsupport ℝ hn
      simp [pdS, hf0]
    have hu0 : u p = 0 := image_eq_zero_of_notMem_tsupport hn
    exact hp (by simp [hA0, hS0, hu0])

/-- Forward heat time `θ(s) = ν a (1 - e^{-s})`. -/
private def fwdTh (ν a s : ℝ) : ℝ := ν * a * (1 - Real.exp (-s))

/-- Forward dilated age `σ(s) = e^{-s} a`. -/
private def fwdSg (a s : ℝ) : ℝ := Real.exp (-s) * a

/-- Forward kernel integrand `G_{θ(u)}(y) ζ(σ(u), w - ι y)`. -/
private def fwdFk (ν a : ℝ) (ζ : Profile → MeridC) (w : ℝ × ℝ) (u : ℝ) (y : Euc 2) : MeridC :=
  gaussKernel 2 (fwdTh ν a u) y • ζ (fwdSg a u, w - B0224.planeι y)

/-- Derivative integrand of `fwdFk` in `u`. -/
private def fwdFp (ν a : ℝ) (ζ : Profile → MeridC) (w : ℝ × ℝ) (u : ℝ) (y : Euc 2) : MeridC :=
  gaussKernel 2 (fwdTh ν a u) y •
      ((-(Real.exp (-u) * a)) • pdS ζ (fwdSg a u, w - B0224.planeι y))
    + (gaussDt 2 (fwdTh ν a u) y * (ν * a * Real.exp (-u))) •
        ζ (fwdSg a u, w - B0224.planeι y)

/-- Age window on which forward bounds are uniform. -/
private def fwdS (ν a t : ℝ) : Set ℝ :=
  {u | (fwdTh ν a t / 2 < fwdTh ν a u ∧ fwdTh ν a u < 2 * fwdTh ν a t) ∧ u ∈ Ioo (t - 1) (t + 1)}

/-- Integrable Gaussian majorant for `fwdFp`. -/
private def fwdBd (A K M1 M2 ν a t : ℝ) (y : Euc 2) : ℝ :=
  (A * (ν * a * Real.exp (-(t - 1))) * M1 + K * (Real.exp (-(t - 1)) * a) * M2)
    * Real.exp (-(1 / (16 * fwdTh ν a t)) * ‖y‖ ^ 2)

private lemma fwdTh_hasDerivAt (ν a s : ℝ) :
    HasDerivAt (fwdTh ν a) (ν * a * Real.exp (-s)) s := by
  unfold fwdTh
  have h1 : HasDerivAt (fun u : ℝ => -u) (-1) s := (hasDerivAt_id' s).neg
  have h2 : HasDerivAt (fun u : ℝ => 1 - Real.exp (-u)) (0 - Real.exp (-s) * (-1)) s :=
    (hasDerivAt_const s (1 : ℝ)).sub h1.exp
  exact (h2.const_mul (ν * a)).congr_deriv (by ring)

private lemma fwdSg_hasDerivAt (a s : ℝ) :
    HasDerivAt (fwdSg a) (-(Real.exp (-s) * a)) s := by
  unfold fwdSg
  have h1 : HasDerivAt (fun u : ℝ => Real.exp (-u)) (-Real.exp (-s)) s := by
    simpa using (hasDerivAt_id s).neg.exp
  exact (h1.mul_const a).congr_deriv (by ring)

private lemma fwdTh_pos {ν a t : ℝ} (hν : 0 < ν) (ha : 0 < a) (ht : 0 < t) :
    0 < fwdTh ν a t := by
  unfold fwdTh
  have h1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  exact mul_pos (mul_pos hν ha) (by linarith)

private lemma fwdFormula {c ν s : ℝ} {φ : Profile → MeridC} (hφ : B0220.QPeriodic c φ)
    (hν : 0 < ν) (p : Profile) (hp : 0 < p.1) (hs : 0 < s) :
    t0Formula c ν s φ p = ∫ y : Euc 2, fwdFk ν p.1 φ p.2 s y := by
  have hθ : 0 < ν * p.1 * (1 - Real.exp (-s)) := fwdTh_pos hν hp hs
  simp only [t0Formula]
  rw [B0220.periodize_of_periodic φ hφ, B0224.planeHeat_of_pos hθ]
  rfl

set_option maxHeartbeats 1000000 in
private lemma fwdHasDerivG {c ν a t : ℝ} {ζ : Profile → MeridC} (hc : 0 < c)
    (hζ : IsMeridTest c ζ) (hν : 0 < ν) (ha : 0 < a) (ht : 0 < t) (w : ℝ × ℝ) :
    HasDerivAt (fun s : ℝ => ∫ y : Euc 2, fwdFk ν a ζ w s y)
      (∫ y : Euc 2, fwdFp ν a ζ w t y) t := by
  have hθ0 : 0 < fwdTh ν a t := fwdTh_pos hν ha ht
  have hcont : Continuous (fwdTh ν a) := by unfold fwdTh; fun_prop
  have e1 : ∀ᶠ u in 𝓝 t, fwdTh ν a t / 2 < fwdTh ν a u :=
    (hcont.tendsto t).eventually_const_lt (by linarith)
  have e2 : ∀ᶠ u in 𝓝 t, fwdTh ν a u < 2 * fwdTh ν a t :=
    (hcont.tendsto t).eventually_lt_const (by linarith)
  have e3 : Ioo (t - 1) (t + 1) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  have hS : fwdS ν a t ∈ 𝓝 t := by
    filter_upwards [e1, e2, e3] with u h1 h2 h3
    exact ⟨⟨h1, h2⟩, h3⟩
  have hζc : Continuous ζ := hζ.smooth.continuous
  have hpdc : Continuous (pdS ζ) := (ptPdS_meridTest hζ).smooth.continuous
  obtain ⟨A, hA0, hA⟩ := UnforcedLeray.Heat.abs_gaussDt_le (d := 2) hθ0
  obtain ⟨K, hK0, hK⟩ := ptGaussEnv hθ0
  obtain ⟨M1, hM1⟩ := merid_test_bounded c hc ζ hζ
  obtain ⟨M2, hM2⟩ := merid_test_bounded c hc (pdS ζ) (ptPdS_meridTest hζ)
  have hpos : 0 < 1 / (16 * fwdTh ν a t) := one_div_pos.mpr (by linarith)
  have hderiv : ∀ (y : Euc 2) (u : ℝ), u ∈ fwdS ν a t →
      HasDerivAt (fun u : ℝ => fwdFk ν a ζ w u y) (fwdFp ν a ζ w u y) u := by
    intro y u hu
    have hu1 : fwdTh ν a t / 2 < fwdTh ν a u := hu.1.1
    have hθu : 0 < fwdTh ν a u := by linarith
    have hc1 : HasDerivAt (fun u : ℝ => gaussKernel 2 (fwdTh ν a u) y)
        (gaussDt 2 (fwdTh ν a u) y * (ν * a * Real.exp (-u))) u :=
      (UnforcedLeray.Heat.hasDerivAt_gaussKernel_time hθu y).comp u (fwdTh_hasDerivAt ν a u)
    have hsg : HasDerivAt (fun u : ℝ => (fwdSg a u, w - B0224.planeι y))
        (-(Real.exp (-u) * a), (0 : ℝ × ℝ)) u :=
      (fwdSg_hasDerivAt a u).prodMk (hasDerivAt_const u (w - B0224.planeι y))
    have hζd : HasFDerivAt ζ (fderiv ℝ ζ (fwdSg a u, w - B0224.planeι y))
        (fwdSg a u, w - B0224.planeι y) :=
      ((hζ.smooth.differentiable (by simp)) _).hasFDerivAt
    have hcomp := hζd.comp_hasDerivAt u hsg
    have hpd : fderiv ℝ ζ (fwdSg a u, w - B0224.planeι y) (-(Real.exp (-u) * a), 0, 0)
        = (-(Real.exp (-u) * a)) • pdS ζ (fwdSg a u, w - B0224.planeι y) := by
      unfold pdS
      rw [show ((-(Real.exp (-u) * a), 0, 0) : Profile) =
          (-(Real.exp (-u) * a)) • ((1 : ℝ), (0 : ℝ), (0 : ℝ))
        from by ext <;> simp, map_smul]
    have hd : HasDerivAt (fun u : ℝ => ζ (fwdSg a u, w - B0224.planeι y))
        ((-(Real.exp (-u) * a)) • pdS ζ (fwdSg a u, w - B0224.planeι y)) u := by
      rw [← hpd]
      exact hcomp
    unfold fwdFk fwdFp
    exact hc1.smul hd
  have hFk_meas : ∀ᶠ u in 𝓝 t, AEStronglyMeasurable (fwdFk ν a ζ w u)
      (volume : Measure (Euc 2)) :=
    Filter.Eventually.of_forall fun u =>
      ((UnforcedLeray.Gaussian.continuous_gaussKernel (d := 2) (fwdTh ν a u)).smul
        (ptCont_shift hζc (fwdSg a u) w)).aestronglyMeasurable
  have hFk_int : Integrable (fwdFk ν a ζ w t) (volume : Measure (Euc 2)) :=
    ptIntKer (g := fun y => ζ (fwdSg a t, w - B0224.planeι y)) hθ0
      (ptCont_shift hζc (fwdSg a t) w) (fun y => hM1 _)
  have hFp_cont : Continuous (fwdFp ν a ζ w t) := by
    unfold fwdFp
    exact ((UnforcedLeray.Gaussian.continuous_gaussKernel (d := 2) (fwdTh ν a t)).smul
        ((ptCont_shift hpdc (fwdSg a t) w).const_smul (-(Real.exp (-t) * a)))).add
      ((((UnforcedLeray.Heat.continuous_gaussDt 2 (fwdTh ν a t)).mul continuous_const).smul
        (ptCont_shift hζc (fwdSg a t) w)))
  have hFp_meas : AEStronglyMeasurable (fwdFp ν a ζ w t) (volume : Measure (Euc 2)) :=
    hFp_cont.aestronglyMeasurable
  have hbound : ∀ᵐ y ∂(volume : Measure (Euc 2)), ∀ u ∈ fwdS ν a t,
      ‖fwdFp ν a ζ w u y‖ ≤ fwdBd A K M1 M2 ν a t y := by
    refine ae_of_all _ fun y u hu => ?_
    have hu1 : fwdTh ν a t / 2 < fwdTh ν a u := hu.1.1
    have hu2 : fwdTh ν a u < 2 * fwdTh ν a t := hu.1.2
    have hu3 : t - 1 < u := hu.2.1
    have hθu : 0 < fwdTh ν a u := by linarith
    have hgK := hK (fwdTh ν a u) hu1 hu2 y
    have hgK0 : 0 ≤ gaussKernel 2 (fwdTh ν a u) y :=
      UnforcedLeray.Gaussian.gaussKernel_nonneg (d := 2) hθu y
    have hE : 0 ≤ Real.exp (-(1 / (16 * fwdTh ν a t)) * ‖y‖ ^ 2) := (Real.exp_pos _).le
    have hexp1 : Real.exp (-u) ≤ Real.exp (-(t - 1)) :=
      Real.exp_le_exp.mpr (by linarith)
    have hexp0 : 0 < Real.exp (-u) := Real.exp_pos (-u)
    have hk : 0 ≤ ν * a * Real.exp (-u) := (mul_pos (mul_pos hν ha) hexp0).le
    have hk' : ν * a * Real.exp (-u) ≤ ν * a * Real.exp (-(t - 1)) :=
      mul_le_mul_of_nonneg_left hexp1 (mul_pos hν ha).le
    have hT1 : ‖(gaussDt 2 (fwdTh ν a u) y * (ν * a * Real.exp (-u)))
        • ζ (fwdSg a u, w - B0224.planeι y)‖
        ≤ (A * Real.exp (-(1 / (16 * fwdTh ν a t)) * ‖y‖ ^ 2) *
            (ν * a * Real.exp (-(t - 1)))) * M1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hk]
      exact mul_le_mul (mul_le_mul (hA (fwdTh ν a u) hu1 hu2 y) hk' hk (mul_nonneg hA0 hE))
        (hM1 _) (norm_nonneg _)
        (mul_nonneg (mul_nonneg hA0 hE) (mul_pos (mul_pos hν ha) (Real.exp_pos _)).le)
    have hT2 : ‖gaussKernel 2 (fwdTh ν a u) y •
        ((-(Real.exp (-u) * a)) • pdS ζ (fwdSg a u, w - B0224.planeι y))‖
        ≤ (K * Real.exp (-(1 / (16 * fwdTh ν a t)) * ‖y‖ ^ 2) *
            (Real.exp (-(t - 1)) * a)) * M2 := by
      have hea : Real.exp (-u) * a ≤ Real.exp (-(t - 1)) * a :=
        mul_le_mul_of_nonneg_right hexp1 ha.le
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hgK0,
        abs_neg, abs_of_pos (mul_pos hexp0 ha)]
      have h3 : gaussKernel 2 (fwdTh ν a u) y * (Real.exp (-u) * a *
          ‖pdS ζ (fwdSg a u, w - B0224.planeι y)‖)
          ≤ (K * Real.exp (-(1 / (16 * fwdTh ν a t)) * ‖y‖ ^ 2) *
              (Real.exp (-(t - 1)) * a)) * M2 := by
        have h4 := mul_le_mul hea (hM2 (fwdSg a u, w - B0224.planeι y))
          (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le ha.le)
        have h5 := mul_le_mul hgK h4 (mul_nonneg (mul_nonneg hexp0.le ha.le) (norm_nonneg _))
          (mul_nonneg hK0 hE)
        linarith [h5]
      linarith [h3]
    unfold fwdFp
    refine (norm_add_le _ _).trans ((add_le_add hT2 hT1).trans_eq ?_)
    unfold fwdBd
    ring
  have hdiff : ∀ᵐ y ∂(volume : Measure (Euc 2)), ∀ u ∈ fwdS ν a t,
      HasDerivAt (fun u : ℝ => fwdFk ν a ζ w u y) (fwdFp ν a ζ w u y) u :=
    ae_of_all _ fun y u hu => hderiv y u hu
  have hbd_int : Integrable (fwdBd A K M1 M2 ν a t) (volume : Measure (Euc 2)) :=
    (UnforcedLeray.Gaussian.integrable_exp_neg_mul_sq_norm (d := 2) hpos).const_mul _
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure (Euc 2)))
    (F := fwdFk ν a ζ w) (F' := fwdFp ν a ζ w) (bound := fwdBd A K M1 M2 ν a t)
    hS hFk_meas hFk_int hFp_meas hbound hbd_int hdiff).2

private lemma fwdHid {c ν a t : ℝ} {ζ : Profile → MeridC} (hc : 0 < c) (hζ : IsMeridTest c ζ)
    (hν : 0 < ν) (ha : 0 < a) (ht : 0 < t) (w : ℝ × ℝ) :
    (∫ y : Euc 2, fwdFp ν a ζ w t y)
      = ∫ y : Euc 2, fwdFk ν a (AepsVecC ν 0 ζ) w t y := by
  simp only [fwdFp, fwdFk]
  have hθ0 : 0 < fwdTh ν a t := fwdTh_pos hν ha ht
  have hk : 0 ≤ ν * a * Real.exp (-t) := (mul_pos (mul_pos hν ha) (Real.exp_pos (-t))).le
  have hζc : Continuous ζ := hζ.smooth.continuous
  have hpdc : Continuous (pdS ζ) := (ptPdS_meridTest hζ).smooth.continuous
  have hAζ : IsMeridTest c (AepsVecC ν 0 ζ) := isMeridTest_AepsVecC_zero ν hζ
  have hAζc : Continuous (AepsVecC ν 0 ζ) := hAζ.smooth.continuous
  obtain ⟨A, hA0, hA⟩ := UnforcedLeray.Heat.abs_gaussDt_le (d := 2) hθ0
  obtain ⟨M1, hM1⟩ := merid_test_bounded c hc ζ hζ
  obtain ⟨M2, hM2⟩ := merid_test_bounded c hc (pdS ζ) (ptPdS_meridTest hζ)
  obtain ⟨M3, hM3⟩ := merid_test_bounded c hc (AepsVecC ν 0 ζ) hAζ
  have hM1n : 0 ≤ M1 := (norm_nonneg _).trans (hM1 0)
  have hX : Integrable (fun y : Euc 2 => (gaussDt 2 (fwdTh ν a t) y * (ν * a * Real.exp (-t)))
      • ζ (fwdSg a t, w - B0224.planeι y)) := by
    refine ptIntEnv (f := fun y => gaussDt 2 (fwdTh ν a t) y * (ν * a * Real.exp (-t)))
      (g := fun y => ζ (fwdSg a t, w - B0224.planeι y))
      (b := 1 / (16 * fwdTh ν a t)) (C := A * (ν * a * Real.exp (-t))) (M := M1)
      (one_div_pos.mpr (by linarith)) ?_ (ptCont_shift hζc _ _) (mul_nonneg hA0 hk) hM1n ?_
      (fun y => hM1 _)
    · exact ((UnforcedLeray.Heat.continuous_gaussDt 2 (fwdTh ν a t)).mul continuous_const)
    · intro y
      rw [abs_mul, abs_of_nonneg hk]
      have h1 := hA (fwdTh ν a t) (by linarith) (by linarith) y
      calc |gaussDt 2 (fwdTh ν a t) y| * (ν * a * Real.exp (-t))
          ≤ (A * Real.exp (-(1 / (16 * fwdTh ν a t)) * ‖y‖ ^ 2)) * (ν * a * Real.exp (-t)) :=
            mul_le_mul_of_nonneg_right h1 hk
        _ = A * (ν * a * Real.exp (-t)) * Real.exp (-(1 / (16 * fwdTh ν a t)) * ‖y‖ ^ 2) := by
            ring
  have hP : Integrable (fun y : Euc 2 => gaussKernel 2 (fwdTh ν a t) y •
      ((-(Real.exp (-t) * a)) • pdS ζ (fwdSg a t, w - B0224.planeι y))) :=
    ptIntKer (g := fun y => (-(Real.exp (-t) * a)) • pdS ζ (fwdSg a t, w - B0224.planeι y))
      hθ0 ((ptCont_shift hpdc _ _).const_smul (-(Real.exp (-t) * a)))
      (M := |-(Real.exp (-t) * a)| * M2)
      (fun y => by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hM2 _) (abs_nonneg _))
  have hC : Integrable (fun y : Euc 2 => gaussKernel 2 (fwdTh ν a t) y •
      AepsVecC ν 0 ζ (fwdSg a t, w - B0224.planeι y)) :=
    ptIntKer (g := fun y => AepsVecC ν 0 ζ (fwdSg a t, w - B0224.planeι y)) hθ0
      (ptCont_shift hAζc _ _) (fun y => hM3 _)
  have hXQ : ∫ y : Euc 2, (gaussDt 2 (fwdTh ν a t) y * (ν * a * Real.exp (-t)))
      • ζ (fwdSg a t, w - B0224.planeι y)
      = ∫ y : Euc 2, (ν * a * Real.exp (-t)) • (gaussKernel 2 (fwdTh ν a t) y •
          (pdQ (pdQ ζ) (fwdSg a t, w - B0224.planeι y)
            + pdEta (pdEta ζ) (fwdSg a t, w - B0224.planeι y))) := by
    calc ∫ y : Euc 2, (gaussDt 2 (fwdTh ν a t) y * (ν * a * Real.exp (-t)))
          • ζ (fwdSg a t, w - B0224.planeι y)
        = ∫ y : Euc 2, (ν * a * Real.exp (-t)) •
            (gaussDt 2 (fwdTh ν a t) y • ζ (fwdSg a t, w - B0224.planeι y)) := by
          congr 1
          funext y
          rw [mul_smul, smul_comm]
      _ = (ν * a * Real.exp (-t)) • ∫ y : Euc 2,
            gaussDt 2 (fwdTh ν a t) y • ζ (fwdSg a t, w - B0224.planeι y) :=
          integral_smul _ _
      _ = (ν * a * Real.exp (-t)) • ∫ y : Euc 2, gaussKernel 2 (fwdTh ν a t) y •
            (pdQ (pdQ ζ) (fwdSg a t, w - B0224.planeι y)
              + pdEta (pdEta ζ) (fwdSg a t, w - B0224.planeι y)) := by
          rw [plane_gaussDt_lap c hc ζ hζ (fwdTh ν a t) (fwdSg a t) hθ0 w]
      _ = _ := (integral_smul _ _).symm
  have hpt : ∀ y : Euc 2,
      (ν * a * Real.exp (-t)) • (gaussKernel 2 (fwdTh ν a t) y •
          (pdQ (pdQ ζ) (fwdSg a t, w - B0224.planeι y)
            + pdEta (pdEta ζ) (fwdSg a t, w - B0224.planeι y)))
      = gaussKernel 2 (fwdTh ν a t) y • AepsVecC ν 0 ζ (fwdSg a t, w - B0224.planeι y)
        - gaussKernel 2 (fwdTh ν a t) y • ((-(Real.exp (-t) * a)) •
            pdS ζ (fwdSg a t, w - B0224.planeι y)) := by
    intro y
    rw [AepsVecC_zero_eq]
    simp only [fwdSg]
    module
  have hQ : ∫ y : Euc 2, (ν * a * Real.exp (-t)) • (gaussKernel 2 (fwdTh ν a t) y •
          (pdQ (pdQ ζ) (fwdSg a t, w - B0224.planeι y)
            + pdEta (pdEta ζ) (fwdSg a t, w - B0224.planeι y)))
      = ∫ y : Euc 2, (gaussKernel 2 (fwdTh ν a t) y •
            AepsVecC ν 0 ζ (fwdSg a t, w - B0224.planeι y)
          - gaussKernel 2 (fwdTh ν a t) y • ((-(Real.exp (-t) * a)) •
            pdS ζ (fwdSg a t, w - B0224.planeι y))) := by
    congr 1
    funext y
    exact hpt y
  rw [integral_add hP hX, hXQ, hQ, integral_sub hC hP]
  abel

/-- Pointwise time derivative of `t0Formula c ν s ζ p` for `s > 0`, `p.1 > 0`. -/
private theorem t0_pt_deriv {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) {ζ : Profile → MeridC}
    (hζ : IsMeridTest c ζ) {t : ℝ} (ht : 0 < t) {p : Profile} (hp : 0 < p.1) :
    HasDerivAt (fun s : ℝ => t0Formula c ν s ζ p)
      (t0Formula c ν t (AepsVecC ν 0 ζ) p) t := by
  have hev : (fun s : ℝ => t0Formula c ν s ζ p) =ᶠ[𝓝 t]
      (fun s : ℝ => ∫ y : Euc 2, fwdFk ν p.1 ζ p.2 s y) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact fwdFormula hζ.periodic hν p hp hs
  have hG := fwdHasDerivG hc hζ hν hp ht p.2
  have hval := fwdFormula (isMeridTest_AepsVecC_zero ν hζ).periodic hν p hp ht
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  rw [hval, ← fwdHid hc hζ hν hp ht p.2]
  exact hG

/-- Uniform `L²(measureH c)` domination of `t0Formula c ν r (AepsVecC ν 0 ζ)` for `r` near `t`. -/
private theorem t0_formula_dom {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) {ζ : Profile → MeridC}
    (hζ : IsMeridTest c ζ) {t : ℝ} (ht : 0 < t) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ g : Profile → ℝ, MemLp g 2 (measureH c) ∧
      ∀ᵐ p ∂(measureH c), ∀ r ∈ Ioo (t - ε) (t + ε),
        ‖t0Formula c ν r (AepsVecC ν 0 ζ) p‖ ≤ g p := by
  have hu : IsMeridTest c (AepsVecC ν 0 ζ) := isMeridTest_AepsVecC_zero ν hζ
  obtain ⟨s0, s1, L, hs0, hb⟩ := hu.band
  obtain ⟨M, hM⟩ := merid_test_bounded c hc _ hu
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set ε : ℝ := t / 2 with hε_def
  have hε0 : 0 < ε := by positivity
  set a : ℝ := s0 * Real.exp (t - ε)
  set b : ℝ := s1 * Real.exp (t + ε)
  set Θ : ℝ := ν * b * (1 - Real.exp (-(t + ε)))
  set C : ℝ := M * (1 + 2 * L ^ 2 + 8 * Θ)
  have ha0 : 0 < a := mul_pos hs0 (Real.exp_pos _)
  refine ⟨ε, hε0, _, mem_lp_majorant c a b C hc ha0, ?_⟩
  filter_upwards [ae_measureH_age_pos c] with p hp1 r hr
  have hr0 : 0 < r := by linarith [hr.1, hε_def]
  have hexp_lt : Real.exp (-r) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hinv : Real.exp r * Real.exp (-r) = 1 := by rw [← Real.exp_add]; simp
  have hper : ∀ z : ℝ × ℝ, B0220.periodize c (AepsVecC ν 0 ζ) (Real.exp (-r) * p.1, z) =
      AepsVecC ν 0 ζ (Real.exp (-r) * p.1, z) := fun z => by
    rw [B0220.periodize_of_periodic _ hu.periodic]
  have hform : t0Formula c ν r (AepsVecC ν 0 ζ) p =
      B0224.planeHeat (ν * p.1 * (1 - Real.exp (-r)))
        (fun z => AepsVecC ν 0 ζ (Real.exp (-r) * p.1, z)) p.2 := by
    unfold t0Formula
    simp only [hper]
  by_cases hab : p.1 ∈ Icc a b
  · have hθ : 0 < ν * p.1 * (1 - Real.exp (-r)) :=
      mul_pos (mul_pos hν hp1) (by linarith)
    have hb0 : 0 < b := lt_of_lt_of_le hp1 hab.2
    have hθΘ : ν * p.1 * (1 - Real.exp (-r)) ≤ Θ := by
      refine mul_le_mul (mul_le_mul_of_nonneg_left hab.2 hν.le)
        (sub_le_sub_left (Real.exp_le_exp.2 (by linarith [hr.2])) _)
        (by linarith) (mul_nonneg hν.le hb0.le)
    have hmom := plane_heat_moment _ L M hθ (fun z => AepsVecC ν 0 ζ (Real.exp (-r) * p.1, z))
      (fun z => hM _) (fun z hz => by
        by_contra hne
        have := (hb _ hne).2
        simp only at hz this
        linarith) p.2
    have hpos : 0 < 1 + p.2.2 ^ 2 := by positivity
    have hCle : M * (1 + 2 * L ^ 2 + 8 * (ν * p.1 * (1 - Real.exp (-r)))) ≤ C :=
      mul_le_mul_of_nonneg_left (by linarith) hM0
    have hPn : ‖B0224.planeHeat (ν * p.1 * (1 - Real.exp (-r)))
        (fun z => AepsVecC ν 0 ζ (Real.exp (-r) * p.1, z)) p.2‖ ≤ C * (1 + p.2.2 ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hpos]
      nlinarith [hmom, hCle]
    rw [hform]
    refine hPn.trans (le_of_eq ?_)
    simp [Set.indicator_of_mem hab]
  · have hv0 : ∀ z : ℝ × ℝ, AepsVecC ν 0 ζ (Real.exp (-r) * p.1, z) = 0 := by
      intro z
      by_contra hne
      apply hab
      have h1' := (hb _ hne).1
      simp only at h1'
      have e1 : p.1 = Real.exp r * (Real.exp (-r) * p.1) := by
        rw [← mul_assoc, hinv, one_mul]
      constructor
      · calc a = s0 * Real.exp (t - ε) := rfl
          _ ≤ (Real.exp (-r) * p.1) * Real.exp (t - ε) :=
              mul_le_mul_of_nonneg_right h1'.1 (Real.exp_pos _).le
          _ ≤ (Real.exp (-r) * p.1) * Real.exp r :=
              mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hr.1.le) (by positivity)
          _ = p.1 := by rw [mul_comm _ (Real.exp r), ← e1]
      · calc p.1 = (Real.exp (-r) * p.1) * Real.exp r := by rw [mul_comm _ (Real.exp r), ← e1]
          _ ≤ s1 * Real.exp r :=
              mul_le_mul_of_nonneg_right h1'.2 (Real.exp_pos _).le
          _ ≤ s1 * Real.exp (t + ε) :=
              mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hr.2.le) (hs0.le.trans (h1'.1.trans h1'.2))
          _ = b := rfl
    have hzero_fn : (fun z : ℝ × ℝ => AepsVecC ν 0 ζ (Real.exp (-r) * p.1, z)) = fun _ => 0 :=
      funext hv0
    have hθ : 0 < ν * p.1 * (1 - Real.exp (-r)) :=
      mul_pos (mul_pos hν hp1) (by linarith)
    rw [hform, hzero_fn, B0224.planeHeat_of_pos hθ]
    simp [Set.indicator_of_notMem hab]

/-- Strong `HSpace c MeridC` derivative of `s ↦ B0224.T0 hc ν s U` on `(0, ∞)`. -/
private theorem t0_strong_deriv {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) {u : Profile → MeridC}
    (hu : IsMeridTest c u) {U A0U : HSpace c MeridC}
    (hU : (U : Profile → MeridC) =ᵐ[measureH c] u)
    (hA0U : (A0U : Profile → MeridC) =ᵐ[measureH c] AepsVecC ν 0 u)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => B0224.T0 hc ν s U) (B0224.T0 hc ν t A0U) t := by
  obtain ⟨ε₀, hε₀, g, hg, hdom⟩ := t0_formula_dom hc hν hu ht
  have hum : StronglyMeasurable u := hu.smooth.continuous.stronglyMeasurable
  have hAm : StronglyMeasurable (AepsVecC ν 0 u) :=
    (isMeridTest_AepsVecC_zero ν hu).smooth.continuous.stronglyMeasurable
  refine lp_hasDerivAt_of_pointwise (measureH c) (fun s => B0224.T0 hc ν s U)
    (B0224.T0 hc ν t A0U) (fun s => t0Formula c ν s u)
    (fun s => t0Formula c ν s (AepsVecC ν 0 u)) g t (min ε₀ t) (lt_min hε₀ ht) hg
    (fun s => t0_rep_ae c ν hc s U u hum hU) (t0_rep_ae c ν hc t A0U _ hAm hA0U) ?_
  filter_upwards [hdom, ae_measureH_age_pos c] with p hp hp1
  intro r hr
  have hr' : r ∈ Ioo (t - ε₀) (t + ε₀) :=
    ⟨by linarith [hr.1, min_le_left ε₀ t], by linarith [hr.2, min_le_left ε₀ t]⟩
  have hr0 : 0 < r := by linarith [hr.1, min_le_right ε₀ t]
  exact ⟨t0_pt_deriv hc hν hu hr0 hp1, hp r hr'⟩

/-- `T0 hc ν t` commutes with `ℂ`-scalar multiplication. -/
private theorem t0c_T0_smul_C {c : ℝ} (hc : 0 < c) (ν t : ℝ) (a : ℂ) (f : HSpace c MeridC) :
    B0224.T0 hc ν t (a • f) = a • B0224.T0 hc ν t f := by
  change B0224.heatH hc (B0224.measurable_heatTime ν t)
    (B0224.dilH (Real.exp_pos (-t)) (a • f)) = _
  rw [t0c_dilH_smul_C, t0c_heatH_smul_C]
  rfl

/-- `B0225.R0 hc ν μ` is a left inverse to `μ - AepsVecC ν 0` on smooth meridional tests. -/
theorem R0_left_inverse_isMeridTest {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) {μ : ℂ}
    (hγ : 0 < μ.re + 1 / 4) {u : Profile → MeridC} {U AU0 : HSpace c MeridC}
    (hu : IsMeridTest c u)
    (hU : (U : Profile → MeridC) =ᵐ[measureH c] u)
    (hAU0 : (AU0 : Profile → MeridC) =ᵐ[measureH c] (fun p => μ • u p - AepsVecC ν 0 u p)) :
    B0225.R0 hc ν μ AU0 = U := by
  have hA0_mem : MemLp (AepsVecC ν 0 u) 2 (measureH c) :=
    memLp_isMeridTest (isMeridTest_AepsVecC_zero ν hu)
  set A0U : HSpace c MeridC := hA0_mem.toLp (AepsVecC ν 0 u)
  have hAU0_eq : AU0 = μ • U - A0U := by
    apply Lp.ext
    filter_upwards [hAU0, Lp.coeFn_sub (μ • U) A0U, Lp.coeFn_smul μ U, hU, hA0_mem.coeFn_toLp]
      with p hp1 hp2 hp3 hp4 hp5
    rw [hp1, hp2, Pi.sub_apply, hp3, Pi.smul_apply, hp4, hp5]
  refine ext_inner_left ℂ fun W => ?_
  have hint : IntegrableOn (fun t : ℝ => Complex.exp (-(μ * t)) • B0224.T0 hc ν t AU0) (Ioi 0) :=
    B0225.integrableOn_lapT0 hc ν hγ AU0
  have hR0 : inner ℂ W (B0225.R0 hc ν μ AU0) =
      ∫ t in Ioi (0 : ℝ), Complex.exp (-(μ * t)) * inner ℂ W (B0224.T0 hc ν t AU0) := by
    rw [B0225.R0_apply hc ν hγ AU0, ← integral_inner hint W]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [inner_smul_right]
  have hcont : ContinuousWithinAt
      (fun t : ℝ => Complex.exp (-(μ * t)) * inner ℂ W (B0224.T0 hc ν t U)) (Ici 0) 0 := by
    have hT0_0 : B0224.T0 hc ν 0 U = U := by rw [B0224.T0_zero_eq]; rfl
    have h1 : ContinuousWithinAt (fun t : ℝ => inner ℂ W (B0224.T0 hc ν t U)) (Ici 0) 0 := by
      unfold ContinuousWithinAt
      show Tendsto (fun t : ℝ => inner ℂ W (B0224.T0 hc ν t U)) (𝓝[≥] 0)
        (𝓝 (inner ℂ W (B0224.T0 hc ν 0 U)))
      rw [hT0_0]
      exact ((continuous_const.inner continuous_id).continuousAt.tendsto).comp
        (t0_strong_cont_zero c ν hc U)
    exact (Continuous.continuousWithinAt (by fun_prop)).mul h1
  have hderiv : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivAt (fun t : ℝ => Complex.exp (-(μ * t)) * inner ℂ W (B0224.T0 hc ν t U))
        (-(Complex.exp (-(μ * x)) * inner ℂ W (B0224.T0 hc ν x AU0))) x := by
    intro x hx
    have hE : HasDerivAt (fun t : ℝ => Complex.exp (-(μ * t)))
        (Complex.exp (-(μ * x)) * (-μ)) x := by
      have h := (((hasDerivAt_id x).ofReal_comp).const_mul μ).neg.cexp
      simpa using h
    have hF : HasDerivAt (fun t : ℝ => inner ℂ W (B0224.T0 hc ν t U))
        (inner ℂ W (B0224.T0 hc ν x A0U)) x := by
      have hd := t0_strong_deriv hc hν hu hU hA0_mem.coeFn_toLp hx
      exact (((innerSL ℂ W).restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt x hd
    have hprod := hE.mul hF
    refine hprod.congr_deriv ?_
    rw [hAU0_eq, map_sub, t0c_T0_smul_C, inner_sub_right, inner_smul_right]
    ring
  have hfint : IntegrableOn
      (fun x : ℝ => -(Complex.exp (-(μ * x)) * inner ℂ W (B0224.T0 hc ν x AU0))) (Ioi 0) := by
    have hI : Integrable (fun t : ℝ => (innerSL ℂ W) (B0225.lapT0 hc ν μ AU0 t))
        (volume.restrict (Ioi (0 : ℝ))) :=
      ContinuousLinearMap.integrable_comp (innerSL ℂ W) hint
    refine hI.neg.congr (Eventually.of_forall fun t => ?_)
    simp only [Pi.neg_apply, innerSL_apply_apply, B0225.lapT0, inner_smul_right]
  have htend : Tendsto
      (fun t : ℝ => Complex.exp (-(μ * t)) * inner ℂ W (B0224.T0 hc ν t U))
      atTop (𝓝 0) := by
    have hexp : Tendsto (fun t : ℝ => Real.exp (-(μ.re + 1 / 4) * t)) atTop (𝓝 0) := by
      have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (Tendsto.const_mul_atTop hγ (tendsto_id (x := atTop)))
      exact Tendsto.congr (fun t => by simp only [Function.comp_apply, id, neg_mul]) h2
    have hb : Tendsto (fun t : ℝ => ‖W‖ * (‖U‖ * Real.exp (-(μ.re + 1 / 4) * t)))
        atTop (𝓝 0) := by
      simpa only [mul_zero] using ((hexp.const_mul ‖U‖).const_mul ‖W‖)
    refine squeeze_zero_norm' (Eventually.of_forall fun t => ?_) hb
    have hEq : Complex.exp (-(μ * t)) * inner ℂ W (B0224.T0 hc ν t U) =
        inner ℂ W (B0225.lapT0 hc ν μ U t) := by
      simp only [B0225.lapT0, inner_smul_right]
    rw [hEq]
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (B0225.norm_lapT0_le hc ν μ U t) (norm_nonneg _))
  have hfinal := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hfint htend
  have hT0_0 : B0224.T0 hc ν 0 U = U := by rw [B0224.T0_zero_eq]; rfl
  simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_mul, hT0_0] at hfinal
  rw [integral_neg] at hfinal
  rw [hR0]
  linear_combination -hfinal

/-! ### 3. Main theorem (`FlatAdjointWeakEq`) -/

/-- **Main theorem (`PartII-a:N04/3/1`)**: weak flat resolvent identity
`⟨(μ - A_0) u, (T0flat hc ν μ).adjoint Z⟩_H = ⟨u, PepsC 0 c Z⟩_H`
for every smooth meridional test `IsMeridTest c u` (source lines 1842–1843). -/
theorem flatAdjointWeakEq : FlatAdjointWeakEq := by
  refine flatAdjointWeakEq_of_apply fun ν c hc hν μ hγ u U AU0 hu hU hAU0 => ?_
  rw [T0flat_eq_PepsC_comp_R0 hc hγ AU0, R0_left_inverse_isMeridTest hc hν hγ hu hU hAU0]

end UnforcedLeray.Short.PartIIa
