import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N04_3_Org

/-!


Source of record: `the November 2 reference manuscript`,
lines 1669-1670 (`P_0` is the planar cylinder projection) and 1724 (`P_0` is a Fourier multiplier
in `(q, η)` at each age `s`).

Proof idea. `P_0 = PepsC 0 c` is the orthogonal projection onto `S = (span G)ᗮ`, where `G` is the
set of gradients `cgrad 0 Φ` of profile tests. Multiplication `M` by a bounded smooth `χ(s)` is
self-adjoint on `H`; it maps each generator to a generator (`cgrad 0 (χ Φ) = χ cgrad 0 Φ` and
`χ Φ` is a profile test), hence maps `span G` into itself, hence `S` into itself. Then
`P (M Z) = M (P Z)` by the characterisation of the star projection.
-/

set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

namespace FlatProjCommAux

/-- A profile test times a smooth function of the age is a profile test. -/
lemma isProfileTest_mul_age {c : ℝ} {Φ : Profile → ℝ} (hΦ : IsProfileTest c Φ)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    IsProfileTest c (fun p => χ p.1 * Φ p) := by
  refine ⟨(hχ.comp contDiff_fst).mul hΦ.smooth, ?_, ?_⟩
  · intro p
    show χ p.1 * Φ (p.1, p.2.1 + c, p.2.2) = χ p.1 * Φ p
    rw [hΦ.periodic p]
  · obtain ⟨s0, s1, L, hs0, hb⟩ := hΦ.band
    refine ⟨s0, s1, L, hs0, fun p hp => hb p ?_⟩
    intro h
    exact hp (by simp [h])

/-- Directional derivative of a function of the age alone in a direction with zero age
component. -/
lemma fderiv_age_apply {χ : ℝ → ℝ} (hχ : Differentiable ℝ χ) (p v : Profile) (hv : v.1 = 0) :
    fderiv ℝ (fun q : Profile => χ q.1) p v = 0 := by
  have hc : HasFDerivAt (fun q : Profile => χ q.1)
      ((deriv χ p.1) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) p :=
    (hχ p.1).hasDerivAt.comp_hasFDerivAt p hasFDerivAt_fst
  rw [hc.fderiv]
  simp [hv]

/-- Product rule for a function of the age times a differentiable function, in a direction
with zero age component. -/
lemma fderiv_mul_age_apply {χ : ℝ → ℝ} (hχ : Differentiable ℝ χ) {Φ : Profile → ℝ}
    (hΦ : Differentiable ℝ Φ) (p v : Profile) (hv : v.1 = 0) :
    fderiv ℝ (fun q : Profile => χ q.1 * Φ q) p v = χ p.1 * fderiv ℝ Φ p v := by
  have hc : HasFDerivAt (fun q : Profile => χ q.1)
      ((deriv χ p.1) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) p :=
    (hχ p.1).hasDerivAt.comp_hasFDerivAt p hasFDerivAt_fst
  have hd := (hΦ p).hasFDerivAt
  have h : fderiv ℝ (fun q : Profile => χ q.1 * Φ q) p = χ p.1 • fderiv ℝ Φ p +
      Φ p • ((deriv χ p.1) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) := (hc.mul hd).fderiv
  rw [h]
  simp [hv]

/-- `cgrad 0` of a profile test times an age function is the age function times `cgrad 0`. -/
lemma cgrad_mul_age {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {Φ : Profile → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) :
    cgrad 0 (fun p => χ p.1 * Φ p) = fun p => χ p.1 • cgrad 0 Φ p := by
  have hχd : Differentiable ℝ χ := hχ.differentiable (by simp)
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by simp)
  funext p
  have hQ : Axi.dQ (fun q : Profile => χ q.1 * Φ q) p = χ p.1 * Axi.dQ Φ p :=
    fderiv_mul_age_apply hχd hΦd p (0, (1, 0)) rfl
  have hE : Axi.dEta (fun q : Profile => χ q.1 * Φ q) p = χ p.1 * Axi.dEta Φ p :=
    fderiv_mul_age_apply hχd hΦd p (0, (0, 1)) rfl
  simp only [cgrad, Deps_zero]
  ext i
  fin_cases i <;> simp [hQ, hE]

/-- The generators `cgrad 0 Φ` of the span whose orthogonal complement is `solenoidalHC 0 c`. -/
def genSet (c : ℝ) : Set (HSpace c MeridC) :=
  {g | ∃ Φ : ProfileTest c, ∃ h : MemLp (cgrad 0 Φ.1) 2 (measureH c), g = h.toLp _}

lemma solenoidalHC_zero_eq (c : ℝ) :
    solenoidalHC 0 c = (Submodule.span ℂ (genSet c))ᗮ := rfl

/-- Multiplication by the bounded continuous age function `χ(s)` on `H`. -/
noncomputable def mulAge (c : ℝ) {χ : ℝ → ℝ} (hχ : Continuous χ) {B : ℝ}
    (hB : ∀ s, |χ s| ≤ B) : HSpace c MeridC →L[ℂ] HSpace c MeridC :=
  mulChi (measureH c) (fun p => χ p.1) (hχ.measurable.comp measurable_fst) (fun p => hB p.1)

lemma coe_mulAge {c : ℝ} {χ : ℝ → ℝ} (hχ : Continuous χ) {B : ℝ} (hB : ∀ s, |χ s| ≤ B)
    (f : HSpace c MeridC) :
    ((mulAge c hχ hB f : HSpace c MeridC) : Profile → MeridC) =ᵐ[measureH c]
      fun p => χ p.1 • ((f : HSpace c MeridC) : Profile → MeridC) p :=
  (memLp_chi_smul (measureH c) (fun p => χ p.1) (hχ.measurable.comp measurable_fst)
    (fun p => hB p.1) (Lp.memLp f)).coeFn_toLp

/-- `mulAge` is self-adjoint for the real multiplier `χ`. -/
lemma inner_mulAge {c : ℝ} {χ : ℝ → ℝ} (hχ : Continuous χ) {B : ℝ} (hB : ∀ s, |χ s| ≤ B)
    (f g : HSpace c MeridC) :
    inner ℂ (mulAge c hχ hB f) g = inner ℂ f (mulAge c hχ hB g) := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coe_mulAge hχ hB f, coe_mulAge hχ hB g] with p h1 h2
  rw [h1, h2]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rw [inner_smul_left, inner_smul_right]
  simp

/-- `mulAge` maps each generator to a generator, after multiplying the test by `χ`. -/
lemma mulAge_genSet {c : ℝ} {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {B : ℝ}
    (hB : ∀ s, |χ s| ≤ B) {g : HSpace c MeridC} (hg : g ∈ genSet c) :
    mulAge c hχ.continuous hB g ∈ Submodule.span ℂ (genSet c) := by
  obtain ⟨Φ, hmem, rfl⟩ := hg
  have hΨ : IsProfileTest c (fun p => χ p.1 * Φ.1 p) := isProfileTest_mul_age Φ.2 hχ
  have hmeas : Measurable (fun p : Profile => χ p.1) :=
    hχ.continuous.measurable.comp measurable_fst
  have hmemΨ : MemLp (cgrad 0 (fun p => χ p.1 * Φ.1 p)) 2 (measureH c) := by
    rw [cgrad_mul_age hχ Φ.2.smooth]
    exact memLp_chi_smul (measureH c) (fun p => χ p.1) hmeas (fun p => hB p.1) hmem
  have heq : mulAge c hχ.continuous hB (hmem.toLp _) = hmemΨ.toLp _ := by
    apply Lp.ext
    filter_upwards [coe_mulAge hχ.continuous hB (hmem.toLp _), hmem.coeFn_toLp,
      hmemΨ.coeFn_toLp] with p h1 h2 h3
    rw [h1, h3, h2, cgrad_mul_age hχ Φ.2.smooth]
  rw [heq]
  exact Submodule.subset_span ⟨⟨_, hΨ⟩, hmemΨ, rfl⟩

lemma mulAge_span {c : ℝ} {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {B : ℝ} (hB : ∀ s, |χ s| ≤ B)
    {x : HSpace c MeridC} (hx : x ∈ Submodule.span ℂ (genSet c)) :
    mulAge c hχ.continuous hB x ∈ Submodule.span ℂ (genSet c) := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact mulAge_genSet hχ hB hx
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

lemma mulAge_solenoidal {c : ℝ} {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {B : ℝ}
    (hB : ∀ s, |χ s| ≤ B) {s : HSpace c MeridC}
    (hs : s ∈ solenoidalHC 0 c) : mulAge c hχ.continuous hB s ∈ solenoidalHC 0 c := by
  rw [solenoidalHC_zero_eq] at hs ⊢
  rw [Submodule.mem_orthogonal] at hs ⊢
  intro u hu
  rw [← inner_mulAge hχ.continuous hB]
  exact hs _ (mulAge_span hχ hB hu)

end FlatProjCommAux

open FlatProjCommAux

/-- **Task `PartII-a:N04/3/5`**: `P_0 = PepsC 0 c` commutes with multiplication by a bounded
smooth function of the age. -/
theorem flatProjCommSMul : FlatProjCommSMul := by
  intro c _hc χ hχ hB' Z Y hY
  obtain ⟨B, hB⟩ := hB'
  have hχc := hχ.continuous
  have hcomm : ∀ W : HSpace c MeridC,
      PepsC 0 c (mulAge c hχc hB W) = mulAge c hχc hB (PepsC 0 c W) := by
    intro W
    show (solenoidalHC 0 c).starProjection (mulAge c hχc hB W) =
      mulAge c hχc hB ((solenoidalHC 0 c).starProjection W)
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
      (mulAge_solenoidal hχ hB
        (Submodule.starProjection_apply_mem _ _))
    intro w hw
    rw [← map_sub, inner_mulAge hχc hB]
    exact inner_eq_zero_symm.mpr
      ((Submodule.mem_orthogonal _ _).mp (Submodule.sub_starProjection_mem_orthogonal W) _
        (mulAge_solenoidal hχ hB hw))
  have hYM : Y = mulAge c hχc hB Z := by
    apply Lp.ext
    filter_upwards [hY, coe_mulAge hχc hB Z] with p h1 h2
    rw [h1, h2, Complex.coe_smul]
  rw [hYM, hcomm Z]
  filter_upwards [coe_mulAge hχc hB (PepsC 0 c Z)] with p h
  rw [h, Complex.coe_smul]

end UnforcedLeray.Short.PartIIa
