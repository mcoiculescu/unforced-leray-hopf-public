import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_2_4
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# `PartII-a:N01/9/1/2/4/1/b`: the slab divergence vanishes

Source `the November 2 reference manuscript`
lines 1650-1658, 1684-1689, 3379-3383, 3426-3430.  Fundamental lemma of the calculus of
variations on the open cell box `s > 0`, `0 < q < c` with the smooth positive weight
`s ^ (-3/2)`.  Integration by parts in the `(q,η)` directions (`G` has compact support, so no
boundary terms) gives `∫ G · s^{-3/2} · (∂_q F₀ + ∂_η F₁) = 0` for all cell tests `G`; then
the fundamental lemma and continuity give the pointwise identity on the box.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.B0220 (Profile)

/-- The cell box `s > 0`, `0 < q < c`, all `η`. -/
abbrev cellBox (c : ℝ) : Set Profile := Ioi (0:ℝ) ×ˢ (Ioo (0:ℝ) c ×ˢ (univ : Set ℝ))

theorem isOpen_cellBox (c : ℝ) : IsOpen (cellBox c) :=
  isOpen_Ioi.prod (isOpen_Ioo.prod isOpen_univ)

/-- The weighted component `s ^ (-3/2) · F_j(s,q,η)`. -/
def wF (F : Profile → UnforcedLeray.B0223.MeridC) (j : Fin 2) (y : Profile) : ℂ :=
  ((y.1 ^ (-(3/2:ℝ)) : ℝ) : ℂ) * F y j

/-- The divergence pairing `∂_q F₀ + ∂_η F₁` at a profile point. -/
def slabD (F : Profile → UnforcedLeray.B0223.MeridC) (p : Profile) : ℂ :=
  fderiv ℝ (fun x : Profile => F x 0) p (0, (1, 0)) +
    fderiv ℝ (fun x : Profile => F x 1) p (0, (0, 1))

theorem contDiff_comp_apply (F : Profile → UnforcedLeray.B0223.MeridC) (hF : ContDiff ℝ ∞ F)
    (j : Fin 2) : ContDiff ℝ ∞ (fun x : Profile => F x j) := by
  have hL : ContDiff ℝ ∞ (fun v : UnforcedLeray.B0223.MeridC => v j) :=
    ((EuclideanSpace.proj j : UnforcedLeray.B0223.MeridC →L[ℂ] ℂ).restrictScalars ℝ).contDiff
  exact hL.comp hF

/-- Slice derivatives: `∂_z [Φ(σ,z)] = ∂Φ(σ,·)` in the direction `(0,v)`. -/
theorem fderiv_slice (Φ : Profile → ℂ) (hΦ : Differentiable ℝ Φ) (σ : ℝ) (y v : ℝ × ℝ) :
    fderiv ℝ (fun z : ℝ × ℝ => Φ (σ, z)) y v = fderiv ℝ Φ (σ, y) (0, v) := by
  have hg : HasFDerivAt (fun z : ℝ × ℝ => ((σ, z) : Profile))
      (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) y :=
    (hasFDerivAt_const σ y).prodMk (hasFDerivAt_id y)
  have hc := HasFDerivAt.comp y (hΦ (σ, y)).hasFDerivAt hg
  rw [show (fun z : ℝ × ℝ => Φ (σ, z)) = Φ ∘ (fun z : ℝ × ℝ => ((σ, z) : Profile)) from rfl,
    hc.fderiv]
  simp

/-- The derivative of the complex weight `s ↦ s^r` in a direction with no `s`-component
vanishes. -/
theorem fderiv_pow_dir (r : ℝ) {p : Profile} (hp : 0 < p.1) {v : Profile} (hv : v.1 = 0) :
    fderiv ℝ (fun x : Profile => ((x.1 ^ r : ℝ) : ℂ)) p v = 0 := by
  have hρ : HasDerivAt (fun s : ℝ => ((s ^ r : ℝ) : ℂ)) (((r * p.1 ^ (r - 1) : ℝ)) : ℂ) p.1 :=
    (Real.hasDerivAt_rpow_const (x := p.1) (p := r) (Or.inl hp.ne')).ofReal_comp
  have hfst : HasFDerivAt (fun x : Profile => x.1) (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) p :=
    hasFDerivAt_fst
  have hc := HasFDerivAt.comp p hρ.hasFDerivAt hfst
  rw [show (fun x : Profile => ((x.1 ^ r : ℝ) : ℂ)) = (fun s : ℝ => ((s ^ r : ℝ) : ℂ)) ∘ Prod.fst
    from rfl, hc.fderiv]
  simp [hv]

/-- The weight `s^{-3/2}` is smooth on the box. -/
theorem contDiffAt_rho (x : Profile) (hx : 0 < x.1) :
    ContDiffAt ℝ ∞ (fun y : Profile => ((y.1 ^ (-(3/2:ℝ)) : ℝ) : ℂ)) x := by
  have h1 : ContDiffAt ℝ ∞ (fun y : Profile => y.1 ^ (-(3/2:ℝ))) x :=
    ContDiffAt.rpow_const_of_ne contDiff_fst.contDiffAt hx.ne'
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp x h1

theorem fderiv_wF_dir (F : Profile → UnforcedLeray.B0223.MeridC) (j : Fin 2) {x : Profile}
    (hx : 0 < x.1) {v : Profile} (hv : v.1 = 0)
    (hFj : Differentiable ℝ (fun y : Profile => F y j)) :
    fderiv ℝ (wF F j) x v =
      ((x.1 ^ (-(3/2:ℝ)) : ℝ) : ℂ) * fderiv ℝ (fun y : Profile => F y j) x v := by
  have hρd : DifferentiableAt ℝ (fun y : Profile => ((y.1 ^ (-(3/2:ℝ)) : ℝ) : ℂ)) x :=
    (contDiffAt_rho x hx).differentiableAt (by simp)
  have hz := fderiv_pow_dir (-(3/2:ℝ)) hx hv
  unfold wF
  rw [fderiv_fun_mul hρd (hFj x)]
  simp [hz]

/-- Fundamental lemma on an open set, for a function continuous on the set. -/
theorem fund_lemma {U : Set Profile} (hU : IsOpen U) {f : Profile → ℂ} (hf : ContinuousOn f U)
    (h : ∀ g : Profile → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ U →
      ∫ x, g x • f x = 0) :
    ∀ x ∈ U, f x = 0 := by
  have hae : ∀ᵐ x ∂(volume : Measure Profile), x ∈ U → f x = 0 :=
    hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hf.locallyIntegrableOn (μ := volume) hU.measurableSet) h
  intro x0 hx0
  by_contra hne
  have hVo : IsOpen (U ∩ f ⁻¹' {0}ᶜ) := hf.isOpen_inter_preimage hU isOpen_compl_singleton
  have hVne : (U ∩ f ⁻¹' {0}ᶜ).Nonempty := ⟨x0, hx0, hne⟩
  have hpos : 0 < (volume : Measure Profile) (U ∩ f ⁻¹' {0}ᶜ) :=
    hVo.measure_pos (μ := volume) hVne
  have hnull : ∀ᵐ x ∂(volume : Measure Profile), x ∉ U ∩ f ⁻¹' {0}ᶜ := by
    filter_upwards [hae] with x hx hxV
    exact hxV.2 (hx hxV.1)
  have h0 := ae_iff.mp hnull
  have h0' : (volume : Measure Profile) (U ∩ f ⁻¹' {0}ᶜ) = 0 := by
    simpa only [not_not, Set.setOf_mem_eq] using h0
  exact hpos.ne' h0'

theorem integrable_of_cont {K : Set Profile} (hK : IsCompact K) {φ : Profile → ℂ}
    (h0 : ∀ x, x ∉ K → φ x = 0) (hc : ContinuousOn φ K) : Integrable φ := by
  have h1 : IntegrableOn φ K := hc.integrableOn_compact hK
  exact (integrableOn_iff_integrable_of_support_subset
    (fun x hx => by by_contra h; exact hx (h0 x h))).mp h1

/-- The test identity: for every smooth compactly supported cell test `G`,
`∫ G · s^{-3/2} · slabD F = 0`, by integration by parts in `(q,η)` and the hypothesis. -/
theorem test_identity (c : ℝ) (F : Profile → UnforcedLeray.B0223.MeridC) (hF : ContDiff ℝ ∞ F)
    (h : ∀ G : Profile → ℝ, ContDiff ℝ ∞ G → HasCompactSupport G →
      tsupport G ⊆ (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) c ×ˢ (Set.univ : Set ℝ))) →
      ∫ p in (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) c ×ˢ (Set.univ : Set ℝ))),
        (((p.1 ^ (-(3/2:ℝ)) : ℝ) : ℂ) * (((UnforcedLeray.Axi.dQ G p : ℝ) : ℂ) * F p 0 +
          ((UnforcedLeray.Axi.dEta G p : ℝ) : ℂ) * F p 1)) = 0)
    (G : Profile → ℝ) (hG : ContDiff ℝ ∞ G) (hGc : HasCompactSupport G)
    (hGs : tsupport G ⊆ cellBox c) :
    ∫ x, G x • (((x.1 ^ (-(3/2:ℝ)) : ℝ) : ℂ) * slabD F x) = 0 := by
  have hGd : Differentiable ℝ G := hG.differentiable (by simp)
  have hGc0 : Continuous G := hG.continuous
  have hGfd : Continuous (fun x => fderiv ℝ G x) := hG.continuous_fderiv (by simp)
  have hKc : IsCompact (tsupport G) := hGc.isCompact
  have hGz : ∀ x, x ∉ tsupport G → G x = 0 := fun x hx => by
    by_contra h'
    exact hx (subset_tsupport G (Function.mem_support.mpr h'))
  have hfdz : ∀ x, x ∉ tsupport G → ∀ v : Profile, fderiv ℝ G x v = 0 := by
    intro x hx v
    have h0 : fderiv ℝ G x = 0 := by
      by_contra h'
      exact hx (support_fderiv_subset (𝕜 := ℝ) (Function.mem_support.mpr h'))
    simp [h0]
  have hFj : ∀ j : Fin 2, Differentiable ℝ (fun x : Profile => F x j) :=
    fun j => (contDiff_comp_apply F hF j).differentiable (by simp)
  -- smoothness of the weighted components on the box
  have hψB : ∀ j : Fin 2, ContDiffOn ℝ ∞ (wF F j) (cellBox c) := by
    intro j x hx
    exact ((contDiffAt_rho x hx.1).mul (contDiff_comp_apply F hF j).contDiffAt).contDiffWithinAt
  have hψd : ∀ j : Fin 2, ∀ x ∈ cellBox c, DifferentiableAt ℝ (wF F j) x := fun j x hx =>
    ((contDiffAt_rho x hx.1).mul (contDiff_comp_apply F hF j).contDiffAt).differentiableAt
      (by simp)
  have hψc : ∀ j : Fin 2, ContinuousOn (wF F j) (cellBox c) := fun j => (hψB j).continuousOn
  have hψfc : ∀ j : Fin 2, ContinuousOn (fun x => fderiv ℝ (wF F j) x) (cellBox c) :=
    fun j => (hψB j).continuousOn_fderiv_of_isOpen (isOpen_cellBox c) (by simp)
  have hwd : ∀ j : Fin 2, ∀ x ∈ tsupport G, DifferentiableAt ℝ (wF F j) x := fun j x hx =>
    hψd j x (hGs hx)
  have hwc : ∀ j : Fin 2, ContinuousOn (wF F j) (tsupport G) := fun j => (hψc j).mono hGs
  have hwfc : ∀ j : Fin 2, ContinuousOn (fun x => fderiv ℝ (wF F j) x) (tsupport G) :=
    fun j => (hψfc j).mono hGs
  have hA : ∀ (j : Fin 2) (v : Profile), Integrable (fun x => fderiv ℝ G x v • wF F j x) :=
    fun j v => integrable_of_cont hKc (fun x hx => by simp [hfdz x hx v])
      (((hGfd.clm_apply continuous_const).continuousOn).smul (hwc j))
  have hB : ∀ (j : Fin 2) (v : Profile), Integrable (fun x => G x • fderiv ℝ (wF F j) x v) :=
    fun j v => integrable_of_cont hKc (fun x hx => by simp [hGz x hx])
      (hGc0.continuousOn.smul ((hwfc j).clm_apply continuousOn_const))
  have hC : ∀ j : Fin 2, Integrable (fun x => G x • wF F j x) :=
    fun j => integrable_of_cont hKc (fun x hx => by simp [hGz x hx])
      (hGc0.continuousOn.smul (hwc j))
  have hHaar : (volume : Measure Profile).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  -- integration by parts in the `(q,η)` directions
  have ibp : ∀ (j : Fin 2) (v : Profile),
      ∫ x, G x • fderiv ℝ (wF F j) x v = -∫ x, fderiv ℝ G x v • wF F j x :=
    fun j v => integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (hA j v) (hB j v) (hC j)
      (fun x _ => hGd x) (fun x hx => hwd j x hx)
  -- pointwise identity on the box
  have hpt : ∀ x, G x • (((x.1 ^ (-(3/2:ℝ)) : ℝ) : ℂ) * slabD F x) =
      G x • fderiv ℝ (wF F 0) x (0, (1, 0)) + G x • fderiv ℝ (wF F 1) x (0, (0, 1)) := by
    intro x
    by_cases hx : x ∈ cellBox c
    · rw [fderiv_wF_dir F 0 (v := (0, (1, 0))) hx.1 rfl (hFj 0),
        fderiv_wF_dir F 1 (v := (0, (0, 1))) hx.1 rfl (hFj 1)]
      simp only [slabD, mul_add, smul_add]
    · have : G x = 0 := hGz x (fun hxK => hx (hGs hxK))
      simp [this]
  have hsum : ∫ x, G x • (((x.1 ^ (-(3/2:ℝ)) : ℝ) : ℂ) * slabD F x) =
      ∫ x, (G x • fderiv ℝ (wF F 0) x (0, (1, 0)) + G x • fderiv ℝ (wF F 1) x (0, (0, 1))) :=
    integral_congr_ae (Filter.Eventually.of_forall hpt)
  have hS : ∫ x, (G x • fderiv ℝ (wF F 0) x (0, (1, 0)) + G x • fderiv ℝ (wF F 1) x (0, (0, 1)))
      = (∫ x, G x • fderiv ℝ (wF F 0) x (0, (1, 0))) +
        (∫ x, G x • fderiv ℝ (wF F 1) x (0, (0, 1))) :=
    integral_add (hB 0 (0, (1, 0))) (hB 1 (0, (0, 1)))
  -- the hypothesis, transported to the whole space
  have hzero : ∀ x, x ∉ cellBox c →
      (((x.1 ^ (-(3/2:ℝ)) : ℝ) : ℂ) * (((UnforcedLeray.Axi.dQ G x : ℝ) : ℂ) * F x 0 +
        ((UnforcedLeray.Axi.dEta G x : ℝ) : ℂ) * F x 1)) = 0 := by
    intro x hx
    have hxK : x ∉ tsupport G := fun hxK => hx (hGs hxK)
    simp [UnforcedLeray.Axi.dQ, UnforcedLeray.Axi.dEta, hfdz x hxK]
  have hh := (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm.trans
    (h G hG hGc hGs)
  have hpt2 : ∀ x, (((x.1 ^ (-(3/2:ℝ)) : ℝ) : ℂ) * (((UnforcedLeray.Axi.dQ G x : ℝ) : ℂ) *
      F x 0 + ((UnforcedLeray.Axi.dEta G x : ℝ) : ℂ) * F x 1)) =
      fderiv ℝ G x (0, (1, 0)) • wF F 0 x + fderiv ℝ G x (0, (0, 1)) • wF F 1 x := by
    intro x
    simp only [wF, Complex.real_smul, UnforcedLeray.Axi.dQ, UnforcedLeray.Axi.dEta]
    ring
  have hint : ∫ x, (((x.1 ^ (-(3/2:ℝ)) : ℝ) : ℂ) * (((UnforcedLeray.Axi.dQ G x : ℝ) : ℂ) *
      F x 0 + ((UnforcedLeray.Axi.dEta G x : ℝ) : ℂ) * F x 1)) =
      ∫ x, (fderiv ℝ G x (0, (1, 0)) • wF F 0 x + fderiv ℝ G x (0, (0, 1)) • wF F 1 x) :=
    integral_congr_ae (Filter.Eventually.of_forall hpt2)
  have hT : ∫ x, (fderiv ℝ G x (0, (1, 0)) • wF F 0 x + fderiv ℝ G x (0, (0, 1)) • wF F 1 x)
      = 0 := by
    rw [← hint]
    exact hh
  have hTs : ∫ x, (fderiv ℝ G x (0, (1, 0)) • wF F 0 x + fderiv ℝ G x (0, (0, 1)) • wF F 1 x)
      = (∫ x, fderiv ℝ G x (0, (1, 0)) • wF F 0 x) +
        (∫ x, fderiv ℝ G x (0, (0, 1)) • wF F 1 x) :=
    integral_add (hA 0 (0, (1, 0))) (hA 1 (0, (0, 1)))
  have e0 := ibp 0 (0, (1, 0))
  have e1 := ibp 1 (0, (0, 1))
  linear_combination hsum + hS + e0 + e1 + hTs - hT

/-- **(S7)** The slab divergence of a smooth force with vanishing weighted cell pairings vanishes
on the open cell `0 < q < c`. -/
theorem slabDivFundamental (c : ℝ) (hc : 0 < c) (F : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) (hF : ContDiff ℝ ∞ F) (h : ∀ G : UnforcedLeray.B0220.Profile → ℝ, ContDiff ℝ ∞ G → HasCompactSupport G → tsupport G ⊆ (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) c ×ˢ (Set.univ : Set ℝ))) → ∫ p in (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) c ×ˢ (Set.univ : Set ℝ))), (((p.1 ^ (-(3/2:ℝ)) : ℝ) : ℂ) * (((UnforcedLeray.Axi.dQ G p : ℝ) : ℂ) * F p 0 + ((UnforcedLeray.Axi.dEta G p : ℝ) : ℂ) * F p 1)) = 0) : ∀ σ q η : ℝ, 0 < σ → 0 < q → q < c → UnforcedLeray.Short.PartIIa.N01.slabDiv F σ (q, η) = 0 := by
  intro σ q η hσ hq0 hqc
  have hFj : ∀ j : Fin 2, Differentiable ℝ (fun x : Profile => F x j) :=
    fun j => (contDiff_comp_apply F hF j).differentiable (by simp)
  have hFjc : ∀ j : Fin 2, Continuous (fderiv ℝ (fun x : Profile => F x j)) :=
    fun j => (contDiff_comp_apply F hF j).continuous_fderiv (by simp)
  have hslabC : Continuous (slabD F) := by
    unfold slabD
    exact ((hFjc 0).clm_apply continuous_const).add ((hFjc 1).clm_apply continuous_const)
  have hfc : ContinuousOn (fun x : Profile => ((x.1 ^ (-(3/2:ℝ)) : ℝ) : ℂ) * slabD F x)
      (cellBox c) := by
    apply ContinuousOn.mul
    · intro x hx
      exact (contDiffAt_rho x hx.1).continuousAt.continuousWithinAt
    · exact hslabC.continuousOn
  have hfund := fund_lemma (isOpen_cellBox c) hfc
    (fun G hG hGc hGs => test_identity c F hF h G hG hGc hGs)
  have hD : ∀ x ∈ cellBox c, slabD F x = 0 := by
    intro x hx
    have hne : ((x.1 ^ (-(3/2:ℝ)) : ℝ) : ℂ) ≠ 0 := by
      have hp : (0:ℝ) < x.1 ^ (-(3/2:ℝ)) := Real.rpow_pos_of_pos hx.1 _
      exact_mod_cast hp.ne'
    exact (mul_eq_zero.mp (hfund x hx)).resolve_left hne
  have hslab : ∀ y : ℝ × ℝ, slabDiv F σ y = slabD F (σ, y) := by
    intro y
    unfold slabDiv
    rw [Fin.sum_univ_two]
    have e0 : fderiv ℝ (fun z : ℝ × ℝ => F (σ, z) 0) y (1, 0) =
        fderiv ℝ (fun x : Profile => F x 0) (σ, y) (0, (1, 0)) :=
      fderiv_slice (fun x : Profile => F x 0) (hFj 0) σ y (1, 0)
    have e1 : fderiv ℝ (fun z : ℝ × ℝ => F (σ, z) 1) y (0, 1) =
        fderiv ℝ (fun x : Profile => F x 1) (σ, y) (0, (0, 1)) :=
      fderiv_slice (fun x : Profile => F x 1) (hFj 1) σ y (0, 1)
    rw [show UnforcedLeray.B0579.dir 0 = (1, 0) from rfl,
      show UnforcedLeray.B0579.dir 1 = (0, 1) from rfl, e0, e1]
    rfl
  rw [hslab]
  exact hD (σ, (q, η)) ⟨hσ, ⟨hq0, hqc⟩, trivial⟩

end UnforcedLeray.Short.PartIIa.N01
