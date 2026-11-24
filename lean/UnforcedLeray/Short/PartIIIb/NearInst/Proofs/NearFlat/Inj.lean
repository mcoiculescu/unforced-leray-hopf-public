import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_3
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Assembly
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Agree

/-!
# `nearD0Inj_of` (source 3560-3581): injectivity of `D₀ = I + M₀S₀`

If `D₀F = 0` then `F = -M₀h` with `h = S₀F`. Then `zsum F = -(v ⊗ h + h ⊗ v)` a.e. (the
meridional block of `F₁ + F₂`, `F₂ = 0`), so `b = velC h` solves the actual equation with zero
force (`IsCausalEnergySolution` with vel `trainVel tr`). Uniqueness of homogeneous causal solutions
(`flatHomogeneousUnique_of_polyCausal`, from `PolyCausal`) gives `b = 0` a.e., hence `h = 0` in `H`,
hence `F = 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- The meridional block of `-(a⊗h + h⊗a)` is `-(a_i h_j + h_i a_j)`. -/
theorem nsSym_neg_ten3Of_symOuter (a h : Merid) (i j : Fin 2) :
    nsSym (-(ten3Of (UnforcedLeray.Short.IIIa.symOuter a h))) (merIdx i) (merIdx j) =
      -(a i * h j + h i * a j) := by
  fin_cases i <;> fin_cases j <;>
    simp [nsSym, ten3Of, UnforcedLeray.Short.IIIa.symOuter, UnforcedLeray.Short.IIIa.embedMerid,
      merIdx, symRZ] <;> ring

/-- Swapping the free and the flat terms in the integrand, pointwise at `p`. -/
theorem flatIntegrand_swap (ν : ℝ) (μ : ℂ) (vel : ℝ → ℝ × ℝ → Fin 2 → ℝ)
    (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (p : ℝ × (ℝ × ℝ))
    (hFp : ∀ i j, F p i j = -(((vel p.1 p.2 i : ℝ) : ℂ) * b p j +
      b p i * ((vel p.1 p.2 j : ℝ) : ℂ))) :
    UnforcedLeray.Short.IIIa.flatIntegrand ν μ (fun _ _ _ => 0) F b Φ p =
      UnforcedLeray.Short.IIIa.flatIntegrand ν μ vel (fun _ _ _ => 0) b Φ p := by
  unfold UnforcedLeray.Short.IIIa.flatIntegrand
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hFp i j]
  dsimp only
  push_cast
  ring

/-- Transport of a causal energy solution along an a.e. identity of the integrands. -/
theorem causal_transport {c ν : ℝ} {μ : ℂ} {vel vel' : ℝ → ℝ × ℝ → Fin 2 → ℝ}
    {F F' : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hF : UnforcedLeray.Short.IIIa.IsCausalEnergySolution c ν μ vel F b G)
    (hI : ∀ Φ, UnforcedLeray.Short.IIIa.flatIntegrand ν μ vel F b Φ =ᵐ[volume.restrict
        (Ioi (0 : ℝ) ×ˢ UnforcedLeray.B0579.cell c)]
      UnforcedLeray.Short.IIIa.flatIntegrand ν μ vel' F' b Φ) :
    UnforcedLeray.Short.IIIa.IsCausalEnergySolution c ν μ vel' F' b G := by
  refine ⟨hF.measurable, hF.gradMeasurable, hF.energyLoc, hF.zeroEntrance, hF.divFree,
    hF.weakGrad, ?_, ?_⟩
  · intro Φ hΦ
    exact (hF.integrable Φ hΦ).congr_fun_ae (hI Φ)
  · intro Φ hΦ
    rw [← integral_congr_ae (hI Φ)]
    exact hF.weak Φ hΦ

/-- **Injectivity of `D₀`** (source 3560-3581), from the uniqueness clause of `PolyCausal`. -/
theorem nearD0Inj_of (hPC : UnforcedLeray.Short.IIIa.PolyCausal) : NearD0Inj := by
  unfold NearD0Inj
  intro P hP Kset hK hKs mZ hmZ
  obtain ⟨ν₀, hν₀, hU⟩ := flatHomogeneousUnique_of_polyCausal hPC hP hK hKs
  refine ⟨ν₀, hν₀, fun ν hν hνν₀ c hc tr htr ρb hρ0 hρ1 μ hμ o hM hS => ?_⟩
  have hcpos : 0 < c := by rw [hc]; positivity
  have hU' : FlatHomogeneousUnique c ν (μ : ℂ) (UnforcedLeray.Short.IIIa.trainVel tr) :=
    hU ν ⟨hν, hνν₀⟩ c hc tr htr μ hμ
  rw [injective_iff_map_eq_zero]
  intro F hF
  obtain ⟨b, G, hb, hsol⟩ := hS F
  have hD : F + o.M0 (o.S0 F) = 0 := by simpa [NearOps.D0] using hF
  have hFeq : F = -(o.M0 (o.S0 F)) := eq_neg_of_add_eq_zero_left hD
  obtain ⟨hMfst, hMsnd⟩ := hM (o.S0 F)
  set h := o.S0 F with hh
  -- the component facts of `F = -M₀h`
  have hsnd : F.snd = 0 := by rw [hFeq, WithLp.neg_snd, hMsnd, neg_zero]
  have hfst0 : F.fst = -(o.M0 h).fst := by rw [hFeq, WithLp.neg_fst]
  have hfst1 : (F.fst : Chart → Ten3) =ᵐ[z1Measure c mZ] -((o.M0 h).fst : Chart → Ten3) := by
    rw [hfst0]
    exact Lp.coeFn_neg _
  have hfst2 : (F.fst : Chart → Ten3) =ᵐ[z1Measure c mZ]
      fun p => -(ten3Of (UnforcedLeray.Short.IIIa.symOuter (trainMer tr p) (h p))) := by
    filter_upwards [hfst1, hMfst] with p h1 h2
    simp only [Pi.neg_apply] at h1
    rw [h1, h2]
  rw [ae_z1Measure] at hfst2
  have hsnd1 : (F.snd : Chart → Ten3) =ᵐ[htRhoMeasure c ρb] 0 := by
    rw [hsnd]
    exact Lp.coeFn_zero _ _ _
  rw [ae_htRhoMeasure hρ0] at hsnd1
  have hz : ∀ᵐ p ∂(ageμ c (-1 / 2)),
      zsum F p = -(ten3Of (UnforcedLeray.Short.IIIa.symOuter (trainMer tr p) (h p))) := by
    filter_upwards [hfst2, hsnd1] with p h1 h2
    have h2' : (F.snd : Chart → Ten3) p = 0 := h2
    simp only [zsum]
    rw [h1, h2', add_zero]
  have hz' := (volCyl_ac_ageμ hcpos (-1 / 2)).ae_le hz
  have hbV := (volCyl_ac_ageμ hcpos (-3 / 2)).ae_le hb
  -- the flat integrand identity
  have hpt : ∀ᵐ p ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ UnforcedLeray.B0579.cell c)),
      ∀ i j, merBlockC (zsum F) p i j = -(((UnforcedLeray.Short.IIIa.trainVel tr p.1 p.2 i : ℝ) : ℂ)
        * b p j + b p i * ((UnforcedLeray.Short.IIIa.trainVel tr p.1 p.2 j : ℝ) : ℂ)) := by
    filter_upwards [hz', hbV] with p h1 h2
    intro i j
    have hbp : ∀ k, b p k = ((h p k : ℝ) : ℂ) := fun k => by
      have := congrFun h2 k
      simpa [velC] using this
    simp only [merBlockC]
    rw [h1, nsSym_neg_ten3Of_symOuter, hbp, hbp]
    simp [trainMer]
  have hI : ∀ Φ, UnforcedLeray.Short.IIIa.flatIntegrand ν μ (fun _ _ _ => 0) (merBlockC (zsum F)) b Φ
      =ᵐ[volume.restrict (Ioi (0 : ℝ) ×ˢ UnforcedLeray.B0579.cell c)]
      UnforcedLeray.Short.IIIa.flatIntegrand ν μ (UnforcedLeray.Short.IIIa.trainVel tr)
        (fun _ _ _ => 0) b Φ := by
    intro Φ
    filter_upwards [hpt] with p hp
    exact flatIntegrand_swap ν μ _ _ b Φ p hp
  have hsol' : UnforcedLeray.Short.IIIa.IsCausalEnergySolution c ν (μ : ℂ)
      (UnforcedLeray.Short.IIIa.trainVel tr) (fun _ _ _ => 0) b G :=
    causal_transport hsol hI
  have hb0 : ∀ᵐ p ∂(ageμ c (-3 / 2)), b p = 0 :=
    (ageμ_ac_volCyl c (-3 / 2)).ae_le (hU' b G hsol')
  have hh0 : ∀ᵐ p ∂(ageμ c (-3 / 2)), (h : Chart → Merid) p = 0 := by
    filter_upwards [hb, hb0] with p h1 h2
    ext i
    have h3 := congrFun (h1.symm.trans h2) i
    simpa [velC] using h3
  have hh0' : (h : Chart → Merid) =ᵐ[ageμ c (-3 / 2)] (0 : Chart → Merid) := hh0
  have hh : h = 0 := Lp.ext (hh0'.trans (Lp.coeFn_zero _ _ _).symm)
  rw [hh, map_zero, neg_zero] at hFeq
  exact hFeq

end UnforcedLeray.Short.PartIIIb.NearInst
