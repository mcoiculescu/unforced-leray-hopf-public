import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_1Org
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.FarMaskAgree
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.BoxDenseZ
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.FarUpperZero

/-!
# The far mask vanishes above the output cut (source 3902-3912)

`farVanishAboveSeq`.  The far part `S_far` of `IsFarMaskG` transports to `farX Sf : Z → H`; the
set of `F` with `1_{s ≥ S}(farX Sf F) = 0` is closed, contains the box class (the pin has the
factor `1_{s<S}`), and box tensors are dense (`NearInst.Masked.boxDenseZ`).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Masked
  UnforcedLeray.Short.PartIIIb.NearInst.Delta
open UnforcedLeray.Blueprint.Planar (PlanarData)

/-- General form: an `IsFarMaskG` operator vanishes a.e. on `{Scut ≤ s}`. -/
theorem farVanishAbove_gen {c mZ ρb γ ν R μ δ Scut : ℝ} (hc : 0 < c) (hmZ : 0 ≤ mZ)
    (hρ : 0 < ρb) (hν : 0 < ν) (Sf : StrG c mZ ρb γ ν →L[ℝ] VelG c γ ν)
    (hSf : IsFarMaskG R μ δ Scut Sf) (T : StrG c mZ ρb γ ν) :
    ∀ᵐ p ∂(ageμ c (-3 / 2)), Scut ≤ p.1 → (Sf T : Chart → Merid) p = 0 := by
  set X := farX c mZ ρb γ ν hν Sf with hXdef
  have hA : MeasurableSet (ageAbove Scut) := measurableSet_le measurable_const measurable_fst
  have hbox : ∀ G : Zsp c mZ ρb,
      (∃ f : Chart → Ten3, IsBoxTensor f ∧ zsum G =ᵐ[ageμ c (-1 / 2)] f) →
        outRestr c (ageAbove Scut) (X G) = 0 := by
    rintro G ⟨f, hf, hzf⟩
    have hT₀f : strSum (strOfZ c mZ ρb γ ν hν G) =ᵐ[ageμ c (-1 / 2)] f := by
      filter_upwards [strSum_strOfZ_ae hρ hν G, hzf] with p a b
      exact a.trans b
    have h1 := hSf (strOfZ c mZ ρb γ ν hν G) f hf hT₀f
    have h2 : (X G : Chart → Merid) =ᵐ[ageμ c (-3 / 2)] farOut R c ν μ δ Scut f :=
      (farX_ae hν Sf G).trans h1
    have hres : (outRestr c (ageAbove Scut) (X G) : Chart → Merid) =ᵐ[ageμ c (-3 / 2)]
        (ageAbove Scut).indicator (fun _ => (1 : ℝ)) • (X G : Chart → Merid) :=
      restrLp_ae hA (X G)
    apply Lp.ext
    filter_upwards [hres, h2, Lp.coeFn_zero (E := Merid) 2 (ageμ c (-3 / 2))] with x e1 e2 e3
    rw [e1, e3]
    change (ageAbove Scut).indicator (fun _ => (1 : ℝ)) x • (X G : Chart → Merid) x = 0
    rw [e2]
    by_cases hx : x ∈ ageAbove Scut
    · have hx' : Scut ≤ x.1 := hx
      rw [Set.indicator_of_mem hx, farOut_eq_zero_of_le f x hx', smul_zero]
    · rw [Set.indicator_of_notMem hx, zero_smul]
  have hclosed : IsClosed {H : Zsp c mZ ρb | outRestr c (ageAbove Scut) (X H) = 0} :=
    isClosed_eq ((outRestr c (ageAbove Scut)).continuous.comp X.continuous) continuous_const
  set F := gainEquiv c mZ ρb γ hν (strIso c mZ ρb γ ν T) with hF
  have hcl : F ∈ closure {H : Zsp c mZ ρb |
      ∃ f : Chart → Ten3, IsBoxTensor f ∧ zsum H =ᵐ[ageμ c (-1 / 2)] f} := by
    rw [Metric.mem_closure_iff]
    intro η hη
    obtain ⟨G', hG', hn⟩ := boxDenseZ c mZ ρb hc hmZ hρ F η hη
    exact ⟨G', hG', by rw [dist_eq_norm]; exact hn⟩
  have hzero : outRestr c (ageAbove Scut) (X F) = 0 :=
    closure_minimal (fun H hH => hbox H hH) hclosed hcl
  have hFT : strOfZ c mZ ρb γ ν hν F = T := by
    simp [strOfZ, hF]
  have e0 := farX_ae hν Sf F
  rw [hFT] at e0
  have hres : (outRestr c (ageAbove Scut) (X F) : Chart → Merid) =ᵐ[ageμ c (-3 / 2)]
      (ageAbove Scut).indicator (fun _ => (1 : ℝ)) • (X F : Chart → Merid) :=
    restrLp_ae hA (X F)
  rw [hzero] at hres
  filter_upwards [hres, e0, Lp.coeFn_zero (E := Merid) 2 (ageμ c (-3 / 2))] with x e1 e2 e3 hx
  rw [← e2]
  have : (ageAbove Scut).indicator (fun _ => (1 : ℝ)) x • (X F : Chart → Merid) x = 0 :=
    e1.symm.trans e3
  rw [Set.indicator_of_mem (show x ∈ ageAbove Scut from hx)] at this
  simpa using this

/-- **Output cut** (3905-3912), sequence level. -/
theorem farVanishAboveSeq (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) :
    FarVanishAboveSeq Pl σ₀ mZ dm dp := by
  intro D _ _ hmZ hst
  refine Eventually.of_forall fun n z _ => ?_
  intro Sf hSf T
  have hν := (D.level n).ν_pos
  have hρ : 0 < (D.level n).ρb D.Pl D.K := by
    have h0 := hst.C0_pos
    have h1 := (D.level n).ε_pos
    unfold ReturnLevel.ρb UnforcedLeray.Short.IIb.rhoB
    have : 0 < (D.level n).ν := hν
    show 0 < D.K.C0 * ((D.level n).ν ^ D.K.k0)⁻¹ * Real.exp (D.K.m0 / (D.level n).ν) *
      (D.level n).ε ^ (3 / 11 : ℝ)
    positivity
  have hmZ' : 0 ≤ D.K.mZ := by linarith [hst.mZ_gt]
  have := farVanishAbove_gen (cOf_pos hν) hmZ' hρ hν Sf hSf T
  rwa [NearInst.ae_srcMeasure]
