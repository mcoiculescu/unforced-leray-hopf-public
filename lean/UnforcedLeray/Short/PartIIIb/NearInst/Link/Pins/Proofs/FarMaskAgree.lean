import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Basic

/-!
# `FarMaskAgree` from box density (source 3902-3912)

Task `PartIII-b:C/near/pins/2`.  The operator `X := (√π)⁻¹ gainH velIso ∘ Sf ∘ strIso⁻¹ ∘ gainEquiv⁻¹`
agrees with `Sf'` on box-class inputs (both are the far kernel of the same box tensor); box inputs
are dense (`Masked.BoxDenseZ`), so `X = Sf'`; the zero stress has zero far output, which absorbs
the difference between the stress `T` and the transported stress `strOfZ F`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)

theorem isBoxTensor_zero : IsBoxTensor (0 : Chart → Ten3) :=
  ⟨measurable_zero, ⟨0, fun p => by simp⟩, ⟨1, 1, 0, one_pos, fun p hp => (hp rfl).elim⟩⟩

theorem nsSym_zero : nsSym (0 : Ten3) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nsSym, symRZ]

theorem sepW_zero (ν : ℝ) (μ : ℂ) (y : Space) (τ : ℝ) :
    UnforcedLeray.Short.IIIa.sepW ν μ (fun _ _ => (0 : Matrix (Fin 3) (Fin 3) ℝ)) y τ = 0 := by
  funext i
  simp [UnforcedLeray.Short.IIIa.sepW]

theorem merRe_zero : merRe (0 : Fin 3 → ℂ) = 0 := by
  ext i
  fin_cases i <;> simp [merRe]

theorem farOut_zero_eq (R c ν μ δ S : ℝ) (x : Chart) :
    Masked.farOut R c ν μ δ S (0 : Chart → Ten3) x = 0 := by
  have hc : cartLift R c (0 : Chart → Ten3) = fun _ _ => (0 : Matrix (Fin 3) (Fin 3) ℝ) := by
    funext τ z
    simp [cartLift, nsSym_zero]
  unfold Masked.farOut
  rw [hc]
  split_ifs
  · simp [sepWfar, sepW_zero, merRe_zero]
  · rfl

/-- Zero component sum gives zero far output. -/
theorem sf_zero_ae {c mZ ρb γ ν R μ δ Scut : ℝ} (Sf : StrG c mZ ρb γ ν →L[ℝ] VelG c γ ν)
    (hSf : Concrete.IsFarMaskG R μ δ Scut Sf) (G : StrG c mZ ρb γ ν)
    (hG : ∀ᵐ p ∂(ageμ c (-1 / 2)), strSum G p = 0) :
    (Sf G : Chart → Merid) =ᵐ[ageμ c (-3 / 2)] (0 : Chart → Merid) := by
  have hG' : strSum G =ᵐ[ageμ c (-1 / 2)] (0 : Chart → Ten3) := by
    filter_upwards [hG] with p hp
    exact hp
  have h := hSf G 0 isBoxTensor_zero hG'
  filter_upwards [h] with x hx
  rw [hx]
  exact farOut_zero_eq R c ν μ δ Scut x

/-- Difference of stresses: the component sum is additive a.e. -/
theorem strSum_sub_ae {c mZ ρb γ ν : ℝ} (hρ : 0 < ρb) (T T' : StrG c mZ ρb γ ν) :
    ∀ᵐ p ∂(ageμ c (-1 / 2)), strSum (T - T') p = strSum T p - strSum T' p := by
  have h1 := Lp.coeFn_sub T.fst T'.fst
  have h2 := Lp.coeFn_sub T.snd T'.snd
  rw [ae_gainZ1Measure c mZ γ ν, ae_z1Measure c mZ] at h1
  rw [ae_gainHTMeasure c ρb γ ν, ae_htRhoMeasure hρ] at h2
  filter_upwards [h1, h2] with p a b
  simp only [strSum]
  rw [show (T - T').fst = T.fst - T'.fst from rfl, show (T - T').snd = T.snd - T'.snd from rfl]
  rw [a, b]
  simp only [Pi.sub_apply]
  abel

/-- The transported stress `g⁻¹`-isometry preimage of a `Z`-element `F` with `F = gain(strIso T)`. -/
def strOfZ (c mZ ρb γ ν : ℝ) (hν : 0 < ν) (F : Zsp c mZ ρb) : StrG c mZ ρb γ ν :=
  (strIso c mZ ρb γ ν).symm ((gainEquiv c mZ ρb γ hν).symm F)

theorem strSum_strOfZ_ae {c mZ ρb γ ν : ℝ} (hρ : 0 < ρb) (hν : 0 < ν) (F : Zsp c mZ ρb) :
    ∀ᵐ p ∂(ageμ c (-1 / 2)), strSum (strOfZ c mZ ρb γ ν hν F) p = zsum F p := by
  have hF : gainEquiv c mZ ρb γ hν (strIso c mZ ρb γ ν (strOfZ c mZ ρb γ ν hν F)) = F := by
    unfold strOfZ
    simp
  have a1 := coeFn_zOfStr_fst γ hν (strOfZ c mZ ρb γ ν hν F)
  have a2 := coeFn_zOfStr_snd γ hν (strOfZ c mZ ρb γ ν hν F)
  rw [hF] at a1 a2
  rw [ae_z1Measure c mZ] at a1
  rw [ae_htRhoMeasure hρ] at a2
  filter_upwards [a1, a2] with p h1 h2
  simp only [strSum, zsum]
  rw [h1, h2]

/-- The transported far operator on `Z`. -/
def farX (c mZ ρb γ ν : ℝ) (hν : 0 < ν) (Sf : StrG c mZ ρb γ ν →L[ℝ] VelG c γ ν) :
    Zsp c mZ ρb →L[ℝ] Hsp c :=
  (Real.sqrt Real.pi)⁻¹ • ((gainH c γ hν).toContinuousLinearMap.comp
    ((velIso c γ ν).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (Sf.comp (((strIso c mZ ρb γ ν).symm).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((gainEquiv c mZ ρb γ hν).symm.toContinuousLinearMap)))))

theorem farX_apply {c mZ ρb γ ν : ℝ} (hν : 0 < ν) (Sf : StrG c mZ ρb γ ν →L[ℝ] VelG c γ ν)
    (F : Zsp c mZ ρb) :
    farX c mZ ρb γ ν hν Sf F =
      (Real.sqrt Real.pi)⁻¹ • gainH c γ hν (velIso c γ ν (Sf (strOfZ c mZ ρb γ ν hν F))) :=
  rfl

theorem farX_ae {c mZ ρb γ ν : ℝ} (hν : 0 < ν) (Sf : StrG c mZ ρb γ ν →L[ℝ] VelG c γ ν)
    (F : Zsp c mZ ρb) :
    (farX c mZ ρb γ ν hν Sf F : Chart → Merid) =ᵐ[ageμ c (-3 / 2)]
      (Sf (strOfZ c mZ ρb γ ν hν F) : Chart → Merid) := by
  rw [farX_apply]
  exact coeFn_hOfVel γ hν (Sf (strOfZ c mZ ρb γ ν hν F))

/-- **`FarMaskAgree` from box density** (source 3902-3912). -/
theorem farMaskAgree_of (hD : Masked.BoxDenseZ) : FarMaskAgree := by
  intro c mZ ρb γ ν R μ δ Scut hc hmZ hρ hν Sf Sf' hSf hSf' T F hTF
  have hbox : ∀ G : Zsp c mZ ρb,
      (∃ f : Chart → Ten3, IsBoxTensor f ∧ zsum G =ᵐ[ageμ c (-1 / 2)] f) →
        farX c mZ ρb γ ν hν Sf G = Sf' G := by
    rintro G ⟨f, hf, hzf⟩
    apply Lp.ext
    have hT₀f : strSum (strOfZ c mZ ρb γ ν hν G) =ᵐ[ageμ c (-1 / 2)] f := by
      filter_upwards [strSum_strOfZ_ae hρ hν G, hzf] with p a b
      exact a.trans b
    have h1 := hSf (strOfZ c mZ ρb γ ν hν G) f hf hT₀f
    have h2 := (Masked.isFarMask_iff R ν μ δ Scut Sf').1 hSf' G f hf hzf
    exact (farX_ae hν Sf G).trans (h1.trans h2.symm)
  have hXS : ∀ G : Zsp c mZ ρb, farX c mZ ρb γ ν hν Sf G = Sf' G := by
    intro G
    have hcl : G ∈ closure {H : Zsp c mZ ρb |
        ∃ f : Chart → Ten3, IsBoxTensor f ∧ zsum H =ᵐ[ageμ c (-1 / 2)] f} := by
      rw [Metric.mem_closure_iff]
      intro η hη
      obtain ⟨G', hG', hn⟩ := hD c mZ ρb hc hmZ hρ G η hη
      exact ⟨G', hG', by rw [dist_eq_norm]; exact hn⟩
    have hclosed : IsClosed {H : Zsp c mZ ρb | farX c mZ ρb γ ν hν Sf H = Sf' H} :=
      isClosed_eq (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
    exact closure_minimal (fun H hH => hbox H hH) hclosed hcl
  -- the zero-sum correction
  have hG : ∀ᵐ p ∂(ageμ c (-1 / 2)), strSum (T - strOfZ c mZ ρb γ ν hν F) p = 0 := by
    filter_upwards [strSum_sub_ae hρ T (strOfZ c mZ ρb γ ν hν F), hTF,
      strSum_strOfZ_ae hρ hν F] with p e h1 h2
    rw [e, h1, h2, sub_self]
  have hz := sf_zero_ae Sf hSf (T - strOfZ c mZ ρb γ ν hν F) hG
  have hd : Sf T - Sf (strOfZ c mZ ρb γ ν hν F) = Sf (T - strOfZ c mZ ρb γ ν hν F) :=
    (map_sub Sf T (strOfZ c mZ ρb γ ν hν F)).symm
  have hc1 : ((Sf (T - strOfZ c mZ ρb γ ν hν F)) : Chart → Merid) =ᵐ[ageμ c (-3 / 2)]
      ((Sf T : Chart → Merid) - (Sf (strOfZ c mZ ρb γ ν hν F) : Chart → Merid)) := by
    rw [← hd]
    have h := Lp.coeFn_sub (Sf T) (Sf (strOfZ c mZ ρb γ ν hν F))
    rw [ae_bodyMeasure] at h
    exact h
  have key1 : (Sf T : Chart → Merid) =ᵐ[ageμ c (-3 / 2)]
      (Sf (strOfZ c mZ ρb γ ν hν F) : Chart → Merid) := by
    filter_upwards [hc1, hz] with p h1 h2
    simp only [Pi.sub_apply, Pi.zero_apply] at h1 h2
    have h3 : (Sf T : Chart → Merid) p - (Sf (strOfZ c mZ ρb γ ν hν F) : Chart → Merid) p = 0 := by
      rw [← h1]
      exact h2
    exact sub_eq_zero.mp h3
  have h3 : (farX c mZ ρb γ ν hν Sf F : Chart → Merid) =ᵐ[ageμ c (-3 / 2)]
      (Sf' F : Chart → Merid) := by
    rw [hXS F]
  exact key1.trans ((farX_ae hν Sf F).symm.trans h3)

end UnforcedLeray.Short.PartIIIb.NearInst
