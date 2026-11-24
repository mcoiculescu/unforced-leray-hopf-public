import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_2.Shared

/-!
# `PartIII-b:C/near/2/Unique` (`FreeStressPinUnique`, source 3541-3552), decomposed

`freeStressPinUnique_of (hU : FreeCausalExistsUnique) : FreeStressPinUnique`: from the uniqueness
clause of the free causal solver (`PartIII-a:T18`).  The unconditional target is the assembly
`freeStressPinUnique_of freeCausalExistsUnique` in `Sub/PartIII-b_C_near_2/Unique.lean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Blueprint.Planar

/-- `K = ofReal '' Kset` is admissible. -/
theorem admissible_ofReal {Kset : Set ℝ} (hK : IsCompact Kset) (hKs : Kset ⊆ Ioo 0 (1 / 4)) :
    UnforcedLeray.Short.IIIa.IsAdmissibleK (Complex.ofReal '' Kset) :=
  ⟨hK.image Complex.continuous_ofReal, by
    rintro _ ⟨x, hx, rfl⟩
    have := hKs hx
    exact ⟨by simpa using this.1, by simpa using this.2⟩⟩

theorem velC_eq_of_ae {c : ℝ} {h h' : Hsp c}
    (e : velC (h : Chart → Merid) =ᵐ[ageμ c (-3 / 2)] velC (h' : Chart → Merid)) : h = h' := by
  apply Lp.ext
  filter_upwards [e] with p hp
  ext i
  have := congrFun hp i
  simpa [velC] using this

theorem freeStressPinUnique_of (hU : UnforcedLeray.Short.IIIa.FreeCausalExistsUnique) :
    FreeStressPinUnique := by
  intro P hP Kset hK hKs
  obtain ⟨ν₀, hν₀, hex⟩ := hU P hP _ (admissible_ofReal hK hKs)
  refine ⟨ν₀, hν₀, ?_⟩
  intro ν hν c hc μ hμ mZ ρb hmZ hρb F h h' hF hF'
  have hc' : ν ^ (-2 : ℝ) = c := by
    rw [hc, Real.rpow_neg hν.1.le, Real.rpow_two]
  have hcpos : 0 < c := by rw [hc]; exact inv_pos.2 (pow_pos hν.1 2)
  have hexμ := hex ν hν (μ : ℂ) ⟨μ, hμ, rfl⟩
  simp only [hc'] at hexμ
  obtain ⟨b, G, hbh, hsol⟩ := hF
  obtain ⟨b', G', hbh', hsol'⟩ := hF'
  obtain ⟨Fm, hsym, hmeas, hae, hnorm⟩ := sourceMeasRepFin c mZ ρb P.eigenvalue.re ν hν.1 hcpos
    hmZ hρb ((gainEquiv c mZ ρb P.eigenvalue.re hν.1).symm F)
  rw [ContinuousLinearEquiv.apply_symm_apply] at hae
  have s1 := freeSolAEInvariant c ν (μ : ℂ) hcpos _ Fm b G hsol hae.symm
  have s2 := freeSolAEInvariant c ν (μ : ℂ) hcpos _ Fm b' G' hsol' hae.symm
  obtain ⟨b₁, G₁, -, -, -, huniq⟩ := hexμ Fm hsym hmeas hnorm
  have e1 : b =ᵐ[ageμ c (-3 / 2)] b₁ := (ageMeasureAC c (-3 / 2) hcpos).ae_le (huniq b G s1)
  have e2 : b' =ᵐ[ageμ c (-3 / 2)] b₁ := (ageMeasureAC c (-3 / 2) hcpos).ae_le (huniq b' G' s2)
  apply velC_eq_of_ae
  filter_upwards [hbh, hbh', e1, e2] with p p1 p2 p3 p4
  rw [← p1, ← p2, p3, p4]

end UnforcedLeray.Short.PartIIIb.NearInst
