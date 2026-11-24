import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Sub.PartIIIb_C_near_delta_8_2_3
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.FlatFreeGain.hh7.AEInvariant
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.FlatFreeGain.hh7.SourceMeasRep
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.FlatFreeGain.hh7.AgeMeasureAC

/-!
# Uniqueness of the free stress operator (item `PartIII-b:C/near/delta/8/2/3`)

Source of record `the November 2 reference manuscript`,
3427-3440 (uniqueness of the causal zero-entrance energy solution).

Two operators `S0 S1 : Z → H` with `IsFreeStress` agree on every gain image `𝖦X`, because the
symmetric measurable representative `Fm` of the source (`sourceMeasRep`) has a unique causal
solution a.e. (`FreeCausalExistsUnique`), invariant under a.e. change of source
(`freeSolAEInvariant`), and a.e. unique in the age measure (`ageMeasureAC`). Since `𝖦` is invertible,
every `F ∈ Z` is a gain image, which gives `S0 = S1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.Blueprint.Planar

theorem freeStressUnique : FreeStressUnique := by
  intro hU P hP Kset hK hKs
  have hadm : UnforcedLeray.Short.IIIa.IsAdmissibleK (Complex.ofReal '' Kset) :=
    ⟨hK.image Complex.continuous_ofReal, by
      rintro _ ⟨x, hx, rfl⟩
      have := hKs hx
      exact ⟨by simpa using this.1, by simpa using this.2⟩⟩
  obtain ⟨ν₀, hν₀, hex⟩ := hU P hP _ hadm
  refine ⟨ν₀, hν₀, ?_⟩
  intro ν c μ mZ ρb hν hνν₀ hc hμ hmZ hρ hρ1 S0 S1 hS0 hS1
  have hc' : ν ^ (-2 : ℝ) = c := by
    rw [hc, Real.rpow_neg hν.le, Real.rpow_two]
  have hcpos : 0 < c := by
    rw [hc]; exact inv_pos.2 (pow_pos hν 2)
  have key : ∀ X : Zsp c mZ ρb,
      S0 (gainEquiv c mZ ρb P.eigenvalue.re hν X) = S1 (gainEquiv c mZ ρb P.eigenvalue.re hν X) := by
    intro X
    obtain ⟨b0, G0, hb0, hsol0⟩ := hS0 (gainEquiv c mZ ρb P.eigenvalue.re hν X)
    obtain ⟨b1, G1, hb1, hsol1⟩ := hS1 (gainEquiv c mZ ρb P.eigenvalue.re hν X)
    obtain ⟨Fm, hsym, hmeas, hae, hnorm⟩ :=
      sourceMeasRep c mZ ρb P.eigenvalue.re ν hν hcpos hmZ hρ hρ1 X
    have hexμ := hex ν ⟨hν, hνν₀⟩ (μ : ℂ) ⟨μ, hμ, rfl⟩
    simp only [hc'] at hexμ
    have hfin : UnforcedLeray.Short.IIIa.tCalNorm c
        (UnforcedLeray.Short.IIIa.gainConj P.eigenvalue.re ν Fm) < ⊤ :=
      hnorm.trans_lt ENNReal.ofReal_lt_top
    obtain ⟨b₁, G₁, hsol₁, -, -, huniq⟩ := hexμ Fm hsym hmeas hfin
    have hsolA := freeSolAEInvariant c ν (μ : ℂ) hcpos _ Fm b0 G0 hsol0 hae.symm
    have hsolB := freeSolAEInvariant c ν (μ : ℂ) hcpos _ Fm b1 G1 hsol1 hae.symm
    have hb0' : b0 =ᵐ[ageμ c (-3 / 2)] b₁ := (ageMeasureAC c (-3 / 2) hcpos).ae_le (huniq b0 G0 hsolA)
    have hb1' : b1 =ᵐ[ageμ c (-3 / 2)] b₁ := (ageMeasureAC c (-3 / 2) hcpos).ae_le (huniq b1 G1 hsolB)
    have hvel := (hb0.symm.trans (hb0'.trans hb1'.symm)).trans hb1
    apply Lp.ext
    filter_upwards [hvel] with p hp
    ext i
    have h2 := congrFun hp i
    simp only [velC] at h2
    exact Complex.ofReal_injective h2
  apply ContinuousLinearMap.ext
  intro F
  have h := key ((gainEquiv c mZ ρb P.eigenvalue.re hν).symm F)
  rwa [ContinuousLinearEquiv.apply_symm_apply] at h

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
