import UnforcedLeray.Short.PartIIb.Sub.T12_2_3
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.LerayLift.SlicePeriodicRep

/-!
# Sub-lemma `T12/2/3/2` (`HelmClassExt`): `P` extends to a continuous map on the cell `L^r` classes

Source of record: `the November 2 reference manuscript`, lines 1923-1926.
Target: `UnforcedLeray.Short.IIb.LerayLiftSub.HelmClassExt` (`Sub/T12_2_3.lean`).

Proof: for a class `f`, the periodic representative `R f z = f (redQ c z.1, z.2)` is a.e. equal to `f`
(`AvgRedQId`, proved inline), hence `CylLp` and in `L^r`. Put `Φ f := [P (R f)]`, which is in `L^r` by
the bound `HelmBoundP`. For a `CylLp` field `F`, `R [F] =ᵐ F`, and `HelmLinP` with `a = -1` together with
the bound shows that `P` respects a.e. equality of `CylLp` fields. Lipschitz continuity with constant `C`
follows from `HelmLinP`, `HelmBoundP` and `R f - R g =ᵐ f - g`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

open UnforcedLeray.Short.IIb.LerayLiftSub

namespace UnforcedLeray.Short.IIb

theorem helmClassExt_proof : UnforcedLeray.Short.IIb.LerayLiftSub.HelmClassExt := by
  intro c r C P hc hr hC hB hL
  have := fact_one_le_ofReal hr
  have hr0 : (0 : ℝ) < r := by linarith
  -- the cell reduction `q ↦ redQ c q` is the identity a.e. for `avgμ c` (inlined `AvgRedQId`)
  have hAvg : ∀ᵐ z ∂(UnforcedLeray.Cyl.avgμ c), (redQ c z.1, z.2) = z := by
    have hcpos : ENNReal.ofReal c⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 hc)).ne'
    unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ UnforcedLeray.Cyl.cell
    rw [Measure.ae_ennreal_smul_measure_eq hcpos,
      ae_restrict_iff' (measurableSet_Ico.prod MeasurableSet.univ)]
    refine ae_of_all _ fun z hz => ?_
    have hq : z.1 ∈ Ico (-c / 2) (c / 2) := hz.1
    rw [redQ_of_mem_cell hc hq]
  -- the periodic representative of a class
  obtain ⟨R, hR⟩ : ∃ R : Lp CMerid (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) →
      (ℝ × ℝ → CMerid), ∀ f z, R f z = (f : ℝ × ℝ → CMerid) (redQ c z.1, z.2) :=
    ⟨fun f z => (f : ℝ × ℝ → CMerid) (redQ c z.1, z.2), fun f z => rfl⟩
  have hRae : ∀ f : Lp CMerid (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c),
      R f =ᵐ[UnforcedLeray.Cyl.avgμ c] (f : ℝ × ℝ → CMerid) := by
    intro f
    filter_upwards [hAvg] with z hz
    rw [hR f z, hz]
  have hRper : ∀ f, ∀ z : ℝ × ℝ, R f (z.1 + c, z.2) = R f z := by
    intro f z
    rw [hR, hR, redQ_add_period hc]
  have hRC : ∀ f : Lp CMerid (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c),
      UnforcedLeray.Short.IIb.CylLp c r (R f) := by
    intro f
    refine ⟨hRper f, ?_⟩
    exact (Lp.memLp f).ae_eq (hRae f).symm
  -- linear combinations of `CylLp` fields are `CylLp`
  have hcomb : ∀ F₁ F₂ : ℝ × ℝ → CMerid, UnforcedLeray.Short.IIb.CylLp c r F₁ →
      UnforcedLeray.Short.IIb.CylLp c r F₂ →
      UnforcedLeray.Short.IIb.CylLp c r (F₁ + (-1 : ℂ) • F₂) := by
    intro F₁ F₂ h₁ h₂
    refine ⟨fun z => ?_, h₁.2.add (h₂.2.const_smul (-1 : ℂ))⟩
    simp only [Pi.add_apply, Pi.smul_apply, h₁.1 z, h₂.1 z]
  -- `P` respects a.e. equality of `CylLp` fields
  have hkey : ∀ F₁ F₂ : ℝ × ℝ → CMerid, UnforcedLeray.Short.IIb.CylLp c r F₁ →
      UnforcedLeray.Short.IIb.CylLp c r F₂ → F₁ =ᵐ[UnforcedLeray.Cyl.avgμ c] F₂ →
      P F₁ =ᵐ[UnforcedLeray.Cyl.avgμ c] P F₂ := by
    intro F₁ F₂ h₁ h₂ hF
    have h0 : F₁ + (-1 : ℂ) • F₂ =ᵐ[UnforcedLeray.Cyl.avgμ c] 0 := by
      filter_upwards [hF] with z hz
      simp [hz, neg_one_smul]
    have hn : eLpNorm (F₁ + (-1 : ℂ) • F₂) (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) = 0 := by
      rw [eLpNorm_congr_ae h0, eLpNorm_zero]
    have hG := hcomb F₁ F₂ h₁ h₂
    have hb := (hB _ hG).2
    rw [hn, mul_zero] at hb
    have hPG : eLpNorm (P (F₁ + (-1 : ℂ) • F₂)) (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) = 0 :=
      le_antisymm hb zero_le
    have hPG0 : P (F₁ + (-1 : ℂ) • F₂) =ᵐ[UnforcedLeray.Cyl.avgμ c] 0 :=
      (eLpNorm_eq_zero_iff (hB _ hG).1.1.2.aestronglyMeasurable (ENNReal.ofReal_pos.2 hr0).ne').1 hPG
    filter_upwards [hL F₁ F₂ (-1 : ℂ) h₁ h₂, hPG0] with z h1 h2
    have h3 : (P F₁ + (-1 : ℂ) • P F₂) z = 0 := by
      rw [← h1]
      exact h2
    have h4 : P F₁ z - P F₂ z = 0 := by
      simpa [sub_eq_add_neg] using h3
    exact sub_eq_zero.1 h4
  -- `P ∘ R` takes values in `L^r`
  have hPmem : ∀ f : Lp CMerid (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c),
      MemLp (P (R f)) (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) :=
    fun f => (hB (R f) (hRC f)).1.1.2
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Lp CMerid (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) →
      Lp CMerid (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c),
      ∀ f, (Φ f : ℝ × ℝ → CMerid) =ᵐ[UnforcedLeray.Cyl.avgμ c] P (R f) :=
    ⟨fun f => (hPmem f).toLp (P (R f)), fun f => MemLp.coeFn_toLp (hPmem f)⟩
  refine ⟨Φ, ?_, ?_⟩
  · have hLip : LipschitzWith (Real.toNNReal C) Φ := by
      unfold LipschitzWith
      intro f g
      show edist (Φ f) (Φ g) ≤ ENNReal.ofReal C * edist f g
      rw [Lp.edist_def, Lp.edist_def]
      have hA : (⇑(Φ f) - ⇑(Φ g)) =ᵐ[UnforcedLeray.Cyl.avgμ c] P (R f) - P (R g) := by
        filter_upwards [hΦ f, hΦ g] with z h1 h2
        simp only [Pi.sub_apply, h1, h2]
      have hB' : P (R f) - P (R g) =ᵐ[UnforcedLeray.Cyl.avgμ c] P (R f + (-1 : ℂ) • R g) := by
        filter_upwards [hL (R f) (R g) (-1 : ℂ) (hRC f) (hRC g)] with z hz
        rw [hz]
        simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, neg_one_smul, sub_eq_add_neg]
      have hC' : R f + (-1 : ℂ) • R g =ᵐ[UnforcedLeray.Cyl.avgμ c] (⇑f - ⇑g) := by
        filter_upwards [hRae f, hRae g] with z h1 h2
        simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, h1, h2, neg_one_smul, sub_eq_add_neg]
      calc eLpNorm (⇑(Φ f) - ⇑(Φ g)) (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c)
          = eLpNorm (P (R f) - P (R g)) (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) :=
            eLpNorm_congr_ae hA
        _ = eLpNorm (P (R f + (-1 : ℂ) • R g)) (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) :=
            eLpNorm_congr_ae hB'
        _ ≤ ENNReal.ofReal C * eLpNorm (R f + (-1 : ℂ) • R g) (ENNReal.ofReal r)
              (UnforcedLeray.Cyl.avgμ c) :=
            (hB _ (hcomb _ _ (hRC f) (hRC g))).2
        _ = ENNReal.ofReal C * eLpNorm (⇑f - ⇑g) (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) := by
            rw [eLpNorm_congr_ae hC']
    exact hLip.continuous
  · intro F h
    have hRF : R (h.2.toLp F) =ᵐ[UnforcedLeray.Cyl.avgμ c] F :=
      (hRae _).trans (MemLp.coeFn_toLp h.2)
    exact (hΦ _).trans (hkey (R (h.2.toLp F)) F (hRC _) h hRF)

end UnforcedLeray.Short.IIb
