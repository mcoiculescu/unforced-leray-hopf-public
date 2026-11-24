import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4.WardBin

/-!
# The old thin stress after the outward cutoff (source 4163-4166, 4171)

`χ_o (thinPart T)` has measurable representative `g` vanishing below `6/(5ν)`, dominated by `|T₁|`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem thinPart_fst_eq {c mZ ρb γ ν : ℝ} (T : StrG c mZ ρb γ ν) :
    (thinPart T).fst = T.fst := by
  simp [thinPart]

theorem thinPart_snd_eq {c mZ ρb γ ν : ℝ} (T : StrG c mZ ρb γ ν) :
    (thinPart T).snd = 0 := by
  simp [thinPart]

theorem chiOThinRep : ChiOThinRep := by
  intro c mZ ρb γ ν χ hχ hν T
  classical
  obtain ⟨m, hmeas, hm⟩ : ∃ m : Chart → Ten3, Measurable m ∧
      ((T.fst : Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν)) : Chart → Ten3) =ᵐ[gainZ1Measure c mZ γ ν] m :=
    ⟨_, (Lp.aestronglyMeasurable (T.fst : Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν))).stronglyMeasurable_mk.measurable,
      (Lp.aestronglyMeasurable (T.fst : Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν))).ae_eq_mk⟩
  have hfst' : ((thinPart T).fst : Chart → Ten3) = (T.fst : Chart → Ten3) := by
    rw [thinPart_fst_eq]
  have hA : ((chiOStr c mZ ρb γ ν hχ (thinPart T)).fst : Chart → Ten3) =ᵐ[gainZ1Measure c mZ γ ν]
      cutFun χ ν • ((T.fst : Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν)) : Chart → Ten3) := by
    have h := NearInst.mulBdd_apply_ae (E := Ten3) (μ := gainZ1Measure c mZ γ ν) (cutFun χ ν)
      (cutFun_measurable hχ ν) 1 (cutFun_bound hχ ν) (thinPart T).fst
    rw [hfst'] at h
    exact h
  have hB' : ((NearInst.mulBdd (E := Ten3) (μ := gainHTMeasure c ρb γ ν) (cutFun χ ν)
      (cutFun_measurable hχ ν) 1 (cutFun_bound hχ ν) (thinPart T).snd : Lp (α := Chart) Ten3 2
        (gainHTMeasure c ρb γ ν)) : Chart → Ten3) =ᵐ[gainHTMeasure c ρb γ ν] (0 : Chart → Ten3) := by
    have h := NearInst.mulBdd_apply_ae (E := Ten3) (μ := gainHTMeasure c ρb γ ν) (cutFun χ ν)
      (cutFun_measurable hχ ν) 1 (cutFun_bound hχ ν) (thinPart T).snd
    have h0 : ((thinPart T).snd : Chart → Ten3) =ᵐ[gainHTMeasure c ρb γ ν] (0 : Chart → Ten3) := by
      rw [thinPart_snd_eq]
      exact Lp.coeFn_zero _ _ _
    filter_upwards [h, h0] with p hp1 hp2
    rw [hp1]
    change cutFun χ ν p • ((thinPart T).snd : Chart → Ten3) p = _
    rw [hp2]
    simp
  have hB : ((chiOStr c mZ ρb γ ν hχ (thinPart T)).snd : Chart → Ten3) =ᵐ[gainHTMeasure c ρb γ ν]
      (0 : Chart → Ten3) := hB'
  refine ⟨fun p => if 6 / (5 * ν) ≤ p.1 then cutFun χ ν p • m p else 0, ?_, ?_, ?_, hB, ?_⟩
  · exact Measurable.ite (measurableSet_le measurable_const measurable_fst)
      ((cutFun_measurable hχ ν).smul hmeas) measurable_const
  · intro p hp
    dsimp only
    rw [if_neg (not_le.2 hp)]
  · filter_upwards [hA, hm] with p hp1 hp2
    rw [hp1]
    change cutFun χ ν p • ((T.fst : Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν)) : Chart → Ten3) p = _
    rw [hp2]
    by_cases h : 6 / (5 * ν) ≤ p.1
    · rw [if_pos h]
    · rw [if_neg h]
      have hlt : p.1 < 6 / (5 * ν) := not_le.1 h
      have h2 : p.1 * (5 * ν) < 6 := (lt_div_iff₀ (mul_pos (by norm_num) hν)).1 hlt
      have hz : cutFun χ ν p = 0 := by
        unfold cutFun
        apply hχ.zero
        nlinarith
      rw [hz, zero_smul]
  · filter_upwards [hm] with p hp
    rw [hp]
    by_cases h : 6 / (5 * ν) ≤ p.1
    · rw [if_pos h]
      have h1 : ‖cutFun χ ν p‖ₑ ≤ 1 := by
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_one.2 (cutFun_bound hχ ν p)
      rw [enorm_smul]
      exact mul_le_of_le_one_left (by positivity) h1
    · rw [if_neg h]
      simp
