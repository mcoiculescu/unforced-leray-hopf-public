import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_4_2
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylHeatMaxReg.Limit.IBP

/-!
# Part II-b, task `PartII-b:T13/1/4/2/6` (`ChmWeakEq`): weak derivatives of smooth functions

Source `the November 2 reference manuscript` lines 1933-1935 and 1377-1424.
For smooth `u` and `L^r` data `g` the weak identities against space-time tests give `g = ∂u`
(resp. `g = ∂_i∂_j u`) almost everywhere: integration by parts (`chmIBP`) turns the weak identity
into `∫ (g - ∂u) φ = 0` for all smooth compactly supported real `φ`, and the fundamental lemma
`ae_eq_of_integral_contDiff_smul_eq` (with `g` locally integrable since `g ∈ L^r`, `r ≥ 1`) gives
equality almost everywhere.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

theorem chmWeakEq : UnforcedLeray.Short.IIb.ChmWeakEq := by
  intro r hr u hu
  have comm : ∀ F : Coord → ℂ, ∀ φ : Coord → ℝ,
      ∫ x, (φ x : ℂ) * F x = ∫ x, F x * (φ x : ℂ) := fun F φ =>
    integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
  refine ⟨fun g hgm hgfin hg => ?_, fun ν hν i j g hgm hgfin hg => ?_⟩
  · have hMem : MemLp g (ENNReal.ofReal r) volume := ⟨hgm, hgfin⟩
    have hLg : LocallyIntegrable g volume :=
      hMem.locallyIntegrable (ENNReal.one_le_ofReal.2 hr.le)
    have hLu : LocallyIntegrable (cdv 0 u) volume :=
      (chmIBP_cdv_contDiff u hu 0).continuous.locallyIntegrable
    refine ae_eq_of_integral_contDiff_smul_eq hLg hLu (fun φ hφs hφc => ?_)
    have hT : IsSTTestCoord φ := ⟨hφs, hφc⟩
    have h1 := (chmIBP u hu φ hT).1
    have h2 := hg φ hT
    have key : ∫ x, g x * (φ x : ℂ) = ∫ x, cdv 0 u x * (φ x : ℂ) :=
      (neg_inj.1 (h1.symm.trans h2)).symm
    simp only [Complex.real_smul]
    rw [comm g φ, comm (cdv 0 u) φ]
    exact key
  · have hνc : (ν : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
    have hMem : MemLp (fun x => (ν : ℂ) * g x) (ENNReal.ofReal r) volume :=
      ⟨hgm.const_mul _, hgfin⟩
    have hg' : MemLp g (ENNReal.ofReal r) volume := by
      have h := hMem.const_mul ((ν : ℂ)⁻¹)
      have e : (fun x => (ν : ℂ)⁻¹ * ((ν : ℂ) * g x)) = g := by
        funext x
        rw [← mul_assoc, inv_mul_cancel₀ hνc, one_mul]
      rwa [e] at h
    have hLg : LocallyIntegrable g volume :=
      hg'.locallyIntegrable (ENNReal.one_le_ofReal.2 hr.le)
    have hLu : LocallyIntegrable (cdv i.succ (cdv j.succ u)) volume :=
      (chmIBP_cdv_contDiff (cdv j.succ u) (chmIBP_cdv_contDiff u hu j.succ) i.succ).continuous.locallyIntegrable
    refine ae_eq_of_integral_contDiff_smul_eq hLg hLu (fun φ hφs hφc => ?_)
    have hT : IsSTTestCoord φ := ⟨hφs, hφc⟩
    have h1 := (chmIBP u hu φ hT).2 i j
    have h2 := hg φ hT
    have key : ∫ x, g x * (φ x : ℂ) = ∫ x, cdv i.succ (cdv j.succ u) x * (φ x : ℂ) :=
      h2.symm.trans h1
    simp only [Complex.real_smul]
    rw [comm g φ, comm (cdv i.succ (cdv j.succ u)) φ]
    exact key

end UnforcedLeray.Short.IIb
