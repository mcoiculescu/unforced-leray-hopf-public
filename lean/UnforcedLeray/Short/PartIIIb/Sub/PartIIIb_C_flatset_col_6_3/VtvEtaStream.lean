import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3

/-!
# `η = s^{-μ} ζ` is a stream test (source 4610, 3511-3514)

Smoothness: on `{s > 0}` the factor `s^{-μ}` is smooth; on `{s < s₁}` the product vanishes
identically near each point, so `ContDiff` is local.  Cylinder test: a constant multiple of a
cylinder test is a cylinder test.  Support: the same `s₁ s₂ R` as for `ζ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- A constant multiple of a cylinder test is a cylinder test. -/
theorem vtvCylSmul {c : ℝ} {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ) (a : ℝ) :
    B0579.IsCylTest c (fun x => a * φ x) where
  smooth := contDiff_const.mul hφ.smooth
  periodic x := by simp [hφ.periodic x]
  band := by
    obtain ⟨R, hR⟩ := hφ.band
    exact ⟨R, fun x hx => by simp [hR x hx]⟩

/-- **`η = s^{-μ}ζ` is a stream test.** -/
theorem vtvEtaStream : VtvEtaStream := by
  intro c μ ζ hζ
  obtain ⟨hsm, hcyl, s1, s2, R, hs1, hsupp⟩ := hζ
  refine ⟨?_, fun s => ?_, s1, s2, R, hs1, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : p.1 < s1
    · have hev : ∀ᶠ q : ℝ × (ℝ × ℝ) in 𝓝 p, q.1 < s1 :=
        (continuous_fst.continuousAt (x := p)).eventually_lt continuousAt_const hp
      have hz : (fun q : ℝ × (ℝ × ℝ) => vtvEta μ ζ q.1 q.2) =ᶠ[𝓝 p] fun _ => (0 : ℝ) := by
        filter_upwards [hev] with q hq
        unfold vtvEta
        rw [hsupp q.1 q.2 (Or.inl hq), mul_zero]
      exact (contDiffAt_const).congr_of_eventuallyEq hz
    · have hp0 : p.1 ≠ 0 := (lt_of_lt_of_le hs1 (not_lt.1 hp)).ne'
      have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × (ℝ × ℝ) => q.1 ^ (-μ)) p :=
        ContDiffAt.rpow_const_of_ne contDiff_fst.contDiffAt hp0
      have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × (ℝ × ℝ) => ζ q.1 q.2) p := hsm.contDiffAt
      exact h1.mul h2
  · exact vtvCylSmul (hcyl s) (s ^ (-μ))
  · intro s x h
    unfold vtvEta
    rw [hsupp s x h, mul_zero]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
