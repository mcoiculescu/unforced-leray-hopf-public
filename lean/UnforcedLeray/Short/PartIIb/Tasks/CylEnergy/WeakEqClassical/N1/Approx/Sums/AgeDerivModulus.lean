import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_1_2_1
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N1.Approx.Sums.EtaCutProps
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N1.Approx.Sums.UnifContBand

/-!


Source: `the November 2 reference manuscript`, lines 2074-2105.
The age derivative on `(t₀, t₁)` is the within-derivative of the jointly smooth `φ` on
`[t₀, t₁] × ℝ²` in direction `(1, 0)`, which is continuous up to the closed band.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

namespace TdSums

theorem ageDerivModulus : UnforcedLeray.Short.IIb.TdSums.AgeDerivModulus := by
  intro c t₀ t₁ R φ hc hR hφ ε hε
  obtain ⟨C, -, hEc⟩ := (etaCutProps : EtaCutProps)
  obtain ⟨hEsm, hEx⟩ := hEc R hR
  rcases lt_or_ge t₀ t₁ with ht | ht
  · have hS : UniqueDiffOn ℝ (Icc t₀ t₁ ×ˢ (univ : Set B0579.Plane)) :=
      (uniqueDiffOn_Icc ht).prod uniqueDiffOn_univ
    have hFd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fderivWithin ℝ (fun z : ℝ × B0579.Plane => φ z.1 z.2) (Icc t₀ t₁ ×ˢ univ))
        (Icc t₀ t₁ ×ˢ univ) :=
      hφ.smooth.fderivWithin hS (by simp)
    have hDcont : ContinuousOn (fun z : ℝ × B0579.Plane =>
        fderivWithin ℝ (fun z : ℝ × B0579.Plane => φ z.1 z.2) (Icc t₀ t₁ ×ˢ univ) z (1, 0))
        (Icc t₀ t₁ ×ˢ univ) :=
      hFd.continuousOn.clm_apply continuousOn_const
    have hcontG : ContinuousOn (fun z : ℝ × B0579.Plane =>
        etaCut R z.2 * fderivWithin ℝ (fun z : ℝ × B0579.Plane => φ z.1 z.2)
          (Icc t₀ t₁ ×ˢ univ) z (1, 0)) (Icc t₀ t₁ ×ˢ univ) :=
      ((hEsm.continuous.comp continuous_snd).continuousOn).mul hDcont
    -- the age derivative is the within-derivative in direction `(1, 0)`
    have hderiv : ∀ r ∈ Ioo t₀ t₁, ∀ x : B0579.Plane,
        deriv (fun s => φ s x) r =
          fderivWithin ℝ (fun z : ℝ × B0579.Plane => φ z.1 z.2) (Icc t₀ t₁ ×ˢ univ) (r, x) (1, 0) := by
      intro r hr x
      have hnhds : Icc t₀ t₁ ×ˢ (univ : Set B0579.Plane) ∈ 𝓝 (r, x) :=
        prod_mem_nhds (Icc_mem_nhds hr.1 hr.2) univ_mem
      have hdiff : DifferentiableAt ℝ (fun z : ℝ × B0579.Plane => φ z.1 z.2) (r, x) :=
        ((hφ.smooth.contDiffAt hnhds).differentiableAt (by simp))
      have hfw : fderivWithin ℝ (fun z : ℝ × B0579.Plane => φ z.1 z.2) (Icc t₀ t₁ ×ˢ univ) (r, x)
          = fderiv ℝ (fun z : ℝ × B0579.Plane => φ z.1 z.2) (r, x) :=
        fderivWithin_of_mem_nhds hnhds
      have hγ : HasDerivAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : B0579.Plane)) r :=
        (hasDerivAt_id r).prodMk (hasDerivAt_const r x)
      have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt r hγ
      have h2 : deriv (fun s => φ s x) r =
          fderiv ℝ (fun z : ℝ × B0579.Plane => φ z.1 z.2) (r, x) (1, 0) := hcomp.deriv
      rw [hfw]
      exact h2
    have hper : ∀ r ∈ Ioo t₀ t₁, ∀ x : B0579.Plane,
        etaCut R (x.1 + c, x.2) * fderivWithin ℝ (fun z : ℝ × B0579.Plane => φ z.1 z.2)
          (Icc t₀ t₁ ×ˢ univ) (r, (x.1 + c, x.2)) (1, 0) =
        etaCut R x * fderivWithin ℝ (fun z : ℝ × B0579.Plane => φ z.1 z.2)
          (Icc t₀ t₁ ×ˢ univ) (r, x) (1, 0) := by
      intro r hr x
      have e1 : fderivWithin ℝ (fun z : ℝ × B0579.Plane => φ z.1 z.2) (Icc t₀ t₁ ×ˢ univ)
          (r, (x.1 + c, x.2)) (1, 0) =
          fderivWithin ℝ (fun z : ℝ × B0579.Plane => φ z.1 z.2) (Icc t₀ t₁ ×ˢ univ)
          (r, x) (1, 0) := by
        rw [← hderiv r hr (x.1 + c, x.2), ← hderiv r hr x]
        apply Filter.EventuallyEq.deriv_eq
        exact Filter.eventually_of_mem (Ioo_mem_nhds hr.1 hr.2)
          (fun s hs => hφ.periodic s (Ioo_subset_Icc_self hs) x)
      rw [(hEx x).2.2.2.2.1 (x.1 + c), e1]
    have hband : ∀ r ∈ Ioo t₀ t₁, ∀ x : B0579.Plane, 2 * R ≤ |x.2| →
        etaCut R x * fderivWithin ℝ (fun z : ℝ × B0579.Plane => φ z.1 z.2)
          (Icc t₀ t₁ ×ˢ univ) (r, x) (1, 0) = 0 := by
      intro r _ x hx
      rw [(hEx x).2.2.2.1 hx, zero_mul]
    obtain ⟨δ, hδ, hG⟩ := unifContBand c t₀ t₁ (2 * R) (Ioo t₀ t₁)
      (fun r x => etaCut R x * fderivWithin ℝ (fun z : ℝ × B0579.Plane => φ z.1 z.2)
        (Icc t₀ t₁ ×ˢ univ) (r, x) (1, 0))
      hc (Ioo_subset_Icc_self) hcontG hper hband ε hε
    refine ⟨δ, hδ, fun r hr r' hr' hd x => ?_⟩
    have key := hG r hr r' hr' hd x
    rw [hderiv r hr x, hderiv r' hr' x]
    exact key
  · refine ⟨1, one_pos, fun r hr r' _ _ x => ?_⟩
    exfalso
    linarith [hr.1, hr.2]

end TdSums

end UnforcedLeray.Short.IIb
