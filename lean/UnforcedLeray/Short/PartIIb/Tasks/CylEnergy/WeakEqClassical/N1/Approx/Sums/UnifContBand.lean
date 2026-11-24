import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_1_2_1

/-!


Source: `the November 2 reference manuscript`, lines 2074-2105.
Pure topology: uniform continuity on the compact set `[t₀,t₁] × [0,c] × [-R,R]`, plus the
`c`-periodicity in `q` to reduce `q` to `[0,c)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

namespace TdSums

/-- **Leaf `/7`: uniform continuity in age on a band.** -/
theorem unifContBand : UnforcedLeray.Short.IIb.TdSums.UnifContBand := by
  intro c t₀ t₁ R I G hc hI hG hP hB ε hε
  have hSc : IsCompact (Icc t₀ t₁ ×ˢ (Icc (0 : ℝ) c ×ˢ Icc (-R) R)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hSsub : Icc t₀ t₁ ×ˢ (Icc (0 : ℝ) c ×ˢ Icc (-R) R) ⊆ Icc t₀ t₁ ×ˢ (univ : Set B0579.Plane) :=
    fun z hz => ⟨hz.1, mem_univ _⟩
  have hFc : ContinuousOn (fun z : ℝ × B0579.Plane => G z.1 z.2)
      (Icc t₀ t₁ ×ˢ (Icc (0 : ℝ) c ×ˢ Icc (-R) R)) := hG.mono hSsub
  have hUC := hSc.uniformContinuousOn_of_continuous hFc
  obtain ⟨δ₀, hδ₀, hδ⟩ := Metric.uniformContinuousOn_iff.mp hUC ε hε
  -- periodicity of the shifted-by-integer-multiples form
  have hper : ∀ r ∈ I, ∀ (v : ℝ) (n : ℤ) (u : ℝ), G r (u + (n : ℝ) * c, v) = G r (u, v) := by
    intro r hr v n
    induction n using Int.induction_on with
    | zero => intro u; simp
    | succ i ih =>
        intro u
        have e : u + (((i : ℤ) + 1 : ℤ) : ℝ) * c = (u + ((i : ℤ) : ℝ) * c) + c := by
          push_cast
          ring
        have p : G r ((u + ((i : ℤ) : ℝ) * c) + c, v) = G r (u + ((i : ℤ) : ℝ) * c, v) :=
          hP r hr (u + ((i : ℤ) : ℝ) * c, v)
        rw [e, p, ih u]
    | pred i ih =>
        intro u
        have e : u + ((-(i : ℤ) - 1 : ℤ) : ℝ) * c + c = u + ((-(i : ℤ) : ℤ) : ℝ) * c := by
          push_cast
          ring
        have p : G r (u + ((-(i : ℤ) - 1 : ℤ) : ℝ) * c + c, v) =
            G r (u + ((-(i : ℤ) - 1 : ℤ) : ℝ) * c, v) :=
          hP r hr (u + ((-(i : ℤ) - 1 : ℤ) : ℝ) * c, v)
        rw [e] at p
        rw [← p]
        exact ih u
  refine ⟨δ₀ / 2, by linarith, fun r hr r' hr' hrr' x => ?_⟩
  by_cases hxR : R ≤ |x.2|
  · rw [hB r hr x hxR, hB r' hr' x hxR, sub_self, abs_zero]
    exact hε.le
  · push_neg at hxR
    obtain ⟨hy0', hyc'⟩ := toIcoMod_mem_Ico hc 0 x.1
    obtain ⟨y, hy0, hyc, n, hxn⟩ : ∃ y : ℝ, 0 ≤ y ∧ y < c ∧ ∃ n : ℤ, x.1 = y + (n : ℝ) * c := by
      refine ⟨toIcoMod hc 0 x.1, hy0', ?_, toIcoDiv hc 0 x.1, ?_⟩
      · linarith
      · have e := toIcoMod_add_toIcoDiv_zsmul hc 0 x.1
        rw [zsmul_eq_mul] at e
        exact e.symm
    obtain ⟨hxa, hxb⟩ := abs_lt.mp hxR
    have hGx : ∀ s ∈ I, G s x = G s (y, x.2) := by
      intro s hs
      calc G s x = G s (x.1, x.2) := rfl
        _ = G s (y + (n : ℝ) * c, x.2) := by rw [hxn]
        _ = G s (y, x.2) := hper s hs x.2 n y
    have hmem : ∀ s ∈ I, (s, (y, x.2)) ∈ Icc t₀ t₁ ×ˢ (Icc (0 : ℝ) c ×ˢ Icc (-R) R) := by
      intro s hs
      exact ⟨hI hs, ⟨⟨hy0, hyc.le⟩, ⟨hxa.le, hxb.le⟩⟩⟩
    have hdist : dist (r, (y, x.2)) (r', (y, x.2)) < δ₀ := by
      rw [Prod.dist_eq, dist_self, Real.dist_eq]
      exact max_lt (by linarith) hδ₀
    have hcl := hδ (r, (y, x.2)) (hmem r hr) (r', (y, x.2)) (hmem r' hr') hdist
    have h3 : |G r (y, x.2) - G r' (y, x.2)| < ε := by
      simpa [Real.dist_eq] using hcl
    rw [hGx r hr, hGx r' hr']
    exact h3.le

end TdSums

end UnforcedLeray.Short.IIb
