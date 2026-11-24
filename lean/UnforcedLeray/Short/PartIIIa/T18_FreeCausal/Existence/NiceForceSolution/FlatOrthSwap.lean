import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.FlatOrthSwap.Integ

/-!
# Part III-a, task `PartIII-a:T18/2/4/4`: the swap `FlatOrthSwap` (SP 3427-3440)

`⟨𝒫₀f, Φ⟩ = ⟨f, Φ⟩` for divergence-free `Φ`: if `(b, G)` is a Leray projection of a continuous
`u` and the tested identity holds for `u` with integrable integrand, it holds for `b`.
Source of record: `the November 2 reference manuscript`, lines 3427-3440.
Helpers: `FlatOrthSwap/Calc.lean` (directional derivatives, divergence algebra),
`FlatOrthSwap/Psi.lean` (slice test fields `Ψ¹`, `Ψ²`), `FlatOrthSwap/Integ.lean`
(integrability on `Ioi 0 ×ˢ cell`). No `sorry`, no axioms.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

open UnforcedLeray.Short.IIIa.FOS

theorem flatOrthSwap : FlatOrthSwap := by
  intro c ν μ hc F u b G hucont hL Φ hΦ hint hint0
  obtain ⟨s1, s2, R, hs1, hsupp⟩ := hΦ.support
  obtain ⟨S2, hs12, hsupp'⟩ : ∃ S2 : ℝ, s1 < S2 ∧
      ∀ s x i, (s < s1 ∨ S2 < s ∨ R < |x.2|) → Φ s x i = 0 := by
    refine ⟨max s2 (s1 + 1), lt_of_lt_of_le (lt_add_one s1) (le_max_right _ _), ?_⟩
    intro s x i h
    apply hsupp s x i
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (lt_of_le_of_lt (le_max_left _ _) h))
    · exact Or.inr (Or.inr h)
  have hG : ∀ i, ContDiff ℝ ∞ (gI Φ i) := fun i => hΦ.smooth i
  have hSm : MeasurableSet (Ioi (0 : ℝ) ×ˢ B0579.cell c) :=
    measurableSet_Ioi.prod (B0579.measurableSet_cell c)
  have hQfin := volume_Qset_ne_top s1 S2 c R
  -- energy of `b` on the finite-measure box
  have hEfin : ∫⁻ p in Qset s1 S2 c R, ENNReal.ofReal (vnorm2 (b p) ^ 2) < ⊤ := by
    have hm1 := lintegral_mono_set (μ := volume)
      (f := fun p => ENNReal.ofReal (vnorm2 (b p) ^ 2)) (Qset_subset_energy s1 S2 c R)
    have hm2 : ∫⁻ p in Icc s1 S2 ×ˢ B0579.cell c, ENNReal.ofReal (vnorm2 (b p) ^ 2) ≤
        ∫⁻ p in Icc s1 S2 ×ˢ B0579.cell c,
          ENNReal.ofReal (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) :=
      lintegral_mono fun p => ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (sq_nonneg _))
    exact lt_of_le_of_lt (hm1.trans hm2) (hL.energyLoc s1 S2 hs1 hs12)
  have hbQ : ∀ i, IntegrableOn (fun p => b p i) (Qset s1 S2 c R) := fun i =>
    integrableOn_comp_vnorm2 hQfin hL.measurable hEfin i
  have huQ : ∀ i, IntegrableOn (fun p => u p i) (Qset s1 S2 c R) := fun i =>
    ((hucont i).continuousOn.integrableOn_compact (isCompact_Kset s1 S2 c R)).mono_set
      (Qset_subset_Kset s1 S2 c R)
  have hB1Q := integrableOn_B1_Q (ν := ν) (c := c) (s1 := s1) (s2 := S2) (R := R) hs1 hG b u hbQ huQ
  have hB2Q := integrableOn_B2_Q (c := c) (s1 := s1) (s2 := S2) (R := R) hG b u hbQ huQ
  have hmB2Q := integrableOn_mB2_Q (μ := μ) (c := c) (s1 := s1) (s2 := S2) (R := R) hs1 hG b u hB2Q
  -- transfer to `Ioi 0 ×ˢ cell`
  have hB1S : IntegrableOn (fun p => B1 ν Φ b u p) (Ioi (0 : ℝ) ×ˢ B0579.cell c) :=
    integrableOn_S_of_Q hSm hB1Q fun p hp hnot => (B12_zero_off (ν := ν) hsupp' b u hp hnot).1
  have hB2S : IntegrableOn (fun p => B2 Φ b u p) (Ioi (0 : ℝ) ×ˢ B0579.cell c) :=
    integrableOn_S_of_Q hSm hB2Q fun p hp hnot => (B12_zero_off (ν := ν) hsupp' b u hp hnot).2
  have hmB2S : IntegrableOn (fun p => μ / ((p.1 : ℝ) : ℂ) * B2 Φ b u p)
      (Ioi (0 : ℝ) ×ˢ B0579.cell c) :=
    integrableOn_S_of_Q hSm hmB2Q fun p hp hnot => by
      rw [(B12_zero_off (ν := ν) hsupp' b u hp hnot).2, mul_zero]
  have hDS : IntegrableOn (fun p => B1 ν Φ b u p + μ / ((p.1 : ℝ) : ℂ) * B2 Φ b u p)
      (Ioi (0 : ℝ) ×ˢ B0579.cell c) :=
    hB1S.add hmB2S
  -- Fubini on the product `(0,∞) × cell`
  have hprod : (volume.restrict (Ioi (0 : ℝ) ×ˢ B0579.cell c)) =
      (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (B0579.cell c)) := by
    rw [Measure.prod_restrict]
    rfl
  have hB1prod : Integrable (fun p => B1 ν Φ b u p)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (B0579.cell c))) := by
    rw [← hprod]
    exact hB1S
  have hB2prod : Integrable (fun p => B2 Φ b u p)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (B0579.cell c))) := by
    rw [← hprod]
    exact hB2S
  have hslB1 := hB1prod.prod_right_ae
  have hslB2 := hB2prod.prod_right_ae
  -- the slice identities (orthogonality of the Leray projection)
  have horth1 : ∀ s : ℝ, 0 < s → ∫ x in B0579.cell c, B1 ν Φ b u (s, x) = 0 := by
    intro s hs
    exact hL.orth s hs (fun x i => psi1 ν Φ s x i) (psi1_isDivFree hΦ ν s)
  have horth2 : ∀ s : ℝ, 0 < s → ∫ x in B0579.cell c, B2 Φ b u (s, x) = 0 := by
    intro s hs
    exact hL.orth s hs (fun x i => Φ s x i) (psi2_isDivFree hΦ s)
  have hfub : ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
      (B1 ν Φ b u p + μ / ((p.1 : ℝ) : ℂ) * B2 Φ b u p) = 0 := by
    have hDprod : Integrable (fun p => B1 ν Φ b u p + μ / ((p.1 : ℝ) : ℂ) * B2 Φ b u p)
        ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (B0579.cell c))) := by
      rw [← hprod]
      exact hDS
    rw [hprod, integral_prod _ hDprod]
    apply integral_eq_zero_of_ae
    filter_upwards [hslB1, hslB2, ae_restrict_mem measurableSet_Ioi] with s h1 h2 hs
    have hs' : (0 : ℝ) < s := hs
    show ∫ x, (B1 ν Φ b u (s, x) + μ / ((s : ℝ) : ℂ) * B2 Φ b u (s, x))
        ∂(volume.restrict (B0579.cell c)) = 0
    rw [integral_add h1 (h2.const_mul _), integral_const_mul, horth1 s hs', horth2 s hs']
    simp
  refine ⟨?_, ?_⟩
  · exact (hint.add hDS).congr_fun (fun p _ => (flat_diff ν μ F Φ b u p).symm) hSm
  · rw [setIntegral_congr_fun hSm (fun p _ => flat_diff ν μ F Φ b u p),
      integral_add hint hDS, hint0, hfub, add_zero]

end UnforcedLeray.Short.IIIa
