import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_5_2_2
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Bounded

/-!
# `PartIII-b:C/grad/3/5/2/2` (jets of `A^y`): `AyJets` for every admissible `A`

Source `the November 2 reference manuscript`
4974-4980, 5063-5079.  `A^y = χ(ν·) A` is `C^6` on `(0,∞)` and every entry used here is `C^2`
on the open set `{s>0}`.  On a bounded open set `U` with `closure U ⊆ {s>0}` the derivatives of
order `≤ 2` of a `C^2` function are bounded (compactness of `closure U`).  The meridional
product `merApply (A^y) (x_j)` is affine in `j`: `x_j = (x_0) - j c e_1` with `c = ν⁻²`, so its
jets are bounded by `M (1 + |j|)`.  Proved: `ayJets`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- A `C^2` function on `{s>0}` has derivatives of order `≤ 2` bounded on each open `U` whose
closure is a compact subset of `{s>0}`. -/
lemma ajb_bound {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Chart → E)
    (U : Set Chart) (hUo : IsOpen U) (hcl : closure U ⊆ {p : Chart | 0 < p.1})
    (hbd : Bornology.IsBounded (closure U))
    (hf : ContDiffOn ℝ 2 f {p : Chart | 0 < p.1}) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k ≤ 2, ∀ p ∈ U, ‖iteratedFDerivWithin ℝ k f U p‖ ≤ M := by
  have hSo : IsOpen {p : Chart | 0 < p.1} := psc2_isOpen_pos
  have hUS : U ⊆ {p : Chart | 0 < p.1} := fun p hp => hcl (subset_closure hp)
  have hK : IsCompact (closure U) := Metric.isCompact_of_isClosed_isBounded isClosed_closure hbd
  have hg : ContinuousOn (fun x => ∑ k ∈ Finset.range 3,
      ‖iteratedFDerivWithin ℝ k f {p : Chart | 0 < p.1} x‖) {p : Chart | 0 < p.1} := by
    apply continuousOn_finsetSum
    intro k hk
    have hk2 : k ≤ 2 := by
      have := Finset.mem_range.1 hk
      omega
    have hk2' : (k : WithTop ℕ∞) ≤ 2 := by exact_mod_cast hk2
    exact (hf.continuousOn_iteratedFDerivWithin hk2' hSo.uniqueDiffOn).norm
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hg.mono hcl)
  refine ⟨|C|, abs_nonneg C, ?_⟩
  intro k hk p hp
  have hpS : p ∈ {p : Chart | 0 < p.1} := hUS hp
  have hkS : k ∈ Finset.range 3 := Finset.mem_range.2 (by omega)
  have e1 : iteratedFDerivWithin ℝ k f U p = iteratedFDerivWithin ℝ k f {p : Chart | 0 < p.1} p := by
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) k hUo hp,
      iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) k hSo hpS]
  rw [e1]
  have h1 : ‖iteratedFDerivWithin ℝ k f {p : Chart | 0 < p.1} p‖ ≤
      ∑ i ∈ Finset.range 3, ‖iteratedFDerivWithin ℝ i f {p : Chart | 0 < p.1} p‖ :=
    Finset.single_le_sum (f := fun i => ‖iteratedFDerivWithin ℝ i f {p : Chart | 0 < p.1} p‖)
      (fun i _ => norm_nonneg _) hkS
  have h2 := hC p (subset_closure hp)
  have hsum0 : 0 ≤ ∑ i ∈ Finset.range 3, ‖iteratedFDerivWithin ℝ i f {p : Chart | 0 < p.1} p‖ :=
    Finset.sum_nonneg (fun i _ => norm_nonneg _)
  rw [Real.norm_of_nonneg hsum0] at h2
  linarith [le_abs_self C]

theorem ayJets (as : ℝ) : AyJets as := by
  intro χ hχ ν hν A hA U hUo hUc hcl hbd
  have hUpos : U ⊆ {p : Chart | 0 < p.1} := fun p hp => hcl (subset_closure hp)
  have hc0 : 0 ≤ cOf ν := by
    unfold cOf
    positivity
  have hA6 : ContDiffOn ℝ 6 (Ay ν χ A) (Ioi 0) := psc2_Ay_contDiffOn ν χ hχ A hA.smooth
  have hAy2 : ContDiffOn ℝ 2 (fun p : Chart => Ay ν χ A p.1) {p : Chart | 0 < p.1} :=
    (hA6.of_le (by norm_num)).comp contDiff_fst.contDiffOn (fun p hp => hp)
  have hT : ContDiffOn ℝ 2 (fun p : Chart => merTrace (Ay ν χ A p.1)) {p : Chart | 0 < p.1} := by
    unfold merTrace
    exact (psc2_entry_contDiffOn (fun p : Chart => Ay ν χ A p.1) hAy2 0 0).add
      (psc2_entry_contDiffOn (fun p : Chart => Ay ν χ A p.1) hAy2 2 2)
  have hW0 : ContDiffOn ℝ 2 (fun p : Chart => merApply (Ay ν χ A p.1) p.2)
      {p : Chart | 0 < p.1} :=
    psc2_merApply_contDiffOn (fun p : Chart => Ay ν χ A p.1) (fun p : Chart => p.2) hAy2
      contDiff_snd.contDiffOn
  have hV : ContDiffOn ℝ 2
      (fun p : Chart => merApply (Ay ν χ A p.1) ((1 : ℝ), (0 : ℝ))) {p : Chart | 0 < p.1} :=
    psc2_merApply_contDiffOn (fun p : Chart => Ay ν χ A p.1)
      (fun _ : Chart => ((1 : ℝ), (0 : ℝ))) hAy2 contDiffOn_const
  obtain ⟨Mt, hMt0, hMt⟩ := ajb_bound (fun p : Chart => merTrace (Ay ν χ A p.1)) U hUo hcl hbd hT
  obtain ⟨M0, hM00, hM0⟩ :=
    ajb_bound (fun p : Chart => merApply (Ay ν χ A p.1) p.2) U hUo hcl hbd hW0
  obtain ⟨MV, hMV0, hMV⟩ :=
    ajb_bound (fun p : Chart => merApply (Ay ν χ A p.1) ((1 : ℝ), (0 : ℝ))) U hUo hcl hbd hV
  refine ⟨Mt + M0 + cOf ν * MV, by have := mul_nonneg hc0 hMV0; linarith, ?_⟩
  intro k hk p hp
  have hkN : (k : WithTop ℕ∞) ≤ 2 := by exact_mod_cast hk
  refine ⟨?_, ?_⟩
  · have := hMt k hk p hp
    have := mul_nonneg hc0 hMV0
    linarith
  · intro j
    have hEq : EqOn (fun q : Chart => merApply (Ay ν χ A q.1) (xj ν j q.2))
        (fun q : Chart => merApply (Ay ν χ A q.1) q.2
          + (-((j : ℝ) * cOf ν)) • merApply (Ay ν χ A q.1) ((1 : ℝ), (0 : ℝ))) U := by
      intro q _
      dsimp only
      refine Prod.ext ?_ ?_ <;>
        simp only [merApply, xj, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
          smul_eq_mul] <;> ring
    rw [iteratedFDerivWithin_congr (𝕜 := ℝ) hEq hp k]
    have hW0U : ContDiffWithinAt ℝ 2 (fun q : Chart => merApply (Ay ν χ A q.1) q.2) U p :=
      (hW0.mono hUpos) p hp
    have hVU : ContDiffWithinAt ℝ 2
        (fun q : Chart => merApply (Ay ν χ A q.1) ((1 : ℝ), (0 : ℝ))) U p :=
      (hV.mono hUpos) p hp
    have h1 : iteratedFDerivWithin ℝ k (fun q : Chart => merApply (Ay ν χ A q.1) q.2
        + (-((j : ℝ) * cOf ν)) • merApply (Ay ν χ A q.1) ((1 : ℝ), (0 : ℝ))) U p
        = iteratedFDerivWithin ℝ k (fun q : Chart => merApply (Ay ν χ A q.1) q.2) U p
          + iteratedFDerivWithin ℝ k (fun q : Chart =>
              (-((j : ℝ) * cOf ν)) • merApply (Ay ν χ A q.1) ((1 : ℝ), (0 : ℝ))) U p :=
      iteratedFDerivWithin_add_apply (hW0U.of_le hkN)
        ((hVU.of_le hkN).const_smul (-((j : ℝ) * cOf ν))) hUo.uniqueDiffOn hp
    have h2 : iteratedFDerivWithin ℝ k (fun q : Chart =>
        (-((j : ℝ) * cOf ν)) • merApply (Ay ν χ A q.1) ((1 : ℝ), (0 : ℝ))) U p
        = (-((j : ℝ) * cOf ν)) • iteratedFDerivWithin ℝ k
          (fun q : Chart => merApply (Ay ν χ A q.1) ((1 : ℝ), (0 : ℝ))) U p :=
      iteratedFDerivWithin_const_smul_apply (𝕜 := ℝ) (a := -((j : ℝ) * cOf ν))
        (hVU.of_le hkN) hUo.uniqueDiffOn hp
    rw [h1, h2]
    have hb1 := hM0 k hk p hp
    have hb2 := hMV k hk p hp
    have hn := norm_add_le (iteratedFDerivWithin ℝ k
        (fun q : Chart => merApply (Ay ν χ A q.1) q.2) U p)
      ((-((j : ℝ) * cOf ν)) • iteratedFDerivWithin ℝ k
        (fun q : Chart => merApply (Ay ν χ A q.1) ((1 : ℝ), (0 : ℝ))) U p)
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_mul, abs_of_nonneg hc0] at hn
    have hJ : 0 ≤ |(j : ℝ)| := abs_nonneg _
    have t1 : |(j : ℝ)| * (cOf ν * ‖iteratedFDerivWithin ℝ k
        (fun q : Chart => merApply (Ay ν χ A q.1) ((1 : ℝ), (0 : ℝ))) U p‖)
        ≤ |(j : ℝ)| * (cOf ν * MV) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb2 hc0) hJ
    have t2 : 0 ≤ (Mt + M0) * |(j : ℝ)| := mul_nonneg (by linarith) hJ
    have t3 : 0 ≤ cOf ν * MV * |(j : ℝ)| := mul_nonneg (mul_nonneg hc0 hMV0) hJ
    have t4 : 0 ≤ M0 * |(j : ℝ)| := mul_nonneg hM00 hJ
    have t5 : 0 ≤ Mt + M0 + cOf ν * MV := by
      have := mul_nonneg hc0 hMV0
      linarith
    nlinarith [t1, t2, t3, t4, t5]

end UnforcedLeray.Short.PartIIIb.Concrete
