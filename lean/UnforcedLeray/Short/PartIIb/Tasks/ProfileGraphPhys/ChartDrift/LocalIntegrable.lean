import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_6_3
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.CellStream.HrBox

/-!
# Part II-b, task `PartII-b:T10/6/3/2` (`HrLocalIntegrable`): local integrability of `H_r` profiles

Source of record: `the November 2 reference manuscript`, SP 1900-1903 (the measure
`s^{r/2-5/2} ds dq/c dη` of `H_r`), and the coordinate test `ψ` with compact support in `s > 0`.
Target `hrLocalIntegrable_proof : UnforcedLeray.Short.IIb.HrLocalIntegrable` (`Sub/PartII-b_T10_6_3`).

Proof. The support of `ψ` lies in `tsupport ψ`, a compact subset `K` of `{s > 0}`. The set `K` lies
in a box `[σ, M] × [-M, M]²` with `σ > 0` (`σ` the infimum of the `s`-projection of `K`). On this box
`b_i` is Lebesgue integrable (`hrBoxIntegrable`), and multiplying by the continuous bounded `ψ` keeps
integrability (`IntegrableOn.mul_continuousOn`). Since `ψ` vanishes off `K`, the integrand is integrable
on `K` and hence on the whole space.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

open UnforcedLeray.Short.IIb in
theorem hrLocalIntegrable_proof : UnforcedLeray.Short.IIb.HrLocalIntegrable := by
  intro c r b ψ i hc hr hb hψ
  have hsupp : Function.support (fun x => b x i * (ψ x : ℂ)) ⊆ tsupport ψ :=
    fun x hx => subset_tsupport ψ (fun h0 => Function.mem_support.1 hx (by simp [h0]))
  refine (integrableOn_iff_integrable_of_support_subset hsupp).1 ?_
  rcases (tsupport ψ).eq_empty_or_nonempty with hK0 | hne
  · rw [hK0]
    exact integrableOn_empty
  · have hKc : IsCompact (tsupport ψ) := HasCompactSupport.isCompact hψ.compact
    obtain ⟨M, hM⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Coord)).1
      hKc.isBounded
    have hP : IsCompact (Prod.fst '' tsupport ψ) := hKc.image continuous_fst
    have hPne : (Prod.fst '' tsupport ψ).Nonempty := hne.image _
    obtain ⟨x0, hx0k, hx0⟩ := hP.sInf_mem hPne
    have hapos : 0 < sInf (Prod.fst '' tsupport ψ) := by
      rw [← hx0]
      exact (hψ.supp hx0k).1
    have hlow : ∀ x ∈ tsupport ψ, sInf (Prod.fst '' tsupport ψ) ≤ x.1 :=
      fun x hx => csInf_le hP.bddBelow ⟨x, hx, rfl⟩
    have hup : ∀ x ∈ tsupport ψ, ‖x‖ ≤ M := fun x hx => by
      have := hM hx
      rwa [mem_closedBall_zero_iff] at this
    have hsubB : tsupport ψ ⊆
        Icc (sInf (Prod.fst '' tsupport ψ)) M ×ˢ (Icc (-M) M ×ˢ Icc (-M) M) := by
      intro x hx
      have h1 : ‖x.1‖ ≤ M := (norm_fst_le x).trans (hup x hx)
      have h2 : ‖x.2.1‖ ≤ M := (norm_fst_le x.2).trans ((norm_snd_le x).trans (hup x hx))
      have h3 : ‖x.2.2‖ ≤ M := (norm_snd_le x.2).trans ((norm_snd_le x).trans (hup x hx))
      rw [Real.norm_eq_abs] at h1 h2 h3
      simp only [mem_prod, mem_Icc]
      exact ⟨⟨hlow x hx, (le_abs_self _).trans h1⟩, abs_le.1 h2, abs_le.1 h3⟩
    have I := hrBoxIntegrable c r b hc hr hb (sInf (Prod.fst '' tsupport ψ)) M M M hapos i
    have hK : IsCompact (Icc (sInf (Prod.fst '' tsupport ψ)) M ×ˢ (Icc (-M) M ×ˢ Icc (-M) M)) :=
      isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
    have hcont : ContinuousOn (fun x : Coord => (ψ x : ℂ))
        (Icc (sInf (Prod.fst '' tsupport ψ)) M ×ˢ (Icc (-M) M ×ˢ Icc (-M) M)) :=
      (Complex.continuous_ofReal.comp hψ.smooth.continuous).continuousOn
    have h2 := I.mul_continuousOn hcont hK
    exact h2.mono_set hsubB
