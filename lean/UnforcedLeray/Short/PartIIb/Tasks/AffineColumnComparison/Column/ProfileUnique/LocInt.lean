import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_5
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.CellStream.HrBox

/-!
# Part II-b, task `PartII-b:G4/3/5/2` (`ProfileLocInt`): local integrability of `√s b_j` on `s > 0`

Source of record: `the November 2 reference manuscript`, SP 1902-1906.
Model: `DivLocInt` (`Tasks/GradLapNvC/DivVanish/LocInt.lean`).

Proof. Let `k ⊆ {s > 0}` be compact, with `s`-infimum `a > 0`, and `k ⊆ B = [a, M] × [-M, M]²`.
On `B`, `√s` is continuous and `b ∈ H_p` is integrable on boxes (`hrBoxIntegrable`, `p = bgp > 1`),
so `√s · b_j` is integrable on `B`, hence on `k`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

namespace ProfileLocHelp

/-- Box integrability of `√s · b_i` for `b ∈ H_p` (`p = bgp`) on a box with `σ > 0`. -/
theorem sqrt_mul_integrableOn {c : ℝ} {b : CProf} (hc : 0 < c) (hb : InHr c bgp b)
    (σ H R L : ℝ) (hσ : 0 < σ) (i : Fin 2) :
    IntegrableOn (fun x : Coord => ((Real.sqrt x.1 : ℝ) : ℂ) * b x i)
      (Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-L) L)) volume := by
  have hbgp : (1 : ℝ) < bgp := by unfold bgp; norm_num
  have h1 := hrBoxIntegrable c bgp b hc hbgp hb σ H R L hσ i
  have hK : IsCompact (Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-L) L)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hcont : ContinuousOn (fun x : Coord => ((Real.sqrt x.1 : ℝ) : ℂ))
      (Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-L) L)) :=
    (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp continuous_fst)).continuousOn
  exact (h1.mul_continuousOn hcont hK).congr_fun (fun x _ => mul_comm _ _) hK.measurableSet

end ProfileLocHelp

open ProfileLocHelp in
/-- **Leaf `PartII-b:G4/3/5/2`** (SP 1902-1906): `√s b_j` is locally integrable on `s > 0`. -/
theorem profileLocInt : UnforcedLeray.Short.IIb.ProfileLocInt := by
  intro c b hc hb j
  rw [locallyIntegrableOn_iff (isOpen_Ioi.prod isOpen_univ).isLocallyClosed]
  intro k hk hkc
  rcases k.eq_empty_or_nonempty with rfl | hne
  · exact integrableOn_empty
  obtain ⟨M, hM⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Coord)).1 hkc.isBounded
  have hP : IsCompact (Prod.fst '' k) := hkc.image continuous_fst
  have hPne : (Prod.fst '' k).Nonempty := hne.image _
  obtain ⟨x0, hx0k, hx0⟩ := hP.sInf_mem hPne
  have hapos : 0 < sInf (Prod.fst '' k) := by
    rw [← hx0]
    exact (hk hx0k).1
  have hlow : ∀ x ∈ k, sInf (Prod.fst '' k) ≤ x.1 :=
    fun x hx => csInf_le hP.bddBelow ⟨x, hx, rfl⟩
  have hup : ∀ x ∈ k, ‖x‖ ≤ M := fun x hx => by
    have := hM hx
    rwa [mem_closedBall_zero_iff] at this
  have hsub : k ⊆ Icc (sInf (Prod.fst '' k)) M ×ˢ (Icc (-M) M ×ˢ Icc (-M) M) := by
    intro x hx
    have h1 : ‖x.1‖ ≤ M := (norm_fst_le x).trans (hup x hx)
    have h2 : ‖x.2.1‖ ≤ M := (norm_fst_le x.2).trans ((norm_snd_le x).trans (hup x hx))
    have h3 : ‖x.2.2‖ ≤ M := (norm_snd_le x.2).trans ((norm_snd_le x).trans (hup x hx))
    rw [Real.norm_eq_abs] at h1 h2 h3
    simp only [mem_prod, mem_Icc]
    exact ⟨⟨hlow x hx, (le_abs_self _).trans h1⟩, abs_le.1 h2, abs_le.1 h3⟩
  have hB := sqrt_mul_integrableOn hc hb (sInf (Prod.fst '' k)) M M M hapos j
  exact hB.mono_set hsub

end UnforcedLeray.Short.IIb
