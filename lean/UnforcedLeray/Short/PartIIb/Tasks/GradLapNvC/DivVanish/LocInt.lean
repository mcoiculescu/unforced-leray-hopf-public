import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T09_4
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.CellStream.HrBox

/-!
# Part II-b, task `PartII-b:T09/4/3` (`DivLocInt`): local integrability of `gDiv` on `s > 0`

Source of record: `the November 2 reference manuscript`, SP 1639-1668, 1912-1916.
Target `divLocInt_proof : UnforcedLeray.Short.IIb.DivLocInt` (`Sub/T09.lean` via `Sub/PartII-b_T09_4`).

Proof. Let `k ⊆ {s > 0}` be compact. Its `s`-infimum `a` is positive and `k` lies in the box
`B = [a, M] × [-M, M]²`. On `B`,
`gDiv = s Qb₀ + ε s b₀ + s Eb₁`, and each summand is integrable:
* `s Qb₀ = √s · (√s Qb₀) = √s · (sqrtS Qb)₀`, with `sqrtS Qb ∈ H_r` integrable on boxes
  (`hrBoxIntegrable`), and `√s` continuous on `B`;
* `s b₀` and `s Eb₁` are handled the same way (`s` continuous on `B`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

namespace DivLocIntHelp

/-- Box integrability of `s · b_i` for an `H_r` profile on a box with `σ > 0`. -/
theorem mul_s_integrableOn {c r : ℝ} {b : CProf} (hc : 0 < c) (hr : 1 < r) (hb : InHr c r b)
    (σ H R L : ℝ) (hσ : 0 < σ) (i : Fin 2) :
    IntegrableOn (fun x : Coord => ((x.1 : ℝ) : ℂ) * b x i)
      (Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-L) L)) volume := by
  have h1 := hrBoxIntegrable c r b hc hr hb σ H R L hσ i
  have hK : IsCompact (Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-L) L)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hcont : ContinuousOn (fun x : Coord => ((x.1 : ℝ) : ℂ))
      (Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-L) L)) :=
    (Complex.continuous_ofReal.comp continuous_fst).continuousOn
  have h2 := h1.mul_continuousOn hcont hK
  exact h2.congr_fun (fun x _ => mul_comm _ _) hK.measurableSet

/-- Box integrability of `s · f_i` for `f` with `√s f ∈ H_r`, on a box with `σ > 0`. -/
theorem mul_sqrt_integrableOn {c r : ℝ} {f : CProf} (hc : 0 < c) (hr : 1 < r)
    (hf : InHr c r (sqrtS f)) (σ H R L : ℝ) (hσ : 0 < σ) (i : Fin 2) :
    IntegrableOn (fun x : Coord => ((x.1 : ℝ) : ℂ) * f x i)
      (Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-L) L)) volume := by
  have h1 := hrBoxIntegrable c r (sqrtS f) hc hr hf σ H R L hσ i
  have hK : IsCompact (Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-L) L)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hcont : ContinuousOn (fun x : Coord => ((Real.sqrt x.1 : ℝ) : ℂ))
      (Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-L) L)) :=
    (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp continuous_fst)).continuousOn
  have h2 := h1.mul_continuousOn hcont hK
  refine h2.congr_fun (fun x hx => ?_) hK.measurableSet
  have hs : 0 ≤ x.1 := hσ.le.trans hx.1.1
  have hm : ((Real.sqrt x.1 : ℝ) : ℂ) * ((Real.sqrt x.1 : ℝ) : ℂ) = ((x.1 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hs]
  simp only [sqrtS, PiLp.smul_apply, smul_eq_mul]
  linear_combination (f x i) * hm

end DivLocIntHelp

open DivLocIntHelp in
/-- **Leaf `T09/4/3`** (SP 1912-1918): `gDiv` is locally integrable on `s > 0`. -/
theorem divLocInt_proof : UnforcedLeray.Short.IIb.DivLocInt := by
  intro c ε r b Qb Eb hc hε hr hd
  have hr1 : (1 : ℝ) < r := by linarith
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
  have hBmeas : MeasurableSet (Icc (sInf (Prod.fst '' k)) M ×ˢ (Icc (-M) M ×ˢ Icc (-M) M)) :=
    measurableSet_Icc.prod (measurableSet_Icc.prod measurableSet_Icc)
  have I1 := mul_sqrt_integrableOn hc hr1 hd.inQ (sInf (Prod.fst '' k)) M M M hapos 0
  have I2 := mul_s_integrableOn hc hr1 hd.inHr (sInf (Prod.fst '' k)) M M M hapos 0
  have I3 := mul_sqrt_integrableOn hc hr1 hd.inE (sInf (Prod.fst '' k)) M M M hapos 1
  have I := (I1.add (I2.const_mul (ε : ℂ))).add I3
  have hB : IntegrableOn (gDiv ε b Qb Eb)
      (Icc (sInf (Prod.fst '' k)) M ×ˢ (Icc (-M) M ×ˢ Icc (-M) M)) volume := by
    refine I.congr_fun (fun x _ => ?_) hBmeas
    simp only [gDiv, Pi.add_apply]
    ring
  exact hB.mono_set hsub
