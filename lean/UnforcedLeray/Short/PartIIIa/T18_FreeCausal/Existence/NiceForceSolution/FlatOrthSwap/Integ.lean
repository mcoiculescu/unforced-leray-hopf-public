import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.FlatOrthSwap.Psi

/-!
# Helper for `PartIII-a:T18/2/4/4` (`FlatOrthSwap`): integrability on `Ioi 0 ×ˢ cell`

The swap integrand is `Σ_i (b_i - u_i)(Ψ¹_i + (μ/s) Ψ²_i)`. It vanishes off the compact-in-`s`,
`η`-bounded box `Q = [s₁,s₂] × cell ∩ {|η| ≤ R}` (`Qset`), where `b ∈ L¹` by `energyLoc` (finite
measure) and `u`, `Ψ`, `μ/s` are bounded. This file collects those facts.
No `sorry`, no axioms.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.FOS

/-- The compact-in-`s` box `[s₁,s₂] × [-c/2,c/2) × [-R,R]` (support of the swap integrand). -/
def Qset (s1 s2 c R : ℝ) : Set V3 := Icc s1 s2 ×ˢ (Ico (-(c / 2)) (c / 2) ×ˢ Icc (-R) R)

/-- The closed compact box containing `Qset`. -/
def Kset (s1 s2 c R : ℝ) : Set V3 := Icc s1 s2 ×ˢ (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R)

lemma Qset_subset_Kset (s1 s2 c R : ℝ) : Qset s1 s2 c R ⊆ Kset s1 s2 c R :=
  Set.prod_mono subset_rfl (Set.prod_mono Ico_subset_Icc_self subset_rfl)

lemma Qset_subset_S {s1 s2 c R : ℝ} (hs1 : 0 < s1) :
    Qset s1 s2 c R ⊆ Ioi (0 : ℝ) ×ˢ B0579.cell c := by
  intro p hp
  exact ⟨lt_of_lt_of_le hs1 hp.1.1, hp.2.1, Set.mem_univ _⟩

lemma Qset_subset_energy (s1 s2 c R : ℝ) : Qset s1 s2 c R ⊆ Icc s1 s2 ×ˢ B0579.cell c :=
  fun p hp => ⟨hp.1, hp.2.1, Set.mem_univ _⟩

lemma isCompact_Kset (s1 s2 c R : ℝ) : IsCompact (Kset s1 s2 c R) :=
  isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)

lemma volume_Qset_ne_top (s1 s2 c R : ℝ) : volume (Qset s1 s2 c R) ≠ ⊤ :=
  ((measure_mono (Qset_subset_Kset s1 s2 c R)).trans_lt
    (isCompact_Kset s1 s2 c R).measure_lt_top).ne

lemma measurableSet_Qset (s1 s2 c R : ℝ) : MeasurableSet (Qset s1 s2 c R) :=
  measurableSet_Icc.prod (measurableSet_Ico.prod measurableSet_Icc)

lemma compl_Qset {s1 s2 c R : ℝ} {p : V3} (hp : p ∈ Ioi (0 : ℝ) ×ˢ B0579.cell c)
    (hnot : p ∉ Qset s1 s2 c R) : p.1 < s1 ∨ s2 < p.1 ∨ R < |p.2.2| := by
  by_contra hcon
  push_neg at hcon
  apply hnot
  exact ⟨⟨hcon.1, hcon.2.1⟩, hp.2.1, abs_le.1 hcon.2.2⟩

lemma norm_le_vnorm2_fos (a : Fin 2 → ℂ) (i : Fin 2) : ‖a i‖ ≤ vnorm2 a := by
  unfold vnorm2
  have h : ‖a i‖ ^ 2 ≤ ∑ j : Fin 2, ‖a j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖a j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have h2 := Real.abs_le_sqrt h
  rwa [abs_of_nonneg (norm_nonneg _)] at h2

lemma continuous_vnorm2_fos : Continuous vnorm2 := by
  unfold vnorm2
  exact Real.continuous_sqrt.comp
    (continuous_finset_sum _ fun j _ => (continuous_norm.comp (continuous_apply j)).pow 2)

/-- Components of an `L¹`-type `b` on a finite-measure set, from a finite `L²`-type energy. -/
lemma integrableOn_comp_vnorm2 {T : Set V3} (hT : volume T ≠ ⊤) {b : V3 → Fin 2 → ℂ}
    (hbm : ∀ i, Measurable fun p => b p i)
    (hfin : ∫⁻ p in T, ENNReal.ofReal (vnorm2 (b p) ^ 2) < ⊤) (i : Fin 2) :
    IntegrableOn (fun p => b p i) T := by
  have hbmeas : Measurable fun p => b p := measurable_pi_iff.2 hbm
  have hvm : Measurable fun p => vnorm2 (b p) := continuous_vnorm2_fos.measurable.comp hbmeas
  have hv2 : Integrable (fun p => vnorm2 (b p) ^ 2) (volume.restrict T) :=
    ⟨(hvm.pow_const 2).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun p => sq_nonneg _)).2 hfin⟩
  have hone : IntegrableOn (fun _ : V3 => (1 : ℝ)) T := integrableOn_const hT
  refine Integrable.mono' (hone.add hv2) (hbm i).aestronglyMeasurable
    (ae_of_all _ fun p => ?_)
  show ‖b p i‖ ≤ 1 + vnorm2 (b p) ^ 2
  have h1 := norm_le_vnorm2_fos (b p) i
  have h2 : vnorm2 (b p) ≤ 1 + vnorm2 (b p) ^ 2 := by
    nlinarith [sq_nonneg (vnorm2 (b p) - 1 / 2)]
  linarith

/-- Bound of a continuous real function, cast to `ℂ`, on the compact box `Kset`. -/
lemma ae_bound_Qset {g : V3 → ℝ} (hg : Continuous g) (s1 s2 c R : ℝ) :
    ∃ C : ℝ, ∀ᵐ p ∂(volume.restrict (Qset s1 s2 c R)), ‖((g p : ℝ) : ℂ)‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Kset s1 s2 c R).exists_bound_of_continuousOn
    (Complex.continuous_ofReal.comp hg).continuousOn
  exact ⟨C, ae_restrict_of_forall_mem (measurableSet_Qset s1 s2 c R)
    fun p hp => hC p (Qset_subset_Kset s1 s2 c R hp)⟩

lemma norm_div_ofReal_le (μ : ℂ) {x s1 : ℝ} (hs1 : 0 < s1) (hx : s1 ≤ x) :
    ‖μ / ((x : ℝ) : ℂ)‖ ≤ ‖μ‖ / s1 := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le hs1 hx)]
  exact div_le_div_of_nonneg_left (norm_nonneg _) hs1 hx

/-- The `Ψ¹`-pairing summand `Σ_i (b_i - u_i) Ψ¹_i`. -/
def B1 (ν : ℝ) (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (b u : V3 → Fin 2 → ℂ) (p : V3) : ℂ :=
  ∑ i : Fin 2, (b p i - u p i) * ((psi1 ν Φ p.1 p.2 i : ℝ) : ℂ)

/-- The `Ψ²`-pairing summand `Σ_i (b_i - u_i) Φ_i`. -/
def B2 (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (b u : V3 → Fin 2 → ℂ) (p : V3) : ℂ :=
  ∑ i : Fin 2, (b p i - u p i) * ((Φ p.1 p.2 i : ℝ) : ℂ)

lemma integrableOn_B1_Q {ν c s1 s2 R : ℝ} {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ}
    (hs1 : 0 < s1) (hG : ∀ i, ContDiff ℝ ∞ (gI Φ i)) (b u : V3 → Fin 2 → ℂ)
    (hbQ : ∀ i, IntegrableOn (fun p => b p i) (Qset s1 s2 c R))
    (huQ : ∀ i, IntegrableOn (fun p => u p i) (Qset s1 s2 c R)) :
    IntegrableOn (fun p => B1 ν Φ b u p) (Qset s1 s2 c R) := by
  unfold B1
  apply integrable_finset_sum
  intro i _
  obtain ⟨C, hC⟩ := ae_bound_Qset (continuous_psi1 hG ν i) s1 s2 c R
  exact ((hbQ i).sub (huQ i)).mul_bdd
    (Complex.continuous_ofReal.comp (continuous_psi1 hG ν i)).aestronglyMeasurable hC

lemma integrableOn_B2_Q {c s1 s2 R : ℝ} {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ}
    (hG : ∀ i, ContDiff ℝ ∞ (gI Φ i)) (b u : V3 → Fin 2 → ℂ)
    (hbQ : ∀ i, IntegrableOn (fun p => b p i) (Qset s1 s2 c R))
    (huQ : ∀ i, IntegrableOn (fun p => u p i) (Qset s1 s2 c R)) :
    IntegrableOn (fun p => B2 Φ b u p) (Qset s1 s2 c R) := by
  unfold B2
  apply integrable_finset_sum
  intro i _
  have hc : Continuous fun p : V3 => Φ p.1 p.2 i := (hG i).continuous
  obtain ⟨C, hC⟩ := ae_bound_Qset hc s1 s2 c R
  exact ((hbQ i).sub (huQ i)).mul_bdd
    (Complex.continuous_ofReal.comp hc).aestronglyMeasurable hC

lemma integrableOn_mB2_Q {μ : ℂ} {c s1 s2 R : ℝ} {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ}
    (hs1 : 0 < s1) (hG : ∀ i, ContDiff ℝ ∞ (gI Φ i)) (b u : V3 → Fin 2 → ℂ)
    (hB2 : IntegrableOn (fun p => B2 Φ b u p) (Qset s1 s2 c R)) :
    IntegrableOn (fun p => μ / ((p.1 : ℝ) : ℂ) * B2 Φ b u p) (Qset s1 s2 c R) := by
  have hcont : ContinuousOn (fun p : V3 => μ / ((p.1 : ℝ) : ℂ)) (Qset s1 s2 c R) := by
    apply ContinuousOn.div continuousOn_const
      (Complex.continuous_ofReal.comp continuous_fst).continuousOn
    intro p hp
    exact Complex.ofReal_ne_zero.2 (ne_of_gt (lt_of_lt_of_le hs1 hp.1.1))
  exact Integrable.bdd_mul hB2 (hcont.aestronglyMeasurable (measurableSet_Qset s1 s2 c R))
    (ae_restrict_of_forall_mem (measurableSet_Qset s1 s2 c R)
      fun p hp => norm_div_ofReal_le μ hs1 hp.1.1)

lemma B12_zero_off {ν c s1 s2 R : ℝ} {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ}
    (hsupp : ∀ s x i, (s < s1 ∨ s2 < s ∨ R < |x.2|) → Φ s x i = 0) (b u : V3 → Fin 2 → ℂ)
    {p : V3} (hp : p ∈ Ioi (0 : ℝ) ×ˢ B0579.cell c) (hnot : p ∉ Qset s1 s2 c R) :
    B1 ν Φ b u p = 0 ∧ B2 Φ b u p = 0 := by
  have h := compl_Qset hp hnot
  have hpsi : ∀ i, psi1 ν Φ p.1 p.2 i = 0 := fun i => psi1_zero ν hsupp p.1 p.2 i h
  have hPhi : ∀ i, Φ p.1 p.2 i = 0 := fun i => hsupp p.1 p.2 i h
  constructor
  · unfold B1
    simp [hpsi]
  · unfold B2
    simp [hPhi]

lemma integrableOn_S_of_Q {f : V3 → ℂ} {S Q : Set V3} (hS : MeasurableSet S)
    (hf : IntegrableOn f Q) (hzero : ∀ p ∈ S, p ∉ Q → f p = 0) : IntegrableOn f S :=
  IntegrableOn.of_forall_diff_eq_zero hf hS (fun p hp => hzero p hp.1 hp.2)

/-- Pointwise swap identity: `flat(b) - flat(u) = Σ_i (b_i - u_i)(Ψ¹_i + (μ/s)Ψ²_i)`. -/
lemma flat_diff (ν : ℝ) (μ : ℂ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (b u : V3 → Fin 2 → ℂ) (p : V3) :
    flatIntegrand ν μ (fun _ _ _ => 0) F b Φ p =
      flatIntegrand ν μ (fun _ _ _ => 0) F u Φ p +
        (B1 ν Φ b u p + μ / ((p.1 : ℝ) : ℂ) * B2 Φ b u p) := by
  simp only [flatIntegrand, B1, B2, psi1, Fin.sum_univ_two, Complex.ofReal_zero, zero_mul,
    mul_zero, add_zero, sub_zero]
  push_cast
  ring

end UnforcedLeray.Short.IIIa.FOS
