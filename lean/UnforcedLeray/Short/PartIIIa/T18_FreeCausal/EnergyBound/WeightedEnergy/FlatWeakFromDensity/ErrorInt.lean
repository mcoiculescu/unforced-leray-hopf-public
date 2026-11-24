import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.FlatWeakFromDensity.Basic

/-!
# Part III-a, helper of `PartIII-a:T18/3/1/2`: integrability of the error term

`errTerm ν b G ψ φ p = ν ψ(s) ∑ᵢ (bᵢ Δφᵢ + ∑ⱼ Gᵢⱼ ∂ⱼφᵢ)` for a spatial flat test `φ`. It vanishes
outside `errSet`, a set of finite measure on which `b, G` are square integrable (`energyLoc`), and
the coefficients `ψ`, `Δφᵢ`, `∂ⱼφᵢ` are bounded and continuous. Hence it is integrable on
`(0,∞) × cell`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The error term `ν ψ(s) ∑ᵢ (bᵢ Δφᵢ + ∑ⱼ Gᵢⱼ ∂ⱼφᵢ)`. -/
def errTerm (ν : ℝ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (ψ : ℝ → ℝ) (φ : ℝ × ℝ → Fin 2 → ℝ) (p : ℝ × (ℝ × ℝ)) : ℂ :=
  (ν : ℂ) * (ψ p.1 : ℂ) * ∑ i : Fin 2, (b p i * (lapP (fun y => φ y i) p.2 : ℂ) +
    ∑ j : Fin 2, G p i j * (B0579.pd j (fun y => φ y i) p.2 : ℂ))

/-- The finite-measure set carrying the error term: `[a, u] × (cell ∩ {|η| ≤ R})`. -/
def errSet (c a u R : ℝ) : Set (ℝ × (ℝ × ℝ)) :=
  Icc a u ×ˢ (Ico (-(c / 2)) (c / 2) ×ˢ Icc (-R) R)

lemma mem_errSet {c a u R : ℝ} {p : ℝ × (ℝ × ℝ)} :
    p ∈ errSet c a u R ↔ p.1 ∈ Icc a u ∧ p.2.1 ∈ Ico (-(c / 2)) (c / 2) ∧ p.2.2 ∈ Icc (-R) R :=
  Iff.rfl

lemma pd_eq_zero_of_band {g : ℝ × ℝ → ℝ} {R : ℝ} (h : ∀ y : ℝ × ℝ, R < |y.2| → g y = 0)
    (j : Fin 2) {x : ℝ × ℝ} (hx : R < |x.2|) : B0579.pd j g x = 0 := by
  have hopen : IsOpen {y : ℝ × ℝ | R < |y.2|} :=
    isOpen_lt continuous_const (continuous_abs.comp continuous_snd)
  have hev : g =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
    Filter.eventually_of_mem (hopen.mem_nhds hx) fun y hy => h y hy
  simp only [B0579.pd]
  rw [hev.fderiv_eq]
  simp

lemma lapP_eq_zero_of_band {g : ℝ × ℝ → ℝ} {R : ℝ} (h : ∀ y : ℝ × ℝ, R < |y.2| → g y = 0)
    {x : ℝ × ℝ} (hx : R < |x.2|) : lapP g x = 0 := by
  have h1 : ∀ y : ℝ × ℝ, R < |y.2| → B0579.pd 0 g y = 0 := fun y hy => pd_eq_zero_of_band h 0 hy
  have h2 : ∀ y : ℝ × ℝ, R < |y.2| → B0579.pd 1 g y = 0 := fun y hy => pd_eq_zero_of_band h 1 hy
  unfold lapP
  rw [pd_eq_zero_of_band h1 0 hx, pd_eq_zero_of_band h2 1 hx, add_zero]

lemma norm_le_vnorm2' (a : Fin 2 → ℂ) (i : Fin 2) : ‖a i‖ ≤ vnorm2 a := by
  unfold vnorm2
  rw [← Real.sqrt_sq (norm_nonneg (a i))]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun j => ‖a j‖ ^ 2)
    (fun j _ => by positivity) (Finset.mem_univ i))

lemma norm_le_tnorm2' (T : Fin 2 → Fin 2 → ℂ) (i j : Fin 2) : ‖T i j‖ ≤ tnorm2 T := by
  unfold tnorm2
  rw [← Real.sqrt_sq (norm_nonneg (T i j))]
  refine Real.sqrt_le_sqrt (le_trans (Finset.single_le_sum (f := fun k => ‖T i k‖ ^ 2)
    (fun k _ => by positivity) (Finset.mem_univ j))
    (Finset.single_le_sum (f := fun l => ∑ k, ‖T l k‖ ^ 2) (fun l _ => by positivity)
      (Finset.mem_univ i)))

lemma measurable_vnorm2' {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} (hb : ∀ i, Measurable fun p => b p i) :
    Measurable fun p => vnorm2 (b p) := by
  unfold vnorm2
  exact Real.continuous_sqrt.measurable.comp (Finset.measurable_sum _ fun i _ => (hb i).norm.pow_const 2)

lemma measurable_tnorm2' {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hG : ∀ i j, Measurable fun p => G p i j) : Measurable fun p => tnorm2 (G p) := by
  unfold tnorm2
  exact Real.continuous_sqrt.measurable.comp (Finset.measurable_sum _ fun i _ =>
    Finset.measurable_sum _ fun j _ => (hG i j).norm.pow_const 2)

/-- The error term is integrable on `(0,∞) × cell`. -/
lemma errTerm_integrableOn {c ν : ℝ} {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} {ψ : ℝ → ℝ} {φ : ℝ × ℝ → Fin 2 → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hts : tsupport ψ ⊆ Ioi 0)
    (hφ : IsFlatSpatialTest c φ)
    (hb : ∀ i, Measurable fun p => b p i) (hG : ∀ i j, Measurable fun p => G p i j)
    (hE : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) < ⊤) :
    IntegrableOn (errTerm ν b G ψ φ) (Ioi (0 : ℝ) ×ˢ B0579.cell c) := by
  obtain ⟨a, u, ha, hsub⟩ := exists_Icc_of_tsupport hψc hts
  obtain ⟨R, hR⟩ := hφ.bounded
  have hψcont : Continuous ψ := hψ.continuous
  obtain ⟨Cψ, hCψ⟩ := hψcont.bounded_above_of_compact_support hψc
  have hCψ0 : 0 ≤ Cψ := (norm_nonneg _).trans (hCψ 0)
  -- square integrability of the energy density on a slightly larger time interval
  have hQint : Integrable (fun p : ℝ × (ℝ × ℝ) => vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2)
      (volume.restrict (Icc (a / 2) (max u a + 1) ×ˢ B0579.cell c)) := by
    refine ⟨((measurable_vnorm2' hb).pow_const 2 |>.add
      ((measurable_tnorm2' hG).pow_const 2)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun p => by positivity)]
    exact hE (a / 2) (max u a + 1) (by linarith) (by linarith [le_max_right u a])
  have hsubQ : errSet c a u R ⊆ Icc (a / 2) (max u a + 1) ×ˢ B0579.cell c := by
    intro p hp
    obtain ⟨h1, h2, _⟩ := mem_errSet.1 hp
    refine Set.mem_prod.2 ⟨Set.mem_Icc.2 ⟨by linarith [h1.1], ?_⟩, Set.mem_prod.2 ⟨h2, trivial⟩⟩
    linarith [h1.2, le_max_left u a]
  have hK : IsCompact (Icc a u ×ˢ (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hTfin : volume (errSet c a u R) < ⊤ := by
    refine lt_of_le_of_lt (measure_mono ?_) hK.measure_lt_top
    intro p hp
    obtain ⟨h1, h2, h3⟩ := mem_errSet.1 hp
    exact Set.mem_prod.2 ⟨h1, Set.mem_prod.2 ⟨Ico_subset_Icc_self h2, h3⟩⟩
  have : IsFiniteMeasure (volume.restrict (errSet c a u R)) :=
    isFiniteMeasure_restrict.2 hTfin.ne
  have hmeasE : MeasurableSet (errSet c a u R) := by
    unfold errSet
    exact measurableSet_Icc.prod (measurableSet_Ico.prod measurableSet_Icc)
  -- the factors `bᵢ` and `Gᵢⱼ` are integrable on `errSet`
  have hbI : ∀ i, Integrable (fun p => b p i) (volume.restrict (errSet c a u R)) := by
    intro i
    refine Integrable.mono' (g := fun p => 1 + (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2))
      ((integrable_const (1 : ℝ)).add (IntegrableOn.mono_set hQint hsubQ))
      (hb i).aestronglyMeasurable ?_
    refine Eventually.of_forall fun p => ?_
    have h1 := norm_le_vnorm2' (b p) i
    nlinarith [sq_nonneg (vnorm2 (b p) - 1), sq_nonneg (vnorm2 (b p)), sq_nonneg (tnorm2 (G p))]
  have hGI : ∀ i j, Integrable (fun p => G p i j) (volume.restrict (errSet c a u R)) := by
    intro i j
    refine Integrable.mono' (g := fun p => 1 + (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2))
      ((integrable_const (1 : ℝ)).add (IntegrableOn.mono_set hQint hsubQ))
      (hG i j).aestronglyMeasurable ?_
    refine Eventually.of_forall fun p => ?_
    have h1 := norm_le_tnorm2' (G p) i j
    nlinarith [sq_nonneg (tnorm2 (G p) - 1), sq_nonneg (tnorm2 (G p)), sq_nonneg (vnorm2 (b p))]
  -- continuity and bounds of the coefficients on the compact `K0 ⊇` the `x`-part of `errSet`
  have hK0 : IsCompact (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R) := isCompact_Icc.prod isCompact_Icc
  have hLc : ∀ i, Continuous (lapP (fun y => φ y i)) := by
    intro i
    unfold lapP
    exact (((isCylTest_component hφ i).pd 0).pd 0 |>.continuous).add
      (((isCylTest_component hφ i).pd 1).pd 1 |>.continuous)
  have hDc : ∀ i j, Continuous (fun x => B0579.pd j (fun y => φ y i) x) := fun i j =>
    ((isCylTest_component hφ i).pd j).continuous
  have hA : ∀ i, Integrable (fun p : ℝ × (ℝ × ℝ) =>
      (ν : ℂ) * (ψ p.1 : ℂ) * (lapP (fun y => φ y i) p.2 : ℂ) * b p i)
      (volume.restrict (errSet c a u R)) := by
    intro i
    obtain ⟨CL, hCL⟩ := hK0.exists_bound_of_continuousOn (hLc i).continuousOn
    have hLi := hLc i
    have hfc : Continuous (fun p : ℝ × (ℝ × ℝ) =>
        (ν : ℂ) * (ψ p.1 : ℂ) * (lapP (fun y => φ y i) p.2 : ℂ)) := by
      fun_prop
    refine Integrable.bdd_mul (c := ‖ν‖ * Cψ * max CL 0) (hbI i) hfc.aestronglyMeasurable ?_
    refine (ae_restrict_iff' hmeasE).2 (Eventually.of_forall fun p hp => ?_)
    obtain ⟨_, h2, h3⟩ := mem_errSet.1 hp
    have hx : p.2 ∈ Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R :=
      Set.mem_prod.2 ⟨Ico_subset_Icc_self h2, h3⟩
    have hL : ‖lapP (fun y => φ y i) p.2‖ ≤ max CL 0 := (hCL p.2 hx).trans (le_max_left _ _)
    have hψb : ‖ψ p.1‖ ≤ Cψ := hCψ p.1
    simp only [norm_mul, Complex.norm_real]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hψb (norm_nonneg _)) hL (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) hCψ0)
  have hB : ∀ i j, Integrable (fun p : ℝ × (ℝ × ℝ) =>
      (ν : ℂ) * (ψ p.1 : ℂ) * (B0579.pd j (fun y => φ y i) p.2 : ℂ) * G p i j)
      (volume.restrict (errSet c a u R)) := by
    intro i j
    obtain ⟨CD, hCD⟩ := hK0.exists_bound_of_continuousOn (hDc i j).continuousOn
    have hfc : Continuous (fun p : ℝ × (ℝ × ℝ) =>
        (ν : ℂ) * (ψ p.1 : ℂ) * (B0579.pd j (fun y => φ y i) p.2 : ℂ)) := by
      have := hDc i j
      fun_prop
    refine Integrable.bdd_mul (c := ‖ν‖ * Cψ * max CD 0) (hGI i j) hfc.aestronglyMeasurable ?_
    refine (ae_restrict_iff' hmeasE).2 (Eventually.of_forall fun p hp => ?_)
    obtain ⟨_, h2, h3⟩ := mem_errSet.1 hp
    have hx : p.2 ∈ Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R :=
      Set.mem_prod.2 ⟨Ico_subset_Icc_self h2, h3⟩
    have hD : ‖B0579.pd j (fun y => φ y i) p.2‖ ≤ max CD 0 := (hCD p.2 hx).trans (le_max_left _ _)
    have hψb : ‖ψ p.1‖ ≤ Cψ := hCψ p.1
    simp only [norm_mul, Complex.norm_real]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hψb (norm_nonneg _)) hD (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) hCψ0)
  -- splitting of the error term into the two sums
  have hEq : errTerm ν b G ψ φ = fun p => (∑ i : Fin 2,
      (ν : ℂ) * (ψ p.1 : ℂ) * (lapP (fun y => φ y i) p.2 : ℂ) * b p i) +
      ∑ i : Fin 2, ∑ j : Fin 2, (ν : ℂ) * (ψ p.1 : ℂ) * (B0579.pd j (fun y => φ y i) p.2 : ℂ) *
        G p i j := by
    funext p
    simp only [errTerm, Fin.sum_univ_two]
    ring
  have hsum : Integrable (fun p : ℝ × (ℝ × ℝ) => (∑ i : Fin 2,
      (ν : ℂ) * (ψ p.1 : ℂ) * (lapP (fun y => φ y i) p.2 : ℂ) * b p i) +
      ∑ i : Fin 2, ∑ j : Fin 2, (ν : ℂ) * (ψ p.1 : ℂ) * (B0579.pd j (fun y => φ y i) p.2 : ℂ) *
        G p i j) (volume.restrict (errSet c a u R)) :=
    (integrable_finsetSum _ fun i _ => hA i).add
      (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hB i j)
  have hErr : IntegrableOn (errTerm ν b G ψ φ) (errSet c a u R) := by
    rw [hEq]
    exact hsum
  -- the error term vanishes off `errSet`
  have hSmeas : MeasurableSet (Ioi (0 : ℝ) ×ˢ B0579.cell c) :=
    measurableSet_Ioi.prod (measurableSet_Ico.prod MeasurableSet.univ)
  refine IntegrableOn.of_forall_sdiff_eq_zero hErr hSmeas ?_
  rintro p ⟨hpS, hpn⟩
  have hpc : p.2.1 ∈ Ico (-(c / 2)) (c / 2) := (Set.mem_prod.1 (Set.mem_prod.1 hpS).2).1
  have hcase : p.1 ∉ Icc a u ∨ R < |p.2.2| := by
    by_contra hcon
    push_neg at hcon
    exact hpn (mem_errSet.2 ⟨hcon.1, hpc, abs_le.1 hcon.2⟩)
  rcases hcase with h1 | h1
  · have hψz : ψ p.1 = 0 := (weight_zero_of_not_mem_Icc hsub h1).1
    simp [errTerm, hψz]
  · have hL : ∀ i, lapP (fun y => φ y i) p.2 = 0 := fun i =>
      lapP_eq_zero_of_band (fun y hy => hR y i hy) h1
    have hD : ∀ i j, B0579.pd j (fun y => φ y i) p.2 = 0 := fun i j =>
      pd_eq_zero_of_band (fun y hy => hR y i hy) j h1
    simp [errTerm, hL, hD]

end UnforcedLeray.Short.IIIa
