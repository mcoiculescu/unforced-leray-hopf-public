import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_10

/-!
# `PartIII-b:C/inst/10/4`: `EAcMeas` from two Gaussian-lattice leaves

Source `the November 2 reference manuscript`
4978 (sums and derivatives converge by Gaussian decay), 5063-5079.

`EAcoef = merOf (s^{-1/2} • s^{3/2} • e_A)`, `e_A = Σ_j eABt …`.  Leaves:
* `EAcTermContLeaf` : each lattice term is jointly continuous in `(s,x)` on `s > 0`
  (`V_j`, `D²V_j`, `∇p_j` are explicit Gaussians times polynomials, smooth in `(s,x)` for `a > 0`);
* `EAcTermDomLeaf` : locally uniform Gaussian domination of the terms, linear in `|B|+|C|`.
Proved here: `ayCont`, `bmatCont` (continuity of `A^y`, `B` on `s > 0`) and
`eaCMeas_of_leaves`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The `j`-th lattice term of `e_A` for matrices `B, C` (source 4971-4972). -/
def eABt (ν s : ℝ) (B C : Mat3) (x : ℝ × ℝ) (j : ℤ) : Vec3 :=
  (2 : ℝ) • mv B (emb (Vj ν s j x))
    + (2 * ν) • hessContr C (Vj ν s j) x
    - mv (fun a b => C a b + C b a) (emb (mgrad (pj ν s j) x))

/-- Leaf T (source 4978, 5063-5079): the terms are jointly continuous in `(s,x)` on `s > 0`
when `B, C` are continuous on `s > 0`. -/
def EAcTermContLeaf : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ B C : ℝ → Mat3, ContinuousOn B (Ioi 0) → ContinuousOn C (Ioi 0) →
    ∀ j : ℤ, ContinuousOn (fun p : Chart => eABt ν p.1 (B p.1) (C p.1) p.2 j) {p : Chart | 0 < p.1}

/-- Leaf D (source 4978, 5063-5079): locally uniform Gaussian domination: for `ν > 0`,
`0 < s0` and `s1, R`, there is a summable `u` with
`‖eABt ν s B C x j‖ ≤ (|B| + |C|) u j` for `s ∈ [s0, s1]`, `‖x‖ ≤ R`, all `B, C, j`
(`V_j, D²V_j, ∇p_j ≤ K (1+|q-jc|)³ e^{-(q-jc)²/(4a)}` with `a ≤ 1+ν s1`; compare
`hessVjBound`, `mgradPjBound`, `eATermSummable_of`). -/
def EAcTermDomLeaf : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ s0 s1 R : ℝ, 0 < s0 → ∃ u : ℤ → ℝ, Summable u ∧
    ∀ s : ℝ, s0 ≤ s → s ≤ s1 → ∀ x : ℝ × ℝ, ‖x‖ ≤ R → ∀ (B C : Mat3) (j : ℤ),
      ‖eABt ν s B C x j‖ ≤ (frob B + frob C) * u j

theorem frob_continuous : Continuous frob := by
  unfold frob
  fun_prop

theorem ayCont (as : ℝ) (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf) (ν : ℝ) (A : ℝ → Mat3)
    (hA : IsAffElem as A) : ContDiffOn ℝ 6 (Ay ν χf A) (Ioi 0) := by
  have hc : ContDiff ℝ 6 (fun s : ℝ => χf (ν * s)) :=
    (hχ.smooth.of_le (WithTop.coe_le_coe.mpr le_top)).comp (contDiff_const.mul contDiff_id)
  exact hc.contDiffOn.smul hA.smooth

theorem bmatCont (as : ℝ) (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf) (ν μ : ℝ) (A : ℝ → Mat3)
    (hA : IsAffElem as A) : ContinuousOn (Bmat ν μ χf A) (Ioi 0) := by
  have h6 := ayCont as χf hχ ν A hA
  have hd : ContinuousOn (deriv (Ay ν χf A)) (Ioi 0) :=
    h6.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  have h1 : ContinuousOn (fun s : ℝ => (μ / s) • Ay ν χf A s) (Ioi 0) := by
    have hf : ContinuousOn (fun s : ℝ => μ / s) (Ioi 0) :=
      continuousOn_const.div continuousOn_id (fun s hs => ne_of_gt hs)
    exact ContinuousOn.smul hf h6.continuousOn
  exact hd.add h1

theorem merOf_continuous : Continuous merOf := by
  unfold merOf
  fun_prop

theorem eaCContOn_of_leaves (as : ℝ) (χf : ℝ → ℝ) (hT : EAcTermContLeaf) (hD : EAcTermDomLeaf)
    (hχ : IsSourceCutoffC χf) (ν μ : ℝ) (hν : 0 < ν) (A : ℝ → Mat3) (hA : IsAffElem as A) :
    ContinuousOn (EAcoef ν μ χf A) {p : Chart | 0 < p.1} := by
  have hAy : ContinuousOn (Ay ν χf A) (Ioi 0) := (ayCont as χf hχ ν A hA).continuousOn
  have hB : ContinuousOn (Bmat ν μ χf A) (Ioi 0) := bmatCont as χf hχ ν μ A hA
  have hT' := hT ν hν _ _ hB hAy
  apply continuousOn_of_locally_continuousOn
  intro p hp
  have hp1 : 0 < p.1 := hp
  set s0 : ℝ := p.1 / 2 with hs0
  set s1 : ℝ := p.1 + 1 with hs1
  set R : ℝ := ‖p.2‖ + 1 with hR
  have hs0pos : 0 < s0 := by positivity
  refine ⟨{q : Chart | s0 < q.1 ∧ q.1 < s1 ∧ ‖q.2‖ < R}, ?_, ⟨by simp only [hs0]; linarith,
    by simp only [hs1]; linarith, by simp only [hR]; linarith⟩, ?_⟩
  · refine (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_fst continuous_const).inter
        (isOpen_lt (continuous_snd.norm) continuous_const))
  obtain ⟨u, hu, hbd⟩ := hD ν hν s0 s1 R hs0pos
  have hcm : ContinuousOn (fun s : ℝ => frob (Bmat ν μ χf A s) + frob (Ay ν χf A s))
      (Icc s0 s1) := by
    have hsub : Icc s0 s1 ⊆ Ioi 0 := fun s hs => lt_of_lt_of_le hs0pos hs.1
    exact (frob_continuous.comp_continuousOn (hB.mono hsub)).add
      (frob_continuous.comp_continuousOn (hAy.mono hsub))
  obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn hcm).bddAbove
  have hG : ContinuousOn (fun q : Chart => ∑' j : ℤ,
      eABt ν q.1 (Bmat ν μ χf A q.1) (Ay ν χf A q.1) q.2 j) ({q : Chart | 0 < q.1} ∩
        {q : Chart | s0 < q.1 ∧ q.1 < s1 ∧ ‖q.2‖ < R}) := by
    refine continuousOn_tsum (u := fun j => M * |u j|) (fun j => (hT' j).mono inter_subset_left)
      (hu.abs.mul_left M) ?_
    intro j q hq
    obtain ⟨_, h1, h2, h3⟩ := hq
    have h4 := hbd q.1 h1.le h2.le q.2 h3.le (Bmat ν μ χf A q.1) (Ay ν χf A q.1) j
    have h5 : frob (Bmat ν μ χf A q.1) + frob (Ay ν χf A q.1) ≤ M :=
      hM ⟨q.1, ⟨h1.le, h2.le⟩, rfl⟩
    calc _ ≤ _ := h4
      _ ≤ (frob (Bmat ν μ χf A q.1) + frob (Ay ν χf A q.1)) * |u j| :=
          mul_le_mul_of_nonneg_left (le_abs_self _)
            (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      _ ≤ M * |u j| := mul_le_mul_of_nonneg_right h5 (abs_nonneg _)
  have hfin : ContinuousOn (EAcoef ν μ χf A) ({q : Chart | 0 < q.1} ∩
        {q : Chart | s0 < q.1 ∧ q.1 < s1 ∧ ‖q.2‖ < R}) := by
    have hs : ContinuousOn (fun q : Chart => (Real.sqrt q.1)⁻¹ * q.1 ^ (3 / 2 : ℝ))
        ({q : Chart | 0 < q.1} ∩ {q : Chart | s0 < q.1 ∧ q.1 < s1 ∧ ‖q.2‖ < R}) := by
      refine ContinuousOn.mul ?_ ?_
      · exact (Real.continuous_sqrt.continuousOn.comp continuous_fst.continuousOn
          (fun _ _ => Set.mem_univ _)).inv₀ (fun q hq => by
            have : 0 < q.1 := hq.1
            exact (Real.sqrt_pos.mpr this).ne')
      · exact ContinuousOn.rpow_const continuous_fst.continuousOn (fun q hq => Or.inl (ne_of_gt hq.1))
    have := merOf_continuous.comp_continuousOn (hs.smul hG)
    refine this.congr (fun q hq => ?_)
    simp only [EAcoef, EA, eA, Function.comp, smul_smul]
    rfl
  exact hfin

theorem eaCMeas_of_leaves (as : ℝ) (χf : ℝ → ℝ) (hT : EAcTermContLeaf) (hD : EAcTermDomLeaf) :
    EAcMeas as χf := by
  intro hχ ν μ hν A hA
  have hc := eaCContOn_of_leaves as χf hT hD hχ ν μ hν A hA
  have hm : MeasurableSet {p : Chart | 0 < p.1} :=
    measurableSet_lt measurable_const measurable_fst
  have hr : AEStronglyMeasurable (EAcoef ν μ χf A)
      ((srcMeasure (cOf ν)).restrict {p : Chart | 0 < p.1}) :=
    hc.aestronglyMeasurable hm
  have hae : ∀ᵐ p ∂(srcMeasure (cOf ν)), p ∈ {p : Chart | 0 < p.1} :=
    ae_srcMeasure_fst_pos (cOf ν)
  rwa [Measure.restrict_eq_self_of_ae_mem hae] at hr

end UnforcedLeray.Short.PartIIIb.Concrete

end
