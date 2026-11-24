import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_9
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.FATermSummable

/-!
# `PartIII-b:C/inst/9/4` decomposed: `fAcMeas`

Source `the November 2 reference manuscript`
proof 5063-5079, cutoff 4953-4963, lattice sums 4963-4985.

`FAcoef p = s • merOf (fAB ν s (Bmat s) x)` with `s = p.1`.  Leaves:

* `BmatContOn` : `s ↦ Bmat ν μ χf A s` is continuous on `(0,∞)` (`A` is `C^6` there);
* `FAtermContOn` : each lattice term `(s,x,B) ↦ emb(DV_j(x)(B x_j)) + B V_j(x)` is continuous
  for `s > 0` (explicit formula `gp_fderiv_Vj`);
* `FAtermLocBound` : locally in `(s,x,B)` (`s > 0`) the terms have a summable majorant in `j`
  (Gaussian bound `fa_term_bound` with constants uniform on a neighbourhood).

Proved here: `bmatContOn` (leaf 1), `fAcMeas_of_leaves`; leaves 2, 3 remain.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Continuity of `FAcoef` on `{0 < p.1}` (source 5063-5079). -/
def FAcContOn (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν μ : ℝ), 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A →
    ContinuousOn (FAcoef ν μ χf A) {p : Chart | 0 < p.1}

theorem fAcMeas_of_contOn (as : ℝ) (χf : ℝ → ℝ) (h : FAcContOn as χf) : FAcMeas as χf := by
  intro hχ ν μ hν A hA
  have hc := h hχ ν μ hν A hA
  have hm : MeasurableSet {p : Chart | 0 < p.1} :=
    measurableSet_lt measurable_const measurable_fst
  have hr : AEStronglyMeasurable (FAcoef ν μ χf A)
      ((srcMeasure (cOf ν)).restrict {p : Chart | 0 < p.1}) := hc.aestronglyMeasurable hm
  have hae : ∀ᵐ p ∂(srcMeasure (cOf ν)), p ∈ {p : Chart | 0 < p.1} :=
    ae_srcMeasure_fst_pos (cOf ν)
  rwa [Measure.restrict_eq_self_of_ae_mem hae] at hr

/-- The `j`-th lattice term as a function of `(s, x, B)`. -/
def faTerm (ν : ℝ) (j : ℤ) (q : ℝ × (ℝ × ℝ) × Mat3) : Vec3 :=
  emb (fderiv ℝ (Vj ν q.1 j) q.2.1 (merApply q.2.2 (xj ν j q.2.1))) +
    mv q.2.2 (emb (Vj ν q.1 j q.2.1))

/-- Leaf 1 (source 4957-4958, 5063-5079). -/
def BmatContOn (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (as ν μ : ℝ) (A : ℝ → Mat3), IsAffElem as A →
    ContinuousOn (Bmat ν μ χf A) (Ioi 0)

/-- Leaf 2 (source 4963-4970): each lattice term is jointly continuous for `s > 0`. -/
def FAtermContOn : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ j : ℤ, ContinuousOn (faTerm ν j) {q | 0 < q.1}

/-- Leaf 3 (source 4963-4970, 5063-5079): locally uniform summable Gaussian majorant. -/
def FAtermLocBound : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ q0 : ℝ × (ℝ × ℝ) × Mat3, 0 < q0.1 →
    ∃ t ∈ 𝓝 q0, t ⊆ {q | 0 < q.1} ∧ ∃ u : ℤ → ℝ, Summable u ∧ ∀ j, ∀ q ∈ t, ‖faTerm ν j q‖ ≤ u j

theorem faSum_contOn (h2 : FAtermContOn) (h3 : FAtermLocBound) (ν : ℝ) (hν : 0 < ν) :
    ContinuousOn (fun q : ℝ × (ℝ × ℝ) × Mat3 => ∑' j : ℤ, faTerm ν j q) {q | 0 < q.1} := by
  have hopen : IsOpen {q : ℝ × (ℝ × ℝ) × Mat3 | 0 < q.1} :=
    isOpen_lt continuous_const continuous_fst
  intro q0 hq0
  refine ContinuousAt.continuousWithinAt ?_
  obtain ⟨t, ht, hts, u, hu, hb⟩ := h3 ν hν q0 hq0
  have hc : ContinuousOn (fun q => ∑' j : ℤ, faTerm ν j q) t :=
    continuousOn_tsum (fun j => (h2 ν hν j).mono hts) hu (fun j q hq => hb j q hq)
  exact hc.continuousAt ht

theorem bmatContOn (χf : ℝ → ℝ) : BmatContOn χf := by
  intro hχ as ν μ A hA
  have hAy : ContDiffOn ℝ 6 (Ay ν χf A) (Ioi 0) := by
    have h1 : ContDiff ℝ 6 (fun s : ℝ => χf (ν * s)) :=
      (hχ.smooth.of_le (by exact WithTop.coe_le_coe.2 (le_top : (6 : ℕ∞) ≤ ⊤))).comp (contDiff_const.mul contDiff_id)
    exact h1.contDiffOn.smul hA.smooth
  have hd : ContinuousOn (deriv (Ay ν χf A)) (Ioi 0) :=
    hAy.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  have h2 : ContinuousOn (fun s : ℝ => (μ / s) • Ay ν χf A s) (Ioi 0) :=
    (continuousOn_const.div continuousOn_id (fun s hs => ne_of_gt hs)).smul hAy.continuousOn
  exact hd.add h2

theorem fAcContOn_of_leaves (as : ℝ) (χf : ℝ → ℝ) (h1 : BmatContOn χf) (h2 : FAtermContOn)
    (h3 : FAtermLocBound) : FAcContOn as χf := by
  intro hχ ν μ hν A hA
  have hB := h1 hχ as ν μ A hA
  have hS := faSum_contOn h2 h3 ν hν
  have hpar : ContinuousOn (fun p : Chart => (p.1, p.2, Bmat ν μ χf A p.1))
      {p : Chart | 0 < p.1} := by
    refine continuousOn_fst.prodMk (continuousOn_snd.prodMk ?_)
    exact hB.comp continuousOn_fst (fun p hp => hp)
  have hmaps : MapsTo (fun p : Chart => (p.1, p.2, Bmat ν μ χf A p.1))
      {p : Chart | 0 < p.1} {q | 0 < q.1} := fun p hp => hp
  have hsum := hS.comp hpar hmaps
  have hscal : ContinuousOn (fun p : Chart => (Real.sqrt p.1)⁻¹ * p.1 ^ (3 / 2 : ℝ))
      {p : Chart | 0 < p.1} := by
    refine ContinuousOn.mul ?_ ?_
    · exact (Real.continuous_sqrt.comp_continuousOn continuousOn_fst).inv₀
        (fun p hp => (Real.sqrt_pos.2 hp).ne')
    · exact ContinuousOn.rpow_const continuousOn_fst (fun p hp => Or.inl (ne_of_gt hp))
  have hmer : Continuous merOf := by
    unfold merOf
    exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => by
      fin_cases i
      · exact (continuous_apply 0)
      · exact (continuous_apply 2))
  have hall : ContinuousOn (fun p : Chart =>
      merOf (-(((Real.sqrt p.1)⁻¹ * p.1 ^ (3 / 2 : ℝ)) •
        ∑' j : ℤ, faTerm ν j (p.1, p.2, Bmat ν μ χf A p.1)))) {p : Chart | 0 < p.1} :=
    hmer.comp_continuousOn ((hscal.smul hsum).neg)
  refine hall.congr (fun p hp => ?_)
  simp only [FAcoef, FA, fA, faTerm, smul_neg, smul_smul]

theorem fAcMeas_of_leaves (as : ℝ) (χf : ℝ → ℝ) (h1 : BmatContOn χf) (h2 : FAtermContOn)
    (h3 : FAtermLocBound) : FAcMeas as χf :=
  fAcMeas_of_contOn as χf (fAcContOn_of_leaves as χf h1 h2 h3)

end UnforcedLeray.Short.PartIIIb.Concrete
